-- Prove2me | solution 1 for syracuse_descends_range_654306_658306
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:48.749454+00:00
-- url     : https://prove2.me/submissions/20a27e11-fd29-4804-920c-77979dbd62fe

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


theorem B983045 : Blo 654306 983045 := bbase (se 4 (by rfl) ⟨92160, by rfl⟩ : syracuseStep 983045 = 184321) (by norm_num)
theorem B983069 : Blo 654306 983069 := bbase (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) (by norm_num)
theorem B1474613 : Blo 654306 1474613 := bbase (se 5 (by rfl) ⟨69122, by rfl⟩ : syracuseStep 1474613 = 138245) (by norm_num)
theorem B983093 : Blo 654306 983093 := bbase (se 5 (by rfl) ⟨46082, by rfl⟩ : syracuseStep 983093 = 92165) (by norm_num)
theorem B983117 : Blo 654306 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B1572949 : Blo 654306 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1245269 : Blo 654306 1245269 := bbase (se 8 (by rfl) ⟨7296, by rfl⟩ : syracuseStep 1245269 = 14593) (by norm_num)
theorem B983141 : Blo 654306 983141 := bbase (se 4 (by rfl) ⟨92169, by rfl⟩ : syracuseStep 983141 = 184339) (by norm_num)
theorem B1474685 : Blo 654306 1474685 := bbase (se 3 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 1474685 = 553007) (by norm_num)
theorem B983165 : Blo 654306 983165 := bbase (se 3 (by rfl) ⟨184343, by rfl⟩ : syracuseStep 983165 = 368687) (by norm_num)
theorem B983189 : Blo 654306 983189 := bbase (se 6 (by rfl) ⟨23043, by rfl⟩ : syracuseStep 983189 = 46087) (by norm_num)
theorem B983213 : Blo 654306 983213 := bbase (se 3 (by rfl) ⟨184352, by rfl⟩ : syracuseStep 983213 = 368705) (by norm_num)
theorem B1474757 : Blo 654306 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B983237 : Blo 654306 983237 := bbase (se 4 (by rfl) ⟨92178, by rfl⟩ : syracuseStep 983237 = 184357) (by norm_num)
theorem B1048781 : Blo 654306 1048781 := bbase (se 3 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 1048781 = 393293) (by norm_num)
theorem B7798997 : Blo 654306 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B983261 : Blo 654306 983261 := bbase (se 3 (by rfl) ⟨184361, by rfl⟩ : syracuseStep 983261 = 368723) (by norm_num)
theorem B983285 : Blo 654306 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B1474829 : Blo 654306 1474829 := bbase (se 3 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 1474829 = 553061) (by norm_num)
theorem B983309 : Blo 654306 983309 := bbase (se 3 (by rfl) ⟨184370, by rfl⟩ : syracuseStep 983309 = 368741) (by norm_num)
theorem B4981013 : Blo 654306 4981013 := bbase (se 6 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 4981013 = 233485) (by norm_num)
theorem B983333 : Blo 654306 983333 := bbase (se 4 (by rfl) ⟨92187, by rfl⟩ : syracuseStep 983333 = 184375) (by norm_num)
theorem B983357 : Blo 654306 983357 := bbase (se 3 (by rfl) ⟨184379, by rfl⟩ : syracuseStep 983357 = 368759) (by norm_num)
theorem B1474901 : Blo 654306 1474901 := bbase (se 10 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 1474901 = 4321) (by norm_num)
theorem B983381 : Blo 654306 983381 := bbase (se 10 (by rfl) ⟨1440, by rfl⟩ : syracuseStep 983381 = 2881) (by norm_num)
theorem B983405 : Blo 654306 983405 := bbase (se 3 (by rfl) ⟨184388, by rfl⟩ : syracuseStep 983405 = 368777) (by norm_num)
theorem B885109 : Blo 654306 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B1245557 : Blo 654306 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B983429 : Blo 654306 983429 := bbase (se 4 (by rfl) ⟨92196, by rfl⟩ : syracuseStep 983429 = 184393) (by norm_num)
theorem B1474973 : Blo 654306 1474973 := bbase (se 3 (by rfl) ⟨276557, by rfl⟩ : syracuseStep 1474973 = 553115) (by norm_num)
theorem B983453 : Blo 654306 983453 := bbase (se 3 (by rfl) ⟨184397, by rfl⟩ : syracuseStep 983453 = 368795) (by norm_num)
theorem B983477 : Blo 654306 983477 := bbase (se 5 (by rfl) ⟨46100, by rfl⟩ : syracuseStep 983477 = 92201) (by norm_num)
theorem B3735989 : Blo 654306 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B1180109 : Blo 654306 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B786893 : Blo 654306 786893 := bbase (se 3 (by rfl) ⟨147542, by rfl⟩ : syracuseStep 786893 = 295085) (by norm_num)
theorem B983501 : Blo 654306 983501 := bbase (se 3 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 983501 = 368813) (by norm_num)
theorem B1475045 : Blo 654306 1475045 := bbase (se 4 (by rfl) ⟨138285, by rfl⟩ : syracuseStep 1475045 = 276571) (by norm_num)
theorem B983525 : Blo 654306 983525 := bbase (se 4 (by rfl) ⟨92205, by rfl⟩ : syracuseStep 983525 = 184411) (by norm_num)
theorem B983549 : Blo 654306 983549 := bbase (se 3 (by rfl) ⟨184415, by rfl⟩ : syracuseStep 983549 = 368831) (by norm_num)
theorem B1245709 : Blo 654306 1245709 := bbase (se 3 (by rfl) ⟨233570, by rfl⟩ : syracuseStep 1245709 = 467141) (by norm_num)
theorem B2654741 : Blo 654306 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B983573 : Blo 654306 983573 := bbase (se 6 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 983573 = 46105) (by norm_num)
theorem B1475117 : Blo 654306 1475117 := bbase (se 3 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 1475117 = 553169) (by norm_num)
theorem B983597 : Blo 654306 983597 := bbase (se 3 (by rfl) ⟨184424, by rfl⟩ : syracuseStep 983597 = 368849) (by norm_num)
theorem B787009 : Blo 654306 787009 := bbase (se 2 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 787009 = 590257) (by norm_num)
theorem B983621 : Blo 654306 983621 := bbase (se 4 (by rfl) ⟨92214, by rfl⟩ : syracuseStep 983621 = 184429) (by norm_num)
theorem B983645 : Blo 654306 983645 := bbase (se 3 (by rfl) ⟨184433, by rfl⟩ : syracuseStep 983645 = 368867) (by norm_num)
theorem B1475189 : Blo 654306 1475189 := bbase (se 5 (by rfl) ⟨69149, by rfl⟩ : syracuseStep 1475189 = 138299) (by norm_num)
theorem B983669 : Blo 654306 983669 := bbase (se 5 (by rfl) ⟨46109, by rfl⟩ : syracuseStep 983669 = 92219) (by norm_num)
theorem B983693 : Blo 654306 983693 := bbase (se 3 (by rfl) ⟨184442, by rfl⟩ : syracuseStep 983693 = 368885) (by norm_num)
theorem B2097829 : Blo 654306 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B983717 : Blo 654306 983717 := bbase (se 4 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 983717 = 184447) (by norm_num)
theorem B1475261 : Blo 654306 1475261 := bbase (se 3 (by rfl) ⟨276611, by rfl⟩ : syracuseStep 1475261 = 553223) (by norm_num)
theorem B983741 : Blo 654306 983741 := bbase (se 3 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 983741 = 368903) (by norm_num)
theorem B6292181 : Blo 654306 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B983765 : Blo 654306 983765 := bbase (se 7 (by rfl) ⟨11528, by rfl⟩ : syracuseStep 983765 = 23057) (by norm_num)
theorem B983789 : Blo 654306 983789 := bbase (se 3 (by rfl) ⟨184460, by rfl⟩ : syracuseStep 983789 = 368921) (by norm_num)
theorem B787205 : Blo 654306 787205 := bbase (se 4 (by rfl) ⟨73800, by rfl⟩ : syracuseStep 787205 = 147601) (by norm_num)
theorem B1475333 : Blo 654306 1475333 := bbase (se 4 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 1475333 = 276625) (by norm_num)
theorem B983813 : Blo 654306 983813 := bbase (se 4 (by rfl) ⟨92232, by rfl⟩ : syracuseStep 983813 = 184465) (by norm_num)
theorem B1573661 : Blo 654306 1573661 := bbase (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) (by norm_num)
theorem B983837 : Blo 654306 983837 := bbase (se 3 (by rfl) ⟨184469, by rfl⟩ : syracuseStep 983837 = 368939) (by norm_num)
theorem B983861 : Blo 654306 983861 := bbase (se 5 (by rfl) ⟨46118, by rfl⟩ : syracuseStep 983861 = 92237) (by norm_num)
theorem B1246013 : Blo 654306 1246013 := bbase (se 3 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 1246013 = 467255) (by norm_num)
theorem B1475405 : Blo 654306 1475405 := bbase (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) (by norm_num)
theorem B983885 : Blo 654306 983885 := bbase (se 3 (by rfl) ⟨184478, by rfl⟩ : syracuseStep 983885 = 368957) (by norm_num)
theorem B983909 : Blo 654306 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B1049453 : Blo 654306 1049453 := bbase (se 3 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 1049453 = 393545) (by norm_num)
theorem B983933 : Blo 654306 983933 := bbase (se 3 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 983933 = 368975) (by norm_num)
theorem B1475477 : Blo 654306 1475477 := bbase (se 6 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 1475477 = 69163) (by norm_num)
theorem B983957 : Blo 654306 983957 := bbase (se 6 (by rfl) ⟨23061, by rfl⟩ : syracuseStep 983957 = 46123) (by norm_num)
theorem B983981 : Blo 654306 983981 := bbase (se 3 (by rfl) ⟨184496, by rfl⟩ : syracuseStep 983981 = 368993) (by norm_num)
theorem B984005 : Blo 654306 984005 := bbase (se 4 (by rfl) ⟨92250, by rfl⟩ : syracuseStep 984005 = 184501) (by norm_num)
theorem B1475549 : Blo 654306 1475549 := bbase (se 3 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 1475549 = 553331) (by norm_num)
theorem B984029 : Blo 654306 984029 := bbase (se 3 (by rfl) ⟨184505, by rfl⟩ : syracuseStep 984029 = 369011) (by norm_num)
theorem B984053 : Blo 654306 984053 := bbase (se 5 (by rfl) ⟨46127, by rfl⟩ : syracuseStep 984053 = 92255) (by norm_num)
theorem B984077 : Blo 654306 984077 := bbase (se 3 (by rfl) ⟨184514, by rfl⟩ : syracuseStep 984077 = 369029) (by norm_num)
theorem B1475621 : Blo 654306 1475621 := bbase (se 4 (by rfl) ⟨138339, by rfl⟩ : syracuseStep 1475621 = 276679) (by norm_num)
theorem B984101 : Blo 654306 984101 := bbase (se 4 (by rfl) ⟨92259, by rfl⟩ : syracuseStep 984101 = 184519) (by norm_num)
theorem B984125 : Blo 654306 984125 := bbase (se 3 (by rfl) ⟨184523, by rfl⟩ : syracuseStep 984125 = 369047) (by norm_num)
theorem B984149 : Blo 654306 984149 := bbase (se 8 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 984149 = 11533) (by norm_num)
theorem B1475693 : Blo 654306 1475693 := bbase (se 3 (by rfl) ⟨276692, by rfl⟩ : syracuseStep 1475693 = 553385) (by norm_num)
theorem B984173 : Blo 654306 984173 := bbase (se 3 (by rfl) ⟨184532, by rfl⟩ : syracuseStep 984173 = 369065) (by norm_num)
theorem B984197 : Blo 654306 984197 := bbase (se 4 (by rfl) ⟨92268, by rfl⟩ : syracuseStep 984197 = 184537) (by norm_num)
theorem B6325397 : Blo 654306 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B984221 : Blo 654306 984221 := bbase (se 3 (by rfl) ⟨184541, by rfl⟩ : syracuseStep 984221 = 369083) (by norm_num)
theorem B1475765 : Blo 654306 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B984245 : Blo 654306 984245 := bbase (se 5 (by rfl) ⟨46136, by rfl⟩ : syracuseStep 984245 = 92273) (by norm_num)
theorem B984269 : Blo 654306 984269 := bbase (se 3 (by rfl) ⟨184550, by rfl⟩ : syracuseStep 984269 = 369101) (by norm_num)
theorem B984293 : Blo 654306 984293 := bbase (se 4 (by rfl) ⟨92277, by rfl⟩ : syracuseStep 984293 = 184555) (by norm_num)
theorem B1475837 : Blo 654306 1475837 := bbase (se 3 (by rfl) ⟨276719, by rfl⟩ : syracuseStep 1475837 = 553439) (by norm_num)
theorem B984317 : Blo 654306 984317 := bbase (se 3 (by rfl) ⟨184559, by rfl⟩ : syracuseStep 984317 = 369119) (by norm_num)
theorem B984341 : Blo 654306 984341 := bbase (se 6 (by rfl) ⟨23070, by rfl⟩ : syracuseStep 984341 = 46141) (by norm_num)
theorem B787753 : Blo 654306 787753 := bbase (se 2 (by rfl) ⟨295407, by rfl⟩ : syracuseStep 787753 = 590815) (by norm_num)
theorem B984365 : Blo 654306 984365 := bbase (se 3 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 984365 = 369137) (by norm_num)
theorem B1475909 : Blo 654306 1475909 := bbase (se 4 (by rfl) ⟨138366, by rfl⟩ : syracuseStep 1475909 = 276733) (by norm_num)
theorem B984389 : Blo 654306 984389 := bbase (se 4 (by rfl) ⟨92286, by rfl⟩ : syracuseStep 984389 = 184573) (by norm_num)
theorem B984413 : Blo 654306 984413 := bbase (se 3 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 984413 = 369155) (by norm_num)
theorem B1049965 : Blo 654306 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B984437 : Blo 654306 984437 := bbase (se 5 (by rfl) ⟨46145, by rfl⟩ : syracuseStep 984437 = 92291) (by norm_num)
theorem B1475981 : Blo 654306 1475981 := bbase (se 3 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 1475981 = 553493) (by norm_num)
theorem B984461 : Blo 654306 984461 := bbase (se 3 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 984461 = 369173) (by norm_num)
theorem B984485 : Blo 654306 984485 := bbase (se 4 (by rfl) ⟨92295, by rfl⟩ : syracuseStep 984485 = 184591) (by norm_num)
theorem B2491829 : Blo 654306 2491829 := bbase (se 5 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 2491829 = 233609) (by norm_num)
theorem B787897 : Blo 654306 787897 := bbase (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) (by norm_num)
theorem B1574333 : Blo 654306 1574333 := bbase (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) (by norm_num)
theorem B984509 : Blo 654306 984509 := bbase (se 3 (by rfl) ⟨184595, by rfl⟩ : syracuseStep 984509 = 369191) (by norm_num)
theorem B1476053 : Blo 654306 1476053 := bbase (se 7 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 1476053 = 34595) (by norm_num)
theorem B984533 : Blo 654306 984533 := bbase (se 7 (by rfl) ⟨11537, by rfl⟩ : syracuseStep 984533 = 23075) (by norm_num)
theorem B984557 : Blo 654306 984557 := bbase (se 3 (by rfl) ⟨184604, by rfl⟩ : syracuseStep 984557 = 369209) (by norm_num)
theorem B984581 : Blo 654306 984581 := bbase (se 4 (by rfl) ⟨92304, by rfl⟩ : syracuseStep 984581 = 184609) (by norm_num)
theorem B1476125 : Blo 654306 1476125 := bbase (se 3 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 1476125 = 553547) (by norm_num)
theorem B984605 : Blo 654306 984605 := bbase (se 3 (by rfl) ⟨184613, by rfl⟩ : syracuseStep 984605 = 369227) (by norm_num)
theorem B1246765 : Blo 654306 1246765 := bbase (se 3 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 1246765 = 467537) (by norm_num)
theorem B984629 : Blo 654306 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B984653 : Blo 654306 984653 := bbase (se 3 (by rfl) ⟨184622, by rfl⟩ : syracuseStep 984653 = 369245) (by norm_num)
theorem B1476197 : Blo 654306 1476197 := bbase (se 4 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 1476197 = 276787) (by norm_num)
theorem B984677 : Blo 654306 984677 := bbase (se 4 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 984677 = 184627) (by norm_num)
theorem B984701 : Blo 654306 984701 := bbase (se 3 (by rfl) ⟨184631, by rfl⟩ : syracuseStep 984701 = 369263) (by norm_num)
theorem B2360981 : Blo 654306 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B984725 : Blo 654306 984725 := bbase (se 6 (by rfl) ⟨23079, by rfl⟩ : syracuseStep 984725 = 46159) (by norm_num)
theorem B1476269 : Blo 654306 1476269 := bbase (se 3 (by rfl) ⟨276800, by rfl⟩ : syracuseStep 1476269 = 553601) (by norm_num)
theorem B984749 : Blo 654306 984749 := bbase (se 3 (by rfl) ⟨184640, by rfl⟩ : syracuseStep 984749 = 369281) (by norm_num)
theorem B1246909 : Blo 654306 1246909 := bbase (se 3 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 1246909 = 467591) (by norm_num)
theorem B984773 : Blo 654306 984773 := bbase (se 4 (by rfl) ⟨92322, by rfl⟩ : syracuseStep 984773 = 184645) (by norm_num)
theorem B2492117 : Blo 654306 2492117 := bbase (se 7 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 2492117 = 58409) (by norm_num)
theorem B984797 : Blo 654306 984797 := bbase (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) (by norm_num)
theorem B1181413 : Blo 654306 1181413 := bbase (se 4 (by rfl) ⟨110757, by rfl⟩ : syracuseStep 1181413 = 221515) (by norm_num)
theorem B1476341 : Blo 654306 1476341 := bbase (se 5 (by rfl) ⟨69203, by rfl⟩ : syracuseStep 1476341 = 138407) (by norm_num)
theorem B984821 : Blo 654306 984821 := bbase (se 5 (by rfl) ⟨46163, by rfl⟩ : syracuseStep 984821 = 92327) (by norm_num)
theorem B984845 : Blo 654306 984845 := bbase (se 3 (by rfl) ⟨184658, by rfl⟩ : syracuseStep 984845 = 369317) (by norm_num)
theorem B984869 : Blo 654306 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B2098997 : Blo 654306 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B1050421 : Blo 654306 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B1476413 : Blo 654306 1476413 := bbase (se 3 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 1476413 = 553655) (by norm_num)
theorem B984893 : Blo 654306 984893 := bbase (se 3 (by rfl) ⟨184667, by rfl⟩ : syracuseStep 984893 = 369335) (by norm_num)
theorem B3147589 : Blo 654306 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B984917 : Blo 654306 984917 := bbase (se 9 (by rfl) ⟨2885, by rfl⟩ : syracuseStep 984917 = 5771) (by norm_num)
theorem B9471829 : Blo 654306 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B1247069 : Blo 654306 1247069 := bbase (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) (by norm_num)
theorem B984941 : Blo 654306 984941 := bbase (se 3 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 984941 = 369353) (by norm_num)
theorem B4786037 : Blo 654306 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B1181557 : Blo 654306 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B1476485 : Blo 654306 1476485 := bbase (se 4 (by rfl) ⟨138420, by rfl⟩ : syracuseStep 1476485 = 276841) (by norm_num)
theorem B984965 : Blo 654306 984965 := bbase (se 4 (by rfl) ⟨92340, by rfl⟩ : syracuseStep 984965 = 184681) (by norm_num)
theorem B984989 : Blo 654306 984989 := bbase (se 3 (by rfl) ⟨184685, by rfl⟩ : syracuseStep 984989 = 369371) (by norm_num)
theorem B1771429 : Blo 654306 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B1869749 : Blo 654306 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B985013 : Blo 654306 985013 := bbase (se 5 (by rfl) ⟨46172, by rfl⟩ : syracuseStep 985013 = 92345) (by norm_num)
theorem B1476557 : Blo 654306 1476557 := bbase (se 3 (by rfl) ⟨276854, by rfl⟩ : syracuseStep 1476557 = 553709) (by norm_num)
theorem B985037 : Blo 654306 985037 := bbase (se 3 (by rfl) ⟨184694, by rfl⟩ : syracuseStep 985037 = 369389) (by norm_num)
theorem B985061 : Blo 654306 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B1247213 : Blo 654306 1247213 := bbase (se 3 (by rfl) ⟨233852, by rfl⟩ : syracuseStep 1247213 = 467705) (by norm_num)
theorem B985085 : Blo 654306 985085 := bbase (se 3 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 985085 = 369407) (by norm_num)
theorem B1476629 : Blo 654306 1476629 := bbase (se 6 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 1476629 = 69217) (by norm_num)
theorem B985109 : Blo 654306 985109 := bbase (se 6 (by rfl) ⟨23088, by rfl⟩ : syracuseStep 985109 = 46177) (by norm_num)
theorem B985133 : Blo 654306 985133 := bbase (se 3 (by rfl) ⟨184712, by rfl⟩ : syracuseStep 985133 = 369425) (by norm_num)
theorem B985157 : Blo 654306 985157 := bbase (se 4 (by rfl) ⟨92358, by rfl⟩ : syracuseStep 985157 = 184717) (by norm_num)
theorem B1476701 : Blo 654306 1476701 := bbase (se 3 (by rfl) ⟨276881, by rfl⟩ : syracuseStep 1476701 = 553763) (by norm_num)
theorem B985181 : Blo 654306 985181 := bbase (se 3 (by rfl) ⟨184721, by rfl⟩ : syracuseStep 985181 = 369443) (by norm_num)
theorem B985205 : Blo 654306 985205 := bbase (se 5 (by rfl) ⟨46181, by rfl⟩ : syracuseStep 985205 = 92363) (by norm_num)
theorem B985229 : Blo 654306 985229 := bbase (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) (by norm_num)
theorem B1181861 : Blo 654306 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1476773 : Blo 654306 1476773 := bbase (se 4 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 1476773 = 276895) (by norm_num)
theorem B985253 : Blo 654306 985253 := bbase (se 4 (by rfl) ⟨92367, by rfl⟩ : syracuseStep 985253 = 184735) (by norm_num)
theorem B985277 : Blo 654306 985277 := bbase (se 3 (by rfl) ⟨184739, by rfl⟩ : syracuseStep 985277 = 369479) (by norm_num)
theorem B985301 : Blo 654306 985301 := bbase (se 7 (by rfl) ⟨11546, by rfl⟩ : syracuseStep 985301 = 23093) (by norm_num)
theorem B1476845 : Blo 654306 1476845 := bbase (se 3 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 1476845 = 553817) (by norm_num)
theorem B985325 : Blo 654306 985325 := bbase (se 3 (by rfl) ⟨184748, by rfl⟩ : syracuseStep 985325 = 369497) (by norm_num)
theorem B985349 : Blo 654306 985349 := bbase (se 4 (by rfl) ⟨92376, by rfl⟩ : syracuseStep 985349 = 184753) (by norm_num)
theorem B1247501 : Blo 654306 1247501 := bbase (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) (by norm_num)
theorem B985373 : Blo 654306 985373 := bbase (se 3 (by rfl) ⟨184757, by rfl⟩ : syracuseStep 985373 = 369515) (by norm_num)
theorem B1476917 : Blo 654306 1476917 := bbase (se 5 (by rfl) ⟨69230, by rfl⟩ : syracuseStep 1476917 = 138461) (by norm_num)
theorem B985397 : Blo 654306 985397 := bbase (se 5 (by rfl) ⟨46190, by rfl⟩ : syracuseStep 985397 = 92381) (by norm_num)
theorem B985421 : Blo 654306 985421 := bbase (se 3 (by rfl) ⟨184766, by rfl⟩ : syracuseStep 985421 = 369533) (by norm_num)
theorem B985445 : Blo 654306 985445 := bbase (se 4 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 985445 = 184771) (by norm_num)
theorem B1476989 : Blo 654306 1476989 := bbase (se 3 (by rfl) ⟨276935, by rfl⟩ : syracuseStep 1476989 = 553871) (by norm_num)
theorem B985469 : Blo 654306 985469 := bbase (se 3 (by rfl) ⟨184775, by rfl⟩ : syracuseStep 985469 = 369551) (by norm_num)
theorem B985493 : Blo 654306 985493 := bbase (se 6 (by rfl) ⟨23097, by rfl⟩ : syracuseStep 985493 = 46195) (by norm_num)
theorem B1247653 : Blo 654306 1247653 := bbase (se 4 (by rfl) ⟨116967, by rfl⟩ : syracuseStep 1247653 = 233935) (by norm_num)
theorem B985517 : Blo 654306 985517 := bbase (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) (by norm_num)
theorem B1477061 : Blo 654306 1477061 := bbase (se 4 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 1477061 = 276949) (by norm_num)
theorem B985541 : Blo 654306 985541 := bbase (se 4 (by rfl) ⟨92394, by rfl⟩ : syracuseStep 985541 = 184789) (by norm_num)
theorem B788945 : Blo 654306 788945 := bbase (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) (by norm_num)
theorem B1051093 : Blo 654306 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B985565 : Blo 654306 985565 := bbase (se 3 (by rfl) ⟨184793, by rfl⟩ : syracuseStep 985565 = 369587) (by norm_num)
theorem B985589 : Blo 654306 985589 := bbase (se 5 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 985589 = 92399) (by norm_num)
theorem B1477133 : Blo 654306 1477133 := bbase (se 3 (by rfl) ⟨276962, by rfl⟩ : syracuseStep 1477133 = 553925) (by norm_num)
theorem B985613 : Blo 654306 985613 := bbase (se 3 (by rfl) ⟨184802, by rfl⟩ : syracuseStep 985613 = 369605) (by norm_num)
theorem B985637 : Blo 654306 985637 := bbase (se 4 (by rfl) ⟨92403, by rfl⟩ : syracuseStep 985637 = 184807) (by norm_num)
theorem B985661 : Blo 654306 985661 := bbase (se 3 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 985661 = 369623) (by norm_num)
theorem B1477205 : Blo 654306 1477205 := bbase (se 8 (by rfl) ⟨8655, by rfl⟩ : syracuseStep 1477205 = 17311) (by norm_num)
theorem B985685 : Blo 654306 985685 := bbase (se 8 (by rfl) ⟨5775, by rfl⟩ : syracuseStep 985685 = 11551) (by norm_num)
theorem B985709 : Blo 654306 985709 := bbase (se 3 (by rfl) ⟨184820, by rfl⟩ : syracuseStep 985709 = 369641) (by norm_num)
theorem B985733 : Blo 654306 985733 := bbase (se 4 (by rfl) ⟨92412, by rfl⟩ : syracuseStep 985733 = 184825) (by norm_num)
theorem B2525845 : Blo 654306 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B1477277 : Blo 654306 1477277 := bbase (se 3 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 1477277 = 553979) (by norm_num)
theorem B985757 : Blo 654306 985757 := bbase (se 3 (by rfl) ⟨184829, by rfl⟩ : syracuseStep 985757 = 369659) (by norm_num)
theorem B985781 : Blo 654306 985781 := bbase (se 5 (by rfl) ⟨46208, by rfl⟩ : syracuseStep 985781 = 92417) (by norm_num)
theorem B985805 : Blo 654306 985805 := bbase (se 3 (by rfl) ⟨184838, by rfl⟩ : syracuseStep 985805 = 369677) (by norm_num)
theorem B1247957 : Blo 654306 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B1477349 : Blo 654306 1477349 := bbase (se 4 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 1477349 = 277003) (by norm_num)
theorem B985829 : Blo 654306 985829 := bbase (se 4 (by rfl) ⟨92421, by rfl⟩ : syracuseStep 985829 = 184843) (by norm_num)
theorem B985853 : Blo 654306 985853 := bbase (se 3 (by rfl) ⟨184847, by rfl⟩ : syracuseStep 985853 = 369695) (by norm_num)
theorem B985877 : Blo 654306 985877 := bbase (se 6 (by rfl) ⟨23106, by rfl⟩ : syracuseStep 985877 = 46213) (by norm_num)
theorem B789277 : Blo 654306 789277 := bbase (se 3 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 789277 = 295979) (by norm_num)
theorem B1477421 : Blo 654306 1477421 := bbase (se 3 (by rfl) ⟨277016, by rfl⟩ : syracuseStep 1477421 = 554033) (by norm_num)
theorem B985901 : Blo 654306 985901 := bbase (se 3 (by rfl) ⟨184856, by rfl⟩ : syracuseStep 985901 = 369713) (by norm_num)
theorem B985925 : Blo 654306 985925 := bbase (se 4 (by rfl) ⟨92430, by rfl⟩ : syracuseStep 985925 = 184861) (by norm_num)
theorem B985949 : Blo 654306 985949 := bbase (se 3 (by rfl) ⟨184865, by rfl⟩ : syracuseStep 985949 = 369731) (by norm_num)
theorem B1477493 : Blo 654306 1477493 := bbase (se 5 (by rfl) ⟨69257, by rfl⟩ : syracuseStep 1477493 = 138515) (by norm_num)
theorem B2493301 : Blo 654306 2493301 := bbase (se 5 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 2493301 = 233747) (by norm_num)
theorem B985973 : Blo 654306 985973 := bbase (se 5 (by rfl) ⟨46217, by rfl⟩ : syracuseStep 985973 = 92435) (by norm_num)
theorem B1051517 : Blo 654306 1051517 := bbase (se 3 (by rfl) ⟨197159, by rfl⟩ : syracuseStep 1051517 = 394319) (by norm_num)
theorem B985997 : Blo 654306 985997 := bbase (se 3 (by rfl) ⟨184874, by rfl⟩ : syracuseStep 985997 = 369749) (by norm_num)
theorem B986021 : Blo 654306 986021 := bbase (se 4 (by rfl) ⟨92439, by rfl⟩ : syracuseStep 986021 = 184879) (by norm_num)
theorem B756649 : Blo 654306 756649 := bbase (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) (by norm_num)
theorem B1477565 : Blo 654306 1477565 := bbase (se 3 (by rfl) ⟨277043, by rfl⟩ : syracuseStep 1477565 = 554087) (by norm_num)
theorem B986045 : Blo 654306 986045 := bbase (se 3 (by rfl) ⟨184883, by rfl⟩ : syracuseStep 986045 = 369767) (by norm_num)
theorem B986069 : Blo 654306 986069 := bbase (se 7 (by rfl) ⟨11555, by rfl⟩ : syracuseStep 986069 = 23111) (by norm_num)
theorem B986093 : Blo 654306 986093 := bbase (se 3 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 986093 = 369785) (by norm_num)
theorem B1477637 : Blo 654306 1477637 := bbase (se 4 (by rfl) ⟨138528, by rfl⟩ : syracuseStep 1477637 = 277057) (by norm_num)
theorem B986117 : Blo 654306 986117 := bbase (se 4 (by rfl) ⟨92448, by rfl⟩ : syracuseStep 986117 = 184897) (by norm_num)
theorem B986141 : Blo 654306 986141 := bbase (se 3 (by rfl) ⟨184901, by rfl⟩ : syracuseStep 986141 = 369803) (by norm_num)
theorem B986165 : Blo 654306 986165 := bbase (se 5 (by rfl) ⟨46226, by rfl⟩ : syracuseStep 986165 = 92453) (by norm_num)
theorem B756797 : Blo 654306 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B1477709 : Blo 654306 1477709 := bbase (se 3 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 1477709 = 554141) (by norm_num)
theorem B986189 : Blo 654306 986189 := bbase (se 3 (by rfl) ⟨184910, by rfl⟩ : syracuseStep 986189 = 369821) (by norm_num)
theorem B1870933 : Blo 654306 1870933 := bbase (se 8 (by rfl) ⟨10962, by rfl⟩ : syracuseStep 1870933 = 21925) (by norm_num)
theorem B986213 : Blo 654306 986213 := bbase (se 4 (by rfl) ⟨92457, by rfl⟩ : syracuseStep 986213 = 184915) (by norm_num)
theorem B986237 : Blo 654306 986237 := bbase (se 3 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 986237 = 369839) (by norm_num)
theorem B1477781 : Blo 654306 1477781 := bbase (se 6 (by rfl) ⟨34635, by rfl⟩ : syracuseStep 1477781 = 69271) (by norm_num)
theorem B986261 : Blo 654306 986261 := bbase (se 6 (by rfl) ⟨23115, by rfl⟩ : syracuseStep 986261 = 46231) (by norm_num)
theorem B1576093 : Blo 654306 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B1051805 : Blo 654306 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B2493605 : Blo 654306 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B986285 : Blo 654306 986285 := bbase (se 3 (by rfl) ⟨184928, by rfl⟩ : syracuseStep 986285 = 369857) (by norm_num)
theorem B986309 : Blo 654306 986309 := bbase (se 4 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 986309 = 184933) (by norm_num)
theorem B1477853 : Blo 654306 1477853 := bbase (se 3 (by rfl) ⟨277097, by rfl⟩ : syracuseStep 1477853 = 554195) (by norm_num)
theorem B986333 : Blo 654306 986333 := bbase (se 3 (by rfl) ⟨184937, by rfl⟩ : syracuseStep 986333 = 369875) (by norm_num)
theorem B1871093 : Blo 654306 1871093 := bbase (se 5 (by rfl) ⟨87707, by rfl⟩ : syracuseStep 1871093 = 175415) (by norm_num)
theorem B986357 : Blo 654306 986357 := bbase (se 5 (by rfl) ⟨46235, by rfl⟩ : syracuseStep 986357 = 92471) (by norm_num)
theorem B986381 : Blo 654306 986381 := bbase (se 3 (by rfl) ⟨184946, by rfl⟩ : syracuseStep 986381 = 369893) (by norm_num)
theorem B1477925 : Blo 654306 1477925 := bbase (se 4 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 1477925 = 277111) (by norm_num)
theorem B986405 : Blo 654306 986405 := bbase (se 4 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 986405 = 184951) (by norm_num)
theorem B986429 : Blo 654306 986429 := bbase (se 3 (by rfl) ⟨184955, by rfl⟩ : syracuseStep 986429 = 369911) (by norm_num)
theorem B986453 : Blo 654306 986453 := bbase (se 11 (by rfl) ⟨722, by rfl⟩ : syracuseStep 986453 = 1445) (by norm_num)
theorem B888157 : Blo 654306 888157 := bbase (se 3 (by rfl) ⟨166529, by rfl⟩ : syracuseStep 888157 = 333059) (by norm_num)
theorem B1477997 : Blo 654306 1477997 := bbase (se 3 (by rfl) ⟨277124, by rfl⟩ : syracuseStep 1477997 = 554249) (by norm_num)
theorem B986477 : Blo 654306 986477 := bbase (se 3 (by rfl) ⟨184964, by rfl⟩ : syracuseStep 986477 = 369929) (by norm_num)
theorem B986501 : Blo 654306 986501 := bbase (se 4 (by rfl) ⟨92484, by rfl⟩ : syracuseStep 986501 = 184969) (by norm_num)
theorem B986525 : Blo 654306 986525 := bbase (se 3 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 986525 = 369947) (by norm_num)
theorem B3313061 : Blo 654306 3313061 := bbase (se 4 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 3313061 = 621199) (by norm_num)
theorem B1478069 : Blo 654306 1478069 := bbase (se 5 (by rfl) ⟨69284, by rfl⟩ : syracuseStep 1478069 = 138569) (by norm_num)
theorem B986549 : Blo 654306 986549 := bbase (se 5 (by rfl) ⟨46244, by rfl⟩ : syracuseStep 986549 = 92489) (by norm_num)
theorem B1248709 : Blo 654306 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B986573 : Blo 654306 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B855517 : Blo 654306 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B1871333 : Blo 654306 1871333 := bbase (se 4 (by rfl) ⟨175437, by rfl⟩ : syracuseStep 1871333 = 350875) (by norm_num)
theorem B986597 : Blo 654306 986597 := bbase (se 4 (by rfl) ⟨92493, by rfl⟩ : syracuseStep 986597 = 184987) (by norm_num)
theorem B1478141 : Blo 654306 1478141 := bbase (se 3 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 1478141 = 554303) (by norm_num)
theorem B986621 : Blo 654306 986621 := bbase (se 3 (by rfl) ⟨184991, by rfl⟩ : syracuseStep 986621 = 369983) (by norm_num)
theorem B986645 : Blo 654306 986645 := bbase (se 6 (by rfl) ⟨23124, by rfl⟩ : syracuseStep 986645 = 46249) (by norm_num)
theorem B986669 : Blo 654306 986669 := bbase (se 3 (by rfl) ⟨185000, by rfl⟩ : syracuseStep 986669 = 370001) (by norm_num)
theorem B1478213 : Blo 654306 1478213 := bbase (se 4 (by rfl) ⟨138582, by rfl⟩ : syracuseStep 1478213 = 277165) (by norm_num)
theorem B986693 : Blo 654306 986693 := bbase (se 4 (by rfl) ⟨92502, by rfl⟩ : syracuseStep 986693 = 185005) (by norm_num)
theorem B1248853 : Blo 654306 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B986717 : Blo 654306 986717 := bbase (se 3 (by rfl) ⟨185009, by rfl⟩ : syracuseStep 986717 = 370019) (by norm_num)
theorem B2100853 : Blo 654306 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B986741 : Blo 654306 986741 := bbase (se 5 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 986741 = 92507) (by norm_num)
theorem B1478285 : Blo 654306 1478285 := bbase (se 3 (by rfl) ⟨277178, by rfl⟩ : syracuseStep 1478285 = 554357) (by norm_num)
theorem B986765 : Blo 654306 986765 := bbase (se 3 (by rfl) ⟨185018, by rfl⟩ : syracuseStep 986765 = 370037) (by norm_num)
theorem B790165 : Blo 654306 790165 := bbase (se 6 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 790165 = 37039) (by norm_num)
theorem B1871525 : Blo 654306 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B986789 : Blo 654306 986789 := bbase (se 4 (by rfl) ⟨92511, by rfl⟩ : syracuseStep 986789 = 185023) (by norm_num)
theorem B986813 : Blo 654306 986813 := bbase (se 3 (by rfl) ⟨185027, by rfl⟩ : syracuseStep 986813 = 370055) (by norm_num)
theorem B1478357 : Blo 654306 1478357 := bbase (se 7 (by rfl) ⟨17324, by rfl⟩ : syracuseStep 1478357 = 34649) (by norm_num)
theorem B986837 : Blo 654306 986837 := bbase (se 7 (by rfl) ⟨11564, by rfl⟩ : syracuseStep 986837 = 23129) (by norm_num)
theorem B986861 : Blo 654306 986861 := bbase (se 3 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 986861 = 370073) (by norm_num)
theorem B1249013 : Blo 654306 1249013 := bbase (se 5 (by rfl) ⟨58547, by rfl⟩ : syracuseStep 1249013 = 117095) (by norm_num)
theorem B1576709 : Blo 654306 1576709 := bbase (se 4 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 1576709 = 295633) (by norm_num)
theorem B986885 : Blo 654306 986885 := bbase (se 4 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 986885 = 185041) (by norm_num)
theorem B1478429 : Blo 654306 1478429 := bbase (se 3 (by rfl) ⟨277205, by rfl⟩ : syracuseStep 1478429 = 554411) (by norm_num)
theorem B986909 : Blo 654306 986909 := bbase (se 3 (by rfl) ⟨185045, by rfl⟩ : syracuseStep 986909 = 370091) (by norm_num)
theorem B986933 : Blo 654306 986933 := bbase (se 5 (by rfl) ⟨46262, by rfl⟩ : syracuseStep 986933 = 92525) (by norm_num)
theorem B986957 : Blo 654306 986957 := bbase (se 3 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 986957 = 370109) (by norm_num)
theorem B1478501 : Blo 654306 1478501 := bbase (se 4 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 1478501 = 277219) (by norm_num)
theorem B986981 : Blo 654306 986981 := bbase (se 4 (by rfl) ⟨92529, by rfl⟩ : syracuseStep 986981 = 185059) (by norm_num)
theorem B757621 : Blo 654306 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B987005 : Blo 654306 987005 := bbase (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) (by norm_num)
theorem B2527109 : Blo 654306 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1249157 : Blo 654306 1249157 := bbase (se 4 (by rfl) ⟨117108, by rfl⟩ : syracuseStep 1249157 = 234217) (by norm_num)
theorem B987029 : Blo 654306 987029 := bbase (se 6 (by rfl) ⟨23133, by rfl⟩ : syracuseStep 987029 = 46267) (by norm_num)
theorem B1478573 : Blo 654306 1478573 := bbase (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) (by norm_num)
theorem B987053 : Blo 654306 987053 := bbase (se 3 (by rfl) ⟨185072, by rfl⟩ : syracuseStep 987053 = 370145) (by norm_num)
theorem B1052605 : Blo 654306 1052605 := bbase (se 3 (by rfl) ⟨197363, by rfl⟩ : syracuseStep 1052605 = 394727) (by norm_num)
theorem B987077 : Blo 654306 987077 := bbase (se 4 (by rfl) ⟨92538, by rfl⟩ : syracuseStep 987077 = 185077) (by norm_num)
theorem B987101 : Blo 654306 987101 := bbase (se 3 (by rfl) ⟨185081, by rfl⟩ : syracuseStep 987101 = 370163) (by norm_num)
theorem B1478645 : Blo 654306 1478645 := bbase (se 5 (by rfl) ⟨69311, by rfl⟩ : syracuseStep 1478645 = 138623) (by norm_num)
theorem B987125 : Blo 654306 987125 := bbase (se 5 (by rfl) ⟨46271, by rfl⟩ : syracuseStep 987125 = 92543) (by norm_num)
theorem B987149 : Blo 654306 987149 := bbase (se 3 (by rfl) ⟨185090, by rfl⟩ : syracuseStep 987149 = 370181) (by norm_num)
theorem B987173 : Blo 654306 987173 := bbase (se 4 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 987173 = 185095) (by norm_num)
theorem B1478717 : Blo 654306 1478717 := bbase (se 3 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 1478717 = 554519) (by norm_num)
theorem B987197 : Blo 654306 987197 := bbase (se 3 (by rfl) ⟨185099, by rfl⟩ : syracuseStep 987197 = 370199) (by norm_num)
theorem B987221 : Blo 654306 987221 := bbase (se 8 (by rfl) ⟨5784, by rfl⟩ : syracuseStep 987221 = 11569) (by norm_num)
theorem B987245 : Blo 654306 987245 := bbase (se 3 (by rfl) ⟨185108, by rfl⟩ : syracuseStep 987245 = 370217) (by norm_num)
theorem B1478789 : Blo 654306 1478789 := bbase (se 4 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 1478789 = 277273) (by norm_num)
theorem B987269 : Blo 654306 987269 := bbase (se 4 (by rfl) ⟨92556, by rfl⟩ : syracuseStep 987269 = 185113) (by norm_num)
theorem B987293 : Blo 654306 987293 := bbase (se 3 (by rfl) ⟨185117, by rfl⟩ : syracuseStep 987293 = 370235) (by norm_num)
theorem B1249445 : Blo 654306 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B987317 : Blo 654306 987317 := bbase (se 5 (by rfl) ⟨46280, by rfl⟩ : syracuseStep 987317 = 92561) (by norm_num)
theorem B1478861 : Blo 654306 1478861 := bbase (se 3 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 1478861 = 554573) (by norm_num)
theorem B987341 : Blo 654306 987341 := bbase (se 3 (by rfl) ⟨185126, by rfl⟩ : syracuseStep 987341 = 370253) (by norm_num)
theorem B8523989 : Blo 654306 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B889061 : Blo 654306 889061 := bbase (se 4 (by rfl) ⟨83349, by rfl⟩ : syracuseStep 889061 = 166699) (by norm_num)
theorem B987365 : Blo 654306 987365 := bbase (se 4 (by rfl) ⟨92565, by rfl⟩ : syracuseStep 987365 = 185131) (by norm_num)
theorem B987389 : Blo 654306 987389 := bbase (se 3 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 987389 = 370271) (by norm_num)
theorem B1478933 : Blo 654306 1478933 := bbase (se 6 (by rfl) ⟨34662, by rfl⟩ : syracuseStep 1478933 = 69325) (by norm_num)
theorem B987413 : Blo 654306 987413 := bbase (se 6 (by rfl) ⟨23142, by rfl⟩ : syracuseStep 987413 = 46285) (by norm_num)
theorem B987437 : Blo 654306 987437 := bbase (se 3 (by rfl) ⟨185144, by rfl⟩ : syracuseStep 987437 = 370289) (by norm_num)
theorem B1249597 : Blo 654306 1249597 := bbase (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) (by norm_num)
theorem B1773893 : Blo 654306 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B1479005 : Blo 654306 1479005 := bbase (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) (by norm_num)
theorem B1479077 : Blo 654306 1479077 := bbase (se 4 (by rfl) ⟨138663, by rfl⟩ : syracuseStep 1479077 = 277327) (by norm_num)
theorem B1348045 : Blo 654306 1348045 := bbase (se 3 (by rfl) ⟨252758, by rfl⟩ : syracuseStep 1348045 = 505517) (by norm_num)
theorem B1053157 : Blo 654306 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B1479149 : Blo 654306 1479149 := bbase (se 3 (by rfl) ⟨277340, by rfl⟩ : syracuseStep 1479149 = 554681) (by norm_num)
theorem B1577477 : Blo 654306 1577477 := bbase (se 4 (by rfl) ⟨147888, by rfl⟩ : syracuseStep 1577477 = 295777) (by norm_num)
theorem B1577485 : Blo 654306 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B1479221 : Blo 654306 1479221 := bbase (se 5 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 1479221 = 138677) (by norm_num)
theorem B1184341 : Blo 654306 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B1479293 : Blo 654306 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B1872517 : Blo 654306 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B3314357 : Blo 654306 3314357 := bbase (se 5 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 3314357 = 310721) (by norm_num)
theorem B1479365 : Blo 654306 1479365 := bbase (se 4 (by rfl) ⟨138690, by rfl⟩ : syracuseStep 1479365 = 277381) (by norm_num)
theorem B1053413 : Blo 654306 1053413 := bbase (se 4 (by rfl) ⟨98757, by rfl⟩ : syracuseStep 1053413 = 197515) (by norm_num)
theorem B1479437 : Blo 654306 1479437 := bbase (se 3 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 1479437 = 554789) (by norm_num)
theorem B1479509 : Blo 654306 1479509 := bbase (se 9 (by rfl) ⟨4334, by rfl⟩ : syracuseStep 1479509 = 8669) (by norm_num)
theorem B1479581 : Blo 654306 1479581 := bbase (se 3 (by rfl) ⟨277421, by rfl⟩ : syracuseStep 1479581 = 554843) (by norm_num)
theorem B2102213 : Blo 654306 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B1479653 : Blo 654306 1479653 := bbase (se 4 (by rfl) ⟨138717, by rfl⟩ : syracuseStep 1479653 = 277435) (by norm_num)
theorem B3085285 : Blo 654306 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B1479725 : Blo 654306 1479725 := bbase (se 3 (by rfl) ⟨277448, by rfl⟩ : syracuseStep 1479725 = 554897) (by norm_num)
theorem B1479797 : Blo 654306 1479797 := bbase (se 5 (by rfl) ⟨69365, by rfl⟩ : syracuseStep 1479797 = 138731) (by norm_num)
theorem B1479869 : Blo 654306 1479869 := bbase (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) (by norm_num)
theorem B2495717 : Blo 654306 2495717 := bbase (se 4 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 2495717 = 467947) (by norm_num)
theorem B1479941 : Blo 654306 1479941 := bbase (se 4 (by rfl) ⟨138744, by rfl⟩ : syracuseStep 1479941 = 277489) (by norm_num)
theorem B1578293 : Blo 654306 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1480013 : Blo 654306 1480013 := bbase (se 3 (by rfl) ⟨277502, by rfl⟩ : syracuseStep 1480013 = 555005) (by norm_num)
theorem B1480085 : Blo 654306 1480085 := bbase (se 6 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 1480085 = 69379) (by norm_num)
theorem B1054117 : Blo 654306 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B1480157 : Blo 654306 1480157 := bbase (se 3 (by rfl) ⟨277529, by rfl⟩ : syracuseStep 1480157 = 555059) (by norm_num)
theorem B2496005 : Blo 654306 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B1480229 : Blo 654306 1480229 := bbase (se 4 (by rfl) ⟨138771, by rfl⟩ : syracuseStep 1480229 = 277543) (by norm_num)
theorem B1480301 : Blo 654306 1480301 := bbase (se 3 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 1480301 = 555113) (by norm_num)
theorem B1185421 : Blo 654306 1185421 := bbase (se 3 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 1185421 = 444533) (by norm_num)
theorem B1480373 : Blo 654306 1480373 := bbase (se 5 (by rfl) ⟨69392, by rfl⟩ : syracuseStep 1480373 = 138785) (by norm_num)
theorem B1873621 : Blo 654306 1873621 := bbase (se 7 (by rfl) ⟨21956, by rfl⟩ : syracuseStep 1873621 = 43913) (by norm_num)
theorem B1185509 : Blo 654306 1185509 := bbase (se 4 (by rfl) ⟨111141, by rfl⟩ : syracuseStep 1185509 = 222283) (by norm_num)
theorem B1480445 : Blo 654306 1480445 := bbase (se 3 (by rfl) ⟨277583, by rfl⟩ : syracuseStep 1480445 = 555167) (by norm_num)
theorem B1185565 : Blo 654306 1185565 := bbase (se 3 (by rfl) ⟨222293, by rfl⟩ : syracuseStep 1185565 = 444587) (by norm_num)
theorem B1480517 : Blo 654306 1480517 := bbase (se 4 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 1480517 = 277597) (by norm_num)
theorem B1120133 : Blo 654306 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B1480589 : Blo 654306 1480589 := bbase (se 3 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 1480589 = 555221) (by norm_num)
theorem B3315653 : Blo 654306 3315653 := bbase (se 4 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 3315653 = 621685) (by norm_num)
theorem B2660309 : Blo 654306 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B1480661 : Blo 654306 1480661 := bbase (se 7 (by rfl) ⟨17351, by rfl⟩ : syracuseStep 1480661 = 34703) (by norm_num)
theorem B1480733 : Blo 654306 1480733 := bbase (se 3 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 1480733 = 555275) (by norm_num)
theorem B3151973 : Blo 654306 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B1480805 : Blo 654306 1480805 := bbase (se 4 (by rfl) ⟨138825, by rfl⟩ : syracuseStep 1480805 = 277651) (by norm_num)
theorem B1480877 : Blo 654306 1480877 := bbase (se 3 (by rfl) ⟨277664, by rfl⟩ : syracuseStep 1480877 = 555329) (by norm_num)
theorem B2463925 : Blo 654306 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B5314805 : Blo 654306 5314805 := bbase (se 5 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 5314805 = 498263) (by norm_num)
theorem B1480949 : Blo 654306 1480949 := bbase (se 5 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 1480949 = 138839) (by norm_num)
theorem B1481021 : Blo 654306 1481021 := bbase (se 3 (by rfl) ⟨277691, by rfl⟩ : syracuseStep 1481021 = 555383) (by norm_num)
theorem B1481093 : Blo 654306 1481093 := bbase (se 4 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 1481093 = 277705) (by norm_num)
theorem B1481165 : Blo 654306 1481165 := bbase (se 3 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 1481165 = 555437) (by norm_num)
theorem B2398805 : Blo 654306 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B2497189 : Blo 654306 2497189 := bbase (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) (by norm_num)
theorem B2497493 : Blo 654306 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B3316949 : Blo 654306 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B2661781 : Blo 654306 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B1416701 : Blo 654306 1416701 := bbase (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) (by norm_num)
theorem B2989781 : Blo 654306 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B3546965 : Blo 654306 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B4988789 : Blo 654306 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B2367413 : Blo 654306 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B1581061 : Blo 654306 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B2105621 : Blo 654306 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B3744053 : Blo 654306 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B3318245 : Blo 654306 3318245 := bbase (se 4 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 3318245 = 622171) (by norm_num)
theorem B1581581 : Blo 654306 1581581 := bbase (se 3 (by rfl) ⟨296546, by rfl⟩ : syracuseStep 1581581 = 593093) (by norm_num)
theorem B1581677 : Blo 654306 1581677 := bbase (se 3 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 1581677 = 593129) (by norm_num)
theorem B2663045 : Blo 654306 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B664237 : Blo 654306 664237 := bbase (se 3 (by rfl) ⟨124544, by rfl⟩ : syracuseStep 664237 = 249089) (by norm_num)
theorem B828245 : Blo 654306 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B828301 : Blo 654306 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B959413 : Blo 654306 959413 := bbase (se 5 (by rfl) ⟨44972, by rfl⟩ : syracuseStep 959413 = 89945) (by norm_num)
theorem B664529 : Blo 654306 664529 := bbase (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) (by norm_num)
theorem B828397 : Blo 654306 828397 := bbase (se 3 (by rfl) ⟨155324, by rfl⟩ : syracuseStep 828397 = 310649) (by norm_num)
theorem B2532485 : Blo 654306 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B828569 : Blo 654306 828569 := bbase (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) (by norm_num)
theorem B828625 : Blo 654306 828625 := bbase (se 2 (by rfl) ⟨310734, by rfl⟩ : syracuseStep 828625 = 621469) (by norm_num)
theorem B828721 : Blo 654306 828721 := bbase (se 2 (by rfl) ⟨310770, by rfl⟩ : syracuseStep 828721 = 621541) (by norm_num)
theorem B3745237 : Blo 654306 3745237 := bbase (se 7 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 3745237 = 87779) (by norm_num)
theorem B828893 : Blo 654306 828893 := bbase (se 3 (by rfl) ⟨155417, by rfl⟩ : syracuseStep 828893 = 310835) (by norm_num)
theorem B2368997 : Blo 654306 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B828949 : Blo 654306 828949 := bbase (se 6 (by rfl) ⟨19428, by rfl⟩ : syracuseStep 828949 = 38857) (by norm_num)
theorem B2106901 : Blo 654306 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B829045 : Blo 654306 829045 := bbase (se 5 (by rfl) ⟨38861, by rfl⟩ : syracuseStep 829045 = 77723) (by norm_num)
theorem B3319541 : Blo 654306 3319541 := bbase (se 5 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 3319541 = 311207) (by norm_num)
theorem B1419005 : Blo 654306 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B829217 : Blo 654306 829217 := bbase (se 2 (by rfl) ⟨310956, by rfl⟩ : syracuseStep 829217 = 621913) (by norm_num)
theorem B829273 : Blo 654306 829273 := bbase (se 2 (by rfl) ⟨310977, by rfl⟩ : syracuseStep 829273 = 621955) (by norm_num)
theorem B2795381 : Blo 654306 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B829369 : Blo 654306 829369 := bbase (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) (by norm_num)
theorem B829541 : Blo 654306 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B665705 : Blo 654306 665705 := bbase (se 2 (by rfl) ⟨249639, by rfl⟩ : syracuseStep 665705 = 499279) (by norm_num)
theorem B829597 : Blo 654306 829597 := bbase (se 3 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 829597 = 311099) (by norm_num)
theorem B829693 : Blo 654306 829693 := bbase (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) (by norm_num)
theorem B829865 : Blo 654306 829865 := bbase (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) (by norm_num)
theorem B829921 : Blo 654306 829921 := bbase (se 2 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 829921 = 622441) (by norm_num)
theorem B830017 : Blo 654306 830017 := bbase (se 2 (by rfl) ⟨311256, by rfl⟩ : syracuseStep 830017 = 622513) (by norm_num)
theorem B698969 : Blo 654306 698969 := bbase (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) (by norm_num)
theorem B666289 : Blo 654306 666289 := bbase (se 2 (by rfl) ⟨249858, by rfl⟩ : syracuseStep 666289 = 499717) (by norm_num)
theorem B3156661 : Blo 654306 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B830189 : Blo 654306 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B830245 : Blo 654306 830245 := bbase (se 4 (by rfl) ⟨77835, by rfl⟩ : syracuseStep 830245 = 155671) (by norm_num)
theorem B2796389 : Blo 654306 2796389 := bbase (se 4 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 2796389 = 524323) (by norm_num)
theorem B2108261 : Blo 654306 2108261 := bbase (se 4 (by rfl) ⟨197649, by rfl⟩ : syracuseStep 2108261 = 395299) (by norm_num)
theorem B830341 : Blo 654306 830341 := bbase (se 4 (by rfl) ⟨77844, by rfl⟩ : syracuseStep 830341 = 155689) (by norm_num)
theorem B2108389 : Blo 654306 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B3320837 : Blo 654306 3320837 := bbase (se 4 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 3320837 = 622657) (by norm_num)
theorem B699413 : Blo 654306 699413 := bbase (se 6 (by rfl) ⟨16392, by rfl⟩ : syracuseStep 699413 = 32785) (by norm_num)
theorem B830513 : Blo 654306 830513 := bbase (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) (by norm_num)
theorem B699473 : Blo 654306 699473 := bbase (se 2 (by rfl) ⟨262302, by rfl⟩ : syracuseStep 699473 = 524605) (by norm_num)
theorem B830569 : Blo 654306 830569 := bbase (se 2 (by rfl) ⟨311463, by rfl⟩ : syracuseStep 830569 = 622927) (by norm_num)
theorem B830665 : Blo 654306 830665 := bbase (se 2 (by rfl) ⟨311499, by rfl⟩ : syracuseStep 830665 = 622999) (by norm_num)
theorem B699601 : Blo 654306 699601 := bbase (se 2 (by rfl) ⟨262350, by rfl⟩ : syracuseStep 699601 = 524701) (by norm_num)
theorem B2108645 : Blo 654306 2108645 := bbase (se 4 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 2108645 = 395371) (by norm_num)
theorem B830837 : Blo 654306 830837 := bbase (se 5 (by rfl) ⟨38945, by rfl⟩ : syracuseStep 830837 = 77891) (by norm_num)
theorem B3747221 : Blo 654306 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B830893 : Blo 654306 830893 := bbase (se 3 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 830893 = 311585) (by norm_num)
theorem B830989 : Blo 654306 830989 := bbase (se 3 (by rfl) ⟨155810, by rfl⟩ : syracuseStep 830989 = 311621) (by norm_num)
theorem B667153 : Blo 654306 667153 := bbase (se 2 (by rfl) ⟨250182, by rfl⟩ : syracuseStep 667153 = 500365) (by norm_num)
theorem B700045 : Blo 654306 700045 := bbase (se 3 (by rfl) ⟨131258, by rfl⟩ : syracuseStep 700045 = 262517) (by norm_num)
theorem B831161 : Blo 654306 831161 := bbase (se 2 (by rfl) ⟨311685, by rfl⟩ : syracuseStep 831161 = 623371) (by norm_num)
theorem B798409 : Blo 654306 798409 := bbase (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) (by norm_num)
theorem B831217 : Blo 654306 831217 := bbase (se 2 (by rfl) ⟨311706, by rfl⟩ : syracuseStep 831217 = 623413) (by norm_num)
theorem B700165 : Blo 654306 700165 := bbase (se 4 (by rfl) ⟨65640, by rfl⟩ : syracuseStep 700165 = 131281) (by norm_num)
theorem B831313 : Blo 654306 831313 := bbase (se 2 (by rfl) ⟨311742, by rfl⟩ : syracuseStep 831313 = 623485) (by norm_num)
theorem B4206421 : Blo 654306 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B2666357 : Blo 654306 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B831485 : Blo 654306 831485 := bbase (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) (by norm_num)
theorem B700417 : Blo 654306 700417 := bbase (se 2 (by rfl) ⟨262656, by rfl⟩ : syracuseStep 700417 = 525313) (by norm_num)
theorem B700421 : Blo 654306 700421 := bbase (se 4 (by rfl) ⟨65664, by rfl⟩ : syracuseStep 700421 = 131329) (by norm_num)
theorem B831541 : Blo 654306 831541 := bbase (se 5 (by rfl) ⟨38978, by rfl⟩ : syracuseStep 831541 = 77957) (by norm_num)
theorem B5615669 : Blo 654306 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B831637 : Blo 654306 831637 := bbase (se 6 (by rfl) ⟨19491, by rfl⟩ : syracuseStep 831637 = 38983) (by norm_num)
theorem B798881 : Blo 654306 798881 := bbase (se 2 (by rfl) ⟨299580, by rfl⟩ : syracuseStep 798881 = 599161) (by norm_num)
theorem B3322133 : Blo 654306 3322133 := bbase (se 6 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 3322133 = 155725) (by norm_num)
theorem B799033 : Blo 654306 799033 := bbase (se 2 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 799033 = 599275) (by norm_num)
theorem B831809 : Blo 654306 831809 := bbase (se 2 (by rfl) ⟨311928, by rfl⟩ : syracuseStep 831809 = 623857) (by norm_num)
theorem B831865 : Blo 654306 831865 := bbase (se 2 (by rfl) ⟨311949, by rfl⟩ : syracuseStep 831865 = 623899) (by norm_num)
theorem B5681621 : Blo 654306 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B831961 : Blo 654306 831961 := bbase (se 2 (by rfl) ⟨311985, by rfl⟩ : syracuseStep 831961 = 623971) (by norm_num)
theorem B700985 : Blo 654306 700985 := bbase (se 2 (by rfl) ⟨262869, by rfl⟩ : syracuseStep 700985 = 525739) (by norm_num)
theorem B2798165 : Blo 654306 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B1684061 : Blo 654306 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B799345 : Blo 654306 799345 := bbase (se 2 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 799345 = 599509) (by norm_num)
theorem B832133 : Blo 654306 832133 := bbase (se 4 (by rfl) ⟨78012, by rfl⟩ : syracuseStep 832133 = 156025) (by norm_num)
theorem B2208437 : Blo 654306 2208437 := bbase (se 5 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 2208437 = 207041) (by norm_num)
theorem B832189 : Blo 654306 832189 := bbase (se 3 (by rfl) ⟨156035, by rfl⟩ : syracuseStep 832189 = 312071) (by norm_num)
theorem B701173 : Blo 654306 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B2372341 : Blo 654306 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B832285 : Blo 654306 832285 := bbase (se 3 (by rfl) ⟨156053, by rfl⟩ : syracuseStep 832285 = 312107) (by norm_num)
theorem B799621 : Blo 654306 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B2372485 : Blo 654306 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B832457 : Blo 654306 832457 := bbase (se 2 (by rfl) ⟨312171, by rfl⟩ : syracuseStep 832457 = 624343) (by norm_num)
theorem B832513 : Blo 654306 832513 := bbase (se 2 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 832513 = 624385) (by norm_num)
theorem B832609 : Blo 654306 832609 := bbase (se 2 (by rfl) ⟨312228, by rfl⟩ : syracuseStep 832609 = 624457) (by norm_num)
theorem B2208869 : Blo 654306 2208869 := bbase (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) (by norm_num)
theorem B832781 : Blo 654306 832781 := bbase (se 3 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 832781 = 312293) (by norm_num)
theorem B832837 : Blo 654306 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B832933 : Blo 654306 832933 := bbase (se 4 (by rfl) ⟨78087, by rfl⟩ : syracuseStep 832933 = 156175) (by norm_num)
theorem B2209301 : Blo 654306 2209301 := bbase (se 6 (by rfl) ⟨51780, by rfl⟩ : syracuseStep 2209301 = 103561) (by norm_num)
theorem B3323429 : Blo 654306 3323429 := bbase (se 4 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 3323429 = 623143) (by norm_num)
theorem B701993 : Blo 654306 701993 := bbase (se 2 (by rfl) ⟨263247, by rfl⟩ : syracuseStep 701993 = 526495) (by norm_num)
theorem B3192389 : Blo 654306 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B833105 : Blo 654306 833105 := bbase (se 2 (by rfl) ⟨312414, by rfl⟩ : syracuseStep 833105 = 624829) (by norm_num)
theorem B833161 : Blo 654306 833161 := bbase (se 2 (by rfl) ⟨312435, by rfl⟩ : syracuseStep 833161 = 624871) (by norm_num)
theorem B800401 : Blo 654306 800401 := bbase (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) (by norm_num)
theorem B931765 : Blo 654306 931765 := bbase (se 5 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 931765 = 87353) (by norm_num)
theorem B2996149 : Blo 654306 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B2209733 : Blo 654306 2209733 := bbase (se 4 (by rfl) ⟨207162, by rfl⟩ : syracuseStep 2209733 = 414325) (by norm_num)
theorem B2701253 : Blo 654306 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B702437 : Blo 654306 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B997469 : Blo 654306 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B931981 : Blo 654306 931981 := bbase (se 3 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 931981 = 349493) (by norm_num)
theorem B6305941 : Blo 654306 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B702685 : Blo 654306 702685 := bbase (se 3 (by rfl) ⟨131753, by rfl⟩ : syracuseStep 702685 = 263507) (by norm_num)
theorem B2210165 : Blo 654306 2210165 := bbase (se 5 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 2210165 = 207203) (by norm_num)
theorem B932357 : Blo 654306 932357 := bbase (se 4 (by rfl) ⟨87408, by rfl⟩ : syracuseStep 932357 = 174817) (by norm_num)
theorem B3160853 : Blo 654306 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B2210597 : Blo 654306 2210597 := bbase (se 4 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 2210597 = 414487) (by norm_num)
theorem B3324725 : Blo 654306 3324725 := bbase (se 5 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 3324725 = 311693) (by norm_num)
theorem B736105 : Blo 654306 736105 := bbase (se 2 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 736105 = 552079) (by norm_num)
theorem B736141 : Blo 654306 736141 := bbase (se 3 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 736141 = 276053) (by norm_num)
theorem B1424269 : Blo 654306 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B736177 : Blo 654306 736177 := bbase (se 2 (by rfl) ⟨276066, by rfl⟩ : syracuseStep 736177 = 552133) (by norm_num)
theorem B2702261 : Blo 654306 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B736213 : Blo 654306 736213 := bbase (se 7 (by rfl) ⟨8627, by rfl⟩ : syracuseStep 736213 = 17255) (by norm_num)
theorem B5618645 : Blo 654306 5618645 := bbase (se 7 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 5618645 = 131687) (by norm_num)
theorem B736249 : Blo 654306 736249 := bbase (se 2 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 736249 = 552187) (by norm_num)
theorem B736285 : Blo 654306 736285 := bbase (se 3 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 736285 = 276107) (by norm_num)
theorem B736321 : Blo 654306 736321 := bbase (se 2 (by rfl) ⟨276120, by rfl⟩ : syracuseStep 736321 = 552241) (by norm_num)
theorem B736357 : Blo 654306 736357 := bbase (se 4 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 736357 = 138067) (by norm_num)
theorem B736393 : Blo 654306 736393 := bbase (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) (by norm_num)
theorem B736429 : Blo 654306 736429 := bbase (se 3 (by rfl) ⟨138080, by rfl⟩ : syracuseStep 736429 = 276161) (by norm_num)
theorem B736465 : Blo 654306 736465 := bbase (se 2 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 736465 = 552349) (by norm_num)
theorem B11943125 : Blo 654306 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B2211029 : Blo 654306 2211029 := bbase (se 7 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 2211029 = 51821) (by norm_num)
theorem B736501 : Blo 654306 736501 := bbase (se 5 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 736501 = 69047) (by norm_num)
theorem B736537 : Blo 654306 736537 := bbase (se 2 (by rfl) ⟨276201, by rfl⟩ : syracuseStep 736537 = 552403) (by norm_num)
theorem B736573 : Blo 654306 736573 := bbase (se 3 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 736573 = 276215) (by norm_num)
theorem B736609 : Blo 654306 736609 := bbase (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) (by norm_num)
theorem B736645 : Blo 654306 736645 := bbase (se 4 (by rfl) ⟨69060, by rfl⟩ : syracuseStep 736645 = 138121) (by norm_num)
theorem B736681 : Blo 654306 736681 := bbase (se 2 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 736681 = 552511) (by norm_num)
theorem B736717 : Blo 654306 736717 := bbase (se 3 (by rfl) ⟨138134, by rfl⟩ : syracuseStep 736717 = 276269) (by norm_num)
theorem B998861 : Blo 654306 998861 := bbase (se 3 (by rfl) ⟨187286, by rfl⟩ : syracuseStep 998861 = 374573) (by norm_num)
theorem B4996565 : Blo 654306 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B1916389 : Blo 654306 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B736753 : Blo 654306 736753 := bbase (se 2 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 736753 = 552565) (by norm_num)
theorem B736789 : Blo 654306 736789 := bbase (se 6 (by rfl) ⟨17268, by rfl⟩ : syracuseStep 736789 = 34537) (by norm_num)
theorem B736825 : Blo 654306 736825 := bbase (se 2 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 736825 = 552619) (by norm_num)
theorem B736861 : Blo 654306 736861 := bbase (se 3 (by rfl) ⟨138161, by rfl⟩ : syracuseStep 736861 = 276323) (by norm_num)
theorem B736897 : Blo 654306 736897 := bbase (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) (by norm_num)
theorem B2211461 : Blo 654306 2211461 := bbase (se 4 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 2211461 = 414649) (by norm_num)
theorem B736933 : Blo 654306 736933 := bbase (se 4 (by rfl) ⟨69087, by rfl⟩ : syracuseStep 736933 = 138175) (by norm_num)
theorem B736969 : Blo 654306 736969 := bbase (se 2 (by rfl) ⟨276363, by rfl⟩ : syracuseStep 736969 = 552727) (by norm_num)
theorem B1261261 : Blo 654306 1261261 := bbase (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) (by norm_num)
theorem B737005 : Blo 654306 737005 := bbase (se 3 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 737005 = 276377) (by norm_num)
theorem B737041 : Blo 654306 737041 := bbase (se 2 (by rfl) ⟨276390, by rfl⟩ : syracuseStep 737041 = 552781) (by norm_num)
theorem B1326869 : Blo 654306 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B737077 : Blo 654306 737077 := bbase (se 5 (by rfl) ⟨34550, by rfl⟩ : syracuseStep 737077 = 69101) (by norm_num)
theorem B1326917 : Blo 654306 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B737113 : Blo 654306 737113 := bbase (se 2 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 737113 = 552835) (by norm_num)
theorem B737149 : Blo 654306 737149 := bbase (se 3 (by rfl) ⟨138215, by rfl⟩ : syracuseStep 737149 = 276431) (by norm_num)
theorem B933781 : Blo 654306 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B737185 : Blo 654306 737185 := bbase (se 2 (by rfl) ⟨276444, by rfl⟩ : syracuseStep 737185 = 552889) (by norm_num)
theorem B737221 : Blo 654306 737221 := bbase (se 4 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 737221 = 138229) (by norm_num)
theorem B737257 : Blo 654306 737257 := bbase (se 2 (by rfl) ⟨276471, by rfl⟩ : syracuseStep 737257 = 552943) (by norm_num)
theorem B737293 : Blo 654306 737293 := bbase (se 3 (by rfl) ⟨138242, by rfl⟩ : syracuseStep 737293 = 276485) (by norm_num)
theorem B737329 : Blo 654306 737329 := bbase (se 2 (by rfl) ⟨276498, by rfl⟩ : syracuseStep 737329 = 552997) (by norm_num)
theorem B2211893 : Blo 654306 2211893 := bbase (se 5 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 2211893 = 207365) (by norm_num)
theorem B3326021 : Blo 654306 3326021 := bbase (se 4 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 3326021 = 623629) (by norm_num)
theorem B737365 : Blo 654306 737365 := bbase (se 8 (by rfl) ⟨4320, by rfl⟩ : syracuseStep 737365 = 8641) (by norm_num)
theorem B3162197 : Blo 654306 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B737401 : Blo 654306 737401 := bbase (se 2 (by rfl) ⟨276525, by rfl⟩ : syracuseStep 737401 = 553051) (by norm_num)
theorem B737437 : Blo 654306 737437 := bbase (se 3 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 737437 = 276539) (by norm_num)
theorem B737473 : Blo 654306 737473 := bbase (se 2 (by rfl) ⟨276552, by rfl⟩ : syracuseStep 737473 = 553105) (by norm_num)
theorem B737509 : Blo 654306 737509 := bbase (se 4 (by rfl) ⟨69141, by rfl⟩ : syracuseStep 737509 = 138283) (by norm_num)
theorem B737545 : Blo 654306 737545 := bbase (se 2 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 737545 = 553159) (by norm_num)
theorem B737581 : Blo 654306 737581 := bbase (se 3 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 737581 = 276593) (by norm_num)
theorem B737617 : Blo 654306 737617 := bbase (se 2 (by rfl) ⟨276606, by rfl⟩ : syracuseStep 737617 = 553213) (by norm_num)
theorem B737653 : Blo 654306 737653 := bbase (se 5 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 737653 = 69155) (by norm_num)
theorem B737689 : Blo 654306 737689 := bbase (se 2 (by rfl) ⟨276633, by rfl⟩ : syracuseStep 737689 = 553267) (by norm_num)
theorem B737725 : Blo 654306 737725 := bbase (se 3 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 737725 = 276647) (by norm_num)
theorem B737761 : Blo 654306 737761 := bbase (se 2 (by rfl) ⟨276660, by rfl⟩ : syracuseStep 737761 = 553321) (by norm_num)
theorem B2212325 : Blo 654306 2212325 := bbase (se 4 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 2212325 = 414811) (by norm_num)
theorem B934373 : Blo 654306 934373 := bbase (se 4 (by rfl) ⟨87597, by rfl⟩ : syracuseStep 934373 = 175195) (by norm_num)
theorem B737797 : Blo 654306 737797 := bbase (se 4 (by rfl) ⟨69168, by rfl⟩ : syracuseStep 737797 = 138337) (by norm_num)
theorem B737833 : Blo 654306 737833 := bbase (se 2 (by rfl) ⟨276687, by rfl⟩ : syracuseStep 737833 = 553375) (by norm_num)
theorem B934453 : Blo 654306 934453 := bbase (se 5 (by rfl) ⟨43802, by rfl⟩ : syracuseStep 934453 = 87605) (by norm_num)
theorem B737869 : Blo 654306 737869 := bbase (se 3 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 737869 = 276701) (by norm_num)
theorem B737905 : Blo 654306 737905 := bbase (se 2 (by rfl) ⟨276714, by rfl⟩ : syracuseStep 737905 = 553429) (by norm_num)
theorem B737941 : Blo 654306 737941 := bbase (se 6 (by rfl) ⟨17295, by rfl⟩ : syracuseStep 737941 = 34591) (by norm_num)
theorem B934573 : Blo 654306 934573 := bbase (se 3 (by rfl) ⟨175232, by rfl⟩ : syracuseStep 934573 = 350465) (by norm_num)
theorem B737977 : Blo 654306 737977 := bbase (se 2 (by rfl) ⟨276741, by rfl⟩ : syracuseStep 737977 = 553483) (by norm_num)
theorem B738013 : Blo 654306 738013 := bbase (se 3 (by rfl) ⟨138377, by rfl⟩ : syracuseStep 738013 = 276755) (by norm_num)
theorem B738049 : Blo 654306 738049 := bbase (se 2 (by rfl) ⟨276768, by rfl⟩ : syracuseStep 738049 = 553537) (by norm_num)
theorem B2802437 : Blo 654306 2802437 := bbase (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) (by norm_num)
theorem B934669 : Blo 654306 934669 := bbase (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) (by norm_num)
theorem B738085 : Blo 654306 738085 := bbase (se 4 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 738085 = 138391) (by norm_num)
theorem B738121 : Blo 654306 738121 := bbase (se 2 (by rfl) ⟨276795, by rfl⟩ : syracuseStep 738121 = 553591) (by norm_num)
theorem B738157 : Blo 654306 738157 := bbase (se 3 (by rfl) ⟨138404, by rfl⟩ : syracuseStep 738157 = 276809) (by norm_num)
theorem B738193 : Blo 654306 738193 := bbase (se 2 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 738193 = 553645) (by norm_num)
theorem B2212757 : Blo 654306 2212757 := bbase (se 6 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 2212757 = 103723) (by norm_num)
theorem B738229 : Blo 654306 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B738265 : Blo 654306 738265 := bbase (se 2 (by rfl) ⟨276849, by rfl⟩ : syracuseStep 738265 = 553699) (by norm_num)
theorem B738301 : Blo 654306 738301 := bbase (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) (by norm_num)
theorem B738337 : Blo 654306 738337 := bbase (se 2 (by rfl) ⟨276876, by rfl⟩ : syracuseStep 738337 = 553753) (by norm_num)
theorem B738373 : Blo 654306 738373 := bbase (se 4 (by rfl) ⟨69222, by rfl⟩ : syracuseStep 738373 = 138445) (by norm_num)
theorem B738409 : Blo 654306 738409 := bbase (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) (by norm_num)
theorem B2999429 : Blo 654306 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B738445 : Blo 654306 738445 := bbase (se 3 (by rfl) ⟨138458, by rfl⟩ : syracuseStep 738445 = 276917) (by norm_num)
theorem B1688741 : Blo 654306 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B738481 : Blo 654306 738481 := bbase (se 2 (by rfl) ⟨276930, by rfl⟩ : syracuseStep 738481 = 553861) (by norm_num)
theorem B738517 : Blo 654306 738517 := bbase (se 7 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 738517 = 17309) (by norm_num)
theorem B738553 : Blo 654306 738553 := bbase (se 2 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 738553 = 553915) (by norm_num)
theorem B935165 : Blo 654306 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B738589 : Blo 654306 738589 := bbase (se 3 (by rfl) ⟨138485, by rfl⟩ : syracuseStep 738589 = 276971) (by norm_num)
theorem B738625 : Blo 654306 738625 := bbase (se 2 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 738625 = 553969) (by norm_num)
theorem B2213189 : Blo 654306 2213189 := bbase (se 4 (by rfl) ⟨207486, by rfl⟩ : syracuseStep 2213189 = 414973) (by norm_num)
theorem B3327317 : Blo 654306 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B738661 : Blo 654306 738661 := bbase (se 4 (by rfl) ⟨69249, by rfl⟩ : syracuseStep 738661 = 138499) (by norm_num)
theorem B738697 : Blo 654306 738697 := bbase (se 2 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 738697 = 554023) (by norm_num)
theorem B738733 : Blo 654306 738733 := bbase (se 3 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 738733 = 277025) (by norm_num)
theorem B738769 : Blo 654306 738769 := bbase (se 2 (by rfl) ⟨277038, by rfl⟩ : syracuseStep 738769 = 554077) (by norm_num)
theorem B738805 : Blo 654306 738805 := bbase (se 5 (by rfl) ⟨34631, by rfl⟩ : syracuseStep 738805 = 69263) (by norm_num)
theorem B738841 : Blo 654306 738841 := bbase (se 2 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 738841 = 554131) (by norm_num)
theorem B5064245 : Blo 654306 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B738877 : Blo 654306 738877 := bbase (se 3 (by rfl) ⟨138539, by rfl⟩ : syracuseStep 738877 = 277079) (by norm_num)
theorem B1656389 : Blo 654306 1656389 := bbase (se 4 (by rfl) ⟨155286, by rfl⟩ : syracuseStep 1656389 = 310573) (by norm_num)
theorem B738913 : Blo 654306 738913 := bbase (se 2 (by rfl) ⟨277092, by rfl⟩ : syracuseStep 738913 = 554185) (by norm_num)
theorem B738949 : Blo 654306 738949 := bbase (se 4 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 738949 = 138553) (by norm_num)
theorem B738985 : Blo 654306 738985 := bbase (se 2 (by rfl) ⟨277119, by rfl⟩ : syracuseStep 738985 = 554239) (by norm_num)
theorem B673481 : Blo 654306 673481 := bbase (se 2 (by rfl) ⟨252555, by rfl⟩ : syracuseStep 673481 = 505111) (by norm_num)
theorem B739021 : Blo 654306 739021 := bbase (se 3 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 739021 = 277133) (by norm_num)
theorem B739057 : Blo 654306 739057 := bbase (se 2 (by rfl) ⟨277146, by rfl⟩ : syracuseStep 739057 = 554293) (by norm_num)
theorem B2213621 : Blo 654306 2213621 := bbase (se 5 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 2213621 = 207527) (by norm_num)
theorem B739093 : Blo 654306 739093 := bbase (se 6 (by rfl) ⟨17322, by rfl⟩ : syracuseStep 739093 = 34645) (by norm_num)
theorem B935717 : Blo 654306 935717 := bbase (se 4 (by rfl) ⟨87723, by rfl⟩ : syracuseStep 935717 = 175447) (by norm_num)
theorem B3360565 : Blo 654306 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B739129 : Blo 654306 739129 := bbase (se 2 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 739129 = 554347) (by norm_num)
theorem B739165 : Blo 654306 739165 := bbase (se 3 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 739165 = 277187) (by norm_num)
theorem B739201 : Blo 654306 739201 := bbase (se 2 (by rfl) ⟨277200, by rfl⟩ : syracuseStep 739201 = 554401) (by norm_num)
theorem B3000197 : Blo 654306 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B1656733 : Blo 654306 1656733 := bbase (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) (by norm_num)
theorem B739237 : Blo 654306 739237 := bbase (se 4 (by rfl) ⟨69303, by rfl⟩ : syracuseStep 739237 = 138607) (by norm_num)
theorem B739273 : Blo 654306 739273 := bbase (se 2 (by rfl) ⟨277227, by rfl⟩ : syracuseStep 739273 = 554455) (by norm_num)
theorem B739309 : Blo 654306 739309 := bbase (se 3 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 739309 = 277241) (by norm_num)
theorem B1656845 : Blo 654306 1656845 := bbase (se 3 (by rfl) ⟨310658, by rfl⟩ : syracuseStep 1656845 = 621317) (by norm_num)
theorem B739345 : Blo 654306 739345 := bbase (se 2 (by rfl) ⟨277254, by rfl⟩ : syracuseStep 739345 = 554509) (by norm_num)
theorem B1263653 : Blo 654306 1263653 := bbase (se 4 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 1263653 = 236935) (by norm_num)
theorem B739381 : Blo 654306 739381 := bbase (se 5 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 739381 = 69317) (by norm_num)
theorem B739417 : Blo 654306 739417 := bbase (se 2 (by rfl) ⟨277281, by rfl⟩ : syracuseStep 739417 = 554563) (by norm_num)
theorem B1329269 : Blo 654306 1329269 := bbase (se 5 (by rfl) ⟨62309, by rfl⟩ : syracuseStep 1329269 = 124619) (by norm_num)
theorem B739453 : Blo 654306 739453 := bbase (se 3 (by rfl) ⟨138647, by rfl⟩ : syracuseStep 739453 = 277295) (by norm_num)
theorem B739489 : Blo 654306 739489 := bbase (se 2 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 739489 = 554617) (by norm_num)
theorem B2214053 : Blo 654306 2214053 := bbase (se 4 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 2214053 = 415135) (by norm_num)
theorem B739525 : Blo 654306 739525 := bbase (se 4 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 739525 = 138661) (by norm_num)
theorem B1657037 : Blo 654306 1657037 := bbase (se 3 (by rfl) ⟨310694, by rfl⟩ : syracuseStep 1657037 = 621389) (by norm_num)
theorem B739561 : Blo 654306 739561 := bbase (se 2 (by rfl) ⟨277335, by rfl⟩ : syracuseStep 739561 = 554671) (by norm_num)
theorem B739597 : Blo 654306 739597 := bbase (se 3 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 739597 = 277349) (by norm_num)
theorem B739633 : Blo 654306 739633 := bbase (se 2 (by rfl) ⟨277362, by rfl⟩ : syracuseStep 739633 = 554725) (by norm_num)
theorem B739669 : Blo 654306 739669 := bbase (se 10 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 739669 = 2167) (by norm_num)
theorem B1493365 : Blo 654306 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B739705 : Blo 654306 739705 := bbase (se 2 (by rfl) ⟨277389, by rfl⟩ : syracuseStep 739705 = 554779) (by norm_num)
theorem B739741 : Blo 654306 739741 := bbase (se 3 (by rfl) ⟨138701, by rfl⟩ : syracuseStep 739741 = 277403) (by norm_num)
theorem B739777 : Blo 654306 739777 := bbase (se 2 (by rfl) ⟨277416, by rfl⟩ : syracuseStep 739777 = 554833) (by norm_num)
theorem B739813 : Blo 654306 739813 := bbase (se 4 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 739813 = 138715) (by norm_num)
theorem B2804213 : Blo 654306 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B739849 : Blo 654306 739849 := bbase (se 2 (by rfl) ⟨277443, by rfl⟩ : syracuseStep 739849 = 554887) (by norm_num)
theorem B6736405 : Blo 654306 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B936469 : Blo 654306 936469 := bbase (se 6 (by rfl) ⟨21948, by rfl⟩ : syracuseStep 936469 = 43897) (by norm_num)
theorem B1657381 : Blo 654306 1657381 := bbase (se 4 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 1657381 = 310759) (by norm_num)
theorem B739885 : Blo 654306 739885 := bbase (se 3 (by rfl) ⟨138728, by rfl⟩ : syracuseStep 739885 = 277457) (by norm_num)
theorem B739921 : Blo 654306 739921 := bbase (se 2 (by rfl) ⟨277470, by rfl⟩ : syracuseStep 739921 = 554941) (by norm_num)
theorem B2214485 : Blo 654306 2214485 := bbase (se 8 (by rfl) ⟨12975, by rfl⟩ : syracuseStep 2214485 = 25951) (by norm_num)
theorem B3328613 : Blo 654306 3328613 := bbase (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) (by norm_num)
theorem B739957 : Blo 654306 739957 := bbase (se 5 (by rfl) ⟨34685, by rfl⟩ : syracuseStep 739957 = 69371) (by norm_num)
theorem B1657493 : Blo 654306 1657493 := bbase (se 6 (by rfl) ⟨38847, by rfl⟩ : syracuseStep 1657493 = 77695) (by norm_num)
theorem B739993 : Blo 654306 739993 := bbase (se 2 (by rfl) ⟨277497, by rfl⟩ : syracuseStep 739993 = 554995) (by norm_num)
theorem B740029 : Blo 654306 740029 := bbase (se 3 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 740029 = 277511) (by norm_num)
theorem B740065 : Blo 654306 740065 := bbase (se 2 (by rfl) ⟨277524, by rfl⟩ : syracuseStep 740065 = 555049) (by norm_num)
theorem B2804453 : Blo 654306 2804453 := bbase (se 4 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 2804453 = 525835) (by norm_num)
theorem B740101 : Blo 654306 740101 := bbase (se 4 (by rfl) ⟨69384, by rfl⟩ : syracuseStep 740101 = 138769) (by norm_num)
theorem B740137 : Blo 654306 740137 := bbase (se 2 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 740137 = 555103) (by norm_num)
theorem B740173 : Blo 654306 740173 := bbase (se 3 (by rfl) ⟨138782, by rfl⟩ : syracuseStep 740173 = 277565) (by norm_num)
theorem B1657685 : Blo 654306 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B740209 : Blo 654306 740209 := bbase (se 2 (by rfl) ⟨277578, by rfl⟩ : syracuseStep 740209 = 555157) (by norm_num)
theorem B740245 : Blo 654306 740245 := bbase (se 6 (by rfl) ⟨17349, by rfl⟩ : syracuseStep 740245 = 34699) (by norm_num)
theorem B740281 : Blo 654306 740281 := bbase (se 2 (by rfl) ⟨277605, by rfl⟩ : syracuseStep 740281 = 555211) (by norm_num)
theorem B740317 : Blo 654306 740317 := bbase (se 3 (by rfl) ⟨138809, by rfl⟩ : syracuseStep 740317 = 277619) (by norm_num)
theorem B740353 : Blo 654306 740353 := bbase (se 2 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 740353 = 555265) (by norm_num)
theorem B2214917 : Blo 654306 2214917 := bbase (se 4 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 2214917 = 415297) (by norm_num)
theorem B4213781 : Blo 654306 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B740389 : Blo 654306 740389 := bbase (se 4 (by rfl) ⟨69411, by rfl⟩ : syracuseStep 740389 = 138823) (by norm_num)
theorem B740425 : Blo 654306 740425 := bbase (se 2 (by rfl) ⟨277659, by rfl⟩ : syracuseStep 740425 = 555319) (by norm_num)
theorem B740461 : Blo 654306 740461 := bbase (se 3 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 740461 = 277673) (by norm_num)
theorem B1264765 : Blo 654306 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B740497 : Blo 654306 740497 := bbase (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) (by norm_num)
theorem B1658029 : Blo 654306 1658029 := bbase (se 3 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 1658029 = 621761) (by norm_num)
theorem B740533 : Blo 654306 740533 := bbase (se 5 (by rfl) ⟨34712, by rfl⟩ : syracuseStep 740533 = 69425) (by norm_num)
theorem B740569 : Blo 654306 740569 := bbase (se 2 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 740569 = 555427) (by norm_num)
theorem B1658141 : Blo 654306 1658141 := bbase (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) (by norm_num)
theorem B937261 : Blo 654306 937261 := bbase (se 3 (by rfl) ⟨175736, by rfl⟩ : syracuseStep 937261 = 351473) (by norm_num)
theorem B1330549 : Blo 654306 1330549 := bbase (se 5 (by rfl) ⟨62369, by rfl⟩ : syracuseStep 1330549 = 124739) (by norm_num)
theorem B2248069 : Blo 654306 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B2215349 : Blo 654306 2215349 := bbase (se 5 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 2215349 = 207689) (by norm_num)
theorem B1658333 : Blo 654306 1658333 := bbase (se 3 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 1658333 = 621875) (by norm_num)
theorem B1068701 : Blo 654306 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B8113877 : Blo 654306 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B2248469 : Blo 654306 2248469 := bbase (se 6 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 2248469 = 105397) (by norm_num)
theorem B1658677 : Blo 654306 1658677 := bbase (se 5 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 1658677 = 155501) (by norm_num)
theorem B2215781 : Blo 654306 2215781 := bbase (se 4 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 2215781 = 415459) (by norm_num)
theorem B3329909 : Blo 654306 3329909 := bbase (se 5 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 3329909 = 312179) (by norm_num)
theorem B1658789 : Blo 654306 1658789 := bbase (se 4 (by rfl) ⟨155511, by rfl⟩ : syracuseStep 1658789 = 311023) (by norm_num)
theorem B970741 : Blo 654306 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B1495037 : Blo 654306 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1658981 : Blo 654306 1658981 := bbase (se 4 (by rfl) ⟨155529, by rfl⟩ : syracuseStep 1658981 = 311059) (by norm_num)
theorem B2216213 : Blo 654306 2216213 := bbase (se 6 (by rfl) ⟨51942, by rfl⟩ : syracuseStep 2216213 = 103885) (by norm_num)
theorem B840061 : Blo 654306 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B1659325 : Blo 654306 1659325 := bbase (se 3 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 1659325 = 622247) (by norm_num)
theorem B1331653 : Blo 654306 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B1659437 : Blo 654306 1659437 := bbase (se 3 (by rfl) ⟨311144, by rfl⟩ : syracuseStep 1659437 = 622289) (by norm_num)
theorem B3986005 : Blo 654306 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B2249381 : Blo 654306 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B2216645 : Blo 654306 2216645 := bbase (se 4 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 2216645 = 415621) (by norm_num)
theorem B1659629 : Blo 654306 1659629 := bbase (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) (by norm_num)
theorem B2806741 : Blo 654306 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B1659973 : Blo 654306 1659973 := bbase (se 4 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 1659973 = 311245) (by norm_num)
theorem B2217077 : Blo 654306 2217077 := bbase (se 5 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 2217077 = 207851) (by norm_num)
theorem B2249845 : Blo 654306 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B3331205 : Blo 654306 3331205 := bbase (se 4 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 3331205 = 624601) (by norm_num)
theorem B1660085 : Blo 654306 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1397989 : Blo 654306 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B840973 : Blo 654306 840973 := bbase (se 3 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 840973 = 315365) (by norm_num)
theorem B1660277 : Blo 654306 1660277 := bbase (se 5 (by rfl) ⟨77825, by rfl⟩ : syracuseStep 1660277 = 155651) (by norm_num)
theorem B3364325 : Blo 654306 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B1332749 : Blo 654306 1332749 := bbase (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) (by norm_num)
theorem B2217509 : Blo 654306 2217509 := bbase (se 4 (by rfl) ⟨207891, by rfl⟩ : syracuseStep 2217509 = 415783) (by norm_num)
theorem B1660621 : Blo 654306 1660621 := bbase (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) (by norm_num)
theorem B1398485 : Blo 654306 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1660733 : Blo 654306 1660733 := bbase (se 3 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 1660733 = 622775) (by norm_num)
theorem B2217941 : Blo 654306 2217941 := bbase (se 7 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 2217941 = 51983) (by norm_num)
theorem B22763477 : Blo 654306 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B1660925 : Blo 654306 1660925 := bbase (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) (by norm_num)
theorem B4216981 : Blo 654306 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B1104205 : Blo 654306 1104205 := bbase (se 3 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 1104205 = 414077) (by norm_num)
theorem B1661269 : Blo 654306 1661269 := bbase (se 10 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 1661269 = 4867) (by norm_num)
theorem B2218373 : Blo 654306 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B3332501 : Blo 654306 3332501 := bbase (se 6 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 3332501 = 156211) (by norm_num)
theorem B1104293 : Blo 654306 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B2808229 : Blo 654306 2808229 := bbase (se 4 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 2808229 = 526543) (by norm_num)
theorem B2808245 : Blo 654306 2808245 := bbase (se 5 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 2808245 = 263273) (by norm_num)
theorem B1661381 : Blo 654306 1661381 := bbase (se 4 (by rfl) ⟨155754, by rfl⟩ : syracuseStep 1661381 = 311509) (by norm_num)
theorem B1104421 : Blo 654306 1104421 := bbase (se 4 (by rfl) ⟨103539, by rfl⟩ : syracuseStep 1104421 = 207079) (by norm_num)
theorem B1399373 : Blo 654306 1399373 := bbase (se 3 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 1399373 = 524765) (by norm_num)
theorem B5331541 : Blo 654306 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B1104509 : Blo 654306 1104509 := bbase (se 3 (by rfl) ⟨207095, by rfl⟩ : syracuseStep 1104509 = 414191) (by norm_num)
theorem B1661573 : Blo 654306 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B1399493 : Blo 654306 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B1891045 : Blo 654306 1891045 := bbase (se 4 (by rfl) ⟨177285, by rfl⟩ : syracuseStep 1891045 = 354571) (by norm_num)
theorem B1104637 : Blo 654306 1104637 := bbase (se 3 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 1104637 = 414239) (by norm_num)
theorem B2218805 : Blo 654306 2218805 := bbase (se 5 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 2218805 = 208013) (by norm_num)
theorem B1104725 : Blo 654306 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B842645 : Blo 654306 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B1104853 : Blo 654306 1104853 := bbase (se 7 (by rfl) ⟨12947, by rfl⟩ : syracuseStep 1104853 = 25895) (by norm_num)
theorem B1661917 : Blo 654306 1661917 := bbase (se 3 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 1661917 = 623219) (by norm_num)
theorem B1104941 : Blo 654306 1104941 := bbase (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) (by norm_num)
theorem B1662029 : Blo 654306 1662029 := bbase (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) (by norm_num)
theorem B1105069 : Blo 654306 1105069 := bbase (se 3 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 1105069 = 414401) (by norm_num)
theorem B842933 : Blo 654306 842933 := bbase (se 5 (by rfl) ⟨39512, by rfl⟩ : syracuseStep 842933 = 79025) (by norm_num)
theorem B2219237 : Blo 654306 2219237 := bbase (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) (by norm_num)
theorem B1105157 : Blo 654306 1105157 := bbase (se 4 (by rfl) ⟨103608, by rfl⟩ : syracuseStep 1105157 = 207217) (by norm_num)
theorem B1662221 : Blo 654306 1662221 := bbase (se 3 (by rfl) ⟨311666, by rfl⟩ : syracuseStep 1662221 = 623333) (by norm_num)
theorem B1400125 : Blo 654306 1400125 := bbase (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) (by norm_num)
theorem B1105285 : Blo 654306 1105285 := bbase (se 4 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 1105285 = 207241) (by norm_num)
theorem B5037461 : Blo 654306 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B1105373 : Blo 654306 1105373 := bbase (se 3 (by rfl) ⟨207257, by rfl⟩ : syracuseStep 1105373 = 414515) (by norm_num)
theorem B1990133 : Blo 654306 1990133 := bbase (se 5 (by rfl) ⟨93287, by rfl⟩ : syracuseStep 1990133 = 186575) (by norm_num)
theorem B1105501 : Blo 654306 1105501 := bbase (se 3 (by rfl) ⟨207281, by rfl⟩ : syracuseStep 1105501 = 414563) (by norm_num)
theorem B1662565 : Blo 654306 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B1793669 : Blo 654306 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B2219669 : Blo 654306 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B1105589 : Blo 654306 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B1662677 : Blo 654306 1662677 := bbase (se 7 (by rfl) ⟨19484, by rfl⟩ : syracuseStep 1662677 = 38969) (by norm_num)
theorem B843529 : Blo 654306 843529 := bbase (se 2 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 843529 = 632647) (by norm_num)
theorem B1105717 : Blo 654306 1105717 := bbase (se 5 (by rfl) ⟨51830, by rfl⟩ : syracuseStep 1105717 = 103661) (by norm_num)
theorem B1892165 : Blo 654306 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1105805 : Blo 654306 1105805 := bbase (se 3 (by rfl) ⟨207338, by rfl⟩ : syracuseStep 1105805 = 414677) (by norm_num)
theorem B1662869 : Blo 654306 1662869 := bbase (se 6 (by rfl) ⟨38973, by rfl⟩ : syracuseStep 1662869 = 77947) (by norm_num)
theorem B1105933 : Blo 654306 1105933 := bbase (se 3 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 1105933 = 414725) (by norm_num)
theorem B2220101 : Blo 654306 2220101 := bbase (se 4 (by rfl) ⟨208134, by rfl⟩ : syracuseStep 2220101 = 416269) (by norm_num)
theorem B1106021 : Blo 654306 1106021 := bbase (se 4 (by rfl) ⟨103689, by rfl⟩ : syracuseStep 1106021 = 207379) (by norm_num)
theorem B1401013 : Blo 654306 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1106149 : Blo 654306 1106149 := bbase (se 4 (by rfl) ⟨103701, by rfl⟩ : syracuseStep 1106149 = 207403) (by norm_num)
theorem B1663213 : Blo 654306 1663213 := bbase (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) (by norm_num)
theorem B1401133 : Blo 654306 1401133 := bbase (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) (by norm_num)
theorem B1106237 : Blo 654306 1106237 := bbase (se 3 (by rfl) ⟨207419, by rfl⟩ : syracuseStep 1106237 = 414839) (by norm_num)
theorem B1663325 : Blo 654306 1663325 := bbase (se 3 (by rfl) ⟨311873, by rfl⟩ : syracuseStep 1663325 = 623747) (by norm_num)
theorem B1106365 : Blo 654306 1106365 := bbase (se 3 (by rfl) ⟨207443, by rfl⟩ : syracuseStep 1106365 = 414887) (by norm_num)
theorem B2220533 : Blo 654306 2220533 := bbase (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) (by norm_num)
theorem B1106453 : Blo 654306 1106453 := bbase (se 6 (by rfl) ⟨25932, by rfl⟩ : syracuseStep 1106453 = 51865) (by norm_num)
theorem B1663517 : Blo 654306 1663517 := bbase (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) (by norm_num)
theorem B1401389 : Blo 654306 1401389 := bbase (se 3 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 1401389 = 525521) (by norm_num)
theorem B2810501 : Blo 654306 2810501 := bbase (se 4 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 2810501 = 526969) (by norm_num)
theorem B1106581 : Blo 654306 1106581 := bbase (se 6 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 1106581 = 51871) (by norm_num)
theorem B4973237 : Blo 654306 4973237 := bbase (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) (by norm_num)
theorem B746209 : Blo 654306 746209 := bbase (se 2 (by rfl) ⟨279828, by rfl⟩ : syracuseStep 746209 = 559657) (by norm_num)
theorem B1106669 : Blo 654306 1106669 := bbase (se 3 (by rfl) ⟨207500, by rfl⟩ : syracuseStep 1106669 = 415001) (by norm_num)
theorem B1106797 : Blo 654306 1106797 := bbase (se 3 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 1106797 = 415049) (by norm_num)
theorem B1663861 : Blo 654306 1663861 := bbase (se 5 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 1663861 = 155987) (by norm_num)
theorem B2220965 : Blo 654306 2220965 := bbase (se 4 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 2220965 = 416431) (by norm_num)
theorem B1106885 : Blo 654306 1106885 := bbase (se 4 (by rfl) ⟨103770, by rfl⟩ : syracuseStep 1106885 = 207541) (by norm_num)
theorem B1663973 : Blo 654306 1663973 := bbase (se 4 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 1663973 = 311995) (by norm_num)
theorem B1107013 : Blo 654306 1107013 := bbase (se 4 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 1107013 = 207565) (by norm_num)
theorem B1107101 : Blo 654306 1107101 := bbase (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) (by norm_num)
theorem B1664165 : Blo 654306 1664165 := bbase (se 4 (by rfl) ⟨156015, by rfl⟩ : syracuseStep 1664165 = 312031) (by norm_num)
theorem B1107229 : Blo 654306 1107229 := bbase (se 3 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 1107229 = 415211) (by norm_num)
theorem B2221397 : Blo 654306 2221397 := bbase (se 12 (by rfl) ⟨813, by rfl⟩ : syracuseStep 2221397 = 1627) (by norm_num)
theorem B1107317 : Blo 654306 1107317 := bbase (se 5 (by rfl) ⟨51905, by rfl⟩ : syracuseStep 1107317 = 103811) (by norm_num)
theorem B1402277 : Blo 654306 1402277 := bbase (se 4 (by rfl) ⟨131463, by rfl⟩ : syracuseStep 1402277 = 262927) (by norm_num)
theorem B1107445 : Blo 654306 1107445 := bbase (se 5 (by rfl) ⟨51911, by rfl⟩ : syracuseStep 1107445 = 103823) (by norm_num)
theorem B1664509 : Blo 654306 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B681485 : Blo 654306 681485 := bbase (se 3 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 681485 = 255557) (by norm_num)
theorem B1107533 : Blo 654306 1107533 := bbase (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) (by norm_num)
theorem B1664621 : Blo 654306 1664621 := bbase (se 3 (by rfl) ⟨312116, by rfl⟩ : syracuseStep 1664621 = 624233) (by norm_num)
theorem B1402517 : Blo 654306 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B1107661 : Blo 654306 1107661 := bbase (se 3 (by rfl) ⟨207686, by rfl⟩ : syracuseStep 1107661 = 415373) (by norm_num)
theorem B1042157 : Blo 654306 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B1107749 : Blo 654306 1107749 := bbase (se 4 (by rfl) ⟨103851, by rfl⟩ : syracuseStep 1107749 = 207703) (by norm_num)
theorem B1664813 : Blo 654306 1664813 := bbase (se 3 (by rfl) ⟨312152, by rfl⟩ : syracuseStep 1664813 = 624305) (by norm_num)
theorem B1107877 : Blo 654306 1107877 := bbase (se 4 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 1107877 = 207727) (by norm_num)
theorem B1107965 : Blo 654306 1107965 := bbase (se 3 (by rfl) ⟨207743, by rfl⟩ : syracuseStep 1107965 = 415487) (by norm_num)
theorem B2484341 : Blo 654306 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B1108093 : Blo 654306 1108093 := bbase (se 3 (by rfl) ⟨207767, by rfl⟩ : syracuseStep 1108093 = 415535) (by norm_num)
theorem B1665157 : Blo 654306 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B1403021 : Blo 654306 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B1009813 : Blo 654306 1009813 := bbase (se 6 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 1009813 = 47335) (by norm_num)
theorem B1403029 : Blo 654306 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B1108181 : Blo 654306 1108181 := bbase (se 7 (by rfl) ⟨12986, by rfl⟩ : syracuseStep 1108181 = 25973) (by norm_num)
theorem B1665269 : Blo 654306 1665269 := bbase (se 5 (by rfl) ⟨78059, by rfl⟩ : syracuseStep 1665269 = 156119) (by norm_num)
theorem B1894661 : Blo 654306 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1108309 : Blo 654306 1108309 := bbase (se 10 (by rfl) ⟨1623, by rfl⟩ : syracuseStep 1108309 = 3247) (by norm_num)
theorem B747905 : Blo 654306 747905 := bbase (se 2 (by rfl) ⟨280464, by rfl⟩ : syracuseStep 747905 = 560929) (by norm_num)
theorem B1108397 : Blo 654306 1108397 := bbase (se 3 (by rfl) ⟨207824, by rfl⟩ : syracuseStep 1108397 = 415649) (by norm_num)
theorem B1665461 : Blo 654306 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B944605 : Blo 654306 944605 := bbase (se 3 (by rfl) ⟨177113, by rfl⟩ : syracuseStep 944605 = 354227) (by norm_num)
theorem B1108525 : Blo 654306 1108525 := bbase (se 3 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 1108525 = 415697) (by norm_num)
theorem B1108613 : Blo 654306 1108613 := bbase (se 4 (by rfl) ⟨103932, by rfl⟩ : syracuseStep 1108613 = 207865) (by norm_num)
theorem B1108741 : Blo 654306 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B1665805 : Blo 654306 1665805 := bbase (se 3 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 1665805 = 624677) (by norm_num)
theorem B1108829 : Blo 654306 1108829 := bbase (se 3 (by rfl) ⟨207905, by rfl⟩ : syracuseStep 1108829 = 415811) (by norm_num)
theorem B1665917 : Blo 654306 1665917 := bbase (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) (by norm_num)
theorem B1108957 : Blo 654306 1108957 := bbase (se 3 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 1108957 = 415859) (by norm_num)
theorem B1109045 : Blo 654306 1109045 := bbase (se 5 (by rfl) ⟨51986, by rfl⟩ : syracuseStep 1109045 = 103973) (by norm_num)
theorem B1666109 : Blo 654306 1666109 := bbase (se 3 (by rfl) ⟨312395, by rfl⟩ : syracuseStep 1666109 = 624791) (by norm_num)
theorem B748613 : Blo 654306 748613 := bbase (se 4 (by rfl) ⟨70182, by rfl⟩ : syracuseStep 748613 = 140365) (by norm_num)
theorem B912493 : Blo 654306 912493 := bbase (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) (by norm_num)
theorem B1109173 : Blo 654306 1109173 := bbase (se 5 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 1109173 = 103985) (by norm_num)
theorem B1404157 : Blo 654306 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B945413 : Blo 654306 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B1109261 : Blo 654306 1109261 := bbase (se 3 (by rfl) ⟨207986, by rfl⟩ : syracuseStep 1109261 = 415973) (by norm_num)
theorem B2485525 : Blo 654306 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B11201813 : Blo 654306 11201813 := bbase (se 6 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 11201813 = 525085) (by norm_num)
theorem B748873 : Blo 654306 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B1109389 : Blo 654306 1109389 := bbase (se 3 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 1109389 = 416021) (by norm_num)
theorem B748945 : Blo 654306 748945 := bbase (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) (by norm_num)
theorem B1011133 : Blo 654306 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1109477 : Blo 654306 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B2485829 : Blo 654306 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B1109605 : Blo 654306 1109605 := bbase (se 4 (by rfl) ⟨104025, by rfl⟩ : syracuseStep 1109605 = 208051) (by norm_num)
theorem B1404533 : Blo 654306 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B1109693 : Blo 654306 1109693 := bbase (se 3 (by rfl) ⟨208067, by rfl⟩ : syracuseStep 1109693 = 416135) (by norm_num)
theorem B1863461 : Blo 654306 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B1109821 : Blo 654306 1109821 := bbase (se 3 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 1109821 = 416183) (by norm_num)
theorem B1109909 : Blo 654306 1109909 := bbase (se 6 (by rfl) ⟨26013, by rfl⟩ : syracuseStep 1109909 = 52027) (by norm_num)
theorem B1110037 : Blo 654306 1110037 := bbase (se 6 (by rfl) ⟨26016, by rfl⟩ : syracuseStep 1110037 = 52033) (by norm_num)
theorem B1110125 : Blo 654306 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1110253 : Blo 654306 1110253 := bbase (se 3 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 1110253 = 416345) (by norm_num)
theorem B749821 : Blo 654306 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B1110341 : Blo 654306 1110341 := bbase (se 4 (by rfl) ⟨104094, by rfl⟩ : syracuseStep 1110341 = 208189) (by norm_num)
theorem B1438133 : Blo 654306 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B1110469 : Blo 654306 1110469 := bbase (se 4 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 1110469 = 208213) (by norm_num)
theorem B1110557 : Blo 654306 1110557 := bbase (se 3 (by rfl) ⟨208229, by rfl⟩ : syracuseStep 1110557 = 416459) (by norm_num)
theorem B1110685 : Blo 654306 1110685 := bbase (se 3 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 1110685 = 416507) (by norm_num)
theorem B1110773 : Blo 654306 1110773 := bbase (se 5 (by rfl) ⟨52067, by rfl⟩ : syracuseStep 1110773 = 104135) (by norm_num)
theorem B1865045 : Blo 654306 1865045 := bbase (se 13 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1865045 = 683) (by norm_num)
theorem B1898101 : Blo 654306 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B2487941 : Blo 654306 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B1472237 : Blo 654306 1472237 := bbase (se 3 (by rfl) ⟨276044, by rfl⟩ : syracuseStep 1472237 = 552089) (by norm_num)
theorem B1242877 : Blo 654306 1242877 := bbase (se 3 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 1242877 = 466079) (by norm_num)
theorem B1472309 : Blo 654306 1472309 := bbase (se 5 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 1472309 = 138029) (by norm_num)
theorem B1472381 : Blo 654306 1472381 := bbase (se 3 (by rfl) ⟨276071, by rfl⟩ : syracuseStep 1472381 = 552143) (by norm_num)
theorem B1243021 : Blo 654306 1243021 := bbase (se 3 (by rfl) ⟨233066, by rfl⟩ : syracuseStep 1243021 = 466133) (by norm_num)
theorem B2488229 : Blo 654306 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1472453 : Blo 654306 1472453 := bbase (se 4 (by rfl) ⟨138042, by rfl⟩ : syracuseStep 1472453 = 276085) (by norm_num)
theorem B1865717 : Blo 654306 1865717 := bbase (se 5 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 1865717 = 174911) (by norm_num)
theorem B1472525 : Blo 654306 1472525 := bbase (se 3 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 1472525 = 552197) (by norm_num)
theorem B1243181 : Blo 654306 1243181 := bbase (se 3 (by rfl) ⟨233096, by rfl⟩ : syracuseStep 1243181 = 466193) (by norm_num)
theorem B1472597 : Blo 654306 1472597 := bbase (se 8 (by rfl) ⟨8628, by rfl⟩ : syracuseStep 1472597 = 17257) (by norm_num)
theorem B1472669 : Blo 654306 1472669 := bbase (se 3 (by rfl) ⟨276125, by rfl⟩ : syracuseStep 1472669 = 552251) (by norm_num)
theorem B1243325 : Blo 654306 1243325 := bbase (se 3 (by rfl) ⟨233123, by rfl⟩ : syracuseStep 1243325 = 466247) (by norm_num)
theorem B1472741 : Blo 654306 1472741 := bbase (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) (by norm_num)
theorem B7469333 : Blo 654306 7469333 := bbase (se 6 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 7469333 = 350125) (by norm_num)
theorem B1472813 : Blo 654306 1472813 := bbase (se 3 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 1472813 = 552305) (by norm_num)
theorem B1472885 : Blo 654306 1472885 := bbase (se 5 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 1472885 = 138083) (by norm_num)
theorem B6322549 : Blo 654306 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B4192661 : Blo 654306 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B1866149 : Blo 654306 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B1472957 : Blo 654306 1472957 := bbase (se 3 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 1472957 = 552359) (by norm_num)
theorem B981461 : Blo 654306 981461 := bbase (se 7 (by rfl) ⟨11501, by rfl⟩ : syracuseStep 981461 = 23003) (by norm_num)
theorem B1243613 : Blo 654306 1243613 := bbase (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) (by norm_num)
theorem B981485 : Blo 654306 981485 := bbase (se 3 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 981485 = 368057) (by norm_num)
theorem B981509 : Blo 654306 981509 := bbase (se 4 (by rfl) ⟨92016, by rfl⟩ : syracuseStep 981509 = 184033) (by norm_num)
theorem B1473029 : Blo 654306 1473029 := bbase (se 4 (by rfl) ⟨138096, by rfl⟩ : syracuseStep 1473029 = 276193) (by norm_num)
theorem B981533 : Blo 654306 981533 := bbase (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) (by norm_num)
theorem B981557 : Blo 654306 981557 := bbase (se 5 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 981557 = 92021) (by norm_num)
theorem B981581 : Blo 654306 981581 := bbase (se 3 (by rfl) ⟨184046, by rfl⟩ : syracuseStep 981581 = 368093) (by norm_num)
theorem B1473101 : Blo 654306 1473101 := bbase (se 3 (by rfl) ⟨276206, by rfl⟩ : syracuseStep 1473101 = 552413) (by norm_num)
theorem B981605 : Blo 654306 981605 := bbase (se 4 (by rfl) ⟨92025, by rfl⟩ : syracuseStep 981605 = 184051) (by norm_num)
theorem B1243765 : Blo 654306 1243765 := bbase (se 5 (by rfl) ⟨58301, by rfl⟩ : syracuseStep 1243765 = 116603) (by norm_num)
theorem B981629 : Blo 654306 981629 := bbase (se 3 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 981629 = 368111) (by norm_num)
theorem B981653 : Blo 654306 981653 := bbase (se 6 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 981653 = 46015) (by norm_num)
theorem B1473173 : Blo 654306 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B981677 : Blo 654306 981677 := bbase (se 3 (by rfl) ⟨184064, by rfl⟩ : syracuseStep 981677 = 368129) (by norm_num)
theorem B981701 : Blo 654306 981701 := bbase (se 4 (by rfl) ⟨92034, by rfl⟩ : syracuseStep 981701 = 184069) (by norm_num)
theorem B981725 : Blo 654306 981725 := bbase (se 3 (by rfl) ⟨184073, by rfl⟩ : syracuseStep 981725 = 368147) (by norm_num)
theorem B1473245 : Blo 654306 1473245 := bbase (se 3 (by rfl) ⟨276233, by rfl⟩ : syracuseStep 1473245 = 552467) (by norm_num)
theorem B981749 : Blo 654306 981749 := bbase (se 5 (by rfl) ⟨46019, by rfl⟩ : syracuseStep 981749 = 92039) (by norm_num)
theorem B981773 : Blo 654306 981773 := bbase (se 3 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 981773 = 368165) (by norm_num)
theorem B981797 : Blo 654306 981797 := bbase (se 4 (by rfl) ⟨92043, by rfl⟩ : syracuseStep 981797 = 184087) (by norm_num)
theorem B1473317 : Blo 654306 1473317 := bbase (se 4 (by rfl) ⟨138123, by rfl⟩ : syracuseStep 1473317 = 276247) (by norm_num)
theorem B981821 : Blo 654306 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B981845 : Blo 654306 981845 := bbase (se 9 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 981845 = 5753) (by norm_num)
theorem B981869 : Blo 654306 981869 := bbase (se 3 (by rfl) ⟨184100, by rfl⟩ : syracuseStep 981869 = 368201) (by norm_num)
theorem B1473389 : Blo 654306 1473389 := bbase (se 3 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 1473389 = 552521) (by norm_num)
theorem B981893 : Blo 654306 981893 := bbase (se 4 (by rfl) ⟨92052, by rfl⟩ : syracuseStep 981893 = 184105) (by norm_num)
theorem B981917 : Blo 654306 981917 := bbase (se 3 (by rfl) ⟨184109, by rfl⟩ : syracuseStep 981917 = 368219) (by norm_num)
theorem B1244069 : Blo 654306 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B981941 : Blo 654306 981941 := bbase (se 5 (by rfl) ⟨46028, by rfl⟩ : syracuseStep 981941 = 92057) (by norm_num)
theorem B1473461 : Blo 654306 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B981965 : Blo 654306 981965 := bbase (se 3 (by rfl) ⟨184118, by rfl⟩ : syracuseStep 981965 = 368237) (by norm_num)
theorem B981989 : Blo 654306 981989 := bbase (se 4 (by rfl) ⟨92061, by rfl⟩ : syracuseStep 981989 = 184123) (by norm_num)
theorem B982013 : Blo 654306 982013 := bbase (se 3 (by rfl) ⟨184127, by rfl⟩ : syracuseStep 982013 = 368255) (by norm_num)
theorem B1473533 : Blo 654306 1473533 := bbase (se 3 (by rfl) ⟨276287, by rfl⟩ : syracuseStep 1473533 = 552575) (by norm_num)
theorem B982037 : Blo 654306 982037 := bbase (se 6 (by rfl) ⟨23016, by rfl⟩ : syracuseStep 982037 = 46033) (by norm_num)
theorem B982061 : Blo 654306 982061 := bbase (se 3 (by rfl) ⟨184136, by rfl⟩ : syracuseStep 982061 = 368273) (by norm_num)
theorem B982085 : Blo 654306 982085 := bbase (se 4 (by rfl) ⟨92070, by rfl⟩ : syracuseStep 982085 = 184141) (by norm_num)
theorem B1473605 : Blo 654306 1473605 := bbase (se 4 (by rfl) ⟨138150, by rfl⟩ : syracuseStep 1473605 = 276301) (by norm_num)
theorem B2489413 : Blo 654306 2489413 := bbase (se 4 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 2489413 = 466765) (by norm_num)
theorem B1997893 : Blo 654306 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B982109 : Blo 654306 982109 := bbase (se 3 (by rfl) ⟨184145, by rfl⟩ : syracuseStep 982109 = 368291) (by norm_num)
theorem B982133 : Blo 654306 982133 := bbase (se 5 (by rfl) ⟨46037, by rfl⟩ : syracuseStep 982133 = 92075) (by norm_num)
theorem B982157 : Blo 654306 982157 := bbase (se 3 (by rfl) ⟨184154, by rfl⟩ : syracuseStep 982157 = 368309) (by norm_num)
theorem B1473677 : Blo 654306 1473677 := bbase (se 3 (by rfl) ⟨276314, by rfl⟩ : syracuseStep 1473677 = 552629) (by norm_num)
theorem B2522261 : Blo 654306 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B1866901 : Blo 654306 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B982181 : Blo 654306 982181 := bbase (se 4 (by rfl) ⟨92079, by rfl⟩ : syracuseStep 982181 = 184159) (by norm_num)
theorem B982205 : Blo 654306 982205 := bbase (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) (by norm_num)
theorem B1768661 : Blo 654306 1768661 := bbase (se 7 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 1768661 = 41453) (by norm_num)
theorem B982229 : Blo 654306 982229 := bbase (se 7 (by rfl) ⟨11510, by rfl⟩ : syracuseStep 982229 = 23021) (by norm_num)
theorem B1473749 : Blo 654306 1473749 := bbase (se 7 (by rfl) ⟨17270, by rfl⟩ : syracuseStep 1473749 = 34541) (by norm_num)
theorem B1998053 : Blo 654306 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B982253 : Blo 654306 982253 := bbase (se 3 (by rfl) ⟨184172, by rfl⟩ : syracuseStep 982253 = 368345) (by norm_num)
theorem B982277 : Blo 654306 982277 := bbase (se 4 (by rfl) ⟨92088, by rfl⟩ : syracuseStep 982277 = 184177) (by norm_num)
theorem B982301 : Blo 654306 982301 := bbase (se 3 (by rfl) ⟨184181, by rfl⟩ : syracuseStep 982301 = 368363) (by norm_num)
theorem B1473821 : Blo 654306 1473821 := bbase (se 3 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 1473821 = 552683) (by norm_num)
theorem B982325 : Blo 654306 982325 := bbase (se 5 (by rfl) ⟨46046, by rfl⟩ : syracuseStep 982325 = 92093) (by norm_num)
theorem B1572173 : Blo 654306 1572173 := bbase (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) (by norm_num)
theorem B982349 : Blo 654306 982349 := bbase (se 3 (by rfl) ⟨184190, by rfl⟩ : syracuseStep 982349 = 368381) (by norm_num)
theorem B982373 : Blo 654306 982373 := bbase (se 4 (by rfl) ⟨92097, by rfl⟩ : syracuseStep 982373 = 184195) (by norm_num)
theorem B1473893 : Blo 654306 1473893 := bbase (se 4 (by rfl) ⟨138177, by rfl⟩ : syracuseStep 1473893 = 276355) (by norm_num)
theorem B2489717 : Blo 654306 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B982397 : Blo 654306 982397 := bbase (se 3 (by rfl) ⟨184199, by rfl⟩ : syracuseStep 982397 = 368399) (by norm_num)
theorem B2653573 : Blo 654306 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B982421 : Blo 654306 982421 := bbase (se 6 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 982421 = 46051) (by norm_num)
theorem B982445 : Blo 654306 982445 := bbase (se 3 (by rfl) ⟨184208, by rfl⟩ : syracuseStep 982445 = 368417) (by norm_num)
theorem B1473965 : Blo 654306 1473965 := bbase (se 3 (by rfl) ⟨276368, by rfl⟩ : syracuseStep 1473965 = 552737) (by norm_num)
theorem B982469 : Blo 654306 982469 := bbase (se 4 (by rfl) ⟨92106, by rfl⟩ : syracuseStep 982469 = 184213) (by norm_num)
theorem B982493 : Blo 654306 982493 := bbase (se 3 (by rfl) ⟨184217, by rfl⟩ : syracuseStep 982493 = 368435) (by norm_num)
theorem B982517 : Blo 654306 982517 := bbase (se 5 (by rfl) ⟨46055, by rfl⟩ : syracuseStep 982517 = 92111) (by norm_num)
theorem B1474037 : Blo 654306 1474037 := bbase (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) (by norm_num)
theorem B982541 : Blo 654306 982541 := bbase (se 3 (by rfl) ⟨184226, by rfl⟩ : syracuseStep 982541 = 368453) (by norm_num)
theorem B982565 : Blo 654306 982565 := bbase (se 4 (by rfl) ⟨92115, by rfl⟩ : syracuseStep 982565 = 184231) (by norm_num)
theorem B982589 : Blo 654306 982589 := bbase (se 3 (by rfl) ⟨184235, by rfl⟩ : syracuseStep 982589 = 368471) (by norm_num)
theorem B1474109 : Blo 654306 1474109 := bbase (se 3 (by rfl) ⟨276395, by rfl⟩ : syracuseStep 1474109 = 552791) (by norm_num)
theorem B982613 : Blo 654306 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B2096741 : Blo 654306 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B982637 : Blo 654306 982637 := bbase (se 3 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 982637 = 368489) (by norm_num)
theorem B982661 : Blo 654306 982661 := bbase (se 4 (by rfl) ⟨92124, by rfl⟩ : syracuseStep 982661 = 184249) (by norm_num)
theorem B1474181 : Blo 654306 1474181 := bbase (se 4 (by rfl) ⟨138204, by rfl⟩ : syracuseStep 1474181 = 276409) (by norm_num)
theorem B1244821 : Blo 654306 1244821 := bbase (se 6 (by rfl) ⟨29175, by rfl⟩ : syracuseStep 1244821 = 58351) (by norm_num)
theorem B982685 : Blo 654306 982685 := bbase (se 3 (by rfl) ⟨184253, by rfl⟩ : syracuseStep 982685 = 368507) (by norm_num)
theorem B982709 : Blo 654306 982709 := bbase (se 5 (by rfl) ⟨46064, by rfl⟩ : syracuseStep 982709 = 92129) (by norm_num)
theorem B982733 : Blo 654306 982733 := bbase (se 3 (by rfl) ⟨184262, by rfl⟩ : syracuseStep 982733 = 368525) (by norm_num)
theorem B1474253 : Blo 654306 1474253 := bbase (se 3 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 1474253 = 552845) (by norm_num)
theorem B982757 : Blo 654306 982757 := bbase (se 4 (by rfl) ⟨92133, by rfl⟩ : syracuseStep 982757 = 184267) (by norm_num)
theorem B982781 : Blo 654306 982781 := bbase (se 3 (by rfl) ⟨184271, by rfl⟩ : syracuseStep 982781 = 368543) (by norm_num)
theorem B982805 : Blo 654306 982805 := bbase (se 6 (by rfl) ⟨23034, by rfl⟩ : syracuseStep 982805 = 46069) (by norm_num)
theorem B1474325 : Blo 654306 1474325 := bbase (se 6 (by rfl) ⟨34554, by rfl⟩ : syracuseStep 1474325 = 69109) (by norm_num)
theorem B1244965 : Blo 654306 1244965 := bbase (se 4 (by rfl) ⟨116715, by rfl⟩ : syracuseStep 1244965 = 233431) (by norm_num)
theorem B982829 : Blo 654306 982829 := bbase (se 3 (by rfl) ⟨184280, by rfl⟩ : syracuseStep 982829 = 368561) (by norm_num)
theorem B982853 : Blo 654306 982853 := bbase (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) (by norm_num)
theorem B982877 : Blo 654306 982877 := bbase (se 3 (by rfl) ⟨184289, by rfl⟩ : syracuseStep 982877 = 368579) (by norm_num)
theorem B1474397 : Blo 654306 1474397 := bbase (se 3 (by rfl) ⟨276449, by rfl⟩ : syracuseStep 1474397 = 552899) (by norm_num)
theorem B1703789 : Blo 654306 1703789 := bbase (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) (by norm_num)
theorem B982901 : Blo 654306 982901 := bbase (se 5 (by rfl) ⟨46073, by rfl⟩ : syracuseStep 982901 = 92147) (by norm_num)
theorem B982925 : Blo 654306 982925 := bbase (se 3 (by rfl) ⟨184298, by rfl⟩ : syracuseStep 982925 = 368597) (by norm_num)
theorem B982949 : Blo 654306 982949 := bbase (se 4 (by rfl) ⟨92151, by rfl⟩ : syracuseStep 982949 = 184303) (by norm_num)
theorem B1474469 : Blo 654306 1474469 := bbase (se 4 (by rfl) ⟨138231, by rfl⟩ : syracuseStep 1474469 = 276463) (by norm_num)
theorem B982973 : Blo 654306 982973 := bbase (se 3 (by rfl) ⟨184307, by rfl⟩ : syracuseStep 982973 = 368615) (by norm_num)
theorem B1245125 : Blo 654306 1245125 := bbase (se 4 (by rfl) ⟨116730, by rfl⟩ : syracuseStep 1245125 = 233461) (by norm_num)
theorem B884693 : Blo 654306 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B982997 : Blo 654306 982997 := bbase (se 7 (by rfl) ⟨11519, by rfl⟩ : syracuseStep 982997 = 23039) (by norm_num)
theorem B983021 : Blo 654306 983021 := bbase (se 3 (by rfl) ⟨184316, by rfl⟩ : syracuseStep 983021 = 368633) (by norm_num)
theorem B1474541 : Blo 654306 1474541 := bbase (se 3 (by rfl) ⟨276476, by rfl⟩ : syracuseStep 1474541 = 552953) (by norm_num)
theorem B655363 : Blo 654306 655363 := bstep (se 1 (by rfl) ⟨491522, by rfl⟩ : syracuseStep 655363 = 983045) B983045
theorem B3735557 : Blo 654306 3735557 := bstep (se 4 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 3735557 = 700417) B700417
theorem B1867789 : Blo 654306 1867789 := bstep (se 3 (by rfl) ⟨350210, by rfl⟩ : syracuseStep 1867789 = 700421) B700421
theorem B1474577 : Blo 654306 1474577 := bstep (se 2 (by rfl) ⟨552966, by rfl⟩ : syracuseStep 1474577 = 1105933) B1105933
theorem B983057 : Blo 654306 983057 := bstep (se 2 (by rfl) ⟨368646, by rfl⟩ : syracuseStep 983057 = 737293) B737293
theorem B655379 : Blo 654306 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B1474595 : Blo 654306 1474595 := bstep (se 1 (by rfl) ⟨1105946, by rfl⟩ : syracuseStep 1474595 = 2211893) B2211893
theorem B983075 : Blo 654306 983075 := bstep (se 1 (by rfl) ⟨737306, by rfl⟩ : syracuseStep 983075 = 1474613) B1474613
theorem B655395 : Blo 654306 655395 := bstep (se 1 (by rfl) ⟨491546, by rfl⟩ : syracuseStep 655395 = 983093) B983093
theorem B655411 : Blo 654306 655411 := bstep (se 1 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 655411 = 983117) B983117
theorem B983105 : Blo 654306 983105 := bstep (se 2 (by rfl) ⟨368664, by rfl⟩ : syracuseStep 983105 = 737329) B737329
theorem B655427 : Blo 654306 655427 := bstep (se 1 (by rfl) ⟨491570, by rfl⟩ : syracuseStep 655427 = 983141) B983141
theorem B983123 : Blo 654306 983123 := bstep (se 1 (by rfl) ⟨737342, by rfl⟩ : syracuseStep 983123 = 1474685) B1474685
theorem B655443 : Blo 654306 655443 := bstep (se 1 (by rfl) ⟨491582, by rfl⟩ : syracuseStep 655443 = 983165) B983165
theorem B655459 : Blo 654306 655459 := bstep (se 1 (by rfl) ⟨491594, by rfl⟩ : syracuseStep 655459 = 983189) B983189
theorem B2097265 : Blo 654306 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B983153 : Blo 654306 983153 := bstep (se 2 (by rfl) ⟨368682, by rfl⟩ : syracuseStep 983153 = 737365) B737365
theorem B655475 : Blo 654306 655475 := bstep (se 1 (by rfl) ⟨491606, by rfl⟩ : syracuseStep 655475 = 983213) B983213
theorem B983171 : Blo 654306 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B655491 : Blo 654306 655491 := bstep (se 1 (by rfl) ⟨491618, by rfl⟩ : syracuseStep 655491 = 983237) B983237
theorem B655507 : Blo 654306 655507 := bstep (se 1 (by rfl) ⟨491630, by rfl⟩ : syracuseStep 655507 = 983261) B983261
theorem B983201 : Blo 654306 983201 := bstep (se 2 (by rfl) ⟨368700, by rfl⟩ : syracuseStep 983201 = 737401) B737401
theorem B655523 : Blo 654306 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B983219 : Blo 654306 983219 := bstep (se 1 (by rfl) ⟨737414, by rfl⟩ : syracuseStep 983219 = 1474829) B1474829
theorem B655539 : Blo 654306 655539 := bstep (se 1 (by rfl) ⟨491654, by rfl⟩ : syracuseStep 655539 = 983309) B983309
theorem B655555 : Blo 654306 655555 := bstep (se 1 (by rfl) ⟨491666, by rfl⟩ : syracuseStep 655555 = 983333) B983333
theorem B983249 : Blo 654306 983249 := bstep (se 2 (by rfl) ⟨368718, by rfl⟩ : syracuseStep 983249 = 737437) B737437
theorem B655571 : Blo 654306 655571 := bstep (se 1 (by rfl) ⟨491678, by rfl⟩ : syracuseStep 655571 = 983357) B983357
theorem B40337621 : Blo 654306 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B983267 : Blo 654306 983267 := bstep (se 1 (by rfl) ⟨737450, by rfl⟩ : syracuseStep 983267 = 1474901) B1474901
theorem B655587 : Blo 654306 655587 := bstep (se 1 (by rfl) ⟨491690, by rfl⟩ : syracuseStep 655587 = 983381) B983381
theorem B1868017 : Blo 654306 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B655603 : Blo 654306 655603 := bstep (se 1 (by rfl) ⟨491702, by rfl⟩ : syracuseStep 655603 = 983405) B983405
theorem B983297 : Blo 654306 983297 := bstep (se 2 (by rfl) ⟨368736, by rfl⟩ : syracuseStep 983297 = 737473) B737473
theorem B655619 : Blo 654306 655619 := bstep (se 1 (by rfl) ⟨491714, by rfl⟩ : syracuseStep 655619 = 983429) B983429
theorem B983315 : Blo 654306 983315 := bstep (se 1 (by rfl) ⟨737486, by rfl⟩ : syracuseStep 983315 = 1474973) B1474973
theorem B655635 : Blo 654306 655635 := bstep (se 1 (by rfl) ⟨491726, by rfl⟩ : syracuseStep 655635 = 983453) B983453
theorem B655651 : Blo 654306 655651 := bstep (se 1 (by rfl) ⟨491738, by rfl⟩ : syracuseStep 655651 = 983477) B983477
theorem B2490659 : Blo 654306 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B1474865 : Blo 654306 1474865 := bstep (se 2 (by rfl) ⟨553074, by rfl⟩ : syracuseStep 1474865 = 1106149) B1106149
theorem B983345 : Blo 654306 983345 := bstep (se 2 (by rfl) ⟨368754, by rfl⟩ : syracuseStep 983345 = 737509) B737509
theorem B655667 : Blo 654306 655667 := bstep (se 1 (by rfl) ⟨491750, by rfl⟩ : syracuseStep 655667 = 983501) B983501
theorem B1474883 : Blo 654306 1474883 := bstep (se 1 (by rfl) ⟨1106162, by rfl⟩ : syracuseStep 1474883 = 2212325) B2212325
theorem B983363 : Blo 654306 983363 := bstep (se 1 (by rfl) ⟨737522, by rfl⟩ : syracuseStep 983363 = 1475045) B1475045
theorem B655683 : Blo 654306 655683 := bstep (se 1 (by rfl) ⟨491762, by rfl⟩ : syracuseStep 655683 = 983525) B983525
theorem B655699 : Blo 654306 655699 := bstep (se 1 (by rfl) ⟨491774, by rfl⟩ : syracuseStep 655699 = 983549) B983549
theorem B983393 : Blo 654306 983393 := bstep (se 2 (by rfl) ⟨368772, by rfl⟩ : syracuseStep 983393 = 737545) B737545
theorem B655715 : Blo 654306 655715 := bstep (se 1 (by rfl) ⟨491786, by rfl⟩ : syracuseStep 655715 = 983573) B983573
theorem B983411 : Blo 654306 983411 := bstep (se 1 (by rfl) ⟨737558, by rfl⟩ : syracuseStep 983411 = 1475117) B1475117
theorem B655731 : Blo 654306 655731 := bstep (se 1 (by rfl) ⟨491798, by rfl⟩ : syracuseStep 655731 = 983597) B983597
theorem B655747 : Blo 654306 655747 := bstep (se 1 (by rfl) ⟨491810, by rfl⟩ : syracuseStep 655747 = 983621) B983621
theorem B983441 : Blo 654306 983441 := bstep (se 2 (by rfl) ⟨368790, by rfl⟩ : syracuseStep 983441 = 737581) B737581
theorem B1868177 : Blo 654306 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B655763 : Blo 654306 655763 := bstep (se 1 (by rfl) ⟨491822, by rfl⟩ : syracuseStep 655763 = 983645) B983645
theorem B983459 : Blo 654306 983459 := bstep (se 1 (by rfl) ⟨737594, by rfl⟩ : syracuseStep 983459 = 1475189) B1475189
theorem B655779 : Blo 654306 655779 := bstep (se 1 (by rfl) ⟨491834, by rfl⟩ : syracuseStep 655779 = 983669) B983669
theorem B2130349 : Blo 654306 2130349 := bstep (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) B798881
theorem B655795 : Blo 654306 655795 := bstep (se 1 (by rfl) ⟨491846, by rfl⟩ : syracuseStep 655795 = 983693) B983693
theorem B983489 : Blo 654306 983489 := bstep (se 2 (by rfl) ⟨368808, by rfl⟩ : syracuseStep 983489 = 737617) B737617
theorem B655811 : Blo 654306 655811 := bstep (se 1 (by rfl) ⟨491858, by rfl⟩ : syracuseStep 655811 = 983717) B983717
theorem B983507 : Blo 654306 983507 := bstep (se 1 (by rfl) ⟨737630, by rfl⟩ : syracuseStep 983507 = 1475261) B1475261
theorem B655827 : Blo 654306 655827 := bstep (se 1 (by rfl) ⟨491870, by rfl⟩ : syracuseStep 655827 = 983741) B983741
theorem B4194787 : Blo 654306 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B655843 : Blo 654306 655843 := bstep (se 1 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 655843 = 983765) B983765
theorem B1180145 : Blo 654306 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B983537 : Blo 654306 983537 := bstep (se 2 (by rfl) ⟨368826, by rfl⟩ : syracuseStep 983537 = 737653) B737653
theorem B655859 : Blo 654306 655859 := bstep (se 1 (by rfl) ⟨491894, by rfl⟩ : syracuseStep 655859 = 983789) B983789
theorem B983555 : Blo 654306 983555 := bstep (se 1 (by rfl) ⟨737666, by rfl⟩ : syracuseStep 983555 = 1475333) B1475333
theorem B655875 : Blo 654306 655875 := bstep (se 1 (by rfl) ⟨491906, by rfl⟩ : syracuseStep 655875 = 983813) B983813
theorem B1868291 : Blo 654306 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B1049107 : Blo 654306 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B655891 : Blo 654306 655891 := bstep (se 1 (by rfl) ⟨491918, by rfl⟩ : syracuseStep 655891 = 983837) B983837
theorem B983585 : Blo 654306 983585 := bstep (se 2 (by rfl) ⟨368844, by rfl⟩ : syracuseStep 983585 = 737689) B737689
theorem B655907 : Blo 654306 655907 := bstep (se 1 (by rfl) ⟨491930, by rfl⟩ : syracuseStep 655907 = 983861) B983861
theorem B983603 : Blo 654306 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B655923 : Blo 654306 655923 := bstep (se 1 (by rfl) ⟨491942, by rfl⟩ : syracuseStep 655923 = 983885) B983885
theorem B655939 : Blo 654306 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B1475153 : Blo 654306 1475153 := bstep (se 2 (by rfl) ⟨553182, by rfl⟩ : syracuseStep 1475153 = 1106365) B1106365
theorem B983633 : Blo 654306 983633 := bstep (se 2 (by rfl) ⟨368862, by rfl⟩ : syracuseStep 983633 = 737725) B737725
theorem B655955 : Blo 654306 655955 := bstep (se 1 (by rfl) ⟨491966, by rfl⟩ : syracuseStep 655955 = 983933) B983933
theorem B1475171 : Blo 654306 1475171 := bstep (se 1 (by rfl) ⟨1106378, by rfl⟩ : syracuseStep 1475171 = 2212757) B2212757
theorem B983651 : Blo 654306 983651 := bstep (se 1 (by rfl) ⟨737738, by rfl⟩ : syracuseStep 983651 = 1475477) B1475477
theorem B655971 : Blo 654306 655971 := bstep (se 1 (by rfl) ⟨491978, by rfl⟩ : syracuseStep 655971 = 983957) B983957
theorem B655987 : Blo 654306 655987 := bstep (se 1 (by rfl) ⟨491990, by rfl⟩ : syracuseStep 655987 = 983981) B983981
theorem B983681 : Blo 654306 983681 := bstep (se 2 (by rfl) ⟨368880, by rfl⟩ : syracuseStep 983681 = 737761) B737761
theorem B656003 : Blo 654306 656003 := bstep (se 1 (by rfl) ⟨492002, by rfl⟩ : syracuseStep 656003 = 984005) B984005
theorem B983699 : Blo 654306 983699 := bstep (se 1 (by rfl) ⟨737774, by rfl⟩ : syracuseStep 983699 = 1475549) B1475549
theorem B656019 : Blo 654306 656019 := bstep (se 1 (by rfl) ⟨492014, by rfl⟩ : syracuseStep 656019 = 984029) B984029
theorem B656035 : Blo 654306 656035 := bstep (se 1 (by rfl) ⟨492026, by rfl⟩ : syracuseStep 656035 = 984053) B984053
theorem B983729 : Blo 654306 983729 := bstep (se 2 (by rfl) ⟨368898, by rfl⟩ : syracuseStep 983729 = 737797) B737797
theorem B656051 : Blo 654306 656051 := bstep (se 1 (by rfl) ⟨492038, by rfl⟩ : syracuseStep 656051 = 984077) B984077
theorem B983747 : Blo 654306 983747 := bstep (se 1 (by rfl) ⟨737810, by rfl⟩ : syracuseStep 983747 = 1475621) B1475621
theorem B656067 : Blo 654306 656067 := bstep (se 1 (by rfl) ⟨492050, by rfl⟩ : syracuseStep 656067 = 984101) B984101
theorem B656083 : Blo 654306 656083 := bstep (se 1 (by rfl) ⟨492062, by rfl⟩ : syracuseStep 656083 = 984125) B984125
theorem B983777 : Blo 654306 983777 := bstep (se 2 (by rfl) ⟨368916, by rfl⟩ : syracuseStep 983777 = 737833) B737833
theorem B656099 : Blo 654306 656099 := bstep (se 1 (by rfl) ⟨492074, by rfl⟩ : syracuseStep 656099 = 984149) B984149
theorem B983795 : Blo 654306 983795 := bstep (se 1 (by rfl) ⟨737846, by rfl⟩ : syracuseStep 983795 = 1475693) B1475693
theorem B656115 : Blo 654306 656115 := bstep (se 1 (by rfl) ⟨492086, by rfl⟩ : syracuseStep 656115 = 984173) B984173
theorem B1245937 : Blo 654306 1245937 := bstep (se 2 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 1245937 = 934453) B934453
theorem B1049345 : Blo 654306 1049345 := bstep (se 2 (by rfl) ⟨393504, by rfl⟩ : syracuseStep 1049345 = 787009) B787009
theorem B656131 : Blo 654306 656131 := bstep (se 1 (by rfl) ⟨492098, by rfl⟩ : syracuseStep 656131 = 984197) B984197
theorem B1999619 : Blo 654306 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B983825 : Blo 654306 983825 := bstep (se 2 (by rfl) ⟨368934, by rfl⟩ : syracuseStep 983825 = 737869) B737869
theorem B656147 : Blo 654306 656147 := bstep (se 1 (by rfl) ⟨492110, by rfl⟩ : syracuseStep 656147 = 984221) B984221
theorem B983843 : Blo 654306 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B656163 : Blo 654306 656163 := bstep (se 1 (by rfl) ⟨492122, by rfl⟩ : syracuseStep 656163 = 984245) B984245
theorem B656179 : Blo 654306 656179 := bstep (se 1 (by rfl) ⟨492134, by rfl⟩ : syracuseStep 656179 = 984269) B984269
theorem B983873 : Blo 654306 983873 := bstep (se 2 (by rfl) ⟨368952, by rfl⟩ : syracuseStep 983873 = 737905) B737905
theorem B656195 : Blo 654306 656195 := bstep (se 1 (by rfl) ⟨492146, by rfl⟩ : syracuseStep 656195 = 984293) B984293
theorem B983891 : Blo 654306 983891 := bstep (se 1 (by rfl) ⟨737918, by rfl⟩ : syracuseStep 983891 = 1475837) B1475837
theorem B656211 : Blo 654306 656211 := bstep (se 1 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 656211 = 984317) B984317
theorem B656227 : Blo 654306 656227 := bstep (se 1 (by rfl) ⟨492170, by rfl⟩ : syracuseStep 656227 = 984341) B984341
theorem B1475441 : Blo 654306 1475441 := bstep (se 2 (by rfl) ⟨553290, by rfl⟩ : syracuseStep 1475441 = 1106581) B1106581
theorem B983921 : Blo 654306 983921 := bstep (se 2 (by rfl) ⟨368970, by rfl⟩ : syracuseStep 983921 = 737941) B737941
theorem B656243 : Blo 654306 656243 := bstep (se 1 (by rfl) ⟨492182, by rfl⟩ : syracuseStep 656243 = 984365) B984365
theorem B1475459 : Blo 654306 1475459 := bstep (se 1 (by rfl) ⟨1106594, by rfl⟩ : syracuseStep 1475459 = 2213189) B2213189
theorem B983939 : Blo 654306 983939 := bstep (se 1 (by rfl) ⟨737954, by rfl⟩ : syracuseStep 983939 = 1475909) B1475909
theorem B656259 : Blo 654306 656259 := bstep (se 1 (by rfl) ⟨492194, by rfl⟩ : syracuseStep 656259 = 984389) B984389
theorem B885649 : Blo 654306 885649 := bstep (se 2 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 885649 = 664237) B664237
theorem B1246097 : Blo 654306 1246097 := bstep (se 2 (by rfl) ⟨467286, by rfl⟩ : syracuseStep 1246097 = 934573) B934573
theorem B656275 : Blo 654306 656275 := bstep (se 1 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 656275 = 984413) B984413
theorem B983969 : Blo 654306 983969 := bstep (se 2 (by rfl) ⟨368988, by rfl⟩ : syracuseStep 983969 = 737977) B737977
theorem B656291 : Blo 654306 656291 := bstep (se 1 (by rfl) ⟨492218, by rfl⟩ : syracuseStep 656291 = 984437) B984437
theorem B983987 : Blo 654306 983987 := bstep (se 1 (by rfl) ⟨737990, by rfl⟩ : syracuseStep 983987 = 1475981) B1475981
theorem B656307 : Blo 654306 656307 := bstep (se 1 (by rfl) ⟨492230, by rfl⟩ : syracuseStep 656307 = 984461) B984461
theorem B656323 : Blo 654306 656323 := bstep (se 1 (by rfl) ⟨492242, by rfl⟩ : syracuseStep 656323 = 984485) B984485
theorem B984017 : Blo 654306 984017 := bstep (se 2 (by rfl) ⟨369006, by rfl⟩ : syracuseStep 984017 = 738013) B738013
theorem B1049555 : Blo 654306 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B656339 : Blo 654306 656339 := bstep (se 1 (by rfl) ⟨492254, by rfl⟩ : syracuseStep 656339 = 984509) B984509
theorem B984035 : Blo 654306 984035 := bstep (se 1 (by rfl) ⟨738026, by rfl⟩ : syracuseStep 984035 = 1476053) B1476053
theorem B656355 : Blo 654306 656355 := bstep (se 1 (by rfl) ⟨492266, by rfl⟩ : syracuseStep 656355 = 984533) B984533
theorem B656371 : Blo 654306 656371 := bstep (se 1 (by rfl) ⟨492278, by rfl⟩ : syracuseStep 656371 = 984557) B984557
theorem B984065 : Blo 654306 984065 := bstep (se 2 (by rfl) ⟨369024, by rfl⟩ : syracuseStep 984065 = 738049) B738049
theorem B656387 : Blo 654306 656387 := bstep (se 1 (by rfl) ⟨492290, by rfl⟩ : syracuseStep 656387 = 984581) B984581
theorem B984083 : Blo 654306 984083 := bstep (se 1 (by rfl) ⟨738062, by rfl⟩ : syracuseStep 984083 = 1476125) B1476125
theorem B656403 : Blo 654306 656403 := bstep (se 1 (by rfl) ⟨492302, by rfl⟩ : syracuseStep 656403 = 984605) B984605
theorem B656419 : Blo 654306 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B3376163 : Blo 654306 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B984113 : Blo 654306 984113 := bstep (se 2 (by rfl) ⟨369042, by rfl⟩ : syracuseStep 984113 = 738085) B738085
theorem B656435 : Blo 654306 656435 := bstep (se 1 (by rfl) ⟨492326, by rfl⟩ : syracuseStep 656435 = 984653) B984653
theorem B984131 : Blo 654306 984131 := bstep (se 1 (by rfl) ⟨738098, by rfl⟩ : syracuseStep 984131 = 1476197) B1476197
theorem B656451 : Blo 654306 656451 := bstep (se 1 (by rfl) ⟨492338, by rfl⟩ : syracuseStep 656451 = 984677) B984677
theorem B656467 : Blo 654306 656467 := bstep (se 1 (by rfl) ⟨492350, by rfl⟩ : syracuseStep 656467 = 984701) B984701
theorem B984161 : Blo 654306 984161 := bstep (se 2 (by rfl) ⟨369060, by rfl⟩ : syracuseStep 984161 = 738121) B738121
theorem B1573987 : Blo 654306 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B656483 : Blo 654306 656483 := bstep (se 1 (by rfl) ⟨492362, by rfl⟩ : syracuseStep 656483 = 984725) B984725
theorem B984179 : Blo 654306 984179 := bstep (se 1 (by rfl) ⟨738134, by rfl⟩ : syracuseStep 984179 = 1476269) B1476269
theorem B656499 : Blo 654306 656499 := bstep (se 1 (by rfl) ⟨492374, by rfl⟩ : syracuseStep 656499 = 984749) B984749
theorem B656515 : Blo 654306 656515 := bstep (se 1 (by rfl) ⟨492386, by rfl⟩ : syracuseStep 656515 = 984773) B984773
theorem B1475729 : Blo 654306 1475729 := bstep (se 2 (by rfl) ⟨553398, by rfl⟩ : syracuseStep 1475729 = 1106797) B1106797
theorem B984209 : Blo 654306 984209 := bstep (se 2 (by rfl) ⟨369078, by rfl⟩ : syracuseStep 984209 = 738157) B738157
theorem B656531 : Blo 654306 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B1475747 : Blo 654306 1475747 := bstep (se 1 (by rfl) ⟨1106810, by rfl⟩ : syracuseStep 1475747 = 2213621) B2213621
theorem B984227 : Blo 654306 984227 := bstep (se 1 (by rfl) ⟨738170, by rfl⟩ : syracuseStep 984227 = 1476341) B1476341
theorem B656547 : Blo 654306 656547 := bstep (se 1 (by rfl) ⟨492410, by rfl⟩ : syracuseStep 656547 = 984821) B984821
theorem B656563 : Blo 654306 656563 := bstep (se 1 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 656563 = 984845) B984845
theorem B984257 : Blo 654306 984257 := bstep (se 2 (by rfl) ⟨369096, by rfl⟩ : syracuseStep 984257 = 738193) B738193
theorem B656579 : Blo 654306 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B3146957 : Blo 654306 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B2098381 : Blo 654306 2098381 := bstep (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) B786893
theorem B984275 : Blo 654306 984275 := bstep (se 1 (by rfl) ⟨738206, by rfl⟩ : syracuseStep 984275 = 1476413) B1476413
theorem B656595 : Blo 654306 656595 := bstep (se 1 (by rfl) ⟨492446, by rfl⟩ : syracuseStep 656595 = 984893) B984893
theorem B656611 : Blo 654306 656611 := bstep (se 1 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 656611 = 984917) B984917
theorem B1279217 : Blo 654306 1279217 := bstep (se 2 (by rfl) ⟨479706, by rfl⟩ : syracuseStep 1279217 = 959413) B959413
theorem B984305 : Blo 654306 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B656627 : Blo 654306 656627 := bstep (se 1 (by rfl) ⟨492470, by rfl⟩ : syracuseStep 656627 = 984941) B984941
theorem B984323 : Blo 654306 984323 := bstep (se 1 (by rfl) ⟨738242, by rfl⟩ : syracuseStep 984323 = 1476485) B1476485
theorem B656643 : Blo 654306 656643 := bstep (se 1 (by rfl) ⟨492482, by rfl⟩ : syracuseStep 656643 = 984965) B984965
theorem B2491661 : Blo 654306 2491661 := bstep (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) B934373
theorem B656659 : Blo 654306 656659 := bstep (se 1 (by rfl) ⟨492494, by rfl⟩ : syracuseStep 656659 = 984989) B984989
theorem B984353 : Blo 654306 984353 := bstep (se 2 (by rfl) ⟨369132, by rfl⟩ : syracuseStep 984353 = 738265) B738265
theorem B1246499 : Blo 654306 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B656675 : Blo 654306 656675 := bstep (se 1 (by rfl) ⟨492506, by rfl⟩ : syracuseStep 656675 = 985013) B985013
theorem B984371 : Blo 654306 984371 := bstep (se 1 (by rfl) ⟨738278, by rfl⟩ : syracuseStep 984371 = 1476557) B1476557
theorem B656691 : Blo 654306 656691 := bstep (se 1 (by rfl) ⟨492518, by rfl⟩ : syracuseStep 656691 = 985037) B985037
theorem B656707 : Blo 654306 656707 := bstep (se 1 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 656707 = 985061) B985061
theorem B984401 : Blo 654306 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B656723 : Blo 654306 656723 := bstep (se 1 (by rfl) ⟨492542, by rfl⟩ : syracuseStep 656723 = 985085) B985085
theorem B984419 : Blo 654306 984419 := bstep (se 1 (by rfl) ⟨738314, by rfl⟩ : syracuseStep 984419 = 1476629) B1476629
theorem B656739 : Blo 654306 656739 := bstep (se 1 (by rfl) ⟨492554, by rfl⟩ : syracuseStep 656739 = 985109) B985109
theorem B656755 : Blo 654306 656755 := bstep (se 1 (by rfl) ⟨492566, by rfl⟩ : syracuseStep 656755 = 985133) B985133
theorem B984449 : Blo 654306 984449 := bstep (se 2 (by rfl) ⟨369168, by rfl⟩ : syracuseStep 984449 = 738337) B738337
theorem B656771 : Blo 654306 656771 := bstep (se 1 (by rfl) ⟨492578, by rfl⟩ : syracuseStep 656771 = 985157) B985157
theorem B7079309 : Blo 654306 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B984467 : Blo 654306 984467 := bstep (se 1 (by rfl) ⟨738350, by rfl⟩ : syracuseStep 984467 = 1476701) B1476701
theorem B656787 : Blo 654306 656787 := bstep (se 1 (by rfl) ⟨492590, by rfl⟩ : syracuseStep 656787 = 985181) B985181
theorem B656803 : Blo 654306 656803 := bstep (se 1 (by rfl) ⟨492602, by rfl⟩ : syracuseStep 656803 = 985205) B985205
theorem B1476017 : Blo 654306 1476017 := bstep (se 2 (by rfl) ⟨553506, by rfl⟩ : syracuseStep 1476017 = 1107013) B1107013
theorem B984497 : Blo 654306 984497 := bstep (se 2 (by rfl) ⟨369186, by rfl⟩ : syracuseStep 984497 = 738373) B738373
theorem B656819 : Blo 654306 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B787907 : Blo 654306 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1476035 : Blo 654306 1476035 := bstep (se 1 (by rfl) ⟨1107026, by rfl⟩ : syracuseStep 1476035 = 2214053) B2214053
theorem B984515 : Blo 654306 984515 := bstep (se 1 (by rfl) ⟨738386, by rfl⟩ : syracuseStep 984515 = 1476773) B1476773
theorem B656835 : Blo 654306 656835 := bstep (se 1 (by rfl) ⟨492626, by rfl⟩ : syracuseStep 656835 = 985253) B985253
theorem B656851 : Blo 654306 656851 := bstep (se 1 (by rfl) ⟨492638, by rfl⟩ : syracuseStep 656851 = 985277) B985277
theorem B984545 : Blo 654306 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B656867 : Blo 654306 656867 := bstep (se 1 (by rfl) ⟨492650, by rfl⟩ : syracuseStep 656867 = 985301) B985301
theorem B1869293 : Blo 654306 1869293 := bstep (se 3 (by rfl) ⟨350492, by rfl⟩ : syracuseStep 1869293 = 700985) B700985
theorem B984563 : Blo 654306 984563 := bstep (se 1 (by rfl) ⟨738422, by rfl⟩ : syracuseStep 984563 = 1476845) B1476845
theorem B656883 : Blo 654306 656883 := bstep (se 1 (by rfl) ⟨492662, by rfl⟩ : syracuseStep 656883 = 985325) B985325
theorem B656899 : Blo 654306 656899 := bstep (se 1 (by rfl) ⟨492674, by rfl⟩ : syracuseStep 656899 = 985349) B985349
theorem B984593 : Blo 654306 984593 := bstep (se 2 (by rfl) ⟨369222, by rfl⟩ : syracuseStep 984593 = 738445) B738445
theorem B656915 : Blo 654306 656915 := bstep (se 1 (by rfl) ⟨492686, by rfl⟩ : syracuseStep 656915 = 985373) B985373
theorem B984611 : Blo 654306 984611 := bstep (se 1 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 984611 = 1476917) B1476917
theorem B656931 : Blo 654306 656931 := bstep (se 1 (by rfl) ⟨492698, by rfl⟩ : syracuseStep 656931 = 985397) B985397
theorem B656947 : Blo 654306 656947 := bstep (se 1 (by rfl) ⟨492710, by rfl⟩ : syracuseStep 656947 = 985421) B985421
theorem B984641 : Blo 654306 984641 := bstep (se 2 (by rfl) ⟨369240, by rfl⟩ : syracuseStep 984641 = 738481) B738481
theorem B656963 : Blo 654306 656963 := bstep (se 1 (by rfl) ⟨492722, by rfl⟩ : syracuseStep 656963 = 985445) B985445
theorem B984659 : Blo 654306 984659 := bstep (se 1 (by rfl) ⟨738494, by rfl⟩ : syracuseStep 984659 = 1476989) B1476989
theorem B656979 : Blo 654306 656979 := bstep (se 1 (by rfl) ⟨492734, by rfl⟩ : syracuseStep 656979 = 985469) B985469
theorem B656995 : Blo 654306 656995 := bstep (se 1 (by rfl) ⟨492746, by rfl⟩ : syracuseStep 656995 = 985493) B985493
theorem B984689 : Blo 654306 984689 := bstep (se 2 (by rfl) ⟨369258, by rfl⟩ : syracuseStep 984689 = 738517) B738517
theorem B657011 : Blo 654306 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B984707 : Blo 654306 984707 := bstep (se 1 (by rfl) ⟨738530, by rfl⟩ : syracuseStep 984707 = 1477061) B1477061
theorem B657027 : Blo 654306 657027 := bstep (se 1 (by rfl) ⟨492770, by rfl⟩ : syracuseStep 657027 = 985541) B985541
theorem B657043 : Blo 654306 657043 := bstep (se 1 (by rfl) ⟨492782, by rfl⟩ : syracuseStep 657043 = 985565) B985565
theorem B984737 : Blo 654306 984737 := bstep (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) B738553
theorem B1869475 : Blo 654306 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B657059 : Blo 654306 657059 := bstep (se 1 (by rfl) ⟨492794, by rfl⟩ : syracuseStep 657059 = 985589) B985589
theorem B984755 : Blo 654306 984755 := bstep (se 1 (by rfl) ⟨738566, by rfl⟩ : syracuseStep 984755 = 1477133) B1477133
theorem B657075 : Blo 654306 657075 := bstep (se 1 (by rfl) ⟨492806, by rfl⟩ : syracuseStep 657075 = 985613) B985613
theorem B657091 : Blo 654306 657091 := bstep (se 1 (by rfl) ⟨492818, by rfl⟩ : syracuseStep 657091 = 985637) B985637
theorem B1476305 : Blo 654306 1476305 := bstep (se 2 (by rfl) ⟨553614, by rfl⟩ : syracuseStep 1476305 = 1107229) B1107229
theorem B984785 : Blo 654306 984785 := bstep (se 2 (by rfl) ⟨369294, by rfl⟩ : syracuseStep 984785 = 738589) B738589
theorem B657107 : Blo 654306 657107 := bstep (se 1 (by rfl) ⟨492830, by rfl⟩ : syracuseStep 657107 = 985661) B985661
theorem B1050337 : Blo 654306 1050337 := bstep (se 2 (by rfl) ⟨393876, by rfl⟩ : syracuseStep 1050337 = 787753) B787753
theorem B1476323 : Blo 654306 1476323 := bstep (se 1 (by rfl) ⟨1107242, by rfl⟩ : syracuseStep 1476323 = 2214485) B2214485
theorem B984803 : Blo 654306 984803 := bstep (se 1 (by rfl) ⟨738602, by rfl⟩ : syracuseStep 984803 = 1477205) B1477205
theorem B657123 : Blo 654306 657123 := bstep (se 1 (by rfl) ⟨492842, by rfl⟩ : syracuseStep 657123 = 985685) B985685
theorem B657139 : Blo 654306 657139 := bstep (se 1 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 657139 = 985709) B985709
theorem B984833 : Blo 654306 984833 := bstep (se 2 (by rfl) ⟨369312, by rfl⟩ : syracuseStep 984833 = 738625) B738625
theorem B657155 : Blo 654306 657155 := bstep (se 1 (by rfl) ⟨492866, by rfl⟩ : syracuseStep 657155 = 985733) B985733
theorem B5998349 : Blo 654306 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B984851 : Blo 654306 984851 := bstep (se 1 (by rfl) ⟨738638, by rfl⟩ : syracuseStep 984851 = 1477277) B1477277
theorem B657171 : Blo 654306 657171 := bstep (se 1 (by rfl) ⟨492878, by rfl⟩ : syracuseStep 657171 = 985757) B985757
theorem B657187 : Blo 654306 657187 := bstep (se 1 (by rfl) ⟨492890, by rfl⟩ : syracuseStep 657187 = 985781) B985781
theorem B984881 : Blo 654306 984881 := bstep (se 2 (by rfl) ⟨369330, by rfl⟩ : syracuseStep 984881 = 738661) B738661
theorem B657203 : Blo 654306 657203 := bstep (se 1 (by rfl) ⟨492902, by rfl⟩ : syracuseStep 657203 = 985805) B985805
theorem B1869635 : Blo 654306 1869635 := bstep (se 1 (by rfl) ⟨1402226, by rfl⟩ : syracuseStep 1869635 = 2804453) B2804453
theorem B984899 : Blo 654306 984899 := bstep (se 1 (by rfl) ⟨738674, by rfl⟩ : syracuseStep 984899 = 1477349) B1477349
theorem B657219 : Blo 654306 657219 := bstep (se 1 (by rfl) ⟨492914, by rfl⟩ : syracuseStep 657219 = 985829) B985829
theorem B657235 : Blo 654306 657235 := bstep (se 1 (by rfl) ⟨492926, by rfl⟩ : syracuseStep 657235 = 985853) B985853
theorem B984929 : Blo 654306 984929 := bstep (se 2 (by rfl) ⟨369348, by rfl⟩ : syracuseStep 984929 = 738697) B738697
theorem B657251 : Blo 654306 657251 := bstep (se 1 (by rfl) ⟨492938, by rfl⟩ : syracuseStep 657251 = 985877) B985877
theorem B984947 : Blo 654306 984947 := bstep (se 1 (by rfl) ⟨738710, by rfl⟩ : syracuseStep 984947 = 1477421) B1477421
theorem B657267 : Blo 654306 657267 := bstep (se 1 (by rfl) ⟨492950, by rfl⟩ : syracuseStep 657267 = 985901) B985901
theorem B657283 : Blo 654306 657283 := bstep (se 1 (by rfl) ⟨492962, by rfl⟩ : syracuseStep 657283 = 985925) B985925
theorem B984977 : Blo 654306 984977 := bstep (se 2 (by rfl) ⟨369366, by rfl⟩ : syracuseStep 984977 = 738733) B738733
theorem B657299 : Blo 654306 657299 := bstep (se 1 (by rfl) ⟨492974, by rfl⟩ : syracuseStep 657299 = 985949) B985949
theorem B984995 : Blo 654306 984995 := bstep (se 1 (by rfl) ⟨738746, by rfl⟩ : syracuseStep 984995 = 1477493) B1477493
theorem B657315 : Blo 654306 657315 := bstep (se 1 (by rfl) ⟨492986, by rfl⟩ : syracuseStep 657315 = 985973) B985973
theorem B657331 : Blo 654306 657331 := bstep (se 1 (by rfl) ⟨492998, by rfl⟩ : syracuseStep 657331 = 985997) B985997
theorem B985025 : Blo 654306 985025 := bstep (se 2 (by rfl) ⟨369384, by rfl⟩ : syracuseStep 985025 = 738769) B738769
theorem B657347 : Blo 654306 657347 := bstep (se 1 (by rfl) ⟨493010, by rfl⟩ : syracuseStep 657347 = 986021) B986021
theorem B985043 : Blo 654306 985043 := bstep (se 1 (by rfl) ⟨738782, by rfl⟩ : syracuseStep 985043 = 1477565) B1477565
theorem B657363 : Blo 654306 657363 := bstep (se 1 (by rfl) ⟨493022, by rfl⟩ : syracuseStep 657363 = 986045) B986045
theorem B657379 : Blo 654306 657379 := bstep (se 1 (by rfl) ⟨493034, by rfl⟩ : syracuseStep 657379 = 986069) B986069
theorem B1476593 : Blo 654306 1476593 := bstep (se 2 (by rfl) ⟨553722, by rfl⟩ : syracuseStep 1476593 = 1107445) B1107445
theorem B985073 : Blo 654306 985073 := bstep (se 2 (by rfl) ⟨369402, by rfl⟩ : syracuseStep 985073 = 738805) B738805
theorem B657395 : Blo 654306 657395 := bstep (se 1 (by rfl) ⟨493046, by rfl⟩ : syracuseStep 657395 = 986093) B986093
theorem B1476611 : Blo 654306 1476611 := bstep (se 1 (by rfl) ⟨1107458, by rfl⟩ : syracuseStep 1476611 = 2214917) B2214917
theorem B985091 : Blo 654306 985091 := bstep (se 1 (by rfl) ⟨738818, by rfl⟩ : syracuseStep 985091 = 1477637) B1477637
theorem B657411 : Blo 654306 657411 := bstep (se 1 (by rfl) ⟨493058, by rfl⟩ : syracuseStep 657411 = 986117) B986117
theorem B2099213 : Blo 654306 2099213 := bstep (se 3 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 2099213 = 787205) B787205
theorem B657427 : Blo 654306 657427 := bstep (se 1 (by rfl) ⟨493070, by rfl⟩ : syracuseStep 657427 = 986141) B986141
theorem B985121 : Blo 654306 985121 := bstep (se 2 (by rfl) ⟨369420, by rfl⟩ : syracuseStep 985121 = 738841) B738841
theorem B657443 : Blo 654306 657443 := bstep (se 1 (by rfl) ⟨493082, by rfl⟩ : syracuseStep 657443 = 986165) B986165
theorem B985139 : Blo 654306 985139 := bstep (se 1 (by rfl) ⟨738854, by rfl⟩ : syracuseStep 985139 = 1477709) B1477709
theorem B657459 : Blo 654306 657459 := bstep (se 1 (by rfl) ⟨493094, by rfl⟩ : syracuseStep 657459 = 986189) B986189
theorem B657475 : Blo 654306 657475 := bstep (se 1 (by rfl) ⟨493106, by rfl⟩ : syracuseStep 657475 = 986213) B986213
theorem B985169 : Blo 654306 985169 := bstep (se 2 (by rfl) ⟨369438, by rfl⟩ : syracuseStep 985169 = 738877) B738877
theorem B657491 : Blo 654306 657491 := bstep (se 1 (by rfl) ⟨493118, by rfl⟩ : syracuseStep 657491 = 986237) B986237
theorem B985187 : Blo 654306 985187 := bstep (se 1 (by rfl) ⟨738890, by rfl⟩ : syracuseStep 985187 = 1477781) B1477781
theorem B657507 : Blo 654306 657507 := bstep (se 1 (by rfl) ⟨493130, by rfl⟩ : syracuseStep 657507 = 986261) B986261
theorem B657523 : Blo 654306 657523 := bstep (se 1 (by rfl) ⟨493142, by rfl⟩ : syracuseStep 657523 = 986285) B986285
theorem B985217 : Blo 654306 985217 := bstep (se 2 (by rfl) ⟨369456, by rfl⟩ : syracuseStep 985217 = 738913) B738913
theorem B657539 : Blo 654306 657539 := bstep (se 1 (by rfl) ⟨493154, by rfl⟩ : syracuseStep 657539 = 986309) B986309
theorem B985235 : Blo 654306 985235 := bstep (se 1 (by rfl) ⟨738926, by rfl⟩ : syracuseStep 985235 = 1477853) B1477853
theorem B657555 : Blo 654306 657555 := bstep (se 1 (by rfl) ⟨493166, by rfl⟩ : syracuseStep 657555 = 986333) B986333
theorem B1247395 : Blo 654306 1247395 := bstep (se 1 (by rfl) ⟨935546, by rfl⟩ : syracuseStep 1247395 = 1871093) B1871093
theorem B657571 : Blo 654306 657571 := bstep (se 1 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 657571 = 986357) B986357
theorem B985265 : Blo 654306 985265 := bstep (se 2 (by rfl) ⟨369474, by rfl⟩ : syracuseStep 985265 = 738949) B738949
theorem B657587 : Blo 654306 657587 := bstep (se 1 (by rfl) ⟨493190, by rfl⟩ : syracuseStep 657587 = 986381) B986381
theorem B985283 : Blo 654306 985283 := bstep (se 1 (by rfl) ⟨738962, by rfl⟩ : syracuseStep 985283 = 1477925) B1477925
theorem B657603 : Blo 654306 657603 := bstep (se 1 (by rfl) ⟨493202, by rfl⟩ : syracuseStep 657603 = 986405) B986405
theorem B657619 : Blo 654306 657619 := bstep (se 1 (by rfl) ⟨493214, by rfl⟩ : syracuseStep 657619 = 986429) B986429
theorem B985313 : Blo 654306 985313 := bstep (se 2 (by rfl) ⟨369492, by rfl⟩ : syracuseStep 985313 = 738985) B738985
theorem B657635 : Blo 654306 657635 := bstep (se 1 (by rfl) ⟨493226, by rfl⟩ : syracuseStep 657635 = 986453) B986453
theorem B985331 : Blo 654306 985331 := bstep (se 1 (by rfl) ⟨738998, by rfl⟩ : syracuseStep 985331 = 1477997) B1477997
theorem B657651 : Blo 654306 657651 := bstep (se 1 (by rfl) ⟨493238, by rfl⟩ : syracuseStep 657651 = 986477) B986477
theorem B657667 : Blo 654306 657667 := bstep (se 1 (by rfl) ⟨493250, by rfl⟩ : syracuseStep 657667 = 986501) B986501
theorem B1476881 : Blo 654306 1476881 := bstep (se 2 (by rfl) ⟨553830, by rfl⟩ : syracuseStep 1476881 = 1107661) B1107661
theorem B985361 : Blo 654306 985361 := bstep (se 2 (by rfl) ⟨369510, by rfl⟩ : syracuseStep 985361 = 739021) B739021
theorem B657683 : Blo 654306 657683 := bstep (se 1 (by rfl) ⟨493262, by rfl⟩ : syracuseStep 657683 = 986525) B986525
theorem B1476899 : Blo 654306 1476899 := bstep (se 1 (by rfl) ⟨1107674, by rfl⟩ : syracuseStep 1476899 = 2215349) B2215349
theorem B985379 : Blo 654306 985379 := bstep (se 1 (by rfl) ⟨739034, by rfl⟩ : syracuseStep 985379 = 1478069) B1478069
theorem B657699 : Blo 654306 657699 := bstep (se 1 (by rfl) ⟨493274, by rfl⟩ : syracuseStep 657699 = 986549) B986549
theorem B1575217 : Blo 654306 1575217 := bstep (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) B1181413
theorem B657715 : Blo 654306 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B985409 : Blo 654306 985409 := bstep (se 2 (by rfl) ⟨369528, by rfl⟩ : syracuseStep 985409 = 739057) B739057
theorem B1247555 : Blo 654306 1247555 := bstep (se 1 (by rfl) ⟨935666, by rfl⟩ : syracuseStep 1247555 = 1871333) B1871333
theorem B657731 : Blo 654306 657731 := bstep (se 1 (by rfl) ⟨493298, by rfl⟩ : syracuseStep 657731 = 986597) B986597
theorem B985427 : Blo 654306 985427 := bstep (se 1 (by rfl) ⟨739070, by rfl⟩ : syracuseStep 985427 = 1478141) B1478141
theorem B657747 : Blo 654306 657747 := bstep (se 1 (by rfl) ⟨493310, by rfl⟩ : syracuseStep 657747 = 986621) B986621
theorem B657763 : Blo 654306 657763 := bstep (se 1 (by rfl) ⟨493322, by rfl⟩ : syracuseStep 657763 = 986645) B986645
theorem B985457 : Blo 654306 985457 := bstep (se 2 (by rfl) ⟨369546, by rfl⟩ : syracuseStep 985457 = 739093) B739093
theorem B657779 : Blo 654306 657779 := bstep (se 1 (by rfl) ⟨493334, by rfl⟩ : syracuseStep 657779 = 986669) B986669
theorem B985475 : Blo 654306 985475 := bstep (se 1 (by rfl) ⟨739106, by rfl⟩ : syracuseStep 985475 = 1478213) B1478213
theorem B657795 : Blo 654306 657795 := bstep (se 1 (by rfl) ⟨493346, by rfl⟩ : syracuseStep 657795 = 986693) B986693
theorem B657811 : Blo 654306 657811 := bstep (se 1 (by rfl) ⟨493358, by rfl⟩ : syracuseStep 657811 = 986717) B986717
theorem B985505 : Blo 654306 985505 := bstep (se 2 (by rfl) ⟨369564, by rfl⟩ : syracuseStep 985505 = 739129) B739129
theorem B657827 : Blo 654306 657827 := bstep (se 1 (by rfl) ⟨493370, by rfl⟩ : syracuseStep 657827 = 986741) B986741
theorem B4196785 : Blo 654306 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B985523 : Blo 654306 985523 := bstep (se 1 (by rfl) ⟨739142, by rfl⟩ : syracuseStep 985523 = 1478285) B1478285
theorem B657843 : Blo 654306 657843 := bstep (se 1 (by rfl) ⟨493382, by rfl⟩ : syracuseStep 657843 = 986765) B986765
theorem B657859 : Blo 654306 657859 := bstep (se 1 (by rfl) ⟨493394, by rfl⟩ : syracuseStep 657859 = 986789) B986789
theorem B985553 : Blo 654306 985553 := bstep (se 2 (by rfl) ⟨369582, by rfl⟩ : syracuseStep 985553 = 739165) B739165
theorem B657875 : Blo 654306 657875 := bstep (se 1 (by rfl) ⟨493406, by rfl⟩ : syracuseStep 657875 = 986813) B986813
theorem B985571 : Blo 654306 985571 := bstep (se 1 (by rfl) ⟨739178, by rfl⟩ : syracuseStep 985571 = 1478357) B1478357
theorem B657891 : Blo 654306 657891 := bstep (se 1 (by rfl) ⟨493418, by rfl⟩ : syracuseStep 657891 = 986837) B986837
theorem B5409251 : Blo 654306 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B657907 : Blo 654306 657907 := bstep (se 1 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 657907 = 986861) B986861
theorem B985601 : Blo 654306 985601 := bstep (se 2 (by rfl) ⟨369600, by rfl⟩ : syracuseStep 985601 = 739201) B739201
theorem B1051139 : Blo 654306 1051139 := bstep (se 1 (by rfl) ⟨788354, by rfl⟩ : syracuseStep 1051139 = 1576709) B1576709
theorem B657923 : Blo 654306 657923 := bstep (se 1 (by rfl) ⟨493442, by rfl⟩ : syracuseStep 657923 = 986885) B986885
theorem B985619 : Blo 654306 985619 := bstep (se 1 (by rfl) ⟨739214, by rfl⟩ : syracuseStep 985619 = 1478429) B1478429
theorem B657939 : Blo 654306 657939 := bstep (se 1 (by rfl) ⟨493454, by rfl⟩ : syracuseStep 657939 = 986909) B986909
theorem B657955 : Blo 654306 657955 := bstep (se 1 (by rfl) ⟨493466, by rfl⟩ : syracuseStep 657955 = 986933) B986933
theorem B2361905 : Blo 654306 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1477169 : Blo 654306 1477169 := bstep (se 2 (by rfl) ⟨553938, by rfl⟩ : syracuseStep 1477169 = 1107877) B1107877
theorem B985649 : Blo 654306 985649 := bstep (se 2 (by rfl) ⟨369618, by rfl⟩ : syracuseStep 985649 = 739237) B739237
theorem B657971 : Blo 654306 657971 := bstep (se 1 (by rfl) ⟨493478, by rfl⟩ : syracuseStep 657971 = 986957) B986957
theorem B1477187 : Blo 654306 1477187 := bstep (se 1 (by rfl) ⟨1107890, by rfl⟩ : syracuseStep 1477187 = 2215781) B2215781
theorem B985667 : Blo 654306 985667 := bstep (se 1 (by rfl) ⟨739250, by rfl⟩ : syracuseStep 985667 = 1478501) B1478501
theorem B657987 : Blo 654306 657987 := bstep (se 1 (by rfl) ⟨493490, by rfl⟩ : syracuseStep 657987 = 986981) B986981
theorem B658003 : Blo 654306 658003 := bstep (se 1 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 658003 = 987005) B987005
theorem B985697 : Blo 654306 985697 := bstep (se 2 (by rfl) ⟨369636, by rfl⟩ : syracuseStep 985697 = 739273) B739273
theorem B658019 : Blo 654306 658019 := bstep (se 1 (by rfl) ⟨493514, by rfl⟩ : syracuseStep 658019 = 987029) B987029
theorem B985715 : Blo 654306 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B658035 : Blo 654306 658035 := bstep (se 1 (by rfl) ⟨493526, by rfl⟩ : syracuseStep 658035 = 987053) B987053
theorem B658051 : Blo 654306 658051 := bstep (se 1 (by rfl) ⟨493538, by rfl⟩ : syracuseStep 658051 = 987077) B987077
theorem B985745 : Blo 654306 985745 := bstep (se 2 (by rfl) ⟨369654, by rfl⟩ : syracuseStep 985745 = 739309) B739309
theorem B658067 : Blo 654306 658067 := bstep (se 1 (by rfl) ⟨493550, by rfl⟩ : syracuseStep 658067 = 987101) B987101
theorem B985763 : Blo 654306 985763 := bstep (se 1 (by rfl) ⟨739322, by rfl⟩ : syracuseStep 985763 = 1478645) B1478645
theorem B658083 : Blo 654306 658083 := bstep (se 1 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 658083 = 987125) B987125
theorem B658099 : Blo 654306 658099 := bstep (se 1 (by rfl) ⟨493574, by rfl⟩ : syracuseStep 658099 = 987149) B987149
theorem B985793 : Blo 654306 985793 := bstep (se 2 (by rfl) ⟨369672, by rfl⟩ : syracuseStep 985793 = 739345) B739345
theorem B658115 : Blo 654306 658115 := bstep (se 1 (by rfl) ⟨493586, by rfl⟩ : syracuseStep 658115 = 987173) B987173
theorem B985811 : Blo 654306 985811 := bstep (se 1 (by rfl) ⟨739358, by rfl⟩ : syracuseStep 985811 = 1478717) B1478717
theorem B658131 : Blo 654306 658131 := bstep (se 1 (by rfl) ⟨493598, by rfl⟩ : syracuseStep 658131 = 987197) B987197
theorem B658147 : Blo 654306 658147 := bstep (se 1 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 658147 = 987221) B987221
theorem B985841 : Blo 654306 985841 := bstep (se 2 (by rfl) ⟨369690, by rfl⟩ : syracuseStep 985841 = 739381) B739381
theorem B658163 : Blo 654306 658163 := bstep (se 1 (by rfl) ⟨493622, by rfl⟩ : syracuseStep 658163 = 987245) B987245
theorem B985859 : Blo 654306 985859 := bstep (se 1 (by rfl) ⟨739394, by rfl⟩ : syracuseStep 985859 = 1478789) B1478789
theorem B658179 : Blo 654306 658179 := bstep (se 1 (by rfl) ⟨493634, by rfl⟩ : syracuseStep 658179 = 987269) B987269
theorem B658195 : Blo 654306 658195 := bstep (se 1 (by rfl) ⟨493646, by rfl⟩ : syracuseStep 658195 = 987293) B987293
theorem B985889 : Blo 654306 985889 := bstep (se 2 (by rfl) ⟨369708, by rfl⟩ : syracuseStep 985889 = 739417) B739417
theorem B658211 : Blo 654306 658211 := bstep (se 1 (by rfl) ⟨493658, by rfl⟩ : syracuseStep 658211 = 987317) B987317
theorem B985907 : Blo 654306 985907 := bstep (se 1 (by rfl) ⟨739430, by rfl⟩ : syracuseStep 985907 = 1478861) B1478861
theorem B658227 : Blo 654306 658227 := bstep (se 1 (by rfl) ⟨493670, by rfl⟩ : syracuseStep 658227 = 987341) B987341
theorem B658243 : Blo 654306 658243 := bstep (se 1 (by rfl) ⟨493682, by rfl⟩ : syracuseStep 658243 = 987365) B987365
theorem B1477457 : Blo 654306 1477457 := bstep (se 2 (by rfl) ⟨554046, by rfl⟩ : syracuseStep 1477457 = 1108093) B1108093
theorem B985937 : Blo 654306 985937 := bstep (se 2 (by rfl) ⟨369726, by rfl⟩ : syracuseStep 985937 = 739453) B739453
theorem B658259 : Blo 654306 658259 := bstep (se 1 (by rfl) ⟨493694, by rfl⟩ : syracuseStep 658259 = 987389) B987389
theorem B1477475 : Blo 654306 1477475 := bstep (se 1 (by rfl) ⟨1108106, by rfl⟩ : syracuseStep 1477475 = 2216213) B2216213
theorem B985955 : Blo 654306 985955 := bstep (se 1 (by rfl) ⟨739466, by rfl⟩ : syracuseStep 985955 = 1478933) B1478933
theorem B658275 : Blo 654306 658275 := bstep (se 1 (by rfl) ⟨493706, by rfl⟩ : syracuseStep 658275 = 987413) B987413
theorem B1870705 : Blo 654306 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B658291 : Blo 654306 658291 := bstep (se 1 (by rfl) ⟨493718, by rfl⟩ : syracuseStep 658291 = 987437) B987437
theorem B985985 : Blo 654306 985985 := bstep (se 2 (by rfl) ⟨369744, by rfl⟩ : syracuseStep 985985 = 739489) B739489
theorem B1182595 : Blo 654306 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B986003 : Blo 654306 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B986033 : Blo 654306 986033 := bstep (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) B739525
theorem B986051 : Blo 654306 986051 := bstep (se 1 (by rfl) ⟨739538, by rfl⟩ : syracuseStep 986051 = 1479077) B1479077
theorem B986081 : Blo 654306 986081 := bstep (se 2 (by rfl) ⟨369780, by rfl⟩ : syracuseStep 986081 = 739561) B739561
theorem B986099 : Blo 654306 986099 := bstep (se 1 (by rfl) ⟨739574, by rfl⟩ : syracuseStep 986099 = 1479149) B1479149
theorem B1051651 : Blo 654306 1051651 := bstep (se 1 (by rfl) ⟨788738, by rfl⟩ : syracuseStep 1051651 = 1577477) B1577477
theorem B986129 : Blo 654306 986129 := bstep (se 2 (by rfl) ⟨369798, by rfl⟩ : syracuseStep 986129 = 739597) B739597
theorem B986147 : Blo 654306 986147 := bstep (se 1 (by rfl) ⟨739610, by rfl⟩ : syracuseStep 986147 = 1479221) B1479221
theorem B986177 : Blo 654306 986177 := bstep (se 2 (by rfl) ⟨369816, by rfl⟩ : syracuseStep 986177 = 739633) B739633
theorem B986195 : Blo 654306 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B1477745 : Blo 654306 1477745 := bstep (se 2 (by rfl) ⟨554154, by rfl⟩ : syracuseStep 1477745 = 1108309) B1108309
theorem B986225 : Blo 654306 986225 := bstep (se 2 (by rfl) ⟨369834, by rfl⟩ : syracuseStep 986225 = 739669) B739669
theorem B1477763 : Blo 654306 1477763 := bstep (se 1 (by rfl) ⟨1108322, by rfl⟩ : syracuseStep 1477763 = 2216645) B2216645
theorem B986243 : Blo 654306 986243 := bstep (se 1 (by rfl) ⟨739682, by rfl⟩ : syracuseStep 986243 = 1479365) B1479365
theorem B986273 : Blo 654306 986273 := bstep (se 2 (by rfl) ⟨369852, by rfl⟩ : syracuseStep 986273 = 739705) B739705
theorem B986291 : Blo 654306 986291 := bstep (se 1 (by rfl) ⟨739718, by rfl⟩ : syracuseStep 986291 = 1479437) B1479437
theorem B986321 : Blo 654306 986321 := bstep (se 2 (by rfl) ⟨369870, by rfl⟩ : syracuseStep 986321 = 739741) B739741
theorem B986339 : Blo 654306 986339 := bstep (se 1 (by rfl) ⟨739754, by rfl⟩ : syracuseStep 986339 = 1479509) B1479509
theorem B986369 : Blo 654306 986369 := bstep (se 2 (by rfl) ⟨369888, by rfl⟩ : syracuseStep 986369 = 739777) B739777
theorem B986387 : Blo 654306 986387 := bstep (se 1 (by rfl) ⟨739790, by rfl⟩ : syracuseStep 986387 = 1479581) B1479581
theorem B986417 : Blo 654306 986417 := bstep (se 2 (by rfl) ⟨369906, by rfl⟩ : syracuseStep 986417 = 739813) B739813
theorem B986435 : Blo 654306 986435 := bstep (se 1 (by rfl) ⟨739826, by rfl⟩ : syracuseStep 986435 = 1479653) B1479653
theorem B2493773 : Blo 654306 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B986465 : Blo 654306 986465 := bstep (se 2 (by rfl) ⟨369924, by rfl⟩ : syracuseStep 986465 = 739849) B739849
theorem B8981873 : Blo 654306 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B1248625 : Blo 654306 1248625 := bstep (se 2 (by rfl) ⟨468234, by rfl⟩ : syracuseStep 1248625 = 936469) B936469
theorem B986483 : Blo 654306 986483 := bstep (se 1 (by rfl) ⟨739862, by rfl⟩ : syracuseStep 986483 = 1479725) B1479725
theorem B1478033 : Blo 654306 1478033 := bstep (se 2 (by rfl) ⟨554262, by rfl⟩ : syracuseStep 1478033 = 1108525) B1108525
theorem B986513 : Blo 654306 986513 := bstep (se 2 (by rfl) ⟨369942, by rfl⟩ : syracuseStep 986513 = 739885) B739885
theorem B1478051 : Blo 654306 1478051 := bstep (se 1 (by rfl) ⟨1108538, by rfl⟩ : syracuseStep 1478051 = 2217077) B2217077
theorem B986531 : Blo 654306 986531 := bstep (se 1 (by rfl) ⟨739898, by rfl⟩ : syracuseStep 986531 = 1479797) B1479797
theorem B986561 : Blo 654306 986561 := bstep (se 2 (by rfl) ⟨369960, by rfl⟩ : syracuseStep 986561 = 739921) B739921
theorem B986579 : Blo 654306 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B986609 : Blo 654306 986609 := bstep (se 2 (by rfl) ⟨369978, by rfl⟩ : syracuseStep 986609 = 739957) B739957
theorem B986627 : Blo 654306 986627 := bstep (se 1 (by rfl) ⟨739970, by rfl⟩ : syracuseStep 986627 = 1479941) B1479941
theorem B986657 : Blo 654306 986657 := bstep (se 2 (by rfl) ⟨369996, by rfl⟩ : syracuseStep 986657 = 739993) B739993
theorem B1052195 : Blo 654306 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B986675 : Blo 654306 986675 := bstep (se 1 (by rfl) ⟨740006, by rfl⟩ : syracuseStep 986675 = 1480013) B1480013
theorem B986705 : Blo 654306 986705 := bstep (se 2 (by rfl) ⟨370014, by rfl⟩ : syracuseStep 986705 = 740029) B740029
theorem B986723 : Blo 654306 986723 := bstep (se 1 (by rfl) ⟨740042, by rfl⟩ : syracuseStep 986723 = 1480085) B1480085
theorem B986753 : Blo 654306 986753 := bstep (se 2 (by rfl) ⟨370032, by rfl⟩ : syracuseStep 986753 = 740065) B740065
theorem B986771 : Blo 654306 986771 := bstep (se 1 (by rfl) ⟨740078, by rfl⟩ : syracuseStep 986771 = 1480157) B1480157
theorem B1478321 : Blo 654306 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B986801 : Blo 654306 986801 := bstep (se 2 (by rfl) ⟨370050, by rfl⟩ : syracuseStep 986801 = 740101) B740101
theorem B888499 : Blo 654306 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B1478339 : Blo 654306 1478339 := bstep (se 1 (by rfl) ⟨1108754, by rfl⟩ : syracuseStep 1478339 = 2217509) B2217509
theorem B986819 : Blo 654306 986819 := bstep (se 1 (by rfl) ⟨740114, by rfl⟩ : syracuseStep 986819 = 1480229) B1480229
theorem B1052369 : Blo 654306 1052369 := bstep (se 2 (by rfl) ⟨394638, by rfl⟩ : syracuseStep 1052369 = 789277) B789277
theorem B986849 : Blo 654306 986849 := bstep (se 2 (by rfl) ⟨370068, by rfl⟩ : syracuseStep 986849 = 740137) B740137
theorem B986867 : Blo 654306 986867 := bstep (se 1 (by rfl) ⟨740150, by rfl⟩ : syracuseStep 986867 = 1480301) B1480301
theorem B3739405 : Blo 654306 3739405 := bstep (se 3 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 3739405 = 1402277) B1402277
theorem B986897 : Blo 654306 986897 := bstep (se 2 (by rfl) ⟨370086, by rfl⟩ : syracuseStep 986897 = 740173) B740173
theorem B986915 : Blo 654306 986915 := bstep (se 1 (by rfl) ⟨740186, by rfl⟩ : syracuseStep 986915 = 1480373) B1480373
theorem B790339 : Blo 654306 790339 := bstep (se 1 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 790339 = 1185509) B1185509
theorem B986945 : Blo 654306 986945 := bstep (se 2 (by rfl) ⟨370104, by rfl⟩ : syracuseStep 986945 = 740209) B740209
theorem B986963 : Blo 654306 986963 := bstep (se 1 (by rfl) ⟨740222, by rfl⟩ : syracuseStep 986963 = 1480445) B1480445
theorem B986993 : Blo 654306 986993 := bstep (se 2 (by rfl) ⟨370122, by rfl⟩ : syracuseStep 986993 = 740245) B740245
theorem B987011 : Blo 654306 987011 := bstep (se 1 (by rfl) ⟨740258, by rfl⟩ : syracuseStep 987011 = 1480517) B1480517
theorem B987041 : Blo 654306 987041 := bstep (se 2 (by rfl) ⟨370140, by rfl⟩ : syracuseStep 987041 = 740281) B740281
theorem B987059 : Blo 654306 987059 := bstep (se 1 (by rfl) ⟨740294, by rfl⟩ : syracuseStep 987059 = 1480589) B1480589
theorem B1478609 : Blo 654306 1478609 := bstep (se 2 (by rfl) ⟨554478, by rfl⟩ : syracuseStep 1478609 = 1108957) B1108957
theorem B987089 : Blo 654306 987089 := bstep (se 2 (by rfl) ⟨370158, by rfl⟩ : syracuseStep 987089 = 740317) B740317
theorem B1773539 : Blo 654306 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B1478627 : Blo 654306 1478627 := bstep (se 1 (by rfl) ⟨1108970, by rfl⟩ : syracuseStep 1478627 = 2217941) B2217941
theorem B987107 : Blo 654306 987107 := bstep (se 1 (by rfl) ⟨740330, by rfl⟩ : syracuseStep 987107 = 1480661) B1480661
theorem B987137 : Blo 654306 987137 := bstep (se 2 (by rfl) ⟨370176, by rfl⟩ : syracuseStep 987137 = 740353) B740353
theorem B987155 : Blo 654306 987155 := bstep (se 1 (by rfl) ⟨740366, by rfl⟩ : syracuseStep 987155 = 1480733) B1480733
theorem B987185 : Blo 654306 987185 := bstep (se 2 (by rfl) ⟨370194, by rfl⟩ : syracuseStep 987185 = 740389) B740389
theorem B2101315 : Blo 654306 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B987203 : Blo 654306 987203 := bstep (se 1 (by rfl) ⟨740402, by rfl⟩ : syracuseStep 987203 = 1480805) B1480805
theorem B4984901 : Blo 654306 4984901 := bstep (se 4 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 4984901 = 934669) B934669
theorem B987233 : Blo 654306 987233 := bstep (se 2 (by rfl) ⟨370212, by rfl⟩ : syracuseStep 987233 = 740425) B740425
theorem B1871981 : Blo 654306 1871981 := bstep (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) B701993
theorem B2494577 : Blo 654306 2494577 := bstep (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) B1870933
theorem B987251 : Blo 654306 987251 := bstep (se 1 (by rfl) ⟨740438, by rfl⟩ : syracuseStep 987251 = 1480877) B1480877
theorem B1216657 : Blo 654306 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B987281 : Blo 654306 987281 := bstep (se 2 (by rfl) ⟨370230, by rfl⟩ : syracuseStep 987281 = 740461) B740461
theorem B3543203 : Blo 654306 3543203 := bstep (se 1 (by rfl) ⟨2657402, by rfl⟩ : syracuseStep 3543203 = 5314805) B5314805
theorem B987299 : Blo 654306 987299 := bstep (se 1 (by rfl) ⟨740474, by rfl⟩ : syracuseStep 987299 = 1480949) B1480949
theorem B987329 : Blo 654306 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B2101457 : Blo 654306 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B987347 : Blo 654306 987347 := bstep (se 1 (by rfl) ⟨740510, by rfl⟩ : syracuseStep 987347 = 1481021) B1481021
theorem B1478897 : Blo 654306 1478897 := bstep (se 2 (by rfl) ⟨554586, by rfl⟩ : syracuseStep 1478897 = 1109173) B1109173
theorem B987377 : Blo 654306 987377 := bstep (se 2 (by rfl) ⟨370266, by rfl⟩ : syracuseStep 987377 = 740533) B740533
theorem B1478915 : Blo 654306 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B987395 : Blo 654306 987395 := bstep (se 1 (by rfl) ⟨740546, by rfl⟩ : syracuseStep 987395 = 1481093) B1481093
theorem B987425 : Blo 654306 987425 := bstep (se 2 (by rfl) ⟨370284, by rfl⟩ : syracuseStep 987425 = 740569) B740569
theorem B1872163 : Blo 654306 1872163 := bstep (se 1 (by rfl) ⟨1404122, by rfl⟩ : syracuseStep 1872163 = 2808245) B2808245
theorem B987443 : Blo 654306 987443 := bstep (se 1 (by rfl) ⟨740582, by rfl⟩ : syracuseStep 987443 = 1481165) B1481165
theorem B1872209 : Blo 654306 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B3314033 : Blo 654306 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B1249681 : Blo 654306 1249681 := bstep (se 2 (by rfl) ⟨468630, by rfl⟩ : syracuseStep 1249681 = 937261) B937261
theorem B1479185 : Blo 654306 1479185 := bstep (se 2 (by rfl) ⟨554694, by rfl⟩ : syracuseStep 1479185 = 1109389) B1109389
theorem B1479203 : Blo 654306 1479203 := bstep (se 1 (by rfl) ⟨1109402, by rfl⟩ : syracuseStep 1479203 = 2218805) B2218805
theorem B15340085 : Blo 654306 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B1348177 : Blo 654306 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B889537 : Blo 654306 889537 := bstep (se 2 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 889537 = 667153) B667153
theorem B4264645 : Blo 654306 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B2495245 : Blo 654306 2495245 := bstep (se 3 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 2495245 = 935717) B935717
theorem B1479473 : Blo 654306 1479473 := bstep (se 2 (by rfl) ⟨554802, by rfl⟩ : syracuseStep 1479473 = 1109605) B1109605
theorem B10654517 : Blo 654306 10654517 := bstep (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) B998861
theorem B1479491 : Blo 654306 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B2987021 : Blo 654306 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B8000525 : Blo 654306 8000525 := bstep (se 3 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 8000525 = 3000197) B3000197
theorem B1479761 : Blo 654306 1479761 := bstep (se 2 (by rfl) ⟨554910, by rfl⟩ : syracuseStep 1479761 = 1109821) B1109821
theorem B1479779 : Blo 654306 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B5608561 : Blo 654306 5608561 := bstep (se 2 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 5608561 = 4206421) B4206421
theorem B2364643 : Blo 654306 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B1578275 : Blo 654306 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B1480049 : Blo 654306 1480049 := bstep (se 2 (by rfl) ⟨555018, by rfl⟩ : syracuseStep 1480049 = 1110037) B1110037
theorem B1480067 : Blo 654306 1480067 := bstep (se 1 (by rfl) ⟨1110050, by rfl⟩ : syracuseStep 1480067 = 2220101) B2220101
theorem B2496035 : Blo 654306 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1775213 : Blo 654306 1775213 := bstep (se 3 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 1775213 = 665705) B665705
theorem B3544717 : Blo 654306 3544717 := bstep (se 3 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 3544717 = 1329269) B1329269
theorem B1480337 : Blo 654306 1480337 := bstep (se 2 (by rfl) ⟨555126, by rfl⟩ : syracuseStep 1480337 = 1110253) B1110253
theorem B1480355 : Blo 654306 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B1054387 : Blo 654306 1054387 := bstep (se 1 (by rfl) ⟨790790, by rfl⟩ : syracuseStep 1054387 = 1581581) B1581581
theorem B3741389 : Blo 654306 3741389 := bstep (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) B1403021
theorem B1054451 : Blo 654306 1054451 := bstep (se 1 (by rfl) ⟨790838, by rfl⟩ : syracuseStep 1054451 = 1581677) B1581677
theorem B1775363 : Blo 654306 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B1873667 : Blo 654306 1873667 := bstep (se 1 (by rfl) ⟨1405250, by rfl⟩ : syracuseStep 1873667 = 2810501) B2810501
theorem B3315491 : Blo 654306 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B1120081 : Blo 654306 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B1775537 : Blo 654306 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1480625 : Blo 654306 1480625 := bstep (se 2 (by rfl) ⟨555234, by rfl⟩ : syracuseStep 1480625 = 1110469) B1110469
theorem B1480643 : Blo 654306 1480643 := bstep (se 1 (by rfl) ⟨1110482, by rfl⟩ : syracuseStep 1480643 = 2220965) B2220965
theorem B11999173 : Blo 654306 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B5314673 : Blo 654306 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B1579121 : Blo 654306 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B2496689 : Blo 654306 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B1480913 : Blo 654306 1480913 := bstep (se 2 (by rfl) ⟨555342, by rfl⟩ : syracuseStep 1480913 = 1110685) B1110685
theorem B1480931 : Blo 654306 1480931 := bstep (se 1 (by rfl) ⟨1110698, by rfl⟩ : syracuseStep 1480931 = 2221397) B2221397
theorem B1579331 : Blo 654306 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B2103853 : Blo 654306 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B3316301 : Blo 654306 3316301 := bstep (se 3 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 3316301 = 1243613) B1243613
theorem B3742321 : Blo 654306 3742321 := bstep (se 2 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 3742321 = 2806741) B2806741
theorem B1121297 : Blo 654306 1121297 := bstep (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) B840973
theorem B2530801 : Blo 654306 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B1580561 : Blo 654306 1580561 := bstep (se 2 (by rfl) ⟨592710, by rfl⟩ : syracuseStep 1580561 = 1185421) B1185421
theorem B2498147 : Blo 654306 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B2498161 : Blo 654306 2498161 := bstep (se 2 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 2498161 = 1873621) B1873621
theorem B4202117 : Blo 654306 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B1580753 : Blo 654306 1580753 := bstep (se 2 (by rfl) ⟨592782, by rfl⟩ : syracuseStep 1580753 = 1185565) B1185565
theorem B1777571 : Blo 654306 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B3743779 : Blo 654306 3743779 := bstep (se 1 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 3743779 = 5615669) B5615669
theorem B3285233 : Blo 654306 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B1122707 : Blo 654306 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B8430065 : Blo 654306 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B3744305 : Blo 654306 3744305 := bstep (se 2 (by rfl) ⟨1404114, by rfl⟩ : syracuseStep 3744305 = 2808229) B2808229
theorem B828787 : Blo 654306 828787 := bstep (se 1 (by rfl) ⟨621590, by rfl⟩ : syracuseStep 828787 = 1243181) B1243181
theorem B664979 : Blo 654306 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B2663857 : Blo 654306 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B3319217 : Blo 654306 3319217 := bstep (se 2 (by rfl) ⟨1244706, by rfl⟩ : syracuseStep 3319217 = 2489413) B2489413
theorem B828883 : Blo 654306 828883 := bstep (se 1 (by rfl) ⟨621662, by rfl⟩ : syracuseStep 828883 = 1243325) B1243325
theorem B2795107 : Blo 654306 2795107 := bstep (se 1 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 2795107 = 4192661) B4192661
theorem B4990733 : Blo 654306 4990733 := bstep (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) B1871525
theorem B2107235 : Blo 654306 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B3549041 : Blo 654306 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B829379 : Blo 654306 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B6301637 : Blo 654306 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B3745763 : Blo 654306 3745763 := bstep (se 1 (by rfl) ⟨2809322, by rfl⟩ : syracuseStep 3745763 = 5618645) B5618645
theorem B1681507 : Blo 654306 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B7088309 : Blo 654306 7088309 := bstep (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) B664529
theorem B1681681 : Blo 654306 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B5613893 : Blo 654306 5613893 := bstep (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) B1052605
theorem B1124705 : Blo 654306 1124705 := bstep (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) B843529
theorem B830083 : Blo 654306 830083 := bstep (se 1 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 830083 = 1245125) B1245125
theorem B2108081 : Blo 654306 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B830179 : Blo 654306 830179 := bstep (se 1 (by rfl) ⟨622634, by rfl⟩ : syracuseStep 830179 = 1245269) B1245269
theorem B699187 : Blo 654306 699187 := bstep (se 1 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 699187 = 1048781) B1048781
theorem B3320675 : Blo 654306 3320675 := bstep (se 1 (by rfl) ⟨2490506, by rfl⟩ : syracuseStep 3320675 = 4981013) B4981013
theorem B8432525 : Blo 654306 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B830675 : Blo 654306 830675 := bstep (se 1 (by rfl) ⟨623006, by rfl⟩ : syracuseStep 830675 = 1246013) B1246013
theorem B699635 : Blo 654306 699635 := bstep (se 1 (by rfl) ⟨524726, by rfl⟩ : syracuseStep 699635 = 1049453) B1049453
theorem B2370829 : Blo 654306 2370829 := bstep (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) B889061
theorem B1125827 : Blo 654306 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B2797105 : Blo 654306 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B994945 : Blo 654306 994945 := bstep (se 2 (by rfl) ⟨373104, by rfl⟩ : syracuseStep 994945 = 746209) B746209
theorem B3321485 : Blo 654306 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B3747653 : Blo 654306 3747653 := bstep (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) B702685
theorem B15150989 : Blo 654306 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B831379 : Blo 654306 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B3190691 : Blo 654306 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B831475 : Blo 654306 831475 := bstep (se 1 (by rfl) ⟨623606, by rfl⟩ : syracuseStep 831475 = 1247213) B1247213
theorem B831971 : Blo 654306 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B701011 : Blo 654306 701011 := bstep (se 1 (by rfl) ⟨525758, by rfl⟩ : syracuseStep 701011 = 1051517) B1051517
theorem B4993649 : Blo 654306 4993649 := bstep (se 2 (by rfl) ⟨1872618, by rfl⟩ : syracuseStep 4993649 = 3745237) B3745237
theorem B2208653 : Blo 654306 2208653 := bstep (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) B828245
theorem B2208707 : Blo 654306 2208707 := bstep (se 1 (by rfl) ⟨1656530, by rfl⟩ : syracuseStep 2208707 = 3313061) B3313061
theorem B7189573 : Blo 654306 7189573 := bstep (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) B1348045
theorem B12629105 : Blo 654306 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B832675 : Blo 654306 832675 := bstep (se 1 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 832675 = 1249013) B1249013
theorem B2208977 : Blo 654306 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B1684739 : Blo 654306 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B832771 : Blo 654306 832771 := bstep (se 1 (by rfl) ⟨624578, by rfl⟩ : syracuseStep 832771 = 1249157) B1249157
theorem B5682659 : Blo 654306 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2209517 : Blo 654306 2209517 := bstep (se 3 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 2209517 = 828569) B828569
theorem B2209571 : Blo 654306 2209571 := bstep (se 1 (by rfl) ⟨1657178, by rfl⟩ : syracuseStep 2209571 = 3314357) B3314357
theorem B702275 : Blo 654306 702275 := bstep (se 1 (by rfl) ⟨526706, by rfl⟩ : syracuseStep 702275 = 1053413) B1053413
theorem B1259473 : Blo 654306 1259473 := bstep (se 2 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 1259473 = 944605) B944605
theorem B2209841 : Blo 654306 2209841 := bstep (se 2 (by rfl) ⟨828690, by rfl⟩ : syracuseStep 2209841 = 1657381) B1657381
theorem B3553541 : Blo 654306 3553541 := bstep (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) B666289
theorem B2242883 : Blo 654306 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B932323 : Blo 654306 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B3324401 : Blo 654306 3324401 := bstep (se 2 (by rfl) ⟨1246650, by rfl⟩ : syracuseStep 3324401 = 2493301) B2493301
theorem B2210381 : Blo 654306 2210381 := bstep (se 3 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 2210381 = 828893) B828893
theorem B2210435 : Blo 654306 2210435 := bstep (se 1 (by rfl) ⟨1657826, by rfl⟩ : syracuseStep 2210435 = 3315653) B3315653
theorem B7977653 : Blo 654306 7977653 := bstep (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) B747905
theorem B1686353 : Blo 654306 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B2210705 : Blo 654306 2210705 := bstep (se 2 (by rfl) ⟨829014, by rfl⟩ : syracuseStep 2210705 = 1658029) B1658029
theorem B932801 : Blo 654306 932801 := bstep (se 2 (by rfl) ⟨349800, by rfl⟩ : syracuseStep 932801 = 699601) B699601
theorem B736195 : Blo 654306 736195 := bstep (se 1 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 736195 = 1104293) B1104293
theorem B932915 : Blo 654306 932915 := bstep (se 1 (by rfl) ⟨699686, by rfl⟩ : syracuseStep 932915 = 1399373) B1399373
theorem B736339 : Blo 654306 736339 := bstep (se 1 (by rfl) ⟨552254, by rfl⟩ : syracuseStep 736339 = 1104509) B1104509
theorem B998497 : Blo 654306 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B932995 : Blo 654306 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B2997425 : Blo 654306 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B736483 : Blo 654306 736483 := bstep (se 1 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 736483 = 1104725) B1104725
theorem B736627 : Blo 654306 736627 := bstep (se 1 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 736627 = 1104941) B1104941
theorem B2211245 : Blo 654306 2211245 := bstep (se 3 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 2211245 = 829217) B829217
theorem B2211299 : Blo 654306 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B2801137 : Blo 654306 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B736771 : Blo 654306 736771 := bstep (se 1 (by rfl) ⟨552578, by rfl⟩ : syracuseStep 736771 = 1105157) B1105157
theorem B1064545 : Blo 654306 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B3358307 : Blo 654306 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B736915 : Blo 654306 736915 := bstep (se 1 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 736915 = 1105373) B1105373
theorem B1326755 : Blo 654306 1326755 := bstep (se 1 (by rfl) ⟨995066, by rfl⟩ : syracuseStep 1326755 = 1990133) B1990133
theorem B933553 : Blo 654306 933553 := bstep (se 2 (by rfl) ⟨350082, by rfl⟩ : syracuseStep 933553 = 700165) B700165
theorem B2211569 : Blo 654306 2211569 := bstep (se 2 (by rfl) ⟨829338, by rfl⟩ : syracuseStep 2211569 = 1658677) B1658677
theorem B737059 : Blo 654306 737059 := bstep (se 1 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 737059 = 1105589) B1105589
theorem B60702605 : Blo 654306 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B3325859 : Blo 654306 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B737203 : Blo 654306 737203 := bstep (se 1 (by rfl) ⟨552902, by rfl⟩ : syracuseStep 737203 = 1105805) B1105805
theorem B1294321 : Blo 654306 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B737347 : Blo 654306 737347 := bstep (se 1 (by rfl) ⟨553010, by rfl⟩ : syracuseStep 737347 = 1106021) B1106021
theorem B737491 : Blo 654306 737491 := bstep (se 1 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 737491 = 1106237) B1106237
theorem B2212109 : Blo 654306 2212109 := bstep (se 3 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 2212109 = 829541) B829541
theorem B2212163 : Blo 654306 2212163 := bstep (se 1 (by rfl) ⟨1659122, by rfl⟩ : syracuseStep 2212163 = 3318245) B3318245
theorem B999761 : Blo 654306 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B737635 : Blo 654306 737635 := bstep (se 1 (by rfl) ⟨553226, by rfl⟩ : syracuseStep 737635 = 1106453) B1106453
theorem B934259 : Blo 654306 934259 := bstep (se 1 (by rfl) ⟨700694, by rfl⟩ : syracuseStep 934259 = 1401389) B1401389
theorem B1065377 : Blo 654306 1065377 := bstep (se 2 (by rfl) ⟨399516, by rfl⟩ : syracuseStep 1065377 = 799033) B799033
theorem B737779 : Blo 654306 737779 := bstep (se 1 (by rfl) ⟨553334, by rfl⟩ : syracuseStep 737779 = 1106669) B1106669
theorem B2212433 : Blo 654306 2212433 := bstep (se 2 (by rfl) ⟨829662, by rfl⟩ : syracuseStep 2212433 = 1659325) B1659325
theorem B737923 : Blo 654306 737923 := bstep (se 1 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 737923 = 1106885) B1106885
theorem B3326669 : Blo 654306 3326669 := bstep (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) B1247501
theorem B1688323 : Blo 654306 1688323 := bstep (se 1 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 1688323 = 2532485) B2532485
theorem B738067 : Blo 654306 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B1065793 : Blo 654306 1065793 := bstep (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) B799345
theorem B738211 : Blo 654306 738211 := bstep (se 1 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 738211 = 1107317) B1107317
theorem B934897 : Blo 654306 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B3163121 : Blo 654306 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B738355 : Blo 654306 738355 := bstep (se 1 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 738355 = 1107533) B1107533
theorem B935011 : Blo 654306 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B2212973 : Blo 654306 2212973 := bstep (se 3 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 2212973 = 829865) B829865
theorem B2213027 : Blo 654306 2213027 := bstep (se 1 (by rfl) ⟨1659770, by rfl⟩ : syracuseStep 2213027 = 3319541) B3319541
theorem B3163313 : Blo 654306 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B738499 : Blo 654306 738499 := bstep (se 1 (by rfl) ⟨553874, by rfl⟩ : syracuseStep 738499 = 1107749) B1107749
theorem B4113713 : Blo 654306 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B738643 : Blo 654306 738643 := bstep (se 1 (by rfl) ⟨553982, by rfl⟩ : syracuseStep 738643 = 1107965) B1107965
theorem B1656227 : Blo 654306 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B2213297 : Blo 654306 2213297 := bstep (se 2 (by rfl) ⟨829986, by rfl⟩ : syracuseStep 2213297 = 1659973) B1659973
theorem B738787 : Blo 654306 738787 := bstep (se 1 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 738787 = 1108181) B1108181
theorem B1263107 : Blo 654306 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B738931 : Blo 654306 738931 := bstep (se 1 (by rfl) ⟨554198, by rfl⟩ : syracuseStep 738931 = 1108397) B1108397
theorem B739075 : Blo 654306 739075 := bstep (se 1 (by rfl) ⟨554306, by rfl⟩ : syracuseStep 739075 = 1108613) B1108613
theorem B4736837 : Blo 654306 4736837 := bstep (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) B888157
theorem B739219 : Blo 654306 739219 := bstep (se 1 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 739219 = 1108829) B1108829
theorem B7096261 : Blo 654306 7096261 := bstep (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) B1330549
theorem B2213837 : Blo 654306 2213837 := bstep (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) B830189
theorem B2213891 : Blo 654306 2213891 := bstep (se 1 (by rfl) ⟨1660418, by rfl⟩ : syracuseStep 2213891 = 3320837) B3320837
theorem B739363 : Blo 654306 739363 := bstep (se 1 (by rfl) ⟨554522, by rfl⟩ : syracuseStep 739363 = 1109045) B1109045
theorem B739507 : Blo 654306 739507 := bstep (se 1 (by rfl) ⟨554630, by rfl⟩ : syracuseStep 739507 = 1109261) B1109261
theorem B1067201 : Blo 654306 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B5621957 : Blo 654306 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B2214161 : Blo 654306 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B739651 : Blo 654306 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B1657169 : Blo 654306 1657169 := bstep (se 2 (by rfl) ⟨621438, by rfl⟩ : syracuseStep 1657169 = 1242877) B1242877
theorem B1657219 : Blo 654306 1657219 := bstep (se 1 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 1657219 = 2485829) B2485829
theorem B2247053 : Blo 654306 2247053 := bstep (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) B842645
theorem B936355 : Blo 654306 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B739795 : Blo 654306 739795 := bstep (se 1 (by rfl) ⟨554846, by rfl⟩ : syracuseStep 739795 = 1109693) B1109693
theorem B1657361 : Blo 654306 1657361 := bstep (se 2 (by rfl) ⟨621510, by rfl⟩ : syracuseStep 1657361 = 1243021) B1243021
theorem B739939 : Blo 654306 739939 := bstep (se 1 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 739939 = 1109909) B1109909
theorem B740083 : Blo 654306 740083 := bstep (se 1 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 740083 = 1110125) B1110125
theorem B2214701 : Blo 654306 2214701 := bstep (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) B830513
theorem B2018125 : Blo 654306 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B2214755 : Blo 654306 2214755 := bstep (se 1 (by rfl) ⟨1661066, by rfl⟩ : syracuseStep 2214755 = 3322133) B3322133
theorem B8407921 : Blo 654306 8407921 := bstep (se 2 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 8407921 = 6305941) B6305941
theorem B5622641 : Blo 654306 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B740227 : Blo 654306 740227 := bstep (se 1 (by rfl) ⟨555170, by rfl⟩ : syracuseStep 740227 = 1110341) B1110341
theorem B740371 : Blo 654306 740371 := bstep (se 1 (by rfl) ⟨555278, by rfl⟩ : syracuseStep 740371 = 1110557) B1110557
theorem B2804813 : Blo 654306 2804813 := bstep (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) B1051805
theorem B2215025 : Blo 654306 2215025 := bstep (se 2 (by rfl) ⟨830634, by rfl⟩ : syracuseStep 2215025 = 1661269) B1661269
theorem B2247821 : Blo 654306 2247821 := bstep (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) B842933
theorem B740515 : Blo 654306 740515 := bstep (se 1 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 740515 = 1110773) B1110773
theorem B4214213 : Blo 654306 4214213 := bstep (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) B790165
theorem B1658353 : Blo 654306 1658353 := bstep (se 2 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 1658353 = 1243765) B1243765
theorem B3329585 : Blo 654306 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B2215565 : Blo 654306 2215565 := bstep (se 3 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 2215565 = 830837) B830837
theorem B2215619 : Blo 654306 2215619 := bstep (se 1 (by rfl) ⟨1661714, by rfl⟩ : syracuseStep 2215619 = 3323429) B3323429
theorem B1658627 : Blo 654306 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B1658819 : Blo 654306 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B2215889 : Blo 654306 2215889 := bstep (se 2 (by rfl) ⟨830958, by rfl⟩ : syracuseStep 2215889 = 1661917) B1661917
theorem B2216429 : Blo 654306 2216429 := bstep (se 3 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 2216429 = 831161) B831161
theorem B2216483 : Blo 654306 2216483 := bstep (se 1 (by rfl) ⟨1662362, by rfl⟩ : syracuseStep 2216483 = 3324725) B3324725
theorem B2216753 : Blo 654306 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B1332035 : Blo 654306 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B1659761 : Blo 654306 1659761 := bstep (se 2 (by rfl) ⟨622410, by rfl⟩ : syracuseStep 1659761 = 1244821) B1244821
theorem B1659811 : Blo 654306 1659811 := bstep (se 1 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 1659811 = 2489717) B2489717
theorem B3331043 : Blo 654306 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B1659953 : Blo 654306 1659953 := bstep (se 2 (by rfl) ⟨622482, by rfl⟩ : syracuseStep 1659953 = 1244965) B1244965
theorem B7492661 : Blo 654306 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B1397827 : Blo 654306 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B1135859 : Blo 654306 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B3986765 : Blo 654306 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B2217293 : Blo 654306 2217293 := bstep (se 3 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 2217293 = 831485) B831485
theorem B2217347 : Blo 654306 2217347 := bstep (se 1 (by rfl) ⟨1663010, by rfl⟩ : syracuseStep 2217347 = 3326021) B3326021
theorem B5199331 : Blo 654306 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B2217617 : Blo 654306 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B3331853 : Blo 654306 3331853 := bstep (se 3 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 3331853 = 1249445) B1249445
theorem B1660945 : Blo 654306 1660945 := bstep (se 2 (by rfl) ⟨622854, by rfl⟩ : syracuseStep 1660945 = 1245709) B1245709
theorem B4216931 : Blo 654306 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2218157 : Blo 654306 2218157 := bstep (se 3 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 2218157 = 831809) B831809
theorem B2218211 : Blo 654306 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B1661219 : Blo 654306 1661219 := bstep (se 1 (by rfl) ⟨1245914, by rfl⟩ : syracuseStep 1661219 = 2491829) B2491829
theorem B1104259 : Blo 654306 1104259 := bstep (se 1 (by rfl) ⟨828194, by rfl⟩ : syracuseStep 1104259 = 1656389) B1656389
theorem B1661411 : Blo 654306 1661411 := bstep (se 1 (by rfl) ⟨1246058, by rfl⟩ : syracuseStep 1661411 = 2492117) B2492117
theorem B2218481 : Blo 654306 2218481 := bstep (se 2 (by rfl) ⟨831930, by rfl⟩ : syracuseStep 2218481 = 1663861) B1663861
theorem B1104401 : Blo 654306 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B1399331 : Blo 654306 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B1104529 : Blo 654306 1104529 := bstep (se 2 (by rfl) ⟨414198, by rfl⟩ : syracuseStep 1104529 = 828397) B828397
theorem B1104563 : Blo 654306 1104563 := bstep (se 1 (by rfl) ⟨828422, by rfl⟩ : syracuseStep 1104563 = 1656845) B1656845
theorem B842435 : Blo 654306 842435 := bstep (se 1 (by rfl) ⟨631826, by rfl⟩ : syracuseStep 842435 = 1263653) B1263653
theorem B1104691 : Blo 654306 1104691 := bstep (se 1 (by rfl) ⟨828518, by rfl⟩ : syracuseStep 1104691 = 1657037) B1657037
theorem B1104833 : Blo 654306 1104833 := bstep (se 2 (by rfl) ⟨414312, by rfl⟩ : syracuseStep 1104833 = 828625) B828625
theorem B2219021 : Blo 654306 2219021 := bstep (se 3 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 2219021 = 832133) B832133
theorem B1104961 : Blo 654306 1104961 := bstep (se 2 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 1104961 = 828721) B828721
theorem B2219075 : Blo 654306 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B86170709 : Blo 654306 86170709 := bstep (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) B1009813
theorem B1104995 : Blo 654306 1104995 := bstep (se 1 (by rfl) ⟨828746, by rfl⟩ : syracuseStep 1104995 = 1657493) B1657493
theorem B1105123 : Blo 654306 1105123 := bstep (se 1 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 1105123 = 1657685) B1657685
theorem B2219345 : Blo 654306 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B2809187 : Blo 654306 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B1105265 : Blo 654306 1105265 := bstep (se 2 (by rfl) ⟨414474, by rfl⟩ : syracuseStep 1105265 = 828949) B828949
theorem B1662353 : Blo 654306 1662353 := bstep (se 2 (by rfl) ⟨623382, by rfl⟩ : syracuseStep 1662353 = 1246765) B1246765
theorem B1662403 : Blo 654306 1662403 := bstep (se 1 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 1662403 = 2493605) B2493605
theorem B1105393 : Blo 654306 1105393 := bstep (se 2 (by rfl) ⟨414522, by rfl⟩ : syracuseStep 1105393 = 829045) B829045
theorem B1105427 : Blo 654306 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B1662545 : Blo 654306 1662545 := bstep (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) B1246909
theorem B1105555 : Blo 654306 1105555 := bstep (se 1 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 1105555 = 1658333) B1658333
theorem B4480753 : Blo 654306 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B1400561 : Blo 654306 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B1105697 : Blo 654306 1105697 := bstep (se 2 (by rfl) ⟨414636, by rfl⟩ : syracuseStep 1105697 = 829273) B829273
theorem B1498979 : Blo 654306 1498979 := bstep (se 1 (by rfl) ⟨1124234, by rfl⟩ : syracuseStep 1498979 = 2248469) B2248469
theorem B2219885 : Blo 654306 2219885 := bstep (se 3 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 2219885 = 832457) B832457
theorem B1105825 : Blo 654306 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B2219939 : Blo 654306 2219939 := bstep (se 1 (by rfl) ⟨1664954, by rfl⟩ : syracuseStep 2219939 = 3329909) B3329909
theorem B1105859 : Blo 654306 1105859 := bstep (se 1 (by rfl) ⟨829394, by rfl⟩ : syracuseStep 1105859 = 1658789) B1658789
theorem B1105987 : Blo 654306 1105987 := bstep (se 1 (by rfl) ⟨829490, by rfl⟩ : syracuseStep 1105987 = 1658981) B1658981
theorem B8413253 : Blo 654306 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B2220209 : Blo 654306 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B1106129 : Blo 654306 1106129 := bstep (se 2 (by rfl) ⟨414798, by rfl⟩ : syracuseStep 1106129 = 829597) B829597
theorem B1106257 : Blo 654306 1106257 := bstep (se 2 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 1106257 = 829693) B829693
theorem B1106291 : Blo 654306 1106291 := bstep (se 1 (by rfl) ⟨829718, by rfl⟩ : syracuseStep 1106291 = 1659437) B1659437
theorem B1991153 : Blo 654306 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B1106419 : Blo 654306 1106419 := bstep (se 1 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 1106419 = 1659629) B1659629
theorem B1663537 : Blo 654306 1663537 := bstep (se 2 (by rfl) ⟨623826, by rfl⟩ : syracuseStep 1663537 = 1247653) B1247653
theorem B1401457 : Blo 654306 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B1106561 : Blo 654306 1106561 := bstep (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) B829921
theorem B1401475 : Blo 654306 1401475 := bstep (se 1 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 1401475 = 2102213) B2102213
theorem B2220749 : Blo 654306 2220749 := bstep (se 3 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 2220749 = 832781) B832781
theorem B1106689 : Blo 654306 1106689 := bstep (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) B830017
theorem B2220803 : Blo 654306 2220803 := bstep (se 1 (by rfl) ⟨1665602, by rfl⟩ : syracuseStep 2220803 = 3331205) B3331205
theorem B1106723 : Blo 654306 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B1663811 : Blo 654306 1663811 := bstep (se 1 (by rfl) ⟨1247858, by rfl⟩ : syracuseStep 1663811 = 2495717) B2495717
theorem B3367793 : Blo 654306 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B1106851 : Blo 654306 1106851 := bstep (se 1 (by rfl) ⟨830138, by rfl⟩ : syracuseStep 1106851 = 1660277) B1660277
theorem B16835525 : Blo 654306 16835525 := bstep (se 4 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 16835525 = 3156661) B3156661
theorem B1664003 : Blo 654306 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B2221073 : Blo 654306 2221073 := bstep (se 2 (by rfl) ⟨832902, by rfl⟩ : syracuseStep 2221073 = 1665805) B1665805
theorem B1106993 : Blo 654306 1106993 := bstep (se 2 (by rfl) ⟨415122, by rfl⟩ : syracuseStep 1106993 = 830245) B830245
theorem B1107121 : Blo 654306 1107121 := bstep (se 2 (by rfl) ⟨415170, by rfl⟩ : syracuseStep 1107121 = 830341) B830341
theorem B10085573 : Blo 654306 10085573 := bstep (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) B1891045
theorem B1107155 : Blo 654306 1107155 := bstep (se 1 (by rfl) ⟨830366, by rfl⟩ : syracuseStep 1107155 = 1660733) B1660733
theorem B1008865 : Blo 654306 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B2811185 : Blo 654306 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B1107283 : Blo 654306 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B1107425 : Blo 654306 1107425 := bstep (se 2 (by rfl) ⟨415284, by rfl⟩ : syracuseStep 1107425 = 830569) B830569
theorem B2221613 : Blo 654306 2221613 := bstep (se 3 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 2221613 = 833105) B833105
theorem B1107553 : Blo 654306 1107553 := bstep (se 2 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 1107553 = 830665) B830665
theorem B2221667 : Blo 654306 2221667 := bstep (se 1 (by rfl) ⟨1666250, by rfl⟩ : syracuseStep 2221667 = 3332501) B3332501
theorem B1107587 : Blo 654306 1107587 := bstep (se 1 (by rfl) ⟨830690, by rfl⟩ : syracuseStep 1107587 = 1661381) B1661381
theorem B1599203 : Blo 654306 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B1107715 : Blo 654306 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B1795949 : Blo 654306 1795949 := bstep (se 3 (by rfl) ⟨336740, by rfl⟩ : syracuseStep 1795949 = 673481) B673481
theorem B1107857 : Blo 654306 1107857 := bstep (se 2 (by rfl) ⟨415446, by rfl⟩ : syracuseStep 1107857 = 830893) B830893
theorem B1664945 : Blo 654306 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B2779085 : Blo 654306 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B1140689 : Blo 654306 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1664995 : Blo 654306 1664995 := bstep (se 1 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 1664995 = 2497493) B2497493
theorem B1107985 : Blo 654306 1107985 := bstep (se 2 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 1107985 = 830989) B830989
theorem B1108019 : Blo 654306 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B7596101 : Blo 654306 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1665137 : Blo 654306 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B1108147 : Blo 654306 1108147 := bstep (se 1 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 1108147 = 1662221) B1662221
theorem B1108289 : Blo 654306 1108289 := bstep (se 2 (by rfl) ⟨415608, by rfl⟩ : syracuseStep 1108289 = 831217) B831217
theorem B944467 : Blo 654306 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B1108417 : Blo 654306 1108417 := bstep (se 2 (by rfl) ⟨415656, by rfl⟩ : syracuseStep 1108417 = 831313) B831313
theorem B1993187 : Blo 654306 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1108451 : Blo 654306 1108451 := bstep (se 1 (by rfl) ⟨831338, by rfl⟩ : syracuseStep 1108451 = 1662677) B1662677
theorem B1010161 : Blo 654306 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B1108579 : Blo 654306 1108579 := bstep (se 1 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 1108579 = 1662869) B1662869
theorem B1108721 : Blo 654306 1108721 := bstep (se 2 (by rfl) ⟨415770, by rfl⟩ : syracuseStep 1108721 = 831541) B831541
theorem B7269173 : Blo 654306 7269173 := bstep (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) B681485
theorem B1403747 : Blo 654306 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B1108849 : Blo 654306 1108849 := bstep (se 2 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 1108849 = 831637) B831637
theorem B1108883 : Blo 654306 1108883 := bstep (se 1 (by rfl) ⟨831662, by rfl⟩ : syracuseStep 1108883 = 1663325) B1663325
theorem B1109011 : Blo 654306 1109011 := bstep (se 1 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 1109011 = 1663517) B1663517
theorem B1666129 : Blo 654306 1666129 := bstep (se 2 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 1666129 = 1249597) B1249597
theorem B1109153 : Blo 654306 1109153 := bstep (se 2 (by rfl) ⟨415932, by rfl⟩ : syracuseStep 1109153 = 831865) B831865
theorem B1109281 : Blo 654306 1109281 := bstep (se 2 (by rfl) ⟨415980, by rfl⟩ : syracuseStep 1109281 = 831961) B831961
theorem B1404209 : Blo 654306 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B1109315 : Blo 654306 1109315 := bstep (se 1 (by rfl) ⟨831986, by rfl⟩ : syracuseStep 1109315 = 1663973) B1663973
theorem B1109443 : Blo 654306 1109443 := bstep (se 1 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 1109443 = 1664165) B1664165
theorem B1109585 : Blo 654306 1109585 := bstep (se 2 (by rfl) ⟨416094, by rfl⟩ : syracuseStep 1109585 = 832189) B832189
theorem B1109713 : Blo 654306 1109713 := bstep (se 2 (by rfl) ⟨416142, by rfl⟩ : syracuseStep 1109713 = 832285) B832285
theorem B1109747 : Blo 654306 1109747 := bstep (se 1 (by rfl) ⟨832310, by rfl⟩ : syracuseStep 1109747 = 1664621) B1664621
theorem B946003 : Blo 654306 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B1109875 : Blo 654306 1109875 := bstep (se 1 (by rfl) ⟨832406, by rfl⟩ : syracuseStep 1109875 = 1664813) B1664813
theorem B1863587 : Blo 654306 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B1110017 : Blo 654306 1110017 := bstep (se 2 (by rfl) ⟨416256, by rfl⟩ : syracuseStep 1110017 = 832513) B832513
theorem B2486285 : Blo 654306 2486285 := bstep (se 3 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 2486285 = 932357) B932357
theorem B19132469 : Blo 654306 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B1110145 : Blo 654306 1110145 := bstep (se 2 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 1110145 = 832609) B832609
theorem B1110179 : Blo 654306 1110179 := bstep (se 1 (by rfl) ⟨832634, by rfl⟩ : syracuseStep 1110179 = 1665269) B1665269
theorem B1863917 : Blo 654306 1863917 := bstep (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) B698969
theorem B1110307 : Blo 654306 1110307 := bstep (se 1 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 1110307 = 1665461) B1665461
theorem B1863985 : Blo 654306 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B1110449 : Blo 654306 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B1110577 : Blo 654306 1110577 := bstep (se 2 (by rfl) ⟨416466, by rfl⟩ : syracuseStep 1110577 = 832933) B832933
theorem B1864259 : Blo 654306 1864259 := bstep (se 1 (by rfl) ⟨1398194, by rfl⟩ : syracuseStep 1864259 = 2796389) B2796389
theorem B1405507 : Blo 654306 1405507 := bstep (se 1 (by rfl) ⟨1054130, by rfl⟩ : syracuseStep 1405507 = 2108261) B2108261
theorem B5599813 : Blo 654306 5599813 := bstep (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) B1049965
theorem B1110611 : Blo 654306 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B1110739 : Blo 654306 1110739 := bstep (se 1 (by rfl) ⟨833054, by rfl⟩ : syracuseStep 1110739 = 1666109) B1666109
theorem B3994373 : Blo 654306 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B1405763 : Blo 654306 1405763 := bstep (se 1 (by rfl) ⟨1054322, by rfl⟩ : syracuseStep 1405763 = 2108645) B2108645
theorem B1110881 : Blo 654306 1110881 := bstep (se 2 (by rfl) ⟨416580, by rfl⟩ : syracuseStep 1110881 = 833161) B833161
theorem B7467875 : Blo 654306 7467875 := bstep (se 1 (by rfl) ⟨5600906, by rfl⟩ : syracuseStep 7467875 = 11201813) B11201813
theorem B7206029 : Blo 654306 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1242307 : Blo 654306 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B10220741 : Blo 654306 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B1242353 : Blo 654306 1242353 := bstep (se 2 (by rfl) ⟨465882, by rfl⟩ : syracuseStep 1242353 = 931765) B931765
theorem B3994865 : Blo 654306 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B1865101 : Blo 654306 1865101 := bstep (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) B699413
theorem B11236805 : Blo 654306 11236805 := bstep (se 4 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 11236805 = 2106901) B2106901
theorem B1996301 : Blo 654306 1996301 := bstep (se 3 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 1996301 = 748613) B748613
theorem B1242641 : Blo 654306 1242641 := bstep (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) B931981
theorem B1865261 : Blo 654306 1865261 := bstep (se 3 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 1865261 = 699473) B699473
theorem B1865443 : Blo 654306 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B1472273 : Blo 654306 1472273 := bstep (se 2 (by rfl) ⟨552102, by rfl⟩ : syracuseStep 1472273 = 1104205) B1104205
theorem B1472291 : Blo 654306 1472291 := bstep (se 1 (by rfl) ⟨1104218, by rfl⟩ : syracuseStep 1472291 = 2208437) B2208437
theorem B1472561 : Blo 654306 1472561 := bstep (se 2 (by rfl) ⟨552210, by rfl⟩ : syracuseStep 1472561 = 1104421) B1104421
theorem B20183093 : Blo 654306 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B1472579 : Blo 654306 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B3733573 : Blo 654306 3733573 := bstep (se 4 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 3733573 = 700045) B700045
theorem B7108721 : Blo 654306 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B1243363 : Blo 654306 1243363 := bstep (se 1 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 1243363 = 1865045) B1865045
theorem B1472849 : Blo 654306 1472849 := bstep (se 2 (by rfl) ⟨552318, by rfl⟩ : syracuseStep 1472849 = 1104637) B1104637
theorem B1472867 : Blo 654306 1472867 := bstep (se 1 (by rfl) ⟨1104650, by rfl⟩ : syracuseStep 1472867 = 2209301) B2209301
theorem B2128259 : Blo 654306 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B981473 : Blo 654306 981473 := bstep (se 2 (by rfl) ⟨368052, by rfl⟩ : syracuseStep 981473 = 736105) B736105
theorem B981491 : Blo 654306 981491 := bstep (se 1 (by rfl) ⟨736118, by rfl⟩ : syracuseStep 981491 = 1472237) B1472237
theorem B981521 : Blo 654306 981521 := bstep (se 2 (by rfl) ⟨368070, by rfl⟩ : syracuseStep 981521 = 736141) B736141
theorem B981539 : Blo 654306 981539 := bstep (se 1 (by rfl) ⟨736154, by rfl⟩ : syracuseStep 981539 = 1472309) B1472309
theorem B981569 : Blo 654306 981569 := bstep (se 2 (by rfl) ⟨368088, by rfl⟩ : syracuseStep 981569 = 736177) B736177
theorem B981587 : Blo 654306 981587 := bstep (se 1 (by rfl) ⟨736190, by rfl⟩ : syracuseStep 981587 = 1472381) B1472381
theorem B981617 : Blo 654306 981617 := bstep (se 2 (by rfl) ⟨368106, by rfl⟩ : syracuseStep 981617 = 736213) B736213
theorem B1473137 : Blo 654306 1473137 := bstep (se 2 (by rfl) ⟨552426, by rfl⟩ : syracuseStep 1473137 = 1104853) B1104853
theorem B981635 : Blo 654306 981635 := bstep (se 1 (by rfl) ⟨736226, by rfl⟩ : syracuseStep 981635 = 1472453) B1472453
theorem B1473155 : Blo 654306 1473155 := bstep (se 1 (by rfl) ⟨1104866, by rfl⟩ : syracuseStep 1473155 = 2209733) B2209733
theorem B1800835 : Blo 654306 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B981665 : Blo 654306 981665 := bstep (se 2 (by rfl) ⟨368124, by rfl⟩ : syracuseStep 981665 = 736249) B736249
theorem B1243811 : Blo 654306 1243811 := bstep (se 1 (by rfl) ⟨932858, by rfl⟩ : syracuseStep 1243811 = 1865717) B1865717
theorem B981683 : Blo 654306 981683 := bstep (se 1 (by rfl) ⟨736262, by rfl⟩ : syracuseStep 981683 = 1472525) B1472525
theorem B981713 : Blo 654306 981713 := bstep (se 2 (by rfl) ⟨368142, by rfl⟩ : syracuseStep 981713 = 736285) B736285
theorem B981731 : Blo 654306 981731 := bstep (se 1 (by rfl) ⟨736298, by rfl⟩ : syracuseStep 981731 = 1472597) B1472597
theorem B981761 : Blo 654306 981761 := bstep (se 2 (by rfl) ⟨368160, by rfl⟩ : syracuseStep 981761 = 736321) B736321
theorem B981779 : Blo 654306 981779 := bstep (se 1 (by rfl) ⟨736334, by rfl⟩ : syracuseStep 981779 = 1472669) B1472669
theorem B981809 : Blo 654306 981809 := bstep (se 2 (by rfl) ⟨368178, by rfl⟩ : syracuseStep 981809 = 736357) B736357
theorem B981827 : Blo 654306 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B981857 : Blo 654306 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B4979555 : Blo 654306 4979555 := bstep (se 1 (by rfl) ⟨3734666, by rfl⟩ : syracuseStep 4979555 = 7469333) B7469333
theorem B2489201 : Blo 654306 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B981875 : Blo 654306 981875 := bstep (se 1 (by rfl) ⟨736406, by rfl⟩ : syracuseStep 981875 = 1472813) B1472813
theorem B981905 : Blo 654306 981905 := bstep (se 2 (by rfl) ⟨368214, by rfl⟩ : syracuseStep 981905 = 736429) B736429
theorem B1473425 : Blo 654306 1473425 := bstep (se 2 (by rfl) ⟨552534, by rfl⟩ : syracuseStep 1473425 = 1105069) B1105069
theorem B981923 : Blo 654306 981923 := bstep (se 1 (by rfl) ⟨736442, by rfl⟩ : syracuseStep 981923 = 1472885) B1472885
theorem B1473443 : Blo 654306 1473443 := bstep (se 1 (by rfl) ⟨1105082, by rfl⟩ : syracuseStep 1473443 = 2210165) B2210165
theorem B981953 : Blo 654306 981953 := bstep (se 2 (by rfl) ⟨368232, by rfl⟩ : syracuseStep 981953 = 736465) B736465
theorem B1244099 : Blo 654306 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B981971 : Blo 654306 981971 := bstep (se 1 (by rfl) ⟨736478, by rfl⟩ : syracuseStep 981971 = 1472957) B1472957
theorem B654307 : Blo 654306 654307 := bstep (se 1 (by rfl) ⟨490730, by rfl⟩ : syracuseStep 654307 = 981461) B981461
theorem B982001 : Blo 654306 982001 := bstep (se 2 (by rfl) ⟨368250, by rfl⟩ : syracuseStep 982001 = 736501) B736501
theorem B654323 : Blo 654306 654323 := bstep (se 1 (by rfl) ⟨490742, by rfl⟩ : syracuseStep 654323 = 981485) B981485
theorem B654339 : Blo 654306 654339 := bstep (se 1 (by rfl) ⟨490754, by rfl⟩ : syracuseStep 654339 = 981509) B981509
theorem B982019 : Blo 654306 982019 := bstep (se 1 (by rfl) ⟨736514, by rfl⟩ : syracuseStep 982019 = 1473029) B1473029
theorem B654355 : Blo 654306 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B982049 : Blo 654306 982049 := bstep (se 2 (by rfl) ⟨368268, by rfl⟩ : syracuseStep 982049 = 736537) B736537
theorem B654371 : Blo 654306 654371 := bstep (se 1 (by rfl) ⟨490778, by rfl⟩ : syracuseStep 654371 = 981557) B981557
theorem B654387 : Blo 654306 654387 := bstep (se 1 (by rfl) ⟨490790, by rfl⟩ : syracuseStep 654387 = 981581) B981581
theorem B982067 : Blo 654306 982067 := bstep (se 1 (by rfl) ⟨736550, by rfl⟩ : syracuseStep 982067 = 1473101) B1473101
theorem B654403 : Blo 654306 654403 := bstep (se 1 (by rfl) ⟨490802, by rfl⟩ : syracuseStep 654403 = 981605) B981605
theorem B2849869 : Blo 654306 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B982097 : Blo 654306 982097 := bstep (se 2 (by rfl) ⟨368286, by rfl⟩ : syracuseStep 982097 = 736573) B736573
theorem B1866833 : Blo 654306 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B654419 : Blo 654306 654419 := bstep (se 1 (by rfl) ⟨490814, by rfl⟩ : syracuseStep 654419 = 981629) B981629
theorem B654435 : Blo 654306 654435 := bstep (se 1 (by rfl) ⟨490826, by rfl⟩ : syracuseStep 654435 = 981653) B981653
theorem B982115 : Blo 654306 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B654451 : Blo 654306 654451 := bstep (se 1 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 654451 = 981677) B981677
theorem B982145 : Blo 654306 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B654467 : Blo 654306 654467 := bstep (se 1 (by rfl) ⟨490850, by rfl⟩ : syracuseStep 654467 = 981701) B981701
theorem B654483 : Blo 654306 654483 := bstep (se 1 (by rfl) ⟨490862, by rfl⟩ : syracuseStep 654483 = 981725) B981725
theorem B982163 : Blo 654306 982163 := bstep (se 1 (by rfl) ⟨736622, by rfl⟩ : syracuseStep 982163 = 1473245) B1473245
theorem B654499 : Blo 654306 654499 := bstep (se 1 (by rfl) ⟨490874, by rfl⟩ : syracuseStep 654499 = 981749) B981749
theorem B3538097 : Blo 654306 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B982193 : Blo 654306 982193 := bstep (se 2 (by rfl) ⟨368322, by rfl⟩ : syracuseStep 982193 = 736645) B736645
theorem B654515 : Blo 654306 654515 := bstep (se 1 (by rfl) ⟨490886, by rfl⟩ : syracuseStep 654515 = 981773) B981773
theorem B1473713 : Blo 654306 1473713 := bstep (se 2 (by rfl) ⟨552642, by rfl⟩ : syracuseStep 1473713 = 1105285) B1105285
theorem B1473731 : Blo 654306 1473731 := bstep (se 1 (by rfl) ⟨1105298, by rfl⟩ : syracuseStep 1473731 = 2210597) B2210597
theorem B654531 : Blo 654306 654531 := bstep (se 1 (by rfl) ⟨490898, by rfl⟩ : syracuseStep 654531 = 981797) B981797
theorem B982211 : Blo 654306 982211 := bstep (se 1 (by rfl) ⟨736658, by rfl⟩ : syracuseStep 982211 = 1473317) B1473317
theorem B654547 : Blo 654306 654547 := bstep (se 1 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 654547 = 981821) B981821
theorem B982241 : Blo 654306 982241 := bstep (se 2 (by rfl) ⟨368340, by rfl⟩ : syracuseStep 982241 = 736681) B736681
theorem B654563 : Blo 654306 654563 := bstep (se 1 (by rfl) ⟨490922, by rfl⟩ : syracuseStep 654563 = 981845) B981845
theorem B654579 : Blo 654306 654579 := bstep (se 1 (by rfl) ⟨490934, by rfl⟩ : syracuseStep 654579 = 981869) B981869
theorem B982259 : Blo 654306 982259 := bstep (se 1 (by rfl) ⟨736694, by rfl⟩ : syracuseStep 982259 = 1473389) B1473389
theorem B654595 : Blo 654306 654595 := bstep (se 1 (by rfl) ⟨490946, by rfl⟩ : syracuseStep 654595 = 981893) B981893
theorem B982289 : Blo 654306 982289 := bstep (se 2 (by rfl) ⟨368358, by rfl⟩ : syracuseStep 982289 = 736717) B736717
theorem B654611 : Blo 654306 654611 := bstep (se 1 (by rfl) ⟨490958, by rfl⟩ : syracuseStep 654611 = 981917) B981917
theorem B654627 : Blo 654306 654627 := bstep (se 1 (by rfl) ⟨490970, by rfl⟩ : syracuseStep 654627 = 981941) B981941
theorem B982307 : Blo 654306 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B654643 : Blo 654306 654643 := bstep (se 1 (by rfl) ⟨490982, by rfl⟩ : syracuseStep 654643 = 981965) B981965
theorem B982337 : Blo 654306 982337 := bstep (se 2 (by rfl) ⟨368376, by rfl⟩ : syracuseStep 982337 = 736753) B736753
theorem B654659 : Blo 654306 654659 := bstep (se 1 (by rfl) ⟨490994, by rfl⟩ : syracuseStep 654659 = 981989) B981989
theorem B654675 : Blo 654306 654675 := bstep (se 1 (by rfl) ⟨491006, by rfl⟩ : syracuseStep 654675 = 982013) B982013
theorem B982355 : Blo 654306 982355 := bstep (se 1 (by rfl) ⟨736766, by rfl⟩ : syracuseStep 982355 = 1473533) B1473533
theorem B654691 : Blo 654306 654691 := bstep (se 1 (by rfl) ⟨491018, by rfl⟩ : syracuseStep 654691 = 982037) B982037
theorem B982385 : Blo 654306 982385 := bstep (se 2 (by rfl) ⟨368394, by rfl⟩ : syracuseStep 982385 = 736789) B736789
theorem B654707 : Blo 654306 654707 := bstep (se 1 (by rfl) ⟨491030, by rfl⟩ : syracuseStep 654707 = 982061) B982061
theorem B654723 : Blo 654306 654723 := bstep (se 1 (by rfl) ⟨491042, by rfl⟩ : syracuseStep 654723 = 982085) B982085
theorem B982403 : Blo 654306 982403 := bstep (se 1 (by rfl) ⟨736802, by rfl⟩ : syracuseStep 982403 = 1473605) B1473605
theorem B654739 : Blo 654306 654739 := bstep (se 1 (by rfl) ⟨491054, by rfl⟩ : syracuseStep 654739 = 982109) B982109
theorem B982433 : Blo 654306 982433 := bstep (se 2 (by rfl) ⟨368412, by rfl⟩ : syracuseStep 982433 = 736825) B736825
theorem B654755 : Blo 654306 654755 := bstep (se 1 (by rfl) ⟨491066, by rfl⟩ : syracuseStep 654755 = 982133) B982133
theorem B654771 : Blo 654306 654771 := bstep (se 1 (by rfl) ⟨491078, by rfl⟩ : syracuseStep 654771 = 982157) B982157
theorem B982451 : Blo 654306 982451 := bstep (se 1 (by rfl) ⟨736838, by rfl⟩ : syracuseStep 982451 = 1473677) B1473677
theorem B654787 : Blo 654306 654787 := bstep (se 1 (by rfl) ⟨491090, by rfl⟩ : syracuseStep 654787 = 982181) B982181
theorem B982481 : Blo 654306 982481 := bstep (se 2 (by rfl) ⟨368430, by rfl⟩ : syracuseStep 982481 = 736861) B736861
theorem B654803 : Blo 654306 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B1474001 : Blo 654306 1474001 := bstep (se 2 (by rfl) ⟨552750, by rfl⟩ : syracuseStep 1474001 = 1105501) B1105501
theorem B1179107 : Blo 654306 1179107 := bstep (se 1 (by rfl) ⟨884330, by rfl⟩ : syracuseStep 1179107 = 1768661) B1768661
theorem B7962083 : Blo 654306 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B654819 : Blo 654306 654819 := bstep (se 1 (by rfl) ⟨491114, by rfl⟩ : syracuseStep 654819 = 982229) B982229
theorem B982499 : Blo 654306 982499 := bstep (se 1 (by rfl) ⟨736874, by rfl⟩ : syracuseStep 982499 = 1473749) B1473749
theorem B1474019 : Blo 654306 1474019 := bstep (se 1 (by rfl) ⟨1105514, by rfl⟩ : syracuseStep 1474019 = 2211029) B2211029
theorem B654835 : Blo 654306 654835 := bstep (se 1 (by rfl) ⟨491126, by rfl⟩ : syracuseStep 654835 = 982253) B982253
theorem B982529 : Blo 654306 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B654851 : Blo 654306 654851 := bstep (se 1 (by rfl) ⟨491138, by rfl⟩ : syracuseStep 654851 = 982277) B982277
theorem B654867 : Blo 654306 654867 := bstep (se 1 (by rfl) ⟨491150, by rfl⟩ : syracuseStep 654867 = 982301) B982301
theorem B982547 : Blo 654306 982547 := bstep (se 1 (by rfl) ⟨736910, by rfl⟩ : syracuseStep 982547 = 1473821) B1473821
theorem B654883 : Blo 654306 654883 := bstep (se 1 (by rfl) ⟨491162, by rfl⟩ : syracuseStep 654883 = 982325) B982325
theorem B982577 : Blo 654306 982577 := bstep (se 2 (by rfl) ⟨368466, by rfl⟩ : syracuseStep 982577 = 736933) B736933
theorem B1048115 : Blo 654306 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B654899 : Blo 654306 654899 := bstep (se 1 (by rfl) ⟨491174, by rfl⟩ : syracuseStep 654899 = 982349) B982349
theorem B654915 : Blo 654306 654915 := bstep (se 1 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 654915 = 982373) B982373
theorem B982595 : Blo 654306 982595 := bstep (se 1 (by rfl) ⟨736946, by rfl⟩ : syracuseStep 982595 = 1473893) B1473893
theorem B654931 : Blo 654306 654931 := bstep (se 1 (by rfl) ⟨491198, by rfl⟩ : syracuseStep 654931 = 982397) B982397
theorem B982625 : Blo 654306 982625 := bstep (se 2 (by rfl) ⟨368484, by rfl⟩ : syracuseStep 982625 = 736969) B736969
theorem B654947 : Blo 654306 654947 := bstep (se 1 (by rfl) ⟨491210, by rfl⟩ : syracuseStep 654947 = 982421) B982421
theorem B654963 : Blo 654306 654963 := bstep (se 1 (by rfl) ⟨491222, by rfl⟩ : syracuseStep 654963 = 982445) B982445
theorem B982643 : Blo 654306 982643 := bstep (se 1 (by rfl) ⟨736982, by rfl⟩ : syracuseStep 982643 = 1473965) B1473965
theorem B654979 : Blo 654306 654979 := bstep (se 1 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 654979 = 982469) B982469
theorem B982673 : Blo 654306 982673 := bstep (se 2 (by rfl) ⟨368502, by rfl⟩ : syracuseStep 982673 = 737005) B737005
theorem B654995 : Blo 654306 654995 := bstep (se 1 (by rfl) ⟨491246, by rfl⟩ : syracuseStep 654995 = 982493) B982493
theorem B655011 : Blo 654306 655011 := bstep (se 1 (by rfl) ⟨491258, by rfl⟩ : syracuseStep 655011 = 982517) B982517
theorem B982691 : Blo 654306 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B655027 : Blo 654306 655027 := bstep (se 1 (by rfl) ⟨491270, by rfl⟩ : syracuseStep 655027 = 982541) B982541
theorem B982721 : Blo 654306 982721 := bstep (se 2 (by rfl) ⟨368520, by rfl⟩ : syracuseStep 982721 = 737041) B737041
theorem B655043 : Blo 654306 655043 := bstep (se 1 (by rfl) ⟨491282, by rfl⟩ : syracuseStep 655043 = 982565) B982565
theorem B655059 : Blo 654306 655059 := bstep (se 1 (by rfl) ⟨491294, by rfl⟩ : syracuseStep 655059 = 982589) B982589
theorem B982739 : Blo 654306 982739 := bstep (se 1 (by rfl) ⟨737054, by rfl⟩ : syracuseStep 982739 = 1474109) B1474109
theorem B655075 : Blo 654306 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B982769 : Blo 654306 982769 := bstep (se 2 (by rfl) ⟨368538, by rfl⟩ : syracuseStep 982769 = 737077) B737077
theorem B1474289 : Blo 654306 1474289 := bstep (se 2 (by rfl) ⟨552858, by rfl⟩ : syracuseStep 1474289 = 1105717) B1105717
theorem B655091 : Blo 654306 655091 := bstep (se 1 (by rfl) ⟨491318, by rfl⟩ : syracuseStep 655091 = 982637) B982637
theorem B655107 : Blo 654306 655107 := bstep (se 1 (by rfl) ⟨491330, by rfl⟩ : syracuseStep 655107 = 982661) B982661
theorem B982787 : Blo 654306 982787 := bstep (se 1 (by rfl) ⟨737090, by rfl⟩ : syracuseStep 982787 = 1474181) B1474181
theorem B1474307 : Blo 654306 1474307 := bstep (se 1 (by rfl) ⟨1105730, by rfl⟩ : syracuseStep 1474307 = 2211461) B2211461
theorem B655123 : Blo 654306 655123 := bstep (se 1 (by rfl) ⟨491342, by rfl⟩ : syracuseStep 655123 = 982685) B982685
theorem B982817 : Blo 654306 982817 := bstep (se 2 (by rfl) ⟨368556, by rfl⟩ : syracuseStep 982817 = 737113) B737113
theorem B655139 : Blo 654306 655139 := bstep (se 1 (by rfl) ⟨491354, by rfl⟩ : syracuseStep 655139 = 982709) B982709
theorem B655155 : Blo 654306 655155 := bstep (se 1 (by rfl) ⟨491366, by rfl⟩ : syracuseStep 655155 = 982733) B982733
theorem B982835 : Blo 654306 982835 := bstep (se 1 (by rfl) ⟨737126, by rfl⟩ : syracuseStep 982835 = 1474253) B1474253
theorem B655171 : Blo 654306 655171 := bstep (se 1 (by rfl) ⟨491378, by rfl⟩ : syracuseStep 655171 = 982757) B982757
theorem B982865 : Blo 654306 982865 := bstep (se 2 (by rfl) ⟨368574, by rfl⟩ : syracuseStep 982865 = 737149) B737149
theorem B655187 : Blo 654306 655187 := bstep (se 1 (by rfl) ⟨491390, by rfl⟩ : syracuseStep 655187 = 982781) B982781
theorem B884579 : Blo 654306 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B655203 : Blo 654306 655203 := bstep (se 1 (by rfl) ⟨491402, by rfl⟩ : syracuseStep 655203 = 982805) B982805
theorem B982883 : Blo 654306 982883 := bstep (se 1 (by rfl) ⟨737162, by rfl⟩ : syracuseStep 982883 = 1474325) B1474325
theorem B1245041 : Blo 654306 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B655219 : Blo 654306 655219 := bstep (se 1 (by rfl) ⟨491414, by rfl⟩ : syracuseStep 655219 = 982829) B982829
theorem B982913 : Blo 654306 982913 := bstep (se 2 (by rfl) ⟨368592, by rfl⟩ : syracuseStep 982913 = 737185) B737185
theorem B884611 : Blo 654306 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B655235 : Blo 654306 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B2359181 : Blo 654306 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B655251 : Blo 654306 655251 := bstep (se 1 (by rfl) ⟨491438, by rfl⟩ : syracuseStep 655251 = 982877) B982877
theorem B982931 : Blo 654306 982931 := bstep (se 1 (by rfl) ⟨737198, by rfl⟩ : syracuseStep 982931 = 1474397) B1474397
theorem B655267 : Blo 654306 655267 := bstep (se 1 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 655267 = 982901) B982901
theorem B982961 : Blo 654306 982961 := bstep (se 2 (by rfl) ⟨368610, by rfl⟩ : syracuseStep 982961 = 737221) B737221
theorem B655283 : Blo 654306 655283 := bstep (se 1 (by rfl) ⟨491462, by rfl⟩ : syracuseStep 655283 = 982925) B982925
theorem B655299 : Blo 654306 655299 := bstep (se 1 (by rfl) ⟨491474, by rfl⟩ : syracuseStep 655299 = 982949) B982949
theorem B982979 : Blo 654306 982979 := bstep (se 1 (by rfl) ⟨737234, by rfl⟩ : syracuseStep 982979 = 1474469) B1474469
theorem B655315 : Blo 654306 655315 := bstep (se 1 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 655315 = 982973) B982973
theorem B983009 : Blo 654306 983009 := bstep (se 2 (by rfl) ⟨368628, by rfl⟩ : syracuseStep 983009 = 737257) B737257
theorem B655331 : Blo 654306 655331 := bstep (se 1 (by rfl) ⟨491498, by rfl⟩ : syracuseStep 655331 = 982997) B982997
theorem B655347 : Blo 654306 655347 := bstep (se 1 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 655347 = 983021) B983021
theorem B983027 : Blo 654306 983027 := bstep (se 1 (by rfl) ⟨737270, by rfl⟩ : syracuseStep 983027 = 1474541) B1474541
theorem B2490371 : Blo 654306 2490371 := bstep (se 1 (by rfl) ⟨1867778, by rfl⟩ : syracuseStep 2490371 = 3735557) B3735557
theorem B983051 : Blo 654306 983051 := bstep (se 1 (by rfl) ⟨737288, by rfl⟩ : syracuseStep 983051 = 1474577) B1474577
theorem B655371 : Blo 654306 655371 := bstep (se 1 (by rfl) ⟨491528, by rfl⟩ : syracuseStep 655371 = 983057) B983057
theorem B2490385 : Blo 654306 2490385 := bstep (se 2 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 2490385 = 1867789) B1867789
theorem B983063 : Blo 654306 983063 := bstep (se 1 (by rfl) ⟨737297, by rfl⟩ : syracuseStep 983063 = 1474595) B1474595
theorem B655383 : Blo 654306 655383 := bstep (se 1 (by rfl) ⟨491537, by rfl⟩ : syracuseStep 655383 = 983075) B983075
theorem B655403 : Blo 654306 655403 := bstep (se 1 (by rfl) ⟨491552, by rfl⟩ : syracuseStep 655403 = 983105) B983105
theorem B655415 : Blo 654306 655415 := bstep (se 1 (by rfl) ⟨491561, by rfl⟩ : syracuseStep 655415 = 983123) B983123
theorem B655435 : Blo 654306 655435 := bstep (se 1 (by rfl) ⟨491576, by rfl⟩ : syracuseStep 655435 = 983153) B983153
theorem B655447 : Blo 654306 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B1474649 : Blo 654306 1474649 := bstep (se 2 (by rfl) ⟨552993, by rfl⟩ : syracuseStep 1474649 = 1105987) B1105987
theorem B983129 : Blo 654306 983129 := bstep (se 2 (by rfl) ⟨368673, by rfl⟩ : syracuseStep 983129 = 737347) B737347
theorem B655467 : Blo 654306 655467 := bstep (se 1 (by rfl) ⟨491600, by rfl⟩ : syracuseStep 655467 = 983201) B983201
theorem B655479 : Blo 654306 655479 := bstep (se 1 (by rfl) ⟨491609, by rfl⟩ : syracuseStep 655479 = 983219) B983219
theorem B655499 : Blo 654306 655499 := bstep (se 1 (by rfl) ⟨491624, by rfl⟩ : syracuseStep 655499 = 983249) B983249
theorem B655511 : Blo 654306 655511 := bstep (se 1 (by rfl) ⟨491633, by rfl⟩ : syracuseStep 655511 = 983267) B983267
theorem B655531 : Blo 654306 655531 := bstep (se 1 (by rfl) ⟨491648, by rfl⟩ : syracuseStep 655531 = 983297) B983297
theorem B1474739 : Blo 654306 1474739 := bstep (se 1 (by rfl) ⟨1106054, by rfl⟩ : syracuseStep 1474739 = 2212109) B2212109
theorem B655543 : Blo 654306 655543 := bstep (se 1 (by rfl) ⟨491657, by rfl⟩ : syracuseStep 655543 = 983315) B983315
theorem B983243 : Blo 654306 983243 := bstep (se 1 (by rfl) ⟨737432, by rfl⟩ : syracuseStep 983243 = 1474865) B1474865
theorem B655563 : Blo 654306 655563 := bstep (se 1 (by rfl) ⟨491672, by rfl⟩ : syracuseStep 655563 = 983345) B983345
theorem B1474775 : Blo 654306 1474775 := bstep (se 1 (by rfl) ⟨1106081, by rfl⟩ : syracuseStep 1474775 = 2212163) B2212163
theorem B983255 : Blo 654306 983255 := bstep (se 1 (by rfl) ⟨737441, by rfl⟩ : syracuseStep 983255 = 1474883) B1474883
theorem B655575 : Blo 654306 655575 := bstep (se 1 (by rfl) ⟨491681, by rfl⟩ : syracuseStep 655575 = 983363) B983363
theorem B655595 : Blo 654306 655595 := bstep (se 1 (by rfl) ⟨491696, by rfl⟩ : syracuseStep 655595 = 983393) B983393
theorem B655607 : Blo 654306 655607 := bstep (se 1 (by rfl) ⟨491705, by rfl⟩ : syracuseStep 655607 = 983411) B983411
theorem B655627 : Blo 654306 655627 := bstep (se 1 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 655627 = 983441) B983441
theorem B1245451 : Blo 654306 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B655639 : Blo 654306 655639 := bstep (se 1 (by rfl) ⟨491729, by rfl⟩ : syracuseStep 655639 = 983459) B983459
theorem B983321 : Blo 654306 983321 := bstep (se 2 (by rfl) ⟨368745, by rfl⟩ : syracuseStep 983321 = 737491) B737491
theorem B655659 : Blo 654306 655659 := bstep (se 1 (by rfl) ⟨491744, by rfl⟩ : syracuseStep 655659 = 983489) B983489
theorem B655671 : Blo 654306 655671 := bstep (se 1 (by rfl) ⟨491753, by rfl⟩ : syracuseStep 655671 = 983507) B983507
theorem B2490689 : Blo 654306 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B786763 : Blo 654306 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B655691 : Blo 654306 655691 := bstep (se 1 (by rfl) ⟨491768, by rfl⟩ : syracuseStep 655691 = 983537) B983537
theorem B655703 : Blo 654306 655703 := bstep (se 1 (by rfl) ⟨491777, by rfl⟩ : syracuseStep 655703 = 983555) B983555
theorem B1245527 : Blo 654306 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B655723 : Blo 654306 655723 := bstep (se 1 (by rfl) ⟨491792, by rfl⟩ : syracuseStep 655723 = 983585) B983585
theorem B655735 : Blo 654306 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B1474955 : Blo 654306 1474955 := bstep (se 1 (by rfl) ⟨1106216, by rfl⟩ : syracuseStep 1474955 = 2212433) B2212433
theorem B983435 : Blo 654306 983435 := bstep (se 1 (by rfl) ⟨737576, by rfl⟩ : syracuseStep 983435 = 1475153) B1475153
theorem B655755 : Blo 654306 655755 := bstep (se 1 (by rfl) ⟨491816, by rfl⟩ : syracuseStep 655755 = 983633) B983633
theorem B983447 : Blo 654306 983447 := bstep (se 1 (by rfl) ⟨737585, by rfl⟩ : syracuseStep 983447 = 1475171) B1475171
theorem B655767 : Blo 654306 655767 := bstep (se 1 (by rfl) ⟨491825, by rfl⟩ : syracuseStep 655767 = 983651) B983651
theorem B655787 : Blo 654306 655787 := bstep (se 1 (by rfl) ⟨491840, by rfl⟩ : syracuseStep 655787 = 983681) B983681
theorem B655799 : Blo 654306 655799 := bstep (se 1 (by rfl) ⟨491849, by rfl⟩ : syracuseStep 655799 = 983699) B983699
theorem B1475009 : Blo 654306 1475009 := bstep (se 2 (by rfl) ⟨553128, by rfl⟩ : syracuseStep 1475009 = 1106257) B1106257
theorem B655819 : Blo 654306 655819 := bstep (se 1 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 655819 = 983729) B983729
theorem B655831 : Blo 654306 655831 := bstep (se 1 (by rfl) ⟨491873, by rfl⟩ : syracuseStep 655831 = 983747) B983747
theorem B983513 : Blo 654306 983513 := bstep (se 2 (by rfl) ⟨368817, by rfl⟩ : syracuseStep 983513 = 737635) B737635
theorem B655851 : Blo 654306 655851 := bstep (se 1 (by rfl) ⟨491888, by rfl⟩ : syracuseStep 655851 = 983777) B983777
theorem B655863 : Blo 654306 655863 := bstep (se 1 (by rfl) ⟨491897, by rfl⟩ : syracuseStep 655863 = 983795) B983795
theorem B655883 : Blo 654306 655883 := bstep (se 1 (by rfl) ⟨491912, by rfl⟩ : syracuseStep 655883 = 983825) B983825
theorem B655895 : Blo 654306 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B655915 : Blo 654306 655915 := bstep (se 1 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 655915 = 983873) B983873
theorem B655927 : Blo 654306 655927 := bstep (se 1 (by rfl) ⟨491945, by rfl⟩ : syracuseStep 655927 = 983891) B983891
theorem B983627 : Blo 654306 983627 := bstep (se 1 (by rfl) ⟨737720, by rfl⟩ : syracuseStep 983627 = 1475441) B1475441
theorem B655947 : Blo 654306 655947 := bstep (se 1 (by rfl) ⟨491960, by rfl⟩ : syracuseStep 655947 = 983921) B983921
theorem B983639 : Blo 654306 983639 := bstep (se 1 (by rfl) ⟨737729, by rfl⟩ : syracuseStep 983639 = 1475459) B1475459
theorem B655959 : Blo 654306 655959 := bstep (se 1 (by rfl) ⟨491969, by rfl⟩ : syracuseStep 655959 = 983939) B983939
theorem B655979 : Blo 654306 655979 := bstep (se 1 (by rfl) ⟨491984, by rfl⟩ : syracuseStep 655979 = 983969) B983969
theorem B655991 : Blo 654306 655991 := bstep (se 1 (by rfl) ⟨491993, by rfl⟩ : syracuseStep 655991 = 983987) B983987
theorem B656011 : Blo 654306 656011 := bstep (se 1 (by rfl) ⟨492008, by rfl⟩ : syracuseStep 656011 = 984017) B984017
theorem B656023 : Blo 654306 656023 := bstep (se 1 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 656023 = 984035) B984035
theorem B1475225 : Blo 654306 1475225 := bstep (se 2 (by rfl) ⟨553209, by rfl⟩ : syracuseStep 1475225 = 1106419) B1106419
theorem B983705 : Blo 654306 983705 := bstep (se 2 (by rfl) ⟨368889, by rfl⟩ : syracuseStep 983705 = 737779) B737779
theorem B656043 : Blo 654306 656043 := bstep (se 1 (by rfl) ⟨492032, by rfl⟩ : syracuseStep 656043 = 984065) B984065
theorem B656055 : Blo 654306 656055 := bstep (se 1 (by rfl) ⟨492041, by rfl⟩ : syracuseStep 656055 = 984083) B984083
theorem B656075 : Blo 654306 656075 := bstep (se 1 (by rfl) ⟨492056, by rfl⟩ : syracuseStep 656075 = 984113) B984113
theorem B656087 : Blo 654306 656087 := bstep (se 1 (by rfl) ⟨492065, by rfl⟩ : syracuseStep 656087 = 984131) B984131
theorem B656107 : Blo 654306 656107 := bstep (se 1 (by rfl) ⟨492080, by rfl⟩ : syracuseStep 656107 = 984161) B984161
theorem B1475315 : Blo 654306 1475315 := bstep (se 1 (by rfl) ⟨1106486, by rfl⟩ : syracuseStep 1475315 = 2212973) B2212973
theorem B656119 : Blo 654306 656119 := bstep (se 1 (by rfl) ⟨492089, by rfl⟩ : syracuseStep 656119 = 984179) B984179
theorem B983819 : Blo 654306 983819 := bstep (se 1 (by rfl) ⟨737864, by rfl⟩ : syracuseStep 983819 = 1475729) B1475729
theorem B656139 : Blo 654306 656139 := bstep (se 1 (by rfl) ⟨492104, by rfl⟩ : syracuseStep 656139 = 984209) B984209
theorem B1475351 : Blo 654306 1475351 := bstep (se 1 (by rfl) ⟨1106513, by rfl⟩ : syracuseStep 1475351 = 2213027) B2213027
theorem B983831 : Blo 654306 983831 := bstep (se 1 (by rfl) ⟨737873, by rfl⟩ : syracuseStep 983831 = 1475747) B1475747
theorem B656151 : Blo 654306 656151 := bstep (se 1 (by rfl) ⟨492113, by rfl⟩ : syracuseStep 656151 = 984227) B984227
theorem B656171 : Blo 654306 656171 := bstep (se 1 (by rfl) ⟨492128, by rfl⟩ : syracuseStep 656171 = 984257) B984257
theorem B2097971 : Blo 654306 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B656183 : Blo 654306 656183 := bstep (se 1 (by rfl) ⟨492137, by rfl⟩ : syracuseStep 656183 = 984275) B984275
theorem B1868609 : Blo 654306 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B852811 : Blo 654306 852811 := bstep (se 1 (by rfl) ⟨639608, by rfl⟩ : syracuseStep 852811 = 1279217) B1279217
theorem B656203 : Blo 654306 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B656215 : Blo 654306 656215 := bstep (se 1 (by rfl) ⟨492161, by rfl⟩ : syracuseStep 656215 = 984323) B984323
theorem B983897 : Blo 654306 983897 := bstep (se 2 (by rfl) ⟨368961, by rfl⟩ : syracuseStep 983897 = 737923) B737923
theorem B1868633 : Blo 654306 1868633 := bstep (se 2 (by rfl) ⟨700737, by rfl⟩ : syracuseStep 1868633 = 1401475) B1401475
theorem B656235 : Blo 654306 656235 := bstep (se 1 (by rfl) ⟨492176, by rfl⟩ : syracuseStep 656235 = 984353) B984353
theorem B656247 : Blo 654306 656247 := bstep (se 1 (by rfl) ⟨492185, by rfl⟩ : syracuseStep 656247 = 984371) B984371
theorem B656267 : Blo 654306 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B656279 : Blo 654306 656279 := bstep (se 1 (by rfl) ⟨492209, by rfl⟩ : syracuseStep 656279 = 984419) B984419
theorem B656299 : Blo 654306 656299 := bstep (se 1 (by rfl) ⟨492224, by rfl⟩ : syracuseStep 656299 = 984449) B984449
theorem B4719539 : Blo 654306 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B656311 : Blo 654306 656311 := bstep (se 1 (by rfl) ⟨492233, by rfl⟩ : syracuseStep 656311 = 984467) B984467
theorem B1475531 : Blo 654306 1475531 := bstep (se 1 (by rfl) ⟨1106648, by rfl⟩ : syracuseStep 1475531 = 2213297) B2213297
theorem B984011 : Blo 654306 984011 := bstep (se 1 (by rfl) ⟨738008, by rfl⟩ : syracuseStep 984011 = 1476017) B1476017
theorem B656331 : Blo 654306 656331 := bstep (se 1 (by rfl) ⟨492248, by rfl⟩ : syracuseStep 656331 = 984497) B984497
theorem B984023 : Blo 654306 984023 := bstep (se 1 (by rfl) ⟨738017, by rfl⟩ : syracuseStep 984023 = 1476035) B1476035
theorem B656343 : Blo 654306 656343 := bstep (se 1 (by rfl) ⟨492257, by rfl⟩ : syracuseStep 656343 = 984515) B984515
theorem B2491357 : Blo 654306 2491357 := bstep (se 3 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 2491357 = 934259) B934259
theorem B656363 : Blo 654306 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B1246195 : Blo 654306 1246195 := bstep (se 1 (by rfl) ⟨934646, by rfl⟩ : syracuseStep 1246195 = 1869293) B1869293
theorem B656375 : Blo 654306 656375 := bstep (se 1 (by rfl) ⟨492281, by rfl⟩ : syracuseStep 656375 = 984563) B984563
theorem B1475585 : Blo 654306 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B656395 : Blo 654306 656395 := bstep (se 1 (by rfl) ⟨492296, by rfl⟩ : syracuseStep 656395 = 984593) B984593
theorem B656407 : Blo 654306 656407 := bstep (se 1 (by rfl) ⟨492305, by rfl⟩ : syracuseStep 656407 = 984611) B984611
theorem B984089 : Blo 654306 984089 := bstep (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) B738067
theorem B656427 : Blo 654306 656427 := bstep (se 1 (by rfl) ⟨492320, by rfl⟩ : syracuseStep 656427 = 984641) B984641
theorem B656439 : Blo 654306 656439 := bstep (se 1 (by rfl) ⟨492329, by rfl⟩ : syracuseStep 656439 = 984659) B984659
theorem B656459 : Blo 654306 656459 := bstep (se 1 (by rfl) ⟨492344, by rfl⟩ : syracuseStep 656459 = 984689) B984689
theorem B656471 : Blo 654306 656471 := bstep (se 1 (by rfl) ⟨492353, by rfl⟩ : syracuseStep 656471 = 984707) B984707
theorem B656491 : Blo 654306 656491 := bstep (se 1 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 656491 = 984737) B984737
theorem B656503 : Blo 654306 656503 := bstep (se 1 (by rfl) ⟨492377, by rfl⟩ : syracuseStep 656503 = 984755) B984755
theorem B984203 : Blo 654306 984203 := bstep (se 1 (by rfl) ⟨738152, by rfl⟩ : syracuseStep 984203 = 1476305) B1476305
theorem B656523 : Blo 654306 656523 := bstep (se 1 (by rfl) ⟨492392, by rfl⟩ : syracuseStep 656523 = 984785) B984785
theorem B984215 : Blo 654306 984215 := bstep (se 1 (by rfl) ⟨738161, by rfl⟩ : syracuseStep 984215 = 1476323) B1476323
theorem B656535 : Blo 654306 656535 := bstep (se 1 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 656535 = 984803) B984803
theorem B656555 : Blo 654306 656555 := bstep (se 1 (by rfl) ⟨492416, by rfl⟩ : syracuseStep 656555 = 984833) B984833
theorem B3998899 : Blo 654306 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B656567 : Blo 654306 656567 := bstep (se 1 (by rfl) ⟨492425, by rfl⟩ : syracuseStep 656567 = 984851) B984851
theorem B1180865 : Blo 654306 1180865 := bstep (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) B885649
theorem B656587 : Blo 654306 656587 := bstep (se 1 (by rfl) ⟨492440, by rfl⟩ : syracuseStep 656587 = 984881) B984881
theorem B1246423 : Blo 654306 1246423 := bstep (se 1 (by rfl) ⟨934817, by rfl⟩ : syracuseStep 1246423 = 1869635) B1869635
theorem B656599 : Blo 654306 656599 := bstep (se 1 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 656599 = 984899) B984899
theorem B1475801 : Blo 654306 1475801 := bstep (se 2 (by rfl) ⟨553425, by rfl⟩ : syracuseStep 1475801 = 1106851) B1106851
theorem B984281 : Blo 654306 984281 := bstep (se 2 (by rfl) ⟨369105, by rfl⟩ : syracuseStep 984281 = 738211) B738211
theorem B656619 : Blo 654306 656619 := bstep (se 1 (by rfl) ⟨492464, by rfl⟩ : syracuseStep 656619 = 984929) B984929
theorem B656631 : Blo 654306 656631 := bstep (se 1 (by rfl) ⟨492473, by rfl⟩ : syracuseStep 656631 = 984947) B984947
theorem B656651 : Blo 654306 656651 := bstep (se 1 (by rfl) ⟨492488, by rfl⟩ : syracuseStep 656651 = 984977) B984977
theorem B656663 : Blo 654306 656663 := bstep (se 1 (by rfl) ⟨492497, by rfl⟩ : syracuseStep 656663 = 984995) B984995
theorem B656683 : Blo 654306 656683 := bstep (se 1 (by rfl) ⟨492512, by rfl⟩ : syracuseStep 656683 = 985025) B985025
theorem B1475891 : Blo 654306 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B656695 : Blo 654306 656695 := bstep (se 1 (by rfl) ⟨492521, by rfl⟩ : syracuseStep 656695 = 985043) B985043
theorem B1246529 : Blo 654306 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B984395 : Blo 654306 984395 := bstep (se 1 (by rfl) ⟨738296, by rfl⟩ : syracuseStep 984395 = 1476593) B1476593
theorem B656715 : Blo 654306 656715 := bstep (se 1 (by rfl) ⟨492536, by rfl⟩ : syracuseStep 656715 = 985073) B985073
theorem B1475927 : Blo 654306 1475927 := bstep (se 1 (by rfl) ⟨1106945, by rfl⟩ : syracuseStep 1475927 = 2213891) B2213891
theorem B984407 : Blo 654306 984407 := bstep (se 1 (by rfl) ⟨738305, by rfl⟩ : syracuseStep 984407 = 1476611) B1476611
theorem B656727 : Blo 654306 656727 := bstep (se 1 (by rfl) ⟨492545, by rfl⟩ : syracuseStep 656727 = 985091) B985091
theorem B656747 : Blo 654306 656747 := bstep (se 1 (by rfl) ⟨492560, by rfl⟩ : syracuseStep 656747 = 985121) B985121
theorem B656759 : Blo 654306 656759 := bstep (se 1 (by rfl) ⟨492569, by rfl⟩ : syracuseStep 656759 = 985139) B985139
theorem B656779 : Blo 654306 656779 := bstep (se 1 (by rfl) ⟨492584, by rfl⟩ : syracuseStep 656779 = 985169) B985169
theorem B656791 : Blo 654306 656791 := bstep (se 1 (by rfl) ⟨492593, by rfl⟩ : syracuseStep 656791 = 985187) B985187
theorem B984473 : Blo 654306 984473 := bstep (se 2 (by rfl) ⟨369177, by rfl⟩ : syracuseStep 984473 = 738355) B738355
theorem B656811 : Blo 654306 656811 := bstep (se 1 (by rfl) ⟨492608, by rfl⟩ : syracuseStep 656811 = 985217) B985217
theorem B656823 : Blo 654306 656823 := bstep (se 1 (by rfl) ⟨492617, by rfl⟩ : syracuseStep 656823 = 985235) B985235
theorem B656843 : Blo 654306 656843 := bstep (se 1 (by rfl) ⟨492632, by rfl⟩ : syracuseStep 656843 = 985265) B985265
theorem B656855 : Blo 654306 656855 := bstep (se 1 (by rfl) ⟨492641, by rfl⟩ : syracuseStep 656855 = 985283) B985283
theorem B2098649 : Blo 654306 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1246681 : Blo 654306 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B656875 : Blo 654306 656875 := bstep (se 1 (by rfl) ⟨492656, by rfl⟩ : syracuseStep 656875 = 985313) B985313
theorem B656887 : Blo 654306 656887 := bstep (se 1 (by rfl) ⟨492665, by rfl⟩ : syracuseStep 656887 = 985331) B985331
theorem B1476107 : Blo 654306 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B984587 : Blo 654306 984587 := bstep (se 1 (by rfl) ⟨738440, by rfl⟩ : syracuseStep 984587 = 1476881) B1476881
theorem B656907 : Blo 654306 656907 := bstep (se 1 (by rfl) ⟨492680, by rfl⟩ : syracuseStep 656907 = 985361) B985361
theorem B984599 : Blo 654306 984599 := bstep (se 1 (by rfl) ⟨738449, by rfl⟩ : syracuseStep 984599 = 1476899) B1476899
theorem B656919 : Blo 654306 656919 := bstep (se 1 (by rfl) ⟨492689, by rfl⟩ : syracuseStep 656919 = 985379) B985379
theorem B656939 : Blo 654306 656939 := bstep (se 1 (by rfl) ⟨492704, by rfl⟩ : syracuseStep 656939 = 985409) B985409
theorem B656951 : Blo 654306 656951 := bstep (se 1 (by rfl) ⟨492713, by rfl⟩ : syracuseStep 656951 = 985427) B985427
theorem B1476161 : Blo 654306 1476161 := bstep (se 2 (by rfl) ⟨553560, by rfl⟩ : syracuseStep 1476161 = 1107121) B1107121
theorem B656971 : Blo 654306 656971 := bstep (se 1 (by rfl) ⟨492728, by rfl⟩ : syracuseStep 656971 = 985457) B985457
theorem B656983 : Blo 654306 656983 := bstep (se 1 (by rfl) ⟨492737, by rfl⟩ : syracuseStep 656983 = 985475) B985475
theorem B984665 : Blo 654306 984665 := bstep (se 2 (by rfl) ⟨369249, by rfl⟩ : syracuseStep 984665 = 738499) B738499
theorem B657003 : Blo 654306 657003 := bstep (se 1 (by rfl) ⟨492752, by rfl⟩ : syracuseStep 657003 = 985505) B985505
theorem B657015 : Blo 654306 657015 := bstep (se 1 (by rfl) ⟨492761, by rfl⟩ : syracuseStep 657015 = 985523) B985523
theorem B657035 : Blo 654306 657035 := bstep (se 1 (by rfl) ⟨492776, by rfl⟩ : syracuseStep 657035 = 985553) B985553
theorem B657047 : Blo 654306 657047 := bstep (se 1 (by rfl) ⟨492785, by rfl⟩ : syracuseStep 657047 = 985571) B985571
theorem B3606167 : Blo 654306 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B657067 : Blo 654306 657067 := bstep (se 1 (by rfl) ⟨492800, by rfl⟩ : syracuseStep 657067 = 985601) B985601
theorem B657079 : Blo 654306 657079 := bstep (se 1 (by rfl) ⟨492809, by rfl⟩ : syracuseStep 657079 = 985619) B985619
theorem B1574603 : Blo 654306 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B984779 : Blo 654306 984779 := bstep (se 1 (by rfl) ⟨738584, by rfl⟩ : syracuseStep 984779 = 1477169) B1477169
theorem B657099 : Blo 654306 657099 := bstep (se 1 (by rfl) ⟨492824, by rfl⟩ : syracuseStep 657099 = 985649) B985649
theorem B984791 : Blo 654306 984791 := bstep (se 1 (by rfl) ⟨738593, by rfl⟩ : syracuseStep 984791 = 1477187) B1477187
theorem B657111 : Blo 654306 657111 := bstep (se 1 (by rfl) ⟨492833, by rfl⟩ : syracuseStep 657111 = 985667) B985667
theorem B657131 : Blo 654306 657131 := bstep (se 1 (by rfl) ⟨492848, by rfl⟩ : syracuseStep 657131 = 985697) B985697
theorem B657143 : Blo 654306 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B657163 : Blo 654306 657163 := bstep (se 1 (by rfl) ⟨492872, by rfl⟩ : syracuseStep 657163 = 985745) B985745
theorem B657175 : Blo 654306 657175 := bstep (se 1 (by rfl) ⟨492881, by rfl⟩ : syracuseStep 657175 = 985763) B985763
theorem B1476377 : Blo 654306 1476377 := bstep (se 2 (by rfl) ⟨553641, by rfl⟩ : syracuseStep 1476377 = 1107283) B1107283
theorem B984857 : Blo 654306 984857 := bstep (se 2 (by rfl) ⟨369321, by rfl⟩ : syracuseStep 984857 = 738643) B738643
theorem B657195 : Blo 654306 657195 := bstep (se 1 (by rfl) ⟨492896, by rfl⟩ : syracuseStep 657195 = 985793) B985793
theorem B657207 : Blo 654306 657207 := bstep (se 1 (by rfl) ⟨492905, by rfl⟩ : syracuseStep 657207 = 985811) B985811
theorem B657227 : Blo 654306 657227 := bstep (se 1 (by rfl) ⟨492920, by rfl⟩ : syracuseStep 657227 = 985841) B985841
theorem B657239 : Blo 654306 657239 := bstep (se 1 (by rfl) ⟨492929, by rfl⟩ : syracuseStep 657239 = 985859) B985859
theorem B657259 : Blo 654306 657259 := bstep (se 1 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 657259 = 985889) B985889
theorem B1476467 : Blo 654306 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B657271 : Blo 654306 657271 := bstep (se 1 (by rfl) ⟨492953, by rfl⟩ : syracuseStep 657271 = 985907) B985907
theorem B984971 : Blo 654306 984971 := bstep (se 1 (by rfl) ⟨738728, by rfl⟩ : syracuseStep 984971 = 1477457) B1477457
theorem B657291 : Blo 654306 657291 := bstep (se 1 (by rfl) ⟨492968, by rfl⟩ : syracuseStep 657291 = 985937) B985937
theorem B1476503 : Blo 654306 1476503 := bstep (se 1 (by rfl) ⟨1107377, by rfl⟩ : syracuseStep 1476503 = 2214755) B2214755
theorem B984983 : Blo 654306 984983 := bstep (se 1 (by rfl) ⟨738737, by rfl⟩ : syracuseStep 984983 = 1477475) B1477475
theorem B657303 : Blo 654306 657303 := bstep (se 1 (by rfl) ⟨492977, by rfl⟩ : syracuseStep 657303 = 985955) B985955
theorem B657323 : Blo 654306 657323 := bstep (se 1 (by rfl) ⟨492992, by rfl⟩ : syracuseStep 657323 = 985985) B985985
theorem B657335 : Blo 654306 657335 := bstep (se 1 (by rfl) ⟨493001, by rfl⟩ : syracuseStep 657335 = 986003) B986003
theorem B657355 : Blo 654306 657355 := bstep (se 1 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 657355 = 986033) B986033
theorem B657367 : Blo 654306 657367 := bstep (se 1 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 657367 = 986051) B986051
theorem B985049 : Blo 654306 985049 := bstep (se 2 (by rfl) ⟨369393, by rfl⟩ : syracuseStep 985049 = 738787) B738787
theorem B657387 : Blo 654306 657387 := bstep (se 1 (by rfl) ⟨493040, by rfl⟩ : syracuseStep 657387 = 986081) B986081
theorem B657399 : Blo 654306 657399 := bstep (se 1 (by rfl) ⟨493049, by rfl⟩ : syracuseStep 657399 = 986099) B986099
theorem B657419 : Blo 654306 657419 := bstep (se 1 (by rfl) ⟨493064, by rfl⟩ : syracuseStep 657419 = 986129) B986129
theorem B10651661 : Blo 654306 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B657431 : Blo 654306 657431 := bstep (se 1 (by rfl) ⟨493073, by rfl⟩ : syracuseStep 657431 = 986147) B986147
theorem B657451 : Blo 654306 657451 := bstep (se 1 (by rfl) ⟨493088, by rfl⟩ : syracuseStep 657451 = 986177) B986177
theorem B1869875 : Blo 654306 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B657463 : Blo 654306 657463 := bstep (se 1 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 657463 = 986195) B986195
theorem B1476683 : Blo 654306 1476683 := bstep (se 1 (by rfl) ⟨1107512, by rfl⟩ : syracuseStep 1476683 = 2215025) B2215025
theorem B985163 : Blo 654306 985163 := bstep (se 1 (by rfl) ⟨738872, by rfl⟩ : syracuseStep 985163 = 1477745) B1477745
theorem B657483 : Blo 654306 657483 := bstep (se 1 (by rfl) ⟨493112, by rfl⟩ : syracuseStep 657483 = 986225) B986225
theorem B985175 : Blo 654306 985175 := bstep (se 1 (by rfl) ⟨738881, by rfl⟩ : syracuseStep 985175 = 1477763) B1477763
theorem B657495 : Blo 654306 657495 := bstep (se 1 (by rfl) ⟨493121, by rfl⟩ : syracuseStep 657495 = 986243) B986243
theorem B657515 : Blo 654306 657515 := bstep (se 1 (by rfl) ⟨493136, by rfl⟩ : syracuseStep 657515 = 986273) B986273
theorem B657527 : Blo 654306 657527 := bstep (se 1 (by rfl) ⟨493145, by rfl⟩ : syracuseStep 657527 = 986291) B986291
theorem B1476737 : Blo 654306 1476737 := bstep (se 2 (by rfl) ⟨553776, by rfl⟩ : syracuseStep 1476737 = 1107553) B1107553
theorem B657547 : Blo 654306 657547 := bstep (se 1 (by rfl) ⟨493160, by rfl⟩ : syracuseStep 657547 = 986321) B986321
theorem B657559 : Blo 654306 657559 := bstep (se 1 (by rfl) ⟨493169, by rfl⟩ : syracuseStep 657559 = 986339) B986339
theorem B985241 : Blo 654306 985241 := bstep (se 2 (by rfl) ⟨369465, by rfl⟩ : syracuseStep 985241 = 738931) B738931
theorem B657579 : Blo 654306 657579 := bstep (se 1 (by rfl) ⟨493184, by rfl⟩ : syracuseStep 657579 = 986369) B986369
theorem B657591 : Blo 654306 657591 := bstep (se 1 (by rfl) ⟨493193, by rfl⟩ : syracuseStep 657591 = 986387) B986387
theorem B657611 : Blo 654306 657611 := bstep (se 1 (by rfl) ⟨493208, by rfl⟩ : syracuseStep 657611 = 986417) B986417
theorem B657623 : Blo 654306 657623 := bstep (se 1 (by rfl) ⟨493217, by rfl⟩ : syracuseStep 657623 = 986435) B986435
theorem B2492633 : Blo 654306 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B657643 : Blo 654306 657643 := bstep (se 1 (by rfl) ⟨493232, by rfl⟩ : syracuseStep 657643 = 986465) B986465
theorem B657655 : Blo 654306 657655 := bstep (se 1 (by rfl) ⟨493241, by rfl⟩ : syracuseStep 657655 = 986483) B986483
theorem B985355 : Blo 654306 985355 := bstep (se 1 (by rfl) ⟨739016, by rfl⟩ : syracuseStep 985355 = 1478033) B1478033
theorem B657675 : Blo 654306 657675 := bstep (se 1 (by rfl) ⟨493256, by rfl⟩ : syracuseStep 657675 = 986513) B986513
theorem B985367 : Blo 654306 985367 := bstep (se 1 (by rfl) ⟨739025, by rfl⟩ : syracuseStep 985367 = 1478051) B1478051
theorem B657687 : Blo 654306 657687 := bstep (se 1 (by rfl) ⟨493265, by rfl⟩ : syracuseStep 657687 = 986531) B986531
theorem B657707 : Blo 654306 657707 := bstep (se 1 (by rfl) ⟨493280, by rfl⟩ : syracuseStep 657707 = 986561) B986561
theorem B657719 : Blo 654306 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B657739 : Blo 654306 657739 := bstep (se 1 (by rfl) ⟨493304, by rfl⟩ : syracuseStep 657739 = 986609) B986609
theorem B657751 : Blo 654306 657751 := bstep (se 1 (by rfl) ⟨493313, by rfl⟩ : syracuseStep 657751 = 986627) B986627
theorem B1476953 : Blo 654306 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B985433 : Blo 654306 985433 := bstep (se 2 (by rfl) ⟨369537, by rfl⟩ : syracuseStep 985433 = 739075) B739075
theorem B657771 : Blo 654306 657771 := bstep (se 1 (by rfl) ⟨493328, by rfl⟩ : syracuseStep 657771 = 986657) B986657
theorem B657783 : Blo 654306 657783 := bstep (se 1 (by rfl) ⟨493337, by rfl⟩ : syracuseStep 657783 = 986675) B986675
theorem B657803 : Blo 654306 657803 := bstep (se 1 (by rfl) ⟨493352, by rfl⟩ : syracuseStep 657803 = 986705) B986705
theorem B657815 : Blo 654306 657815 := bstep (se 1 (by rfl) ⟨493361, by rfl⟩ : syracuseStep 657815 = 986723) B986723
theorem B657835 : Blo 654306 657835 := bstep (se 1 (by rfl) ⟨493376, by rfl⟩ : syracuseStep 657835 = 986753) B986753
theorem B1477043 : Blo 654306 1477043 := bstep (se 1 (by rfl) ⟨1107782, by rfl⟩ : syracuseStep 1477043 = 2215565) B2215565
theorem B657847 : Blo 654306 657847 := bstep (se 1 (by rfl) ⟨493385, by rfl⟩ : syracuseStep 657847 = 986771) B986771
theorem B985547 : Blo 654306 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B657867 : Blo 654306 657867 := bstep (se 1 (by rfl) ⟨493400, by rfl⟩ : syracuseStep 657867 = 986801) B986801
theorem B1477079 : Blo 654306 1477079 := bstep (se 1 (by rfl) ⟨1107809, by rfl⟩ : syracuseStep 1477079 = 2215619) B2215619
theorem B985559 : Blo 654306 985559 := bstep (se 1 (by rfl) ⟨739169, by rfl⟩ : syracuseStep 985559 = 1478339) B1478339
theorem B657879 : Blo 654306 657879 := bstep (se 1 (by rfl) ⟨493409, by rfl⟩ : syracuseStep 657879 = 986819) B986819
theorem B657899 : Blo 654306 657899 := bstep (se 1 (by rfl) ⟨493424, by rfl⟩ : syracuseStep 657899 = 986849) B986849
theorem B657911 : Blo 654306 657911 := bstep (se 1 (by rfl) ⟨493433, by rfl⟩ : syracuseStep 657911 = 986867) B986867
theorem B657931 : Blo 654306 657931 := bstep (se 1 (by rfl) ⟨493448, by rfl⟩ : syracuseStep 657931 = 986897) B986897
theorem B657943 : Blo 654306 657943 := bstep (se 1 (by rfl) ⟨493457, by rfl⟩ : syracuseStep 657943 = 986915) B986915
theorem B985625 : Blo 654306 985625 := bstep (se 2 (by rfl) ⟨369609, by rfl⟩ : syracuseStep 985625 = 739219) B739219
theorem B657963 : Blo 654306 657963 := bstep (se 1 (by rfl) ⟨493472, by rfl⟩ : syracuseStep 657963 = 986945) B986945
theorem B657975 : Blo 654306 657975 := bstep (se 1 (by rfl) ⟨493481, by rfl⟩ : syracuseStep 657975 = 986963) B986963
theorem B657995 : Blo 654306 657995 := bstep (se 1 (by rfl) ⟨493496, by rfl⟩ : syracuseStep 657995 = 986993) B986993
theorem B658007 : Blo 654306 658007 := bstep (se 1 (by rfl) ⟨493505, by rfl⟩ : syracuseStep 658007 = 987011) B987011
theorem B658027 : Blo 654306 658027 := bstep (se 1 (by rfl) ⟨493520, by rfl⟩ : syracuseStep 658027 = 987041) B987041
theorem B658039 : Blo 654306 658039 := bstep (se 1 (by rfl) ⟨493529, by rfl⟩ : syracuseStep 658039 = 987059) B987059
theorem B1477259 : Blo 654306 1477259 := bstep (se 1 (by rfl) ⟨1107944, by rfl⟩ : syracuseStep 1477259 = 2215889) B2215889
theorem B985739 : Blo 654306 985739 := bstep (se 1 (by rfl) ⟨739304, by rfl⟩ : syracuseStep 985739 = 1478609) B1478609
theorem B658059 : Blo 654306 658059 := bstep (se 1 (by rfl) ⟨493544, by rfl⟩ : syracuseStep 658059 = 987089) B987089
theorem B1182359 : Blo 654306 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B985751 : Blo 654306 985751 := bstep (se 1 (by rfl) ⟨739313, by rfl⟩ : syracuseStep 985751 = 1478627) B1478627
theorem B658071 : Blo 654306 658071 := bstep (se 1 (by rfl) ⟨493553, by rfl⟩ : syracuseStep 658071 = 987107) B987107
theorem B658091 : Blo 654306 658091 := bstep (se 1 (by rfl) ⟨493568, by rfl⟩ : syracuseStep 658091 = 987137) B987137
theorem B658103 : Blo 654306 658103 := bstep (se 1 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 658103 = 987155) B987155
theorem B1477313 : Blo 654306 1477313 := bstep (se 2 (by rfl) ⟨553992, by rfl⟩ : syracuseStep 1477313 = 1107985) B1107985
theorem B658123 : Blo 654306 658123 := bstep (se 1 (by rfl) ⟨493592, by rfl⟩ : syracuseStep 658123 = 987185) B987185
theorem B658135 : Blo 654306 658135 := bstep (se 1 (by rfl) ⟨493601, by rfl⟩ : syracuseStep 658135 = 987203) B987203
theorem B985817 : Blo 654306 985817 := bstep (se 2 (by rfl) ⟨369681, by rfl⟩ : syracuseStep 985817 = 739363) B739363
theorem B658155 : Blo 654306 658155 := bstep (se 1 (by rfl) ⟨493616, by rfl⟩ : syracuseStep 658155 = 987233) B987233
theorem B1247987 : Blo 654306 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B658167 : Blo 654306 658167 := bstep (se 1 (by rfl) ⟨493625, by rfl⟩ : syracuseStep 658167 = 987251) B987251
theorem B658187 : Blo 654306 658187 := bstep (se 1 (by rfl) ⟨493640, by rfl⟩ : syracuseStep 658187 = 987281) B987281
theorem B2362135 : Blo 654306 2362135 := bstep (se 1 (by rfl) ⟨1771601, by rfl⟩ : syracuseStep 2362135 = 3543203) B3543203
theorem B658199 : Blo 654306 658199 := bstep (se 1 (by rfl) ⟨493649, by rfl⟩ : syracuseStep 658199 = 987299) B987299
theorem B658219 : Blo 654306 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B658231 : Blo 654306 658231 := bstep (se 1 (by rfl) ⟨493673, by rfl⟩ : syracuseStep 658231 = 987347) B987347
theorem B985931 : Blo 654306 985931 := bstep (se 1 (by rfl) ⟨739448, by rfl⟩ : syracuseStep 985931 = 1478897) B1478897
theorem B658251 : Blo 654306 658251 := bstep (se 1 (by rfl) ⟨493688, by rfl⟩ : syracuseStep 658251 = 987377) B987377
theorem B985943 : Blo 654306 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B658263 : Blo 654306 658263 := bstep (se 1 (by rfl) ⟨493697, by rfl⟩ : syracuseStep 658263 = 987395) B987395
theorem B658283 : Blo 654306 658283 := bstep (se 1 (by rfl) ⟨493712, by rfl⟩ : syracuseStep 658283 = 987425) B987425
theorem B658295 : Blo 654306 658295 := bstep (se 1 (by rfl) ⟨493721, by rfl⟩ : syracuseStep 658295 = 987443) B987443
theorem B1248139 : Blo 654306 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B1477529 : Blo 654306 1477529 := bstep (se 2 (by rfl) ⟨554073, by rfl⟩ : syracuseStep 1477529 = 1108147) B1108147
theorem B986009 : Blo 654306 986009 := bstep (se 2 (by rfl) ⟨369753, by rfl⟩ : syracuseStep 986009 = 739507) B739507
theorem B1477619 : Blo 654306 1477619 := bstep (se 1 (by rfl) ⟨1108214, by rfl⟩ : syracuseStep 1477619 = 2216429) B2216429
theorem B986123 : Blo 654306 986123 := bstep (se 1 (by rfl) ⟨739592, by rfl⟩ : syracuseStep 986123 = 1479185) B1479185
theorem B1477655 : Blo 654306 1477655 := bstep (se 1 (by rfl) ⟨1108241, by rfl⟩ : syracuseStep 1477655 = 2216483) B2216483
theorem B986135 : Blo 654306 986135 := bstep (se 1 (by rfl) ⟨739601, by rfl⟩ : syracuseStep 986135 = 1479203) B1479203
theorem B986201 : Blo 654306 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B1477835 : Blo 654306 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B986315 : Blo 654306 986315 := bstep (se 1 (by rfl) ⟨739736, by rfl⟩ : syracuseStep 986315 = 1479473) B1479473
theorem B888023 : Blo 654306 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B986327 : Blo 654306 986327 := bstep (se 1 (by rfl) ⟨739745, by rfl⟩ : syracuseStep 986327 = 1479491) B1479491
theorem B1248473 : Blo 654306 1248473 := bstep (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) B936355
theorem B1477889 : Blo 654306 1477889 := bstep (se 2 (by rfl) ⟨554208, by rfl⟩ : syracuseStep 1477889 = 1108417) B1108417
theorem B986393 : Blo 654306 986393 := bstep (se 2 (by rfl) ⟨369897, by rfl⟩ : syracuseStep 986393 = 739795) B739795
theorem B1346881 : Blo 654306 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B986507 : Blo 654306 986507 := bstep (se 1 (by rfl) ⟨739880, by rfl⟩ : syracuseStep 986507 = 1479761) B1479761
theorem B986519 : Blo 654306 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B1478105 : Blo 654306 1478105 := bstep (se 2 (by rfl) ⟨554289, by rfl⟩ : syracuseStep 1478105 = 1108579) B1108579
theorem B986585 : Blo 654306 986585 := bstep (se 2 (by rfl) ⟨369969, by rfl⟩ : syracuseStep 986585 = 739939) B739939
theorem B1052183 : Blo 654306 1052183 := bstep (se 1 (by rfl) ⟨789137, by rfl⟩ : syracuseStep 1052183 = 1578275) B1578275
theorem B2657843 : Blo 654306 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B1478195 : Blo 654306 1478195 := bstep (se 1 (by rfl) ⟨1108646, by rfl⟩ : syracuseStep 1478195 = 2217293) B2217293
theorem B986699 : Blo 654306 986699 := bstep (se 1 (by rfl) ⟨740024, by rfl⟩ : syracuseStep 986699 = 1480049) B1480049
theorem B1478231 : Blo 654306 1478231 := bstep (se 1 (by rfl) ⟨1108673, by rfl⟩ : syracuseStep 1478231 = 2217347) B2217347
theorem B986711 : Blo 654306 986711 := bstep (se 1 (by rfl) ⟨740033, by rfl⟩ : syracuseStep 986711 = 1480067) B1480067
theorem B986777 : Blo 654306 986777 := bstep (se 2 (by rfl) ⟨370041, by rfl⟩ : syracuseStep 986777 = 740083) B740083
theorem B1183475 : Blo 654306 1183475 := bstep (se 1 (by rfl) ⟨887606, by rfl⟩ : syracuseStep 1183475 = 1775213) B1775213
theorem B1478411 : Blo 654306 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B986891 : Blo 654306 986891 := bstep (se 1 (by rfl) ⟨740168, by rfl⟩ : syracuseStep 986891 = 1480337) B1480337
theorem B2690833 : Blo 654306 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B986903 : Blo 654306 986903 := bstep (se 1 (by rfl) ⟨740177, by rfl⟩ : syracuseStep 986903 = 1480355) B1480355
theorem B2494259 : Blo 654306 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B11210561 : Blo 654306 11210561 := bstep (se 2 (by rfl) ⟨4203960, by rfl⟩ : syracuseStep 11210561 = 8407921) B8407921
theorem B2494273 : Blo 654306 2494273 := bstep (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) B1870705
theorem B1478465 : Blo 654306 1478465 := bstep (se 2 (by rfl) ⟨554424, by rfl⟩ : syracuseStep 1478465 = 1108849) B1108849
theorem B1249111 : Blo 654306 1249111 := bstep (se 1 (by rfl) ⟨936833, by rfl⟩ : syracuseStep 1249111 = 1873667) B1873667
theorem B1576793 : Blo 654306 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B986969 : Blo 654306 986969 := bstep (se 2 (by rfl) ⟨370113, by rfl⟩ : syracuseStep 986969 = 740227) B740227
theorem B2101085 : Blo 654306 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B1183691 : Blo 654306 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B987083 : Blo 654306 987083 := bstep (se 1 (by rfl) ⟨740312, by rfl⟩ : syracuseStep 987083 = 1480625) B1480625
theorem B987095 : Blo 654306 987095 := bstep (se 1 (by rfl) ⟨740321, by rfl⟩ : syracuseStep 987095 = 1480643) B1480643
theorem B1478681 : Blo 654306 1478681 := bstep (se 2 (by rfl) ⟨554505, by rfl⟩ : syracuseStep 1478681 = 1109011) B1109011
theorem B987161 : Blo 654306 987161 := bstep (se 2 (by rfl) ⟨370185, by rfl⟩ : syracuseStep 987161 = 740371) B740371
theorem B3313709 : Blo 654306 3313709 := bstep (se 3 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 3313709 = 1242641) B1242641
theorem B3543115 : Blo 654306 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B1052747 : Blo 654306 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B1478771 : Blo 654306 1478771 := bstep (se 1 (by rfl) ⟨1109078, by rfl⟩ : syracuseStep 1478771 = 2218157) B2218157
theorem B987275 : Blo 654306 987275 := bstep (se 1 (by rfl) ⟨740456, by rfl⟩ : syracuseStep 987275 = 1480913) B1480913
theorem B1478807 : Blo 654306 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B987287 : Blo 654306 987287 := bstep (se 1 (by rfl) ⟨740465, by rfl⟩ : syracuseStep 987287 = 1480931) B1480931
theorem B1052887 : Blo 654306 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B987353 : Blo 654306 987353 := bstep (se 2 (by rfl) ⟨370257, by rfl⟩ : syracuseStep 987353 = 740515) B740515
theorem B1478987 : Blo 654306 1478987 := bstep (se 1 (by rfl) ⟨1109240, by rfl⟩ : syracuseStep 1478987 = 2218481) B2218481
theorem B1479041 : Blo 654306 1479041 := bstep (se 2 (by rfl) ⟨554640, by rfl⟩ : syracuseStep 1479041 = 1109281) B1109281
theorem B1479257 : Blo 654306 1479257 := bstep (se 2 (by rfl) ⟨554721, by rfl⟩ : syracuseStep 1479257 = 1109443) B1109443
theorem B4264541 : Blo 654306 4264541 := bstep (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) B1599203
theorem B1479347 : Blo 654306 1479347 := bstep (se 1 (by rfl) ⟨1109510, by rfl⟩ : syracuseStep 1479347 = 2219021) B2219021
theorem B1479383 : Blo 654306 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B57447139 : Blo 654306 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B1872733 : Blo 654306 1872733 := bstep (se 3 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 1872733 = 702275) B702275
theorem B1479563 : Blo 654306 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B1872791 : Blo 654306 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B1479617 : Blo 654306 1479617 := bstep (se 2 (by rfl) ⟨554856, by rfl⟩ : syracuseStep 1479617 = 1109713) B1109713
theorem B1053707 : Blo 654306 1053707 := bstep (se 1 (by rfl) ⟨790280, by rfl⟩ : syracuseStep 1053707 = 1580561) B1580561
theorem B4985873 : Blo 654306 4985873 := bstep (se 2 (by rfl) ⟨1869702, by rfl⟩ : syracuseStep 4985873 = 3739405) B3739405
theorem B1053785 : Blo 654306 1053785 := bstep (se 2 (by rfl) ⟨395169, by rfl⟩ : syracuseStep 1053785 = 790339) B790339
theorem B1479833 : Blo 654306 1479833 := bstep (se 2 (by rfl) ⟨554937, by rfl⟩ : syracuseStep 1479833 = 1109875) B1109875
theorem B1479923 : Blo 654306 1479923 := bstep (se 1 (by rfl) ⟨1109942, by rfl⟩ : syracuseStep 1479923 = 2219885) B2219885
theorem B1185047 : Blo 654306 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B1479959 : Blo 654306 1479959 := bstep (se 1 (by rfl) ⟨1109969, by rfl⟩ : syracuseStep 1479959 = 2219939) B2219939
theorem B5608835 : Blo 654306 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B1480139 : Blo 654306 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B1480193 : Blo 654306 1480193 := bstep (se 2 (by rfl) ⟨555072, by rfl⟩ : syracuseStep 1480193 = 1110145) B1110145
theorem B2496203 : Blo 654306 2496203 := bstep (se 1 (by rfl) ⟨1872152, by rfl⟩ : syracuseStep 2496203 = 3744305) B3744305
theorem B2496217 : Blo 654306 2496217 := bstep (se 2 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 2496217 = 1872163) B1872163
theorem B1480409 : Blo 654306 1480409 := bstep (se 2 (by rfl) ⟨555153, by rfl⟩ : syracuseStep 1480409 = 1110307) B1110307
theorem B1480499 : Blo 654306 1480499 := bstep (se 1 (by rfl) ⟨1110374, by rfl⟩ : syracuseStep 1480499 = 2220749) B2220749
theorem B1480535 : Blo 654306 1480535 := bstep (se 1 (by rfl) ⟨1110401, by rfl⟩ : syracuseStep 1480535 = 2220803) B2220803
theorem B1480715 : Blo 654306 1480715 := bstep (se 1 (by rfl) ⟨1110536, by rfl⟩ : syracuseStep 1480715 = 2221073) B2221073
theorem B1480769 : Blo 654306 1480769 := bstep (se 2 (by rfl) ⟨555288, by rfl⟩ : syracuseStep 1480769 = 1110577) B1110577
theorem B1874009 : Blo 654306 1874009 := bstep (se 2 (by rfl) ⟨702753, by rfl⟩ : syracuseStep 1874009 = 1405507) B1405507
theorem B1874123 : Blo 654306 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B1186049 : Blo 654306 1186049 := bstep (se 2 (by rfl) ⟨444768, by rfl⟩ : syracuseStep 1186049 = 889537) B889537
theorem B1480985 : Blo 654306 1480985 := bstep (se 2 (by rfl) ⟨555369, by rfl⟩ : syracuseStep 1480985 = 1110739) B1110739
theorem B1481075 : Blo 654306 1481075 := bstep (se 1 (by rfl) ⟨1110806, by rfl⟩ : syracuseStep 1481075 = 2221613) B2221613
theorem B1481111 : Blo 654306 1481111 := bstep (se 1 (by rfl) ⟨1110833, by rfl⟩ : syracuseStep 1481111 = 2221667) B2221667
theorem B5380613 : Blo 654306 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B2366027 : Blo 654306 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B4201091 : Blo 654306 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B2497175 : Blo 654306 2497175 := bstep (se 1 (by rfl) ⟨1872881, by rfl⟩ : syracuseStep 2497175 = 3745763) B3745763
theorem B4725539 : Blo 654306 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B7478081 : Blo 654306 7478081 := bstep (se 2 (by rfl) ⟨2804280, by rfl⟩ : syracuseStep 7478081 = 5608561) B5608561
theorem B3742595 : Blo 654306 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B3152857 : Blo 654306 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B8985973 : Blo 654306 8985973 := bstep (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) B842435
theorem B4726289 : Blo 654306 4726289 := bstep (se 2 (by rfl) ⟨1772358, by rfl⟩ : syracuseStep 4726289 = 3544717) B3544717
theorem B4496941 : Blo 654306 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B3317597 : Blo 654306 3317597 := bstep (se 3 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 3317597 = 1244099) B1244099
theorem B2498435 : Blo 654306 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B15998897 : Blo 654306 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B1679297 : Blo 654306 1679297 := bstep (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) B1259473
theorem B12754979 : Blo 654306 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B2990125 : Blo 654306 2990125 := bstep (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) B1121297
theorem B5677573 : Blo 654306 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B77537845 : Blo 654306 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B4989761 : Blo 654306 4989761 := bstep (se 2 (by rfl) ⟨1871160, by rfl⟩ : syracuseStep 4989761 = 3742321) B3742321
theorem B828235 : Blo 654306 828235 := bstep (se 1 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 828235 = 1242353) B1242353
theorem B2663243 : Blo 654306 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B1123159 : Blo 654306 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B2369027 : Blo 654306 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B1418839 : Blo 654306 1418839 := bstep (se 1 (by rfl) ⟨1064129, by rfl⟩ : syracuseStep 1418839 = 2128259) B2128259
theorem B8955485 : Blo 654306 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B829207 : Blo 654306 829207 := bstep (se 1 (by rfl) ⟨621905, by rfl⟩ : syracuseStep 829207 = 1243811) B1243811
theorem B5318435 : Blo 654306 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B3319703 : Blo 654306 3319703 := bstep (se 1 (by rfl) ⟨2489777, by rfl⟩ : syracuseStep 3319703 = 4979555) B4979555
theorem B5974337 : Blo 654306 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B698743 : Blo 654306 698743 := bstep (se 1 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 698743 = 1048115) B1048115
theorem B830027 : Blo 654306 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B4991705 : Blo 654306 4991705 := bstep (se 2 (by rfl) ⟨1871889, by rfl⟩ : syracuseStep 4991705 = 3743779) B3743779
theorem B2796353 : Blo 654306 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B699563 : Blo 654306 699563 := bstep (se 1 (by rfl) ⟨524672, by rfl⟩ : syracuseStep 699563 = 1049345) B1049345
theorem B830731 : Blo 654306 830731 := bstep (se 1 (by rfl) ⟨623048, by rfl⟩ : syracuseStep 830731 = 1246097) B1246097
theorem B2108747 : Blo 654306 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B830999 : Blo 654306 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B2666029 : Blo 654306 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2993885 : Blo 654306 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1421057 : Blo 654306 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B3747971 : Blo 654306 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B831703 : Blo 654306 831703 := bstep (se 1 (by rfl) ⟨623777, by rfl⟩ : syracuseStep 831703 = 1247555) B1247555
theorem B8401157 : Blo 654306 8401157 := bstep (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) B1575217
theorem B2797841 : Blo 654306 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B700759 : Blo 654306 700759 := bstep (se 1 (by rfl) ⟨525569, by rfl⟩ : syracuseStep 700759 = 1051139) B1051139
theorem B3551809 : Blo 654306 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B3748427 : Blo 654306 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B701579 : Blo 654306 701579 := bstep (se 1 (by rfl) ⟨526184, by rfl⟩ : syracuseStep 701579 = 1052369) B1052369
theorem B35042485 : Blo 654306 35042485 := bstep (se 5 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 35042485 = 3285233) B3285233
theorem B2798813 : Blo 654306 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B3323267 : Blo 654306 3323267 := bstep (se 1 (by rfl) ⟨2492450, by rfl⟩ : syracuseStep 3323267 = 4984901) B4984901
theorem B38417813 : Blo 654306 38417813 := bstep (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) B1800835
theorem B2242009 : Blo 654306 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B2209355 : Blo 654306 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B2242241 : Blo 654306 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B8435501 : Blo 654306 8435501 := bstep (se 3 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 8435501 = 3163313) B3163313
theorem B2209625 : Blo 654306 2209625 := bstep (se 2 (by rfl) ⟨828609, by rfl⟩ : syracuseStep 2209625 = 1657219) B1657219
theorem B4995107 : Blo 654306 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B932249 : Blo 654306 932249 := bstep (se 2 (by rfl) ⟨349593, by rfl⟩ : syracuseStep 932249 = 699187) B699187
theorem B702967 : Blo 654306 702967 := bstep (se 1 (by rfl) ⟨527225, by rfl⟩ : syracuseStep 702967 = 1054451) B1054451
theorem B2210327 : Blo 654306 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B7093109 : Blo 654306 7093109 := bstep (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) B664979
theorem B736267 : Blo 654306 736267 := bstep (se 1 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 736267 = 1104401) B1104401
theorem B3161105 : Blo 654306 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B932887 : Blo 654306 932887 := bstep (se 1 (by rfl) ⟨699665, by rfl⟩ : syracuseStep 932887 = 1399331) B1399331
theorem B2210867 : Blo 654306 2210867 := bstep (se 1 (by rfl) ⟨1658150, by rfl⟩ : syracuseStep 2210867 = 3316301) B3316301
theorem B736375 : Blo 654306 736375 := bstep (se 1 (by rfl) ⟨552281, by rfl⟩ : syracuseStep 736375 = 1104563) B1104563
theorem B736555 : Blo 654306 736555 := bstep (se 1 (by rfl) ⟨552416, by rfl⟩ : syracuseStep 736555 = 1104833) B1104833
theorem B2211137 : Blo 654306 2211137 := bstep (se 2 (by rfl) ⟨829176, by rfl⟩ : syracuseStep 2211137 = 1658353) B1658353
theorem B4734301 : Blo 654306 4734301 := bstep (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) B1775363
theorem B736663 : Blo 654306 736663 := bstep (se 1 (by rfl) ⟨552497, by rfl⟩ : syracuseStep 736663 = 1104995) B1104995
theorem B1326593 : Blo 654306 1326593 := bstep (se 2 (by rfl) ⟨497472, by rfl⟩ : syracuseStep 1326593 = 994945) B994945
theorem B12631565 : Blo 654306 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B736843 : Blo 654306 736843 := bstep (se 1 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 736843 = 1105265) B1105265
theorem B5619293 : Blo 654306 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B736951 : Blo 654306 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B2801411 : Blo 654306 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B1261337 : Blo 654306 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B933707 : Blo 654306 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B2211677 : Blo 654306 2211677 := bstep (se 3 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 2211677 = 829379) B829379
theorem B737131 : Blo 654306 737131 := bstep (se 1 (by rfl) ⟨552848, by rfl⟩ : syracuseStep 737131 = 1105697) B1105697
theorem B999319 : Blo 654306 999319 := bstep (se 1 (by rfl) ⟨749489, by rfl⟩ : syracuseStep 999319 = 1498979) B1498979
theorem B737239 : Blo 654306 737239 := bstep (se 1 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 737239 = 1105859) B1105859
theorem B2801753 : Blo 654306 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B737419 : Blo 654306 737419 := bstep (se 1 (by rfl) ⟨553064, by rfl⟩ : syracuseStep 737419 = 1106129) B1106129
theorem B1622209 : Blo 654306 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B737527 : Blo 654306 737527 := bstep (se 1 (by rfl) ⟨553145, by rfl⟩ : syracuseStep 737527 = 1106291) B1106291
theorem B1327435 : Blo 654306 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B5620043 : Blo 654306 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B737707 : Blo 654306 737707 := bstep (se 1 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 737707 = 1106561) B1106561
theorem B737815 : Blo 654306 737815 := bstep (se 1 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 737815 = 1106723) B1106723
theorem B163627573 : Blo 654306 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B2245195 : Blo 654306 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B11223683 : Blo 654306 11223683 := bstep (se 1 (by rfl) ⟨8417762, by rfl⟩ : syracuseStep 11223683 = 16835525) B16835525
theorem B737995 : Blo 654306 737995 := bstep (se 1 (by rfl) ⟨553496, by rfl⟩ : syracuseStep 737995 = 1106993) B1106993
theorem B934681 : Blo 654306 934681 := bstep (se 2 (by rfl) ⟨350505, by rfl⟩ : syracuseStep 934681 = 701011) B701011
theorem B738103 : Blo 654306 738103 := bstep (se 1 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 738103 = 1107155) B1107155
theorem B2999213 : Blo 654306 2999213 := bstep (se 3 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 2999213 = 1124705) B1124705
theorem B5686193 : Blo 654306 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B2212811 : Blo 654306 2212811 := bstep (se 1 (by rfl) ⟨1659608, by rfl⟩ : syracuseStep 2212811 = 3319217) B3319217
theorem B738283 : Blo 654306 738283 := bstep (se 1 (by rfl) ⟨553712, by rfl⟩ : syracuseStep 738283 = 1107425) B1107425
theorem B3326993 : Blo 654306 3326993 := bstep (se 2 (by rfl) ⟨1247622, by rfl⟩ : syracuseStep 3326993 = 2495245) B2495245
theorem B738391 : Blo 654306 738391 := bstep (se 1 (by rfl) ⟨553793, by rfl⟩ : syracuseStep 738391 = 1107587) B1107587
theorem B3327155 : Blo 654306 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B2213081 : Blo 654306 2213081 := bstep (se 2 (by rfl) ⟨829905, by rfl⟩ : syracuseStep 2213081 = 1659811) B1659811
theorem B1197299 : Blo 654306 1197299 := bstep (se 1 (by rfl) ⟨897974, by rfl⟩ : syracuseStep 1197299 = 1795949) B1795949
theorem B738571 : Blo 654306 738571 := bstep (se 1 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 738571 = 1107857) B1107857
theorem B1852723 : Blo 654306 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B738679 : Blo 654306 738679 := bstep (se 1 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 738679 = 1108019) B1108019
theorem B5064067 : Blo 654306 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B9586097 : Blo 654306 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B738859 : Blo 654306 738859 := bstep (se 1 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 738859 = 1108289) B1108289
theorem B1656409 : Blo 654306 1656409 := bstep (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) B1242307
theorem B1328791 : Blo 654306 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B738967 : Blo 654306 738967 := bstep (se 1 (by rfl) ⟨554225, by rfl⟩ : syracuseStep 738967 = 1108451) B1108451
theorem B739147 : Blo 654306 739147 := bstep (se 1 (by rfl) ⟨554360, by rfl⟩ : syracuseStep 739147 = 1108721) B1108721
theorem B2213783 : Blo 654306 2213783 := bstep (se 1 (by rfl) ⟨1660337, by rfl⟩ : syracuseStep 2213783 = 3320675) B3320675
theorem B935831 : Blo 654306 935831 := bstep (se 1 (by rfl) ⟨701873, by rfl⟩ : syracuseStep 935831 = 1403747) B1403747
theorem B5621683 : Blo 654306 5621683 := bstep (se 1 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 5621683 = 8432525) B8432525
theorem B739255 : Blo 654306 739255 := bstep (se 1 (by rfl) ⟨554441, by rfl⟩ : syracuseStep 739255 = 1108883) B1108883
theorem B6932441 : Blo 654306 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B739435 : Blo 654306 739435 := bstep (se 1 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 739435 = 1109153) B1109153
theorem B936139 : Blo 654306 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B739543 : Blo 654306 739543 := bstep (se 1 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 739543 = 1109315) B1109315
theorem B739723 : Blo 654306 739723 := bstep (se 1 (by rfl) ⟨554792, by rfl⟩ : syracuseStep 739723 = 1109585) B1109585
theorem B2214323 : Blo 654306 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B1493441 : Blo 654306 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B739831 : Blo 654306 739831 := bstep (se 1 (by rfl) ⟨554873, by rfl⟩ : syracuseStep 739831 = 1109747) B1109747
theorem B740011 : Blo 654306 740011 := bstep (se 1 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 740011 = 1110017) B1110017
theorem B1657523 : Blo 654306 1657523 := bstep (se 1 (by rfl) ⟨1243142, by rfl⟩ : syracuseStep 1657523 = 2486285) B2486285
theorem B2214593 : Blo 654306 2214593 := bstep (se 2 (by rfl) ⟨830472, by rfl⟩ : syracuseStep 2214593 = 1660945) B1660945
theorem B740119 : Blo 654306 740119 := bstep (se 1 (by rfl) ⟨555089, by rfl⟩ : syracuseStep 740119 = 1110179) B1110179
theorem B740299 : Blo 654306 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B1657817 : Blo 654306 1657817 := bstep (se 2 (by rfl) ⟨621681, by rfl⟩ : syracuseStep 1657817 = 1243363) B1243363
theorem B740407 : Blo 654306 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B3329099 : Blo 654306 3329099 := bstep (se 1 (by rfl) ⟨2496824, by rfl⟩ : syracuseStep 3329099 = 4993649) B4993649
theorem B937175 : Blo 654306 937175 := bstep (se 1 (by rfl) ⟨702881, by rfl⟩ : syracuseStep 937175 = 1405763) B1405763
theorem B2215133 : Blo 654306 2215133 := bstep (se 3 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 2215133 = 830675) B830675
theorem B740587 : Blo 654306 740587 := bstep (se 1 (by rfl) ⟨555440, by rfl⟩ : syracuseStep 740587 = 1110881) B1110881
theorem B2805137 : Blo 654306 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B4804019 : Blo 654306 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B4738661 : Blo 654306 4738661 := bstep (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) B888499
theorem B7491203 : Blo 654306 7491203 := bstep (se 1 (by rfl) ⟨5618402, by rfl⟩ : syracuseStep 7491203 = 11236805) B11236805
theorem B1330867 : Blo 654306 1330867 := bstep (se 1 (by rfl) ⟨998150, by rfl⟩ : syracuseStep 1330867 = 1996301) B1996301
theorem B13455395 : Blo 654306 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B4739147 : Blo 654306 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B2805853 : Blo 654306 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B1331329 : Blo 654306 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B1495255 : Blo 654306 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B2216267 : Blo 654306 2216267 := bstep (se 1 (by rfl) ⟨1662200, by rfl⟩ : syracuseStep 2216267 = 3324401) B3324401
theorem B4215341 : Blo 654306 4215341 := bstep (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) B1580753
theorem B1659467 : Blo 654306 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B2216537 : Blo 654306 2216537 := bstep (se 2 (by rfl) ⟨831201, by rfl⟩ : syracuseStep 2216537 = 1662403) B1662403
theorem B3330881 : Blo 654306 3330881 := bstep (se 2 (by rfl) ⟨1249080, by rfl⟩ : syracuseStep 3330881 = 2498161) B2498161
theorem B8508509 : Blo 654306 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B2217239 : Blo 654306 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B1725761 : Blo 654306 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B26891747 : Blo 654306 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1660439 : Blo 654306 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B710251 : Blo 654306 710251 := bstep (se 1 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 710251 = 1065377) B1065377
theorem B2217779 : Blo 654306 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B1333079 : Blo 654306 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B2840465 : Blo 654306 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B5593049 : Blo 654306 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B2250775 : Blo 654306 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B1398809 : Blo 654306 1398809 := bstep (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) B1049107
theorem B2218049 : Blo 654306 2218049 := bstep (se 2 (by rfl) ⟨831768, by rfl⟩ : syracuseStep 2218049 = 1663537) B1663537
theorem B1661107 : Blo 654306 1661107 := bstep (se 1 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 1661107 = 2491661) B2491661
theorem B1104151 : Blo 654306 1104151 := bstep (se 1 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 1104151 = 1656227) B1656227
theorem B1661249 : Blo 654306 1661249 := bstep (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) B1245937
theorem B842071 : Blo 654306 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B2251097 : Blo 654306 2251097 := bstep (se 2 (by rfl) ⟨844161, by rfl⟩ : syracuseStep 2251097 = 1688323) B1688323
theorem B2218589 : Blo 654306 2218589 := bstep (se 3 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 2218589 = 831971) B831971
theorem B1399475 : Blo 654306 1399475 := bstep (se 1 (by rfl) ⟨1049606, by rfl⟩ : syracuseStep 1399475 = 2099213) B2099213
theorem B711467 : Blo 654306 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B1104779 : Blo 654306 1104779 := bstep (se 1 (by rfl) ⟨828584, by rfl⟩ : syracuseStep 1104779 = 1657169) B1657169
theorem B1104907 : Blo 654306 1104907 := bstep (se 1 (by rfl) ⟨828680, by rfl⟩ : syracuseStep 1104907 = 1657361) B1657361
theorem B5037157 : Blo 654306 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B1105049 : Blo 654306 1105049 := bstep (se 2 (by rfl) ⟨414393, by rfl⟩ : syracuseStep 1105049 = 828787) B828787
theorem B1105177 : Blo 654306 1105177 := bstep (se 2 (by rfl) ⟨414441, by rfl⟩ : syracuseStep 1105177 = 828883) B828883
theorem B1498547 : Blo 654306 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B3726809 : Blo 654306 3726809 := bstep (se 2 (by rfl) ⟨1397553, by rfl⟩ : syracuseStep 3726809 = 2795107) B2795107
theorem B1662515 : Blo 654306 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B5987915 : Blo 654306 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B2809475 : Blo 654306 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B2219723 : Blo 654306 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B1105751 : Blo 654306 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B12115829 : Blo 654306 12115829 := bstep (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) B1135859
theorem B9461681 : Blo 654306 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B1105879 : Blo 654306 1105879 := bstep (se 1 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 1105879 = 1658819) B1658819
theorem B2219993 : Blo 654306 2219993 := bstep (se 2 (by rfl) ⟨832497, by rfl⟩ : syracuseStep 2219993 = 1664995) B1664995
theorem B1663051 : Blo 654306 1663051 := bstep (se 1 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 1663051 = 2494577) B2494577
theorem B1400971 : Blo 654306 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B1663193 : Blo 654306 1663193 := bstep (se 2 (by rfl) ⟨623697, by rfl⟩ : syracuseStep 1663193 = 1247395) B1247395
theorem B26894861 : Blo 654306 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B7103011 : Blo 654306 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B5595713 : Blo 654306 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B1106507 : Blo 654306 1106507 := bstep (se 1 (by rfl) ⟨829880, by rfl⟩ : syracuseStep 1106507 = 1659761) B1659761
theorem B2220695 : Blo 654306 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B1991347 : Blo 654306 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B5333683 : Blo 654306 5333683 := bstep (se 1 (by rfl) ⟨4000262, by rfl⟩ : syracuseStep 5333683 = 8000525) B8000525
theorem B1106635 : Blo 654306 1106635 := bstep (se 1 (by rfl) ⟨829976, by rfl⟩ : syracuseStep 1106635 = 1659953) B1659953
theorem B10969901 : Blo 654306 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B1106777 : Blo 654306 1106777 := bstep (se 2 (by rfl) ⟨415041, by rfl⟩ : syracuseStep 1106777 = 830083) B830083
theorem B1106905 : Blo 654306 1106905 := bstep (se 2 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 1106905 = 830179) B830179
theorem B1664023 : Blo 654306 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B2221235 : Blo 654306 2221235 := bstep (se 1 (by rfl) ⟨1665926, by rfl⟩ : syracuseStep 2221235 = 3331853) B3331853
theorem B1402201 : Blo 654306 1402201 := bstep (se 2 (by rfl) ⟨525825, by rfl⟩ : syracuseStep 1402201 = 1051651) B1051651
theorem B2811287 : Blo 654306 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B2221505 : Blo 654306 2221505 := bstep (se 2 (by rfl) ⟨833064, by rfl⟩ : syracuseStep 2221505 = 1666129) B1666129
theorem B1664459 : Blo 654306 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B1107479 : Blo 654306 1107479 := bstep (se 1 (by rfl) ⟨830609, by rfl⟩ : syracuseStep 1107479 = 1661219) B1661219
theorem B1107607 : Blo 654306 1107607 := bstep (se 1 (by rfl) ⟨830705, by rfl⟩ : syracuseStep 1107607 = 1661411) B1661411
theorem B1664833 : Blo 654306 1664833 := bstep (se 2 (by rfl) ⟨624312, by rfl⟩ : syracuseStep 1664833 = 1248625) B1248625
theorem B3729473 : Blo 654306 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B1108235 : Blo 654306 1108235 := bstep (se 1 (by rfl) ⟨831176, by rfl⟩ : syracuseStep 1108235 = 1662353) B1662353
theorem B60615029 : Blo 654306 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B1108363 : Blo 654306 1108363 := bstep (se 1 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 1108363 = 1662545) B1662545
theorem B1665431 : Blo 654306 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B1108505 : Blo 654306 1108505 := bstep (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) B831379
theorem B3041837 : Blo 654306 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B1108633 : Blo 654306 1108633 := bstep (se 2 (by rfl) ⟨415737, by rfl⟩ : syracuseStep 1108633 = 831475) B831475
theorem B2485313 : Blo 654306 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B15199301 : Blo 654306 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1666241 : Blo 654306 1666241 := bstep (se 2 (by rfl) ⟨624840, by rfl⟩ : syracuseStep 1666241 = 1249681) B1249681
theorem B1109207 : Blo 654306 1109207 := bstep (se 1 (by rfl) ⟨831905, by rfl⟩ : syracuseStep 1109207 = 1663811) B1663811
theorem B1109335 : Blo 654306 1109335 := bstep (se 1 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 1109335 = 1664003) B1664003
theorem B7466417 : Blo 654306 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B1797569 : Blo 654306 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B5992141 : Blo 654306 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B1109963 : Blo 654306 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B1110091 : Blo 654306 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B1863769 : Blo 654306 1863769 := bstep (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) B1397827
theorem B1110233 : Blo 654306 1110233 := bstep (se 2 (by rfl) ⟨416337, by rfl⟩ : syracuseStep 1110233 = 832675) B832675
theorem B1110361 : Blo 654306 1110361 := bstep (se 2 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 1110361 = 832771) B832771
theorem B1405387 : Blo 654306 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B2486801 : Blo 654306 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1405849 : Blo 654306 1405849 := bstep (se 2 (by rfl) ⟨527193, by rfl⟩ : syracuseStep 1405849 = 1054387) B1054387
theorem B750551 : Blo 654306 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B2487257 : Blo 654306 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B2487469 : Blo 654306 2487469 := bstep (se 3 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 2487469 = 932801) B932801
theorem B1242391 : Blo 654306 1242391 := bstep (se 1 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 1242391 = 1863587) B1863587
theorem B4978097 : Blo 654306 4978097 := bstep (se 2 (by rfl) ⟨1866786, by rfl⟩ : syracuseStep 4978097 = 3733573) B3733573
theorem B2487773 : Blo 654306 2487773 := bstep (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) B932915
theorem B1242611 : Blo 654306 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B1242839 : Blo 654306 1242839 := bstep (se 1 (by rfl) ⟨932129, by rfl⟩ : syracuseStep 1242839 = 1864259) B1864259
theorem B1472345 : Blo 654306 1472345 := bstep (se 2 (by rfl) ⟨552129, by rfl⟩ : syracuseStep 1472345 = 1104259) B1104259
theorem B4978583 : Blo 654306 4978583 := bstep (se 1 (by rfl) ⟨3733937, by rfl⟩ : syracuseStep 4978583 = 7467875) B7467875
theorem B1472435 : Blo 654306 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B1472471 : Blo 654306 1472471 := bstep (se 1 (by rfl) ⟨1104353, by rfl⟩ : syracuseStep 1472471 = 2208707) B2208707
theorem B1243097 : Blo 654306 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B1865693 : Blo 654306 1865693 := bstep (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) B699635
theorem B8419403 : Blo 654306 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B6813827 : Blo 654306 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B1472651 : Blo 654306 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B1472705 : Blo 654306 1472705 := bstep (se 2 (by rfl) ⟨552264, by rfl⟩ : syracuseStep 1472705 = 1104529) B1104529
theorem B1243507 : Blo 654306 1243507 := bstep (se 1 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 1243507 = 1865261) B1865261
theorem B1472921 : Blo 654306 1472921 := bstep (se 2 (by rfl) ⟨552345, by rfl⟩ : syracuseStep 1472921 = 1104691) B1104691
theorem B1473011 : Blo 654306 1473011 := bstep (se 1 (by rfl) ⟨1104758, by rfl⟩ : syracuseStep 1473011 = 2209517) B2209517
theorem B5601797 : Blo 654306 5601797 := bstep (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) B1050337
theorem B981515 : Blo 654306 981515 := bstep (se 1 (by rfl) ⟨736136, by rfl⟩ : syracuseStep 981515 = 1472273) B1472273
theorem B981527 : Blo 654306 981527 := bstep (se 1 (by rfl) ⟨736145, by rfl⟩ : syracuseStep 981527 = 1472291) B1472291
theorem B1473047 : Blo 654306 1473047 := bstep (se 1 (by rfl) ⟨1104785, by rfl⟩ : syracuseStep 1473047 = 2209571) B2209571
theorem B981593 : Blo 654306 981593 := bstep (se 2 (by rfl) ⟨368097, by rfl⟩ : syracuseStep 981593 = 736195) B736195
theorem B981707 : Blo 654306 981707 := bstep (se 1 (by rfl) ⟨736280, by rfl⟩ : syracuseStep 981707 = 1472561) B1472561
theorem B1473227 : Blo 654306 1473227 := bstep (se 1 (by rfl) ⟨1104920, by rfl⟩ : syracuseStep 1473227 = 2209841) B2209841
theorem B981719 : Blo 654306 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B1473281 : Blo 654306 1473281 := bstep (se 2 (by rfl) ⟨552480, by rfl⟩ : syracuseStep 1473281 = 1104961) B1104961
theorem B981785 : Blo 654306 981785 := bstep (se 2 (by rfl) ⟨368169, by rfl⟩ : syracuseStep 981785 = 736339) B736339
theorem B1243993 : Blo 654306 1243993 := bstep (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) B932995
theorem B981899 : Blo 654306 981899 := bstep (se 1 (by rfl) ⟨736424, by rfl⟩ : syracuseStep 981899 = 1472849) B1472849
theorem B981911 : Blo 654306 981911 := bstep (se 1 (by rfl) ⟨736433, by rfl⟩ : syracuseStep 981911 = 1472867) B1472867
theorem B981977 : Blo 654306 981977 := bstep (se 2 (by rfl) ⟨368241, by rfl⟩ : syracuseStep 981977 = 736483) B736483
theorem B1473497 : Blo 654306 1473497 := bstep (se 2 (by rfl) ⟨552561, by rfl⟩ : syracuseStep 1473497 = 1105123) B1105123
theorem B654315 : Blo 654306 654315 := bstep (se 1 (by rfl) ⟨490736, by rfl⟩ : syracuseStep 654315 = 981473) B981473
theorem B654327 : Blo 654306 654327 := bstep (se 1 (by rfl) ⟨490745, by rfl⟩ : syracuseStep 654327 = 981491) B981491
theorem B654347 : Blo 654306 654347 := bstep (se 1 (by rfl) ⟨490760, by rfl⟩ : syracuseStep 654347 = 981521) B981521
theorem B654359 : Blo 654306 654359 := bstep (se 1 (by rfl) ⟨490769, by rfl⟩ : syracuseStep 654359 = 981539) B981539
theorem B654379 : Blo 654306 654379 := bstep (se 1 (by rfl) ⟨490784, by rfl⟩ : syracuseStep 654379 = 981569) B981569
theorem B1473587 : Blo 654306 1473587 := bstep (se 1 (by rfl) ⟨1105190, by rfl⟩ : syracuseStep 1473587 = 2210381) B2210381
theorem B654391 : Blo 654306 654391 := bstep (se 1 (by rfl) ⟨490793, by rfl⟩ : syracuseStep 654391 = 981587) B981587
theorem B654411 : Blo 654306 654411 := bstep (se 1 (by rfl) ⟨490808, by rfl⟩ : syracuseStep 654411 = 981617) B981617
theorem B982091 : Blo 654306 982091 := bstep (se 1 (by rfl) ⟨736568, by rfl⟩ : syracuseStep 982091 = 1473137) B1473137
theorem B654423 : Blo 654306 654423 := bstep (se 1 (by rfl) ⟨490817, by rfl⟩ : syracuseStep 654423 = 981635) B981635
theorem B982103 : Blo 654306 982103 := bstep (se 1 (by rfl) ⟨736577, by rfl⟩ : syracuseStep 982103 = 1473155) B1473155
theorem B1473623 : Blo 654306 1473623 := bstep (se 1 (by rfl) ⟨1105217, by rfl⟩ : syracuseStep 1473623 = 2210435) B2210435
theorem B654443 : Blo 654306 654443 := bstep (se 1 (by rfl) ⟨490832, by rfl⟩ : syracuseStep 654443 = 981665) B981665
theorem B654455 : Blo 654306 654455 := bstep (se 1 (by rfl) ⟨490841, by rfl⟩ : syracuseStep 654455 = 981683) B981683
theorem B654475 : Blo 654306 654475 := bstep (se 1 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 654475 = 981713) B981713
theorem B654487 : Blo 654306 654487 := bstep (se 1 (by rfl) ⟨490865, by rfl⟩ : syracuseStep 654487 = 981731) B981731
theorem B982169 : Blo 654306 982169 := bstep (se 2 (by rfl) ⟨368313, by rfl⟩ : syracuseStep 982169 = 736627) B736627
theorem B654507 : Blo 654306 654507 := bstep (se 1 (by rfl) ⟨490880, by rfl⟩ : syracuseStep 654507 = 981761) B981761
theorem B654519 : Blo 654306 654519 := bstep (se 1 (by rfl) ⟨490889, by rfl⟩ : syracuseStep 654519 = 981779) B981779
theorem B654539 : Blo 654306 654539 := bstep (se 1 (by rfl) ⟨490904, by rfl⟩ : syracuseStep 654539 = 981809) B981809
theorem B654551 : Blo 654306 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B654571 : Blo 654306 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B654583 : Blo 654306 654583 := bstep (se 1 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 654583 = 981875) B981875
theorem B654603 : Blo 654306 654603 := bstep (se 1 (by rfl) ⟨490952, by rfl⟩ : syracuseStep 654603 = 981905) B981905
theorem B982283 : Blo 654306 982283 := bstep (se 1 (by rfl) ⟨736712, by rfl⟩ : syracuseStep 982283 = 1473425) B1473425
theorem B1473803 : Blo 654306 1473803 := bstep (se 1 (by rfl) ⟨1105352, by rfl⟩ : syracuseStep 1473803 = 2210705) B2210705
theorem B654615 : Blo 654306 654615 := bstep (se 1 (by rfl) ⟨490961, by rfl⟩ : syracuseStep 654615 = 981923) B981923
theorem B982295 : Blo 654306 982295 := bstep (se 1 (by rfl) ⟨736721, by rfl⟩ : syracuseStep 982295 = 1473443) B1473443
theorem B654635 : Blo 654306 654635 := bstep (se 1 (by rfl) ⟨490976, by rfl⟩ : syracuseStep 654635 = 981953) B981953
theorem B654647 : Blo 654306 654647 := bstep (se 1 (by rfl) ⟨490985, by rfl⟩ : syracuseStep 654647 = 981971) B981971
theorem B3374401 : Blo 654306 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B1473857 : Blo 654306 1473857 := bstep (se 2 (by rfl) ⟨552696, by rfl⟩ : syracuseStep 1473857 = 1105393) B1105393
theorem B3734849 : Blo 654306 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B654667 : Blo 654306 654667 := bstep (se 1 (by rfl) ⟨491000, by rfl⟩ : syracuseStep 654667 = 982001) B982001
theorem B654679 : Blo 654306 654679 := bstep (se 1 (by rfl) ⟨491009, by rfl⟩ : syracuseStep 654679 = 982019) B982019
theorem B982361 : Blo 654306 982361 := bstep (se 2 (by rfl) ⟨368385, by rfl⟩ : syracuseStep 982361 = 736771) B736771
theorem B4717925 : Blo 654306 4717925 := bstep (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) B884611
theorem B654699 : Blo 654306 654699 := bstep (se 1 (by rfl) ⟨491024, by rfl⟩ : syracuseStep 654699 = 982049) B982049
theorem B654711 : Blo 654306 654711 := bstep (se 1 (by rfl) ⟨491033, by rfl⟩ : syracuseStep 654711 = 982067) B982067
theorem B654731 : Blo 654306 654731 := bstep (se 1 (by rfl) ⟨491048, by rfl⟩ : syracuseStep 654731 = 982097) B982097
theorem B1244555 : Blo 654306 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B654743 : Blo 654306 654743 := bstep (se 1 (by rfl) ⟨491057, by rfl⟩ : syracuseStep 654743 = 982115) B982115
theorem B654763 : Blo 654306 654763 := bstep (se 1 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 654763 = 982145) B982145
theorem B654775 : Blo 654306 654775 := bstep (se 1 (by rfl) ⟨491081, by rfl⟩ : syracuseStep 654775 = 982163) B982163
theorem B1998283 : Blo 654306 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B2358731 : Blo 654306 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B654795 : Blo 654306 654795 := bstep (se 1 (by rfl) ⟨491096, by rfl⟩ : syracuseStep 654795 = 982193) B982193
theorem B982475 : Blo 654306 982475 := bstep (se 1 (by rfl) ⟨736856, by rfl⟩ : syracuseStep 982475 = 1473713) B1473713
theorem B654807 : Blo 654306 654807 := bstep (se 1 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 654807 = 982211) B982211
theorem B982487 : Blo 654306 982487 := bstep (se 1 (by rfl) ⟨736865, by rfl⟩ : syracuseStep 982487 = 1473731) B1473731
theorem B654827 : Blo 654306 654827 := bstep (se 1 (by rfl) ⟨491120, by rfl⟩ : syracuseStep 654827 = 982241) B982241
theorem B654839 : Blo 654306 654839 := bstep (se 1 (by rfl) ⟨491129, by rfl⟩ : syracuseStep 654839 = 982259) B982259
theorem B654859 : Blo 654306 654859 := bstep (se 1 (by rfl) ⟨491144, by rfl⟩ : syracuseStep 654859 = 982289) B982289
theorem B654871 : Blo 654306 654871 := bstep (se 1 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 654871 = 982307) B982307
theorem B982553 : Blo 654306 982553 := bstep (se 2 (by rfl) ⟨368457, by rfl⟩ : syracuseStep 982553 = 736915) B736915
theorem B1474073 : Blo 654306 1474073 := bstep (se 2 (by rfl) ⟨552777, by rfl⟩ : syracuseStep 1474073 = 1105555) B1105555
theorem B654891 : Blo 654306 654891 := bstep (se 1 (by rfl) ⟨491168, by rfl⟩ : syracuseStep 654891 = 982337) B982337
theorem B654903 : Blo 654306 654903 := bstep (se 1 (by rfl) ⟨491177, by rfl⟩ : syracuseStep 654903 = 982355) B982355
theorem B1244737 : Blo 654306 1244737 := bstep (se 2 (by rfl) ⟨466776, by rfl⟩ : syracuseStep 1244737 = 933553) B933553
theorem B654923 : Blo 654306 654923 := bstep (se 1 (by rfl) ⟨491192, by rfl⟩ : syracuseStep 654923 = 982385) B982385
theorem B654935 : Blo 654306 654935 := bstep (se 1 (by rfl) ⟨491201, by rfl⟩ : syracuseStep 654935 = 982403) B982403
theorem B2358877 : Blo 654306 2358877 := bstep (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) B884579
theorem B654955 : Blo 654306 654955 := bstep (se 1 (by rfl) ⟨491216, by rfl⟩ : syracuseStep 654955 = 982433) B982433
theorem B1474163 : Blo 654306 1474163 := bstep (se 1 (by rfl) ⟨1105622, by rfl⟩ : syracuseStep 1474163 = 2211245) B2211245
theorem B654967 : Blo 654306 654967 := bstep (se 1 (by rfl) ⟨491225, by rfl⟩ : syracuseStep 654967 = 982451) B982451
theorem B654987 : Blo 654306 654987 := bstep (se 1 (by rfl) ⟨491240, by rfl⟩ : syracuseStep 654987 = 982481) B982481
theorem B982667 : Blo 654306 982667 := bstep (se 1 (by rfl) ⟨737000, by rfl⟩ : syracuseStep 982667 = 1474001) B1474001
theorem B786071 : Blo 654306 786071 := bstep (se 1 (by rfl) ⟨589553, by rfl⟩ : syracuseStep 786071 = 1179107) B1179107
theorem B5308055 : Blo 654306 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B654999 : Blo 654306 654999 := bstep (se 1 (by rfl) ⟨491249, by rfl⟩ : syracuseStep 654999 = 982499) B982499
theorem B982679 : Blo 654306 982679 := bstep (se 1 (by rfl) ⟨737009, by rfl⟩ : syracuseStep 982679 = 1474019) B1474019
theorem B1474199 : Blo 654306 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B655019 : Blo 654306 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B655031 : Blo 654306 655031 := bstep (se 1 (by rfl) ⟨491273, by rfl⟩ : syracuseStep 655031 = 982547) B982547
theorem B655051 : Blo 654306 655051 := bstep (se 1 (by rfl) ⟨491288, by rfl⟩ : syracuseStep 655051 = 982577) B982577
theorem B40402637 : Blo 654306 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B655063 : Blo 654306 655063 := bstep (se 1 (by rfl) ⟨491297, by rfl⟩ : syracuseStep 655063 = 982595) B982595
theorem B982745 : Blo 654306 982745 := bstep (se 2 (by rfl) ⟨368529, by rfl⟩ : syracuseStep 982745 = 737059) B737059
theorem B655083 : Blo 654306 655083 := bstep (se 1 (by rfl) ⟨491312, by rfl⟩ : syracuseStep 655083 = 982625) B982625
theorem B655095 : Blo 654306 655095 := bstep (se 1 (by rfl) ⟨491321, by rfl⟩ : syracuseStep 655095 = 982643) B982643
theorem B655115 : Blo 654306 655115 := bstep (se 1 (by rfl) ⟨491336, by rfl⟩ : syracuseStep 655115 = 982673) B982673
theorem B884503 : Blo 654306 884503 := bstep (se 1 (by rfl) ⟨663377, by rfl⟩ : syracuseStep 884503 = 1326755) B1326755
theorem B655127 : Blo 654306 655127 := bstep (se 1 (by rfl) ⟨491345, by rfl⟩ : syracuseStep 655127 = 982691) B982691
theorem B655147 : Blo 654306 655147 := bstep (se 1 (by rfl) ⟨491360, by rfl⟩ : syracuseStep 655147 = 982721) B982721
theorem B655159 : Blo 654306 655159 := bstep (se 1 (by rfl) ⟨491369, by rfl⟩ : syracuseStep 655159 = 982739) B982739
theorem B655179 : Blo 654306 655179 := bstep (se 1 (by rfl) ⟨491384, by rfl⟩ : syracuseStep 655179 = 982769) B982769
theorem B982859 : Blo 654306 982859 := bstep (se 1 (by rfl) ⟨737144, by rfl⟩ : syracuseStep 982859 = 1474289) B1474289
theorem B1474379 : Blo 654306 1474379 := bstep (se 1 (by rfl) ⟨1105784, by rfl⟩ : syracuseStep 1474379 = 2211569) B2211569
theorem B655191 : Blo 654306 655191 := bstep (se 1 (by rfl) ⟨491393, by rfl⟩ : syracuseStep 655191 = 982787) B982787
theorem B982871 : Blo 654306 982871 := bstep (se 1 (by rfl) ⟨737153, by rfl⟩ : syracuseStep 982871 = 1474307) B1474307
theorem B655211 : Blo 654306 655211 := bstep (se 1 (by rfl) ⟨491408, by rfl⟩ : syracuseStep 655211 = 982817) B982817
theorem B655223 : Blo 654306 655223 := bstep (se 1 (by rfl) ⟨491417, by rfl⟩ : syracuseStep 655223 = 982835) B982835
theorem B1474433 : Blo 654306 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B655243 : Blo 654306 655243 := bstep (se 1 (by rfl) ⟨491432, by rfl⟩ : syracuseStep 655243 = 982865) B982865
theorem B655255 : Blo 654306 655255 := bstep (se 1 (by rfl) ⟨491441, by rfl⟩ : syracuseStep 655255 = 982883) B982883
theorem B982937 : Blo 654306 982937 := bstep (se 2 (by rfl) ⟨368601, by rfl⟩ : syracuseStep 982937 = 737203) B737203
theorem B655275 : Blo 654306 655275 := bstep (se 1 (by rfl) ⟨491456, by rfl⟩ : syracuseStep 655275 = 982913) B982913
theorem B40468403 : Blo 654306 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B1572787 : Blo 654306 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B655287 : Blo 654306 655287 := bstep (se 1 (by rfl) ⟨491465, by rfl⟩ : syracuseStep 655287 = 982931) B982931
theorem B655307 : Blo 654306 655307 := bstep (se 1 (by rfl) ⟨491480, by rfl⟩ : syracuseStep 655307 = 982961) B982961
theorem B655319 : Blo 654306 655319 := bstep (se 1 (by rfl) ⟨491489, by rfl⟩ : syracuseStep 655319 = 982979) B982979
theorem B655339 : Blo 654306 655339 := bstep (se 1 (by rfl) ⟨491504, by rfl⟩ : syracuseStep 655339 = 983009) B983009
theorem B655351 : Blo 654306 655351 := bstep (se 1 (by rfl) ⟨491513, by rfl⟩ : syracuseStep 655351 = 983027) B983027
theorem B655367 : Blo 654306 655367 := bstep (se 1 (by rfl) ⟨491525, by rfl⟩ : syracuseStep 655367 = 983051) B983051
theorem B655375 : Blo 654306 655375 := bstep (se 1 (by rfl) ⟨491531, by rfl⟩ : syracuseStep 655375 = 983063) B983063
theorem B983099 : Blo 654306 983099 := bstep (se 1 (by rfl) ⟨737324, by rfl⟩ : syracuseStep 983099 = 1474649) B1474649
theorem B655419 : Blo 654306 655419 := bstep (se 1 (by rfl) ⟨491564, by rfl⟩ : syracuseStep 655419 = 983129) B983129
theorem B1867835 : Blo 654306 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B983159 : Blo 654306 983159 := bstep (se 1 (by rfl) ⟨737369, by rfl⟩ : syracuseStep 983159 = 1474739) B1474739
theorem B655495 : Blo 654306 655495 := bstep (se 1 (by rfl) ⟨491621, by rfl⟩ : syracuseStep 655495 = 983243) B983243
theorem B983183 : Blo 654306 983183 := bstep (se 1 (by rfl) ⟨737387, by rfl⟩ : syracuseStep 983183 = 1474775) B1474775
theorem B655503 : Blo 654306 655503 := bstep (se 1 (by rfl) ⟨491627, by rfl⟩ : syracuseStep 655503 = 983255) B983255
theorem B983225 : Blo 654306 983225 := bstep (se 2 (by rfl) ⟨368709, by rfl⟩ : syracuseStep 983225 = 737419) B737419
theorem B1867961 : Blo 654306 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B655547 : Blo 654306 655547 := bstep (se 1 (by rfl) ⟨491660, by rfl⟩ : syracuseStep 655547 = 983321) B983321
theorem B2162945 : Blo 654306 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B983303 : Blo 654306 983303 := bstep (se 1 (by rfl) ⟨737477, by rfl⟩ : syracuseStep 983303 = 1474955) B1474955
theorem B655623 : Blo 654306 655623 := bstep (se 1 (by rfl) ⟨491717, by rfl⟩ : syracuseStep 655623 = 983435) B983435
theorem B655631 : Blo 654306 655631 := bstep (se 1 (by rfl) ⟨491723, by rfl⟩ : syracuseStep 655631 = 983447) B983447
theorem B983339 : Blo 654306 983339 := bstep (se 1 (by rfl) ⟨737504, by rfl⟩ : syracuseStep 983339 = 1475009) B1475009
theorem B655675 : Blo 654306 655675 := bstep (se 1 (by rfl) ⟨491756, by rfl⟩ : syracuseStep 655675 = 983513) B983513
theorem B983369 : Blo 654306 983369 := bstep (se 2 (by rfl) ⟨368763, by rfl⟩ : syracuseStep 983369 = 737527) B737527
theorem B655751 : Blo 654306 655751 := bstep (se 1 (by rfl) ⟨491813, by rfl⟩ : syracuseStep 655751 = 983627) B983627
theorem B655759 : Blo 654306 655759 := bstep (se 1 (by rfl) ⟨491819, by rfl⟩ : syracuseStep 655759 = 983639) B983639
theorem B983483 : Blo 654306 983483 := bstep (se 1 (by rfl) ⟨737612, by rfl⟩ : syracuseStep 983483 = 1475225) B1475225
theorem B655803 : Blo 654306 655803 := bstep (se 1 (by rfl) ⟨491852, by rfl⟩ : syracuseStep 655803 = 983705) B983705
theorem B983543 : Blo 654306 983543 := bstep (se 1 (by rfl) ⟨737657, by rfl⟩ : syracuseStep 983543 = 1475315) B1475315
theorem B655879 : Blo 654306 655879 := bstep (se 1 (by rfl) ⟨491909, by rfl⟩ : syracuseStep 655879 = 983819) B983819
theorem B983567 : Blo 654306 983567 := bstep (se 1 (by rfl) ⟨737675, by rfl⟩ : syracuseStep 983567 = 1475351) B1475351
theorem B655887 : Blo 654306 655887 := bstep (se 1 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 655887 = 983831) B983831
theorem B983609 : Blo 654306 983609 := bstep (se 2 (by rfl) ⟨368853, by rfl⟩ : syracuseStep 983609 = 737707) B737707
theorem B655931 : Blo 654306 655931 := bstep (se 1 (by rfl) ⟨491948, by rfl⟩ : syracuseStep 655931 = 983897) B983897
theorem B1245755 : Blo 654306 1245755 := bstep (se 1 (by rfl) ⟨934316, by rfl⟩ : syracuseStep 1245755 = 1868633) B1868633
theorem B1999475 : Blo 654306 1999475 := bstep (se 1 (by rfl) ⟨1499606, by rfl⟩ : syracuseStep 1999475 = 2999213) B2999213
theorem B3146359 : Blo 654306 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B1475207 : Blo 654306 1475207 := bstep (se 1 (by rfl) ⟨1106405, by rfl⟩ : syracuseStep 1475207 = 2212811) B2212811
theorem B983687 : Blo 654306 983687 := bstep (se 1 (by rfl) ⟨737765, by rfl⟩ : syracuseStep 983687 = 1475531) B1475531
theorem B656007 : Blo 654306 656007 := bstep (se 1 (by rfl) ⟨492005, by rfl⟩ : syracuseStep 656007 = 984011) B984011
theorem B656015 : Blo 654306 656015 := bstep (se 1 (by rfl) ⟨492011, by rfl⟩ : syracuseStep 656015 = 984023) B984023
theorem B983723 : Blo 654306 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B7570097 : Blo 654306 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B656059 : Blo 654306 656059 := bstep (se 1 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 656059 = 984089) B984089
theorem B983753 : Blo 654306 983753 := bstep (se 2 (by rfl) ⟨368907, by rfl⟩ : syracuseStep 983753 = 737815) B737815
theorem B9470681 : Blo 654306 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B103383793 : Blo 654306 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B218170097 : Blo 654306 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B656135 : Blo 654306 656135 := bstep (se 1 (by rfl) ⟨492101, by rfl⟩ : syracuseStep 656135 = 984203) B984203
theorem B656143 : Blo 654306 656143 := bstep (se 1 (by rfl) ⟨492107, by rfl⟩ : syracuseStep 656143 = 984215) B984215
theorem B1475387 : Blo 654306 1475387 := bstep (se 1 (by rfl) ⟨1106540, by rfl⟩ : syracuseStep 1475387 = 2213081) B2213081
theorem B983867 : Blo 654306 983867 := bstep (se 1 (by rfl) ⟨737900, by rfl⟩ : syracuseStep 983867 = 1475801) B1475801
theorem B656187 : Blo 654306 656187 := bstep (se 1 (by rfl) ⟨492140, by rfl⟩ : syracuseStep 656187 = 984281) B984281
theorem B983927 : Blo 654306 983927 := bstep (se 1 (by rfl) ⟨737945, by rfl⟩ : syracuseStep 983927 = 1475891) B1475891
theorem B656263 : Blo 654306 656263 := bstep (se 1 (by rfl) ⟨492197, by rfl⟩ : syracuseStep 656263 = 984395) B984395
theorem B983951 : Blo 654306 983951 := bstep (se 1 (by rfl) ⟨737963, by rfl⟩ : syracuseStep 983951 = 1475927) B1475927
theorem B656271 : Blo 654306 656271 := bstep (se 1 (by rfl) ⟨492203, by rfl⟩ : syracuseStep 656271 = 984407) B984407
theorem B7111577 : Blo 654306 7111577 := bstep (se 2 (by rfl) ⟨2666841, by rfl⟩ : syracuseStep 7111577 = 5333683) B5333683
theorem B1475513 : Blo 654306 1475513 := bstep (se 2 (by rfl) ⟨553317, by rfl⟩ : syracuseStep 1475513 = 1106635) B1106635
theorem B983993 : Blo 654306 983993 := bstep (se 2 (by rfl) ⟨368997, by rfl⟩ : syracuseStep 983993 = 737995) B737995
theorem B656315 : Blo 654306 656315 := bstep (se 1 (by rfl) ⟨492236, by rfl⟩ : syracuseStep 656315 = 984473) B984473
theorem B6390731 : Blo 654306 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B984071 : Blo 654306 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B656391 : Blo 654306 656391 := bstep (se 1 (by rfl) ⟨492293, by rfl⟩ : syracuseStep 656391 = 984587) B984587
theorem B656399 : Blo 654306 656399 := bstep (se 1 (by rfl) ⟨492299, by rfl⟩ : syracuseStep 656399 = 984599) B984599
theorem B1246241 : Blo 654306 1246241 := bstep (se 2 (by rfl) ⟨467340, by rfl⟩ : syracuseStep 1246241 = 934681) B934681
theorem B984107 : Blo 654306 984107 := bstep (se 1 (by rfl) ⟨738080, by rfl⟩ : syracuseStep 984107 = 1476161) B1476161
theorem B656443 : Blo 654306 656443 := bstep (se 1 (by rfl) ⟨492332, by rfl⟩ : syracuseStep 656443 = 984665) B984665
theorem B984137 : Blo 654306 984137 := bstep (se 2 (by rfl) ⟨369051, by rfl⟩ : syracuseStep 984137 = 738103) B738103
theorem B1049735 : Blo 654306 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B656519 : Blo 654306 656519 := bstep (se 1 (by rfl) ⟨492389, by rfl⟩ : syracuseStep 656519 = 984779) B984779
theorem B656527 : Blo 654306 656527 := bstep (se 1 (by rfl) ⟨492395, by rfl⟩ : syracuseStep 656527 = 984791) B984791
theorem B984251 : Blo 654306 984251 := bstep (se 1 (by rfl) ⟨738188, by rfl⟩ : syracuseStep 984251 = 1476377) B1476377
theorem B656571 : Blo 654306 656571 := bstep (se 1 (by rfl) ⟨492428, by rfl⟩ : syracuseStep 656571 = 984857) B984857
theorem B984311 : Blo 654306 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B656647 : Blo 654306 656647 := bstep (se 1 (by rfl) ⟨492485, by rfl⟩ : syracuseStep 656647 = 984971) B984971
theorem B1475855 : Blo 654306 1475855 := bstep (se 1 (by rfl) ⟨1106891, by rfl⟩ : syracuseStep 1475855 = 2213783) B2213783
theorem B984335 : Blo 654306 984335 := bstep (se 1 (by rfl) ⟨738251, by rfl⟩ : syracuseStep 984335 = 1476503) B1476503
theorem B656655 : Blo 654306 656655 := bstep (se 1 (by rfl) ⟨492491, by rfl⟩ : syracuseStep 656655 = 984983) B984983
theorem B1475873 : Blo 654306 1475873 := bstep (se 2 (by rfl) ⟨553452, by rfl⟩ : syracuseStep 1475873 = 1106905) B1106905
theorem B984377 : Blo 654306 984377 := bstep (se 2 (by rfl) ⟨369141, by rfl⟩ : syracuseStep 984377 = 738283) B738283
theorem B656699 : Blo 654306 656699 := bstep (se 1 (by rfl) ⟨492524, by rfl⟩ : syracuseStep 656699 = 985049) B985049
theorem B4621627 : Blo 654306 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B1246583 : Blo 654306 1246583 := bstep (se 1 (by rfl) ⟨934937, by rfl⟩ : syracuseStep 1246583 = 1869875) B1869875
theorem B984455 : Blo 654306 984455 := bstep (se 1 (by rfl) ⟨738341, by rfl⟩ : syracuseStep 984455 = 1476683) B1476683
theorem B656775 : Blo 654306 656775 := bstep (se 1 (by rfl) ⟨492581, by rfl⟩ : syracuseStep 656775 = 985163) B985163
theorem B656783 : Blo 654306 656783 := bstep (se 1 (by rfl) ⟨492587, by rfl⟩ : syracuseStep 656783 = 985175) B985175
theorem B984491 : Blo 654306 984491 := bstep (se 1 (by rfl) ⟨738368, by rfl⟩ : syracuseStep 984491 = 1476737) B1476737
theorem B656827 : Blo 654306 656827 := bstep (se 1 (by rfl) ⟨492620, by rfl⟩ : syracuseStep 656827 = 985241) B985241
theorem B984521 : Blo 654306 984521 := bstep (se 2 (by rfl) ⟨369195, by rfl⟩ : syracuseStep 984521 = 738391) B738391
theorem B656903 : Blo 654306 656903 := bstep (se 1 (by rfl) ⟨492677, by rfl⟩ : syracuseStep 656903 = 985355) B985355
theorem B656911 : Blo 654306 656911 := bstep (se 1 (by rfl) ⟨492683, by rfl⟩ : syracuseStep 656911 = 985367) B985367
theorem B984635 : Blo 654306 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B656955 : Blo 654306 656955 := bstep (se 1 (by rfl) ⟨492716, by rfl⟩ : syracuseStep 656955 = 985433) B985433
theorem B1476215 : Blo 654306 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B984695 : Blo 654306 984695 := bstep (se 1 (by rfl) ⟨738521, by rfl⟩ : syracuseStep 984695 = 1477043) B1477043
theorem B657031 : Blo 654306 657031 := bstep (se 1 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 657031 = 985547) B985547
theorem B984719 : Blo 654306 984719 := bstep (se 1 (by rfl) ⟨738539, by rfl⟩ : syracuseStep 984719 = 1477079) B1477079
theorem B657039 : Blo 654306 657039 := bstep (se 1 (by rfl) ⟨492779, by rfl⟩ : syracuseStep 657039 = 985559) B985559
theorem B984761 : Blo 654306 984761 := bstep (se 2 (by rfl) ⟨369285, by rfl⟩ : syracuseStep 984761 = 738571) B738571
theorem B657083 : Blo 654306 657083 := bstep (se 1 (by rfl) ⟨492812, by rfl⟩ : syracuseStep 657083 = 985625) B985625
theorem B7079653 : Blo 654306 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B4196069 : Blo 654306 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B984839 : Blo 654306 984839 := bstep (se 1 (by rfl) ⟨738629, by rfl⟩ : syracuseStep 984839 = 1477259) B1477259
theorem B657159 : Blo 654306 657159 := bstep (se 1 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 657159 = 985739) B985739
theorem B788239 : Blo 654306 788239 := bstep (se 1 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 788239 = 1182359) B1182359
theorem B657167 : Blo 654306 657167 := bstep (se 1 (by rfl) ⟨492875, by rfl⟩ : syracuseStep 657167 = 985751) B985751
theorem B1869601 : Blo 654306 1869601 := bstep (se 2 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 1869601 = 1402201) B1402201
theorem B1476395 : Blo 654306 1476395 := bstep (se 1 (by rfl) ⟨1107296, by rfl⟩ : syracuseStep 1476395 = 2214593) B2214593
theorem B984875 : Blo 654306 984875 := bstep (se 1 (by rfl) ⟨738656, by rfl⟩ : syracuseStep 984875 = 1477313) B1477313
theorem B657211 : Blo 654306 657211 := bstep (se 1 (by rfl) ⟨492908, by rfl⟩ : syracuseStep 657211 = 985817) B985817
theorem B984905 : Blo 654306 984905 := bstep (se 2 (by rfl) ⟨369339, by rfl⟩ : syracuseStep 984905 = 738679) B738679
theorem B6752089 : Blo 654306 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B657287 : Blo 654306 657287 := bstep (se 1 (by rfl) ⟨492965, by rfl⟩ : syracuseStep 657287 = 985931) B985931
theorem B657295 : Blo 654306 657295 := bstep (se 1 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 657295 = 985943) B985943
theorem B985019 : Blo 654306 985019 := bstep (se 1 (by rfl) ⟨738764, by rfl⟩ : syracuseStep 985019 = 1477529) B1477529
theorem B657339 : Blo 654306 657339 := bstep (se 1 (by rfl) ⟨493004, by rfl⟩ : syracuseStep 657339 = 986009) B986009
theorem B985079 : Blo 654306 985079 := bstep (se 1 (by rfl) ⟨738809, by rfl⟩ : syracuseStep 985079 = 1477619) B1477619
theorem B657415 : Blo 654306 657415 := bstep (se 1 (by rfl) ⟨493061, by rfl⟩ : syracuseStep 657415 = 986123) B986123
theorem B985103 : Blo 654306 985103 := bstep (se 1 (by rfl) ⟨738827, by rfl⟩ : syracuseStep 985103 = 1477655) B1477655
theorem B657423 : Blo 654306 657423 := bstep (se 1 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 657423 = 986135) B986135
theorem B985145 : Blo 654306 985145 := bstep (se 2 (by rfl) ⟨369429, by rfl⟩ : syracuseStep 985145 = 738859) B738859
theorem B657467 : Blo 654306 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B985223 : Blo 654306 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B657543 : Blo 654306 657543 := bstep (se 1 (by rfl) ⟨493157, by rfl⟩ : syracuseStep 657543 = 986315) B986315
theorem B657551 : Blo 654306 657551 := bstep (se 1 (by rfl) ⟨493163, by rfl⟩ : syracuseStep 657551 = 986327) B986327
theorem B1476755 : Blo 654306 1476755 := bstep (se 1 (by rfl) ⟨1107566, by rfl⟩ : syracuseStep 1476755 = 2215133) B2215133
theorem B985259 : Blo 654306 985259 := bstep (se 1 (by rfl) ⟨738944, by rfl⟩ : syracuseStep 985259 = 1477889) B1477889
theorem B4982957 : Blo 654306 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B657595 : Blo 654306 657595 := bstep (se 1 (by rfl) ⟨493196, by rfl⟩ : syracuseStep 657595 = 986393) B986393
theorem B1771721 : Blo 654306 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1476809 : Blo 654306 1476809 := bstep (se 2 (by rfl) ⟨553803, by rfl⟩ : syracuseStep 1476809 = 1107607) B1107607
theorem B985289 : Blo 654306 985289 := bstep (se 2 (by rfl) ⟨369483, by rfl⟩ : syracuseStep 985289 = 738967) B738967
theorem B657671 : Blo 654306 657671 := bstep (se 1 (by rfl) ⟨493253, by rfl⟩ : syracuseStep 657671 = 986507) B986507
theorem B1870091 : Blo 654306 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B657679 : Blo 654306 657679 := bstep (se 1 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 657679 = 986519) B986519
theorem B985403 : Blo 654306 985403 := bstep (se 1 (by rfl) ⟨739052, by rfl⟩ : syracuseStep 985403 = 1478105) B1478105
theorem B657723 : Blo 654306 657723 := bstep (se 1 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 657723 = 986585) B986585
theorem B1771895 : Blo 654306 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B985463 : Blo 654306 985463 := bstep (se 1 (by rfl) ⟨739097, by rfl⟩ : syracuseStep 985463 = 1478195) B1478195
theorem B657799 : Blo 654306 657799 := bstep (se 1 (by rfl) ⟨493349, by rfl⟩ : syracuseStep 657799 = 986699) B986699
theorem B985487 : Blo 654306 985487 := bstep (se 1 (by rfl) ⟨739115, by rfl⟩ : syracuseStep 985487 = 1478231) B1478231
theorem B657807 : Blo 654306 657807 := bstep (se 1 (by rfl) ⟨493355, by rfl⟩ : syracuseStep 657807 = 986711) B986711
theorem B985529 : Blo 654306 985529 := bstep (se 2 (by rfl) ⟨369573, by rfl⟩ : syracuseStep 985529 = 739147) B739147
theorem B657851 : Blo 654306 657851 := bstep (se 1 (by rfl) ⟨493388, by rfl⟩ : syracuseStep 657851 = 986777) B986777
theorem B788983 : Blo 654306 788983 := bstep (se 1 (by rfl) ⟨591737, by rfl⟩ : syracuseStep 788983 = 1183475) B1183475
theorem B985607 : Blo 654306 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B657927 : Blo 654306 657927 := bstep (se 1 (by rfl) ⟨493445, by rfl⟩ : syracuseStep 657927 = 986891) B986891
theorem B657935 : Blo 654306 657935 := bstep (se 1 (by rfl) ⟨493451, by rfl⟩ : syracuseStep 657935 = 986903) B986903
theorem B7473707 : Blo 654306 7473707 := bstep (se 1 (by rfl) ⟨5605280, by rfl⟩ : syracuseStep 7473707 = 11210561) B11210561
theorem B985643 : Blo 654306 985643 := bstep (se 1 (by rfl) ⟨739232, by rfl⟩ : syracuseStep 985643 = 1478465) B1478465
theorem B657979 : Blo 654306 657979 := bstep (se 1 (by rfl) ⟨493484, by rfl⟩ : syracuseStep 657979 = 986969) B986969
theorem B2001469 : Blo 654306 2001469 := bstep (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) B750551
theorem B985673 : Blo 654306 985673 := bstep (se 2 (by rfl) ⟨369627, by rfl⟩ : syracuseStep 985673 = 739255) B739255
theorem B658055 : Blo 654306 658055 := bstep (se 1 (by rfl) ⟨493541, by rfl⟩ : syracuseStep 658055 = 987083) B987083
theorem B658063 : Blo 654306 658063 := bstep (se 1 (by rfl) ⟨493547, by rfl⟩ : syracuseStep 658063 = 987095) B987095
theorem B985787 : Blo 654306 985787 := bstep (se 1 (by rfl) ⟨739340, by rfl⟩ : syracuseStep 985787 = 1478681) B1478681
theorem B658107 : Blo 654306 658107 := bstep (se 1 (by rfl) ⟨493580, by rfl⟩ : syracuseStep 658107 = 987161) B987161
theorem B985847 : Blo 654306 985847 := bstep (se 1 (by rfl) ⟨739385, by rfl⟩ : syracuseStep 985847 = 1478771) B1478771
theorem B658183 : Blo 654306 658183 := bstep (se 1 (by rfl) ⟨493637, by rfl⟩ : syracuseStep 658183 = 987275) B987275
theorem B985871 : Blo 654306 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B658191 : Blo 654306 658191 := bstep (se 1 (by rfl) ⟨493643, by rfl⟩ : syracuseStep 658191 = 987287) B987287
theorem B985913 : Blo 654306 985913 := bstep (se 2 (by rfl) ⟨369717, by rfl⟩ : syracuseStep 985913 = 739435) B739435
theorem B658235 : Blo 654306 658235 := bstep (se 1 (by rfl) ⟨493676, by rfl⟩ : syracuseStep 658235 = 987353) B987353
theorem B1477511 : Blo 654306 1477511 := bstep (se 1 (by rfl) ⟨1108133, by rfl⟩ : syracuseStep 1477511 = 2216267) B2216267
theorem B985991 : Blo 654306 985991 := bstep (se 1 (by rfl) ⟨739493, by rfl⟩ : syracuseStep 985991 = 1478987) B1478987
theorem B986027 : Blo 654306 986027 := bstep (se 1 (by rfl) ⟨739520, by rfl⟩ : syracuseStep 986027 = 1479041) B1479041
theorem B1248185 : Blo 654306 1248185 := bstep (se 2 (by rfl) ⟨468069, by rfl⟩ : syracuseStep 1248185 = 936139) B936139
theorem B986057 : Blo 654306 986057 := bstep (se 2 (by rfl) ⟨369771, by rfl⟩ : syracuseStep 986057 = 739543) B739543
theorem B1870877 : Blo 654306 1870877 := bstep (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) B701579
theorem B1477691 : Blo 654306 1477691 := bstep (se 1 (by rfl) ⟨1108268, by rfl⟩ : syracuseStep 1477691 = 2216537) B2216537
theorem B986171 : Blo 654306 986171 := bstep (se 1 (by rfl) ⟨739628, by rfl⟩ : syracuseStep 986171 = 1479257) B1479257
theorem B986231 : Blo 654306 986231 := bstep (se 1 (by rfl) ⟨739673, by rfl⟩ : syracuseStep 986231 = 1479347) B1479347
theorem B986255 : Blo 654306 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B3148973 : Blo 654306 3148973 := bstep (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) B1180865
theorem B1477817 : Blo 654306 1477817 := bstep (se 2 (by rfl) ⟨554181, by rfl⟩ : syracuseStep 1477817 = 1108363) B1108363
theorem B986297 : Blo 654306 986297 := bstep (se 2 (by rfl) ⟨369861, by rfl⟩ : syracuseStep 986297 = 739723) B739723
theorem B986375 : Blo 654306 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B1248527 : Blo 654306 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B986411 : Blo 654306 986411 := bstep (se 1 (by rfl) ⟨739808, by rfl⟩ : syracuseStep 986411 = 1479617) B1479617
theorem B986441 : Blo 654306 986441 := bstep (se 2 (by rfl) ⟨369915, by rfl⟩ : syracuseStep 986441 = 739831) B739831
theorem B5672339 : Blo 654306 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B986555 : Blo 654306 986555 := bstep (se 1 (by rfl) ⟨739916, by rfl⟩ : syracuseStep 986555 = 1479833) B1479833
theorem B986615 : Blo 654306 986615 := bstep (se 1 (by rfl) ⟨739961, by rfl⟩ : syracuseStep 986615 = 1479923) B1479923
theorem B1478159 : Blo 654306 1478159 := bstep (se 1 (by rfl) ⟨1108619, by rfl⟩ : syracuseStep 1478159 = 2217239) B2217239
theorem B790031 : Blo 654306 790031 := bstep (se 1 (by rfl) ⟨592523, by rfl⟩ : syracuseStep 790031 = 1185047) B1185047
theorem B986639 : Blo 654306 986639 := bstep (se 1 (by rfl) ⟨739979, by rfl⟩ : syracuseStep 986639 = 1479959) B1479959
theorem B1478177 : Blo 654306 1478177 := bstep (se 2 (by rfl) ⟨554316, by rfl⟩ : syracuseStep 1478177 = 1108633) B1108633
theorem B1150507 : Blo 654306 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B986681 : Blo 654306 986681 := bstep (se 2 (by rfl) ⟨370005, by rfl⟩ : syracuseStep 986681 = 740011) B740011
theorem B3739223 : Blo 654306 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B10620517 : Blo 654306 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B986759 : Blo 654306 986759 := bstep (se 1 (by rfl) ⟨740069, by rfl⟩ : syracuseStep 986759 = 1480139) B1480139
theorem B17927831 : Blo 654306 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B986795 : Blo 654306 986795 := bstep (se 1 (by rfl) ⟨740096, by rfl⟩ : syracuseStep 986795 = 1480193) B1480193
theorem B3149513 : Blo 654306 3149513 := bstep (se 2 (by rfl) ⟨1181067, by rfl⟩ : syracuseStep 3149513 = 2362135) B2362135
theorem B986825 : Blo 654306 986825 := bstep (se 2 (by rfl) ⟨370059, by rfl⟩ : syracuseStep 986825 = 740119) B740119
theorem B986939 : Blo 654306 986939 := bstep (se 1 (by rfl) ⟨740204, by rfl⟩ : syracuseStep 986939 = 1480409) B1480409
theorem B1478519 : Blo 654306 1478519 := bstep (se 1 (by rfl) ⟨1108889, by rfl⟩ : syracuseStep 1478519 = 2217779) B2217779
theorem B986999 : Blo 654306 986999 := bstep (se 1 (by rfl) ⟨740249, by rfl⟩ : syracuseStep 986999 = 1480499) B1480499
theorem B987023 : Blo 654306 987023 := bstep (se 1 (by rfl) ⟨740267, by rfl⟩ : syracuseStep 987023 = 1480535) B1480535
theorem B987065 : Blo 654306 987065 := bstep (se 2 (by rfl) ⟨370149, by rfl⟩ : syracuseStep 987065 = 740299) B740299
theorem B987143 : Blo 654306 987143 := bstep (se 1 (by rfl) ⟨740357, by rfl⟩ : syracuseStep 987143 = 1480715) B1480715
theorem B1478699 : Blo 654306 1478699 := bstep (se 1 (by rfl) ⟨1109024, by rfl⟩ : syracuseStep 1478699 = 2218049) B2218049
theorem B987179 : Blo 654306 987179 := bstep (se 1 (by rfl) ⟨740384, by rfl⟩ : syracuseStep 987179 = 1480769) B1480769
theorem B1249339 : Blo 654306 1249339 := bstep (se 1 (by rfl) ⟨937004, by rfl⟩ : syracuseStep 1249339 = 1874009) B1874009
theorem B987209 : Blo 654306 987209 := bstep (se 2 (by rfl) ⟨370203, by rfl⟩ : syracuseStep 987209 = 740407) B740407
theorem B1249415 : Blo 654306 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B987323 : Blo 654306 987323 := bstep (se 1 (by rfl) ⟨740492, by rfl⟩ : syracuseStep 987323 = 1480985) B1480985
theorem B987383 : Blo 654306 987383 := bstep (se 1 (by rfl) ⟨740537, by rfl⟩ : syracuseStep 987383 = 1481075) B1481075
theorem B987407 : Blo 654306 987407 := bstep (se 1 (by rfl) ⟨740555, by rfl⟩ : syracuseStep 987407 = 1481111) B1481111
theorem B987449 : Blo 654306 987449 := bstep (se 2 (by rfl) ⟨370293, by rfl⟩ : syracuseStep 987449 = 740587) B740587
theorem B1577351 : Blo 654306 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1479059 : Blo 654306 1479059 := bstep (se 1 (by rfl) ⟨1109294, by rfl⟩ : syracuseStep 1479059 = 2218589) B2218589
theorem B1479113 : Blo 654306 1479113 := bstep (se 2 (by rfl) ⟨554667, by rfl⟩ : syracuseStep 1479113 = 1109335) B1109335
theorem B3150359 : Blo 654306 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B4985387 : Blo 654306 4985387 := bstep (se 1 (by rfl) ⟨3739040, by rfl⟩ : syracuseStep 4985387 = 7478081) B7478081
theorem B2495063 : Blo 654306 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B1774489 : Blo 654306 1774489 := bstep (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) B1330867
theorem B3150859 : Blo 654306 3150859 := bstep (se 1 (by rfl) ⟨2363144, by rfl⟩ : syracuseStep 3150859 = 4726289) B4726289
theorem B7574573 : Blo 654306 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B2495549 : Blo 654306 2495549 := bstep (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) B935831
theorem B1872983 : Blo 654306 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B1479815 : Blo 654306 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B1479995 : Blo 654306 1479995 := bstep (se 1 (by rfl) ⟨1109996, by rfl⟩ : syracuseStep 1479995 = 2219993) B2219993
theorem B4724153 : Blo 654306 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B1480121 : Blo 654306 1480121 := bstep (se 2 (by rfl) ⟨555045, by rfl⟩ : syracuseStep 1480121 = 1110091) B1110091
theorem B3741137 : Blo 654306 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B1775105 : Blo 654306 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B17929907 : Blo 654306 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B1480463 : Blo 654306 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1480481 : Blo 654306 1480481 := bstep (se 2 (by rfl) ⟨555180, by rfl⟩ : syracuseStep 1480481 = 1110361) B1110361
theorem B7313267 : Blo 654306 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B1775495 : Blo 654306 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B1873849 : Blo 654306 1873849 := bstep (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) B1405387
theorem B1480823 : Blo 654306 1480823 := bstep (se 1 (by rfl) ⟨1110617, by rfl⟩ : syracuseStep 1480823 = 2221235) B2221235
theorem B15931565 : Blo 654306 15931565 := bstep (se 3 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 15931565 = 5974337) B5974337
theorem B1874191 : Blo 654306 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B1481003 : Blo 654306 1481003 := bstep (se 1 (by rfl) ⟨1110752, by rfl⟩ : syracuseStep 1481003 = 2221505) B2221505
theorem B1579351 : Blo 654306 1579351 := bstep (se 1 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 1579351 = 2369027) B2369027
theorem B5970323 : Blo 654306 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B2496977 : Blo 654306 2496977 := bstep (se 2 (by rfl) ⟨936366, by rfl⟩ : syracuseStep 2496977 = 1872733) B1872733
theorem B3545623 : Blo 654306 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B1874465 : Blo 654306 1874465 := bstep (se 2 (by rfl) ⟨702924, by rfl⟩ : syracuseStep 1874465 = 1405849) B1405849
theorem B3316625 : Blo 654306 3316625 := bstep (se 2 (by rfl) ⟨1243734, by rfl⟩ : syracuseStep 3316625 = 2487469) B2487469
theorem B40410019 : Blo 654306 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B2989345 : Blo 654306 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B10132867 : Blo 654306 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2498647 : Blo 654306 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B2498951 : Blo 654306 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B1122761 : Blo 654306 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B2368061 : Blo 654306 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B2499133 : Blo 654306 2499133 := bstep (se 3 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 2499133 = 937175) B937175
theorem B3318731 : Blo 654306 3318731 := bstep (se 1 (by rfl) ⟨2489048, by rfl⟩ : syracuseStep 3318731 = 4978097) B4978097
theorem B828407 : Blo 654306 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B828559 : Blo 654306 828559 := bstep (se 1 (by rfl) ⟨621419, by rfl⟩ : syracuseStep 828559 = 1242839) B1242839
theorem B3319055 : Blo 654306 3319055 := bstep (se 1 (by rfl) ⟨2489291, by rfl⟩ : syracuseStep 3319055 = 4978583) B4978583
theorem B4203809 : Blo 654306 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B828731 : Blo 654306 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B5612935 : Blo 654306 5612935 := bstep (se 1 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 5612935 = 8419403) B8419403
theorem B4499201 : Blo 654306 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B4728739 : Blo 654306 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B2664377 : Blo 654306 2664377 := bstep (se 2 (by rfl) ⟨999141, by rfl⟩ : syracuseStep 2664377 = 1998283) B1998283
theorem B2107403 : Blo 654306 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B4204781 : Blo 654306 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B829703 : Blo 654306 829703 := bstep (se 1 (by rfl) ⟨622277, by rfl⟩ : syracuseStep 829703 = 1244555) B1244555
theorem B3746195 : Blo 654306 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B3156509 : Blo 654306 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B26978935 : Blo 654306 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B3320513 : Blo 654306 3320513 := bstep (se 2 (by rfl) ⟨1245192, by rfl⟩ : syracuseStep 3320513 = 2490385) B2490385
theorem B3746695 : Blo 654306 3746695 := bstep (se 1 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 3746695 = 5620043) B5620043
theorem B830351 : Blo 654306 830351 := bstep (se 1 (by rfl) ⟨622763, by rfl⟩ : syracuseStep 830351 = 1245527) B1245527
theorem B7482455 : Blo 654306 7482455 := bstep (se 1 (by rfl) ⟨5611841, by rfl⟩ : syracuseStep 7482455 = 11223683) B11223683
theorem B2993593 : Blo 654306 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B3321809 : Blo 654306 3321809 := bstep (se 2 (by rfl) ⟨1245678, by rfl⟩ : syracuseStep 3321809 = 2491357) B2491357
theorem B995627 : Blo 654306 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B2470297 : Blo 654306 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B2208545 : Blo 654306 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B701455 : Blo 654306 701455 := bstep (se 1 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 701455 = 1052183) B1052183
theorem B3159107 : Blo 654306 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B4994135 : Blo 654306 4994135 := bstep (se 1 (by rfl) ⟨3745601, by rfl⟩ : syracuseStep 4994135 = 7491203) B7491203
theorem B2209139 : Blo 654306 2209139 := bstep (se 1 (by rfl) ⟨1656854, by rfl⟩ : syracuseStep 2209139 = 3313709) B3313709
theorem B701831 : Blo 654306 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B3159431 : Blo 654306 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B931657 : Blo 654306 931657 := bstep (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) B698743
theorem B3192797 : Blo 654306 3192797 := bstep (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) B1197299
theorem B3323915 : Blo 654306 3323915 := bstep (se 1 (by rfl) ⟨2492936, by rfl⟩ : syracuseStep 3323915 = 4985873) B4985873
theorem B702523 : Blo 654306 702523 := bstep (se 1 (by rfl) ⟨526892, by rfl⟩ : syracuseStep 702523 = 1053785) B1053785
theorem B3324077 : Blo 654306 3324077 := bstep (se 3 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 3324077 = 1246529) B1246529
theorem B3587075 : Blo 654306 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B9616445 : Blo 654306 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B2800727 : Blo 654306 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B736519 : Blo 654306 736519 := bstep (se 1 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 736519 = 1104779) B1104779
theorem B3554705 : Blo 654306 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B736699 : Blo 654306 736699 := bstep (se 1 (by rfl) ⟨552524, by rfl⟩ : syracuseStep 736699 = 1105049) B1105049
theorem B3587777 : Blo 654306 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B3325697 : Blo 654306 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B737167 : Blo 654306 737167 := bstep (se 1 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 737167 = 1105751) B1105751
theorem B2211731 : Blo 654306 2211731 := bstep (se 1 (by rfl) ⟨1658798, by rfl⟩ : syracuseStep 2211731 = 3317597) B3317597
theorem B8077219 : Blo 654306 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B6307787 : Blo 654306 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B10665931 : Blo 654306 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B8503319 : Blo 654306 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B737671 : Blo 654306 737671 := bstep (se 1 (by rfl) ⟨553253, by rfl⟩ : syracuseStep 737671 = 1106507) B1106507
theorem B934345 : Blo 654306 934345 := bstep (se 2 (by rfl) ⟨350379, by rfl⟩ : syracuseStep 934345 = 700759) B700759
theorem B3326507 : Blo 654306 3326507 := bstep (se 1 (by rfl) ⟨2494880, by rfl⟩ : syracuseStep 3326507 = 4989761) B4989761
theorem B737851 : Blo 654306 737851 := bstep (se 1 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 737851 = 1106777) B1106777
theorem B3162797 : Blo 654306 3162797 := bstep (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) B1186049
theorem B4735745 : Blo 654306 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B76596185 : Blo 654306 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B738319 : Blo 654306 738319 := bstep (se 1 (by rfl) ⟨553739, by rfl⟩ : syracuseStep 738319 = 1107479) B1107479
theorem B2213135 : Blo 654306 2213135 := bstep (se 1 (by rfl) ⟨1659851, by rfl⟩ : syracuseStep 2213135 = 3319703) B3319703
theorem B738823 : Blo 654306 738823 := bstep (se 1 (by rfl) ⟨554117, by rfl⟩ : syracuseStep 738823 = 1108235) B1108235
theorem B2213405 : Blo 654306 2213405 := bstep (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) B830027
theorem B739003 : Blo 654306 739003 := bstep (se 1 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 739003 = 1108505) B1108505
theorem B1656521 : Blo 654306 1656521 := bstep (se 2 (by rfl) ⟨621195, by rfl⟩ : syracuseStep 1656521 = 1242391) B1242391
theorem B3327803 : Blo 654306 3327803 := bstep (se 1 (by rfl) ⟨2495852, by rfl⟩ : syracuseStep 3327803 = 4991705) B4991705
theorem B3327965 : Blo 654306 3327965 := bstep (se 3 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 3327965 = 1247987) B1247987
theorem B1656875 : Blo 654306 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B739471 : Blo 654306 739471 := bstep (se 1 (by rfl) ⟨554603, by rfl⟩ : syracuseStep 739471 = 1109207) B1109207
theorem B3328289 : Blo 654306 3328289 := bstep (se 2 (by rfl) ⟨1248108, by rfl⟩ : syracuseStep 3328289 = 2496217) B2496217
theorem B1198379 : Blo 654306 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B739975 : Blo 654306 739975 := bstep (se 1 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 739975 = 1109963) B1109963
theorem B3001033 : Blo 654306 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B740155 : Blo 654306 740155 := bstep (se 1 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 740155 = 1110233) B1110233
theorem B2214809 : Blo 654306 2214809 := bstep (se 2 (by rfl) ⟨830553, by rfl⟩ : syracuseStep 2214809 = 1661107) B1661107
theorem B1657867 : Blo 654306 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B7588981 : Blo 654306 7588981 := bstep (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) B711467
theorem B1658009 : Blo 654306 1658009 := bstep (se 2 (by rfl) ⟨621753, by rfl⟩ : syracuseStep 1658009 = 1243507) B1243507
theorem B3788005 : Blo 654306 3788005 := bstep (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) B710251
theorem B3329261 : Blo 654306 3329261 := bstep (se 3 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 3329261 = 1248473) B1248473
theorem B1658171 : Blo 654306 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B937289 : Blo 654306 937289 := bstep (se 2 (by rfl) ⟨351483, by rfl⟩ : syracuseStep 937289 = 702967) B702967
theorem B2215511 : Blo 654306 2215511 := bstep (se 1 (by rfl) ⟨1661633, by rfl⟩ : syracuseStep 2215511 = 3323267) B3323267
theorem B25611875 : Blo 654306 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B1658515 : Blo 654306 1658515 := bstep (se 1 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 1658515 = 2487773) B2487773
theorem B1658657 : Blo 654306 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B1494827 : Blo 654306 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B5623667 : Blo 654306 5623667 := bstep (se 1 (by rfl) ⟨4217750, by rfl⟩ : syracuseStep 5623667 = 8435501) B8435501
theorem B3330071 : Blo 654306 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B2215997 : Blo 654306 2215997 := bstep (se 3 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 2215997 = 830999) B830999
theorem B4542551 : Blo 654306 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B6312401 : Blo 654306 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B11981297 : Blo 654306 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B3363565 : Blo 654306 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B1659649 : Blo 654306 1659649 := bstep (se 2 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 1659649 = 1244737) B1244737
theorem B4478125 : Blo 654306 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B1332425 : Blo 654306 1332425 := bstep (se 2 (by rfl) ⟨499659, by rfl⟩ : syracuseStep 1332425 = 999319) B999319
theorem B1660247 : Blo 654306 1660247 := bstep (se 1 (by rfl) ⟨1245185, by rfl⟩ : syracuseStep 1660247 = 2490371) B2490371
theorem B3986833 : Blo 654306 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B2217401 : Blo 654306 2217401 := bstep (se 2 (by rfl) ⟨831525, by rfl⟩ : syracuseStep 2217401 = 1663051) B1663051
theorem B1660459 : Blo 654306 1660459 := bstep (se 1 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 1660459 = 2490689) B2490689
theorem B1660601 : Blo 654306 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B1398647 : Blo 654306 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B3790795 : Blo 654306 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B2217995 : Blo 654306 2217995 := bstep (se 1 (by rfl) ⟨1663496, by rfl⟩ : syracuseStep 2217995 = 3326993) B3326993
theorem B2218103 : Blo 654306 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B1104313 : Blo 654306 1104313 := bstep (se 2 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 1104313 = 828235) B828235
theorem B1497545 : Blo 654306 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B1661593 : Blo 654306 1661593 := bstep (se 2 (by rfl) ⟨623097, by rfl⟩ : syracuseStep 1661593 = 1246195) B1246195
theorem B7101107 : Blo 654306 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B2218697 : Blo 654306 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B1661755 : Blo 654306 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B5331865 : Blo 654306 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B1661897 : Blo 654306 1661897 := bstep (se 2 (by rfl) ⟨623211, by rfl⟩ : syracuseStep 1661897 = 1246423) B1246423
theorem B1105015 : Blo 654306 1105015 := bstep (se 1 (by rfl) ⟨828761, by rfl⟩ : syracuseStep 1105015 = 1657523) B1657523
theorem B1662241 : Blo 654306 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B1105211 : Blo 654306 1105211 := bstep (se 1 (by rfl) ⟨828908, by rfl⟩ : syracuseStep 1105211 = 1657817) B1657817
theorem B2219399 : Blo 654306 2219399 := bstep (se 1 (by rfl) ⟨1664549, by rfl⟩ : syracuseStep 2219399 = 3329099) B3329099
theorem B3202679 : Blo 654306 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1105609 : Blo 654306 1105609 := bstep (se 2 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 1105609 = 829207) B829207
theorem B2219777 : Blo 654306 2219777 := bstep (se 2 (by rfl) ⟨832416, by rfl⟩ : syracuseStep 2219777 = 1664833) B1664833
theorem B1662839 : Blo 654306 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B1400723 : Blo 654306 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B7495577 : Blo 654306 7495577 := bstep (se 2 (by rfl) ⟨2810841, by rfl⟩ : syracuseStep 7495577 = 5621683) B5621683
theorem B8970263 : Blo 654306 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B2809885 : Blo 654306 2809885 := bstep (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) B1053707
theorem B2810227 : Blo 654306 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B1106311 : Blo 654306 1106311 := bstep (se 1 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 1106311 = 1659467) B1659467
theorem B2843027 : Blo 654306 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B2220587 : Blo 654306 2220587 := bstep (se 1 (by rfl) ⟨1665440, by rfl⟩ : syracuseStep 2220587 = 3330881) B3330881
theorem B7463501 : Blo 654306 7463501 := bstep (se 3 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 7463501 = 2798813) B2798813
theorem B1106959 : Blo 654306 1106959 := bstep (se 1 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 1106959 = 1660439) B1660439
theorem B1664135 : Blo 654306 1664135 := bstep (se 1 (by rfl) ⟨1248101, by rfl⟩ : syracuseStep 1664135 = 2496203) B2496203
theorem B1664185 : Blo 654306 1664185 := bstep (se 2 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 1664185 = 1248139) B1248139
theorem B5596397 : Blo 654306 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B3728699 : Blo 654306 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B1107499 : Blo 654306 1107499 := bstep (se 1 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 1107499 = 1661249) B1661249
theorem B1500731 : Blo 654306 1500731 := bstep (se 1 (by rfl) ⟨1125548, by rfl⟩ : syracuseStep 1500731 = 2251097) B2251097
theorem B1107641 : Blo 654306 1107641 := bstep (se 2 (by rfl) ⟨415365, by rfl⟩ : syracuseStep 1107641 = 830731) B830731
theorem B4548325 : Blo 654306 4548325 := bstep (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) B852811
theorem B1795841 : Blo 654306 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B1664783 : Blo 654306 1664783 := bstep (se 1 (by rfl) ⟨1248587, by rfl⟩ : syracuseStep 1664783 = 2497175) B2497175
theorem B7989521 : Blo 654306 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B2484539 : Blo 654306 2484539 := bstep (se 1 (by rfl) ⟨1863404, by rfl⟩ : syracuseStep 2484539 = 3726809) B3726809
theorem B1108343 : Blo 654306 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B3991943 : Blo 654306 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B1665481 : Blo 654306 1665481 := bstep (se 2 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 1665481 = 1249111) B1249111
theorem B4975181 : Blo 654306 4975181 := bstep (se 3 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 4975181 = 1865693) B1865693
theorem B1665623 : Blo 654306 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B3730157 : Blo 654306 3730157 := bstep (se 3 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 3730157 = 1398809) B1398809
theorem B2485025 : Blo 654306 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B1108795 : Blo 654306 1108795 := bstep (se 1 (by rfl) ⟨831596, by rfl⟩ : syracuseStep 1108795 = 1663193) B1663193
theorem B1993673 : Blo 654306 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1108937 : Blo 654306 1108937 := bstep (se 2 (by rfl) ⟨415851, by rfl⟩ : syracuseStep 1108937 = 831703) B831703
theorem B1403849 : Blo 654306 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B3730475 : Blo 654306 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B1109639 : Blo 654306 1109639 := bstep (se 1 (by rfl) ⟨832229, by rfl⟩ : syracuseStep 1109639 = 1664459) B1664459
theorem B2485997 : Blo 654306 2485997 := bstep (se 3 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 2485997 = 932249) B932249
theorem B2486315 : Blo 654306 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B46723313 : Blo 654306 46723313 := bstep (se 2 (by rfl) ⟨17521242, by rfl⟩ : syracuseStep 46723313 = 35042485) B35042485
theorem B1110287 : Blo 654306 1110287 := bstep (se 1 (by rfl) ⟨832715, by rfl⟩ : syracuseStep 1110287 = 1665431) B1665431
theorem B2027891 : Blo 654306 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B3731933 : Blo 654306 3731933 := bstep (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) B1399475
theorem B1864235 : Blo 654306 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1110827 : Blo 654306 1110827 := bstep (se 1 (by rfl) ⟨833120, by rfl⟩ : syracuseStep 1110827 = 1666241) B1666241
theorem B1405831 : Blo 654306 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B4977611 : Blo 654306 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B1995923 : Blo 654306 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B947371 : Blo 654306 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B5600771 : Blo 654306 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B1865227 : Blo 654306 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B23983685 : Blo 654306 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B1472201 : Blo 654306 1472201 := bstep (se 2 (by rfl) ⟨552075, by rfl⟩ : syracuseStep 1472201 = 1104151) B1104151
theorem B1865501 : Blo 654306 1865501 := bstep (se 3 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 1865501 = 699563) B699563
theorem B7567141 : Blo 654306 7567141 := bstep (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) B1418839
theorem B14219509 : Blo 654306 14219509 := bstep (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) B1333079
theorem B1472903 : Blo 654306 1472903 := bstep (se 1 (by rfl) ⟨1104677, by rfl⟩ : syracuseStep 1472903 = 2209355) B2209355
theorem B3996125 : Blo 654306 3996125 := bstep (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) B1498547
theorem B6289949 : Blo 654306 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B981563 : Blo 654306 981563 := bstep (se 1 (by rfl) ⟨736172, by rfl⟩ : syracuseStep 981563 = 1472345) B1472345
theorem B1473083 : Blo 654306 1473083 := bstep (se 1 (by rfl) ⟨1104812, by rfl⟩ : syracuseStep 1473083 = 2209625) B2209625
theorem B981623 : Blo 654306 981623 := bstep (se 1 (by rfl) ⟨736217, by rfl⟩ : syracuseStep 981623 = 1472435) B1472435
theorem B981647 : Blo 654306 981647 := bstep (se 1 (by rfl) ⟨736235, by rfl⟩ : syracuseStep 981647 = 1472471) B1472471
theorem B981689 : Blo 654306 981689 := bstep (se 2 (by rfl) ⟨368133, by rfl⟩ : syracuseStep 981689 = 736267) B736267
theorem B1473209 : Blo 654306 1473209 := bstep (se 2 (by rfl) ⟨552453, by rfl⟩ : syracuseStep 1473209 = 1104907) B1104907
theorem B1243849 : Blo 654306 1243849 := bstep (se 2 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 1243849 = 932887) B932887
theorem B981767 : Blo 654306 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B4717349 : Blo 654306 4717349 := bstep (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) B884503
theorem B981803 : Blo 654306 981803 := bstep (se 1 (by rfl) ⟨736352, by rfl⟩ : syracuseStep 981803 = 1472705) B1472705
theorem B6716209 : Blo 654306 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B981833 : Blo 654306 981833 := bstep (se 2 (by rfl) ⟨368187, by rfl⟩ : syracuseStep 981833 = 736375) B736375
theorem B981947 : Blo 654306 981947 := bstep (se 1 (by rfl) ⟨736460, by rfl⟩ : syracuseStep 981947 = 1472921) B1472921
theorem B982007 : Blo 654306 982007 := bstep (se 1 (by rfl) ⟨736505, by rfl⟩ : syracuseStep 982007 = 1473011) B1473011
theorem B3734531 : Blo 654306 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B654343 : Blo 654306 654343 := bstep (se 1 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 654343 = 981515) B981515
theorem B654351 : Blo 654306 654351 := bstep (se 1 (by rfl) ⟨490763, by rfl⟩ : syracuseStep 654351 = 981527) B981527
theorem B982031 : Blo 654306 982031 := bstep (se 1 (by rfl) ⟨736523, by rfl⟩ : syracuseStep 982031 = 1473047) B1473047
theorem B1473551 : Blo 654306 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B1473569 : Blo 654306 1473569 := bstep (se 2 (by rfl) ⟨552588, by rfl⟩ : syracuseStep 1473569 = 1105177) B1105177
theorem B982073 : Blo 654306 982073 := bstep (se 2 (by rfl) ⟨368277, by rfl⟩ : syracuseStep 982073 = 736555) B736555
theorem B654395 : Blo 654306 654395 := bstep (se 1 (by rfl) ⟨490796, by rfl⟩ : syracuseStep 654395 = 981593) B981593
theorem B2096189 : Blo 654306 2096189 := bstep (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) B786071
theorem B654471 : Blo 654306 654471 := bstep (se 1 (by rfl) ⟨490853, by rfl⟩ : syracuseStep 654471 = 981707) B981707
theorem B982151 : Blo 654306 982151 := bstep (se 1 (by rfl) ⟨736613, by rfl⟩ : syracuseStep 982151 = 1473227) B1473227
theorem B654479 : Blo 654306 654479 := bstep (se 1 (by rfl) ⟨490859, by rfl⟩ : syracuseStep 654479 = 981719) B981719
theorem B982187 : Blo 654306 982187 := bstep (se 1 (by rfl) ⟨736640, by rfl⟩ : syracuseStep 982187 = 1473281) B1473281
theorem B654523 : Blo 654306 654523 := bstep (se 1 (by rfl) ⟨490892, by rfl⟩ : syracuseStep 654523 = 981785) B981785
theorem B982217 : Blo 654306 982217 := bstep (se 2 (by rfl) ⟨368331, by rfl⟩ : syracuseStep 982217 = 736663) B736663
theorem B654599 : Blo 654306 654599 := bstep (se 1 (by rfl) ⟨490949, by rfl⟩ : syracuseStep 654599 = 981899) B981899
theorem B654607 : Blo 654306 654607 := bstep (se 1 (by rfl) ⟨490955, by rfl⟩ : syracuseStep 654607 = 981911) B981911
theorem B982331 : Blo 654306 982331 := bstep (se 1 (by rfl) ⟨736748, by rfl⟩ : syracuseStep 982331 = 1473497) B1473497
theorem B654651 : Blo 654306 654651 := bstep (se 1 (by rfl) ⟨490988, by rfl⟩ : syracuseStep 654651 = 981977) B981977
theorem B982391 : Blo 654306 982391 := bstep (se 1 (by rfl) ⟨736793, by rfl⟩ : syracuseStep 982391 = 1473587) B1473587
theorem B1473911 : Blo 654306 1473911 := bstep (se 1 (by rfl) ⟨1105433, by rfl⟩ : syracuseStep 1473911 = 2210867) B2210867
theorem B654727 : Blo 654306 654727 := bstep (se 1 (by rfl) ⟨491045, by rfl⟩ : syracuseStep 654727 = 982091) B982091
theorem B654735 : Blo 654306 654735 := bstep (se 1 (by rfl) ⟨491051, by rfl⟩ : syracuseStep 654735 = 982103) B982103
theorem B982415 : Blo 654306 982415 := bstep (se 1 (by rfl) ⟨736811, by rfl⟩ : syracuseStep 982415 = 1473623) B1473623
theorem B982457 : Blo 654306 982457 := bstep (se 2 (by rfl) ⟨368421, by rfl⟩ : syracuseStep 982457 = 736843) B736843
theorem B654779 : Blo 654306 654779 := bstep (se 1 (by rfl) ⟨491084, by rfl⟩ : syracuseStep 654779 = 982169) B982169
theorem B3145169 : Blo 654306 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B654855 : Blo 654306 654855 := bstep (se 1 (by rfl) ⟨491141, by rfl⟩ : syracuseStep 654855 = 982283) B982283
theorem B982535 : Blo 654306 982535 := bstep (se 1 (by rfl) ⟨736901, by rfl⟩ : syracuseStep 982535 = 1473803) B1473803
theorem B654863 : Blo 654306 654863 := bstep (se 1 (by rfl) ⟨491147, by rfl⟩ : syracuseStep 654863 = 982295) B982295
theorem B2489885 : Blo 654306 2489885 := bstep (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) B933707
theorem B982571 : Blo 654306 982571 := bstep (se 1 (by rfl) ⟨736928, by rfl⟩ : syracuseStep 982571 = 1473857) B1473857
theorem B1474091 : Blo 654306 1474091 := bstep (se 1 (by rfl) ⟨1105568, by rfl⟩ : syracuseStep 1474091 = 2211137) B2211137
theorem B2489899 : Blo 654306 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B654907 : Blo 654306 654907 := bstep (se 1 (by rfl) ⟨491180, by rfl⟩ : syracuseStep 654907 = 982361) B982361
theorem B3145283 : Blo 654306 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B982601 : Blo 654306 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B654983 : Blo 654306 654983 := bstep (se 1 (by rfl) ⟨491237, by rfl⟩ : syracuseStep 654983 = 982475) B982475
theorem B654991 : Blo 654306 654991 := bstep (se 1 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 654991 = 982487) B982487
theorem B884395 : Blo 654306 884395 := bstep (se 1 (by rfl) ⟨663296, by rfl⟩ : syracuseStep 884395 = 1326593) B1326593
theorem B8421043 : Blo 654306 8421043 := bstep (se 1 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 8421043 = 12631565) B12631565
theorem B655035 : Blo 654306 655035 := bstep (se 1 (by rfl) ⟨491276, by rfl⟩ : syracuseStep 655035 = 982553) B982553
theorem B982715 : Blo 654306 982715 := bstep (se 1 (by rfl) ⟨737036, by rfl⟩ : syracuseStep 982715 = 1474073) B1474073
theorem B982775 : Blo 654306 982775 := bstep (se 1 (by rfl) ⟨737081, by rfl⟩ : syracuseStep 982775 = 1474163) B1474163
theorem B655111 : Blo 654306 655111 := bstep (se 1 (by rfl) ⟨491333, by rfl⟩ : syracuseStep 655111 = 982667) B982667
theorem B3538703 : Blo 654306 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B655119 : Blo 654306 655119 := bstep (se 1 (by rfl) ⟨491339, by rfl⟩ : syracuseStep 655119 = 982679) B982679
theorem B982799 : Blo 654306 982799 := bstep (se 1 (by rfl) ⟨737099, by rfl⟩ : syracuseStep 982799 = 1474199) B1474199
theorem B26935091 : Blo 654306 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B982841 : Blo 654306 982841 := bstep (se 2 (by rfl) ⟨368565, by rfl⟩ : syracuseStep 982841 = 737131) B737131
theorem B655163 : Blo 654306 655163 := bstep (se 1 (by rfl) ⟨491372, by rfl⟩ : syracuseStep 655163 = 982745) B982745
theorem B1867607 : Blo 654306 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B655239 : Blo 654306 655239 := bstep (se 1 (by rfl) ⟨491429, by rfl⟩ : syracuseStep 655239 = 982859) B982859
theorem B982919 : Blo 654306 982919 := bstep (se 1 (by rfl) ⟨737189, by rfl⟩ : syracuseStep 982919 = 1474379) B1474379
theorem B655247 : Blo 654306 655247 := bstep (se 1 (by rfl) ⟨491435, by rfl⟩ : syracuseStep 655247 = 982871) B982871
theorem B1474451 : Blo 654306 1474451 := bstep (se 1 (by rfl) ⟨1105838, by rfl⟩ : syracuseStep 1474451 = 2211677) B2211677
theorem B2097049 : Blo 654306 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B982955 : Blo 654306 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B655291 : Blo 654306 655291 := bstep (se 1 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 655291 = 982937) B982937
theorem B982985 : Blo 654306 982985 := bstep (se 2 (by rfl) ⟨368619, by rfl⟩ : syracuseStep 982985 = 737239) B737239
theorem B1474505 : Blo 654306 1474505 := bstep (se 2 (by rfl) ⟨552939, by rfl⟩ : syracuseStep 1474505 = 1105879) B1105879
theorem B5668879 : Blo 654306 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B655399 : Blo 654306 655399 := bstep (se 1 (by rfl) ⟨491549, by rfl⟩ : syracuseStep 655399 = 983099) B983099
theorem B1245223 : Blo 654306 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B655439 : Blo 654306 655439 := bstep (se 1 (by rfl) ⟨491579, by rfl⟩ : syracuseStep 655439 = 983159) B983159
theorem B655455 : Blo 654306 655455 := bstep (se 1 (by rfl) ⟨491591, by rfl⟩ : syracuseStep 655455 = 983183) B983183
theorem B655483 : Blo 654306 655483 := bstep (se 1 (by rfl) ⟨491612, by rfl⟩ : syracuseStep 655483 = 983225) B983225
theorem B1245307 : Blo 654306 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B1441963 : Blo 654306 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B655535 : Blo 654306 655535 := bstep (se 1 (by rfl) ⟨491651, by rfl⟩ : syracuseStep 655535 = 983303) B983303
theorem B655559 : Blo 654306 655559 := bstep (se 1 (by rfl) ⟨491669, by rfl⟩ : syracuseStep 655559 = 983339) B983339
theorem B655579 : Blo 654306 655579 := bstep (se 1 (by rfl) ⟨491684, by rfl⟩ : syracuseStep 655579 = 983369) B983369
theorem B655655 : Blo 654306 655655 := bstep (se 1 (by rfl) ⟨491741, by rfl⟩ : syracuseStep 655655 = 983483) B983483
theorem B655695 : Blo 654306 655695 := bstep (se 1 (by rfl) ⟨491771, by rfl⟩ : syracuseStep 655695 = 983543) B983543
theorem B655711 : Blo 654306 655711 := bstep (se 1 (by rfl) ⟨491783, by rfl⟩ : syracuseStep 655711 = 983567) B983567
theorem B655739 : Blo 654306 655739 := bstep (se 1 (by rfl) ⟨491804, by rfl⟩ : syracuseStep 655739 = 983609) B983609
theorem B983471 : Blo 654306 983471 := bstep (se 1 (by rfl) ⟨737603, by rfl⟩ : syracuseStep 983471 = 1475207) B1475207
theorem B655791 : Blo 654306 655791 := bstep (se 1 (by rfl) ⟨491843, by rfl⟩ : syracuseStep 655791 = 983687) B983687
theorem B655815 : Blo 654306 655815 := bstep (se 1 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 655815 = 983723) B983723
theorem B5046731 : Blo 654306 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B655835 : Blo 654306 655835 := bstep (se 1 (by rfl) ⟨491876, by rfl⟩ : syracuseStep 655835 = 983753) B983753
theorem B1475081 : Blo 654306 1475081 := bstep (se 2 (by rfl) ⟨553155, by rfl⟩ : syracuseStep 1475081 = 1106311) B1106311
theorem B983561 : Blo 654306 983561 := bstep (se 2 (by rfl) ⟨368835, by rfl⟩ : syracuseStep 983561 = 737671) B737671
theorem B983591 : Blo 654306 983591 := bstep (se 1 (by rfl) ⟨737693, by rfl⟩ : syracuseStep 983591 = 1475387) B1475387
theorem B655911 : Blo 654306 655911 := bstep (se 1 (by rfl) ⟨491933, by rfl⟩ : syracuseStep 655911 = 983867) B983867
theorem B655951 : Blo 654306 655951 := bstep (se 1 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 655951 = 983927) B983927
theorem B655967 : Blo 654306 655967 := bstep (se 1 (by rfl) ⟨491975, by rfl⟩ : syracuseStep 655967 = 983951) B983951
theorem B1245793 : Blo 654306 1245793 := bstep (se 2 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 1245793 = 934345) B934345
theorem B983675 : Blo 654306 983675 := bstep (se 1 (by rfl) ⟨737756, by rfl⟩ : syracuseStep 983675 = 1475513) B1475513
theorem B655995 : Blo 654306 655995 := bstep (se 1 (by rfl) ⟨491996, by rfl⟩ : syracuseStep 655995 = 983993) B983993
theorem B4260487 : Blo 654306 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B656047 : Blo 654306 656047 := bstep (se 1 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 656047 = 984071) B984071
theorem B656071 : Blo 654306 656071 := bstep (se 1 (by rfl) ⟨492053, by rfl⟩ : syracuseStep 656071 = 984107) B984107
theorem B656091 : Blo 654306 656091 := bstep (se 1 (by rfl) ⟨492068, by rfl⟩ : syracuseStep 656091 = 984137) B984137
theorem B983801 : Blo 654306 983801 := bstep (se 2 (by rfl) ⟨368925, by rfl⟩ : syracuseStep 983801 = 737851) B737851
theorem B656167 : Blo 654306 656167 := bstep (se 1 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 656167 = 984251) B984251
theorem B4195145 : Blo 654306 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B656207 : Blo 654306 656207 := bstep (se 1 (by rfl) ⟨492155, by rfl⟩ : syracuseStep 656207 = 984311) B984311
theorem B1475423 : Blo 654306 1475423 := bstep (se 1 (by rfl) ⟨1106567, by rfl⟩ : syracuseStep 1475423 = 2213135) B2213135
theorem B983903 : Blo 654306 983903 := bstep (se 1 (by rfl) ⟨737927, by rfl⟩ : syracuseStep 983903 = 1475855) B1475855
theorem B656223 : Blo 654306 656223 := bstep (se 1 (by rfl) ⟨492167, by rfl⟩ : syracuseStep 656223 = 984335) B984335
theorem B983915 : Blo 654306 983915 := bstep (se 1 (by rfl) ⟨737936, by rfl⟩ : syracuseStep 983915 = 1475873) B1475873
theorem B656251 : Blo 654306 656251 := bstep (se 1 (by rfl) ⟨492188, by rfl⟩ : syracuseStep 656251 = 984377) B984377
theorem B656303 : Blo 654306 656303 := bstep (se 1 (by rfl) ⟨492227, by rfl⟩ : syracuseStep 656303 = 984455) B984455
theorem B656327 : Blo 654306 656327 := bstep (se 1 (by rfl) ⟨492245, by rfl⟩ : syracuseStep 656327 = 984491) B984491
theorem B656347 : Blo 654306 656347 := bstep (se 1 (by rfl) ⟨492260, by rfl⟩ : syracuseStep 656347 = 984521) B984521
theorem B1475603 : Blo 654306 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B656423 : Blo 654306 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B984143 : Blo 654306 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B656463 : Blo 654306 656463 := bstep (se 1 (by rfl) ⟨492347, by rfl⟩ : syracuseStep 656463 = 984695) B984695
theorem B656479 : Blo 654306 656479 := bstep (se 1 (by rfl) ⟨492359, by rfl⟩ : syracuseStep 656479 = 984719) B984719
theorem B656507 : Blo 654306 656507 := bstep (se 1 (by rfl) ⟨492380, by rfl⟩ : syracuseStep 656507 = 984761) B984761
theorem B656559 : Blo 654306 656559 := bstep (se 1 (by rfl) ⟨492419, by rfl⟩ : syracuseStep 656559 = 984839) B984839
theorem B984263 : Blo 654306 984263 := bstep (se 1 (by rfl) ⟨738197, by rfl⟩ : syracuseStep 984263 = 1476395) B1476395
theorem B656583 : Blo 654306 656583 := bstep (se 1 (by rfl) ⟨492437, by rfl⟩ : syracuseStep 656583 = 984875) B984875
theorem B656603 : Blo 654306 656603 := bstep (se 1 (by rfl) ⟨492452, by rfl⟩ : syracuseStep 656603 = 984905) B984905
theorem B656679 : Blo 654306 656679 := bstep (se 1 (by rfl) ⟨492509, by rfl⟩ : syracuseStep 656679 = 985019) B985019
theorem B31950125 : Blo 654306 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B656719 : Blo 654306 656719 := bstep (se 1 (by rfl) ⟨492539, by rfl⟩ : syracuseStep 656719 = 985079) B985079
theorem B656735 : Blo 654306 656735 := bstep (se 1 (by rfl) ⟨492551, by rfl⟩ : syracuseStep 656735 = 985103) B985103
theorem B1475945 : Blo 654306 1475945 := bstep (se 2 (by rfl) ⟨553479, by rfl⟩ : syracuseStep 1475945 = 1106959) B1106959
theorem B984425 : Blo 654306 984425 := bstep (se 2 (by rfl) ⟨369159, by rfl⟩ : syracuseStep 984425 = 738319) B738319
theorem B656763 : Blo 654306 656763 := bstep (se 1 (by rfl) ⟨492572, by rfl⟩ : syracuseStep 656763 = 985145) B985145
theorem B656815 : Blo 654306 656815 := bstep (se 1 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 656815 = 985223) B985223
theorem B984503 : Blo 654306 984503 := bstep (se 1 (by rfl) ⟨738377, by rfl⟩ : syracuseStep 984503 = 1476755) B1476755
theorem B656839 : Blo 654306 656839 := bstep (se 1 (by rfl) ⟨492629, by rfl⟩ : syracuseStep 656839 = 985259) B985259
theorem B1181147 : Blo 654306 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B984539 : Blo 654306 984539 := bstep (se 1 (by rfl) ⟨738404, by rfl⟩ : syracuseStep 984539 = 1476809) B1476809
theorem B656859 : Blo 654306 656859 := bstep (se 1 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 656859 = 985289) B985289
theorem B1246727 : Blo 654306 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B656935 : Blo 654306 656935 := bstep (se 1 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 656935 = 985403) B985403
theorem B1181263 : Blo 654306 1181263 := bstep (se 1 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 1181263 = 1771895) B1771895
theorem B656975 : Blo 654306 656975 := bstep (se 1 (by rfl) ⟨492731, by rfl⟩ : syracuseStep 656975 = 985463) B985463
theorem B656991 : Blo 654306 656991 := bstep (se 1 (by rfl) ⟨492743, by rfl⟩ : syracuseStep 656991 = 985487) B985487
theorem B657019 : Blo 654306 657019 := bstep (se 1 (by rfl) ⟨492764, by rfl⟩ : syracuseStep 657019 = 985529) B985529
theorem B657071 : Blo 654306 657071 := bstep (se 1 (by rfl) ⟨492803, by rfl⟩ : syracuseStep 657071 = 985607) B985607
theorem B4982471 : Blo 654306 4982471 := bstep (se 1 (by rfl) ⟨3736853, by rfl⟩ : syracuseStep 4982471 = 7473707) B7473707
theorem B657095 : Blo 654306 657095 := bstep (se 1 (by rfl) ⟨492821, by rfl⟩ : syracuseStep 657095 = 985643) B985643
theorem B657115 : Blo 654306 657115 := bstep (se 1 (by rfl) ⟨492836, by rfl⟩ : syracuseStep 657115 = 985673) B985673
theorem B6162169 : Blo 654306 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B657191 : Blo 654306 657191 := bstep (se 1 (by rfl) ⟨492893, by rfl⟩ : syracuseStep 657191 = 985787) B985787
theorem B657231 : Blo 654306 657231 := bstep (se 1 (by rfl) ⟨492923, by rfl⟩ : syracuseStep 657231 = 985847) B985847
theorem B657247 : Blo 654306 657247 := bstep (se 1 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 657247 = 985871) B985871
theorem B657275 : Blo 654306 657275 := bstep (se 1 (by rfl) ⟨492956, by rfl⟩ : syracuseStep 657275 = 985913) B985913
theorem B985007 : Blo 654306 985007 := bstep (se 1 (by rfl) ⟨738755, by rfl⟩ : syracuseStep 985007 = 1477511) B1477511
theorem B657327 : Blo 654306 657327 := bstep (se 1 (by rfl) ⟨492995, by rfl⟩ : syracuseStep 657327 = 985991) B985991
theorem B1476539 : Blo 654306 1476539 := bstep (se 1 (by rfl) ⟨1107404, by rfl⟩ : syracuseStep 1476539 = 2214809) B2214809
theorem B657351 : Blo 654306 657351 := bstep (se 1 (by rfl) ⟨493013, by rfl⟩ : syracuseStep 657351 = 986027) B986027
theorem B657371 : Blo 654306 657371 := bstep (se 1 (by rfl) ⟨493028, by rfl⟩ : syracuseStep 657371 = 986057) B986057
theorem B985097 : Blo 654306 985097 := bstep (se 2 (by rfl) ⟨369411, by rfl⟩ : syracuseStep 985097 = 738823) B738823
theorem B1247251 : Blo 654306 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B985127 : Blo 654306 985127 := bstep (se 1 (by rfl) ⟨738845, by rfl⟩ : syracuseStep 985127 = 1477691) B1477691
theorem B657447 : Blo 654306 657447 := bstep (se 1 (by rfl) ⟨493085, by rfl⟩ : syracuseStep 657447 = 986171) B986171
theorem B1476665 : Blo 654306 1476665 := bstep (se 2 (by rfl) ⟨553749, by rfl⟩ : syracuseStep 1476665 = 1107499) B1107499
theorem B657487 : Blo 654306 657487 := bstep (se 1 (by rfl) ⟨493115, by rfl⟩ : syracuseStep 657487 = 986231) B986231
theorem B657503 : Blo 654306 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B2099315 : Blo 654306 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B985211 : Blo 654306 985211 := bstep (se 1 (by rfl) ⟨738908, by rfl⟩ : syracuseStep 985211 = 1477817) B1477817
theorem B657531 : Blo 654306 657531 := bstep (se 1 (by rfl) ⟨493148, by rfl⟩ : syracuseStep 657531 = 986297) B986297
theorem B657583 : Blo 654306 657583 := bstep (se 1 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 657583 = 986375) B986375
theorem B657607 : Blo 654306 657607 := bstep (se 1 (by rfl) ⟨493205, by rfl⟩ : syracuseStep 657607 = 986411) B986411
theorem B657627 : Blo 654306 657627 := bstep (se 1 (by rfl) ⟨493220, by rfl⟩ : syracuseStep 657627 = 986441) B986441
theorem B985337 : Blo 654306 985337 := bstep (se 2 (by rfl) ⟨369501, by rfl⟩ : syracuseStep 985337 = 739003) B739003
theorem B657703 : Blo 654306 657703 := bstep (se 1 (by rfl) ⟨493277, by rfl⟩ : syracuseStep 657703 = 986555) B986555
theorem B9439537 : Blo 654306 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B6064433 : Blo 654306 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B657743 : Blo 654306 657743 := bstep (se 1 (by rfl) ⟨493307, by rfl⟩ : syracuseStep 657743 = 986615) B986615
theorem B985439 : Blo 654306 985439 := bstep (se 1 (by rfl) ⟨739079, by rfl⟩ : syracuseStep 985439 = 1478159) B1478159
theorem B657759 : Blo 654306 657759 := bstep (se 1 (by rfl) ⟨493319, by rfl⟩ : syracuseStep 657759 = 986639) B986639
theorem B1050985 : Blo 654306 1050985 := bstep (se 2 (by rfl) ⟨394119, by rfl⟩ : syracuseStep 1050985 = 788239) B788239
theorem B985451 : Blo 654306 985451 := bstep (se 1 (by rfl) ⟨739088, by rfl⟩ : syracuseStep 985451 = 1478177) B1478177
theorem B657787 : Blo 654306 657787 := bstep (se 1 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 657787 = 986681) B986681
theorem B2492801 : Blo 654306 2492801 := bstep (se 2 (by rfl) ⟨934800, by rfl⟩ : syracuseStep 2492801 = 1869601) B1869601
theorem B1477007 : Blo 654306 1477007 := bstep (se 1 (by rfl) ⟨1107755, by rfl⟩ : syracuseStep 1477007 = 2215511) B2215511
theorem B2492815 : Blo 654306 2492815 := bstep (se 1 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 2492815 = 3739223) B3739223
theorem B17074583 : Blo 654306 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B657839 : Blo 654306 657839 := bstep (se 1 (by rfl) ⟨493379, by rfl⟩ : syracuseStep 657839 = 986759) B986759
theorem B657863 : Blo 654306 657863 := bstep (se 1 (by rfl) ⟨493397, by rfl⟩ : syracuseStep 657863 = 986795) B986795
theorem B2099675 : Blo 654306 2099675 := bstep (se 1 (by rfl) ⟨1574756, by rfl⟩ : syracuseStep 2099675 = 3149513) B3149513
theorem B657883 : Blo 654306 657883 := bstep (se 1 (by rfl) ⟨493412, by rfl⟩ : syracuseStep 657883 = 986825) B986825
theorem B657959 : Blo 654306 657959 := bstep (se 1 (by rfl) ⟨493469, by rfl⟩ : syracuseStep 657959 = 986939) B986939
theorem B985679 : Blo 654306 985679 := bstep (se 1 (by rfl) ⟨739259, by rfl⟩ : syracuseStep 985679 = 1478519) B1478519
theorem B657999 : Blo 654306 657999 := bstep (se 1 (by rfl) ⟨493499, by rfl⟩ : syracuseStep 657999 = 986999) B986999
theorem B658015 : Blo 654306 658015 := bstep (se 1 (by rfl) ⟨493511, by rfl⟩ : syracuseStep 658015 = 987023) B987023
theorem B658043 : Blo 654306 658043 := bstep (se 1 (by rfl) ⟨493532, by rfl⟩ : syracuseStep 658043 = 987065) B987065
theorem B658095 : Blo 654306 658095 := bstep (se 1 (by rfl) ⟨493571, by rfl⟩ : syracuseStep 658095 = 987143) B987143
theorem B985799 : Blo 654306 985799 := bstep (se 1 (by rfl) ⟨739349, by rfl⟩ : syracuseStep 985799 = 1478699) B1478699
theorem B658119 : Blo 654306 658119 := bstep (se 1 (by rfl) ⟨493589, by rfl⟩ : syracuseStep 658119 = 987179) B987179
theorem B1477331 : Blo 654306 1477331 := bstep (se 1 (by rfl) ⟨1107998, by rfl⟩ : syracuseStep 1477331 = 2215997) B2215997
theorem B658139 : Blo 654306 658139 := bstep (se 1 (by rfl) ⟨493604, by rfl⟩ : syracuseStep 658139 = 987209) B987209
theorem B658215 : Blo 654306 658215 := bstep (se 1 (by rfl) ⟨493661, by rfl⟩ : syracuseStep 658215 = 987323) B987323
theorem B658255 : Blo 654306 658255 := bstep (se 1 (by rfl) ⟨493691, by rfl⟩ : syracuseStep 658255 = 987383) B987383
theorem B658271 : Blo 654306 658271 := bstep (se 1 (by rfl) ⟨493703, by rfl⟩ : syracuseStep 658271 = 987407) B987407
theorem B985961 : Blo 654306 985961 := bstep (se 2 (by rfl) ⟨369735, by rfl⟩ : syracuseStep 985961 = 739471) B739471
theorem B658299 : Blo 654306 658299 := bstep (se 1 (by rfl) ⟨493724, by rfl⟩ : syracuseStep 658299 = 987449) B987449
theorem B986039 : Blo 654306 986039 := bstep (se 1 (by rfl) ⟨739529, by rfl⟩ : syracuseStep 986039 = 1479059) B1479059
theorem B986075 : Blo 654306 986075 := bstep (se 1 (by rfl) ⟨739556, by rfl⟩ : syracuseStep 986075 = 1479113) B1479113
theorem B2100239 : Blo 654306 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B5049715 : Blo 654306 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B986543 : Blo 654306 986543 := bstep (se 1 (by rfl) ⟨739907, by rfl⟩ : syracuseStep 986543 = 1479815) B1479815
theorem B888283 : Blo 654306 888283 := bstep (se 1 (by rfl) ⟨666212, by rfl⟩ : syracuseStep 888283 = 1332425) B1332425
theorem B986633 : Blo 654306 986633 := bstep (se 2 (by rfl) ⟨369987, by rfl⟩ : syracuseStep 986633 = 739975) B739975
theorem B986663 : Blo 654306 986663 := bstep (se 1 (by rfl) ⟨739997, by rfl⟩ : syracuseStep 986663 = 1479995) B1479995
theorem B3149435 : Blo 654306 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B1478267 : Blo 654306 1478267 := bstep (se 1 (by rfl) ⟨1108700, by rfl⟩ : syracuseStep 1478267 = 2217401) B2217401
theorem B986747 : Blo 654306 986747 := bstep (se 1 (by rfl) ⟨740060, by rfl⟩ : syracuseStep 986747 = 1480121) B1480121
theorem B2494091 : Blo 654306 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1183403 : Blo 654306 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B1871549 : Blo 654306 1871549 := bstep (se 3 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 1871549 = 701831) B701831
theorem B1478393 : Blo 654306 1478393 := bstep (se 2 (by rfl) ⟨554397, by rfl⟩ : syracuseStep 1478393 = 1108795) B1108795
theorem B986873 : Blo 654306 986873 := bstep (se 2 (by rfl) ⟨370077, by rfl⟩ : syracuseStep 986873 = 740155) B740155
theorem B986975 : Blo 654306 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B986987 : Blo 654306 986987 := bstep (se 1 (by rfl) ⟨740240, by rfl⟩ : syracuseStep 986987 = 1480481) B1480481
theorem B1183663 : Blo 654306 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B1478663 : Blo 654306 1478663 := bstep (se 1 (by rfl) ⟨1108997, by rfl⟩ : syracuseStep 1478663 = 2217995) B2217995
theorem B1478735 : Blo 654306 1478735 := bstep (se 1 (by rfl) ⟨1109051, by rfl⟩ : syracuseStep 1478735 = 2218103) B2218103
theorem B987215 : Blo 654306 987215 := bstep (se 1 (by rfl) ⟨740411, by rfl⟩ : syracuseStep 987215 = 1480823) B1480823
theorem B10621043 : Blo 654306 10621043 := bstep (se 1 (by rfl) ⟨7965782, by rfl⟩ : syracuseStep 10621043 = 15931565) B15931565
theorem B987335 : Blo 654306 987335 := bstep (se 1 (by rfl) ⟨740501, by rfl⟩ : syracuseStep 987335 = 1481003) B1481003
theorem B5050673 : Blo 654306 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B1249643 : Blo 654306 1249643 := bstep (se 1 (by rfl) ⟨937232, by rfl⟩ : syracuseStep 1249643 = 1874465) B1874465
theorem B1479131 : Blo 654306 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B14160689 : Blo 654306 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B1479599 : Blo 654306 1479599 := bstep (se 1 (by rfl) ⟨1109699, by rfl⟩ : syracuseStep 1479599 = 2219399) B2219399
theorem B19502045 : Blo 654306 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B1479851 : Blo 654306 1479851 := bstep (se 1 (by rfl) ⟨1109888, by rfl⟩ : syracuseStep 1479851 = 2219777) B2219777
theorem B1480391 : Blo 654306 1480391 := bstep (se 1 (by rfl) ⟨1110293, by rfl⟩ : syracuseStep 1480391 = 2220587) B2220587
theorem B1578707 : Blo 654306 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B21305389 : Blo 654306 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B1874441 : Blo 654306 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B2365985 : Blo 654306 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B1776251 : Blo 654306 1776251 := bstep (se 1 (by rfl) ⟨1332188, by rfl⟩ : syracuseStep 1776251 = 2664377) B2664377
theorem B4201145 : Blo 654306 4201145 := bstep (se 2 (by rfl) ⟨1575429, by rfl⟩ : syracuseStep 4201145 = 3150859) B3150859
theorem B5970833 : Blo 654306 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B2661295 : Blo 654306 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B2497463 : Blo 654306 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B2104339 : Blo 654306 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B3316787 : Blo 654306 3316787 := bstep (se 1 (by rfl) ⟨2487590, by rfl⟩ : syracuseStep 3316787 = 4975181) B4975181
theorem B5315777 : Blo 654306 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B4988303 : Blo 654306 4988303 := bstep (se 1 (by rfl) ⟨3741227, by rfl⟩ : syracuseStep 4988303 = 7482455) B7482455
theorem B3743597 : Blo 654306 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B5316461 : Blo 654306 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B2498465 : Blo 654306 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B5054393 : Blo 654306 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B663751 : Blo 654306 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B1351927 : Blo 654306 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2498921 : Blo 654306 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B2105801 : Blo 654306 2105801 := bstep (se 2 (by rfl) ⟨789675, by rfl⟩ : syracuseStep 2105801 = 1579351) B1579351
theorem B3318407 : Blo 654306 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B4727497 : Blo 654306 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B2106071 : Blo 654306 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B2499437 : Blo 654306 2499437 := bstep (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) B937289
theorem B2106287 : Blo 654306 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B8954945 : Blo 654306 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B53880025 : Blo 654306 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B2106749 : Blo 654306 2106749 := bstep (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) B790031
theorem B2664083 : Blo 654306 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B13510489 : Blo 654306 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B3319865 : Blo 654306 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B2369803 : Blo 654306 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B2796065 : Blo 654306 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B4205191 : Blo 654306 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B3746513 : Blo 654306 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B830503 : Blo 654306 830503 := bstep (se 1 (by rfl) ⟨622877, by rfl⟩ : syracuseStep 830503 = 1245755) B1245755
theorem B2108531 : Blo 654306 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B3746969 : Blo 654306 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B3157163 : Blo 654306 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B51064123 : Blo 654306 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B830827 : Blo 654306 830827 := bstep (se 1 (by rfl) ⟨623120, by rfl⟩ : syracuseStep 830827 = 1246241) B1246241
theorem B699823 : Blo 654306 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B831055 : Blo 654306 831055 := bstep (se 1 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 831055 = 1246583) B1246583
theorem B4206269 : Blo 654306 4206269 := bstep (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) B1577351
theorem B2797379 : Blo 654306 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B2994029 : Blo 654306 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B3321971 : Blo 654306 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B7483913 : Blo 654306 7483913 := bstep (se 2 (by rfl) ⟨2806467, by rfl⟩ : syracuseStep 7483913 = 5612935) B5612935
theorem B832123 : Blo 654306 832123 := bstep (se 1 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 832123 = 1248185) B1248185
theorem B832351 : Blo 654306 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B3781559 : Blo 654306 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B996551 : Blo 654306 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B6304985 : Blo 654306 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B3749111 : Blo 654306 3749111 := bstep (se 1 (by rfl) ⟨2811833, by rfl⟩ : syracuseStep 3749111 = 5623667) B5623667
theorem B4207909 : Blo 654306 4207909 := bstep (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) B788983
theorem B2209085 : Blo 654306 2209085 := bstep (se 3 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 2209085 = 828407) B828407
theorem B3028367 : Blo 654306 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B832943 : Blo 654306 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B4994621 : Blo 654306 4994621 := bstep (se 3 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 4994621 = 1872983) B1872983
theorem B4208267 : Blo 654306 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B3323591 : Blo 654306 3323591 := bstep (se 1 (by rfl) ⟨2492693, by rfl⟩ : syracuseStep 3323591 = 4985387) B4985387
theorem B2668625 : Blo 654306 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B2209949 : Blo 654306 2209949 := bstep (se 3 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 2209949 = 828731) B828731
theorem B16005509 : Blo 654306 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B4995593 : Blo 654306 4995593 := bstep (se 2 (by rfl) ⟨1873347, by rfl⟩ : syracuseStep 4995593 = 3746695) B3746695
theorem B2210489 : Blo 654306 2210489 := bstep (se 2 (by rfl) ⟨828933, by rfl⟩ : syracuseStep 2210489 = 1657867) B1657867
theorem B3980215 : Blo 654306 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B998363 : Blo 654306 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B4734071 : Blo 654306 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B2211083 : Blo 654306 2211083 := bstep (se 1 (by rfl) ⟨1658312, by rfl⟩ : syracuseStep 2211083 = 3316625) B3316625
theorem B2211353 : Blo 654306 2211353 := bstep (se 2 (by rfl) ⟨829257, by rfl⟩ : syracuseStep 2211353 = 1658515) B1658515
theorem B736807 : Blo 654306 736807 := bstep (se 1 (by rfl) ⟨552605, by rfl⟩ : syracuseStep 736807 = 1105211) B1105211
theorem B933815 : Blo 654306 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B4997051 : Blo 654306 4997051 := bstep (se 1 (by rfl) ⟨3747788, by rfl⟩ : syracuseStep 4997051 = 7495577) B7495577
theorem B5980175 : Blo 654306 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B3293729 : Blo 654306 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B2212487 : Blo 654306 2212487 := bstep (se 1 (by rfl) ⟨1659365, by rfl⟩ : syracuseStep 2212487 = 3318731) B3318731
theorem B2212541 : Blo 654306 2212541 := bstep (se 3 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 2212541 = 829703) B829703
theorem B3195677 : Blo 654306 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B2212703 : Blo 654306 2212703 := bstep (se 1 (by rfl) ⟨1659527, by rfl⟩ : syracuseStep 2212703 = 3319055) B3319055
theorem B2802539 : Blo 654306 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B2212865 : Blo 654306 2212865 := bstep (se 2 (by rfl) ⟨829824, by rfl⟩ : syracuseStep 2212865 = 1659649) B1659649
theorem B1000487 : Blo 654306 1000487 := bstep (se 1 (by rfl) ⟨750365, by rfl⟩ : syracuseStep 1000487 = 1500731) B1500731
theorem B738427 : Blo 654306 738427 := bstep (se 1 (by rfl) ⟨553820, by rfl⟩ : syracuseStep 738427 = 1107641) B1107641
theorem B1197227 : Blo 654306 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B2999467 : Blo 654306 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B935273 : Blo 654306 935273 := bstep (se 2 (by rfl) ⟨350727, by rfl⟩ : syracuseStep 935273 = 701455) B701455
theorem B2803187 : Blo 654306 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B1656359 : Blo 654306 1656359 := bstep (se 1 (by rfl) ⟨1242269, by rfl⟩ : syracuseStep 1656359 = 2484539) B2484539
theorem B1263161 : Blo 654306 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B738895 : Blo 654306 738895 := bstep (se 1 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 738895 = 1108343) B1108343
theorem B2213675 : Blo 654306 2213675 := bstep (se 1 (by rfl) ⟨1660256, by rfl⟩ : syracuseStep 2213675 = 3320513) B3320513
theorem B1656683 : Blo 654306 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B739291 : Blo 654306 739291 := bstep (se 1 (by rfl) ⟨554468, by rfl⟩ : syracuseStep 739291 = 1108937) B1108937
theorem B2213945 : Blo 654306 2213945 := bstep (se 2 (by rfl) ⟨830229, by rfl⟩ : syracuseStep 2213945 = 1660459) B1660459
theorem B2214269 : Blo 654306 2214269 := bstep (se 3 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 2214269 = 830351) B830351
theorem B739759 : Blo 654306 739759 := bstep (se 1 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 739759 = 1109639) B1109639
theorem B1657331 : Blo 654306 1657331 := bstep (se 1 (by rfl) ⟨1242998, by rfl⟩ : syracuseStep 1657331 = 2485997) B2485997
theorem B2214539 : Blo 654306 2214539 := bstep (se 1 (by rfl) ⟨1660904, by rfl⟩ : syracuseStep 2214539 = 3321809) B3321809
theorem B1657543 : Blo 654306 1657543 := bstep (se 1 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 1657543 = 2486315) B2486315
theorem B936697 : Blo 654306 936697 := bstep (se 2 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 936697 = 702523) B702523
theorem B31148875 : Blo 654306 31148875 := bstep (se 1 (by rfl) ⟨23361656, by rfl⟩ : syracuseStep 31148875 = 46723313) B46723313
theorem B740191 : Blo 654306 740191 := bstep (se 1 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 740191 = 1110287) B1110287
theorem B18959345 : Blo 654306 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B740551 : Blo 654306 740551 := bstep (se 1 (by rfl) ⟨555413, by rfl⟩ : syracuseStep 740551 = 1110827) B1110827
theorem B3329423 : Blo 654306 3329423 := bstep (se 1 (by rfl) ⟨2497067, by rfl⟩ : syracuseStep 3329423 = 4994135) B4994135
theorem B1330615 : Blo 654306 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B2215457 : Blo 654306 2215457 := bstep (se 2 (by rfl) ⟨830796, by rfl⟩ : syracuseStep 2215457 = 1661593) B1661593
theorem B1658465 : Blo 654306 1658465 := bstep (se 2 (by rfl) ⟨621924, by rfl⟩ : syracuseStep 1658465 = 1243849) B1243849
theorem B2215673 : Blo 654306 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B2215943 : Blo 654306 2215943 := bstep (se 1 (by rfl) ⟨1661957, by rfl⟩ : syracuseStep 2215943 = 3323915) B3323915
theorem B2216051 : Blo 654306 2216051 := bstep (se 1 (by rfl) ⟨1662038, by rfl⟩ : syracuseStep 2216051 = 3324077) B3324077
theorem B8540477 : Blo 654306 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B3985793 : Blo 654306 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B2216321 : Blo 654306 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B1397459 : Blo 654306 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B6410963 : Blo 654306 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B43078501 : Blo 654306 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B11228057 : Blo 654306 11228057 := bstep (se 2 (by rfl) ⟨4210521, by rfl⟩ : syracuseStep 11228057 = 8421043) B8421043
theorem B1659923 : Blo 654306 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B2217131 : Blo 654306 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B3331529 : Blo 654306 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B2217671 : Blo 654306 2217671 := bstep (se 1 (by rfl) ⟨1663253, by rfl⟩ : syracuseStep 2217671 = 3326507) B3326507
theorem B1332983 : Blo 654306 1332983 := bstep (se 1 (by rfl) ⟨999737, by rfl⟩ : syracuseStep 1332983 = 1999475) B1999475
theorem B6313787 : Blo 654306 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B145446731 : Blo 654306 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B4741051 : Blo 654306 4741051 := bstep (se 1 (by rfl) ⟨3555788, by rfl⟩ : syracuseStep 4741051 = 7111577) B7111577
theorem B3332177 : Blo 654306 3332177 := bstep (se 2 (by rfl) ⟨1249566, by rfl⟩ : syracuseStep 3332177 = 2499133) B2499133
theorem B1104347 : Blo 654306 1104347 := bstep (se 1 (by rfl) ⟨828260, by rfl⟩ : syracuseStep 1104347 = 1656521) B1656521
theorem B2218535 : Blo 654306 2218535 := bstep (se 1 (by rfl) ⟨1663901, by rfl⟩ : syracuseStep 2218535 = 3327803) B3327803
theorem B2218643 : Blo 654306 2218643 := bstep (se 1 (by rfl) ⟨1663982, by rfl⟩ : syracuseStep 2218643 = 3327965) B3327965
theorem B1104583 : Blo 654306 1104583 := bstep (se 1 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 1104583 = 1656875) B1656875
theorem B4971293 : Blo 654306 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B1104745 : Blo 654306 1104745 := bstep (se 2 (by rfl) ⟨414279, by rfl⟩ : syracuseStep 1104745 = 828559) B828559
theorem B2218859 : Blo 654306 2218859 := bstep (se 1 (by rfl) ⟨1664144, by rfl⟩ : syracuseStep 2218859 = 3328289) B3328289
theorem B2218913 : Blo 654306 2218913 := bstep (se 2 (by rfl) ⟨832092, by rfl⟩ : syracuseStep 2218913 = 1664185) B1664185
theorem B1105339 : Blo 654306 1105339 := bstep (se 1 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 1105339 = 1658009) B1658009
theorem B2219507 : Blo 654306 2219507 := bstep (se 1 (by rfl) ⟨1664630, by rfl⟩ : syracuseStep 2219507 = 3329261) B3329261
theorem B1105447 : Blo 654306 1105447 := bstep (se 1 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 1105447 = 1658171) B1658171
theorem B11951887 : Blo 654306 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B9002785 : Blo 654306 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B1105771 : Blo 654306 1105771 := bstep (se 1 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 1105771 = 1658657) B1658657
theorem B2220047 : Blo 654306 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B1663375 : Blo 654306 1663375 := bstep (se 1 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 1663375 = 2495063) B2495063
theorem B2220641 : Blo 654306 2220641 := bstep (se 2 (by rfl) ⟨832740, by rfl⟩ : syracuseStep 2220641 = 1665481) B1665481
theorem B1663699 : Blo 654306 1663699 := bstep (se 1 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 1663699 = 2495549) B2495549
theorem B35971913 : Blo 654306 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1106831 : Blo 654306 1106831 := bstep (se 1 (by rfl) ⟨830123, by rfl⟩ : syracuseStep 1106831 = 1660247) B1660247
theorem B11953271 : Blo 654306 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B1107067 : Blo 654306 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B551380229 : Blo 654306 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B10118641 : Blo 654306 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1664651 : Blo 654306 1664651 := bstep (se 1 (by rfl) ⟨1248488, by rfl⟩ : syracuseStep 1664651 = 2496977) B2496977
theorem B3991457 : Blo 654306 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B1107931 : Blo 654306 1107931 := bstep (se 1 (by rfl) ⟨830948, by rfl⟩ : syracuseStep 1107931 = 1661897) B1661897
theorem B1534009 : Blo 654306 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B3729725 : Blo 654306 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B1108559 : Blo 654306 1108559 := bstep (se 1 (by rfl) ⟨831419, by rfl⟩ : syracuseStep 1108559 = 1662839) B1662839
theorem B1665785 : Blo 654306 1665785 := bstep (se 2 (by rfl) ⟨624669, by rfl⟩ : syracuseStep 1665785 = 1249339) B1249339
theorem B1665967 : Blo 654306 1665967 := bstep (se 1 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 1665967 = 2498951) B2498951
theorem B1895351 : Blo 654306 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B4975667 : Blo 654306 4975667 := bstep (se 1 (by rfl) ⟨3731750, by rfl⟩ : syracuseStep 4975667 = 7463501) B7463501
theorem B1109423 : Blo 654306 1109423 := bstep (se 1 (by rfl) ⟨832067, by rfl⟩ : syracuseStep 1109423 = 1664135) B1664135
theorem B3730931 : Blo 654306 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B2485799 : Blo 654306 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B4484753 : Blo 654306 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B1109855 : Blo 654306 1109855 := bstep (se 1 (by rfl) ⟨832391, by rfl⟩ : syracuseStep 1109855 = 1664783) B1664783
theorem B1404935 : Blo 654306 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B1110415 : Blo 654306 1110415 := bstep (se 1 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 1110415 = 1665623) B1665623
theorem B2486771 : Blo 654306 2486771 := bstep (se 1 (by rfl) ⟨1865078, by rfl⟩ : syracuseStep 2486771 = 3730157) B3730157
theorem B2486969 : Blo 654306 2486969 := bstep (se 2 (by rfl) ⟨932613, by rfl⟩ : syracuseStep 2486969 = 1865227) B1865227
theorem B2486983 : Blo 654306 2486983 := bstep (se 1 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 2486983 = 3730475) B3730475
theorem B10089521 : Blo 654306 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B1242209 : Blo 654306 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B2487955 : Blo 654306 2487955 := bstep (se 1 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 2487955 = 3731933) B3731933
theorem B1472363 : Blo 654306 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B1472417 : Blo 654306 1472417 := bstep (se 2 (by rfl) ⟨552156, by rfl⟩ : syracuseStep 1472417 = 1104313) B1104313
theorem B1472759 : Blo 654306 1472759 := bstep (se 1 (by rfl) ⟨1104569, by rfl⟩ : syracuseStep 1472759 = 2209139) B2209139
theorem B3733847 : Blo 654306 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B15989123 : Blo 654306 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B981467 : Blo 654306 981467 := bstep (se 1 (by rfl) ⟨736100, by rfl⟩ : syracuseStep 981467 = 1472201) B1472201
theorem B1243667 : Blo 654306 1243667 := bstep (se 1 (by rfl) ⟨932750, by rfl⟩ : syracuseStep 1243667 = 1865501) B1865501
theorem B7109153 : Blo 654306 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B2128531 : Blo 654306 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B1473353 : Blo 654306 1473353 := bstep (se 2 (by rfl) ⟨552507, by rfl⟩ : syracuseStep 1473353 = 1105015) B1105015
theorem B981935 : Blo 654306 981935 := bstep (se 1 (by rfl) ⟨736451, by rfl⟩ : syracuseStep 981935 = 1472903) B1472903
theorem B982025 : Blo 654306 982025 := bstep (se 2 (by rfl) ⟨368259, by rfl⟩ : syracuseStep 982025 = 736519) B736519
theorem B4193299 : Blo 654306 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B654375 : Blo 654306 654375 := bstep (se 1 (by rfl) ⟨490781, by rfl⟩ : syracuseStep 654375 = 981563) B981563
theorem B982055 : Blo 654306 982055 := bstep (se 1 (by rfl) ⟨736541, by rfl⟩ : syracuseStep 982055 = 1473083) B1473083
theorem B654415 : Blo 654306 654415 := bstep (se 1 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 654415 = 981623) B981623
theorem B654431 : Blo 654306 654431 := bstep (se 1 (by rfl) ⟨490823, by rfl⟩ : syracuseStep 654431 = 981647) B981647
theorem B654459 : Blo 654306 654459 := bstep (se 1 (by rfl) ⟨490844, by rfl⟩ : syracuseStep 654459 = 981689) B981689
theorem B982139 : Blo 654306 982139 := bstep (se 1 (by rfl) ⟨736604, by rfl⟩ : syracuseStep 982139 = 1473209) B1473209
theorem B654511 : Blo 654306 654511 := bstep (se 1 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 654511 = 981767) B981767
theorem B3144899 : Blo 654306 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B654535 : Blo 654306 654535 := bstep (se 1 (by rfl) ⟨490901, by rfl⟩ : syracuseStep 654535 = 981803) B981803
theorem B654555 : Blo 654306 654555 := bstep (se 1 (by rfl) ⟨490916, by rfl⟩ : syracuseStep 654555 = 981833) B981833
theorem B982265 : Blo 654306 982265 := bstep (se 2 (by rfl) ⟨368349, by rfl⟩ : syracuseStep 982265 = 736699) B736699
theorem B654631 : Blo 654306 654631 := bstep (se 1 (by rfl) ⟨490973, by rfl⟩ : syracuseStep 654631 = 981947) B981947
theorem B654671 : Blo 654306 654671 := bstep (se 1 (by rfl) ⟨491003, by rfl⟩ : syracuseStep 654671 = 982007) B982007
theorem B2391383 : Blo 654306 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B2489687 : Blo 654306 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B654687 : Blo 654306 654687 := bstep (se 1 (by rfl) ⟨491015, by rfl⟩ : syracuseStep 654687 = 982031) B982031
theorem B982367 : Blo 654306 982367 := bstep (se 1 (by rfl) ⟨736775, by rfl⟩ : syracuseStep 982367 = 1473551) B1473551
theorem B982379 : Blo 654306 982379 := bstep (se 1 (by rfl) ⟨736784, by rfl⟩ : syracuseStep 982379 = 1473569) B1473569
theorem B654715 : Blo 654306 654715 := bstep (se 1 (by rfl) ⟨491036, by rfl⟩ : syracuseStep 654715 = 982073) B982073
theorem B1867151 : Blo 654306 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B654767 : Blo 654306 654767 := bstep (se 1 (by rfl) ⟨491075, by rfl⟩ : syracuseStep 654767 = 982151) B982151
theorem B654791 : Blo 654306 654791 := bstep (se 1 (by rfl) ⟨491093, by rfl⟩ : syracuseStep 654791 = 982187) B982187
theorem B654811 : Blo 654306 654811 := bstep (se 1 (by rfl) ⟨491108, by rfl⟩ : syracuseStep 654811 = 982217) B982217
theorem B654887 : Blo 654306 654887 := bstep (se 1 (by rfl) ⟨491165, by rfl⟩ : syracuseStep 654887 = 982331) B982331
theorem B1179193 : Blo 654306 1179193 := bstep (se 2 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 1179193 = 884395) B884395
theorem B654927 : Blo 654306 654927 := bstep (se 1 (by rfl) ⟨491195, by rfl⟩ : syracuseStep 654927 = 982391) B982391
theorem B982607 : Blo 654306 982607 := bstep (se 1 (by rfl) ⟨736955, by rfl⟩ : syracuseStep 982607 = 1473911) B1473911
theorem B654943 : Blo 654306 654943 := bstep (se 1 (by rfl) ⟨491207, by rfl⟩ : syracuseStep 654943 = 982415) B982415
theorem B1474145 : Blo 654306 1474145 := bstep (se 2 (by rfl) ⟨552804, by rfl⟩ : syracuseStep 1474145 = 1105609) B1105609
theorem B654971 : Blo 654306 654971 := bstep (se 1 (by rfl) ⟨491228, by rfl⟩ : syracuseStep 654971 = 982457) B982457
theorem B2096779 : Blo 654306 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B655023 : Blo 654306 655023 := bstep (se 1 (by rfl) ⟨491267, by rfl⟩ : syracuseStep 655023 = 982535) B982535
theorem B655047 : Blo 654306 655047 := bstep (se 1 (by rfl) ⟨491285, by rfl⟩ : syracuseStep 655047 = 982571) B982571
theorem B982727 : Blo 654306 982727 := bstep (se 1 (by rfl) ⟨737045, by rfl⟩ : syracuseStep 982727 = 1474091) B1474091
theorem B2096855 : Blo 654306 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B655067 : Blo 654306 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B655143 : Blo 654306 655143 := bstep (se 1 (by rfl) ⟨491357, by rfl⟩ : syracuseStep 655143 = 982715) B982715
theorem B2391851 : Blo 654306 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B655183 : Blo 654306 655183 := bstep (se 1 (by rfl) ⟨491387, by rfl⟩ : syracuseStep 655183 = 982775) B982775
theorem B2359135 : Blo 654306 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B655199 : Blo 654306 655199 := bstep (se 1 (by rfl) ⟨491399, by rfl⟩ : syracuseStep 655199 = 982799) B982799
theorem B982889 : Blo 654306 982889 := bstep (se 2 (by rfl) ⟨368583, by rfl⟩ : syracuseStep 982889 = 737167) B737167
theorem B17956727 : Blo 654306 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B655227 : Blo 654306 655227 := bstep (se 1 (by rfl) ⟨491420, by rfl⟩ : syracuseStep 655227 = 982841) B982841
theorem B1245071 : Blo 654306 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B655279 : Blo 654306 655279 := bstep (se 1 (by rfl) ⟨491459, by rfl⟩ : syracuseStep 655279 = 982919) B982919
theorem B982967 : Blo 654306 982967 := bstep (se 1 (by rfl) ⟨737225, by rfl⟩ : syracuseStep 982967 = 1474451) B1474451
theorem B1474487 : Blo 654306 1474487 := bstep (se 1 (by rfl) ⟨1105865, by rfl⟩ : syracuseStep 1474487 = 2211731) B2211731
theorem B14221241 : Blo 654306 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B655303 : Blo 654306 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B655323 : Blo 654306 655323 := bstep (se 1 (by rfl) ⟨491492, by rfl⟩ : syracuseStep 655323 = 982985) B982985
theorem B983003 : Blo 654306 983003 := bstep (se 1 (by rfl) ⟨737252, by rfl⟩ : syracuseStep 983003 = 1474505) B1474505
theorem B885001 : Blo 654306 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B655647 : Blo 654306 655647 := bstep (se 1 (by rfl) ⟨491735, by rfl⟩ : syracuseStep 655647 = 983471) B983471
theorem B1802569 : Blo 654306 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B983387 : Blo 654306 983387 := bstep (se 1 (by rfl) ⟨737540, by rfl⟩ : syracuseStep 983387 = 1475081) B1475081
theorem B655707 : Blo 654306 655707 := bstep (se 1 (by rfl) ⟨491780, by rfl⟩ : syracuseStep 655707 = 983561) B983561
theorem B2195819 : Blo 654306 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B655727 : Blo 654306 655727 := bstep (se 1 (by rfl) ⟨491795, by rfl⟩ : syracuseStep 655727 = 983591) B983591
theorem B655783 : Blo 654306 655783 := bstep (se 1 (by rfl) ⟨491837, by rfl⟩ : syracuseStep 655783 = 983675) B983675
theorem B1474991 : Blo 654306 1474991 := bstep (se 1 (by rfl) ⟨1106243, by rfl⟩ : syracuseStep 1474991 = 2212487) B2212487
theorem B1475027 : Blo 654306 1475027 := bstep (se 1 (by rfl) ⟨1106270, by rfl⟩ : syracuseStep 1475027 = 2212541) B2212541
theorem B655867 : Blo 654306 655867 := bstep (se 1 (by rfl) ⟨491900, by rfl⟩ : syracuseStep 655867 = 983801) B983801
theorem B1475135 : Blo 654306 1475135 := bstep (se 1 (by rfl) ⟨1106351, by rfl⟩ : syracuseStep 1475135 = 2212703) B2212703
theorem B983615 : Blo 654306 983615 := bstep (se 1 (by rfl) ⟨737711, by rfl⟩ : syracuseStep 983615 = 1475423) B1475423
theorem B655935 : Blo 654306 655935 := bstep (se 1 (by rfl) ⟨491951, by rfl⟩ : syracuseStep 655935 = 983903) B983903
theorem B655943 : Blo 654306 655943 := bstep (se 1 (by rfl) ⟨491957, by rfl⟩ : syracuseStep 655943 = 983915) B983915
theorem B1868359 : Blo 654306 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B1475243 : Blo 654306 1475243 := bstep (se 1 (by rfl) ⟨1106432, by rfl⟩ : syracuseStep 1475243 = 2212865) B2212865
theorem B983735 : Blo 654306 983735 := bstep (se 1 (by rfl) ⟨737801, by rfl⟩ : syracuseStep 983735 = 1475603) B1475603
theorem B656095 : Blo 654306 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B656175 : Blo 654306 656175 := bstep (se 1 (by rfl) ⟨492131, by rfl⟩ : syracuseStep 656175 = 984263) B984263
theorem B21300083 : Blo 654306 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B983963 : Blo 654306 983963 := bstep (se 1 (by rfl) ⟨737972, by rfl⟩ : syracuseStep 983963 = 1475945) B1475945
theorem B656283 : Blo 654306 656283 := bstep (se 1 (by rfl) ⟨492212, by rfl⟩ : syracuseStep 656283 = 984425) B984425
theorem B656335 : Blo 654306 656335 := bstep (se 1 (by rfl) ⟨492251, by rfl⟩ : syracuseStep 656335 = 984503) B984503
theorem B656359 : Blo 654306 656359 := bstep (se 1 (by rfl) ⟨492269, by rfl⟩ : syracuseStep 656359 = 984539) B984539
theorem B1475783 : Blo 654306 1475783 := bstep (se 1 (by rfl) ⟨1106837, by rfl⟩ : syracuseStep 1475783 = 2213675) B2213675
theorem B656671 : Blo 654306 656671 := bstep (se 1 (by rfl) ⟨492503, by rfl⟩ : syracuseStep 656671 = 985007) B985007
theorem B984359 : Blo 654306 984359 := bstep (se 1 (by rfl) ⟨738269, by rfl⟩ : syracuseStep 984359 = 1476539) B1476539
theorem B656731 : Blo 654306 656731 := bstep (se 1 (by rfl) ⟨492548, by rfl⟩ : syracuseStep 656731 = 985097) B985097
theorem B656751 : Blo 654306 656751 := bstep (se 1 (by rfl) ⟨492563, by rfl⟩ : syracuseStep 656751 = 985127) B985127
theorem B1475963 : Blo 654306 1475963 := bstep (se 1 (by rfl) ⟨1106972, by rfl⟩ : syracuseStep 1475963 = 2213945) B2213945
theorem B984443 : Blo 654306 984443 := bstep (se 1 (by rfl) ⟨738332, by rfl⟩ : syracuseStep 984443 = 1476665) B1476665
theorem B656807 : Blo 654306 656807 := bstep (se 1 (by rfl) ⟨492605, by rfl⟩ : syracuseStep 656807 = 985211) B985211
theorem B1476089 : Blo 654306 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B984569 : Blo 654306 984569 := bstep (se 2 (by rfl) ⟨369213, by rfl⟩ : syracuseStep 984569 = 738427) B738427
theorem B656891 : Blo 654306 656891 := bstep (se 1 (by rfl) ⟨492668, by rfl⟩ : syracuseStep 656891 = 985337) B985337
theorem B3999289 : Blo 654306 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B656959 : Blo 654306 656959 := bstep (se 1 (by rfl) ⟨492719, by rfl⟩ : syracuseStep 656959 = 985439) B985439
theorem B656967 : Blo 654306 656967 := bstep (se 1 (by rfl) ⟨492725, by rfl⟩ : syracuseStep 656967 = 985451) B985451
theorem B1476179 : Blo 654306 1476179 := bstep (se 1 (by rfl) ⟨1107134, by rfl⟩ : syracuseStep 1476179 = 2214269) B2214269
theorem B984671 : Blo 654306 984671 := bstep (se 1 (by rfl) ⟨738503, by rfl⟩ : syracuseStep 984671 = 1477007) B1477007
theorem B657119 : Blo 654306 657119 := bstep (se 1 (by rfl) ⟨492839, by rfl⟩ : syracuseStep 657119 = 985679) B985679
theorem B1476359 : Blo 654306 1476359 := bstep (se 1 (by rfl) ⟨1107269, by rfl⟩ : syracuseStep 1476359 = 2214539) B2214539
theorem B657199 : Blo 654306 657199 := bstep (se 1 (by rfl) ⟨492899, by rfl⟩ : syracuseStep 657199 = 985799) B985799
theorem B984887 : Blo 654306 984887 := bstep (se 1 (by rfl) ⟨738665, by rfl⟩ : syracuseStep 984887 = 1477331) B1477331
theorem B657307 : Blo 654306 657307 := bstep (se 1 (by rfl) ⟨492980, by rfl⟩ : syracuseStep 657307 = 985961) B985961
theorem B657359 : Blo 654306 657359 := bstep (se 1 (by rfl) ⟨493019, by rfl⟩ : syracuseStep 657359 = 986039) B986039
theorem B657383 : Blo 654306 657383 := bstep (se 1 (by rfl) ⟨493037, by rfl⟩ : syracuseStep 657383 = 986075) B986075
theorem B8521805 : Blo 654306 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B1575017 : Blo 654306 1575017 := bstep (se 2 (by rfl) ⟨590631, by rfl⟩ : syracuseStep 1575017 = 1181263) B1181263
theorem B985193 : Blo 654306 985193 := bstep (se 2 (by rfl) ⟨369447, by rfl⟩ : syracuseStep 985193 = 738895) B738895
theorem B657695 : Blo 654306 657695 := bstep (se 1 (by rfl) ⟨493271, by rfl⟩ : syracuseStep 657695 = 986543) B986543
theorem B657755 : Blo 654306 657755 := bstep (se 1 (by rfl) ⟨493316, by rfl⟩ : syracuseStep 657755 = 986633) B986633
theorem B1476971 : Blo 654306 1476971 := bstep (se 1 (by rfl) ⟨1107728, by rfl⟩ : syracuseStep 1476971 = 2215457) B2215457
theorem B657775 : Blo 654306 657775 := bstep (se 1 (by rfl) ⟨493331, by rfl⟩ : syracuseStep 657775 = 986663) B986663
theorem B2099623 : Blo 654306 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B985511 : Blo 654306 985511 := bstep (se 1 (by rfl) ⟨739133, by rfl⟩ : syracuseStep 985511 = 1478267) B1478267
theorem B657831 : Blo 654306 657831 := bstep (se 1 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 657831 = 986747) B986747
theorem B788935 : Blo 654306 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B1247699 : Blo 654306 1247699 := bstep (se 1 (by rfl) ⟨935774, by rfl⟩ : syracuseStep 1247699 = 1871549) B1871549
theorem B1477115 : Blo 654306 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B985595 : Blo 654306 985595 := bstep (se 1 (by rfl) ⟨739196, by rfl⟩ : syracuseStep 985595 = 1478393) B1478393
theorem B657915 : Blo 654306 657915 := bstep (se 1 (by rfl) ⟨493436, by rfl⟩ : syracuseStep 657915 = 986873) B986873
theorem B657983 : Blo 654306 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B657991 : Blo 654306 657991 := bstep (se 1 (by rfl) ⟨493493, by rfl⟩ : syracuseStep 657991 = 986987) B986987
theorem B1477241 : Blo 654306 1477241 := bstep (se 2 (by rfl) ⟨553965, by rfl⟩ : syracuseStep 1477241 = 1107931) B1107931
theorem B985721 : Blo 654306 985721 := bstep (se 2 (by rfl) ⟨369645, by rfl⟩ : syracuseStep 985721 = 739291) B739291
theorem B1477295 : Blo 654306 1477295 := bstep (se 1 (by rfl) ⟨1107971, by rfl⟩ : syracuseStep 1477295 = 2215943) B2215943
theorem B985775 : Blo 654306 985775 := bstep (se 1 (by rfl) ⟨739331, by rfl⟩ : syracuseStep 985775 = 1478663) B1478663
theorem B985823 : Blo 654306 985823 := bstep (se 1 (by rfl) ⟨739367, by rfl⟩ : syracuseStep 985823 = 1478735) B1478735
theorem B658143 : Blo 654306 658143 := bstep (se 1 (by rfl) ⟨493607, by rfl⟩ : syracuseStep 658143 = 987215) B987215
theorem B7080695 : Blo 654306 7080695 := bstep (se 1 (by rfl) ⟨5310521, by rfl⟩ : syracuseStep 7080695 = 10621043) B10621043
theorem B1477367 : Blo 654306 1477367 := bstep (se 1 (by rfl) ⟨1108025, by rfl⟩ : syracuseStep 1477367 = 2216051) B2216051
theorem B658223 : Blo 654306 658223 := bstep (se 1 (by rfl) ⟨493667, by rfl⟩ : syracuseStep 658223 = 987335) B987335
theorem B2657195 : Blo 654306 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B1477547 : Blo 654306 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B986087 : Blo 654306 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B12586049 : Blo 654306 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B9440459 : Blo 654306 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B986345 : Blo 654306 986345 := bstep (se 2 (by rfl) ⟨369879, by rfl⟩ : syracuseStep 986345 = 739759) B739759
theorem B986399 : Blo 654306 986399 := bstep (se 1 (by rfl) ⟨739799, by rfl⟩ : syracuseStep 986399 = 1479599) B1479599
theorem B1478087 : Blo 654306 1478087 := bstep (se 1 (by rfl) ⟨1108565, by rfl⟩ : syracuseStep 1478087 = 2217131) B2217131
theorem B986567 : Blo 654306 986567 := bstep (se 1 (by rfl) ⟨739925, by rfl⟩ : syracuseStep 986567 = 1479851) B1479851
theorem B5606921 : Blo 654306 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B2494061 : Blo 654306 2494061 := bstep (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) B935273
theorem B1248929 : Blo 654306 1248929 := bstep (se 2 (by rfl) ⟨468348, by rfl⟩ : syracuseStep 1248929 = 936697) B936697
theorem B986921 : Blo 654306 986921 := bstep (se 2 (by rfl) ⟨370095, by rfl⟩ : syracuseStep 986921 = 740191) B740191
theorem B1478447 : Blo 654306 1478447 := bstep (se 1 (by rfl) ⟨1108835, by rfl⟩ : syracuseStep 1478447 = 2217671) B2217671
theorem B986927 : Blo 654306 986927 := bstep (se 1 (by rfl) ⟨740195, by rfl⟩ : syracuseStep 986927 = 1480391) B1480391
theorem B1052471 : Blo 654306 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B888655 : Blo 654306 888655 := bstep (se 1 (by rfl) ⟨666491, by rfl⟩ : syracuseStep 888655 = 1332983) B1332983
theorem B96964487 : Blo 654306 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B3149725 : Blo 654306 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B7475165 : Blo 654306 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B987401 : Blo 654306 987401 := bstep (se 2 (by rfl) ⟨370275, by rfl⟩ : syracuseStep 987401 = 740551) B740551
theorem B1577323 : Blo 654306 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B1479023 : Blo 654306 1479023 := bstep (se 1 (by rfl) ⟨1109267, by rfl⟩ : syracuseStep 1479023 = 2218535) B2218535
theorem B1184167 : Blo 654306 1184167 := bstep (se 1 (by rfl) ⟨888125, by rfl⟩ : syracuseStep 1184167 = 1776251) B1776251
theorem B1479095 : Blo 654306 1479095 := bstep (se 1 (by rfl) ⟨1109321, by rfl⟩ : syracuseStep 1479095 = 2218643) B2218643
theorem B3314195 : Blo 654306 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B1479239 : Blo 654306 1479239 := bstep (se 1 (by rfl) ⟨1109429, by rfl⟩ : syracuseStep 1479239 = 2218859) B2218859
theorem B1774153 : Blo 654306 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1479275 : Blo 654306 1479275 := bstep (se 1 (by rfl) ⟨1109456, by rfl⟩ : syracuseStep 1479275 = 2218913) B2218913
theorem B1184377 : Blo 654306 1184377 := bstep (se 2 (by rfl) ⟨444141, by rfl⟩ : syracuseStep 1184377 = 888283) B888283
theorem B3543851 : Blo 654306 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B1479671 : Blo 654306 1479671 := bstep (se 1 (by rfl) ⟨1109753, by rfl⟩ : syracuseStep 1479671 = 2219507) B2219507
theorem B1578217 : Blo 654306 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B3544307 : Blo 654306 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B2495731 : Blo 654306 2495731 := bstep (se 1 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 2495731 = 3743597) B3743597
theorem B1480031 : Blo 654306 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B1480427 : Blo 654306 1480427 := bstep (se 1 (by rfl) ⟨1110320, by rfl⟩ : syracuseStep 1480427 = 2220641) B2220641
theorem B1480553 : Blo 654306 1480553 := bstep (se 2 (by rfl) ⟨555207, by rfl⟩ : syracuseStep 1480553 = 1110415) B1110415
theorem B5969963 : Blo 654306 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B3315977 : Blo 654306 3315977 := bstep (se 2 (by rfl) ⟨1243491, by rfl⟩ : syracuseStep 3315977 = 2486983) B2486983
theorem B42637661 : Blo 654306 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B1776055 : Blo 654306 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B2660971 : Blo 654306 2660971 := bstep (se 1 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 2660971 = 3991457) B3991457
theorem B5610545 : Blo 654306 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B2497675 : Blo 654306 2497675 := bstep (se 1 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 2497675 = 3746513) B3746513
theorem B3317111 : Blo 654306 3317111 := bstep (se 1 (by rfl) ⟨2487833, by rfl⟩ : syracuseStep 3317111 = 4975667) B4975667
theorem B2497979 : Blo 654306 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B2104775 : Blo 654306 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B3317273 : Blo 654306 3317273 := bstep (se 2 (by rfl) ⟨1243977, by rfl⟩ : syracuseStep 3317273 = 2487955) B2487955
theorem B2989835 : Blo 654306 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B2662301 : Blo 654306 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B4989275 : Blo 654306 4989275 := bstep (se 1 (by rfl) ⟨3741956, by rfl⟩ : syracuseStep 4989275 = 7483913) B7483913
theorem B6726347 : Blo 654306 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B828139 : Blo 654306 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B664367 : Blo 654306 664367 := bstep (se 1 (by rfl) ⟨498275, by rfl⟩ : syracuseStep 664367 = 996551) B996551
theorem B4203323 : Blo 654306 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2499407 : Blo 654306 2499407 := bstep (se 1 (by rfl) ⟨1874555, by rfl⟩ : syracuseStep 2499407 = 3749111) B3749111
theorem B3548393 : Blo 654306 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B1779083 : Blo 654306 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B829111 : Blo 654306 829111 := bstep (se 1 (by rfl) ⟨621833, by rfl⟩ : syracuseStep 829111 = 1243667) B1243667
theorem B3156047 : Blo 654306 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2795705 : Blo 654306 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B15935849 : Blo 654306 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B3320189 : Blo 654306 3320189 := bstep (se 3 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 3320189 = 1245071) B1245071
theorem B12003713 : Blo 654306 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B11971151 : Blo 654306 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B9480827 : Blo 654306 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B2796763 : Blo 654306 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B666991 : Blo 654306 666991 := bstep (se 1 (by rfl) ⟨500243, by rfl⟩ : syracuseStep 666991 = 1000487) B1000487
theorem B5680649 : Blo 654306 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B6303329 : Blo 654306 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B831151 : Blo 654306 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B3321647 : Blo 654306 3321647 := bstep (se 1 (by rfl) ⟨2491235, by rfl⟩ : syracuseStep 3321647 = 4982471) B4982471
theorem B4042955 : Blo 654306 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B11383055 : Blo 654306 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B71840033 : Blo 654306 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B2045345 : Blo 654306 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B833095 : Blo 654306 833095 := bstep (se 1 (by rfl) ⟨624821, by rfl⟩ : syracuseStep 833095 = 1249643) B1249643
theorem B3159737 : Blo 654306 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B3192605 : Blo 654306 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B4273975 : Blo 654306 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B3323753 : Blo 654306 3323753 := bstep (se 2 (by rfl) ⟨1246407, by rfl⟩ : syracuseStep 3323753 = 2492815) B2492815
theorem B7485371 : Blo 654306 7485371 := bstep (se 1 (by rfl) ⟨5614028, by rfl⟩ : syracuseStep 7485371 = 11228057) B11228057
theorem B2210057 : Blo 654306 2210057 := bstep (se 2 (by rfl) ⟨828771, by rfl⟩ : syracuseStep 2210057 = 1657543) B1657543
theorem B8075645 : Blo 654306 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B4209191 : Blo 654306 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B736231 : Blo 654306 736231 := bstep (se 1 (by rfl) ⟨552173, by rfl⟩ : syracuseStep 736231 = 1104347) B1104347
theorem B2800763 : Blo 654306 2800763 := bstep (se 1 (by rfl) ⟨2100572, by rfl⟩ : syracuseStep 2800763 = 4201145) B4201145
theorem B6732953 : Blo 654306 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B3980555 : Blo 654306 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B2211191 : Blo 654306 2211191 := bstep (se 1 (by rfl) ⟨1658393, by rfl⟩ : syracuseStep 2211191 = 3316787) B3316787
theorem B3325535 : Blo 654306 3325535 := bstep (se 1 (by rfl) ⟨2494151, by rfl⟩ : syracuseStep 3325535 = 4988303) B4988303
theorem B2212271 : Blo 654306 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B737887 : Blo 654306 737887 := bstep (se 1 (by rfl) ⟨553415, by rfl⟩ : syracuseStep 737887 = 1106831) B1106831
theorem B4998509 : Blo 654306 4998509 := bstep (se 3 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 4998509 = 1874441) B1874441
theorem B2213243 : Blo 654306 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B739039 : Blo 654306 739039 := bstep (se 1 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 739039 = 1108559) B1108559
theorem B739615 : Blo 654306 739615 := bstep (se 1 (by rfl) ⟨554711, by rfl⟩ : syracuseStep 739615 = 1109423) B1109423
theorem B1657199 : Blo 654306 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B2804179 : Blo 654306 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B739903 : Blo 654306 739903 := bstep (se 1 (by rfl) ⟨554927, by rfl⟩ : syracuseStep 739903 = 1109855) B1109855
theorem B936623 : Blo 654306 936623 := bstep (se 1 (by rfl) ⟨702467, by rfl⟩ : syracuseStep 936623 = 1404935) B1404935
theorem B2214647 : Blo 654306 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B1657847 : Blo 654306 1657847 := bstep (se 1 (by rfl) ⟨1243385, by rfl⟩ : syracuseStep 1657847 = 2486771) B2486771
theorem B1657979 : Blo 654306 1657979 := bstep (se 1 (by rfl) ⟨1243484, by rfl⟩ : syracuseStep 1657979 = 2486969) B2486969
theorem B2838041 : Blo 654306 2838041 := bstep (se 2 (by rfl) ⟨1064265, by rfl⟩ : syracuseStep 2838041 = 2128531) B2128531
theorem B3329747 : Blo 654306 3329747 := bstep (se 1 (by rfl) ⟨2497310, by rfl⟩ : syracuseStep 3329747 = 4994621) B4994621
theorem B2805511 : Blo 654306 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B2215727 : Blo 654306 2215727 := bstep (se 1 (by rfl) ⟨1661795, by rfl⟩ : syracuseStep 2215727 = 3323591) B3323591
theorem B5591065 : Blo 654306 5591065 := bstep (se 2 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 5591065 = 4193299) B4193299
theorem B2805785 : Blo 654306 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B10670339 : Blo 654306 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B3330395 : Blo 654306 3330395 := bstep (se 1 (by rfl) ⟨2497796, by rfl⟩ : syracuseStep 3330395 = 4995593) B4995593
theorem B4739435 : Blo 654306 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B1594255 : Blo 654306 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B1659791 : Blo 654306 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B1397903 : Blo 654306 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B1594567 : Blo 654306 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B3331367 : Blo 654306 3331367 := bstep (se 1 (by rfl) ⟨2498525, by rfl⟩ : syracuseStep 3331367 = 4997051) B4997051
theorem B3986783 : Blo 654306 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B7558505 : Blo 654306 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B1660297 : Blo 654306 1660297 := bstep (se 2 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 1660297 = 1245223) B1245223
theorem B1660409 : Blo 654306 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B1922617 : Blo 654306 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B3364487 : Blo 654306 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2217833 : Blo 654306 2217833 := bstep (se 2 (by rfl) ⟨831687, by rfl⟩ : syracuseStep 2217833 = 1663375) B1663375
theorem B1661057 : Blo 654306 1661057 := bstep (se 2 (by rfl) ⟨622896, by rfl⟩ : syracuseStep 1661057 = 1245793) B1245793
theorem B2218265 : Blo 654306 2218265 := bstep (se 2 (by rfl) ⟨831849, by rfl⟩ : syracuseStep 2218265 = 1663699) B1663699
theorem B1104239 : Blo 654306 1104239 := bstep (se 1 (by rfl) ⟨828179, by rfl⟩ : syracuseStep 1104239 = 1656359) B1656359
theorem B1104455 : Blo 654306 1104455 := bstep (se 1 (by rfl) ⟨828341, by rfl⟩ : syracuseStep 1104455 = 1656683) B1656683
theorem B1661867 : Blo 654306 1661867 := bstep (se 1 (by rfl) ⟨1246400, by rfl⟩ : syracuseStep 1661867 = 2492801) B2492801
theorem B1399783 : Blo 654306 1399783 := bstep (se 1 (by rfl) ⟨1049837, by rfl⟩ : syracuseStep 1399783 = 2099675) B2099675
theorem B1104887 : Blo 654306 1104887 := bstep (se 1 (by rfl) ⟨828665, by rfl⟩ : syracuseStep 1104887 = 1657331) B1657331
theorem B3726557 : Blo 654306 3726557 := bstep (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) B1397459
theorem B13491521 : Blo 654306 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B12639563 : Blo 654306 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B1400159 : Blo 654306 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B2219615 : Blo 654306 2219615 := bstep (se 1 (by rfl) ⟨1664711, by rfl⟩ : syracuseStep 2219615 = 3329423) B3329423
theorem B8216225 : Blo 654306 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B1105643 : Blo 654306 1105643 := bstep (se 1 (by rfl) ⟨829232, by rfl⟩ : syracuseStep 1105643 = 1658465) B1658465
theorem B1662727 : Blo 654306 1662727 := bstep (se 1 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 1662727 = 2494091) B2494091
theorem B18013985 : Blo 654306 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1663001 : Blo 654306 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B3367115 : Blo 654306 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B5693651 : Blo 654306 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B31875389 : Blo 654306 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B1401313 : Blo 654306 1401313 := bstep (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) B1050985
theorem B13001363 : Blo 654306 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B1106615 : Blo 654306 1106615 := bstep (se 1 (by rfl) ⟨829961, by rfl⟩ : syracuseStep 1106615 = 1659923) B1659923
theorem B2221019 : Blo 654306 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B2221181 : Blo 654306 2221181 := bstep (se 3 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 2221181 = 832943) B832943
theorem B2221289 : Blo 654306 2221289 := bstep (se 2 (by rfl) ⟨832983, by rfl⟩ : syracuseStep 2221289 = 1665967) B1665967
theorem B1107337 : Blo 654306 1107337 := bstep (se 2 (by rfl) ⟨415251, by rfl⟩ : syracuseStep 1107337 = 830503) B830503
theorem B2221451 : Blo 654306 2221451 := bstep (se 1 (by rfl) ⟨1666088, by rfl⟩ : syracuseStep 2221451 = 3332177) B3332177
theorem B3368429 : Blo 654306 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B166127333 : Blo 654306 166127333 := bstep (se 4 (by rfl) ⟨15574437, by rfl⟩ : syracuseStep 166127333 = 31148875) B31148875
theorem B68085497 : Blo 654306 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B1107769 : Blo 654306 1107769 := bstep (se 2 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 1107769 = 830827) B830827
theorem B1664975 : Blo 654306 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B1108073 : Blo 654306 1108073 := bstep (se 2 (by rfl) ⟨415527, by rfl⟩ : syracuseStep 1108073 = 831055) B831055
theorem B1665643 : Blo 654306 1665643 := bstep (se 1 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 1665643 = 2498465) B2498465
theorem B3369595 : Blo 654306 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1665947 : Blo 654306 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B1403867 : Blo 654306 1403867 := bstep (se 1 (by rfl) ⟨1052900, by rfl⟩ : syracuseStep 1403867 = 2105801) B2105801
theorem B5598173 : Blo 654306 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B1404047 : Blo 654306 1404047 := bstep (se 1 (by rfl) ⟨1053035, by rfl⟩ : syracuseStep 1404047 = 2106071) B2106071
theorem B23981275 : Blo 654306 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B1666291 : Blo 654306 1666291 := bstep (se 1 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 1666291 = 2499437) B2499437
theorem B1404191 : Blo 654306 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B1109497 : Blo 654306 1109497 := bstep (se 2 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 1109497 = 832123) B832123
theorem B367586819 : Blo 654306 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B1404499 : Blo 654306 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1109767 : Blo 654306 1109767 := bstep (se 1 (by rfl) ⟨832325, by rfl⟩ : syracuseStep 1109767 = 1664651) B1664651
theorem B1109801 : Blo 654306 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B57438001 : Blo 654306 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B2486483 : Blo 654306 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B1864043 : Blo 654306 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B1110523 : Blo 654306 1110523 := bstep (se 1 (by rfl) ⟨832892, by rfl⟩ : syracuseStep 1110523 = 1665785) B1665785
theorem B1405687 : Blo 654306 1405687 := bstep (se 1 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 1405687 = 2108531) B2108531
theorem B3732389 : Blo 654306 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B2487287 : Blo 654306 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B1864919 : Blo 654306 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1996019 : Blo 654306 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B6321401 : Blo 654306 6321401 := bstep (se 2 (by rfl) ⟨2370525, by rfl⟩ : syracuseStep 6321401 = 4741051) B4741051
theorem B28407185 : Blo 654306 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B2521039 : Blo 654306 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B1472723 : Blo 654306 1472723 := bstep (se 1 (by rfl) ⟨1104542, by rfl⟩ : syracuseStep 1472723 = 2209085) B2209085
theorem B1472777 : Blo 654306 1472777 := bstep (se 2 (by rfl) ⟨552291, by rfl⟩ : syracuseStep 1472777 = 1104583) B1104583
theorem B4979069 : Blo 654306 4979069 := bstep (se 3 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 4979069 = 1867151) B1867151
theorem B1472993 : Blo 654306 1472993 := bstep (se 2 (by rfl) ⟨552372, by rfl⟩ : syracuseStep 1472993 = 1104745) B1104745
theorem B981575 : Blo 654306 981575 := bstep (se 1 (by rfl) ⟨736181, by rfl⟩ : syracuseStep 981575 = 1472363) B1472363
theorem B5306953 : Blo 654306 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B981611 : Blo 654306 981611 := bstep (se 1 (by rfl) ⟨736208, by rfl⟩ : syracuseStep 981611 = 1472417) B1472417
theorem B1473299 : Blo 654306 1473299 := bstep (se 1 (by rfl) ⟨1104974, by rfl⟩ : syracuseStep 1473299 = 2209949) B2209949
theorem B981839 : Blo 654306 981839 := bstep (se 1 (by rfl) ⟨736379, by rfl⟩ : syracuseStep 981839 = 1472759) B1472759
theorem B2489231 : Blo 654306 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B654311 : Blo 654306 654311 := bstep (se 1 (by rfl) ⟨490733, by rfl⟩ : syracuseStep 654311 = 981467) B981467
theorem B1473659 : Blo 654306 1473659 := bstep (se 1 (by rfl) ⟨1105244, by rfl⟩ : syracuseStep 1473659 = 2210489) B2210489
theorem B12582053 : Blo 654306 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B982235 : Blo 654306 982235 := bstep (se 1 (by rfl) ⟨736676, by rfl⟩ : syracuseStep 982235 = 1473353) B1473353
theorem B20217077 : Blo 654306 20217077 := bstep (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) B1895351
theorem B1473785 : Blo 654306 1473785 := bstep (se 2 (by rfl) ⟨552669, by rfl⟩ : syracuseStep 1473785 = 1105339) B1105339
theorem B654623 : Blo 654306 654623 := bstep (se 1 (by rfl) ⟨490967, by rfl⟩ : syracuseStep 654623 = 981935) B981935
theorem B654683 : Blo 654306 654683 := bstep (se 1 (by rfl) ⟨491012, by rfl⟩ : syracuseStep 654683 = 982025) B982025
theorem B654703 : Blo 654306 654703 := bstep (se 1 (by rfl) ⟨491027, by rfl⟩ : syracuseStep 654703 = 982055) B982055
theorem B982409 : Blo 654306 982409 := bstep (se 2 (by rfl) ⟨368403, by rfl⟩ : syracuseStep 982409 = 736807) B736807
theorem B1473929 : Blo 654306 1473929 := bstep (se 2 (by rfl) ⟨552723, by rfl⟩ : syracuseStep 1473929 = 1105447) B1105447
theorem B1572257 : Blo 654306 1572257 := bstep (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) B1179193
theorem B654759 : Blo 654306 654759 := bstep (se 1 (by rfl) ⟨491069, by rfl⟩ : syracuseStep 654759 = 982139) B982139
theorem B2096599 : Blo 654306 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B654843 : Blo 654306 654843 := bstep (se 1 (by rfl) ⟨491132, by rfl⟩ : syracuseStep 654843 = 982265) B982265
theorem B1474055 : Blo 654306 1474055 := bstep (se 1 (by rfl) ⟨1105541, by rfl⟩ : syracuseStep 1474055 = 2211083) B2211083
theorem B654911 : Blo 654306 654911 := bstep (se 1 (by rfl) ⟨491183, by rfl⟩ : syracuseStep 654911 = 982367) B982367
theorem B654919 : Blo 654306 654919 := bstep (se 1 (by rfl) ⟨491189, by rfl⟩ : syracuseStep 654919 = 982379) B982379
theorem B1474235 : Blo 654306 1474235 := bstep (se 1 (by rfl) ⟨1105676, by rfl⟩ : syracuseStep 1474235 = 2211353) B2211353
theorem B655071 : Blo 654306 655071 := bstep (se 1 (by rfl) ⟨491303, by rfl⟩ : syracuseStep 655071 = 982607) B982607
theorem B982763 : Blo 654306 982763 := bstep (se 1 (by rfl) ⟨737072, by rfl⟩ : syracuseStep 982763 = 1474145) B1474145
theorem B655151 : Blo 654306 655151 := bstep (se 1 (by rfl) ⟨491363, by rfl⟩ : syracuseStep 655151 = 982727) B982727
theorem B1474361 : Blo 654306 1474361 := bstep (se 2 (by rfl) ⟨552885, by rfl⟩ : syracuseStep 1474361 = 1105771) B1105771
theorem B2490173 : Blo 654306 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B655259 : Blo 654306 655259 := bstep (se 1 (by rfl) ⟨491444, by rfl⟩ : syracuseStep 655259 = 982889) B982889
theorem B655311 : Blo 654306 655311 := bstep (se 1 (by rfl) ⟨491483, by rfl⟩ : syracuseStep 655311 = 982967) B982967
theorem B982991 : Blo 654306 982991 := bstep (se 1 (by rfl) ⟨737243, by rfl⟩ : syracuseStep 982991 = 1474487) B1474487
theorem B655335 : Blo 654306 655335 := bstep (se 1 (by rfl) ⟨491501, by rfl⟩ : syracuseStep 655335 = 983003) B983003
theorem B655591 : Blo 654306 655591 := bstep (se 1 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 655591 = 983387) B983387
theorem B1474847 : Blo 654306 1474847 := bstep (se 1 (by rfl) ⟨1106135, by rfl⟩ : syracuseStep 1474847 = 2212271) B2212271
theorem B983327 : Blo 654306 983327 := bstep (se 1 (by rfl) ⟨737495, by rfl⟩ : syracuseStep 983327 = 1474991) B1474991
theorem B983351 : Blo 654306 983351 := bstep (se 1 (by rfl) ⟨737513, by rfl⟩ : syracuseStep 983351 = 1475027) B1475027
theorem B1180001 : Blo 654306 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B983423 : Blo 654306 983423 := bstep (se 1 (by rfl) ⟨737567, by rfl⟩ : syracuseStep 983423 = 1475135) B1475135
theorem B655743 : Blo 654306 655743 := bstep (se 1 (by rfl) ⟨491807, by rfl⟩ : syracuseStep 655743 = 983615) B983615
theorem B983495 : Blo 654306 983495 := bstep (se 1 (by rfl) ⟨737621, by rfl⟩ : syracuseStep 983495 = 1475243) B1475243
theorem B655823 : Blo 654306 655823 := bstep (se 1 (by rfl) ⟨491867, by rfl⟩ : syracuseStep 655823 = 983735) B983735
theorem B655975 : Blo 654306 655975 := bstep (se 1 (by rfl) ⟨491981, by rfl⟩ : syracuseStep 655975 = 983963) B983963
theorem B1868417 : Blo 654306 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B2491145 : Blo 654306 2491145 := bstep (se 2 (by rfl) ⟨934179, by rfl⟩ : syracuseStep 2491145 = 1868359) B1868359
theorem B983849 : Blo 654306 983849 := bstep (se 2 (by rfl) ⟨368943, by rfl⟩ : syracuseStep 983849 = 737887) B737887
theorem B983855 : Blo 654306 983855 := bstep (se 1 (by rfl) ⟨737891, by rfl⟩ : syracuseStep 983855 = 1475783) B1475783
theorem B656239 : Blo 654306 656239 := bstep (se 1 (by rfl) ⟨492179, by rfl⟩ : syracuseStep 656239 = 984359) B984359
theorem B1475495 : Blo 654306 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B983975 : Blo 654306 983975 := bstep (se 1 (by rfl) ⟨737981, by rfl⟩ : syracuseStep 983975 = 1475963) B1475963
theorem B656295 : Blo 654306 656295 := bstep (se 1 (by rfl) ⟨492221, by rfl⟩ : syracuseStep 656295 = 984443) B984443
theorem B984059 : Blo 654306 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B656379 : Blo 654306 656379 := bstep (se 1 (by rfl) ⟨492284, by rfl⟩ : syracuseStep 656379 = 984569) B984569
theorem B984119 : Blo 654306 984119 := bstep (se 1 (by rfl) ⟨738089, by rfl⟩ : syracuseStep 984119 = 1476179) B1476179
theorem B656447 : Blo 654306 656447 := bstep (se 1 (by rfl) ⟨492335, by rfl⟩ : syracuseStep 656447 = 984671) B984671
theorem B984239 : Blo 654306 984239 := bstep (se 1 (by rfl) ⟨738179, by rfl⟩ : syracuseStep 984239 = 1476359) B1476359
theorem B656591 : Blo 654306 656591 := bstep (se 1 (by rfl) ⟨492443, by rfl⟩ : syracuseStep 656591 = 984887) B984887
theorem B1050011 : Blo 654306 1050011 := bstep (se 1 (by rfl) ⟨787508, by rfl⟩ : syracuseStep 1050011 = 1575017) B1575017
theorem B656795 : Blo 654306 656795 := bstep (se 1 (by rfl) ⟨492596, by rfl⟩ : syracuseStep 656795 = 985193) B985193
theorem B984647 : Blo 654306 984647 := bstep (se 1 (by rfl) ⟨738485, by rfl⟩ : syracuseStep 984647 = 1476971) B1476971
theorem B657007 : Blo 654306 657007 := bstep (se 1 (by rfl) ⟨492755, by rfl⟩ : syracuseStep 657007 = 985511) B985511
theorem B984743 : Blo 654306 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B657063 : Blo 654306 657063 := bstep (se 1 (by rfl) ⟨492797, by rfl⟩ : syracuseStep 657063 = 985595) B985595
theorem B984827 : Blo 654306 984827 := bstep (se 1 (by rfl) ⟨738620, by rfl⟩ : syracuseStep 984827 = 1477241) B1477241
theorem B657147 : Blo 654306 657147 := bstep (se 1 (by rfl) ⟨492860, by rfl⟩ : syracuseStep 657147 = 985721) B985721
theorem B984863 : Blo 654306 984863 := bstep (se 1 (by rfl) ⟨738647, by rfl⟩ : syracuseStep 984863 = 1477295) B1477295
theorem B657183 : Blo 654306 657183 := bstep (se 1 (by rfl) ⟨492887, by rfl⟩ : syracuseStep 657183 = 985775) B985775
theorem B657215 : Blo 654306 657215 := bstep (se 1 (by rfl) ⟨492911, by rfl⟩ : syracuseStep 657215 = 985823) B985823
theorem B4720463 : Blo 654306 4720463 := bstep (se 1 (by rfl) ⟨3540347, by rfl⟩ : syracuseStep 4720463 = 7080695) B7080695
theorem B1476431 : Blo 654306 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B984911 : Blo 654306 984911 := bstep (se 1 (by rfl) ⟨738683, by rfl⟩ : syracuseStep 984911 = 1477367) B1477367
theorem B1476449 : Blo 654306 1476449 := bstep (se 2 (by rfl) ⟨553668, by rfl⟩ : syracuseStep 1476449 = 1107337) B1107337
theorem B1771463 : Blo 654306 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B985031 : Blo 654306 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B657391 : Blo 654306 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B8390699 : Blo 654306 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B1771645 : Blo 654306 1771645 := bstep (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) B664367
theorem B6293639 : Blo 654306 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B657563 : Blo 654306 657563 := bstep (se 1 (by rfl) ⟨493172, by rfl⟩ : syracuseStep 657563 = 986345) B986345
theorem B657599 : Blo 654306 657599 := bstep (se 1 (by rfl) ⟨493199, by rfl⟩ : syracuseStep 657599 = 986399) B986399
theorem B985385 : Blo 654306 985385 := bstep (se 2 (by rfl) ⟨369519, by rfl⟩ : syracuseStep 985385 = 739039) B739039
theorem B985391 : Blo 654306 985391 := bstep (se 1 (by rfl) ⟨739043, by rfl⟩ : syracuseStep 985391 = 1478087) B1478087
theorem B657711 : Blo 654306 657711 := bstep (se 1 (by rfl) ⟨493283, by rfl⟩ : syracuseStep 657711 = 986567) B986567
theorem B3737947 : Blo 654306 3737947 := bstep (se 1 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 3737947 = 5606921) B5606921
theorem B1477025 : Blo 654306 1477025 := bstep (se 2 (by rfl) ⟨553884, by rfl⟩ : syracuseStep 1477025 = 1107769) B1107769
theorem B657947 : Blo 654306 657947 := bstep (se 1 (by rfl) ⟨493460, by rfl⟩ : syracuseStep 657947 = 986921) B986921
theorem B1477151 : Blo 654306 1477151 := bstep (se 1 (by rfl) ⟨1107863, by rfl⟩ : syracuseStep 1477151 = 2215727) B2215727
theorem B985631 : Blo 654306 985631 := bstep (se 1 (by rfl) ⟨739223, by rfl⟩ : syracuseStep 985631 = 1478447) B1478447
theorem B657951 : Blo 654306 657951 := bstep (se 1 (by rfl) ⟨493463, by rfl⟩ : syracuseStep 657951 = 986927) B986927
theorem B4983443 : Blo 654306 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B1870523 : Blo 654306 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B658267 : Blo 654306 658267 := bstep (se 1 (by rfl) ⟨493700, by rfl⟩ : syracuseStep 658267 = 987401) B987401
theorem B986015 : Blo 654306 986015 := bstep (se 1 (by rfl) ⟨739511, by rfl⟩ : syracuseStep 986015 = 1479023) B1479023
theorem B986063 : Blo 654306 986063 := bstep (se 1 (by rfl) ⟨739547, by rfl⟩ : syracuseStep 986063 = 1479095) B1479095
theorem B986153 : Blo 654306 986153 := bstep (se 2 (by rfl) ⟨369807, by rfl⟩ : syracuseStep 986153 = 739615) B739615
theorem B986159 : Blo 654306 986159 := bstep (se 1 (by rfl) ⟨739619, by rfl⟩ : syracuseStep 986159 = 1479239) B1479239
theorem B986183 : Blo 654306 986183 := bstep (se 1 (by rfl) ⟨739637, by rfl⟩ : syracuseStep 986183 = 1479275) B1479275
theorem B1051913 : Blo 654306 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B3738905 : Blo 654306 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B986447 : Blo 654306 986447 := bstep (se 1 (by rfl) ⟨739835, by rfl⟩ : syracuseStep 986447 = 1479671) B1479671
theorem B986537 : Blo 654306 986537 := bstep (se 2 (by rfl) ⟨369951, by rfl⟩ : syracuseStep 986537 = 739903) B739903
theorem B2362871 : Blo 654306 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B4492793 : Blo 654306 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B2657855 : Blo 654306 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B986687 : Blo 654306 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B986951 : Blo 654306 986951 := bstep (se 1 (by rfl) ⟨740213, by rfl⟩ : syracuseStep 986951 = 1480427) B1480427
theorem B1478555 : Blo 654306 1478555 := bstep (se 1 (by rfl) ⟨1108916, by rfl⟩ : syracuseStep 1478555 = 2217833) B2217833
theorem B987035 : Blo 654306 987035 := bstep (se 1 (by rfl) ⟨740276, by rfl⟩ : syracuseStep 987035 = 1480553) B1480553
theorem B1478843 : Blo 654306 1478843 := bstep (se 1 (by rfl) ⟨1109132, by rfl⟩ : syracuseStep 1478843 = 2218265) B2218265
theorem B889321 : Blo 654306 889321 := bstep (se 2 (by rfl) ⟨333495, by rfl⟩ : syracuseStep 889321 = 666991) B666991
theorem B1479329 : Blo 654306 1479329 := bstep (se 2 (by rfl) ⟨554748, by rfl⟩ : syracuseStep 1479329 = 1109497) B1109497
theorem B3740363 : Blo 654306 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B1872665 : Blo 654306 1872665 := bstep (se 2 (by rfl) ⟨702249, by rfl⟩ : syracuseStep 1872665 = 1404499) B1404499
theorem B8426375 : Blo 654306 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B3740681 : Blo 654306 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B1479689 : Blo 654306 1479689 := bstep (se 2 (by rfl) ⟨554883, by rfl⟩ : syracuseStep 1479689 = 1109767) B1109767
theorem B1479743 : Blo 654306 1479743 := bstep (se 1 (by rfl) ⟨1109807, by rfl⟩ : syracuseStep 1479743 = 2219615) B2219615
theorem B76584001 : Blo 654306 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B1184873 : Blo 654306 1184873 := bstep (se 2 (by rfl) ⟨444327, by rfl⟩ : syracuseStep 1184873 = 888655) B888655
theorem B5477483 : Blo 654306 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B4199633 : Blo 654306 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1774867 : Blo 654306 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2103097 : Blo 654306 2103097 := bstep (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) B1577323
theorem B1578889 : Blo 654306 1578889 := bstep (se 2 (by rfl) ⟨592083, by rfl⟩ : syracuseStep 1578889 = 1184167) B1184167
theorem B1480679 : Blo 654306 1480679 := bstep (se 1 (by rfl) ⟨1110509, by rfl⟩ : syracuseStep 1480679 = 2221019) B2221019
theorem B1480697 : Blo 654306 1480697 := bstep (se 2 (by rfl) ⟨555261, by rfl⟩ : syracuseStep 1480697 = 1110523) B1110523
theorem B1480787 : Blo 654306 1480787 := bstep (se 1 (by rfl) ⟨1110590, by rfl⟩ : syracuseStep 1480787 = 2221181) B2221181
theorem B2365537 : Blo 654306 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B2365595 : Blo 654306 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B1480859 : Blo 654306 1480859 := bstep (se 1 (by rfl) ⟨1110644, by rfl⟩ : syracuseStep 1480859 = 2221289) B2221289
theorem B1579169 : Blo 654306 1579169 := bstep (se 2 (by rfl) ⟨592188, by rfl⟩ : syracuseStep 1579169 = 1184377) B1184377
theorem B1186055 : Blo 654306 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B1480967 : Blo 654306 1480967 := bstep (se 1 (by rfl) ⟨1110725, by rfl⟩ : syracuseStep 1480967 = 2221451) B2221451
theorem B1874249 : Blo 654306 1874249 := bstep (se 2 (by rfl) ⟨702843, by rfl⟩ : syracuseStep 1874249 = 1405687) B1405687
theorem B45390331 : Blo 654306 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B2104031 : Blo 654306 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B10623899 : Blo 654306 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B8002475 : Blo 654306 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B2104289 : Blo 654306 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B2497661 : Blo 654306 2497661 := bstep (se 3 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 2497661 = 936623) B936623
theorem B2563489 : Blo 654306 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B4202219 : Blo 654306 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B2695303 : Blo 654306 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B2368073 : Blo 654306 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B3547961 : Blo 654306 3547961 := bstep (se 2 (by rfl) ⟨1330485, by rfl⟩ : syracuseStep 3547961 = 2660971) B2660971
theorem B2106491 : Blo 654306 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B4990247 : Blo 654306 4990247 := bstep (se 1 (by rfl) ⟨3742685, by rfl⟩ : syracuseStep 4990247 = 7485371) B7485371
theorem B15148397 : Blo 654306 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B5383763 : Blo 654306 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3319379 : Blo 654306 3319379 := bstep (se 1 (by rfl) ⟨2489534, by rfl⟩ : syracuseStep 3319379 = 4979069) B4979069
theorem B2795465 : Blo 654306 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B13478051 : Blo 654306 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B2403425 : Blo 654306 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B14200055 : Blo 654306 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B28454237 : Blo 654306 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B831799 : Blo 654306 831799 := bstep (se 1 (by rfl) ⟨623849, by rfl⟩ : syracuseStep 831799 = 1247699) B1247699
theorem B9450269 : Blo 654306 9450269 := bstep (se 3 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 9450269 = 3543851) B3543851
theorem B832619 : Blo 654306 832619 := bstep (se 1 (by rfl) ⟨624464, by rfl⟩ : syracuseStep 832619 = 1248929) B1248929
theorem B3159623 : Blo 654306 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B2209463 : Blo 654306 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B2799497 : Blo 654306 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B5454253 : Blo 654306 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B2242991 : Blo 654306 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B3979975 : Blo 654306 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B2210651 : Blo 654306 2210651 := bstep (se 1 (by rfl) ⟨1657988, by rfl⟩ : syracuseStep 2210651 = 3315977) B3315977
theorem B28425107 : Blo 654306 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B736159 : Blo 654306 736159 := bstep (se 1 (by rfl) ⟨552119, by rfl⟩ : syracuseStep 736159 = 1104239) B1104239
theorem B736303 : Blo 654306 736303 := bstep (se 1 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 736303 = 1104455) B1104455
theorem B443006221 : Blo 654306 443006221 := bstep (se 3 (by rfl) ⟨83063666, by rfl⟩ : syracuseStep 443006221 = 166127333) B166127333
theorem B736591 : Blo 654306 736591 := bstep (se 1 (by rfl) ⟨552443, by rfl⟩ : syracuseStep 736591 = 1104887) B1104887
theorem B8994347 : Blo 654306 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B933439 : Blo 654306 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B2211407 : Blo 654306 2211407 := bstep (se 1 (by rfl) ⟨1658555, by rfl⟩ : syracuseStep 2211407 = 3317111) B3317111
theorem B2211515 : Blo 654306 2211515 := bstep (se 1 (by rfl) ⟨1658636, by rfl⟩ : syracuseStep 2211515 = 3317273) B3317273
theorem B737095 : Blo 654306 737095 := bstep (se 1 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 737095 = 1105643) B1105643
theorem B12009323 : Blo 654306 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B7454753 : Blo 654306 7454753 := bstep (se 2 (by rfl) ⟨2795532, by rfl⟩ : syracuseStep 7454753 = 5591065) B5591065
theorem B2244743 : Blo 654306 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B22724813 : Blo 654306 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B21250259 : Blo 654306 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B3326183 : Blo 654306 3326183 := bstep (se 1 (by rfl) ⟨2494637, by rfl⟩ : syracuseStep 3326183 = 4989275) B4989275
theorem B8667575 : Blo 654306 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B737743 : Blo 654306 737743 := bstep (se 1 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 737743 = 1106615) B1106615
theorem B2802215 : Blo 654306 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B2245619 : Blo 654306 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B738715 : Blo 654306 738715 := bstep (se 1 (by rfl) ⟨554036, by rfl⟩ : syracuseStep 738715 = 1108073) B1108073
theorem B2213459 : Blo 654306 2213459 := bstep (se 1 (by rfl) ⟨1660094, by rfl⟩ : syracuseStep 2213459 = 3320189) B3320189
theorem B3327641 : Blo 654306 3327641 := bstep (se 2 (by rfl) ⟨1247865, by rfl⟩ : syracuseStep 3327641 = 2495731) B2495731
theorem B7980767 : Blo 654306 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B2213729 : Blo 654306 2213729 := bstep (se 2 (by rfl) ⟨830148, by rfl⟩ : syracuseStep 2213729 = 1660297) B1660297
theorem B935911 : Blo 654306 935911 := bstep (se 1 (by rfl) ⟨701933, by rfl⟩ : syracuseStep 935911 = 1403867) B1403867
theorem B936031 : Blo 654306 936031 := bstep (se 1 (by rfl) ⟨702023, by rfl⟩ : syracuseStep 936031 = 1404047) B1404047
theorem B936127 : Blo 654306 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B245057879 : Blo 654306 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B739867 : Blo 654306 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B2214431 : Blo 654306 2214431 := bstep (se 1 (by rfl) ⟨1660823, by rfl⟩ : syracuseStep 2214431 = 3321647) B3321647
theorem B3361385 : Blo 654306 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B1657655 : Blo 654306 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B7588703 : Blo 654306 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B47893355 : Blo 654306 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B1658191 : Blo 654306 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1330679 : Blo 654306 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B4214267 : Blo 654306 4214267 := bstep (se 1 (by rfl) ⟨3160700, by rfl⟩ : syracuseStep 4214267 = 6321401) B6321401
theorem B2215835 : Blo 654306 2215835 := bstep (se 1 (by rfl) ⟨1661876, by rfl⟩ : syracuseStep 2215835 = 3323753) B3323753
theorem B3330233 : Blo 654306 3330233 := bstep (se 2 (by rfl) ⟨1248837, by rfl⟩ : syracuseStep 3330233 = 2497675) B2497675
theorem B22794533 : Blo 654306 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B2806127 : Blo 654306 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B1659487 : Blo 654306 1659487 := bstep (se 1 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 1659487 = 2489231) B2489231
theorem B2806589 : Blo 654306 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B2216969 : Blo 654306 2216969 := bstep (se 2 (by rfl) ⟨831363, by rfl⟩ : syracuseStep 2216969 = 1662727) B1662727
theorem B2217023 : Blo 654306 2217023 := bstep (se 1 (by rfl) ⟨1662767, by rfl⟩ : syracuseStep 2217023 = 3325535) B3325535
theorem B1660115 : Blo 654306 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B1463879 : Blo 654306 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B3332339 : Blo 654306 3332339 := bstep (se 1 (by rfl) ⟨2499254, by rfl⟩ : syracuseStep 3332339 = 4998509) B4998509
theorem B1104185 : Blo 654306 1104185 := bstep (se 2 (by rfl) ⟨414069, by rfl⟩ : syracuseStep 1104185 = 828139) B828139
theorem B1104799 : Blo 654306 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B1105231 : Blo 654306 1105231 := bstep (se 1 (by rfl) ⟨828923, by rfl⟩ : syracuseStep 1105231 = 1657847) B1657847
theorem B5332385 : Blo 654306 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B1105319 : Blo 654306 1105319 := bstep (se 1 (by rfl) ⟨828989, by rfl⟩ : syracuseStep 1105319 = 1657979) B1657979
theorem B1105481 : Blo 654306 1105481 := bstep (se 2 (by rfl) ⟨414555, by rfl⟩ : syracuseStep 1105481 = 829111) B829111
theorem B1892027 : Blo 654306 1892027 := bstep (se 1 (by rfl) ⟨1419020, by rfl⟩ : syracuseStep 1892027 = 2838041) B2838041
theorem B1662707 : Blo 654306 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B2219831 : Blo 654306 2219831 := bstep (se 1 (by rfl) ⟨1664873, by rfl⟩ : syracuseStep 2219831 = 3329747) B3329747
theorem B64642991 : Blo 654306 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B2220263 : Blo 654306 2220263 := bstep (se 1 (by rfl) ⟨1665197, by rfl⟩ : syracuseStep 2220263 = 3330395) B3330395
theorem B3727741 : Blo 654306 3727741 := bstep (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) B1397903
theorem B1106527 : Blo 654306 1106527 := bstep (se 1 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 1106527 = 1659791) B1659791
theorem B2220857 : Blo 654306 2220857 := bstep (se 2 (by rfl) ⟨832821, by rfl⟩ : syracuseStep 2220857 = 1665643) B1665643
theorem B2220911 : Blo 654306 2220911 := bstep (se 1 (by rfl) ⟨1665683, by rfl⟩ : syracuseStep 2220911 = 3331367) B3331367
theorem B5039003 : Blo 654306 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B1106939 : Blo 654306 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B1107371 : Blo 654306 1107371 := bstep (se 1 (by rfl) ⟨830528, by rfl⟩ : syracuseStep 1107371 = 1661057) B1661057
theorem B3729017 : Blo 654306 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B31975033 : Blo 654306 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B2221721 : Blo 654306 2221721 := bstep (se 2 (by rfl) ⟨833145, by rfl⟩ : syracuseStep 2221721 = 1666291) B1666291
theorem B1107911 : Blo 654306 1107911 := bstep (se 1 (by rfl) ⟨830933, by rfl⟩ : syracuseStep 1107911 = 1661867) B1661867
theorem B2484371 : Blo 654306 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B1108201 : Blo 654306 1108201 := bstep (se 2 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 1108201 = 831151) B831151
theorem B1665319 : Blo 654306 1665319 := bstep (se 1 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 1665319 = 2497979) B2497979
theorem B1403183 : Blo 654306 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B1993223 : Blo 654306 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B1108667 : Blo 654306 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B3795767 : Blo 654306 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B4484231 : Blo 654306 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B1666271 : Blo 654306 1666271 := bstep (se 1 (by rfl) ⟨1249703, by rfl⟩ : syracuseStep 1666271 = 2499407) B2499407
theorem B2125673 : Blo 654306 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B1109983 : Blo 654306 1109983 := bstep (se 1 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 1109983 = 1664975) B1664975
theorem B1863803 : Blo 654306 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B2126089 : Blo 654306 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B6320551 : Blo 654306 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B1110631 : Blo 654306 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B3732115 : Blo 654306 3732115 := bstep (se 1 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 3732115 = 5598173) B5598173
theorem B1110793 : Blo 654306 1110793 := bstep (se 2 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 1110793 = 833095) B833095
theorem B1242695 : Blo 654306 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B2488259 : Blo 654306 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B7075937 : Blo 654306 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B1243279 : Blo 654306 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B18938123 : Blo 654306 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B4192685 : Blo 654306 4192685 := bstep (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) B1572257
theorem B2128403 : Blo 654306 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B981641 : Blo 654306 981641 := bstep (se 2 (by rfl) ⟨368115, by rfl⟩ : syracuseStep 981641 = 736231) B736231
theorem B1866377 : Blo 654306 1866377 := bstep (se 2 (by rfl) ⟨699891, by rfl⟩ : syracuseStep 1866377 = 1399783) B1399783
theorem B981815 : Blo 654306 981815 := bstep (se 1 (by rfl) ⟨736361, by rfl⟩ : syracuseStep 981815 = 1472723) B1472723
theorem B981851 : Blo 654306 981851 := bstep (se 1 (by rfl) ⟨736388, by rfl⟩ : syracuseStep 981851 = 1472777) B1472777
theorem B1473371 : Blo 654306 1473371 := bstep (se 1 (by rfl) ⟨1105028, by rfl⟩ : syracuseStep 1473371 = 2210057) B2210057
theorem B981995 : Blo 654306 981995 := bstep (se 1 (by rfl) ⟨736496, by rfl⟩ : syracuseStep 981995 = 1472993) B1472993
theorem B654383 : Blo 654306 654383 := bstep (se 1 (by rfl) ⟨490787, by rfl⟩ : syracuseStep 654383 = 981575) B981575
theorem B654407 : Blo 654306 654407 := bstep (se 1 (by rfl) ⟨490805, by rfl⟩ : syracuseStep 654407 = 981611) B981611
theorem B982199 : Blo 654306 982199 := bstep (se 1 (by rfl) ⟨736649, by rfl⟩ : syracuseStep 982199 = 1473299) B1473299
theorem B654559 : Blo 654306 654559 := bstep (se 1 (by rfl) ⟨490919, by rfl⟩ : syracuseStep 654559 = 981839) B981839
theorem B1867175 : Blo 654306 1867175 := bstep (se 1 (by rfl) ⟨1400381, by rfl⟩ : syracuseStep 1867175 = 2800763) B2800763
theorem B982439 : Blo 654306 982439 := bstep (se 1 (by rfl) ⟨736829, by rfl⟩ : syracuseStep 982439 = 1473659) B1473659
theorem B4488635 : Blo 654306 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B8388035 : Blo 654306 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B654823 : Blo 654306 654823 := bstep (se 1 (by rfl) ⟨491117, by rfl⟩ : syracuseStep 654823 = 982235) B982235
theorem B982523 : Blo 654306 982523 := bstep (se 1 (by rfl) ⟨736892, by rfl⟩ : syracuseStep 982523 = 1473785) B1473785
theorem B2653703 : Blo 654306 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B1474127 : Blo 654306 1474127 := bstep (se 1 (by rfl) ⟨1105595, by rfl⟩ : syracuseStep 1474127 = 2211191) B2211191
theorem B654939 : Blo 654306 654939 := bstep (se 1 (by rfl) ⟨491204, by rfl⟩ : syracuseStep 654939 = 982409) B982409
theorem B982619 : Blo 654306 982619 := bstep (se 1 (by rfl) ⟨736964, by rfl⟩ : syracuseStep 982619 = 1473929) B1473929
theorem B982703 : Blo 654306 982703 := bstep (se 1 (by rfl) ⟨737027, by rfl⟩ : syracuseStep 982703 = 1474055) B1474055
theorem B982823 : Blo 654306 982823 := bstep (se 1 (by rfl) ⟨737117, by rfl⟩ : syracuseStep 982823 = 1474235) B1474235
theorem B655175 : Blo 654306 655175 := bstep (se 1 (by rfl) ⟨491381, by rfl⟩ : syracuseStep 655175 = 982763) B982763
theorem B982907 : Blo 654306 982907 := bstep (se 1 (by rfl) ⟨737180, by rfl⟩ : syracuseStep 982907 = 1474361) B1474361
theorem B655327 : Blo 654306 655327 := bstep (se 1 (by rfl) ⟨491495, by rfl⟩ : syracuseStep 655327 = 982991) B982991
theorem B983231 : Blo 654306 983231 := bstep (se 1 (by rfl) ⟨737423, by rfl⟩ : syracuseStep 983231 = 1474847) B1474847
theorem B655551 : Blo 654306 655551 := bstep (se 1 (by rfl) ⟨491663, by rfl⟩ : syracuseStep 655551 = 983327) B983327
theorem B655567 : Blo 654306 655567 := bstep (se 1 (by rfl) ⟨491675, by rfl⟩ : syracuseStep 655567 = 983351) B983351
theorem B786667 : Blo 654306 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B655615 : Blo 654306 655615 := bstep (se 1 (by rfl) ⟨491711, by rfl⟩ : syracuseStep 655615 = 983423) B983423
theorem B655663 : Blo 654306 655663 := bstep (se 1 (by rfl) ⟨491747, by rfl⟩ : syracuseStep 655663 = 983495) B983495
theorem B1868143 : Blo 654306 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B1245611 : Blo 654306 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B655899 : Blo 654306 655899 := bstep (se 1 (by rfl) ⟨491924, by rfl⟩ : syracuseStep 655899 = 983849) B983849
theorem B655903 : Blo 654306 655903 := bstep (se 1 (by rfl) ⟨491927, by rfl⟩ : syracuseStep 655903 = 983855) B983855
theorem B983657 : Blo 654306 983657 := bstep (se 2 (by rfl) ⟨368871, by rfl⟩ : syracuseStep 983657 = 737743) B737743
theorem B983663 : Blo 654306 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B655983 : Blo 654306 655983 := bstep (se 1 (by rfl) ⟨491987, by rfl⟩ : syracuseStep 655983 = 983975) B983975
theorem B656039 : Blo 654306 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B656079 : Blo 654306 656079 := bstep (se 1 (by rfl) ⟨492059, by rfl⟩ : syracuseStep 656079 = 984119) B984119
theorem B656159 : Blo 654306 656159 := bstep (se 1 (by rfl) ⟨492119, by rfl⟩ : syracuseStep 656159 = 984239) B984239
theorem B1475369 : Blo 654306 1475369 := bstep (se 2 (by rfl) ⟨553263, by rfl⟩ : syracuseStep 1475369 = 1106527) B1106527
theorem B656431 : Blo 654306 656431 := bstep (se 1 (by rfl) ⟨492323, by rfl⟩ : syracuseStep 656431 = 984647) B984647
theorem B1475639 : Blo 654306 1475639 := bstep (se 1 (by rfl) ⟨1106729, by rfl⟩ : syracuseStep 1475639 = 2213459) B2213459
theorem B656495 : Blo 654306 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B656551 : Blo 654306 656551 := bstep (se 1 (by rfl) ⟨492413, by rfl⟩ : syracuseStep 656551 = 984827) B984827
theorem B656575 : Blo 654306 656575 := bstep (se 1 (by rfl) ⟨492431, by rfl⟩ : syracuseStep 656575 = 984863) B984863
theorem B3146975 : Blo 654306 3146975 := bstep (se 1 (by rfl) ⟨2360231, by rfl⟩ : syracuseStep 3146975 = 4720463) B4720463
theorem B984287 : Blo 654306 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B656607 : Blo 654306 656607 := bstep (se 1 (by rfl) ⟨492455, by rfl⟩ : syracuseStep 656607 = 984911) B984911
theorem B1475819 : Blo 654306 1475819 := bstep (se 1 (by rfl) ⟨1106864, by rfl⟩ : syracuseStep 1475819 = 2213729) B2213729
theorem B984299 : Blo 654306 984299 := bstep (se 1 (by rfl) ⟨738224, by rfl⟩ : syracuseStep 984299 = 1476449) B1476449
theorem B1180975 : Blo 654306 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B656687 : Blo 654306 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B656923 : Blo 654306 656923 := bstep (se 1 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 656923 = 985385) B985385
theorem B656927 : Blo 654306 656927 := bstep (se 1 (by rfl) ⟨492695, by rfl⟩ : syracuseStep 656927 = 985391) B985391
theorem B984683 : Blo 654306 984683 := bstep (se 1 (by rfl) ⟨738512, by rfl⟩ : syracuseStep 984683 = 1477025) B1477025
theorem B1476287 : Blo 654306 1476287 := bstep (se 1 (by rfl) ⟨1107215, by rfl⟩ : syracuseStep 1476287 = 2214431) B2214431
theorem B984767 : Blo 654306 984767 := bstep (se 1 (by rfl) ⟨738575, by rfl⟩ : syracuseStep 984767 = 1477151) B1477151
theorem B657087 : Blo 654306 657087 := bstep (se 1 (by rfl) ⟨492815, by rfl⟩ : syracuseStep 657087 = 985631) B985631
theorem B1247015 : Blo 654306 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B984953 : Blo 654306 984953 := bstep (se 2 (by rfl) ⟨369357, by rfl⟩ : syracuseStep 984953 = 738715) B738715
theorem B657343 : Blo 654306 657343 := bstep (se 1 (by rfl) ⟨493007, by rfl⟩ : syracuseStep 657343 = 986015) B986015
theorem B657375 : Blo 654306 657375 := bstep (se 1 (by rfl) ⟨493031, by rfl⟩ : syracuseStep 657375 = 986063) B986063
theorem B657435 : Blo 654306 657435 := bstep (se 1 (by rfl) ⟨493076, by rfl⟩ : syracuseStep 657435 = 986153) B986153
theorem B657439 : Blo 654306 657439 := bstep (se 1 (by rfl) ⟨493079, by rfl⟩ : syracuseStep 657439 = 986159) B986159
theorem B657455 : Blo 654306 657455 := bstep (se 1 (by rfl) ⟨493091, by rfl⟩ : syracuseStep 657455 = 986183) B986183
theorem B42633377 : Blo 654306 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B2492603 : Blo 654306 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B657631 : Blo 654306 657631 := bstep (se 1 (by rfl) ⟨493223, by rfl⟩ : syracuseStep 657631 = 986447) B986447
theorem B657691 : Blo 654306 657691 := bstep (se 1 (by rfl) ⟨493268, by rfl⟩ : syracuseStep 657691 = 986537) B986537
theorem B887119 : Blo 654306 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1771903 : Blo 654306 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B657791 : Blo 654306 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B657967 : Blo 654306 657967 := bstep (se 1 (by rfl) ⟨493475, by rfl⟩ : syracuseStep 657967 = 986951) B986951
theorem B1477223 : Blo 654306 1477223 := bstep (se 1 (by rfl) ⟨1107917, by rfl⟩ : syracuseStep 1477223 = 2215835) B2215835
theorem B985703 : Blo 654306 985703 := bstep (se 1 (by rfl) ⟨739277, by rfl⟩ : syracuseStep 985703 = 1478555) B1478555
theorem B658023 : Blo 654306 658023 := bstep (se 1 (by rfl) ⟨493517, by rfl⟩ : syracuseStep 658023 = 987035) B987035
theorem B1247881 : Blo 654306 1247881 := bstep (se 2 (by rfl) ⟨467955, by rfl⟩ : syracuseStep 1247881 = 935911) B935911
theorem B985895 : Blo 654306 985895 := bstep (se 1 (by rfl) ⟨739421, by rfl⟩ : syracuseStep 985895 = 1478843) B1478843
theorem B1248041 : Blo 654306 1248041 := bstep (se 2 (by rfl) ⟨468015, by rfl⟩ : syracuseStep 1248041 = 936031) B936031
theorem B2362193 : Blo 654306 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B1870751 : Blo 654306 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B1477601 : Blo 654306 1477601 := bstep (se 2 (by rfl) ⟨554100, by rfl⟩ : syracuseStep 1477601 = 1108201) B1108201
theorem B986219 : Blo 654306 986219 := bstep (se 1 (by rfl) ⟨739664, by rfl⟩ : syracuseStep 986219 = 1479329) B1479329
theorem B4983929 : Blo 654306 4983929 := bstep (se 2 (by rfl) ⟨1868973, by rfl⟩ : syracuseStep 4983929 = 3737947) B3737947
theorem B2493575 : Blo 654306 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B1248443 : Blo 654306 1248443 := bstep (se 1 (by rfl) ⟨936332, by rfl⟩ : syracuseStep 1248443 = 1872665) B1872665
theorem B1871059 : Blo 654306 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B2493787 : Blo 654306 2493787 := bstep (se 1 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 2493787 = 3740681) B3740681
theorem B1477979 : Blo 654306 1477979 := bstep (se 1 (by rfl) ⟨1108484, by rfl⟩ : syracuseStep 1477979 = 2216969) B2216969
theorem B986459 : Blo 654306 986459 := bstep (se 1 (by rfl) ⟨739844, by rfl⟩ : syracuseStep 986459 = 1479689) B1479689
theorem B986489 : Blo 654306 986489 := bstep (se 2 (by rfl) ⟨369933, by rfl⟩ : syracuseStep 986489 = 739867) B739867
theorem B1478015 : Blo 654306 1478015 := bstep (se 1 (by rfl) ⟨1108511, by rfl⟩ : syracuseStep 1478015 = 2217023) B2217023
theorem B986495 : Blo 654306 986495 := bstep (se 1 (by rfl) ⟨739871, by rfl⟩ : syracuseStep 986495 = 1479743) B1479743
theorem B987119 : Blo 654306 987119 := bstep (se 1 (by rfl) ⟨740339, by rfl⟩ : syracuseStep 987119 = 1480679) B1480679
theorem B987131 : Blo 654306 987131 := bstep (se 1 (by rfl) ⟨740348, by rfl⟩ : syracuseStep 987131 = 1480697) B1480697
theorem B987191 : Blo 654306 987191 := bstep (se 1 (by rfl) ⟨740393, by rfl⟩ : syracuseStep 987191 = 1480787) B1480787
theorem B1577063 : Blo 654306 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B987239 : Blo 654306 987239 := bstep (se 1 (by rfl) ⟨740429, by rfl⟩ : syracuseStep 987239 = 1480859) B1480859
theorem B1052779 : Blo 654306 1052779 := bstep (se 1 (by rfl) ⟨789584, by rfl⟩ : syracuseStep 1052779 = 1579169) B1579169
theorem B790703 : Blo 654306 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B987311 : Blo 654306 987311 := bstep (se 1 (by rfl) ⟨740483, by rfl⟩ : syracuseStep 987311 = 1480967) B1480967
theorem B3903677 : Blo 654306 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B1249499 : Blo 654306 1249499 := bstep (se 1 (by rfl) ⟨937124, by rfl⟩ : syracuseStep 1249499 = 1874249) B1874249
theorem B7082599 : Blo 654306 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B1479887 : Blo 654306 1479887 := bstep (se 1 (by rfl) ⟨1109915, by rfl⟩ : syracuseStep 1479887 = 2219831) B2219831
theorem B1479977 : Blo 654306 1479977 := bstep (se 2 (by rfl) ⟨554991, by rfl⟩ : syracuseStep 1479977 = 1109983) B1109983
theorem B1480175 : Blo 654306 1480175 := bstep (se 1 (by rfl) ⟨1110131, by rfl⟩ : syracuseStep 1480175 = 2220263) B2220263
theorem B16783037 : Blo 654306 16783037 := bstep (se 3 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 16783037 = 6293639) B6293639
theorem B2365307 : Blo 654306 2365307 := bstep (se 1 (by rfl) ⟨1773980, by rfl⟩ : syracuseStep 2365307 = 3547961) B3547961
theorem B1480571 : Blo 654306 1480571 := bstep (se 1 (by rfl) ⟨1110428, by rfl⟩ : syracuseStep 1480571 = 2220857) B2220857
theorem B8427401 : Blo 654306 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B1480607 : Blo 654306 1480607 := bstep (se 1 (by rfl) ⟨1110455, by rfl⟩ : syracuseStep 1480607 = 2220911) B2220911
theorem B1185761 : Blo 654306 1185761 := bstep (se 2 (by rfl) ⟨444660, by rfl⟩ : syracuseStep 1185761 = 889321) B889321
theorem B3741821 : Blo 654306 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B1480841 : Blo 654306 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B10098931 : Blo 654306 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B1481057 : Blo 654306 1481057 := bstep (se 2 (by rfl) ⟨555396, by rfl⟩ : syracuseStep 1481057 = 1110793) B1110793
theorem B1481147 : Blo 654306 1481147 := bstep (se 1 (by rfl) ⟨1110860, by rfl⟩ : syracuseStep 1481147 = 2221721) B2221721
theorem B5675741 : Blo 654306 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B102112001 : Blo 654306 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B8985367 : Blo 654306 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B2366489 : Blo 654306 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2530511 : Blo 654306 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B2989487 : Blo 654306 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B2105185 : Blo 654306 2105185 := bstep (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) B1578889
theorem B1417115 : Blo 654306 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B3154049 : Blo 654306 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B6300179 : Blo 654306 6300179 := bstep (se 1 (by rfl) ⟨4725134, by rfl⟩ : syracuseStep 6300179 = 9450269) B9450269
theorem B828463 : Blo 654306 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B2106415 : Blo 654306 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B11969693 : Blo 654306 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B6300989 : Blo 654306 6300989 := bstep (se 3 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 6300989 = 2362871) B2362871
theorem B12625415 : Blo 654306 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B2795123 : Blo 654306 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B3417985 : Blo 654306 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B18950071 : Blo 654306 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B8006215 : Blo 654306 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B14166839 : Blo 654306 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B5778383 : Blo 654306 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B60599501 : Blo 654306 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B700007 : Blo 654306 700007 := bstep (se 1 (by rfl) ⟨525005, by rfl⟩ : syracuseStep 700007 = 1050011) B1050011
theorem B4992677 : Blo 654306 4992677 := bstep (se 4 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 4992677 = 936127) B936127
theorem B5320511 : Blo 654306 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B3322295 : Blo 654306 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B5059135 : Blo 654306 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B31928903 : Blo 654306 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B3159661 : Blo 654306 3159661 := bstep (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) B1184873
theorem B5617309 : Blo 654306 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B5617583 : Blo 654306 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B3651655 : Blo 654306 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B2799755 : Blo 654306 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B736123 : Blo 654306 736123 := bstep (se 1 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 736123 = 1104185) B1104185
theorem B2210921 : Blo 654306 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B3554923 : Blo 654306 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B736879 : Blo 654306 736879 := bstep (se 1 (by rfl) ⟨552659, by rfl⟩ : syracuseStep 736879 = 1105319) B1105319
theorem B736987 : Blo 654306 736987 := bstep (se 1 (by rfl) ⟨552740, by rfl⟩ : syracuseStep 736987 = 1105481) B1105481
theorem B1261351 : Blo 654306 1261351 := bstep (se 1 (by rfl) ⟨946013, by rfl⟩ : syracuseStep 1261351 = 1892027) B1892027
theorem B2801479 : Blo 654306 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B2834785 : Blo 654306 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B3359335 : Blo 654306 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B737959 : Blo 654306 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B2212649 : Blo 654306 2212649 := bstep (se 2 (by rfl) ⟨829743, by rfl⟩ : syracuseStep 2212649 = 1659487) B1659487
theorem B3326831 : Blo 654306 3326831 := bstep (se 1 (by rfl) ⟨2495123, by rfl⟩ : syracuseStep 3326831 = 4990247) B4990247
theorem B738247 : Blo 654306 738247 := bstep (se 1 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 738247 = 1107371) B1107371
theorem B3589175 : Blo 654306 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B2212919 : Blo 654306 2212919 := bstep (se 1 (by rfl) ⟨1659689, by rfl⟩ : syracuseStep 2212919 = 3319379) B3319379
theorem B5981309 : Blo 654306 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B738607 : Blo 654306 738607 := bstep (se 1 (by rfl) ⟨553955, by rfl⟩ : syracuseStep 738607 = 1107911) B1107911
theorem B1656247 : Blo 654306 1656247 := bstep (se 1 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 1656247 = 2484371) B2484371
theorem B8963693 : Blo 654306 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B1328815 : Blo 654306 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B739111 : Blo 654306 739111 := bstep (se 1 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 739111 = 1108667) B1108667
theorem B2804129 : Blo 654306 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B1657705 : Blo 654306 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B2805101 : Blo 654306 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B1658839 : Blo 654306 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B11980781 : Blo 654306 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B689525237 : Blo 654306 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B5592023 : Blo 654306 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B4969835 : Blo 654306 4969835 := bstep (se 1 (by rfl) ⟨3727376, by rfl⟩ : syracuseStep 4969835 = 7454753) B7454753
theorem B1496495 : Blo 654306 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B2217455 : Blo 654306 2217455 := bstep (se 1 (by rfl) ⟨1663091, by rfl⟩ : syracuseStep 2217455 = 3326183) B3326183
theorem B3593737 : Blo 654306 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B4970321 : Blo 654306 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B1660763 : Blo 654306 1660763 := bstep (se 1 (by rfl) ⟨1245572, by rfl⟩ : syracuseStep 1660763 = 2491145) B2491145
theorem B1497079 : Blo 654306 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B2218427 : Blo 654306 2218427 := bstep (se 1 (by rfl) ⟨1663820, by rfl⟩ : syracuseStep 2218427 = 3327641) B3327641
theorem B5593799 : Blo 654306 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B6314861 : Blo 654306 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B163371919 : Blo 654306 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B1105103 : Blo 654306 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B2809511 : Blo 654306 2809511 := bstep (se 1 (by rfl) ⟨2107133, by rfl⟩ : syracuseStep 2809511 = 4214267) B4214267
theorem B2220155 : Blo 654306 2220155 := bstep (se 1 (by rfl) ⟨1665116, by rfl⟩ : syracuseStep 2220155 = 3330233) B3330233
theorem B15196355 : Blo 654306 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B2220317 : Blo 654306 2220317 := bstep (se 3 (by rfl) ⟨416309, by rfl⟩ : syracuseStep 2220317 = 832619) B832619
theorem B2220425 : Blo 654306 2220425 := bstep (se 2 (by rfl) ⟨832659, by rfl⟩ : syracuseStep 2220425 = 1665319) B1665319
theorem B1106743 : Blo 654306 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B2221559 : Blo 654306 2221559 := bstep (se 1 (by rfl) ⟨1666169, by rfl⟩ : syracuseStep 2221559 = 3332339) B3332339
theorem B1402687 : Blo 654306 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B5334983 : Blo 654306 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1402859 : Blo 654306 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B1665107 : Blo 654306 1665107 := bstep (se 1 (by rfl) ⟨1248830, by rfl⟩ : syracuseStep 1665107 = 2497661) B2497661
theorem B1108471 : Blo 654306 1108471 := bstep (se 1 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 1108471 = 1662707) B1662707
theorem B1109065 : Blo 654306 1109065 := bstep (se 2 (by rfl) ⟨415899, by rfl⟩ : syracuseStep 1109065 = 831799) B831799
theorem B4976153 : Blo 654306 4976153 := bstep (se 2 (by rfl) ⟨1866057, by rfl⟩ : syracuseStep 4976153 = 3732115) B3732115
theorem B2486011 : Blo 654306 2486011 := bstep (se 1 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 2486011 = 3729017) B3729017
theorem B1863643 : Blo 654306 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B1602283 : Blo 654306 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1110847 : Blo 654306 1110847 := bstep (se 1 (by rfl) ⟨833135, by rfl⟩ : syracuseStep 1110847 = 1666271) B1666271
theorem B9466703 : Blo 654306 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B18969491 : Blo 654306 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1242535 : Blo 654306 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B7272337 : Blo 654306 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B60520441 : Blo 654306 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B5306633 : Blo 654306 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B1472975 : Blo 654306 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B981545 : Blo 654306 981545 := bstep (se 2 (by rfl) ⟨368079, by rfl⟩ : syracuseStep 981545 = 736159) B736159
theorem B1473065 : Blo 654306 1473065 := bstep (se 2 (by rfl) ⟨552399, by rfl⟩ : syracuseStep 1473065 = 1104799) B1104799
theorem B1866331 : Blo 654306 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B981737 : Blo 654306 981737 := bstep (se 2 (by rfl) ⟨368151, by rfl⟩ : syracuseStep 981737 = 736303) B736303
theorem B4717291 : Blo 654306 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B590674961 : Blo 654306 590674961 := bstep (se 2 (by rfl) ⟨221503110, by rfl⟩ : syracuseStep 590674961 = 443006221) B443006221
theorem B654427 : Blo 654306 654427 := bstep (se 1 (by rfl) ⟨490820, by rfl⟩ : syracuseStep 654427 = 981641) B981641
theorem B1244251 : Blo 654306 1244251 := bstep (se 1 (by rfl) ⟨933188, by rfl⟩ : syracuseStep 1244251 = 1866377) B1866377
theorem B982121 : Blo 654306 982121 := bstep (se 2 (by rfl) ⟨368295, by rfl⟩ : syracuseStep 982121 = 736591) B736591
theorem B1473641 : Blo 654306 1473641 := bstep (se 2 (by rfl) ⟨552615, by rfl⟩ : syracuseStep 1473641 = 1105231) B1105231
theorem B654543 : Blo 654306 654543 := bstep (se 1 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 654543 = 981815) B981815
theorem B654567 : Blo 654306 654567 := bstep (se 1 (by rfl) ⟨490925, by rfl⟩ : syracuseStep 654567 = 981851) B981851
theorem B982247 : Blo 654306 982247 := bstep (se 1 (by rfl) ⟨736685, by rfl⟩ : syracuseStep 982247 = 1473371) B1473371
theorem B1473767 : Blo 654306 1473767 := bstep (se 1 (by rfl) ⟨1105325, by rfl⟩ : syracuseStep 1473767 = 2210651) B2210651
theorem B654663 : Blo 654306 654663 := bstep (se 1 (by rfl) ⟨490997, by rfl⟩ : syracuseStep 654663 = 981995) B981995
theorem B1244585 : Blo 654306 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B654799 : Blo 654306 654799 := bstep (se 1 (by rfl) ⟨491099, by rfl⟩ : syracuseStep 654799 = 982199) B982199
theorem B654959 : Blo 654306 654959 := bstep (se 1 (by rfl) ⟨491219, by rfl⟩ : syracuseStep 654959 = 982439) B982439
theorem B1244783 : Blo 654306 1244783 := bstep (se 1 (by rfl) ⟨933587, by rfl⟩ : syracuseStep 1244783 = 1867175) B1867175
theorem B655015 : Blo 654306 655015 := bstep (se 1 (by rfl) ⟨491261, by rfl⟩ : syracuseStep 655015 = 982523) B982523
theorem B1769135 : Blo 654306 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B5996231 : Blo 654306 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B982751 : Blo 654306 982751 := bstep (se 1 (by rfl) ⟨737063, by rfl⟩ : syracuseStep 982751 = 1474127) B1474127
theorem B1474271 : Blo 654306 1474271 := bstep (se 1 (by rfl) ⟨1105703, by rfl⟩ : syracuseStep 1474271 = 2211407) B2211407
theorem B655079 : Blo 654306 655079 := bstep (se 1 (by rfl) ⟨491309, by rfl⟩ : syracuseStep 655079 = 982619) B982619
theorem B982793 : Blo 654306 982793 := bstep (se 2 (by rfl) ⟨368547, by rfl⟩ : syracuseStep 982793 = 737095) B737095
theorem B655135 : Blo 654306 655135 := bstep (se 1 (by rfl) ⟨491351, by rfl⟩ : syracuseStep 655135 = 982703) B982703
theorem B1474343 : Blo 654306 1474343 := bstep (se 1 (by rfl) ⟨1105757, by rfl⟩ : syracuseStep 1474343 = 2211515) B2211515
theorem B655215 : Blo 654306 655215 := bstep (se 1 (by rfl) ⟨491411, by rfl⟩ : syracuseStep 655215 = 982823) B982823
theorem B655271 : Blo 654306 655271 := bstep (se 1 (by rfl) ⟨491453, by rfl⟩ : syracuseStep 655271 = 982907) B982907
theorem B655487 : Blo 654306 655487 := bstep (se 1 (by rfl) ⟨491615, by rfl⟩ : syracuseStep 655487 = 983231) B983231
theorem B1048889 : Blo 654306 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B655771 : Blo 654306 655771 := bstep (se 1 (by rfl) ⟨491828, by rfl⟩ : syracuseStep 655771 = 983657) B983657
theorem B655775 : Blo 654306 655775 := bstep (se 1 (by rfl) ⟨491831, by rfl⟩ : syracuseStep 655775 = 983663) B983663
theorem B2490857 : Blo 654306 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B1475099 : Blo 654306 1475099 := bstep (se 1 (by rfl) ⟨1106324, by rfl⟩ : syracuseStep 1475099 = 2212649) B2212649
theorem B983579 : Blo 654306 983579 := bstep (se 1 (by rfl) ⟨737684, by rfl⟩ : syracuseStep 983579 = 1475369) B1475369
theorem B2392783 : Blo 654306 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B1475279 : Blo 654306 1475279 := bstep (se 1 (by rfl) ⟨1106459, by rfl⟩ : syracuseStep 1475279 = 2212919) B2212919
theorem B983759 : Blo 654306 983759 := bstep (se 1 (by rfl) ⟨737819, by rfl⟩ : syracuseStep 983759 = 1475639) B1475639
theorem B2097983 : Blo 654306 2097983 := bstep (se 1 (by rfl) ⟨1573487, by rfl⟩ : syracuseStep 2097983 = 3146975) B3146975
theorem B656191 : Blo 654306 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B983879 : Blo 654306 983879 := bstep (se 1 (by rfl) ⟨737909, by rfl⟩ : syracuseStep 983879 = 1475819) B1475819
theorem B656199 : Blo 654306 656199 := bstep (se 1 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 656199 = 984299) B984299
theorem B983945 : Blo 654306 983945 := bstep (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) B737959
theorem B656455 : Blo 654306 656455 := bstep (se 1 (by rfl) ⟨492341, by rfl⟩ : syracuseStep 656455 = 984683) B984683
theorem B1475657 : Blo 654306 1475657 := bstep (se 2 (by rfl) ⟨553371, by rfl⟩ : syracuseStep 1475657 = 1106743) B1106743
theorem B984191 : Blo 654306 984191 := bstep (se 1 (by rfl) ⟨738143, by rfl⟩ : syracuseStep 984191 = 1476287) B1476287
theorem B656511 : Blo 654306 656511 := bstep (se 1 (by rfl) ⟨492383, by rfl⟩ : syracuseStep 656511 = 984767) B984767
theorem B656635 : Blo 654306 656635 := bstep (se 1 (by rfl) ⟨492476, by rfl⟩ : syracuseStep 656635 = 984953) B984953
theorem B984329 : Blo 654306 984329 := bstep (se 2 (by rfl) ⟨369123, by rfl⟩ : syracuseStep 984329 = 738247) B738247
theorem B1869419 : Blo 654306 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B1574633 : Blo 654306 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B984809 : Blo 654306 984809 := bstep (se 2 (by rfl) ⟨369303, by rfl⟩ : syracuseStep 984809 = 738607) B738607
theorem B984815 : Blo 654306 984815 := bstep (se 1 (by rfl) ⟨738611, by rfl⟩ : syracuseStep 984815 = 1477223) B1477223
theorem B657135 : Blo 654306 657135 := bstep (se 1 (by rfl) ⟨492851, by rfl⟩ : syracuseStep 657135 = 985703) B985703
theorem B657263 : Blo 654306 657263 := bstep (se 1 (by rfl) ⟨492947, by rfl⟩ : syracuseStep 657263 = 985895) B985895
theorem B1574795 : Blo 654306 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B1247167 : Blo 654306 1247167 := bstep (se 1 (by rfl) ⟨935375, by rfl⟩ : syracuseStep 1247167 = 1870751) B1870751
theorem B985067 : Blo 654306 985067 := bstep (se 1 (by rfl) ⟨738800, by rfl⟩ : syracuseStep 985067 = 1477601) B1477601
theorem B657479 : Blo 654306 657479 := bstep (se 1 (by rfl) ⟨493109, by rfl⟩ : syracuseStep 657479 = 986219) B986219
theorem B985319 : Blo 654306 985319 := bstep (se 1 (by rfl) ⟨738989, by rfl⟩ : syracuseStep 985319 = 1477979) B1477979
theorem B657639 : Blo 654306 657639 := bstep (se 1 (by rfl) ⟨493229, by rfl⟩ : syracuseStep 657639 = 986459) B986459
theorem B1771753 : Blo 654306 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B1870067 : Blo 654306 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B657659 : Blo 654306 657659 := bstep (se 1 (by rfl) ⟨493244, by rfl⟩ : syracuseStep 657659 = 986489) B986489
theorem B985343 : Blo 654306 985343 := bstep (se 1 (by rfl) ⟨739007, by rfl⟩ : syracuseStep 985343 = 1478015) B1478015
theorem B657663 : Blo 654306 657663 := bstep (se 1 (by rfl) ⟨493247, by rfl⟩ : syracuseStep 657663 = 986495) B986495
theorem B985481 : Blo 654306 985481 := bstep (se 2 (by rfl) ⟨369555, by rfl⟩ : syracuseStep 985481 = 739111) B739111
theorem B4557313 : Blo 654306 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B25266761 : Blo 654306 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B658079 : Blo 654306 658079 := bstep (se 1 (by rfl) ⟨493559, by rfl⟩ : syracuseStep 658079 = 987119) B987119
theorem B658087 : Blo 654306 658087 := bstep (se 1 (by rfl) ⟨493565, by rfl⟩ : syracuseStep 658087 = 987131) B987131
theorem B658127 : Blo 654306 658127 := bstep (se 1 (by rfl) ⟨493595, by rfl⟩ : syracuseStep 658127 = 987191) B987191
theorem B1051375 : Blo 654306 1051375 := bstep (se 1 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 1051375 = 1577063) B1577063
theorem B658159 : Blo 654306 658159 := bstep (se 1 (by rfl) ⟨493619, by rfl⟩ : syracuseStep 658159 = 987239) B987239
theorem B658207 : Blo 654306 658207 := bstep (se 1 (by rfl) ⟨493655, by rfl⟩ : syracuseStep 658207 = 987311) B987311
theorem B2362537 : Blo 654306 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B1477961 : Blo 654306 1477961 := bstep (se 2 (by rfl) ⟨554235, by rfl⟩ : syracuseStep 1477961 = 1108471) B1108471
theorem B986591 : Blo 654306 986591 := bstep (se 1 (by rfl) ⟨739943, by rfl⟩ : syracuseStep 986591 = 1479887) B1479887
theorem B986651 : Blo 654306 986651 := bstep (se 1 (by rfl) ⟨739988, by rfl⟩ : syracuseStep 986651 = 1479977) B1479977
theorem B3313223 : Blo 654306 3313223 := bstep (se 1 (by rfl) ⟨2484917, by rfl⟩ : syracuseStep 3313223 = 4969835) B4969835
theorem B1478303 : Blo 654306 1478303 := bstep (se 1 (by rfl) ⟨1108727, by rfl⟩ : syracuseStep 1478303 = 2217455) B2217455
theorem B986783 : Blo 654306 986783 := bstep (se 1 (by rfl) ⟨740087, by rfl⟩ : syracuseStep 986783 = 1480175) B1480175
theorem B3313547 : Blo 654306 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B1576871 : Blo 654306 1576871 := bstep (se 1 (by rfl) ⟨1182653, by rfl⟩ : syracuseStep 1576871 = 2365307) B2365307
theorem B987047 : Blo 654306 987047 := bstep (se 1 (by rfl) ⟨740285, by rfl⟩ : syracuseStep 987047 = 1480571) B1480571
theorem B987071 : Blo 654306 987071 := bstep (se 1 (by rfl) ⟨740303, by rfl⟩ : syracuseStep 987071 = 1480607) B1480607
theorem B790507 : Blo 654306 790507 := bstep (se 1 (by rfl) ⟨592880, by rfl⟩ : syracuseStep 790507 = 1185761) B1185761
theorem B2494547 : Blo 654306 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B987227 : Blo 654306 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B1478753 : Blo 654306 1478753 := bstep (se 2 (by rfl) ⟨554532, by rfl⟩ : syracuseStep 1478753 = 1109065) B1109065
theorem B987371 : Blo 654306 987371 := bstep (se 1 (by rfl) ⟨740528, by rfl⟩ : syracuseStep 987371 = 1481057) B1481057
theorem B2494745 : Blo 654306 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B1478951 : Blo 654306 1478951 := bstep (se 1 (by rfl) ⟨1109213, by rfl⟩ : syracuseStep 1478951 = 2218427) B2218427
theorem B987431 : Blo 654306 987431 := bstep (se 1 (by rfl) ⟨740573, by rfl⟩ : syracuseStep 987431 = 1481147) B1481147
theorem B1577659 : Blo 654306 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B3314681 : Blo 654306 3314681 := bstep (se 2 (by rfl) ⟨1243005, by rfl⟩ : syracuseStep 3314681 = 2486011) B2486011
theorem B1873007 : Blo 654306 1873007 := bstep (se 1 (by rfl) ⟨1404755, by rfl⟩ : syracuseStep 1873007 = 2809511) B2809511
theorem B1480103 : Blo 654306 1480103 := bstep (se 1 (by rfl) ⟨1110077, by rfl⟩ : syracuseStep 1480103 = 2220155) B2220155
theorem B2102699 : Blo 654306 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B10130903 : Blo 654306 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B1480211 : Blo 654306 1480211 := bstep (se 1 (by rfl) ⟨1110158, by rfl⟩ : syracuseStep 1480211 = 2220317) B2220317
theorem B1480283 : Blo 654306 1480283 := bstep (se 1 (by rfl) ⟨1110212, by rfl⟩ : syracuseStep 1480283 = 2220425) B2220425
theorem B4200119 : Blo 654306 4200119 := bstep (se 1 (by rfl) ⟨3150089, by rfl⟩ : syracuseStep 4200119 = 6300179) B6300179
theorem B9443465 : Blo 654306 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B4200659 : Blo 654306 4200659 := bstep (se 1 (by rfl) ⟨3150494, by rfl⟩ : syracuseStep 4200659 = 6300989) B6300989
theorem B2136377 : Blo 654306 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1481039 : Blo 654306 1481039 := bstep (se 1 (by rfl) ⟨1110779, by rfl⟩ : syracuseStep 1481039 = 2221559) B2221559
theorem B1481129 : Blo 654306 1481129 := bstep (se 2 (by rfl) ⟨555423, by rfl⟩ : syracuseStep 1481129 = 1110847) B1110847
theorem B9444559 : Blo 654306 9444559 := bstep (se 1 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 9444559 = 14166839) B14166839
theorem B4791649 : Blo 654306 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B3317435 : Blo 654306 3317435 := bstep (se 1 (by rfl) ⟨2488076, by rfl⟩ : syracuseStep 3317435 = 4976153) B4976153
theorem B3547007 : Blo 654306 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B1575133229 : Blo 654306 1575133229 := bstep (se 3 (by rfl) ⟨295337480, by rfl⟩ : syracuseStep 1575133229 = 590674961) B590674961
theorem B3318893 : Blo 654306 3318893 := bstep (se 3 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 3318893 = 1244585) B1244585
theorem B7971965 : Blo 654306 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B3745055 : Blo 654306 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B6727205 : Blo 654306 6727205 := bstep (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) B1261351
theorem B7480997 : Blo 654306 7480997 := bstep (se 4 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 7480997 = 1402687) B1402687
theorem B3778973 : Blo 654306 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B829855 : Blo 654306 829855 := bstep (se 1 (by rfl) ⟨622391, by rfl⟩ : syracuseStep 829855 = 1244783) B1244783
theorem B830407 : Blo 654306 830407 := bstep (se 1 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 830407 = 1245611) B1245611
theorem B3779713 : Blo 654306 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B5975795 : Blo 654306 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B28422251 : Blo 654306 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B4731301 : Blo 654306 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B8434165 : Blo 654306 8434165 := bstep (se 5 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 8434165 = 790703) B790703
theorem B832027 : Blo 654306 832027 := bstep (se 1 (by rfl) ⟨624020, by rfl⟩ : syracuseStep 832027 = 1248041) B1248041
theorem B2208329 : Blo 654306 2208329 := bstep (se 2 (by rfl) ⟨828123, by rfl⟩ : syracuseStep 2208329 = 1656247) B1656247
theorem B3322619 : Blo 654306 3322619 := bstep (se 1 (by rfl) ⟨2491964, by rfl⟩ : syracuseStep 3322619 = 4983929) B4983929
theorem B832295 : Blo 654306 832295 := bstep (se 1 (by rfl) ⟨624221, by rfl⟩ : syracuseStep 832295 = 1248443) B1248443
theorem B2602451 : Blo 654306 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B832999 : Blo 654306 832999 := bstep (se 1 (by rfl) ⟨624749, by rfl⟩ : syracuseStep 832999 = 1249499) B1249499
theorem B11188691 : Blo 654306 11188691 := bstep (se 1 (by rfl) ⟨8391518, by rfl⟩ : syracuseStep 11188691 = 16783037) B16783037
theorem B2210273 : Blo 654306 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B5618267 : Blo 654306 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B3325049 : Blo 654306 3325049 := bstep (se 2 (by rfl) ⟨1246893, by rfl⟩ : syracuseStep 3325049 = 2493787) B2493787
theorem B3783827 : Blo 654306 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B68074667 : Blo 654306 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B4209907 : Blo 654306 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B3325373 : Blo 654306 3325373 := bstep (se 3 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 3325373 = 1247015) B1247015
theorem B736735 : Blo 654306 736735 := bstep (se 1 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 736735 = 1105103) B1105103
theorem B1687007 : Blo 654306 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B2211785 : Blo 654306 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B7979795 : Blo 654306 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B3556655 : Blo 654306 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B935239 : Blo 654306 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B1656713 : Blo 654306 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B4212881 : Blo 654306 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B7489745 : Blo 654306 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B3328451 : Blo 654306 3328451 := bstep (se 1 (by rfl) ⟨2496338, by rfl⟩ : syracuseStep 3328451 = 4992677) B4992677
theorem B80693921 : Blo 654306 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B4868873 : Blo 654306 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B2214863 : Blo 654306 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B21285935 : Blo 654306 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B6311135 : Blo 654306 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B11980489 : Blo 654306 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B217829225 : Blo 654306 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B1659001 : Blo 654306 1659001 := bstep (se 2 (by rfl) ⟨622125, by rfl⟩ : syracuseStep 1659001 = 1244251) B1244251
theorem B4739897 : Blo 654306 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B2806913 : Blo 654306 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B2217887 : Blo 654306 2217887 := bstep (se 1 (by rfl) ⟨1663415, by rfl⟩ : syracuseStep 2217887 = 3326831) B3326831
theorem B3987539 : Blo 654306 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B4479113 : Blo 654306 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B1838733965 : Blo 654306 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B1104617 : Blo 654306 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B2808553 : Blo 654306 2808553 := bstep (se 2 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 2808553 = 2106415) B2106415
theorem B1661735 : Blo 654306 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B1662383 : Blo 654306 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B7987187 : Blo 654306 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B3728015 : Blo 654306 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B10674953 : Blo 654306 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B1663841 : Blo 654306 1663841 := bstep (se 2 (by rfl) ⟨623940, by rfl⟩ : syracuseStep 1663841 = 1247881) B1247881
theorem B3990653 : Blo 654306 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B1107175 : Blo 654306 1107175 := bstep (se 1 (by rfl) ⟨830381, by rfl⟩ : syracuseStep 1107175 = 1660763) B1660763
theorem B3729199 : Blo 654306 3729199 := bstep (se 1 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 3729199 = 5593799) B5593799
theorem B2484857 : Blo 654306 2484857 := bstep (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) B1863643
theorem B1403705 : Blo 654306 1403705 := bstep (se 2 (by rfl) ⟨526389, by rfl⟩ : syracuseStep 1403705 = 1052779) B1052779
theorem B6745513 : Blo 654306 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B8416943 : Blo 654306 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B1863415 : Blo 654306 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B1110071 : Blo 654306 1110071 := bstep (se 1 (by rfl) ⟨832553, by rfl⟩ : syracuseStep 1110071 = 1665107) B1665107
theorem B40399667 : Blo 654306 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B9696449 : Blo 654306 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B1996105 : Blo 654306 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B13465241 : Blo 654306 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B12646327 : Blo 654306 12646327 := bstep (se 1 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 12646327 = 18969491) B18969491
theorem B2488441 : Blo 654306 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B6289721 : Blo 654306 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B981497 : Blo 654306 981497 := bstep (se 2 (by rfl) ⟨368061, by rfl⟩ : syracuseStep 981497 = 736123) B736123
theorem B1866503 : Blo 654306 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B3537755 : Blo 654306 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B1866685 : Blo 654306 1866685 := bstep (se 3 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 1866685 = 700007) B700007
theorem B981983 : Blo 654306 981983 := bstep (se 1 (by rfl) ⟨736487, by rfl⟩ : syracuseStep 981983 = 1472975) B1472975
theorem B654363 : Blo 654306 654363 := bstep (se 1 (by rfl) ⟨490772, by rfl⟩ : syracuseStep 654363 = 981545) B981545
theorem B982043 : Blo 654306 982043 := bstep (se 1 (by rfl) ⟨736532, by rfl⟩ : syracuseStep 982043 = 1473065) B1473065
theorem B4717693 : Blo 654306 4717693 := bstep (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) B1769135
theorem B654491 : Blo 654306 654491 := bstep (se 1 (by rfl) ⟨490868, by rfl⟩ : syracuseStep 654491 = 981737) B981737
theorem B654747 : Blo 654306 654747 := bstep (se 1 (by rfl) ⟨491060, by rfl⟩ : syracuseStep 654747 = 982121) B982121
theorem B982427 : Blo 654306 982427 := bstep (se 1 (by rfl) ⟨736820, by rfl⟩ : syracuseStep 982427 = 1473641) B1473641
theorem B1473947 : Blo 654306 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B982505 : Blo 654306 982505 := bstep (se 2 (by rfl) ⟨368439, by rfl⟩ : syracuseStep 982505 = 736879) B736879
theorem B654831 : Blo 654306 654831 := bstep (se 1 (by rfl) ⟨491123, by rfl⟩ : syracuseStep 654831 = 982247) B982247
theorem B982511 : Blo 654306 982511 := bstep (se 1 (by rfl) ⟨736883, by rfl⟩ : syracuseStep 982511 = 1473767) B1473767
theorem B61636085 : Blo 654306 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B982649 : Blo 654306 982649 := bstep (se 2 (by rfl) ⟨368493, by rfl⟩ : syracuseStep 982649 = 736987) B736987
theorem B3735305 : Blo 654306 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B3997487 : Blo 654306 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B655167 : Blo 654306 655167 := bstep (se 1 (by rfl) ⟨491375, by rfl⟩ : syracuseStep 655167 = 982751) B982751
theorem B982847 : Blo 654306 982847 := bstep (se 1 (by rfl) ⟨737135, by rfl⟩ : syracuseStep 982847 = 1474271) B1474271
theorem B655195 : Blo 654306 655195 := bstep (se 1 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 655195 = 982793) B982793
theorem B982895 : Blo 654306 982895 := bstep (se 1 (by rfl) ⟨737171, by rfl⟩ : syracuseStep 982895 = 1474343) B1474343
theorem B983399 : Blo 654306 983399 := bstep (se 1 (by rfl) ⟨737549, by rfl⟩ : syracuseStep 983399 = 1475099) B1475099
theorem B655719 : Blo 654306 655719 := bstep (se 1 (by rfl) ⟨491789, by rfl⟩ : syracuseStep 655719 = 983579) B983579
theorem B983519 : Blo 654306 983519 := bstep (se 1 (by rfl) ⟨737639, by rfl⟩ : syracuseStep 983519 = 1475279) B1475279
theorem B655839 : Blo 654306 655839 := bstep (se 1 (by rfl) ⟨491879, by rfl⟩ : syracuseStep 655839 = 983759) B983759
theorem B655919 : Blo 654306 655919 := bstep (se 1 (by rfl) ⟨491939, by rfl⟩ : syracuseStep 655919 = 983879) B983879
theorem B655963 : Blo 654306 655963 := bstep (se 1 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 655963 = 983945) B983945
theorem B983771 : Blo 654306 983771 := bstep (se 1 (by rfl) ⟨737828, by rfl⟩ : syracuseStep 983771 = 1475657) B1475657
theorem B656127 : Blo 654306 656127 := bstep (se 1 (by rfl) ⟨492095, by rfl⟩ : syracuseStep 656127 = 984191) B984191
theorem B656219 : Blo 654306 656219 := bstep (se 1 (by rfl) ⟨492164, by rfl⟩ : syracuseStep 656219 = 984329) B984329
theorem B1246279 : Blo 654306 1246279 := bstep (se 1 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 1246279 = 1869419) B1869419
theorem B1049755 : Blo 654306 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B656539 : Blo 654306 656539 := bstep (se 1 (by rfl) ⟨492404, by rfl⟩ : syracuseStep 656539 = 984809) B984809
theorem B656543 : Blo 654306 656543 := bstep (se 1 (by rfl) ⟨492407, by rfl⟩ : syracuseStep 656543 = 984815) B984815
theorem B1049863 : Blo 654306 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B656711 : Blo 654306 656711 := bstep (se 1 (by rfl) ⟨492533, by rfl⟩ : syracuseStep 656711 = 985067) B985067
theorem B656879 : Blo 654306 656879 := bstep (se 1 (by rfl) ⟨492659, by rfl⟩ : syracuseStep 656879 = 985319) B985319
theorem B656895 : Blo 654306 656895 := bstep (se 1 (by rfl) ⟨492671, by rfl⟩ : syracuseStep 656895 = 985343) B985343
theorem B656987 : Blo 654306 656987 := bstep (se 1 (by rfl) ⟨492740, by rfl⟩ : syracuseStep 656987 = 985481) B985481
theorem B1476233 : Blo 654306 1476233 := bstep (se 2 (by rfl) ⟨553587, by rfl⟩ : syracuseStep 1476233 = 1107175) B1107175
theorem B16844507 : Blo 654306 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B1246985 : Blo 654306 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B3245915 : Blo 654306 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B1476575 : Blo 654306 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B14190623 : Blo 654306 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B25233605 : Blo 654306 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B985307 : Blo 654306 985307 := bstep (se 1 (by rfl) ⟨738980, by rfl⟩ : syracuseStep 985307 = 1477961) B1477961
theorem B657727 : Blo 654306 657727 := bstep (se 1 (by rfl) ⟨493295, by rfl⟩ : syracuseStep 657727 = 986591) B986591
theorem B657767 : Blo 654306 657767 := bstep (se 1 (by rfl) ⟨493325, by rfl⟩ : syracuseStep 657767 = 986651) B986651
theorem B985535 : Blo 654306 985535 := bstep (se 1 (by rfl) ⟨739151, by rfl⟩ : syracuseStep 985535 = 1478303) B1478303
theorem B657855 : Blo 654306 657855 := bstep (se 1 (by rfl) ⟨493391, by rfl⟩ : syracuseStep 657855 = 986783) B986783
theorem B1051247 : Blo 654306 1051247 := bstep (se 1 (by rfl) ⟨788435, by rfl⟩ : syracuseStep 1051247 = 1576871) B1576871
theorem B658031 : Blo 654306 658031 := bstep (se 1 (by rfl) ⟨493523, by rfl⟩ : syracuseStep 658031 = 987047) B987047
theorem B658047 : Blo 654306 658047 := bstep (se 1 (by rfl) ⟨493535, by rfl⟩ : syracuseStep 658047 = 987071) B987071
theorem B658151 : Blo 654306 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B985835 : Blo 654306 985835 := bstep (se 1 (by rfl) ⟨739376, by rfl⟩ : syracuseStep 985835 = 1478753) B1478753
theorem B658247 : Blo 654306 658247 := bstep (se 1 (by rfl) ⟨493685, by rfl⟩ : syracuseStep 658247 = 987371) B987371
theorem B985967 : Blo 654306 985967 := bstep (se 1 (by rfl) ⟨739475, by rfl⟩ : syracuseStep 985967 = 1478951) B1478951
theorem B658287 : Blo 654306 658287 := bstep (se 1 (by rfl) ⟨493715, by rfl⟩ : syracuseStep 658287 = 987431) B987431
theorem B2362337 : Blo 654306 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B25857197 : Blo 654306 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B1248671 : Blo 654306 1248671 := bstep (se 1 (by rfl) ⟨936503, by rfl⟩ : syracuseStep 1248671 = 1873007) B1873007
theorem B1871275 : Blo 654306 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B986735 : Blo 654306 986735 := bstep (se 1 (by rfl) ⟨740051, by rfl⟩ : syracuseStep 986735 = 1480103) B1480103
theorem B6753935 : Blo 654306 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B986807 : Blo 654306 986807 := bstep (se 1 (by rfl) ⟨740105, by rfl⟩ : syracuseStep 986807 = 1480211) B1480211
theorem B986855 : Blo 654306 986855 := bstep (se 1 (by rfl) ⟨740141, by rfl⟩ : syracuseStep 986855 = 1480283) B1480283
theorem B1478591 : Blo 654306 1478591 := bstep (se 1 (by rfl) ⟨1108943, by rfl⟩ : syracuseStep 1478591 = 2217887) B2217887
theorem B2658359 : Blo 654306 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2986075 : Blo 654306 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B6295643 : Blo 654306 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B987359 : Blo 654306 987359 := bstep (se 1 (by rfl) ⟨740519, by rfl⟩ : syracuseStep 987359 = 1481039) B1481039
theorem B987419 : Blo 654306 987419 := bstep (se 1 (by rfl) ⟨740564, by rfl⟩ : syracuseStep 987419 = 1481129) B1481129
theorem B1225822643 : Blo 654306 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B2364671 : Blo 654306 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B1054009 : Blo 654306 1054009 := bstep (se 2 (by rfl) ⟨395253, by rfl⟩ : syracuseStep 1054009 = 790507) B790507
theorem B7116635 : Blo 654306 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B4986845 : Blo 654306 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B11245553 : Blo 654306 11245553 := bstep (se 2 (by rfl) ⟨4217082, by rfl⟩ : syracuseStep 11245553 = 8434165) B8434165
theorem B20158469 : Blo 654306 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B5314643 : Blo 654306 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B2660435 : Blo 654306 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B2496703 : Blo 654306 2496703 := bstep (se 1 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 2496703 = 3745055) B3745055
theorem B2103545 : Blo 654306 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B4987331 : Blo 654306 4987331 := bstep (se 1 (by rfl) ⟨3740498, by rfl⟩ : syracuseStep 4987331 = 7480997) B7480997
theorem B2661473 : Blo 654306 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B5611295 : Blo 654306 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B18948167 : Blo 654306 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B3317921 : Blo 654306 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B3744737 : Blo 654306 3744737 := bstep (se 2 (by rfl) ⟨1404276, by rfl⟩ : syracuseStep 3744737 = 2808553) B2808553
theorem B12592745 : Blo 654306 12592745 := bstep (se 2 (by rfl) ⟨4722279, by rfl⟩ : syracuseStep 12592745 = 9444559) B9444559
theorem B5613209 : Blo 654306 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B3745511 : Blo 654306 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B15935453 : Blo 654306 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B1124671 : Blo 654306 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B2664991 : Blo 654306 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B5319863 : Blo 654306 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B2797037 : Blo 654306 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B2371103 : Blo 654306 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B4993163 : Blo 654306 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B4207423 : Blo 654306 4207423 := bstep (se 1 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 4207423 = 6311135) B6311135
theorem B2208815 : Blo 654306 2208815 := bstep (se 1 (by rfl) ⟨1656611, by rfl⟩ : syracuseStep 2208815 = 3313223) B3313223
theorem B2209031 : Blo 654306 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B3159931 : Blo 654306 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B2209787 : Blo 654306 2209787 := bstep (se 1 (by rfl) ⟨1657340, by rfl⟩ : syracuseStep 2209787 = 3314681) B3314681
theorem B6076417 : Blo 654306 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B2800079 : Blo 654306 2800079 := bstep (se 1 (by rfl) ⟨2100059, by rfl⟩ : syracuseStep 2800079 = 4200119) B4200119
theorem B2800439 : Blo 654306 2800439 := bstep (se 1 (by rfl) ⟨2100329, by rfl⟩ : syracuseStep 2800439 = 4200659) B4200659
theorem B1424251 : Blo 654306 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B736411 : Blo 654306 736411 := bstep (se 1 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 736411 = 1104617) B1104617
theorem B8994017 : Blo 654306 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B15973985 : Blo 654306 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B2211623 : Blo 654306 2211623 := bstep (se 1 (by rfl) ⟨1658717, by rfl⟩ : syracuseStep 2211623 = 3317435) B3317435
theorem B5324791 : Blo 654306 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B2212001 : Blo 654306 2212001 := bstep (se 2 (by rfl) ⟨829500, by rfl⟩ : syracuseStep 2212001 = 1659001) B1659001
theorem B2212595 : Blo 654306 2212595 := bstep (se 1 (by rfl) ⟨1659446, by rfl⟩ : syracuseStep 2212595 = 3318893) B3318893
theorem B12600197 : Blo 654306 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1656571 : Blo 654306 1656571 := bstep (se 1 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 1656571 = 2484857) B2484857
theorem B935803 : Blo 654306 935803 := bstep (se 1 (by rfl) ⟨701852, by rfl⟩ : syracuseStep 935803 = 1403705) B1403705
theorem B16861769 : Blo 654306 16861769 := bstep (se 2 (by rfl) ⟨6323163, by rfl⟩ : syracuseStep 16861769 = 12646327) B12646327
theorem B740047 : Blo 654306 740047 := bstep (se 1 (by rfl) ⟨555035, by rfl⟩ : syracuseStep 740047 = 1110071) B1110071
theorem B2215079 : Blo 654306 2215079 := bstep (se 1 (by rfl) ⟨1661309, by rfl⟩ : syracuseStep 2215079 = 3322619) B3322619
theorem B7459127 : Blo 654306 7459127 := bstep (se 1 (by rfl) ⟨5594345, by rfl⟩ : syracuseStep 7459127 = 11188691) B11188691
theorem B2216699 : Blo 654306 2216699 := bstep (se 1 (by rfl) ⟨1662524, by rfl⟩ : syracuseStep 2216699 = 3325049) B3325049
theorem B2216915 : Blo 654306 2216915 := bstep (se 1 (by rfl) ⟨1662686, by rfl⟩ : syracuseStep 2216915 = 3325373) B3325373
theorem B4200355277 : Blo 654306 4200355277 := bstep (se 3 (by rfl) ⟨787566614, by rfl⟩ : syracuseStep 4200355277 = 1575133229) B1575133229
theorem B1660571 : Blo 654306 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B1398655 : Blo 654306 1398655 := bstep (se 1 (by rfl) ⟨1048991, by rfl⟩ : syracuseStep 1398655 = 2097983) B2097983
theorem B1104475 : Blo 654306 1104475 := bstep (se 1 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 1104475 = 1656713) B1656713
theorem B2808587 : Blo 654306 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B2218967 : Blo 654306 2218967 := bstep (se 1 (by rfl) ⟨1664225, by rfl⟩ : syracuseStep 2218967 = 3328451) B3328451
theorem B53795947 : Blo 654306 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B2219453 : Blo 654306 2219453 := bstep (se 3 (by rfl) ⟨416147, by rfl⟩ : syracuseStep 2219453 = 832295) B832295
theorem B4972265 : Blo 654306 4972265 := bstep (se 2 (by rfl) ⟨1864599, by rfl⟩ : syracuseStep 4972265 = 3729199) B3729199
theorem B145219483 : Blo 654306 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B1662889 : Blo 654306 1662889 := bstep (se 2 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 1662889 = 1247167) B1247167
theorem B1663031 : Blo 654306 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B1663163 : Blo 654306 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B1106473 : Blo 654306 1106473 := bstep (se 2 (by rfl) ⟨414927, by rfl⟩ : syracuseStep 1106473 = 829855) B829855
theorem B1401799 : Blo 654306 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1401833 : Blo 654306 1401833 := bstep (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) B1051375
theorem B1107209 : Blo 654306 1107209 := bstep (se 2 (by rfl) ⟨415203, by rfl⟩ : syracuseStep 1107209 = 830407) B830407
theorem B51046037 : Blo 654306 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B1107823 : Blo 654306 1107823 := bstep (se 1 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 1107823 = 1661735) B1661735
theorem B1108255 : Blo 654306 1108255 := bstep (se 1 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 1108255 = 1662383) B1662383
theorem B2484553 : Blo 654306 2484553 := bstep (se 2 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 2484553 = 1863415) B1863415
theorem B2485343 : Blo 654306 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B1109227 : Blo 654306 1109227 := bstep (se 1 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 1109227 = 1663841) B1663841
theorem B1109369 : Blo 654306 1109369 := bstep (se 2 (by rfl) ⟨416013, by rfl⟩ : syracuseStep 1109369 = 832027) B832027
theorem B4484803 : Blo 654306 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B2519315 : Blo 654306 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B1110665 : Blo 654306 1110665 := bstep (se 2 (by rfl) ⟨416499, by rfl⟩ : syracuseStep 1110665 = 832999) B832999
theorem B1472219 : Blo 654306 1472219 := bstep (se 1 (by rfl) ⟨1104164, by rfl⟩ : syracuseStep 1472219 = 2208329) B2208329
theorem B26933111 : Blo 654306 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B1734967 : Blo 654306 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B8976827 : Blo 654306 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B2488913 : Blo 654306 2488913 := bstep (se 2 (by rfl) ⟨933342, by rfl⟩ : syracuseStep 2488913 = 1866685) B1866685
theorem B6290257 : Blo 654306 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B4193147 : Blo 654306 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B1473515 : Blo 654306 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B654331 : Blo 654306 654331 := bstep (se 1 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 654331 = 981497) B981497
theorem B6388865 : Blo 654306 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B1244335 : Blo 654306 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B2358503 : Blo 654306 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B982313 : Blo 654306 982313 := bstep (se 2 (by rfl) ⟨368367, by rfl⟩ : syracuseStep 982313 = 736735) B736735
theorem B654655 : Blo 654306 654655 := bstep (se 1 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 654655 = 981983) B981983
theorem B654695 : Blo 654306 654695 := bstep (se 1 (by rfl) ⟨491021, by rfl⟩ : syracuseStep 654695 = 982043) B982043
theorem B2522551 : Blo 654306 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B45383111 : Blo 654306 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B654951 : Blo 654306 654951 := bstep (se 1 (by rfl) ⟨491213, by rfl⟩ : syracuseStep 654951 = 982427) B982427
theorem B982631 : Blo 654306 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B655003 : Blo 654306 655003 := bstep (se 1 (by rfl) ⟨491252, by rfl⟩ : syracuseStep 655003 = 982505) B982505
theorem B655007 : Blo 654306 655007 := bstep (se 1 (by rfl) ⟨491255, by rfl⟩ : syracuseStep 655007 = 982511) B982511
theorem B41090723 : Blo 654306 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B655099 : Blo 654306 655099 := bstep (se 1 (by rfl) ⟨491324, by rfl⟩ : syracuseStep 655099 = 982649) B982649
theorem B2490203 : Blo 654306 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B655231 : Blo 654306 655231 := bstep (se 1 (by rfl) ⟨491423, by rfl⟩ : syracuseStep 655231 = 982847) B982847
theorem B655263 : Blo 654306 655263 := bstep (se 1 (by rfl) ⟨491447, by rfl⟩ : syracuseStep 655263 = 982895) B982895
theorem B1474523 : Blo 654306 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B1474667 : Blo 654306 1474667 := bstep (se 1 (by rfl) ⟨1106000, by rfl⟩ : syracuseStep 1474667 = 2212001) B2212001
theorem B655599 : Blo 654306 655599 := bstep (se 1 (by rfl) ⟨491699, by rfl⟩ : syracuseStep 655599 = 983399) B983399
theorem B655679 : Blo 654306 655679 := bstep (se 1 (by rfl) ⟨491759, by rfl⟩ : syracuseStep 655679 = 983519) B983519
theorem B15925733 : Blo 654306 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B655847 : Blo 654306 655847 := bstep (se 1 (by rfl) ⟨491885, by rfl⟩ : syracuseStep 655847 = 983771) B983771
theorem B1475063 : Blo 654306 1475063 := bstep (se 1 (by rfl) ⟨1106297, by rfl⟩ : syracuseStep 1475063 = 2212595) B2212595
theorem B1475297 : Blo 654306 1475297 := bstep (se 2 (by rfl) ⟨553236, by rfl⟩ : syracuseStep 1475297 = 1106473) B1106473
theorem B984155 : Blo 654306 984155 := bstep (se 1 (by rfl) ⟨738116, by rfl⟩ : syracuseStep 984155 = 1476233) B1476233
theorem B2163943 : Blo 654306 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B1869065 : Blo 654306 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B984383 : Blo 654306 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B656871 : Blo 654306 656871 := bstep (se 1 (by rfl) ⟨492653, by rfl⟩ : syracuseStep 656871 = 985307) B985307
theorem B657023 : Blo 654306 657023 := bstep (se 1 (by rfl) ⟨492767, by rfl⟩ : syracuseStep 657023 = 985535) B985535
theorem B11241179 : Blo 654306 11241179 := bstep (se 1 (by rfl) ⟨8430884, by rfl⟩ : syracuseStep 11241179 = 16861769) B16861769
theorem B657223 : Blo 654306 657223 := bstep (se 1 (by rfl) ⟨492917, by rfl⟩ : syracuseStep 657223 = 985835) B985835
theorem B657311 : Blo 654306 657311 := bstep (se 1 (by rfl) ⟨492983, by rfl⟩ : syracuseStep 657311 = 985967) B985967
theorem B1574891 : Blo 654306 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1476719 : Blo 654306 1476719 := bstep (se 1 (by rfl) ⟨1107539, by rfl⟩ : syracuseStep 1476719 = 2215079) B2215079
theorem B17238131 : Blo 654306 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B657823 : Blo 654306 657823 := bstep (se 1 (by rfl) ⟨493367, by rfl⟩ : syracuseStep 657823 = 986735) B986735
theorem B657871 : Blo 654306 657871 := bstep (se 1 (by rfl) ⟨493403, by rfl⟩ : syracuseStep 657871 = 986807) B986807
theorem B1477097 : Blo 654306 1477097 := bstep (se 2 (by rfl) ⟨553911, by rfl⟩ : syracuseStep 1477097 = 1107823) B1107823
theorem B657903 : Blo 654306 657903 := bstep (se 1 (by rfl) ⟨493427, by rfl⟩ : syracuseStep 657903 = 986855) B986855
theorem B1247737 : Blo 654306 1247737 := bstep (se 2 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 1247737 = 935803) B935803
theorem B3738221 : Blo 654306 3738221 := bstep (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) B1401833
theorem B985727 : Blo 654306 985727 := bstep (se 1 (by rfl) ⟨739295, by rfl⟩ : syracuseStep 985727 = 1478591) B1478591
theorem B4197095 : Blo 654306 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B658239 : Blo 654306 658239 := bstep (se 1 (by rfl) ⟨493679, by rfl⟩ : syracuseStep 658239 = 987359) B987359
theorem B658279 : Blo 654306 658279 := bstep (se 1 (by rfl) ⟨493709, by rfl⟩ : syracuseStep 658279 = 987419) B987419
theorem B1477673 : Blo 654306 1477673 := bstep (se 2 (by rfl) ⟨554127, by rfl⟩ : syracuseStep 1477673 = 1108255) B1108255
theorem B3312737 : Blo 654306 3312737 := bstep (se 2 (by rfl) ⟨1242276, by rfl⟩ : syracuseStep 3312737 = 2484553) B2484553
theorem B1477799 : Blo 654306 1477799 := bstep (se 1 (by rfl) ⟨1108349, by rfl⟩ : syracuseStep 1477799 = 2216699) B2216699
theorem B1477943 : Blo 654306 1477943 := bstep (se 1 (by rfl) ⟨1108457, by rfl⟩ : syracuseStep 1477943 = 2216915) B2216915
theorem B986729 : Blo 654306 986729 := bstep (se 2 (by rfl) ⟨370023, by rfl⟩ : syracuseStep 986729 = 740047) B740047
theorem B13438979 : Blo 654306 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B3543095 : Blo 654306 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B1773623 : Blo 654306 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B1478969 : Blo 654306 1478969 := bstep (se 2 (by rfl) ⟨554613, by rfl⟩ : syracuseStep 1478969 = 1109227) B1109227
theorem B1872391 : Blo 654306 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B2495033 : Blo 654306 2495033 := bstep (se 2 (by rfl) ⟨935637, by rfl⟩ : syracuseStep 2495033 = 1871275) B1871275
theorem B1479311 : Blo 654306 1479311 := bstep (se 1 (by rfl) ⟨1109483, by rfl⟩ : syracuseStep 1479311 = 2218967) B2218967
theorem B1774315 : Blo 654306 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B1479635 : Blo 654306 1479635 := bstep (se 1 (by rfl) ⟨1109726, by rfl⟩ : syracuseStep 1479635 = 2219453) B2219453
theorem B3314843 : Blo 654306 3314843 := bstep (se 1 (by rfl) ⟨2486132, by rfl⟩ : syracuseStep 3314843 = 4972265) B4972265
theorem B3740863 : Blo 654306 3740863 := bstep (se 1 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 3740863 = 5611295) B5611295
theorem B2496491 : Blo 654306 2496491 := bstep (se 1 (by rfl) ⟨1872368, by rfl⟩ : syracuseStep 2496491 = 3744737) B3744737
theorem B8395163 : Blo 654306 8395163 := bstep (se 1 (by rfl) ⟨6296372, by rfl⟩ : syracuseStep 8395163 = 12592745) B12592745
theorem B5609897 : Blo 654306 5609897 := bstep (se 2 (by rfl) ⟨2103711, by rfl⟩ : syracuseStep 5609897 = 4207423) B4207423
theorem B3742139 : Blo 654306 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B2497007 : Blo 654306 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B10623635 : Blo 654306 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B3546575 : Blo 654306 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B1580735 : Blo 654306 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B8101889 : Blo 654306 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B1679543 : Blo 654306 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B2795431 : Blo 654306 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B30255407 : Blo 654306 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B7088957 : Blo 654306 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B8400131 : Blo 654306 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B831323 : Blo 654306 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B16822403 : Blo 654306 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B700831 : Blo 654306 700831 := bstep (se 1 (by rfl) ⟨525623, by rfl⟩ : syracuseStep 700831 = 1051247) B1051247
theorem B832447 : Blo 654306 832447 := bstep (se 1 (by rfl) ⟨624335, by rfl⟩ : syracuseStep 832447 = 1248671) B1248671
theorem B2208761 : Blo 654306 2208761 := bstep (se 2 (by rfl) ⟨828285, by rfl⟩ : syracuseStep 2208761 = 1656571) B1656571
theorem B4502623 : Blo 654306 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B817215095 : Blo 654306 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B6305789 : Blo 654306 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B3553321 : Blo 654306 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B2800236851 : Blo 654306 2800236851 := bstep (se 1 (by rfl) ⟨2100177638, by rfl⟩ : syracuseStep 2800236851 = 4200355277) B4200355277
theorem B3324563 : Blo 654306 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B3324887 : Blo 654306 3324887 := bstep (se 1 (by rfl) ⟨2493665, by rfl⟩ : syracuseStep 3324887 = 4987331) B4987331
theorem B5979737 : Blo 654306 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B12632111 : Blo 654306 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B2211947 : Blo 654306 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B738139 : Blo 654306 738139 := bstep (se 1 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 738139 = 1107209) B1107209
theorem B34030691 : Blo 654306 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B1656895 : Blo 654306 1656895 := bstep (se 1 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 1656895 = 2485343) B2485343
theorem B739579 : Blo 654306 739579 := bstep (se 1 (by rfl) ⟨554684, by rfl⟩ : syracuseStep 739579 = 1109369) B1109369
theorem B4213241 : Blo 654306 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B3328775 : Blo 654306 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B3328937 : Blo 654306 3328937 := bstep (se 2 (by rfl) ⟨1248351, by rfl⟩ : syracuseStep 3328937 = 2496703) B2496703
theorem B2313289 : Blo 654306 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B740443 : Blo 654306 740443 := bstep (se 1 (by rfl) ⟨555332, by rfl⟩ : syracuseStep 740443 = 1110665) B1110665
theorem B1659113 : Blo 654306 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B5984551 : Blo 654306 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B1659275 : Blo 654306 1659275 := bstep (se 1 (by rfl) ⟨1244456, by rfl⟩ : syracuseStep 1659275 = 2488913) B2488913
theorem B3363401 : Blo 654306 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B2217185 : Blo 654306 2217185 := bstep (se 2 (by rfl) ⟨831444, by rfl⟩ : syracuseStep 2217185 = 1662889) B1662889
theorem B1660135 : Blo 654306 1660135 := bstep (se 1 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 1660135 = 2490203) B2490203
theorem B7099721 : Blo 654306 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B11229671 : Blo 654306 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B9460415 : Blo 654306 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B1661705 : Blo 654306 1661705 := bstep (se 2 (by rfl) ⟨623139, by rfl⟩ : syracuseStep 1661705 = 1246279) B1246279
theorem B1399673 : Blo 654306 1399673 := bstep (se 2 (by rfl) ⟨524877, by rfl⟩ : syracuseStep 1399673 = 1049755) B1049755
theorem B1399817 : Blo 654306 1399817 := bstep (se 2 (by rfl) ⟨524931, by rfl⟩ : syracuseStep 1399817 = 1049863) B1049863
theorem B4972751 : Blo 654306 4972751 := bstep (se 1 (by rfl) ⟨3729563, by rfl⟩ : syracuseStep 4972751 = 7459127) B7459127
theorem B1499561 : Blo 654306 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B1107047 : Blo 654306 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B4744423 : Blo 654306 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B7497035 : Blo 654306 7497035 := bstep (se 1 (by rfl) ⟨5622776, by rfl⟩ : syracuseStep 7497035 = 11245553) B11245553
theorem B1402363 : Blo 654306 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1108687 : Blo 654306 1108687 := bstep (se 1 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 1108687 = 1663031) B1663031
theorem B1108775 : Blo 654306 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B1405345 : Blo 654306 1405345 := bstep (se 2 (by rfl) ⟨527004, by rfl⟩ : syracuseStep 1405345 = 1054009) B1054009
theorem B1864691 : Blo 654306 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B1864873 : Blo 654306 1864873 := bstep (se 2 (by rfl) ⟨699327, by rfl⟩ : syracuseStep 1864873 = 1398655) B1398655
theorem B23984045 : Blo 654306 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B1472543 : Blo 654306 1472543 := bstep (se 1 (by rfl) ⟨1104407, by rfl⟩ : syracuseStep 1472543 = 2208815) B2208815
theorem B1472633 : Blo 654306 1472633 := bstep (se 2 (by rfl) ⟨552237, by rfl⟩ : syracuseStep 1472633 = 1104475) B1104475
theorem B1472687 : Blo 654306 1472687 := bstep (se 1 (by rfl) ⟨1104515, by rfl⟩ : syracuseStep 1472687 = 2209031) B2209031
theorem B8387009 : Blo 654306 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B981479 : Blo 654306 981479 := bstep (se 1 (by rfl) ⟨736109, by rfl⟩ : syracuseStep 981479 = 1472219) B1472219
theorem B1899001 : Blo 654306 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B17955407 : Blo 654306 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B1473191 : Blo 654306 1473191 := bstep (se 1 (by rfl) ⟨1104893, by rfl⟩ : syracuseStep 1473191 = 2209787) B2209787
theorem B71727929 : Blo 654306 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B981881 : Blo 654306 981881 := bstep (se 2 (by rfl) ⟨368205, by rfl⟩ : syracuseStep 981881 = 736411) B736411
theorem B1866719 : Blo 654306 1866719 := bstep (se 1 (by rfl) ⟨1400039, by rfl⟩ : syracuseStep 1866719 = 2800079) B2800079
theorem B1866959 : Blo 654306 1866959 := bstep (se 1 (by rfl) ⟨1400219, by rfl⟩ : syracuseStep 1866959 = 2800439) B2800439
theorem B982343 : Blo 654306 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B4259243 : Blo 654306 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B1572335 : Blo 654306 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B654875 : Blo 654306 654875 := bstep (se 1 (by rfl) ⟨491156, by rfl⟩ : syracuseStep 654875 = 982313) B982313
theorem B10649323 : Blo 654306 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B655087 : Blo 654306 655087 := bstep (se 1 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 655087 = 982631) B982631
theorem B27393815 : Blo 654306 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B1474415 : Blo 654306 1474415 := bstep (se 1 (by rfl) ⟨1105811, by rfl⟩ : syracuseStep 1474415 = 2211623) B2211623
theorem B193625977 : Blo 654306 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B983015 : Blo 654306 983015 := bstep (se 1 (by rfl) ⟨737261, by rfl⟩ : syracuseStep 983015 = 1474523) B1474523
theorem B8421407 : Blo 654306 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B1474631 : Blo 654306 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B983111 : Blo 654306 983111 := bstep (se 1 (by rfl) ⟨737333, by rfl⟩ : syracuseStep 983111 = 1474667) B1474667
theorem B10617155 : Blo 654306 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B983375 : Blo 654306 983375 := bstep (se 1 (by rfl) ⟨737531, by rfl⟩ : syracuseStep 983375 = 1475063) B1475063
theorem B983531 : Blo 654306 983531 := bstep (se 1 (by rfl) ⟨737648, by rfl⟩ : syracuseStep 983531 = 1475297) B1475297
theorem B656103 : Blo 654306 656103 := bstep (se 1 (by rfl) ⟨492077, by rfl⟩ : syracuseStep 656103 = 984155) B984155
theorem B1246043 : Blo 654306 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B656255 : Blo 654306 656255 := bstep (se 1 (by rfl) ⟨492191, by rfl⟩ : syracuseStep 656255 = 984383) B984383
theorem B984185 : Blo 654306 984185 := bstep (se 2 (by rfl) ⟨369069, by rfl⟩ : syracuseStep 984185 = 738139) B738139
theorem B1049927 : Blo 654306 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B984479 : Blo 654306 984479 := bstep (se 1 (by rfl) ⟨738359, by rfl⟩ : syracuseStep 984479 = 1476719) B1476719
theorem B2885257 : Blo 654306 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B6325897 : Blo 654306 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B984731 : Blo 654306 984731 := bstep (se 1 (by rfl) ⟨738548, by rfl⟩ : syracuseStep 984731 = 1477097) B1477097
theorem B2492147 : Blo 654306 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B657151 : Blo 654306 657151 := bstep (se 1 (by rfl) ⟨492863, by rfl⟩ : syracuseStep 657151 = 985727) B985727
theorem B1869817 : Blo 654306 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B985115 : Blo 654306 985115 := bstep (se 1 (by rfl) ⟨738836, by rfl⟩ : syracuseStep 985115 = 1477673) B1477673
theorem B985199 : Blo 654306 985199 := bstep (se 1 (by rfl) ⟨738899, by rfl⟩ : syracuseStep 985199 = 1477799) B1477799
theorem B3737765 : Blo 654306 3737765 := bstep (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) B700831
theorem B985295 : Blo 654306 985295 := bstep (se 1 (by rfl) ⟨738971, by rfl⟩ : syracuseStep 985295 = 1477943) B1477943
theorem B657819 : Blo 654306 657819 := bstep (se 1 (by rfl) ⟨493364, by rfl⟩ : syracuseStep 657819 = 986729) B986729
theorem B2362063 : Blo 654306 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B985979 : Blo 654306 985979 := bstep (se 1 (by rfl) ⟨739484, by rfl⟩ : syracuseStep 985979 = 1478969) B1478969
theorem B986105 : Blo 654306 986105 := bstep (se 2 (by rfl) ⟨369789, by rfl⟩ : syracuseStep 986105 = 739579) B739579
theorem B986207 : Blo 654306 986207 := bstep (se 1 (by rfl) ⟨739655, by rfl⟩ : syracuseStep 986207 = 1479311) B1479311
theorem B986423 : Blo 654306 986423 := bstep (se 1 (by rfl) ⟨739817, by rfl⟩ : syracuseStep 986423 = 1479635) B1479635
theorem B1478123 : Blo 654306 1478123 := bstep (se 1 (by rfl) ⟨1108592, by rfl⟩ : syracuseStep 1478123 = 2217185) B2217185
theorem B1478249 : Blo 654306 1478249 := bstep (se 2 (by rfl) ⟨554343, by rfl⟩ : syracuseStep 1478249 = 1108687) B1108687
theorem B987257 : Blo 654306 987257 := bstep (se 2 (by rfl) ⟨370221, by rfl⟩ : syracuseStep 987257 = 740443) B740443
theorem B3739931 : Blo 654306 3739931 := bstep (se 1 (by rfl) ⟨2804948, by rfl⟩ : syracuseStep 3739931 = 5609897) B5609897
theorem B2494759 : Blo 654306 2494759 := bstep (se 1 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 2494759 = 3742139) B3742139
theorem B7082423 : Blo 654306 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B2364383 : Blo 654306 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B1053823 : Blo 654306 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B1119695 : Blo 654306 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B3315167 : Blo 654306 3315167 := bstep (se 1 (by rfl) ⟨2486375, by rfl⟩ : syracuseStep 3315167 = 4972751) B4972751
theorem B1873793 : Blo 654306 1873793 := bstep (se 2 (by rfl) ⟨702672, by rfl⟩ : syracuseStep 1873793 = 1405345) B1405345
theorem B2496521 : Blo 654306 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B6003497 : Blo 654306 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B4987817 : Blo 654306 4987817 := bstep (se 2 (by rfl) ⟨1870431, by rfl⟩ : syracuseStep 4987817 = 3740863) B3740863
theorem B4725971 : Blo 654306 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B11214935 : Blo 654306 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B2532001 : Blo 654306 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B544810063 : Blo 654306 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B4203859 : Blo 654306 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B11970271 : Blo 654306 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B47818619 : Blo 654306 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B14199097 : Blo 654306 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B18262543 : Blo 654306 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B4729661 : Blo 654306 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B22687127 : Blo 654306 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B183873397 : Blo 654306 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B2798063 : Blo 654306 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B2208491 : Blo 654306 2208491 := bstep (se 1 (by rfl) ⟨1656368, by rfl⟩ : syracuseStep 2208491 = 3312737) B3312737
theorem B8959319 : Blo 654306 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B2209193 : Blo 654306 2209193 := bstep (se 2 (by rfl) ⟨828447, by rfl⟩ : syracuseStep 2209193 = 1656895) B1656895
theorem B2209895 : Blo 654306 2209895 := bstep (se 1 (by rfl) ⟨1657421, by rfl⟩ : syracuseStep 2209895 = 3314843) B3314843
theorem B4733147 : Blo 654306 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B7486447 : Blo 654306 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B6306943 : Blo 654306 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B933115 : Blo 654306 933115 := bstep (se 1 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 933115 = 1399673) B1399673
theorem B933211 : Blo 654306 933211 := bstep (se 1 (by rfl) ⟨699908, by rfl⟩ : syracuseStep 933211 = 1399817) B1399817
theorem B999707 : Blo 654306 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B12337541 : Blo 654306 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B7979401 : Blo 654306 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B738031 : Blo 654306 738031 := bstep (se 1 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 738031 = 1107047) B1107047
theorem B4998023 : Blo 654306 4998023 := bstep (se 1 (by rfl) ⟨3748517, by rfl⟩ : syracuseStep 4998023 = 7497035) B7497035
theorem B20170271 : Blo 654306 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B2213513 : Blo 654306 2213513 := bstep (se 2 (by rfl) ⟨830067, by rfl⟩ : syracuseStep 2213513 = 1660135) B1660135
theorem B739183 : Blo 654306 739183 := bstep (se 1 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 739183 = 1108775) B1108775
theorem B4737761 : Blo 654306 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B11357981 : Blo 654306 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B5591339 : Blo 654306 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B2216375 : Blo 654306 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B2216591 : Blo 654306 2216591 := bstep (se 1 (by rfl) ⟨1662443, by rfl⟩ : syracuseStep 2216591 = 3324887) B3324887
theorem B2216861 : Blo 654306 2216861 := bstep (se 3 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 2216861 = 831323) B831323
theorem B3986491 : Blo 654306 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B258167969 : Blo 654306 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B7494119 : Blo 654306 7494119 := bstep (se 1 (by rfl) ⟨5620589, by rfl⟩ : syracuseStep 7494119 = 11241179) B11241179
theorem B8969069 : Blo 654306 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B2808827 : Blo 654306 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B2219183 : Blo 654306 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B2219291 : Blo 654306 2219291 := bstep (se 1 (by rfl) ⟨1664468, by rfl⟩ : syracuseStep 2219291 = 3328937) B3328937
theorem B3727241 : Blo 654306 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B1106075 : Blo 654306 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B1106183 : Blo 654306 1106183 := bstep (se 1 (by rfl) ⟨829637, by rfl⟩ : syracuseStep 1106183 = 1659275) B1659275
theorem B1663355 : Blo 654306 1663355 := bstep (se 1 (by rfl) ⟨1247516, by rfl⟩ : syracuseStep 1663355 = 2495033) B2495033
theorem B1663649 : Blo 654306 1663649 := bstep (se 2 (by rfl) ⟨623868, by rfl⟩ : syracuseStep 1663649 = 1247737) B1247737
theorem B9463013 : Blo 654306 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B1664327 : Blo 654306 1664327 := bstep (se 1 (by rfl) ⟨1248245, by rfl⟩ : syracuseStep 1664327 = 2496491) B2496491
theorem B5596775 : Blo 654306 5596775 := bstep (se 1 (by rfl) ⟨4197581, by rfl⟩ : syracuseStep 5596775 = 8395163) B8395163
theorem B1664671 : Blo 654306 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B1107803 : Blo 654306 1107803 := bstep (se 1 (by rfl) ⟨830852, by rfl⟩ : syracuseStep 1107803 = 1661705) B1661705
theorem B5401259 : Blo 654306 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B1109929 : Blo 654306 1109929 := bstep (se 2 (by rfl) ⟨416223, by rfl⟩ : syracuseStep 1109929 = 832447) B832447
theorem B2486497 : Blo 654306 2486497 := bstep (se 2 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 2486497 = 1864873) B1864873
theorem B5600087 : Blo 654306 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B1243127 : Blo 654306 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B1472507 : Blo 654306 1472507 := bstep (se 1 (by rfl) ⟨1104380, by rfl⟩ : syracuseStep 1472507 = 2208761) B2208761
theorem B15989363 : Blo 654306 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B981695 : Blo 654306 981695 := bstep (se 1 (by rfl) ⟨736271, by rfl⟩ : syracuseStep 981695 = 1472543) B1472543
theorem B981755 : Blo 654306 981755 := bstep (se 1 (by rfl) ⟨736316, by rfl⟩ : syracuseStep 981755 = 1472633) B1472633
theorem B981791 : Blo 654306 981791 := bstep (se 1 (by rfl) ⟨736343, by rfl⟩ : syracuseStep 981791 = 1472687) B1472687
theorem B1866824567 : Blo 654306 1866824567 := bstep (se 1 (by rfl) ⟨1400118425, by rfl⟩ : syracuseStep 1866824567 = 2800236851) B2800236851
theorem B654319 : Blo 654306 654319 := bstep (se 1 (by rfl) ⟨490739, by rfl⟩ : syracuseStep 654319 = 981479) B981479
theorem B982127 : Blo 654306 982127 := bstep (se 1 (by rfl) ⟨736595, by rfl⟩ : syracuseStep 982127 = 1473191) B1473191
theorem B654587 : Blo 654306 654587 := bstep (se 1 (by rfl) ⟨490940, by rfl⟩ : syracuseStep 654587 = 981881) B981881
theorem B1244479 : Blo 654306 1244479 := bstep (se 1 (by rfl) ⟨933359, by rfl⟩ : syracuseStep 1244479 = 1866719) B1866719
theorem B1244639 : Blo 654306 1244639 := bstep (se 1 (by rfl) ⟨933479, by rfl⟩ : syracuseStep 1244639 = 1866959) B1866959
theorem B654895 : Blo 654306 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B1048223 : Blo 654306 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B982943 : Blo 654306 982943 := bstep (se 1 (by rfl) ⟨737207, by rfl⟩ : syracuseStep 982943 = 1474415) B1474415
theorem B655343 : Blo 654306 655343 := bstep (se 1 (by rfl) ⟨491507, by rfl⟩ : syracuseStep 655343 = 983015) B983015
theorem B983087 : Blo 654306 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B655407 : Blo 654306 655407 := bstep (se 1 (by rfl) ⟨491555, by rfl⟩ : syracuseStep 655407 = 983111) B983111
theorem B7078103 : Blo 654306 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B655583 : Blo 654306 655583 := bstep (se 1 (by rfl) ⟨491687, by rfl⟩ : syracuseStep 655583 = 983375) B983375
theorem B8225027 : Blo 654306 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B655687 : Blo 654306 655687 := bstep (se 1 (by rfl) ⟨491765, by rfl⟩ : syracuseStep 655687 = 983531) B983531
theorem B656123 : Blo 654306 656123 := bstep (se 1 (by rfl) ⟨492092, by rfl⟩ : syracuseStep 656123 = 984185) B984185
theorem B3376001 : Blo 654306 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B656319 : Blo 654306 656319 := bstep (se 1 (by rfl) ⟨492239, by rfl⟩ : syracuseStep 656319 = 984479) B984479
theorem B984041 : Blo 654306 984041 := bstep (se 2 (by rfl) ⟨369015, by rfl⟩ : syracuseStep 984041 = 738031) B738031
theorem B1475675 : Blo 654306 1475675 := bstep (se 1 (by rfl) ⟨1106756, by rfl⟩ : syracuseStep 1475675 = 2213513) B2213513
theorem B656487 : Blo 654306 656487 := bstep (se 1 (by rfl) ⟨492365, by rfl⟩ : syracuseStep 656487 = 984731) B984731
theorem B656743 : Blo 654306 656743 := bstep (se 1 (by rfl) ⟨492557, by rfl⟩ : syracuseStep 656743 = 985115) B985115
theorem B656799 : Blo 654306 656799 := bstep (se 1 (by rfl) ⟨492599, by rfl⟩ : syracuseStep 656799 = 985199) B985199
theorem B2491843 : Blo 654306 2491843 := bstep (se 1 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 2491843 = 3737765) B3737765
theorem B656863 : Blo 654306 656863 := bstep (se 1 (by rfl) ⟨492647, by rfl⟩ : syracuseStep 656863 = 985295) B985295
theorem B5605145 : Blo 654306 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B657319 : Blo 654306 657319 := bstep (se 1 (by rfl) ⟨492989, by rfl⟩ : syracuseStep 657319 = 985979) B985979
theorem B657403 : Blo 654306 657403 := bstep (se 1 (by rfl) ⟨493052, by rfl⟩ : syracuseStep 657403 = 986105) B986105
theorem B657471 : Blo 654306 657471 := bstep (se 1 (by rfl) ⟨493103, by rfl⟩ : syracuseStep 657471 = 986207) B986207
theorem B657615 : Blo 654306 657615 := bstep (se 1 (by rfl) ⟨493211, by rfl⟩ : syracuseStep 657615 = 986423) B986423
theorem B15960361 : Blo 654306 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B985415 : Blo 654306 985415 := bstep (se 1 (by rfl) ⟨739061, by rfl⟩ : syracuseStep 985415 = 1478123) B1478123
theorem B985499 : Blo 654306 985499 := bstep (se 1 (by rfl) ⟨739124, by rfl⟩ : syracuseStep 985499 = 1478249) B1478249
theorem B985577 : Blo 654306 985577 := bstep (se 2 (by rfl) ⟨369591, by rfl⟩ : syracuseStep 985577 = 739183) B739183
theorem B7571987 : Blo 654306 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B2493089 : Blo 654306 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B658171 : Blo 654306 658171 := bstep (se 1 (by rfl) ⟨493628, by rfl⟩ : syracuseStep 658171 = 987257) B987257
theorem B2493287 : Blo 654306 2493287 := bstep (se 1 (by rfl) ⟨1869965, by rfl⟩ : syracuseStep 2493287 = 3739931) B3739931
theorem B4721615 : Blo 654306 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B1477583 : Blo 654306 1477583 := bstep (se 1 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 1477583 = 2216375) B2216375
theorem B1477727 : Blo 654306 1477727 := bstep (se 1 (by rfl) ⟨1108295, by rfl⟩ : syracuseStep 1477727 = 2216591) B2216591
theorem B1477907 : Blo 654306 1477907 := bstep (se 1 (by rfl) ⟨1108430, by rfl⟩ : syracuseStep 1477907 = 2216861) B2216861
theorem B1576255 : Blo 654306 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B24350057 : Blo 654306 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B3149417 : Blo 654306 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B1249195 : Blo 654306 1249195 := bstep (se 1 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 1249195 = 1873793) B1873793
theorem B4002331 : Blo 654306 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B1872551 : Blo 654306 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B1479455 : Blo 654306 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B3150647 : Blo 654306 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1479527 : Blo 654306 1479527 := bstep (se 1 (by rfl) ⟨1109645, by rfl⟩ : syracuseStep 1479527 = 2219291) B2219291
theorem B1479905 : Blo 654306 1479905 := bstep (se 2 (by rfl) ⟨554964, by rfl⟩ : syracuseStep 1479905 = 1109929) B1109929
theorem B3315005 : Blo 654306 3315005 := bstep (se 3 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 3315005 = 1243127) B1243127
theorem B7476623 : Blo 654306 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B3315329 : Blo 654306 3315329 := bstep (se 2 (by rfl) ⟨1243248, by rfl⟩ : syracuseStep 3315329 = 2486497) B2486497
theorem B5315321 : Blo 654306 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B3153107 : Blo 654306 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B5972879 : Blo 654306 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B3155431 : Blo 654306 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B10659575 : Blo 654306 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B829759 : Blo 654306 829759 := bstep (se 1 (by rfl) ⟨622319, by rfl⟩ : syracuseStep 829759 = 1244639) B1244639
theorem B698815 : Blo 654306 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B5614271 : Blo 654306 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B2665885 : Blo 654306 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B13446847 : Blo 654306 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B726413417 : Blo 654306 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B3158507 : Blo 654306 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B3847009 : Blo 654306 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B8434529 : Blo 654306 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B3322781 : Blo 654306 3322781 := bstep (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) B1246043
theorem B172111979 : Blo 654306 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B2799805 : Blo 654306 2799805 := bstep (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) B1049927
theorem B2210111 : Blo 654306 2210111 := bstep (se 1 (by rfl) ⟨1657583, by rfl⟩ : syracuseStep 2210111 = 3315167) B3315167
theorem B4996079 : Blo 654306 4996079 := bstep (se 1 (by rfl) ⟨3747059, by rfl⟩ : syracuseStep 4996079 = 7494119) B7494119
theorem B5979379 : Blo 654306 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B3325211 : Blo 654306 3325211 := bstep (se 1 (by rfl) ⟨2493908, by rfl⟩ : syracuseStep 3325211 = 4987817) B4987817
theorem B11943413 : Blo 654306 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B737383 : Blo 654306 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B737455 : Blo 654306 737455 := bstep (se 1 (by rfl) ⟨553091, by rfl⟩ : syracuseStep 737455 = 1106183) B1106183
theorem B3326345 : Blo 654306 3326345 := bstep (se 2 (by rfl) ⟨1247379, by rfl⟩ : syracuseStep 3326345 = 2494759) B2494759
theorem B6308675 : Blo 654306 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B738535 : Blo 654306 738535 := bstep (se 1 (by rfl) ⟨553901, by rfl⟩ : syracuseStep 738535 = 1107803) B1107803
theorem B15124751 : Blo 654306 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B9981929 : Blo 654306 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B8409257 : Blo 654306 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B1659305 : Blo 654306 1659305 := bstep (se 2 (by rfl) ⟨622239, by rfl⟩ : syracuseStep 1659305 = 1244479) B1244479
theorem B1244549711 : Blo 654306 1244549711 := bstep (se 1 (by rfl) ⟨933412283, by rfl⟩ : syracuseStep 1244549711 = 1866824567) B1866824567
theorem B10639201 : Blo 654306 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B3332015 : Blo 654306 3332015 := bstep (se 1 (by rfl) ⟨2499011, by rfl⟩ : syracuseStep 3332015 = 4998023) B4998023
theorem B1661431 : Blo 654306 1661431 := bstep (se 1 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 1661431 = 2492147) B2492147
theorem B2219561 : Blo 654306 2219561 := bstep (se 2 (by rfl) ⟨832335, by rfl⟩ : syracuseStep 2219561 = 1664671) B1664671
theorem B3727559 : Blo 654306 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B18932129 : Blo 654306 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B1664347 : Blo 654306 1664347 := bstep (se 1 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 1664347 = 2496521) B2496521
theorem B245164529 : Blo 654306 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B2484827 : Blo 654306 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B1108903 : Blo 654306 1108903 := bstep (se 1 (by rfl) ⟨831677, by rfl⟩ : syracuseStep 1108903 = 1663355) B1663355
theorem B1109099 : Blo 654306 1109099 := bstep (se 1 (by rfl) ⟨831824, by rfl⟩ : syracuseStep 1109099 = 1663649) B1663649
theorem B1109551 : Blo 654306 1109551 := bstep (se 1 (by rfl) ⟨832163, by rfl⟩ : syracuseStep 1109551 = 1664327) B1664327
theorem B3731183 : Blo 654306 3731183 := bstep (se 1 (by rfl) ⟨2798387, by rfl⟩ : syracuseStep 3731183 = 5596775) B5596775
theorem B31879079 : Blo 654306 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B1405097 : Blo 654306 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B3600839 : Blo 654306 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B4977125 : Blo 654306 4977125 := bstep (se 4 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 4977125 = 933211) B933211
theorem B1865375 : Blo 654306 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B1472327 : Blo 654306 1472327 := bstep (se 1 (by rfl) ⟨1104245, by rfl⟩ : syracuseStep 1472327 = 2208491) B2208491
theorem B3733391 : Blo 654306 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B1472795 : Blo 654306 1472795 := bstep (se 1 (by rfl) ⟨1104596, by rfl⟩ : syracuseStep 1472795 = 2209193) B2209193
theorem B981671 : Blo 654306 981671 := bstep (se 1 (by rfl) ⟨736253, by rfl⟩ : syracuseStep 981671 = 1472507) B1472507
theorem B1473263 : Blo 654306 1473263 := bstep (se 1 (by rfl) ⟨1104947, by rfl⟩ : syracuseStep 1473263 = 2209895) B2209895
theorem B1244153 : Blo 654306 1244153 := bstep (se 2 (by rfl) ⟨466557, by rfl⟩ : syracuseStep 1244153 = 933115) B933115
theorem B654463 : Blo 654306 654463 := bstep (se 1 (by rfl) ⟨490847, by rfl⟩ : syracuseStep 654463 = 981695) B981695
theorem B654503 : Blo 654306 654503 := bstep (se 1 (by rfl) ⟨490877, by rfl⟩ : syracuseStep 654503 = 981755) B981755
theorem B654527 : Blo 654306 654527 := bstep (se 1 (by rfl) ⟨490895, by rfl⟩ : syracuseStep 654527 = 981791) B981791
theorem B654751 : Blo 654306 654751 := bstep (se 1 (by rfl) ⟨491063, by rfl⟩ : syracuseStep 654751 = 982127) B982127
theorem B655295 : Blo 654306 655295 := bstep (se 1 (by rfl) ⟨491471, by rfl⟩ : syracuseStep 655295 = 982943) B982943
theorem B655391 : Blo 654306 655391 := bstep (se 1 (by rfl) ⟨491543, by rfl⟩ : syracuseStep 655391 = 983087) B983087
theorem B983177 : Blo 654306 983177 := bstep (se 2 (by rfl) ⟨368691, by rfl⟩ : syracuseStep 983177 = 737383) B737383
theorem B4718735 : Blo 654306 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B983273 : Blo 654306 983273 := bstep (se 2 (by rfl) ⟨368727, by rfl⟩ : syracuseStep 983273 = 737455) B737455
theorem B656027 : Blo 654306 656027 := bstep (se 1 (by rfl) ⟨492020, by rfl⟩ : syracuseStep 656027 = 984041) B984041
theorem B983783 : Blo 654306 983783 := bstep (se 1 (by rfl) ⟨737837, by rfl⟩ : syracuseStep 983783 = 1475675) B1475675
theorem B3736763 : Blo 654306 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B656943 : Blo 654306 656943 := bstep (se 1 (by rfl) ⟨492707, by rfl⟩ : syracuseStep 656943 = 985415) B985415
theorem B656999 : Blo 654306 656999 := bstep (se 1 (by rfl) ⟨492749, by rfl⟩ : syracuseStep 656999 = 985499) B985499
theorem B984713 : Blo 654306 984713 := bstep (se 2 (by rfl) ⟨369267, by rfl⟩ : syracuseStep 984713 = 738535) B738535
theorem B657051 : Blo 654306 657051 := bstep (se 1 (by rfl) ⟨492788, by rfl⟩ : syracuseStep 657051 = 985577) B985577
theorem B5047991 : Blo 654306 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B3147743 : Blo 654306 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B985055 : Blo 654306 985055 := bstep (se 1 (by rfl) ⟨738791, by rfl⟩ : syracuseStep 985055 = 1477583) B1477583
theorem B985151 : Blo 654306 985151 := bstep (se 1 (by rfl) ⟨738863, by rfl⟩ : syracuseStep 985151 = 1477727) B1477727
theorem B985271 : Blo 654306 985271 := bstep (se 1 (by rfl) ⟨738953, by rfl⟩ : syracuseStep 985271 = 1477907) B1477907
theorem B2099611 : Blo 654306 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B6654619 : Blo 654306 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B5606171 : Blo 654306 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B1248367 : Blo 654306 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B986303 : Blo 654306 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B2100431 : Blo 654306 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B986351 : Blo 654306 986351 := bstep (se 1 (by rfl) ⟨739763, by rfl⟩ : syracuseStep 986351 = 1479527) B1479527
theorem B986603 : Blo 654306 986603 := bstep (se 1 (by rfl) ⟨739952, by rfl⟩ : syracuseStep 986603 = 1479905) B1479905
theorem B4984415 : Blo 654306 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B1478537 : Blo 654306 1478537 := bstep (se 2 (by rfl) ⟨554451, by rfl⟩ : syracuseStep 1478537 = 1108903) B1108903
theorem B2101673 : Blo 654306 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B1479401 : Blo 654306 1479401 := bstep (se 2 (by rfl) ⟨554775, by rfl⟩ : syracuseStep 1479401 = 1109551) B1109551
theorem B17929129 : Blo 654306 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B1479707 : Blo 654306 1479707 := bstep (se 1 (by rfl) ⟨1109780, by rfl⟩ : syracuseStep 1479707 = 2219561) B2219561
theorem B12621419 : Blo 654306 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B3742847 : Blo 654306 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B2400559 : Blo 654306 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B3318083 : Blo 654306 3318083 := bstep (se 1 (by rfl) ⟨2488562, by rfl⟩ : syracuseStep 3318083 = 4977125) B4977125
theorem B2105671 : Blo 654306 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B7972505 : Blo 654306 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B829435 : Blo 654306 829435 := bstep (se 1 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 829435 = 1244153) B1244153
theorem B5483351 : Blo 654306 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B4205783 : Blo 654306 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B3322457 : Blo 654306 3322457 := bstep (se 2 (by rfl) ⟨1245921, by rfl⟩ : syracuseStep 3322457 = 2491843) B2491843
theorem B4207241 : Blo 654306 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B16233371 : Blo 654306 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B829699807 : Blo 654306 829699807 := bstep (se 1 (by rfl) ⟨622274855, by rfl⟩ : syracuseStep 829699807 = 1244549711) B1244549711
theorem B21280481 : Blo 654306 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B931753 : Blo 654306 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B2210003 : Blo 654306 2210003 := bstep (se 1 (by rfl) ⟨1657502, by rfl⟩ : syracuseStep 2210003 = 3315005) B3315005
theorem B2210219 : Blo 654306 2210219 := bstep (se 1 (by rfl) ⟨1657664, by rfl⟩ : syracuseStep 2210219 = 3315329) B3315329
theorem B3554513 : Blo 654306 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B458965277 : Blo 654306 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B3981919 : Blo 654306 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B5129345 : Blo 654306 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B1656551 : Blo 654306 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B14174189 : Blo 654306 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B739399 : Blo 654306 739399 := bstep (se 1 (by rfl) ⟨554549, by rfl⟩ : syracuseStep 739399 = 1109099) B1109099
theorem B21252719 : Blo 654306 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B936731 : Blo 654306 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B8408285 : Blo 654306 8408285 := bstep (se 3 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 8408285 = 3153107) B3153107
theorem B5623019 : Blo 654306 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B2215187 : Blo 654306 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B2215241 : Blo 654306 2215241 := bstep (se 2 (by rfl) ⟨830715, by rfl⟩ : syracuseStep 2215241 = 1661431) B1661431
theorem B3330719 : Blo 654306 3330719 := bstep (se 1 (by rfl) ⟨2498039, by rfl⟩ : syracuseStep 3330719 = 4996079) B4996079
theorem B2216807 : Blo 654306 2216807 := bstep (se 1 (by rfl) ⟨1662605, by rfl⟩ : syracuseStep 2216807 = 3325211) B3325211
theorem B2217563 : Blo 654306 2217563 := bstep (se 1 (by rfl) ⟨1663172, by rfl⟩ : syracuseStep 2217563 = 3326345) B3326345
theorem B2250667 : Blo 654306 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B10083167 : Blo 654306 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B1662059 : Blo 654306 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B2219129 : Blo 654306 2219129 := bstep (se 2 (by rfl) ⟨832173, by rfl⟩ : syracuseStep 2219129 = 1664347) B1664347
theorem B1662191 : Blo 654306 1662191 := bstep (se 1 (by rfl) ⟨1246643, by rfl⟩ : syracuseStep 1662191 = 2493287) B2493287
theorem B1106203 : Blo 654306 1106203 := bstep (se 1 (by rfl) ⟨829652, by rfl⟩ : syracuseStep 1106203 = 1659305) B1659305
theorem B1106345 : Blo 654306 1106345 := bstep (se 2 (by rfl) ⟨414879, by rfl⟩ : syracuseStep 1106345 = 829759) B829759
theorem B2221343 : Blo 654306 2221343 := bstep (se 1 (by rfl) ⟨1666007, by rfl⟩ : syracuseStep 2221343 = 3332015) B3332015
theorem B1665593 : Blo 654306 1665593 := bstep (se 2 (by rfl) ⟨624597, by rfl⟩ : syracuseStep 1665593 = 1249195) B1249195
theorem B2485039 : Blo 654306 2485039 := bstep (se 1 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 2485039 = 3727559) B3727559
theorem B5336441 : Blo 654306 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B7106383 : Blo 654306 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B163443019 : Blo 654306 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B14185601 : Blo 654306 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B2487455 : Blo 654306 2487455 := bstep (se 1 (by rfl) ⟨1865591, by rfl⟩ : syracuseStep 2487455 = 3731183) B3731183
theorem B484275611 : Blo 654306 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B3733073 : Blo 654306 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B1243583 : Blo 654306 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B981551 : Blo 654306 981551 := bstep (se 1 (by rfl) ⟨736163, by rfl⟩ : syracuseStep 981551 = 1472327) B1472327
theorem B2488927 : Blo 654306 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B981863 : Blo 654306 981863 := bstep (se 1 (by rfl) ⟨736397, by rfl⟩ : syracuseStep 981863 = 1472795) B1472795
theorem B1473407 : Blo 654306 1473407 := bstep (se 1 (by rfl) ⟨1105055, by rfl⟩ : syracuseStep 1473407 = 2210111) B2210111
theorem B654447 : Blo 654306 654447 := bstep (se 1 (by rfl) ⟨490835, by rfl⟩ : syracuseStep 654447 = 981671) B981671
theorem B982175 : Blo 654306 982175 := bstep (se 1 (by rfl) ⟨736631, by rfl⟩ : syracuseStep 982175 = 1473263) B1473263
theorem B7962275 : Blo 654306 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B655451 : Blo 654306 655451 := bstep (se 1 (by rfl) ⟨491588, by rfl⟩ : syracuseStep 655451 = 983177) B983177
theorem B3145823 : Blo 654306 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B655515 : Blo 654306 655515 := bstep (se 1 (by rfl) ⟨491636, by rfl⟩ : syracuseStep 655515 = 983273) B983273
theorem B1474937 : Blo 654306 1474937 := bstep (se 2 (by rfl) ⟨553101, by rfl⟩ : syracuseStep 1474937 = 1106203) B1106203
theorem B655855 : Blo 654306 655855 := bstep (se 1 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 655855 = 983783) B983783
theorem B2491175 : Blo 654306 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B5309225 : Blo 654306 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B656475 : Blo 654306 656475 := bstep (se 1 (by rfl) ⟨492356, by rfl⟩ : syracuseStep 656475 = 984713) B984713
theorem B5604461 : Blo 654306 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B2098495 : Blo 654306 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B656703 : Blo 654306 656703 := bstep (se 1 (by rfl) ⟨492527, by rfl⟩ : syracuseStep 656703 = 985055) B985055
theorem B656767 : Blo 654306 656767 := bstep (se 1 (by rfl) ⟨492575, by rfl⟩ : syracuseStep 656767 = 985151) B985151
theorem B656847 : Blo 654306 656847 := bstep (se 1 (by rfl) ⟨492635, by rfl⟩ : syracuseStep 656847 = 985271) B985271
theorem B3737447 : Blo 654306 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B657535 : Blo 654306 657535 := bstep (se 1 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 657535 = 986303) B986303
theorem B5605523 : Blo 654306 5605523 := bstep (se 1 (by rfl) ⟨4204142, by rfl⟩ : syracuseStep 5605523 = 8408285) B8408285
theorem B657567 : Blo 654306 657567 := bstep (se 1 (by rfl) ⟨493175, by rfl⟩ : syracuseStep 657567 = 986351) B986351
theorem B1476791 : Blo 654306 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B1476827 : Blo 654306 1476827 := bstep (se 1 (by rfl) ⟨1107620, by rfl⟩ : syracuseStep 1476827 = 2215241) B2215241
theorem B657735 : Blo 654306 657735 := bstep (se 1 (by rfl) ⟨493301, by rfl⟩ : syracuseStep 657735 = 986603) B986603
theorem B985691 : Blo 654306 985691 := bstep (se 1 (by rfl) ⟨739268, by rfl⟩ : syracuseStep 985691 = 1478537) B1478537
theorem B985865 : Blo 654306 985865 := bstep (se 2 (by rfl) ⟨369699, by rfl⟩ : syracuseStep 985865 = 739399) B739399
theorem B986267 : Blo 654306 986267 := bstep (se 1 (by rfl) ⟨739700, by rfl⟩ : syracuseStep 986267 = 1479401) B1479401
theorem B1477871 : Blo 654306 1477871 := bstep (se 1 (by rfl) ⟨1108403, by rfl⟩ : syracuseStep 1477871 = 2216807) B2216807
theorem B986471 : Blo 654306 986471 := bstep (se 1 (by rfl) ⟨739853, by rfl⟩ : syracuseStep 986471 = 1479707) B1479707
theorem B35491301 : Blo 654306 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B1478375 : Blo 654306 1478375 := bstep (se 1 (by rfl) ⟨1108781, by rfl⟩ : syracuseStep 1478375 = 2217563) B2217563
theorem B3313385 : Blo 654306 3313385 := bstep (se 2 (by rfl) ⟨1242519, by rfl⟩ : syracuseStep 3313385 = 2485039) B2485039
theorem B6722111 : Blo 654306 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B1479419 : Blo 654306 1479419 := bstep (se 1 (by rfl) ⟨1109564, by rfl⟩ : syracuseStep 1479419 = 2219129) B2219129
theorem B2495231 : Blo 654306 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B9475177 : Blo 654306 9475177 := bstep (se 2 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 9475177 = 7106383) B7106383
theorem B1480895 : Blo 654306 1480895 := bstep (se 1 (by rfl) ⟨1110671, by rfl⟩ : syracuseStep 1480895 = 2221343) B2221343
theorem B5315003 : Blo 654306 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B2497949 : Blo 654306 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B10822247 : Blo 654306 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B3318569 : Blo 654306 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B829055 : Blo 654306 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B2369675 : Blo 654306 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B3419563 : Blo 654306 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B9449459 : Blo 654306 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B11219309 : Blo 654306 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B14168479 : Blo 654306 14168479 := bstep (se 1 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 14168479 = 21252719) B21252719
theorem B3748679 : Blo 654306 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B3322943 : Blo 654306 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B2799481 : Blo 654306 2799481 := bstep (se 2 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 2799481 = 2099611) B2099611
theorem B2212055 : Blo 654306 2212055 := bstep (se 1 (by rfl) ⟨1659041, by rfl⟩ : syracuseStep 2212055 = 3318083) B3318083
theorem B737563 : Blo 654306 737563 := bstep (se 1 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 737563 = 1106345) B1106345
theorem B217924025 : Blo 654306 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B23905505 : Blo 654306 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B3655567 : Blo 654306 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B2803855 : Blo 654306 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B3557627 : Blo 654306 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B1106266409 : Blo 654306 1106266409 := bstep (se 2 (by rfl) ⟨414849903, by rfl⟩ : syracuseStep 1106266409 = 829699807) B829699807
theorem B3000889 : Blo 654306 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B2214971 : Blo 654306 2214971 := bstep (se 1 (by rfl) ⟨1661228, by rfl⟩ : syracuseStep 2214971 = 3322457) B3322457
theorem B9457067 : Blo 654306 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B1658303 : Blo 654306 1658303 := bstep (se 1 (by rfl) ⟨1243727, by rfl⟩ : syracuseStep 1658303 = 2487455) B2487455
theorem B322850407 : Blo 654306 322850407 := bstep (se 1 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 322850407 = 484275611) B484275611
theorem B4969349 : Blo 654306 4969349 := bstep (se 4 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 4969349 = 931753) B931753
theorem B305976851 : Blo 654306 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B2807561 : Blo 654306 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B3365327 : Blo 654306 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B1104367 : Blo 654306 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B12802981 : Blo 654306 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B1105913 : Blo 654306 1105913 := bstep (se 2 (by rfl) ⟨414717, by rfl⟩ : syracuseStep 1105913 = 829435) B829435
theorem B2220479 : Blo 654306 2220479 := bstep (se 1 (by rfl) ⟨1665359, by rfl⟩ : syracuseStep 2220479 = 3330719) B3330719
theorem B8414279 : Blo 654306 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B1664489 : Blo 654306 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B1108039 : Blo 654306 1108039 := bstep (se 1 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 1108039 = 1662059) B1662059
theorem B1108127 : Blo 654306 1108127 := bstep (se 1 (by rfl) ⟨831095, by rfl⟩ : syracuseStep 1108127 = 1662191) B1662191
theorem B1110395 : Blo 654306 1110395 := bstep (se 1 (by rfl) ⟨832796, by rfl⟩ : syracuseStep 1110395 = 1665593) B1665593
theorem B5601149 : Blo 654306 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B2488715 : Blo 654306 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B14186987 : Blo 654306 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B1473335 : Blo 654306 1473335 := bstep (se 1 (by rfl) ⟨1105001, by rfl⟩ : syracuseStep 1473335 = 2210003) B2210003
theorem B1473479 : Blo 654306 1473479 := bstep (se 1 (by rfl) ⟨1105109, by rfl⟩ : syracuseStep 1473479 = 2210219) B2210219
theorem B654367 : Blo 654306 654367 := bstep (se 1 (by rfl) ⟨490775, by rfl⟩ : syracuseStep 654367 = 981551) B981551
theorem B654575 : Blo 654306 654575 := bstep (se 1 (by rfl) ⟨490931, by rfl⟩ : syracuseStep 654575 = 981863) B981863
theorem B982271 : Blo 654306 982271 := bstep (se 1 (by rfl) ⟨736703, by rfl⟩ : syracuseStep 982271 = 1473407) B1473407
theorem B654783 : Blo 654306 654783 := bstep (se 1 (by rfl) ⟨491087, by rfl⟩ : syracuseStep 654783 = 982175) B982175
theorem B5308183 : Blo 654306 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B2097215 : Blo 654306 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B1474703 : Blo 654306 1474703 := bstep (se 1 (by rfl) ⟨1106027, by rfl⟩ : syracuseStep 1474703 = 2212055) B2212055
theorem B983291 : Blo 654306 983291 := bstep (se 1 (by rfl) ⟨737468, by rfl⟩ : syracuseStep 983291 = 1474937) B1474937
theorem B983417 : Blo 654306 983417 := bstep (se 2 (by rfl) ⟨368781, by rfl⟩ : syracuseStep 983417 = 737563) B737563
theorem B3539483 : Blo 654306 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B3736307 : Blo 654306 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B2491631 : Blo 654306 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B3737015 : Blo 654306 3737015 := bstep (se 1 (by rfl) ⟨2802761, by rfl⟩ : syracuseStep 3737015 = 5605523) B5605523
theorem B984527 : Blo 654306 984527 := bstep (se 1 (by rfl) ⟨738395, by rfl⟩ : syracuseStep 984527 = 1476791) B1476791
theorem B984551 : Blo 654306 984551 := bstep (se 1 (by rfl) ⟨738413, by rfl⟩ : syracuseStep 984551 = 1476827) B1476827
theorem B737510939 : Blo 654306 737510939 := bstep (se 1 (by rfl) ⟨553133204, by rfl⟩ : syracuseStep 737510939 = 1106266409) B1106266409
theorem B657127 : Blo 654306 657127 := bstep (se 1 (by rfl) ⟨492845, by rfl⟩ : syracuseStep 657127 = 985691) B985691
theorem B657243 : Blo 654306 657243 := bstep (se 1 (by rfl) ⟨492932, by rfl⟩ : syracuseStep 657243 = 985865) B985865
theorem B1476647 : Blo 654306 1476647 := bstep (se 1 (by rfl) ⟨1107485, by rfl⟩ : syracuseStep 1476647 = 2214971) B2214971
theorem B657511 : Blo 654306 657511 := bstep (se 1 (by rfl) ⟨493133, by rfl⟩ : syracuseStep 657511 = 986267) B986267
theorem B985247 : Blo 654306 985247 := bstep (se 1 (by rfl) ⟨738935, by rfl⟩ : syracuseStep 985247 = 1477871) B1477871
theorem B657647 : Blo 654306 657647 := bstep (se 1 (by rfl) ⟨493235, by rfl⟩ : syracuseStep 657647 = 986471) B986471
theorem B23660867 : Blo 654306 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B985583 : Blo 654306 985583 := bstep (se 1 (by rfl) ⟨739187, by rfl⟩ : syracuseStep 985583 = 1478375) B1478375
theorem B1477385 : Blo 654306 1477385 := bstep (se 2 (by rfl) ⟨554019, by rfl⟩ : syracuseStep 1477385 = 1108039) B1108039
theorem B3738473 : Blo 654306 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B986279 : Blo 654306 986279 := bstep (se 1 (by rfl) ⟨739709, by rfl⟩ : syracuseStep 986279 = 1479419) B1479419
theorem B3312899 : Blo 654306 3312899 := bstep (se 1 (by rfl) ⟨2484674, by rfl⟩ : syracuseStep 3312899 = 4969349) B4969349
theorem B4001185 : Blo 654306 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B203984567 : Blo 654306 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B987263 : Blo 654306 987263 := bstep (se 1 (by rfl) ⟨740447, by rfl⟩ : syracuseStep 987263 = 1480895) B1480895
theorem B3543335 : Blo 654306 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B4559417 : Blo 654306 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B1480319 : Blo 654306 1480319 := bstep (se 1 (by rfl) ⟨1110239, by rfl⟩ : syracuseStep 1480319 = 2220479) B2220479
theorem B7214831 : Blo 654306 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B5609519 : Blo 654306 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B6299639 : Blo 654306 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B7479539 : Blo 654306 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B2499119 : Blo 654306 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B15937003 : Blo 654306 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B2371751 : Blo 654306 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B2797993 : Blo 654306 2797993 := bstep (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) B2098495
theorem B6304711 : Blo 654306 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B2208923 : Blo 654306 2208923 := bstep (se 1 (by rfl) ⟨1656692, by rfl⟩ : syracuseStep 2208923 = 3313385) B3313385
theorem B2243551 : Blo 654306 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B2210813 : Blo 654306 2210813 := bstep (se 3 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 2210813 = 829055) B829055
theorem B7486829 : Blo 654306 7486829 := bstep (se 3 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 7486829 = 2807561) B2807561
theorem B737275 : Blo 654306 737275 := bstep (se 1 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 737275 = 1105913) B1105913
theorem B2212379 : Blo 654306 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B18891305 : Blo 654306 18891305 := bstep (se 2 (by rfl) ⟨7084239, by rfl⟩ : syracuseStep 18891305 = 14168479) B14168479
theorem B738751 : Blo 654306 738751 := bstep (se 1 (by rfl) ⟨554063, by rfl⟩ : syracuseStep 738751 = 1108127) B1108127
theorem B12633569 : Blo 654306 12633569 := bstep (se 2 (by rfl) ⟨4737588, by rfl⟩ : syracuseStep 12633569 = 9475177) B9475177
theorem B740263 : Blo 654306 740263 := bstep (se 1 (by rfl) ⟨555197, by rfl⟩ : syracuseStep 740263 = 1110395) B1110395
theorem B2215295 : Blo 654306 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B1659143 : Blo 654306 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B9457991 : Blo 654306 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B1660783 : Blo 654306 1660783 := bstep (se 1 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 1660783 = 2491175) B2491175
theorem B1105535 : Blo 654306 1105535 := bstep (se 1 (by rfl) ⟨829151, by rfl⟩ : syracuseStep 1105535 = 1658303) B1658303
theorem B4874089 : Blo 654306 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B4481407 : Blo 654306 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B1663487 : Blo 654306 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B2324522933 : Blo 654306 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B430467209 : Blo 654306 430467209 := bstep (se 2 (by rfl) ⟨161425203, by rfl⟩ : syracuseStep 430467209 = 322850407) B322850407
theorem B1665299 : Blo 654306 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B6319133 : Blo 654306 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B1109659 : Blo 654306 1109659 := bstep (se 1 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 1109659 = 1664489) B1664489
theorem B3732641 : Blo 654306 3732641 := bstep (se 2 (by rfl) ⟨1399740, by rfl⟩ : syracuseStep 3732641 = 2799481) B2799481
theorem B1472489 : Blo 654306 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B17070641 : Blo 654306 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B3734099 : Blo 654306 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B982223 : Blo 654306 982223 := bstep (se 1 (by rfl) ⟨736667, by rfl⟩ : syracuseStep 982223 = 1473335) B1473335
theorem B982319 : Blo 654306 982319 := bstep (se 1 (by rfl) ⟨736739, by rfl⟩ : syracuseStep 982319 = 1473479) B1473479
theorem B654847 : Blo 654306 654847 := bstep (se 1 (by rfl) ⟨491135, by rfl⟩ : syracuseStep 654847 = 982271) B982271
theorem B7077577 : Blo 654306 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B983135 : Blo 654306 983135 := bstep (se 1 (by rfl) ⟨737351, by rfl⟩ : syracuseStep 983135 = 1474703) B1474703
theorem B655527 : Blo 654306 655527 := bstep (se 1 (by rfl) ⟨491645, by rfl⟩ : syracuseStep 655527 = 983291) B983291
theorem B655611 : Blo 654306 655611 := bstep (se 1 (by rfl) ⟨491708, by rfl⟩ : syracuseStep 655611 = 983417) B983417
theorem B2359655 : Blo 654306 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B1474919 : Blo 654306 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B2490871 : Blo 654306 2490871 := bstep (se 1 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 2490871 = 3736307) B3736307
theorem B2491343 : Blo 654306 2491343 := bstep (se 1 (by rfl) ⟨1868507, by rfl⟩ : syracuseStep 2491343 = 3737015) B3737015
theorem B656351 : Blo 654306 656351 := bstep (se 1 (by rfl) ⟨492263, by rfl⟩ : syracuseStep 656351 = 984527) B984527
theorem B8422379 : Blo 654306 8422379 := bstep (se 1 (by rfl) ⟨6316784, by rfl⟩ : syracuseStep 8422379 = 12633569) B12633569
theorem B656367 : Blo 654306 656367 := bstep (se 1 (by rfl) ⟨492275, by rfl⟩ : syracuseStep 656367 = 984551) B984551
theorem B984431 : Blo 654306 984431 := bstep (se 1 (by rfl) ⟨738323, by rfl⟩ : syracuseStep 984431 = 1476647) B1476647
theorem B656831 : Blo 654306 656831 := bstep (se 1 (by rfl) ⟨492623, by rfl⟩ : syracuseStep 656831 = 985247) B985247
theorem B657055 : Blo 654306 657055 := bstep (se 1 (by rfl) ⟨492791, by rfl⟩ : syracuseStep 657055 = 985583) B985583
theorem B984923 : Blo 654306 984923 := bstep (se 1 (by rfl) ⟨738692, by rfl⟩ : syracuseStep 984923 = 1477385) B1477385
theorem B2492315 : Blo 654306 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B985001 : Blo 654306 985001 := bstep (se 2 (by rfl) ⟨369375, by rfl⟩ : syracuseStep 985001 = 738751) B738751
theorem B657519 : Blo 654306 657519 := bstep (se 1 (by rfl) ⟨493139, by rfl⟩ : syracuseStep 657519 = 986279) B986279
theorem B1476863 : Blo 654306 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B135989711 : Blo 654306 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B658175 : Blo 654306 658175 := bstep (se 1 (by rfl) ⟨493631, by rfl⟩ : syracuseStep 658175 = 987263) B987263
theorem B2362223 : Blo 654306 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B986879 : Blo 654306 986879 := bstep (se 1 (by rfl) ⟨740159, by rfl⟩ : syracuseStep 986879 = 1480319) B1480319
theorem B987017 : Blo 654306 987017 := bstep (se 2 (by rfl) ⟨370131, by rfl⟩ : syracuseStep 987017 = 740263) B740263
theorem B3739679 : Blo 654306 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B1479545 : Blo 654306 1479545 := bstep (se 2 (by rfl) ⟨554829, by rfl⟩ : syracuseStep 1479545 = 1109659) B1109659
theorem B4199759 : Blo 654306 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B4986359 : Blo 654306 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B1581167 : Blo 654306 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B2991401 : Blo 654306 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B11380427 : Blo 654306 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B4991219 : Blo 654306 4991219 := bstep (se 1 (by rfl) ⟨3743414, by rfl⟩ : syracuseStep 4991219 = 7486829) B7486829
theorem B6498785 : Blo 654306 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B12594203 : Blo 654306 12594203 := bstep (se 1 (by rfl) ⟨9445652, by rfl⟩ : syracuseStep 12594203 = 18891305) B18891305
theorem B5975209 : Blo 654306 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B2208599 : Blo 654306 2208599 := bstep (se 1 (by rfl) ⟨1656449, by rfl⟩ : syracuseStep 2208599 = 3312899) B3312899
theorem B6305327 : Blo 654306 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B21249337 : Blo 654306 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B737023 : Blo 654306 737023 := bstep (se 1 (by rfl) ⟨552767, by rfl⟩ : syracuseStep 737023 = 1105535) B1105535
theorem B63095645 : Blo 654306 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B8406281 : Blo 654306 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B1549681955 : Blo 654306 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B4212755 : Blo 654306 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B2214377 : Blo 654306 2214377 := bstep (se 2 (by rfl) ⟨830391, by rfl⟩ : syracuseStep 2214377 = 1660783) B1660783
theorem B1398143 : Blo 654306 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B1661087 : Blo 654306 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B491673959 : Blo 654306 491673959 := bstep (se 1 (by rfl) ⟨368755469, by rfl⟩ : syracuseStep 491673959 = 737510939) B737510939
theorem B1106095 : Blo 654306 1106095 := bstep (se 1 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 1106095 = 1659143) B1659143
theorem B3039611 : Blo 654306 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B4809887 : Blo 654306 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B5334913 : Blo 654306 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B1108991 : Blo 654306 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B1666079 : Blo 654306 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B3730657 : Blo 654306 3730657 := bstep (se 2 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 3730657 = 2797993) B2797993
theorem B286978139 : Blo 654306 286978139 := bstep (se 1 (by rfl) ⟨215233604, by rfl⟩ : syracuseStep 286978139 = 430467209) B430467209
theorem B1110199 : Blo 654306 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B1472615 : Blo 654306 1472615 := bstep (se 1 (by rfl) ⟨1104461, by rfl⟩ : syracuseStep 1472615 = 2208923) B2208923
theorem B2488427 : Blo 654306 2488427 := bstep (se 1 (by rfl) ⟨1866320, by rfl⟩ : syracuseStep 2488427 = 3732641) B3732641
theorem B981659 : Blo 654306 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B2489399 : Blo 654306 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B1473875 : Blo 654306 1473875 := bstep (se 1 (by rfl) ⟨1105406, by rfl⟩ : syracuseStep 1473875 = 2210813) B2210813
theorem B654815 : Blo 654306 654815 := bstep (se 1 (by rfl) ⟨491111, by rfl⟩ : syracuseStep 654815 = 982223) B982223
theorem B654879 : Blo 654306 654879 := bstep (se 1 (by rfl) ⟨491159, by rfl⟩ : syracuseStep 654879 = 982319) B982319
theorem B9436769 : Blo 654306 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B983033 : Blo 654306 983033 := bstep (se 2 (by rfl) ⟨368637, by rfl⟩ : syracuseStep 983033 = 737275) B737275
theorem B655423 : Blo 654306 655423 := bstep (se 1 (by rfl) ⟨491567, by rfl⟩ : syracuseStep 655423 = 983135) B983135
theorem B1474793 : Blo 654306 1474793 := bstep (se 2 (by rfl) ⟨553047, by rfl⟩ : syracuseStep 1474793 = 1106095) B1106095
theorem B1573103 : Blo 654306 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B983279 : Blo 654306 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B5604187 : Blo 654306 5604187 := bstep (se 1 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 5604187 = 8406281) B8406281
theorem B656287 : Blo 654306 656287 := bstep (se 1 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 656287 = 984431) B984431
theorem B656615 : Blo 654306 656615 := bstep (se 1 (by rfl) ⟨492461, by rfl⟩ : syracuseStep 656615 = 984923) B984923
theorem B656667 : Blo 654306 656667 := bstep (se 1 (by rfl) ⟨492500, by rfl⟩ : syracuseStep 656667 = 985001) B985001
theorem B984575 : Blo 654306 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B1476251 : Blo 654306 1476251 := bstep (se 1 (by rfl) ⟨1107188, by rfl⟩ : syracuseStep 1476251 = 2214377) B2214377
theorem B1574815 : Blo 654306 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B657919 : Blo 654306 657919 := bstep (se 1 (by rfl) ⟨493439, by rfl⟩ : syracuseStep 657919 = 986879) B986879
theorem B7113217 : Blo 654306 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B658011 : Blo 654306 658011 := bstep (se 1 (by rfl) ⟨493508, by rfl⟩ : syracuseStep 658011 = 987017) B987017
theorem B2493119 : Blo 654306 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B986363 : Blo 654306 986363 := bstep (se 1 (by rfl) ⟨739772, by rfl⟩ : syracuseStep 986363 = 1479545) B1479545
theorem B7966945 : Blo 654306 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B327782639 : Blo 654306 327782639 := bstep (se 1 (by rfl) ⟨245836979, by rfl⟩ : syracuseStep 327782639 = 491673959) B491673959
theorem B1480265 : Blo 654306 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B4332523 : Blo 654306 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B8396135 : Blo 654306 8396135 := bstep (se 1 (by rfl) ⟨6297101, by rfl⟩ : syracuseStep 8396135 = 12594203) B12594203
theorem B4203551 : Blo 654306 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B5614919 : Blo 654306 5614919 := bstep (se 1 (by rfl) ⟨4211189, by rfl⟩ : syracuseStep 5614919 = 8422379) B8422379
theorem B3321161 : Blo 654306 3321161 := bstep (se 2 (by rfl) ⟨1245435, by rfl⟩ : syracuseStep 3321161 = 2490871) B2490871
theorem B1033121303 : Blo 654306 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B2799839 : Blo 654306 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B932095 : Blo 654306 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B3324239 : Blo 654306 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B32422517 : Blo 654306 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B7586951 : Blo 654306 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B3327479 : Blo 654306 3327479 := bstep (se 1 (by rfl) ⟨2495609, by rfl⟩ : syracuseStep 3327479 = 4991219) B4991219
theorem B739327 : Blo 654306 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B191318759 : Blo 654306 191318759 := bstep (se 1 (by rfl) ⟨143489069, by rfl⟩ : syracuseStep 191318759 = 286978139) B286978139
theorem B1658951 : Blo 654306 1658951 := bstep (se 1 (by rfl) ⟨1244213, by rfl⟩ : syracuseStep 1658951 = 2488427) B2488427
theorem B28332449 : Blo 654306 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B1659599 : Blo 654306 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B4216445 : Blo 654306 4216445 := bstep (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) B1581167
theorem B1660895 : Blo 654306 1660895 := bstep (se 1 (by rfl) ⟨1245671, by rfl⟩ : syracuseStep 1660895 = 2491343) B2491343
theorem B1661543 : Blo 654306 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B2808503 : Blo 654306 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B90659807 : Blo 654306 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B168255053 : Blo 654306 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B1107391 : Blo 654306 1107391 := bstep (se 1 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 1107391 = 1661087) B1661087
theorem B4974209 : Blo 654306 4974209 := bstep (se 2 (by rfl) ⟨1865328, by rfl⟩ : syracuseStep 4974209 = 3730657) B3730657
theorem B3206591 : Blo 654306 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B1994267 : Blo 654306 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B1110719 : Blo 654306 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B1472399 : Blo 654306 1472399 := bstep (se 1 (by rfl) ⟨1104299, by rfl⟩ : syracuseStep 1472399 = 2208599) B2208599
theorem B981743 : Blo 654306 981743 := bstep (se 1 (by rfl) ⟨736307, by rfl⟩ : syracuseStep 981743 = 1472615) B1472615
theorem B654439 : Blo 654306 654439 := bstep (se 1 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 654439 = 981659) B981659
theorem B982583 : Blo 654306 982583 := bstep (se 1 (by rfl) ⟨736937, by rfl⟩ : syracuseStep 982583 = 1473875) B1473875
theorem B982697 : Blo 654306 982697 := bstep (se 2 (by rfl) ⟨368511, by rfl⟩ : syracuseStep 982697 = 737023) B737023
theorem B6291179 : Blo 654306 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B655355 : Blo 654306 655355 := bstep (se 1 (by rfl) ⟨491516, by rfl⟩ : syracuseStep 655355 = 983033) B983033
theorem B983195 : Blo 654306 983195 := bstep (se 1 (by rfl) ⟨737396, by rfl⟩ : syracuseStep 983195 = 1474793) B1474793
theorem B1048735 : Blo 654306 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B655519 : Blo 654306 655519 := bstep (se 1 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 655519 = 983279) B983279
theorem B656383 : Blo 654306 656383 := bstep (se 1 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 656383 = 984575) B984575
theorem B984167 : Blo 654306 984167 := bstep (se 1 (by rfl) ⟨738125, by rfl⟩ : syracuseStep 984167 = 1476251) B1476251
theorem B7472249 : Blo 654306 7472249 := bstep (se 2 (by rfl) ⟨2802093, by rfl⟩ : syracuseStep 7472249 = 5604187) B5604187
theorem B1476521 : Blo 654306 1476521 := bstep (se 2 (by rfl) ⟨553695, by rfl⟩ : syracuseStep 1476521 = 1107391) B1107391
theorem B657575 : Blo 654306 657575 := bstep (se 1 (by rfl) ⟨493181, by rfl⟩ : syracuseStep 657575 = 986363) B986363
theorem B2099753 : Blo 654306 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B985769 : Blo 654306 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B986843 : Blo 654306 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B1872335 : Blo 654306 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B112170035 : Blo 654306 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B10622593 : Blo 654306 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B3316139 : Blo 654306 3316139 := bstep (se 1 (by rfl) ⟨2487104, by rfl⟩ : syracuseStep 3316139 = 4974209) B4974209
theorem B3743279 : Blo 654306 3743279 := bstep (se 1 (by rfl) ⟨2807459, by rfl⟩ : syracuseStep 3743279 = 5614919) B5614919
theorem B2137727 : Blo 654306 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B5776697 : Blo 654306 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B5318045 : Blo 654306 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B127545839 : Blo 654306 127545839 := bstep (se 1 (by rfl) ⟨95659379, by rfl⟩ : syracuseStep 127545839 = 191318759) B191318759
theorem B18888299 : Blo 654306 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B20231869 : Blo 654306 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B9484289 : Blo 654306 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B60439871 : Blo 654306 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B2802367 : Blo 654306 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B2214107 : Blo 654306 2214107 := bstep (se 1 (by rfl) ⟨1660580, by rfl⟩ : syracuseStep 2214107 = 3321161) B3321161
theorem B740479 : Blo 654306 740479 := bstep (se 1 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 740479 = 1110719) B1110719
theorem B2216159 : Blo 654306 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B21615011 : Blo 654306 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B2218319 : Blo 654306 2218319 := bstep (se 1 (by rfl) ⟨1663739, by rfl⟩ : syracuseStep 2218319 = 3327479) B3327479
theorem B1662079 : Blo 654306 1662079 := bstep (se 1 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 1662079 = 2493119) B2493119
theorem B1105967 : Blo 654306 1105967 := bstep (se 1 (by rfl) ⟨829475, by rfl⟩ : syracuseStep 1105967 = 1658951) B1658951
theorem B218521759 : Blo 654306 218521759 := bstep (se 1 (by rfl) ⟨163891319, by rfl⟩ : syracuseStep 218521759 = 327782639) B327782639
theorem B1106399 : Blo 654306 1106399 := bstep (se 1 (by rfl) ⟨829799, by rfl⟩ : syracuseStep 1106399 = 1659599) B1659599
theorem B2810963 : Blo 654306 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B1107263 : Blo 654306 1107263 := bstep (se 1 (by rfl) ⟨830447, by rfl⟩ : syracuseStep 1107263 = 1660895) B1660895
theorem B1107695 : Blo 654306 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B5597423 : Blo 654306 5597423 := bstep (se 1 (by rfl) ⟨4198067, by rfl⟩ : syracuseStep 5597423 = 8396135) B8396135
theorem B688747535 : Blo 654306 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B1242793 : Blo 654306 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B981599 : Blo 654306 981599 := bstep (se 1 (by rfl) ⟨736199, by rfl⟩ : syracuseStep 981599 = 1472399) B1472399
theorem B1866559 : Blo 654306 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B654495 : Blo 654306 654495 := bstep (se 1 (by rfl) ⟨490871, by rfl⟩ : syracuseStep 654495 = 981743) B981743
theorem B655055 : Blo 654306 655055 := bstep (se 1 (by rfl) ⟨491291, by rfl⟩ : syracuseStep 655055 = 982583) B982583
theorem B655131 : Blo 654306 655131 := bstep (se 1 (by rfl) ⟨491348, by rfl⟩ : syracuseStep 655131 = 982697) B982697
theorem B4194119 : Blo 654306 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B655463 : Blo 654306 655463 := bstep (se 1 (by rfl) ⟨491597, by rfl⟩ : syracuseStep 655463 = 983195) B983195
theorem B656111 : Blo 654306 656111 := bstep (se 1 (by rfl) ⟨492083, by rfl⟩ : syracuseStep 656111 = 984167) B984167
theorem B4981499 : Blo 654306 4981499 := bstep (se 1 (by rfl) ⟨3736124, by rfl⟩ : syracuseStep 4981499 = 7472249) B7472249
theorem B3736489 : Blo 654306 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B984347 : Blo 654306 984347 := bstep (se 1 (by rfl) ⟨738260, by rfl⟩ : syracuseStep 984347 = 1476521) B1476521
theorem B1476071 : Blo 654306 1476071 := bstep (se 1 (by rfl) ⟨1107053, by rfl⟩ : syracuseStep 1476071 = 2214107) B2214107
theorem B657179 : Blo 654306 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B657895 : Blo 654306 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B1477439 : Blo 654306 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B1248223 : Blo 654306 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B74780023 : Blo 654306 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B15404525 : Blo 654306 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B987305 : Blo 654306 987305 := bstep (se 2 (by rfl) ⟨370239, by rfl⟩ : syracuseStep 987305 = 740479) B740479
theorem B1478879 : Blo 654306 1478879 := bstep (se 1 (by rfl) ⟨1109159, by rfl⟩ : syracuseStep 1478879 = 2218319) B2218319
theorem B2495519 : Blo 654306 2495519 := bstep (se 1 (by rfl) ⟨1871639, by rfl⟩ : syracuseStep 2495519 = 3743279) B3743279
theorem B1873975 : Blo 654306 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B3545363 : Blo 654306 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B14163457 : Blo 654306 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B26975825 : Blo 654306 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B12592199 : Blo 654306 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B11184317 : Blo 654306 11184317 := bstep (se 3 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 11184317 = 4194119) B4194119
theorem B2210759 : Blo 654306 2210759 := bstep (se 1 (by rfl) ⟨1658069, by rfl⟩ : syracuseStep 2210759 = 3316139) B3316139
theorem B1425151 : Blo 654306 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B737311 : Blo 654306 737311 := bstep (se 1 (by rfl) ⟨552983, by rfl⟩ : syracuseStep 737311 = 1105967) B1105967
theorem B737599 : Blo 654306 737599 := bstep (se 1 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 737599 = 1106399) B1106399
theorem B738175 : Blo 654306 738175 := bstep (se 1 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 738175 = 1107263) B1107263
theorem B738463 : Blo 654306 738463 := bstep (se 1 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 738463 = 1107695) B1107695
theorem B1657057 : Blo 654306 1657057 := bstep (se 2 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 1657057 = 1242793) B1242793
theorem B459165023 : Blo 654306 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B2216105 : Blo 654306 2216105 := bstep (se 2 (by rfl) ⟨831039, by rfl⟩ : syracuseStep 2216105 = 1662079) B1662079
theorem B40293247 : Blo 654306 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B1398313 : Blo 654306 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B291362345 : Blo 654306 291362345 := bstep (se 2 (by rfl) ⟨109260879, by rfl⟩ : syracuseStep 291362345 = 218521759) B218521759
theorem B1399835 : Blo 654306 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B14410007 : Blo 654306 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B3731615 : Blo 654306 3731615 := bstep (se 1 (by rfl) ⟨2798711, by rfl⟩ : syracuseStep 3731615 = 5597423) B5597423
theorem B85030559 : Blo 654306 85030559 := bstep (se 1 (by rfl) ⟨63772919, by rfl⟩ : syracuseStep 85030559 = 127545839) B127545839
theorem B2488745 : Blo 654306 2488745 := bstep (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) B1866559
theorem B6322859 : Blo 654306 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B654399 : Blo 654306 654399 := bstep (se 1 (by rfl) ⟨490799, by rfl⟩ : syracuseStep 654399 = 981599) B981599
theorem B983081 : Blo 654306 983081 := bstep (se 2 (by rfl) ⟨368655, by rfl⟩ : syracuseStep 983081 = 737311) B737311
theorem B983465 : Blo 654306 983465 := bstep (se 2 (by rfl) ⟨368799, by rfl⟩ : syracuseStep 983465 = 737599) B737599
theorem B656231 : Blo 654306 656231 := bstep (se 1 (by rfl) ⟨492173, by rfl⟩ : syracuseStep 656231 = 984347) B984347
theorem B984047 : Blo 654306 984047 := bstep (se 1 (by rfl) ⟨738035, by rfl⟩ : syracuseStep 984047 = 1476071) B1476071
theorem B984233 : Blo 654306 984233 := bstep (se 2 (by rfl) ⟨369087, by rfl⟩ : syracuseStep 984233 = 738175) B738175
theorem B4981985 : Blo 654306 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B984617 : Blo 654306 984617 := bstep (se 2 (by rfl) ⟨369231, by rfl⟩ : syracuseStep 984617 = 738463) B738463
theorem B984959 : Blo 654306 984959 := bstep (se 1 (by rfl) ⟨738719, by rfl⟩ : syracuseStep 984959 = 1477439) B1477439
theorem B1477403 : Blo 654306 1477403 := bstep (se 1 (by rfl) ⟨1108052, by rfl⟩ : syracuseStep 1477403 = 2216105) B2216105
theorem B658203 : Blo 654306 658203 := bstep (se 1 (by rfl) ⟨493652, by rfl⟩ : syracuseStep 658203 = 987305) B987305
theorem B985919 : Blo 654306 985919 := bstep (se 1 (by rfl) ⟨739439, by rfl⟩ : syracuseStep 985919 = 1478879) B1478879
theorem B2363575 : Blo 654306 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B9606671 : Blo 654306 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B8394799 : Blo 654306 8394799 := bstep (se 1 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 8394799 = 12592199) B12592199
theorem B2498633 : Blo 654306 2498633 := bstep (se 2 (by rfl) ⟨936987, by rfl⟩ : syracuseStep 2498633 = 1873975) B1873975
theorem B18884609 : Blo 654306 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B3320999 : Blo 654306 3320999 := bstep (se 1 (by rfl) ⟨2490749, by rfl⟩ : syracuseStep 3320999 = 4981499) B4981499
theorem B10269683 : Blo 654306 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B2209409 : Blo 654306 2209409 := bstep (se 2 (by rfl) ⟨828528, by rfl⟩ : syracuseStep 2209409 = 1657057) B1657057
theorem B933223 : Blo 654306 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B53724329 : Blo 654306 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B7456211 : Blo 654306 7456211 := bstep (se 1 (by rfl) ⟨5592158, by rfl⟩ : syracuseStep 7456211 = 11184317) B11184317
theorem B7457669 : Blo 654306 7457669 := bstep (se 4 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 7457669 = 1398313) B1398313
theorem B1659163 : Blo 654306 1659163 := bstep (se 1 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 1659163 = 2488745) B2488745
theorem B4215239 : Blo 654306 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B306110015 : Blo 654306 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B1663679 : Blo 654306 1663679 := bstep (se 1 (by rfl) ⟨1247759, by rfl⟩ : syracuseStep 1663679 = 2495519) B2495519
theorem B194241563 : Blo 654306 194241563 := bstep (se 1 (by rfl) ⟨145681172, by rfl⟩ : syracuseStep 194241563 = 291362345) B291362345
theorem B1664297 : Blo 654306 1664297 := bstep (se 2 (by rfl) ⟨624111, by rfl⟩ : syracuseStep 1664297 = 1248223) B1248223
theorem B99706697 : Blo 654306 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B17983883 : Blo 654306 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B2487743 : Blo 654306 2487743 := bstep (se 1 (by rfl) ⟨1865807, by rfl⟩ : syracuseStep 2487743 = 3731615) B3731615
theorem B56687039 : Blo 654306 56687039 := bstep (se 1 (by rfl) ⟨42515279, by rfl⟩ : syracuseStep 56687039 = 85030559) B85030559
theorem B1473839 : Blo 654306 1473839 := bstep (se 1 (by rfl) ⟨1105379, by rfl⟩ : syracuseStep 1473839 = 2210759) B2210759
theorem B1900201 : Blo 654306 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B655387 : Blo 654306 655387 := bstep (se 1 (by rfl) ⟨491540, by rfl⟩ : syracuseStep 655387 = 983081) B983081
theorem B655643 : Blo 654306 655643 := bstep (se 1 (by rfl) ⟨491732, by rfl⟩ : syracuseStep 655643 = 983465) B983465
theorem B656031 : Blo 654306 656031 := bstep (se 1 (by rfl) ⟨492023, by rfl⟩ : syracuseStep 656031 = 984047) B984047
theorem B35816219 : Blo 654306 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B656155 : Blo 654306 656155 := bstep (se 1 (by rfl) ⟨492116, by rfl⟩ : syracuseStep 656155 = 984233) B984233
theorem B656411 : Blo 654306 656411 := bstep (se 1 (by rfl) ⟨492308, by rfl⟩ : syracuseStep 656411 = 984617) B984617
theorem B656639 : Blo 654306 656639 := bstep (se 1 (by rfl) ⟨492479, by rfl⟩ : syracuseStep 656639 = 984959) B984959
theorem B984935 : Blo 654306 984935 := bstep (se 1 (by rfl) ⟨738701, by rfl⟩ : syracuseStep 984935 = 1477403) B1477403
theorem B657279 : Blo 654306 657279 := bstep (se 1 (by rfl) ⟨492959, by rfl⟩ : syracuseStep 657279 = 985919) B985919
theorem B3151433 : Blo 654306 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B12589739 : Blo 654306 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B37791359 : Blo 654306 37791359 := bstep (se 1 (by rfl) ⟨28343519, by rfl⟩ : syracuseStep 37791359 = 56687039) B56687039
theorem B2533601 : Blo 654306 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B3321323 : Blo 654306 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B6404447 : Blo 654306 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B2212217 : Blo 654306 2212217 := bstep (se 2 (by rfl) ⟨829581, by rfl⟩ : syracuseStep 2212217 = 1659163) B1659163
theorem B66471131 : Blo 654306 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B2213999 : Blo 654306 2213999 := bstep (se 1 (by rfl) ⟨1660499, by rfl⟩ : syracuseStep 2213999 = 3320999) B3320999
theorem B11193065 : Blo 654306 11193065 := bstep (se 2 (by rfl) ⟨4197399, by rfl⟩ : syracuseStep 11193065 = 8394799) B8394799
theorem B1658495 : Blo 654306 1658495 := bstep (se 1 (by rfl) ⟨1243871, by rfl⟩ : syracuseStep 1658495 = 2487743) B2487743
theorem B4970807 : Blo 654306 4970807 := bstep (se 1 (by rfl) ⟨3728105, by rfl⟩ : syracuseStep 4970807 = 7456211) B7456211
theorem B4971779 : Blo 654306 4971779 := bstep (se 1 (by rfl) ⟨3728834, by rfl⟩ : syracuseStep 4971779 = 7457669) B7457669
theorem B2810159 : Blo 654306 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B204073343 : Blo 654306 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B1665755 : Blo 654306 1665755 := bstep (se 1 (by rfl) ⟨1249316, by rfl⟩ : syracuseStep 1665755 = 2498633) B2498633
theorem B1109119 : Blo 654306 1109119 := bstep (se 1 (by rfl) ⟨831839, by rfl⟩ : syracuseStep 1109119 = 1663679) B1663679
theorem B129494375 : Blo 654306 129494375 := bstep (se 1 (by rfl) ⟨97120781, by rfl⟩ : syracuseStep 129494375 = 194241563) B194241563
theorem B1109531 : Blo 654306 1109531 := bstep (se 1 (by rfl) ⟨832148, by rfl⟩ : syracuseStep 1109531 = 1664297) B1664297
theorem B11989255 : Blo 654306 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B6846455 : Blo 654306 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B1472939 : Blo 654306 1472939 := bstep (se 1 (by rfl) ⟨1104704, by rfl⟩ : syracuseStep 1472939 = 2209409) B2209409
theorem B1244297 : Blo 654306 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B982559 : Blo 654306 982559 := bstep (se 1 (by rfl) ⟨736919, by rfl⟩ : syracuseStep 982559 = 1473839) B1473839
theorem B1474811 : Blo 654306 1474811 := bstep (se 1 (by rfl) ⟨1106108, by rfl⟩ : syracuseStep 1474811 = 2212217) B2212217
theorem B656623 : Blo 654306 656623 := bstep (se 1 (by rfl) ⟨492467, by rfl⟩ : syracuseStep 656623 = 984935) B984935
theorem B1475999 : Blo 654306 1475999 := bstep (se 1 (by rfl) ⟨1106999, by rfl⟩ : syracuseStep 1475999 = 2213999) B2213999
theorem B1478825 : Blo 654306 1478825 := bstep (se 2 (by rfl) ⟨554559, by rfl⟩ : syracuseStep 1478825 = 1109119) B1109119
theorem B3313871 : Blo 654306 3313871 := bstep (se 1 (by rfl) ⟨2485403, by rfl⟩ : syracuseStep 3313871 = 4970807) B4970807
theorem B8393159 : Blo 654306 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B3314519 : Blo 654306 3314519 := bstep (se 1 (by rfl) ⟨2485889, by rfl⟩ : syracuseStep 3314519 = 4971779) B4971779
theorem B18257213 : Blo 654306 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B1873439 : Blo 654306 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B17078525 : Blo 654306 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B829531 : Blo 654306 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B44314087 : Blo 654306 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B8403821 : Blo 654306 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B1689067 : Blo 654306 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B86329583 : Blo 654306 86329583 := bstep (se 1 (by rfl) ⟨64747187, by rfl⟩ : syracuseStep 86329583 = 129494375) B129494375
theorem B2214215 : Blo 654306 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B739687 : Blo 654306 739687 := bstep (se 1 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 739687 = 1109531) B1109531
theorem B23877479 : Blo 654306 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B7462043 : Blo 654306 7462043 := bstep (se 1 (by rfl) ⟨5596532, by rfl⟩ : syracuseStep 7462043 = 11193065) B11193065
theorem B1105663 : Blo 654306 1105663 := bstep (se 1 (by rfl) ⟨829247, by rfl⟩ : syracuseStep 1105663 = 1658495) B1658495
theorem B15985673 : Blo 654306 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B25194239 : Blo 654306 25194239 := bstep (se 1 (by rfl) ⟨18895679, by rfl⟩ : syracuseStep 25194239 = 37791359) B37791359
theorem B136048895 : Blo 654306 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B1110503 : Blo 654306 1110503 := bstep (se 1 (by rfl) ⟨832877, by rfl⟩ : syracuseStep 1110503 = 1665755) B1665755
theorem B981959 : Blo 654306 981959 := bstep (se 1 (by rfl) ⟨736469, by rfl⟩ : syracuseStep 981959 = 1472939) B1472939
theorem B655039 : Blo 654306 655039 := bstep (se 1 (by rfl) ⟨491279, by rfl⟩ : syracuseStep 655039 = 982559) B982559
theorem B983207 : Blo 654306 983207 := bstep (se 1 (by rfl) ⟨737405, by rfl⟩ : syracuseStep 983207 = 1474811) B1474811
theorem B983999 : Blo 654306 983999 := bstep (se 1 (by rfl) ⟨737999, by rfl⟩ : syracuseStep 983999 = 1475999) B1475999
theorem B1476143 : Blo 654306 1476143 := bstep (se 1 (by rfl) ⟨1107107, by rfl⟩ : syracuseStep 1476143 = 2214215) B2214215
theorem B985883 : Blo 654306 985883 := bstep (se 1 (by rfl) ⟨739412, by rfl⟩ : syracuseStep 985883 = 1478825) B1478825
theorem B986249 : Blo 654306 986249 := bstep (se 2 (by rfl) ⟨369843, by rfl⟩ : syracuseStep 986249 = 739687) B739687
theorem B1248959 : Blo 654306 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B59085449 : Blo 654306 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B10657115 : Blo 654306 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B57553055 : Blo 654306 57553055 := bstep (se 1 (by rfl) ⟨43164791, by rfl⟩ : syracuseStep 57553055 = 86329583) B86329583
theorem B2209247 : Blo 654306 2209247 := bstep (se 1 (by rfl) ⟨1656935, by rfl⟩ : syracuseStep 2209247 = 3313871) B3313871
theorem B2209679 : Blo 654306 2209679 := bstep (se 1 (by rfl) ⟨1657259, by rfl⟩ : syracuseStep 2209679 = 3314519) B3314519
theorem B12171475 : Blo 654306 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B11385683 : Blo 654306 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B16796159 : Blo 654306 16796159 := bstep (se 1 (by rfl) ⟨12597119, by rfl⟩ : syracuseStep 16796159 = 25194239) B25194239
theorem B740335 : Blo 654306 740335 := bstep (se 1 (by rfl) ⟨555251, by rfl⟩ : syracuseStep 740335 = 1110503) B1110503
theorem B2252089 : Blo 654306 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B1106041 : Blo 654306 1106041 := bstep (se 2 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 1106041 = 829531) B829531
theorem B5595439 : Blo 654306 5595439 := bstep (se 1 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 5595439 = 8393159) B8393159
theorem B15918319 : Blo 654306 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B4974695 : Blo 654306 4974695 := bstep (se 1 (by rfl) ⟨3731021, by rfl⟩ : syracuseStep 4974695 = 7462043) B7462043
theorem B90699263 : Blo 654306 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B5602547 : Blo 654306 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B654639 : Blo 654306 654639 := bstep (se 1 (by rfl) ⟨490979, by rfl⟩ : syracuseStep 654639 = 981959) B981959
theorem B1474217 : Blo 654306 1474217 := bstep (se 2 (by rfl) ⟨552831, by rfl⟩ : syracuseStep 1474217 = 1105663) B1105663
theorem B655471 : Blo 654306 655471 := bstep (se 1 (by rfl) ⟨491603, by rfl⟩ : syracuseStep 655471 = 983207) B983207
theorem B1474721 : Blo 654306 1474721 := bstep (se 2 (by rfl) ⟨553020, by rfl⟩ : syracuseStep 1474721 = 1106041) B1106041
theorem B655999 : Blo 654306 655999 := bstep (se 1 (by rfl) ⟨491999, by rfl⟩ : syracuseStep 655999 = 983999) B983999
theorem B984095 : Blo 654306 984095 := bstep (se 1 (by rfl) ⟨738071, by rfl⟩ : syracuseStep 984095 = 1476143) B1476143
theorem B64914533 : Blo 654306 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B657255 : Blo 654306 657255 := bstep (se 1 (by rfl) ⟨492941, by rfl⟩ : syracuseStep 657255 = 985883) B985883
theorem B657499 : Blo 654306 657499 := bstep (se 1 (by rfl) ⟨493124, by rfl⟩ : syracuseStep 657499 = 986249) B986249
theorem B39390299 : Blo 654306 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B987113 : Blo 654306 987113 := bstep (se 2 (by rfl) ⟨370167, by rfl⟩ : syracuseStep 987113 = 740335) B740335
theorem B3316463 : Blo 654306 3316463 := bstep (se 1 (by rfl) ⟨2487347, by rfl⟩ : syracuseStep 3316463 = 4974695) B4974695
theorem B60466175 : Blo 654306 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B12011141 : Blo 654306 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B3330557 : Blo 654306 3330557 := bstep (se 3 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 3330557 = 1248959) B1248959
theorem B7590455 : Blo 654306 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B7460585 : Blo 654306 7460585 := bstep (se 2 (by rfl) ⟨2797719, by rfl⟩ : syracuseStep 7460585 = 5595439) B5595439
theorem B21224425 : Blo 654306 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B11197439 : Blo 654306 11197439 := bstep (se 1 (by rfl) ⟨8398079, by rfl⟩ : syracuseStep 11197439 = 16796159) B16796159
theorem B7104743 : Blo 654306 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B38368703 : Blo 654306 38368703 := bstep (se 1 (by rfl) ⟨28776527, by rfl⟩ : syracuseStep 38368703 = 57553055) B57553055
theorem B1472831 : Blo 654306 1472831 := bstep (se 1 (by rfl) ⟨1104623, by rfl⟩ : syracuseStep 1472831 = 2209247) B2209247
theorem B1473119 : Blo 654306 1473119 := bstep (se 1 (by rfl) ⟨1104839, by rfl⟩ : syracuseStep 1473119 = 2209679) B2209679
theorem B3735031 : Blo 654306 3735031 := bstep (se 1 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 3735031 = 5602547) B5602547
theorem B982811 : Blo 654306 982811 := bstep (se 1 (by rfl) ⟨737108, by rfl⟩ : syracuseStep 982811 = 1474217) B1474217
theorem B983147 : Blo 654306 983147 := bstep (se 1 (by rfl) ⟨737360, by rfl⟩ : syracuseStep 983147 = 1474721) B1474721
theorem B656063 : Blo 654306 656063 := bstep (se 1 (by rfl) ⟨492047, by rfl⟩ : syracuseStep 656063 = 984095) B984095
theorem B658075 : Blo 654306 658075 := bstep (se 1 (by rfl) ⟨493556, by rfl⟩ : syracuseStep 658075 = 987113) B987113
theorem B40310783 : Blo 654306 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B8007427 : Blo 654306 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B26260199 : Blo 654306 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B5060303 : Blo 654306 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B2210975 : Blo 654306 2210975 := bstep (se 1 (by rfl) ⟨1658231, by rfl⟩ : syracuseStep 2210975 = 3316463) B3316463
theorem B4736495 : Blo 654306 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B25579135 : Blo 654306 25579135 := bstep (se 1 (by rfl) ⟨19184351, by rfl⟩ : syracuseStep 25579135 = 38368703) B38368703
theorem B28299233 : Blo 654306 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B43276355 : Blo 654306 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B2220371 : Blo 654306 2220371 := bstep (se 1 (by rfl) ⟨1665278, by rfl⟩ : syracuseStep 2220371 = 3330557) B3330557
theorem B4973723 : Blo 654306 4973723 := bstep (se 1 (by rfl) ⟨3730292, by rfl⟩ : syracuseStep 4973723 = 7460585) B7460585
theorem B7464959 : Blo 654306 7464959 := bstep (se 1 (by rfl) ⟨5598719, by rfl⟩ : syracuseStep 7464959 = 11197439) B11197439
theorem B981887 : Blo 654306 981887 := bstep (se 1 (by rfl) ⟨736415, by rfl⟩ : syracuseStep 981887 = 1472831) B1472831
theorem B982079 : Blo 654306 982079 := bstep (se 1 (by rfl) ⟨736559, by rfl⟩ : syracuseStep 982079 = 1473119) B1473119
theorem B4980041 : Blo 654306 4980041 := bstep (se 2 (by rfl) ⟨1867515, by rfl⟩ : syracuseStep 4980041 = 3735031) B3735031
theorem B655207 : Blo 654306 655207 := bstep (se 1 (by rfl) ⟨491405, by rfl⟩ : syracuseStep 655207 = 982811) B982811
theorem B655431 : Blo 654306 655431 := bstep (se 1 (by rfl) ⟨491573, by rfl⟩ : syracuseStep 655431 = 983147) B983147
theorem B26873855 : Blo 654306 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B1480247 : Blo 654306 1480247 := bstep (se 1 (by rfl) ⟨1110185, by rfl⟩ : syracuseStep 1480247 = 2220371) B2220371
theorem B3315815 : Blo 654306 3315815 := bstep (se 1 (by rfl) ⟨2486861, by rfl⟩ : syracuseStep 3315815 = 4973723) B4973723
theorem B17506799 : Blo 654306 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B136422053 : Blo 654306 136422053 := bstep (se 4 (by rfl) ⟨12789567, by rfl⟩ : syracuseStep 136422053 = 25579135) B25579135
theorem B3320027 : Blo 654306 3320027 := bstep (se 1 (by rfl) ⟨2490020, by rfl⟩ : syracuseStep 3320027 = 4980041) B4980041
theorem B3157663 : Blo 654306 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B28850903 : Blo 654306 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B18866155 : Blo 654306 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B10676569 : Blo 654306 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B4976639 : Blo 654306 4976639 := bstep (se 1 (by rfl) ⟨3732479, by rfl⟩ : syracuseStep 4976639 = 7464959) B7464959
theorem B3373535 : Blo 654306 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B654591 : Blo 654306 654591 := bstep (se 1 (by rfl) ⟨490943, by rfl⟩ : syracuseStep 654591 = 981887) B981887
theorem B654719 : Blo 654306 654719 := bstep (se 1 (by rfl) ⟨491039, by rfl⟩ : syracuseStep 654719 = 982079) B982079
theorem B1473983 : Blo 654306 1473983 := bstep (se 1 (by rfl) ⟨1105487, by rfl⟩ : syracuseStep 1473983 = 2210975) B2210975
theorem B986831 : Blo 654306 986831 := bstep (se 1 (by rfl) ⟨740123, by rfl⟩ : syracuseStep 986831 = 1480247) B1480247
theorem B11671199 : Blo 654306 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B3317759 : Blo 654306 3317759 := bstep (se 1 (by rfl) ⟨2488319, by rfl⟩ : syracuseStep 3317759 = 4976639) B4976639
theorem B14235425 : Blo 654306 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B2210543 : Blo 654306 2210543 := bstep (se 1 (by rfl) ⟨1657907, by rfl⟩ : syracuseStep 2210543 = 3315815) B3315815
theorem B4210217 : Blo 654306 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B90948035 : Blo 654306 90948035 := bstep (se 1 (by rfl) ⟨68211026, by rfl⟩ : syracuseStep 90948035 = 136422053) B136422053
theorem B8996093 : Blo 654306 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B2213351 : Blo 654306 2213351 := bstep (se 1 (by rfl) ⟨1660013, by rfl⟩ : syracuseStep 2213351 = 3320027) B3320027
theorem B25154873 : Blo 654306 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B17915903 : Blo 654306 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B19233935 : Blo 654306 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B982655 : Blo 654306 982655 := bstep (se 1 (by rfl) ⟨736991, by rfl⟩ : syracuseStep 982655 = 1473983) B1473983
theorem B5997395 : Blo 654306 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B1475567 : Blo 654306 1475567 := bstep (se 1 (by rfl) ⟨1106675, by rfl⟩ : syracuseStep 1475567 = 2213351) B2213351
theorem B657887 : Blo 654306 657887 := bstep (se 1 (by rfl) ⟨493415, by rfl⟩ : syracuseStep 657887 = 986831) B986831
theorem B12822623 : Blo 654306 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B60632023 : Blo 654306 60632023 := bstep (se 1 (by rfl) ⟨45474017, by rfl⟩ : syracuseStep 60632023 = 90948035) B90948035
theorem B7780799 : Blo 654306 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B2211839 : Blo 654306 2211839 := bstep (se 1 (by rfl) ⟨1658879, by rfl⟩ : syracuseStep 2211839 = 3317759) B3317759
theorem B11943935 : Blo 654306 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B9490283 : Blo 654306 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B2806811 : Blo 654306 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B16769915 : Blo 654306 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B1473695 : Blo 654306 1473695 := bstep (se 1 (by rfl) ⟨1105271, by rfl⟩ : syracuseStep 1473695 = 2210543) B2210543
theorem B655103 : Blo 654306 655103 := bstep (se 1 (by rfl) ⟨491327, by rfl⟩ : syracuseStep 655103 = 982655) B982655
theorem B983711 : Blo 654306 983711 := bstep (se 1 (by rfl) ⟨737783, by rfl⟩ : syracuseStep 983711 = 1475567) B1475567
theorem B15993053 : Blo 654306 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B6326855 : Blo 654306 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B1871207 : Blo 654306 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B80842697 : Blo 654306 80842697 := bstep (se 2 (by rfl) ⟨30316011, by rfl⟩ : syracuseStep 80842697 = 60632023) B60632023
theorem B11179943 : Blo 654306 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B5187199 : Blo 654306 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B1474559 : Blo 654306 1474559 := bstep (se 1 (by rfl) ⟨1105919, by rfl⟩ : syracuseStep 1474559 = 2211839) B2211839
theorem B7962623 : Blo 654306 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B8548415 : Blo 654306 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B982463 : Blo 654306 982463 := bstep (se 1 (by rfl) ⟨736847, by rfl⟩ : syracuseStep 982463 = 1473695) B1473695
theorem B655807 : Blo 654306 655807 := bstep (se 1 (by rfl) ⟨491855, by rfl⟩ : syracuseStep 655807 = 983711) B983711
theorem B6916265 : Blo 654306 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B1247471 : Blo 654306 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B10662035 : Blo 654306 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B7453295 : Blo 654306 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B4217903 : Blo 654306 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B53895131 : Blo 654306 53895131 := bstep (se 1 (by rfl) ⟨40421348, by rfl⟩ : syracuseStep 53895131 = 80842697) B80842697
theorem B5698943 : Blo 654306 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B983039 : Blo 654306 983039 := bstep (se 1 (by rfl) ⟨737279, by rfl⟩ : syracuseStep 983039 = 1474559) B1474559
theorem B654975 : Blo 654306 654975 := bstep (se 1 (by rfl) ⟨491231, by rfl⟩ : syracuseStep 654975 = 982463) B982463
theorem B5308415 : Blo 654306 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B3538943 : Blo 654306 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B831647 : Blo 654306 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B35930087 : Blo 654306 35930087 := bstep (se 1 (by rfl) ⟨26947565, by rfl⟩ : syracuseStep 35930087 = 53895131) B53895131
theorem B655359 : Blo 654306 655359 := bstep (se 1 (by rfl) ⟨491519, by rfl⟩ : syracuseStep 655359 = 983039) B983039
theorem B4968863 : Blo 654306 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B28432093 : Blo 654306 28432093 := bstep (se 3 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 28432093 = 10662035) B10662035
theorem B4610843 : Blo 654306 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B2811935 : Blo 654306 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B3799295 : Blo 654306 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B3312575 : Blo 654306 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B2359295 : Blo 654306 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B2532863 : Blo 654306 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B2217725 : Blo 654306 2217725 := bstep (se 3 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 2217725 = 831647) B831647
theorem B3073895 : Blo 654306 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B7498493 : Blo 654306 7498493 := bstep (se 3 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 7498493 = 2811935) B2811935
theorem B37909457 : Blo 654306 37909457 := bstep (se 2 (by rfl) ⟨14216046, by rfl⟩ : syracuseStep 37909457 = 28432093) B28432093
theorem B23953391 : Blo 654306 23953391 := bstep (se 1 (by rfl) ⟨17965043, by rfl⟩ : syracuseStep 23953391 = 35930087) B35930087
theorem B1478483 : Blo 654306 1478483 := bstep (se 1 (by rfl) ⟨1108862, by rfl⟩ : syracuseStep 1478483 = 2217725) B2217725
theorem B25272971 : Blo 654306 25272971 := bstep (se 1 (by rfl) ⟨18954728, by rfl⟩ : syracuseStep 25272971 = 37909457) B37909457
theorem B15968927 : Blo 654306 15968927 := bstep (se 1 (by rfl) ⟨11976695, by rfl⟩ : syracuseStep 15968927 = 23953391) B23953391
theorem B2208383 : Blo 654306 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B1572863 : Blo 654306 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B1688575 : Blo 654306 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B2049263 : Blo 654306 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B4998995 : Blo 654306 4998995 := bstep (se 1 (by rfl) ⟨3749246, by rfl⟩ : syracuseStep 4998995 = 7498493) B7498493
theorem B985655 : Blo 654306 985655 := bstep (se 1 (by rfl) ⟨739241, by rfl⟩ : syracuseStep 985655 = 1478483) B1478483
theorem B16848647 : Blo 654306 16848647 := bstep (se 1 (by rfl) ⟨12636485, by rfl⟩ : syracuseStep 16848647 = 25272971) B25272971
theorem B1366175 : Blo 654306 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B3332663 : Blo 654306 3332663 := bstep (se 1 (by rfl) ⟨2499497, by rfl⟩ : syracuseStep 3332663 = 4998995) B4998995
theorem B2251433 : Blo 654306 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B10645951 : Blo 654306 10645951 := bstep (se 1 (by rfl) ⟨7984463, by rfl⟩ : syracuseStep 10645951 = 15968927) B15968927
theorem B1472255 : Blo 654306 1472255 := bstep (se 1 (by rfl) ⟨1104191, by rfl⟩ : syracuseStep 1472255 = 2208383) B2208383
theorem B4194301 : Blo 654306 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B657103 : Blo 654306 657103 := bstep (se 1 (by rfl) ⟨492827, by rfl⟩ : syracuseStep 657103 = 985655) B985655
theorem B14194601 : Blo 654306 14194601 := bstep (se 2 (by rfl) ⟨5322975, by rfl⟩ : syracuseStep 14194601 = 10645951) B10645951
theorem B6003821 : Blo 654306 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B5592401 : Blo 654306 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B11232431 : Blo 654306 11232431 := bstep (se 1 (by rfl) ⟨8424323, by rfl⟩ : syracuseStep 11232431 = 16848647) B16848647
theorem B910783 : Blo 654306 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B2221775 : Blo 654306 2221775 := bstep (se 1 (by rfl) ⟨1666331, by rfl⟩ : syracuseStep 2221775 = 3332663) B3332663
theorem B981503 : Blo 654306 981503 := bstep (se 1 (by rfl) ⟨736127, by rfl⟩ : syracuseStep 981503 = 1472255) B1472255
theorem B4002547 : Blo 654306 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B1481183 : Blo 654306 1481183 := bstep (se 1 (by rfl) ⟨1110887, by rfl⟩ : syracuseStep 1481183 = 2221775) B2221775
theorem B4857509 : Blo 654306 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B7488287 : Blo 654306 7488287 := bstep (se 1 (by rfl) ⟨5616215, by rfl⟩ : syracuseStep 7488287 = 11232431) B11232431
theorem B3728267 : Blo 654306 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B9463067 : Blo 654306 9463067 := bstep (se 1 (by rfl) ⟨7097300, by rfl⟩ : syracuseStep 9463067 = 14194601) B14194601
theorem B654335 : Blo 654306 654335 := bstep (se 1 (by rfl) ⟨490751, by rfl⟩ : syracuseStep 654335 = 981503) B981503
theorem B987455 : Blo 654306 987455 := bstep (se 1 (by rfl) ⟨740591, by rfl⟩ : syracuseStep 987455 = 1481183) B1481183
theorem B4992191 : Blo 654306 4992191 := bstep (se 1 (by rfl) ⟨3744143, by rfl⟩ : syracuseStep 4992191 = 7488287) B7488287
theorem B6308711 : Blo 654306 6308711 := bstep (se 1 (by rfl) ⟨4731533, by rfl⟩ : syracuseStep 6308711 = 9463067) B9463067
theorem B3238339 : Blo 654306 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B2485511 : Blo 654306 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B5336729 : Blo 654306 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B658303 : Blo 654306 658303 := bstep (se 1 (by rfl) ⟨493727, by rfl⟩ : syracuseStep 658303 = 987455) B987455
theorem B4205807 : Blo 654306 4205807 := bstep (se 1 (by rfl) ⟨3154355, by rfl⟩ : syracuseStep 4205807 = 6308711) B6308711
theorem B3328127 : Blo 654306 3328127 := bstep (se 1 (by rfl) ⟨2496095, by rfl⟩ : syracuseStep 3328127 = 4992191) B4992191
theorem B1657007 : Blo 654306 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B3557819 : Blo 654306 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B4317785 : Blo 654306 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B2371879 : Blo 654306 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B2803871 : Blo 654306 2803871 := bstep (se 1 (by rfl) ⟨2102903, by rfl⟩ : syracuseStep 2803871 = 4205807) B4205807
theorem B2218751 : Blo 654306 2218751 := bstep (se 1 (by rfl) ⟨1664063, by rfl⟩ : syracuseStep 2218751 = 3328127) B3328127
theorem B1104671 : Blo 654306 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B2878523 : Blo 654306 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B1869247 : Blo 654306 1869247 := bstep (se 1 (by rfl) ⟨1401935, by rfl⟩ : syracuseStep 1869247 = 2803871) B2803871
theorem B1479167 : Blo 654306 1479167 := bstep (se 1 (by rfl) ⟨1109375, by rfl⟩ : syracuseStep 1479167 = 2218751) B2218751
theorem B736447 : Blo 654306 736447 := bstep (se 1 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 736447 = 1104671) B1104671
theorem B3162505 : Blo 654306 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B1919015 : Blo 654306 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B1279343 : Blo 654306 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B2492329 : Blo 654306 2492329 := bstep (se 2 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 2492329 = 1869247) B1869247
theorem B986111 : Blo 654306 986111 := bstep (se 1 (by rfl) ⟨739583, by rfl⟩ : syracuseStep 986111 = 1479167) B1479167
theorem B4216673 : Blo 654306 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B981929 : Blo 654306 981929 := bstep (se 2 (by rfl) ⟨368223, by rfl⟩ : syracuseStep 981929 = 736447) B736447
theorem B852895 : Blo 654306 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B657407 : Blo 654306 657407 := bstep (se 1 (by rfl) ⟨493055, by rfl⟩ : syracuseStep 657407 = 986111) B986111
theorem B3323105 : Blo 654306 3323105 := bstep (se 2 (by rfl) ⟨1246164, by rfl⟩ : syracuseStep 3323105 = 2492329) B2492329
theorem B2811115 : Blo 654306 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B654619 : Blo 654306 654619 := bstep (se 1 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 654619 = 981929) B981929
theorem B3748153 : Blo 654306 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B2215403 : Blo 654306 2215403 := bstep (se 1 (by rfl) ⟨1661552, by rfl⟩ : syracuseStep 2215403 = 3323105) B3323105
theorem B4548773 : Blo 654306 4548773 := bstep (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) B852895
theorem B1476935 : Blo 654306 1476935 := bstep (se 1 (by rfl) ⟨1107701, by rfl⟩ : syracuseStep 1476935 = 2215403) B2215403
theorem B4997537 : Blo 654306 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B3032515 : Blo 654306 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B984623 : Blo 654306 984623 := bstep (se 1 (by rfl) ⟨738467, by rfl⟩ : syracuseStep 984623 = 1476935) B1476935
theorem B4043353 : Blo 654306 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B3331691 : Blo 654306 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B656415 : Blo 654306 656415 := bstep (se 1 (by rfl) ⟨492311, by rfl⟩ : syracuseStep 656415 = 984623) B984623
theorem B5391137 : Blo 654306 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B2221127 : Blo 654306 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B1480751 : Blo 654306 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B3594091 : Blo 654306 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B987167 : Blo 654306 987167 := bstep (se 1 (by rfl) ⟨740375, by rfl⟩ : syracuseStep 987167 = 1480751) B1480751
theorem B4792121 : Blo 654306 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B658111 : Blo 654306 658111 := bstep (se 1 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 658111 = 987167) B987167
theorem B3194747 : Blo 654306 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2129831 : Blo 654306 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1419887 : Blo 654306 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B3786365 : Blo 654306 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B2524243 : Blo 654306 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B3365657 : Blo 654306 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B2243771 : Blo 654306 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1495847 : Blo 654306 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B997231 : Blo 654306 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B1329641 : Blo 654306 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B886427 : Blo 654306 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B9455221 : Blo 654306 9455221 := bstep (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) B886427
theorem B12606961 : Blo 654306 12606961 := bstep (se 2 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 12606961 = 9455221) B9455221
theorem B16809281 : Blo 654306 16809281 := bstep (se 2 (by rfl) ⟨6303480, by rfl⟩ : syracuseStep 16809281 = 12606961) B12606961
theorem B11206187 : Blo 654306 11206187 := bstep (se 1 (by rfl) ⟨8404640, by rfl⟩ : syracuseStep 11206187 = 16809281) B16809281
theorem B7470791 : Blo 654306 7470791 := bstep (se 1 (by rfl) ⟨5603093, by rfl⟩ : syracuseStep 7470791 = 11206187) B11206187
theorem B4980527 : Blo 654306 4980527 := bstep (se 1 (by rfl) ⟨3735395, by rfl⟩ : syracuseStep 4980527 = 7470791) B7470791
theorem B3320351 : Blo 654306 3320351 := bstep (se 1 (by rfl) ⟨2490263, by rfl⟩ : syracuseStep 3320351 = 4980527) B4980527
theorem B2213567 : Blo 654306 2213567 := bstep (se 1 (by rfl) ⟨1660175, by rfl⟩ : syracuseStep 2213567 = 3320351) B3320351
theorem B1475711 : Blo 654306 1475711 := bstep (se 1 (by rfl) ⟨1106783, by rfl⟩ : syracuseStep 1475711 = 2213567) B2213567
theorem B983807 : Blo 654306 983807 := bstep (se 1 (by rfl) ⟨737855, by rfl⟩ : syracuseStep 983807 = 1475711) B1475711
theorem B655871 : Blo 654306 655871 := bstep (se 1 (by rfl) ⟨491903, by rfl⟩ : syracuseStep 655871 = 983807) B983807

theorem C0 (j : ℕ) (h1 : 163576 ≤ j) (h2 : j ≤ 164275) : Blo 654306 (4 * j + 3) := by
  interval_cases j
  · exact B654307
  · exact B654311
  · exact B654315
  · exact B654319
  · exact B654323
  · exact B654327
  · exact B654331
  · exact B654335
  · exact B654339
  · exact B654343
  · exact B654347
  · exact B654351
  · exact B654355
  · exact B654359
  · exact B654363
  · exact B654367
  · exact B654371
  · exact B654375
  · exact B654379
  · exact B654383
  · exact B654387
  · exact B654391
  · exact B654395
  · exact B654399
  · exact B654403
  · exact B654407
  · exact B654411
  · exact B654415
  · exact B654419
  · exact B654423
  · exact B654427
  · exact B654431
  · exact B654435
  · exact B654439
  · exact B654443
  · exact B654447
  · exact B654451
  · exact B654455
  · exact B654459
  · exact B654463
  · exact B654467
  · exact B654471
  · exact B654475
  · exact B654479
  · exact B654483
  · exact B654487
  · exact B654491
  · exact B654495
  · exact B654499
  · exact B654503
  · exact B654507
  · exact B654511
  · exact B654515
  · exact B654519
  · exact B654523
  · exact B654527
  · exact B654531
  · exact B654535
  · exact B654539
  · exact B654543
  · exact B654547
  · exact B654551
  · exact B654555
  · exact B654559
  · exact B654563
  · exact B654567
  · exact B654571
  · exact B654575
  · exact B654579
  · exact B654583
  · exact B654587
  · exact B654591
  · exact B654595
  · exact B654599
  · exact B654603
  · exact B654607
  · exact B654611
  · exact B654615
  · exact B654619
  · exact B654623
  · exact B654627
  · exact B654631
  · exact B654635
  · exact B654639
  · exact B654643
  · exact B654647
  · exact B654651
  · exact B654655
  · exact B654659
  · exact B654663
  · exact B654667
  · exact B654671
  · exact B654675
  · exact B654679
  · exact B654683
  · exact B654687
  · exact B654691
  · exact B654695
  · exact B654699
  · exact B654703
  · exact B654707
  · exact B654711
  · exact B654715
  · exact B654719
  · exact B654723
  · exact B654727
  · exact B654731
  · exact B654735
  · exact B654739
  · exact B654743
  · exact B654747
  · exact B654751
  · exact B654755
  · exact B654759
  · exact B654763
  · exact B654767
  · exact B654771
  · exact B654775
  · exact B654779
  · exact B654783
  · exact B654787
  · exact B654791
  · exact B654795
  · exact B654799
  · exact B654803
  · exact B654807
  · exact B654811
  · exact B654815
  · exact B654819
  · exact B654823
  · exact B654827
  · exact B654831
  · exact B654835
  · exact B654839
  · exact B654843
  · exact B654847
  · exact B654851
  · exact B654855
  · exact B654859
  · exact B654863
  · exact B654867
  · exact B654871
  · exact B654875
  · exact B654879
  · exact B654883
  · exact B654887
  · exact B654891
  · exact B654895
  · exact B654899
  · exact B654903
  · exact B654907
  · exact B654911
  · exact B654915
  · exact B654919
  · exact B654923
  · exact B654927
  · exact B654931
  · exact B654935
  · exact B654939
  · exact B654943
  · exact B654947
  · exact B654951
  · exact B654955
  · exact B654959
  · exact B654963
  · exact B654967
  · exact B654971
  · exact B654975
  · exact B654979
  · exact B654983
  · exact B654987
  · exact B654991
  · exact B654995
  · exact B654999
  · exact B655003
  · exact B655007
  · exact B655011
  · exact B655015
  · exact B655019
  · exact B655023
  · exact B655027
  · exact B655031
  · exact B655035
  · exact B655039
  · exact B655043
  · exact B655047
  · exact B655051
  · exact B655055
  · exact B655059
  · exact B655063
  · exact B655067
  · exact B655071
  · exact B655075
  · exact B655079
  · exact B655083
  · exact B655087
  · exact B655091
  · exact B655095
  · exact B655099
  · exact B655103
  · exact B655107
  · exact B655111
  · exact B655115
  · exact B655119
  · exact B655123
  · exact B655127
  · exact B655131
  · exact B655135
  · exact B655139
  · exact B655143
  · exact B655147
  · exact B655151
  · exact B655155
  · exact B655159
  · exact B655163
  · exact B655167
  · exact B655171
  · exact B655175
  · exact B655179
  · exact B655183
  · exact B655187
  · exact B655191
  · exact B655195
  · exact B655199
  · exact B655203
  · exact B655207
  · exact B655211
  · exact B655215
  · exact B655219
  · exact B655223
  · exact B655227
  · exact B655231
  · exact B655235
  · exact B655239
  · exact B655243
  · exact B655247
  · exact B655251
  · exact B655255
  · exact B655259
  · exact B655263
  · exact B655267
  · exact B655271
  · exact B655275
  · exact B655279
  · exact B655283
  · exact B655287
  · exact B655291
  · exact B655295
  · exact B655299
  · exact B655303
  · exact B655307
  · exact B655311
  · exact B655315
  · exact B655319
  · exact B655323
  · exact B655327
  · exact B655331
  · exact B655335
  · exact B655339
  · exact B655343
  · exact B655347
  · exact B655351
  · exact B655355
  · exact B655359
  · exact B655363
  · exact B655367
  · exact B655371
  · exact B655375
  · exact B655379
  · exact B655383
  · exact B655387
  · exact B655391
  · exact B655395
  · exact B655399
  · exact B655403
  · exact B655407
  · exact B655411
  · exact B655415
  · exact B655419
  · exact B655423
  · exact B655427
  · exact B655431
  · exact B655435
  · exact B655439
  · exact B655443
  · exact B655447
  · exact B655451
  · exact B655455
  · exact B655459
  · exact B655463
  · exact B655467
  · exact B655471
  · exact B655475
  · exact B655479
  · exact B655483
  · exact B655487
  · exact B655491
  · exact B655495
  · exact B655499
  · exact B655503
  · exact B655507
  · exact B655511
  · exact B655515
  · exact B655519
  · exact B655523
  · exact B655527
  · exact B655531
  · exact B655535
  · exact B655539
  · exact B655543
  · exact B655547
  · exact B655551
  · exact B655555
  · exact B655559
  · exact B655563
  · exact B655567
  · exact B655571
  · exact B655575
  · exact B655579
  · exact B655583
  · exact B655587
  · exact B655591
  · exact B655595
  · exact B655599
  · exact B655603
  · exact B655607
  · exact B655611
  · exact B655615
  · exact B655619
  · exact B655623
  · exact B655627
  · exact B655631
  · exact B655635
  · exact B655639
  · exact B655643
  · exact B655647
  · exact B655651
  · exact B655655
  · exact B655659
  · exact B655663
  · exact B655667
  · exact B655671
  · exact B655675
  · exact B655679
  · exact B655683
  · exact B655687
  · exact B655691
  · exact B655695
  · exact B655699
  · exact B655703
  · exact B655707
  · exact B655711
  · exact B655715
  · exact B655719
  · exact B655723
  · exact B655727
  · exact B655731
  · exact B655735
  · exact B655739
  · exact B655743
  · exact B655747
  · exact B655751
  · exact B655755
  · exact B655759
  · exact B655763
  · exact B655767
  · exact B655771
  · exact B655775
  · exact B655779
  · exact B655783
  · exact B655787
  · exact B655791
  · exact B655795
  · exact B655799
  · exact B655803
  · exact B655807
  · exact B655811
  · exact B655815
  · exact B655819
  · exact B655823
  · exact B655827
  · exact B655831
  · exact B655835
  · exact B655839
  · exact B655843
  · exact B655847
  · exact B655851
  · exact B655855
  · exact B655859
  · exact B655863
  · exact B655867
  · exact B655871
  · exact B655875
  · exact B655879
  · exact B655883
  · exact B655887
  · exact B655891
  · exact B655895
  · exact B655899
  · exact B655903
  · exact B655907
  · exact B655911
  · exact B655915
  · exact B655919
  · exact B655923
  · exact B655927
  · exact B655931
  · exact B655935
  · exact B655939
  · exact B655943
  · exact B655947
  · exact B655951
  · exact B655955
  · exact B655959
  · exact B655963
  · exact B655967
  · exact B655971
  · exact B655975
  · exact B655979
  · exact B655983
  · exact B655987
  · exact B655991
  · exact B655995
  · exact B655999
  · exact B656003
  · exact B656007
  · exact B656011
  · exact B656015
  · exact B656019
  · exact B656023
  · exact B656027
  · exact B656031
  · exact B656035
  · exact B656039
  · exact B656043
  · exact B656047
  · exact B656051
  · exact B656055
  · exact B656059
  · exact B656063
  · exact B656067
  · exact B656071
  · exact B656075
  · exact B656079
  · exact B656083
  · exact B656087
  · exact B656091
  · exact B656095
  · exact B656099
  · exact B656103
  · exact B656107
  · exact B656111
  · exact B656115
  · exact B656119
  · exact B656123
  · exact B656127
  · exact B656131
  · exact B656135
  · exact B656139
  · exact B656143
  · exact B656147
  · exact B656151
  · exact B656155
  · exact B656159
  · exact B656163
  · exact B656167
  · exact B656171
  · exact B656175
  · exact B656179
  · exact B656183
  · exact B656187
  · exact B656191
  · exact B656195
  · exact B656199
  · exact B656203
  · exact B656207
  · exact B656211
  · exact B656215
  · exact B656219
  · exact B656223
  · exact B656227
  · exact B656231
  · exact B656235
  · exact B656239
  · exact B656243
  · exact B656247
  · exact B656251
  · exact B656255
  · exact B656259
  · exact B656263
  · exact B656267
  · exact B656271
  · exact B656275
  · exact B656279
  · exact B656283
  · exact B656287
  · exact B656291
  · exact B656295
  · exact B656299
  · exact B656303
  · exact B656307
  · exact B656311
  · exact B656315
  · exact B656319
  · exact B656323
  · exact B656327
  · exact B656331
  · exact B656335
  · exact B656339
  · exact B656343
  · exact B656347
  · exact B656351
  · exact B656355
  · exact B656359
  · exact B656363
  · exact B656367
  · exact B656371
  · exact B656375
  · exact B656379
  · exact B656383
  · exact B656387
  · exact B656391
  · exact B656395
  · exact B656399
  · exact B656403
  · exact B656407
  · exact B656411
  · exact B656415
  · exact B656419
  · exact B656423
  · exact B656427
  · exact B656431
  · exact B656435
  · exact B656439
  · exact B656443
  · exact B656447
  · exact B656451
  · exact B656455
  · exact B656459
  · exact B656463
  · exact B656467
  · exact B656471
  · exact B656475
  · exact B656479
  · exact B656483
  · exact B656487
  · exact B656491
  · exact B656495
  · exact B656499
  · exact B656503
  · exact B656507
  · exact B656511
  · exact B656515
  · exact B656519
  · exact B656523
  · exact B656527
  · exact B656531
  · exact B656535
  · exact B656539
  · exact B656543
  · exact B656547
  · exact B656551
  · exact B656555
  · exact B656559
  · exact B656563
  · exact B656567
  · exact B656571
  · exact B656575
  · exact B656579
  · exact B656583
  · exact B656587
  · exact B656591
  · exact B656595
  · exact B656599
  · exact B656603
  · exact B656607
  · exact B656611
  · exact B656615
  · exact B656619
  · exact B656623
  · exact B656627
  · exact B656631
  · exact B656635
  · exact B656639
  · exact B656643
  · exact B656647
  · exact B656651
  · exact B656655
  · exact B656659
  · exact B656663
  · exact B656667
  · exact B656671
  · exact B656675
  · exact B656679
  · exact B656683
  · exact B656687
  · exact B656691
  · exact B656695
  · exact B656699
  · exact B656703
  · exact B656707
  · exact B656711
  · exact B656715
  · exact B656719
  · exact B656723
  · exact B656727
  · exact B656731
  · exact B656735
  · exact B656739
  · exact B656743
  · exact B656747
  · exact B656751
  · exact B656755
  · exact B656759
  · exact B656763
  · exact B656767
  · exact B656771
  · exact B656775
  · exact B656779
  · exact B656783
  · exact B656787
  · exact B656791
  · exact B656795
  · exact B656799
  · exact B656803
  · exact B656807
  · exact B656811
  · exact B656815
  · exact B656819
  · exact B656823
  · exact B656827
  · exact B656831
  · exact B656835
  · exact B656839
  · exact B656843
  · exact B656847
  · exact B656851
  · exact B656855
  · exact B656859
  · exact B656863
  · exact B656867
  · exact B656871
  · exact B656875
  · exact B656879
  · exact B656883
  · exact B656887
  · exact B656891
  · exact B656895
  · exact B656899
  · exact B656903
  · exact B656907
  · exact B656911
  · exact B656915
  · exact B656919
  · exact B656923
  · exact B656927
  · exact B656931
  · exact B656935
  · exact B656939
  · exact B656943
  · exact B656947
  · exact B656951
  · exact B656955
  · exact B656959
  · exact B656963
  · exact B656967
  · exact B656971
  · exact B656975
  · exact B656979
  · exact B656983
  · exact B656987
  · exact B656991
  · exact B656995
  · exact B656999
  · exact B657003
  · exact B657007
  · exact B657011
  · exact B657015
  · exact B657019
  · exact B657023
  · exact B657027
  · exact B657031
  · exact B657035
  · exact B657039
  · exact B657043
  · exact B657047
  · exact B657051
  · exact B657055
  · exact B657059
  · exact B657063
  · exact B657067
  · exact B657071
  · exact B657075
  · exact B657079
  · exact B657083
  · exact B657087
  · exact B657091
  · exact B657095
  · exact B657099
  · exact B657103

theorem C1 (j : ℕ) (h1 : 164276 ≤ j) (h2 : j ≤ 164575) : Blo 654306 (4 * j + 3) := by
  interval_cases j
  · exact B657107
  · exact B657111
  · exact B657115
  · exact B657119
  · exact B657123
  · exact B657127
  · exact B657131
  · exact B657135
  · exact B657139
  · exact B657143
  · exact B657147
  · exact B657151
  · exact B657155
  · exact B657159
  · exact B657163
  · exact B657167
  · exact B657171
  · exact B657175
  · exact B657179
  · exact B657183
  · exact B657187
  · exact B657191
  · exact B657195
  · exact B657199
  · exact B657203
  · exact B657207
  · exact B657211
  · exact B657215
  · exact B657219
  · exact B657223
  · exact B657227
  · exact B657231
  · exact B657235
  · exact B657239
  · exact B657243
  · exact B657247
  · exact B657251
  · exact B657255
  · exact B657259
  · exact B657263
  · exact B657267
  · exact B657271
  · exact B657275
  · exact B657279
  · exact B657283
  · exact B657287
  · exact B657291
  · exact B657295
  · exact B657299
  · exact B657303
  · exact B657307
  · exact B657311
  · exact B657315
  · exact B657319
  · exact B657323
  · exact B657327
  · exact B657331
  · exact B657335
  · exact B657339
  · exact B657343
  · exact B657347
  · exact B657351
  · exact B657355
  · exact B657359
  · exact B657363
  · exact B657367
  · exact B657371
  · exact B657375
  · exact B657379
  · exact B657383
  · exact B657387
  · exact B657391
  · exact B657395
  · exact B657399
  · exact B657403
  · exact B657407
  · exact B657411
  · exact B657415
  · exact B657419
  · exact B657423
  · exact B657427
  · exact B657431
  · exact B657435
  · exact B657439
  · exact B657443
  · exact B657447
  · exact B657451
  · exact B657455
  · exact B657459
  · exact B657463
  · exact B657467
  · exact B657471
  · exact B657475
  · exact B657479
  · exact B657483
  · exact B657487
  · exact B657491
  · exact B657495
  · exact B657499
  · exact B657503
  · exact B657507
  · exact B657511
  · exact B657515
  · exact B657519
  · exact B657523
  · exact B657527
  · exact B657531
  · exact B657535
  · exact B657539
  · exact B657543
  · exact B657547
  · exact B657551
  · exact B657555
  · exact B657559
  · exact B657563
  · exact B657567
  · exact B657571
  · exact B657575
  · exact B657579
  · exact B657583
  · exact B657587
  · exact B657591
  · exact B657595
  · exact B657599
  · exact B657603
  · exact B657607
  · exact B657611
  · exact B657615
  · exact B657619
  · exact B657623
  · exact B657627
  · exact B657631
  · exact B657635
  · exact B657639
  · exact B657643
  · exact B657647
  · exact B657651
  · exact B657655
  · exact B657659
  · exact B657663
  · exact B657667
  · exact B657671
  · exact B657675
  · exact B657679
  · exact B657683
  · exact B657687
  · exact B657691
  · exact B657695
  · exact B657699
  · exact B657703
  · exact B657707
  · exact B657711
  · exact B657715
  · exact B657719
  · exact B657723
  · exact B657727
  · exact B657731
  · exact B657735
  · exact B657739
  · exact B657743
  · exact B657747
  · exact B657751
  · exact B657755
  · exact B657759
  · exact B657763
  · exact B657767
  · exact B657771
  · exact B657775
  · exact B657779
  · exact B657783
  · exact B657787
  · exact B657791
  · exact B657795
  · exact B657799
  · exact B657803
  · exact B657807
  · exact B657811
  · exact B657815
  · exact B657819
  · exact B657823
  · exact B657827
  · exact B657831
  · exact B657835
  · exact B657839
  · exact B657843
  · exact B657847
  · exact B657851
  · exact B657855
  · exact B657859
  · exact B657863
  · exact B657867
  · exact B657871
  · exact B657875
  · exact B657879
  · exact B657883
  · exact B657887
  · exact B657891
  · exact B657895
  · exact B657899
  · exact B657903
  · exact B657907
  · exact B657911
  · exact B657915
  · exact B657919
  · exact B657923
  · exact B657927
  · exact B657931
  · exact B657935
  · exact B657939
  · exact B657943
  · exact B657947
  · exact B657951
  · exact B657955
  · exact B657959
  · exact B657963
  · exact B657967
  · exact B657971
  · exact B657975
  · exact B657979
  · exact B657983
  · exact B657987
  · exact B657991
  · exact B657995
  · exact B657999
  · exact B658003
  · exact B658007
  · exact B658011
  · exact B658015
  · exact B658019
  · exact B658023
  · exact B658027
  · exact B658031
  · exact B658035
  · exact B658039
  · exact B658043
  · exact B658047
  · exact B658051
  · exact B658055
  · exact B658059
  · exact B658063
  · exact B658067
  · exact B658071
  · exact B658075
  · exact B658079
  · exact B658083
  · exact B658087
  · exact B658091
  · exact B658095
  · exact B658099
  · exact B658103
  · exact B658107
  · exact B658111
  · exact B658115
  · exact B658119
  · exact B658123
  · exact B658127
  · exact B658131
  · exact B658135
  · exact B658139
  · exact B658143
  · exact B658147
  · exact B658151
  · exact B658155
  · exact B658159
  · exact B658163
  · exact B658167
  · exact B658171
  · exact B658175
  · exact B658179
  · exact B658183
  · exact B658187
  · exact B658191
  · exact B658195
  · exact B658199
  · exact B658203
  · exact B658207
  · exact B658211
  · exact B658215
  · exact B658219
  · exact B658223
  · exact B658227
  · exact B658231
  · exact B658235
  · exact B658239
  · exact B658243
  · exact B658247
  · exact B658251
  · exact B658255
  · exact B658259
  · exact B658263
  · exact B658267
  · exact B658271
  · exact B658275
  · exact B658279
  · exact B658283
  · exact B658287
  · exact B658291
  · exact B658295
  · exact B658299
  · exact B658303

theorem solution (m : ℕ) (hlo : 654306 ≤ m) (hhi : m ≤ 658306) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 163576 ≤ j := by omega
    have hj2 : j ≤ 164575 := by omega
    have hb : Blo 654306 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 164276 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
