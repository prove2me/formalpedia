-- Prove2me | solution 1 for syracuse_descends_range_435777_439777
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:55.846273+00:00
-- url     : https://prove2.me/submissions/a680361a-29a4-470e-bfea-1970cb249dc9

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


theorem B491521 : Blo 435777 491521 := bbase (se 2 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 491521 = 368641) (by norm_num)
theorem B655373 : Blo 435777 655373 := bbase (se 3 (by rfl) ⟨122882, by rfl⟩ : syracuseStep 655373 = 245765) (by norm_num)
theorem B983069 : Blo 435777 983069 := bbase (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) (by norm_num)
theorem B655397 : Blo 435777 655397 := bbase (se 4 (by rfl) ⟨61443, by rfl⟩ : syracuseStep 655397 = 122887) (by norm_num)
theorem B491557 : Blo 435777 491557 := bbase (se 4 (by rfl) ⟨46083, by rfl⟩ : syracuseStep 491557 = 92167) (by norm_num)
theorem B1048621 : Blo 435777 1048621 := bbase (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) (by norm_num)
theorem B655421 : Blo 435777 655421 := bbase (se 3 (by rfl) ⟨122891, by rfl⟩ : syracuseStep 655421 = 245783) (by norm_num)
theorem B491593 : Blo 435777 491593 := bbase (se 2 (by rfl) ⟨184347, by rfl⟩ : syracuseStep 491593 = 368695) (by norm_num)
theorem B622669 : Blo 435777 622669 := bbase (se 3 (by rfl) ⟨116750, by rfl⟩ : syracuseStep 622669 = 233501) (by norm_num)
theorem B655445 : Blo 435777 655445 := bbase (se 8 (by rfl) ⟨3840, by rfl⟩ : syracuseStep 655445 = 7681) (by norm_num)
theorem B1245269 : Blo 435777 1245269 := bbase (se 8 (by rfl) ⟨7296, by rfl⟩ : syracuseStep 1245269 = 14593) (by norm_num)
theorem B983141 : Blo 435777 983141 := bbase (se 4 (by rfl) ⟨92169, by rfl⟩ : syracuseStep 983141 = 184339) (by norm_num)
theorem B655469 : Blo 435777 655469 := bbase (se 3 (by rfl) ⟨122900, by rfl⟩ : syracuseStep 655469 = 245801) (by norm_num)
theorem B491629 : Blo 435777 491629 := bbase (se 3 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 491629 = 184361) (by norm_num)
theorem B655493 : Blo 435777 655493 := bbase (se 4 (by rfl) ⟨61452, by rfl⟩ : syracuseStep 655493 = 122905) (by norm_num)
theorem B491665 : Blo 435777 491665 := bbase (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) (by norm_num)
theorem B655517 : Blo 435777 655517 := bbase (se 3 (by rfl) ⟨122909, by rfl⟩ : syracuseStep 655517 = 245819) (by norm_num)
theorem B983213 : Blo 435777 983213 := bbase (se 3 (by rfl) ⟨184352, by rfl⟩ : syracuseStep 983213 = 368705) (by norm_num)
theorem B655541 : Blo 435777 655541 := bbase (se 5 (by rfl) ⟨30728, by rfl⟩ : syracuseStep 655541 = 61457) (by norm_num)
theorem B491701 : Blo 435777 491701 := bbase (se 5 (by rfl) ⟨23048, by rfl⟩ : syracuseStep 491701 = 46097) (by norm_num)
theorem B655565 : Blo 435777 655565 := bbase (se 3 (by rfl) ⟨122918, by rfl⟩ : syracuseStep 655565 = 245837) (by norm_num)
theorem B7798997 : Blo 435777 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B491737 : Blo 435777 491737 := bbase (se 2 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 491737 = 368803) (by norm_num)
theorem B655589 : Blo 435777 655589 := bbase (se 4 (by rfl) ⟨61461, by rfl⟩ : syracuseStep 655589 = 122923) (by norm_num)
theorem B983285 : Blo 435777 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B655613 : Blo 435777 655613 := bbase (se 3 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 655613 = 245855) (by norm_num)
theorem B491773 : Blo 435777 491773 := bbase (se 3 (by rfl) ⟨92207, by rfl⟩ : syracuseStep 491773 = 184415) (by norm_num)
theorem B655637 : Blo 435777 655637 := bbase (se 6 (by rfl) ⟨15366, by rfl⟩ : syracuseStep 655637 = 30733) (by norm_num)
theorem B491809 : Blo 435777 491809 := bbase (se 2 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 491809 = 368857) (by norm_num)
theorem B622885 : Blo 435777 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B655661 : Blo 435777 655661 := bbase (se 3 (by rfl) ⟨122936, by rfl⟩ : syracuseStep 655661 = 245873) (by norm_num)
theorem B983357 : Blo 435777 983357 := bbase (se 3 (by rfl) ⟨184379, by rfl⟩ : syracuseStep 983357 = 368759) (by norm_num)
theorem B655685 : Blo 435777 655685 := bbase (se 4 (by rfl) ⟨61470, by rfl⟩ : syracuseStep 655685 = 122941) (by norm_num)
theorem B491845 : Blo 435777 491845 := bbase (se 4 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 491845 = 92221) (by norm_num)
theorem B2359637 : Blo 435777 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B1474901 : Blo 435777 1474901 := bbase (se 10 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 1474901 = 4321) (by norm_num)
theorem B590173 : Blo 435777 590173 := bbase (se 3 (by rfl) ⟨110657, by rfl⟩ : syracuseStep 590173 = 221315) (by norm_num)
theorem B655709 : Blo 435777 655709 := bbase (se 3 (by rfl) ⟨122945, by rfl⟩ : syracuseStep 655709 = 245891) (by norm_num)
theorem B491881 : Blo 435777 491881 := bbase (se 2 (by rfl) ⟨184455, by rfl⟩ : syracuseStep 491881 = 368911) (by norm_num)
theorem B655733 : Blo 435777 655733 := bbase (se 5 (by rfl) ⟨30737, by rfl⟩ : syracuseStep 655733 = 61475) (by norm_num)
theorem B983429 : Blo 435777 983429 := bbase (se 4 (by rfl) ⟨92196, by rfl⟩ : syracuseStep 983429 = 184393) (by norm_num)
theorem B655757 : Blo 435777 655757 := bbase (se 3 (by rfl) ⟨122954, by rfl⟩ : syracuseStep 655757 = 245909) (by norm_num)
theorem B491917 : Blo 435777 491917 := bbase (se 3 (by rfl) ⟨92234, by rfl⟩ : syracuseStep 491917 = 184469) (by norm_num)
theorem B655781 : Blo 435777 655781 := bbase (se 4 (by rfl) ⟨61479, by rfl⟩ : syracuseStep 655781 = 122959) (by norm_num)
theorem B491953 : Blo 435777 491953 := bbase (se 2 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 491953 = 368965) (by norm_num)
theorem B655805 : Blo 435777 655805 := bbase (se 3 (by rfl) ⟨122963, by rfl⟩ : syracuseStep 655805 = 245927) (by norm_num)
theorem B983501 : Blo 435777 983501 := bbase (se 3 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 983501 = 368813) (by norm_num)
theorem B655829 : Blo 435777 655829 := bbase (se 7 (by rfl) ⟨7685, by rfl⟩ : syracuseStep 655829 = 15371) (by norm_num)
theorem B491989 : Blo 435777 491989 := bbase (se 7 (by rfl) ⟨5765, by rfl⟩ : syracuseStep 491989 = 11531) (by norm_num)
theorem B655853 : Blo 435777 655853 := bbase (se 3 (by rfl) ⟨122972, by rfl⟩ : syracuseStep 655853 = 245945) (by norm_num)
theorem B492025 : Blo 435777 492025 := bbase (se 2 (by rfl) ⟨184509, by rfl⟩ : syracuseStep 492025 = 369019) (by norm_num)
theorem B655877 : Blo 435777 655877 := bbase (se 4 (by rfl) ⟨61488, by rfl⟩ : syracuseStep 655877 = 122977) (by norm_num)
theorem B983573 : Blo 435777 983573 := bbase (se 6 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 983573 = 46105) (by norm_num)
theorem B655901 : Blo 435777 655901 := bbase (se 3 (by rfl) ⟨122981, by rfl⟩ : syracuseStep 655901 = 245963) (by norm_num)
theorem B492061 : Blo 435777 492061 := bbase (se 3 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 492061 = 184523) (by norm_num)
theorem B655925 : Blo 435777 655925 := bbase (se 5 (by rfl) ⟨30746, by rfl⟩ : syracuseStep 655925 = 61493) (by norm_num)
theorem B492097 : Blo 435777 492097 := bbase (se 2 (by rfl) ⟨184536, by rfl⟩ : syracuseStep 492097 = 369073) (by norm_num)
theorem B655949 : Blo 435777 655949 := bbase (se 3 (by rfl) ⟨122990, by rfl⟩ : syracuseStep 655949 = 245981) (by norm_num)
theorem B983645 : Blo 435777 983645 := bbase (se 3 (by rfl) ⟨184433, by rfl⟩ : syracuseStep 983645 = 368867) (by norm_num)
theorem B655973 : Blo 435777 655973 := bbase (se 4 (by rfl) ⟨61497, by rfl⟩ : syracuseStep 655973 = 122995) (by norm_num)
theorem B492133 : Blo 435777 492133 := bbase (se 4 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 492133 = 92275) (by norm_num)
theorem B655997 : Blo 435777 655997 := bbase (se 3 (by rfl) ⟨122999, by rfl⟩ : syracuseStep 655997 = 245999) (by norm_num)
theorem B492169 : Blo 435777 492169 := bbase (se 2 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 492169 = 369127) (by norm_num)
theorem B1049237 : Blo 435777 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B656021 : Blo 435777 656021 := bbase (se 6 (by rfl) ⟨15375, by rfl⟩ : syracuseStep 656021 = 30751) (by norm_num)
theorem B623261 : Blo 435777 623261 := bbase (se 3 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 623261 = 233723) (by norm_num)
theorem B983717 : Blo 435777 983717 := bbase (se 4 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 983717 = 184447) (by norm_num)
theorem B656045 : Blo 435777 656045 := bbase (se 3 (by rfl) ⟨123008, by rfl⟩ : syracuseStep 656045 = 246017) (by norm_num)
theorem B492205 : Blo 435777 492205 := bbase (se 3 (by rfl) ⟨92288, by rfl⟩ : syracuseStep 492205 = 184577) (by norm_num)
theorem B656069 : Blo 435777 656069 := bbase (se 4 (by rfl) ⟨61506, by rfl⟩ : syracuseStep 656069 = 123013) (by norm_num)
theorem B492241 : Blo 435777 492241 := bbase (se 2 (by rfl) ⟨184590, by rfl⟩ : syracuseStep 492241 = 369181) (by norm_num)
theorem B6292181 : Blo 435777 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B656093 : Blo 435777 656093 := bbase (se 3 (by rfl) ⟨123017, by rfl⟩ : syracuseStep 656093 = 246035) (by norm_num)
theorem B983789 : Blo 435777 983789 := bbase (se 3 (by rfl) ⟨184460, by rfl⟩ : syracuseStep 983789 = 368921) (by norm_num)
theorem B656117 : Blo 435777 656117 := bbase (se 5 (by rfl) ⟨30755, by rfl⟩ : syracuseStep 656117 = 61511) (by norm_num)
theorem B492277 : Blo 435777 492277 := bbase (se 5 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 492277 = 46151) (by norm_num)
theorem B1475333 : Blo 435777 1475333 := bbase (se 4 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 1475333 = 276625) (by norm_num)
theorem B656141 : Blo 435777 656141 := bbase (se 3 (by rfl) ⟨123026, by rfl⟩ : syracuseStep 656141 = 246053) (by norm_num)
theorem B492313 : Blo 435777 492313 := bbase (se 2 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 492313 = 369235) (by norm_num)
theorem B656165 : Blo 435777 656165 := bbase (se 4 (by rfl) ⟨61515, by rfl⟩ : syracuseStep 656165 = 123031) (by norm_num)
theorem B983861 : Blo 435777 983861 := bbase (se 5 (by rfl) ⟨46118, by rfl⟩ : syracuseStep 983861 = 92237) (by norm_num)
theorem B656189 : Blo 435777 656189 := bbase (se 3 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 656189 = 246071) (by norm_num)
theorem B492349 : Blo 435777 492349 := bbase (se 3 (by rfl) ⟨92315, by rfl⟩ : syracuseStep 492349 = 184631) (by norm_num)
theorem B656213 : Blo 435777 656213 := bbase (se 9 (by rfl) ⟨1922, by rfl⟩ : syracuseStep 656213 = 3845) (by norm_num)
theorem B492385 : Blo 435777 492385 := bbase (se 2 (by rfl) ⟨184644, by rfl⟩ : syracuseStep 492385 = 369289) (by norm_num)
theorem B656237 : Blo 435777 656237 := bbase (se 3 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 656237 = 246089) (by norm_num)
theorem B983933 : Blo 435777 983933 := bbase (se 3 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 983933 = 368975) (by norm_num)
theorem B656261 : Blo 435777 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B492421 : Blo 435777 492421 := bbase (se 4 (by rfl) ⟨46164, by rfl⟩ : syracuseStep 492421 = 92329) (by norm_num)
theorem B656285 : Blo 435777 656285 := bbase (se 3 (by rfl) ⟨123053, by rfl⟩ : syracuseStep 656285 = 246107) (by norm_num)
theorem B492457 : Blo 435777 492457 := bbase (se 2 (by rfl) ⟨184671, by rfl⟩ : syracuseStep 492457 = 369343) (by norm_num)
theorem B656309 : Blo 435777 656309 := bbase (se 5 (by rfl) ⟨30764, by rfl⟩ : syracuseStep 656309 = 61529) (by norm_num)
theorem B984005 : Blo 435777 984005 := bbase (se 4 (by rfl) ⟨92250, by rfl⟩ : syracuseStep 984005 = 184501) (by norm_num)
theorem B656333 : Blo 435777 656333 := bbase (se 3 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 656333 = 246125) (by norm_num)
theorem B492493 : Blo 435777 492493 := bbase (se 3 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 492493 = 184685) (by norm_num)
theorem B1049573 : Blo 435777 1049573 := bbase (se 4 (by rfl) ⟨98397, by rfl⟩ : syracuseStep 1049573 = 196795) (by norm_num)
theorem B656357 : Blo 435777 656357 := bbase (se 4 (by rfl) ⟨61533, by rfl⟩ : syracuseStep 656357 = 123067) (by norm_num)
theorem B492529 : Blo 435777 492529 := bbase (se 2 (by rfl) ⟨184698, by rfl⟩ : syracuseStep 492529 = 369397) (by norm_num)
theorem B656381 : Blo 435777 656381 := bbase (se 3 (by rfl) ⟨123071, by rfl⟩ : syracuseStep 656381 = 246143) (by norm_num)
theorem B984077 : Blo 435777 984077 := bbase (se 3 (by rfl) ⟨184514, by rfl⟩ : syracuseStep 984077 = 369029) (by norm_num)
theorem B656405 : Blo 435777 656405 := bbase (se 6 (by rfl) ⟨15384, by rfl⟩ : syracuseStep 656405 = 30769) (by norm_num)
theorem B492565 : Blo 435777 492565 := bbase (se 6 (by rfl) ⟨11544, by rfl⟩ : syracuseStep 492565 = 23089) (by norm_num)
theorem B656429 : Blo 435777 656429 := bbase (se 3 (by rfl) ⟨123080, by rfl⟩ : syracuseStep 656429 = 246161) (by norm_num)
theorem B492601 : Blo 435777 492601 := bbase (se 2 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 492601 = 369451) (by norm_num)
theorem B787525 : Blo 435777 787525 := bbase (se 4 (by rfl) ⟨73830, by rfl⟩ : syracuseStep 787525 = 147661) (by norm_num)
theorem B656453 : Blo 435777 656453 := bbase (se 4 (by rfl) ⟨61542, by rfl⟩ : syracuseStep 656453 = 123085) (by norm_num)
theorem B984149 : Blo 435777 984149 := bbase (se 8 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 984149 = 11533) (by norm_num)
theorem B656477 : Blo 435777 656477 := bbase (se 3 (by rfl) ⟨123089, by rfl⟩ : syracuseStep 656477 = 246179) (by norm_num)
theorem B492637 : Blo 435777 492637 := bbase (se 3 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 492637 = 184739) (by norm_num)
theorem B525425 : Blo 435777 525425 := bbase (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) (by norm_num)
theorem B656501 : Blo 435777 656501 := bbase (se 5 (by rfl) ⟨30773, by rfl⟩ : syracuseStep 656501 = 61547) (by norm_num)
theorem B492673 : Blo 435777 492673 := bbase (se 2 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 492673 = 369505) (by norm_num)
theorem B656525 : Blo 435777 656525 := bbase (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) (by norm_num)
theorem B6325397 : Blo 435777 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B984221 : Blo 435777 984221 := bbase (se 3 (by rfl) ⟨184541, by rfl⟩ : syracuseStep 984221 = 369083) (by norm_num)
theorem B656549 : Blo 435777 656549 := bbase (se 4 (by rfl) ⟨61551, by rfl⟩ : syracuseStep 656549 = 123103) (by norm_num)
theorem B492709 : Blo 435777 492709 := bbase (se 4 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 492709 = 92383) (by norm_num)
theorem B1475765 : Blo 435777 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B656573 : Blo 435777 656573 := bbase (se 3 (by rfl) ⟨123107, by rfl⟩ : syracuseStep 656573 = 246215) (by norm_num)
theorem B492745 : Blo 435777 492745 := bbase (se 2 (by rfl) ⟨184779, by rfl⟩ : syracuseStep 492745 = 369559) (by norm_num)
theorem B525521 : Blo 435777 525521 := bbase (se 2 (by rfl) ⟨197070, by rfl⟩ : syracuseStep 525521 = 394141) (by norm_num)
theorem B656597 : Blo 435777 656597 := bbase (se 7 (by rfl) ⟨7694, by rfl⟩ : syracuseStep 656597 = 15389) (by norm_num)
theorem B591077 : Blo 435777 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B525541 : Blo 435777 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B984293 : Blo 435777 984293 := bbase (se 4 (by rfl) ⟨92277, by rfl⟩ : syracuseStep 984293 = 184555) (by norm_num)
theorem B656621 : Blo 435777 656621 := bbase (se 3 (by rfl) ⟨123116, by rfl⟩ : syracuseStep 656621 = 246233) (by norm_num)
theorem B492781 : Blo 435777 492781 := bbase (se 3 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 492781 = 184793) (by norm_num)
theorem B656645 : Blo 435777 656645 := bbase (se 4 (by rfl) ⟨61560, by rfl⟩ : syracuseStep 656645 = 123121) (by norm_num)
theorem B492817 : Blo 435777 492817 := bbase (se 2 (by rfl) ⟨184806, by rfl⟩ : syracuseStep 492817 = 369613) (by norm_num)
theorem B656669 : Blo 435777 656669 := bbase (se 3 (by rfl) ⟨123125, by rfl⟩ : syracuseStep 656669 = 246251) (by norm_num)
theorem B984365 : Blo 435777 984365 := bbase (se 3 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 984365 = 369137) (by norm_num)
theorem B4195637 : Blo 435777 4195637 := bbase (se 5 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 4195637 = 393341) (by norm_num)
theorem B656693 : Blo 435777 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B492853 : Blo 435777 492853 := bbase (se 5 (by rfl) ⟨23102, by rfl⟩ : syracuseStep 492853 = 46205) (by norm_num)
theorem B656717 : Blo 435777 656717 := bbase (se 3 (by rfl) ⟨123134, by rfl⟩ : syracuseStep 656717 = 246269) (by norm_num)
theorem B492889 : Blo 435777 492889 := bbase (se 2 (by rfl) ⟨184833, by rfl⟩ : syracuseStep 492889 = 369667) (by norm_num)
theorem B656741 : Blo 435777 656741 := bbase (se 4 (by rfl) ⟨61569, by rfl⟩ : syracuseStep 656741 = 123139) (by norm_num)
theorem B1049965 : Blo 435777 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B984437 : Blo 435777 984437 := bbase (se 5 (by rfl) ⟨46145, by rfl⟩ : syracuseStep 984437 = 92291) (by norm_num)
theorem B525685 : Blo 435777 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B656765 : Blo 435777 656765 := bbase (se 3 (by rfl) ⟨123143, by rfl⟩ : syracuseStep 656765 = 246287) (by norm_num)
theorem B492925 : Blo 435777 492925 := bbase (se 3 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 492925 = 184847) (by norm_num)
theorem B656789 : Blo 435777 656789 := bbase (se 6 (by rfl) ⟨15393, by rfl⟩ : syracuseStep 656789 = 30787) (by norm_num)
theorem B492961 : Blo 435777 492961 := bbase (se 2 (by rfl) ⟨184860, by rfl⟩ : syracuseStep 492961 = 369721) (by norm_num)
theorem B656813 : Blo 435777 656813 := bbase (se 3 (by rfl) ⟨123152, by rfl⟩ : syracuseStep 656813 = 246305) (by norm_num)
theorem B984509 : Blo 435777 984509 := bbase (se 3 (by rfl) ⟨184595, by rfl⟩ : syracuseStep 984509 = 369191) (by norm_num)
theorem B656837 : Blo 435777 656837 := bbase (se 4 (by rfl) ⟨61578, by rfl⟩ : syracuseStep 656837 = 123157) (by norm_num)
theorem B492997 : Blo 435777 492997 := bbase (se 4 (by rfl) ⟨46218, by rfl⟩ : syracuseStep 492997 = 92437) (by norm_num)
theorem B656861 : Blo 435777 656861 := bbase (se 3 (by rfl) ⟨123161, by rfl⟩ : syracuseStep 656861 = 246323) (by norm_num)
theorem B493033 : Blo 435777 493033 := bbase (se 2 (by rfl) ⟨184887, by rfl⟩ : syracuseStep 493033 = 369775) (by norm_num)
theorem B656885 : Blo 435777 656885 := bbase (se 5 (by rfl) ⟨30791, by rfl⟩ : syracuseStep 656885 = 61583) (by norm_num)
theorem B984581 : Blo 435777 984581 := bbase (se 4 (by rfl) ⟨92304, by rfl⟩ : syracuseStep 984581 = 184609) (by norm_num)
theorem B656909 : Blo 435777 656909 := bbase (se 3 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 656909 = 246341) (by norm_num)
theorem B493069 : Blo 435777 493069 := bbase (se 3 (by rfl) ⟨92450, by rfl⟩ : syracuseStep 493069 = 184901) (by norm_num)
theorem B656933 : Blo 435777 656933 := bbase (se 4 (by rfl) ⟨61587, by rfl⟩ : syracuseStep 656933 = 123175) (by norm_num)
theorem B493105 : Blo 435777 493105 := bbase (se 2 (by rfl) ⟨184914, by rfl⟩ : syracuseStep 493105 = 369829) (by norm_num)
theorem B656957 : Blo 435777 656957 := bbase (se 3 (by rfl) ⟨123179, by rfl⟩ : syracuseStep 656957 = 246359) (by norm_num)
theorem B984653 : Blo 435777 984653 := bbase (se 3 (by rfl) ⟨184622, by rfl⟩ : syracuseStep 984653 = 369245) (by norm_num)
theorem B656981 : Blo 435777 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B493141 : Blo 435777 493141 := bbase (se 8 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 493141 = 5779) (by norm_num)
theorem B1476197 : Blo 435777 1476197 := bbase (se 4 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 1476197 = 276787) (by norm_num)
theorem B657005 : Blo 435777 657005 := bbase (se 3 (by rfl) ⟨123188, by rfl⟩ : syracuseStep 657005 = 246377) (by norm_num)
theorem B493177 : Blo 435777 493177 := bbase (se 2 (by rfl) ⟨184941, by rfl⟩ : syracuseStep 493177 = 369883) (by norm_num)
theorem B1246853 : Blo 435777 1246853 := bbase (se 4 (by rfl) ⟨116892, by rfl⟩ : syracuseStep 1246853 = 233785) (by norm_num)
theorem B657029 : Blo 435777 657029 := bbase (se 4 (by rfl) ⟨61596, by rfl⟩ : syracuseStep 657029 = 123193) (by norm_num)
theorem B984725 : Blo 435777 984725 := bbase (se 6 (by rfl) ⟨23079, by rfl⟩ : syracuseStep 984725 = 46159) (by norm_num)
theorem B657053 : Blo 435777 657053 := bbase (se 3 (by rfl) ⟨123197, by rfl⟩ : syracuseStep 657053 = 246395) (by norm_num)
theorem B493213 : Blo 435777 493213 := bbase (se 3 (by rfl) ⟨92477, by rfl⟩ : syracuseStep 493213 = 184955) (by norm_num)
theorem B657077 : Blo 435777 657077 := bbase (se 5 (by rfl) ⟨30800, by rfl⟩ : syracuseStep 657077 = 61601) (by norm_num)
theorem B493249 : Blo 435777 493249 := bbase (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) (by norm_num)
theorem B591557 : Blo 435777 591557 := bbase (se 4 (by rfl) ⟨55458, by rfl⟩ : syracuseStep 591557 = 110917) (by norm_num)
theorem B657101 : Blo 435777 657101 := bbase (se 3 (by rfl) ⟨123206, by rfl⟩ : syracuseStep 657101 = 246413) (by norm_num)
theorem B886493 : Blo 435777 886493 := bbase (se 3 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 886493 = 332435) (by norm_num)
theorem B984797 : Blo 435777 984797 := bbase (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) (by norm_num)
theorem B657125 : Blo 435777 657125 := bbase (se 4 (by rfl) ⟨61605, by rfl⟩ : syracuseStep 657125 = 123211) (by norm_num)
theorem B493285 : Blo 435777 493285 := bbase (se 4 (by rfl) ⟨46245, by rfl⟩ : syracuseStep 493285 = 92491) (by norm_num)
theorem B657149 : Blo 435777 657149 := bbase (se 3 (by rfl) ⟨123215, by rfl⟩ : syracuseStep 657149 = 246431) (by norm_num)
theorem B493321 : Blo 435777 493321 := bbase (se 2 (by rfl) ⟨184995, by rfl⟩ : syracuseStep 493321 = 369991) (by norm_num)
theorem B657173 : Blo 435777 657173 := bbase (se 6 (by rfl) ⟨15402, by rfl⟩ : syracuseStep 657173 = 30805) (by norm_num)
theorem B984869 : Blo 435777 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B657197 : Blo 435777 657197 := bbase (se 3 (by rfl) ⟨123224, by rfl⟩ : syracuseStep 657197 = 246449) (by norm_num)
theorem B493357 : Blo 435777 493357 := bbase (se 3 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 493357 = 185009) (by norm_num)
theorem B657221 : Blo 435777 657221 := bbase (se 4 (by rfl) ⟨61614, by rfl⟩ : syracuseStep 657221 = 123229) (by norm_num)
theorem B493393 : Blo 435777 493393 := bbase (se 2 (by rfl) ⟨185022, by rfl⟩ : syracuseStep 493393 = 370045) (by norm_num)
theorem B9471829 : Blo 435777 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B591709 : Blo 435777 591709 := bbase (se 3 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 591709 = 221891) (by norm_num)
theorem B657245 : Blo 435777 657245 := bbase (se 3 (by rfl) ⟨123233, by rfl⟩ : syracuseStep 657245 = 246467) (by norm_num)
theorem B984941 : Blo 435777 984941 := bbase (se 3 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 984941 = 369353) (by norm_num)
theorem B1181557 : Blo 435777 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B657269 : Blo 435777 657269 := bbase (se 5 (by rfl) ⟨30809, by rfl⟩ : syracuseStep 657269 = 61619) (by norm_num)
theorem B493429 : Blo 435777 493429 := bbase (se 5 (by rfl) ⟨23129, by rfl⟩ : syracuseStep 493429 = 46259) (by norm_num)
theorem B657293 : Blo 435777 657293 := bbase (se 3 (by rfl) ⟨123242, by rfl⟩ : syracuseStep 657293 = 246485) (by norm_num)
theorem B493465 : Blo 435777 493465 := bbase (se 2 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 493465 = 370099) (by norm_num)
theorem B1771429 : Blo 435777 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B657317 : Blo 435777 657317 := bbase (se 4 (by rfl) ⟨61623, by rfl⟩ : syracuseStep 657317 = 123247) (by norm_num)
theorem B1869749 : Blo 435777 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B985013 : Blo 435777 985013 := bbase (se 5 (by rfl) ⟨46172, by rfl⟩ : syracuseStep 985013 = 92345) (by norm_num)
theorem B657341 : Blo 435777 657341 := bbase (se 3 (by rfl) ⟨123251, by rfl⟩ : syracuseStep 657341 = 246503) (by norm_num)
theorem B493501 : Blo 435777 493501 := bbase (se 3 (by rfl) ⟨92531, by rfl⟩ : syracuseStep 493501 = 185063) (by norm_num)
theorem B657365 : Blo 435777 657365 := bbase (se 7 (by rfl) ⟨7703, by rfl⟩ : syracuseStep 657365 = 15407) (by norm_num)
theorem B493537 : Blo 435777 493537 := bbase (se 2 (by rfl) ⟨185076, by rfl⟩ : syracuseStep 493537 = 370153) (by norm_num)
theorem B657389 : Blo 435777 657389 := bbase (se 3 (by rfl) ⟨123260, by rfl⟩ : syracuseStep 657389 = 246521) (by norm_num)
theorem B985085 : Blo 435777 985085 := bbase (se 3 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 985085 = 369407) (by norm_num)
theorem B657413 : Blo 435777 657413 := bbase (se 4 (by rfl) ⟨61632, by rfl⟩ : syracuseStep 657413 = 123265) (by norm_num)
theorem B493573 : Blo 435777 493573 := bbase (se 4 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 493573 = 92545) (by norm_num)
theorem B1476629 : Blo 435777 1476629 := bbase (se 6 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 1476629 = 69217) (by norm_num)
theorem B657437 : Blo 435777 657437 := bbase (se 3 (by rfl) ⟨123269, by rfl⟩ : syracuseStep 657437 = 246539) (by norm_num)
theorem B493609 : Blo 435777 493609 := bbase (se 2 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 493609 = 370207) (by norm_num)
theorem B624685 : Blo 435777 624685 := bbase (se 3 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 624685 = 234257) (by norm_num)
theorem B657461 : Blo 435777 657461 := bbase (se 5 (by rfl) ⟨30818, by rfl⟩ : syracuseStep 657461 = 61637) (by norm_num)
theorem B985157 : Blo 435777 985157 := bbase (se 4 (by rfl) ⟨92358, by rfl⟩ : syracuseStep 985157 = 184717) (by norm_num)
theorem B657485 : Blo 435777 657485 := bbase (se 3 (by rfl) ⟨123278, by rfl⟩ : syracuseStep 657485 = 246557) (by norm_num)
theorem B493645 : Blo 435777 493645 := bbase (se 3 (by rfl) ⟨92558, by rfl⟩ : syracuseStep 493645 = 185117) (by norm_num)
theorem B657509 : Blo 435777 657509 := bbase (se 4 (by rfl) ⟨61641, by rfl⟩ : syracuseStep 657509 = 123283) (by norm_num)
theorem B493681 : Blo 435777 493681 := bbase (se 2 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 493681 = 370261) (by norm_num)
theorem B657533 : Blo 435777 657533 := bbase (se 3 (by rfl) ⟨123287, by rfl⟩ : syracuseStep 657533 = 246575) (by norm_num)
theorem B985229 : Blo 435777 985229 := bbase (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) (by norm_num)
theorem B657557 : Blo 435777 657557 := bbase (se 6 (by rfl) ⟨15411, by rfl⟩ : syracuseStep 657557 = 30823) (by norm_num)
theorem B493717 : Blo 435777 493717 := bbase (se 6 (by rfl) ⟨11571, by rfl⟩ : syracuseStep 493717 = 23143) (by norm_num)
theorem B1181861 : Blo 435777 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B657581 : Blo 435777 657581 := bbase (se 3 (by rfl) ⟨123296, by rfl⟩ : syracuseStep 657581 = 246593) (by norm_num)
theorem B493753 : Blo 435777 493753 := bbase (se 2 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 493753 = 370315) (by norm_num)
theorem B657605 : Blo 435777 657605 := bbase (se 4 (by rfl) ⟨61650, by rfl⟩ : syracuseStep 657605 = 123301) (by norm_num)
theorem B985301 : Blo 435777 985301 := bbase (se 7 (by rfl) ⟨11546, by rfl⟩ : syracuseStep 985301 = 23093) (by norm_num)
theorem B657629 : Blo 435777 657629 := bbase (se 3 (by rfl) ⟨123305, by rfl⟩ : syracuseStep 657629 = 246611) (by norm_num)
theorem B493789 : Blo 435777 493789 := bbase (se 3 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 493789 = 185171) (by norm_num)
theorem B657653 : Blo 435777 657653 := bbase (se 5 (by rfl) ⟨30827, by rfl⟩ : syracuseStep 657653 = 61655) (by norm_num)
theorem B493825 : Blo 435777 493825 := bbase (se 2 (by rfl) ⟨185184, by rfl⟩ : syracuseStep 493825 = 370369) (by norm_num)
theorem B657677 : Blo 435777 657677 := bbase (se 3 (by rfl) ⟨123314, by rfl⟩ : syracuseStep 657677 = 246629) (by norm_num)
theorem B985373 : Blo 435777 985373 := bbase (se 3 (by rfl) ⟨184757, by rfl⟩ : syracuseStep 985373 = 369515) (by norm_num)
theorem B788773 : Blo 435777 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B1247525 : Blo 435777 1247525 := bbase (se 4 (by rfl) ⟨116955, by rfl⟩ : syracuseStep 1247525 = 233911) (by norm_num)
theorem B657701 : Blo 435777 657701 := bbase (se 4 (by rfl) ⟨61659, by rfl⟩ : syracuseStep 657701 = 123319) (by norm_num)
theorem B493861 : Blo 435777 493861 := bbase (se 4 (by rfl) ⟨46299, by rfl⟩ : syracuseStep 493861 = 92599) (by norm_num)
theorem B657725 : Blo 435777 657725 := bbase (se 3 (by rfl) ⟨123323, by rfl⟩ : syracuseStep 657725 = 246647) (by norm_num)
theorem B493897 : Blo 435777 493897 := bbase (se 2 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 493897 = 370423) (by norm_num)
theorem B559445 : Blo 435777 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B657749 : Blo 435777 657749 := bbase (se 10 (by rfl) ⟨963, by rfl⟩ : syracuseStep 657749 = 1927) (by norm_num)
theorem B985445 : Blo 435777 985445 := bbase (se 4 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 985445 = 184771) (by norm_num)
theorem B657773 : Blo 435777 657773 := bbase (se 3 (by rfl) ⟨123332, by rfl⟩ : syracuseStep 657773 = 246665) (by norm_num)
theorem B493933 : Blo 435777 493933 := bbase (se 3 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 493933 = 185225) (by norm_num)
theorem B657797 : Blo 435777 657797 := bbase (se 4 (by rfl) ⟨61668, by rfl⟩ : syracuseStep 657797 = 123337) (by norm_num)
theorem B493969 : Blo 435777 493969 := bbase (se 2 (by rfl) ⟨185238, by rfl⟩ : syracuseStep 493969 = 370477) (by norm_num)
theorem B657821 : Blo 435777 657821 := bbase (se 3 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 657821 = 246683) (by norm_num)
theorem B985517 : Blo 435777 985517 := bbase (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) (by norm_num)
theorem B657845 : Blo 435777 657845 := bbase (se 5 (by rfl) ⟨30836, by rfl⟩ : syracuseStep 657845 = 61673) (by norm_num)
theorem B494005 : Blo 435777 494005 := bbase (se 5 (by rfl) ⟨23156, by rfl⟩ : syracuseStep 494005 = 46313) (by norm_num)
theorem B1477061 : Blo 435777 1477061 := bbase (se 4 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 1477061 = 276949) (by norm_num)
theorem B657869 : Blo 435777 657869 := bbase (se 3 (by rfl) ⟨123350, by rfl⟩ : syracuseStep 657869 = 246701) (by norm_num)
theorem B494041 : Blo 435777 494041 := bbase (se 2 (by rfl) ⟨185265, by rfl⟩ : syracuseStep 494041 = 370531) (by norm_num)
theorem B657893 : Blo 435777 657893 := bbase (se 4 (by rfl) ⟨61677, by rfl⟩ : syracuseStep 657893 = 123355) (by norm_num)
theorem B985589 : Blo 435777 985589 := bbase (se 5 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 985589 = 92399) (by norm_num)
theorem B657917 : Blo 435777 657917 := bbase (se 3 (by rfl) ⟨123359, by rfl⟩ : syracuseStep 657917 = 246719) (by norm_num)
theorem B494077 : Blo 435777 494077 := bbase (se 3 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 494077 = 185279) (by norm_num)
theorem B657941 : Blo 435777 657941 := bbase (se 6 (by rfl) ⟨15420, by rfl⟩ : syracuseStep 657941 = 30841) (by norm_num)
theorem B494113 : Blo 435777 494113 := bbase (se 2 (by rfl) ⟨185292, by rfl⟩ : syracuseStep 494113 = 370585) (by norm_num)
theorem B657965 : Blo 435777 657965 := bbase (se 3 (by rfl) ⟨123368, by rfl⟩ : syracuseStep 657965 = 246737) (by norm_num)
theorem B985661 : Blo 435777 985661 := bbase (se 3 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 985661 = 369623) (by norm_num)
theorem B789061 : Blo 435777 789061 := bbase (se 4 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 789061 = 147949) (by norm_num)
theorem B657989 : Blo 435777 657989 := bbase (se 4 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 657989 = 123373) (by norm_num)
theorem B494149 : Blo 435777 494149 := bbase (se 4 (by rfl) ⟨46326, by rfl⟩ : syracuseStep 494149 = 92653) (by norm_num)
theorem B658013 : Blo 435777 658013 := bbase (se 3 (by rfl) ⟨123377, by rfl⟩ : syracuseStep 658013 = 246755) (by norm_num)
theorem B494185 : Blo 435777 494185 := bbase (se 2 (by rfl) ⟨185319, by rfl⟩ : syracuseStep 494185 = 370639) (by norm_num)
theorem B658037 : Blo 435777 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B625277 : Blo 435777 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B1575557 : Blo 435777 1575557 := bbase (se 4 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 1575557 = 295417) (by norm_num)
theorem B985733 : Blo 435777 985733 := bbase (se 4 (by rfl) ⟨92412, by rfl⟩ : syracuseStep 985733 = 184825) (by norm_num)
theorem B658061 : Blo 435777 658061 := bbase (se 3 (by rfl) ⟨123386, by rfl⟩ : syracuseStep 658061 = 246773) (by norm_num)
theorem B494221 : Blo 435777 494221 := bbase (se 3 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 494221 = 185333) (by norm_num)
theorem B658085 : Blo 435777 658085 := bbase (se 4 (by rfl) ⟨61695, by rfl⟩ : syracuseStep 658085 = 123391) (by norm_num)
theorem B494257 : Blo 435777 494257 := bbase (se 2 (by rfl) ⟨185346, by rfl⟩ : syracuseStep 494257 = 370693) (by norm_num)
theorem B658109 : Blo 435777 658109 := bbase (se 3 (by rfl) ⟨123395, by rfl⟩ : syracuseStep 658109 = 246791) (by norm_num)
theorem B985805 : Blo 435777 985805 := bbase (se 3 (by rfl) ⟨184838, by rfl⟩ : syracuseStep 985805 = 369677) (by norm_num)
theorem B625357 : Blo 435777 625357 := bbase (se 3 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 625357 = 234509) (by norm_num)
theorem B1247957 : Blo 435777 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B658133 : Blo 435777 658133 := bbase (se 7 (by rfl) ⟨7712, by rfl⟩ : syracuseStep 658133 = 15425) (by norm_num)
theorem B494293 : Blo 435777 494293 := bbase (se 7 (by rfl) ⟨5792, by rfl⟩ : syracuseStep 494293 = 11585) (by norm_num)
theorem B658157 : Blo 435777 658157 := bbase (se 3 (by rfl) ⟨123404, by rfl⟩ : syracuseStep 658157 = 246809) (by norm_num)
theorem B494329 : Blo 435777 494329 := bbase (se 2 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 494329 = 370747) (by norm_num)
theorem B658181 : Blo 435777 658181 := bbase (se 4 (by rfl) ⟨61704, by rfl⟩ : syracuseStep 658181 = 123409) (by norm_num)
theorem B985877 : Blo 435777 985877 := bbase (se 6 (by rfl) ⟨23106, by rfl⟩ : syracuseStep 985877 = 46213) (by norm_num)
theorem B789277 : Blo 435777 789277 := bbase (se 3 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 789277 = 295979) (by norm_num)
theorem B658205 : Blo 435777 658205 := bbase (se 3 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 658205 = 246827) (by norm_num)
theorem B494365 : Blo 435777 494365 := bbase (se 3 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 494365 = 185387) (by norm_num)
theorem B658229 : Blo 435777 658229 := bbase (se 5 (by rfl) ⟨30854, by rfl⟩ : syracuseStep 658229 = 61709) (by norm_num)
theorem B494401 : Blo 435777 494401 := bbase (se 2 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 494401 = 370801) (by norm_num)
theorem B625477 : Blo 435777 625477 := bbase (se 4 (by rfl) ⟨58638, by rfl⟩ : syracuseStep 625477 = 117277) (by norm_num)
theorem B658253 : Blo 435777 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B985949 : Blo 435777 985949 := bbase (se 3 (by rfl) ⟨184865, by rfl⟩ : syracuseStep 985949 = 369731) (by norm_num)
theorem B658277 : Blo 435777 658277 := bbase (se 4 (by rfl) ⟨61713, by rfl⟩ : syracuseStep 658277 = 123427) (by norm_num)
theorem B494437 : Blo 435777 494437 := bbase (se 4 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 494437 = 92707) (by norm_num)
theorem B1477493 : Blo 435777 1477493 := bbase (se 5 (by rfl) ⟨69257, by rfl⟩ : syracuseStep 1477493 = 138515) (by norm_num)
theorem B658301 : Blo 435777 658301 := bbase (se 3 (by rfl) ⟨123431, by rfl⟩ : syracuseStep 658301 = 246863) (by norm_num)
theorem B494473 : Blo 435777 494473 := bbase (se 2 (by rfl) ⟨185427, by rfl⟩ : syracuseStep 494473 = 370855) (by norm_num)
theorem B658325 : Blo 435777 658325 := bbase (se 6 (by rfl) ⟨15429, by rfl⟩ : syracuseStep 658325 = 30859) (by norm_num)
theorem B986021 : Blo 435777 986021 := bbase (se 4 (by rfl) ⟨92439, by rfl⟩ : syracuseStep 986021 = 184879) (by norm_num)
theorem B625573 : Blo 435777 625573 := bbase (se 4 (by rfl) ⟨58647, by rfl⟩ : syracuseStep 625573 = 117295) (by norm_num)
theorem B658349 : Blo 435777 658349 := bbase (se 3 (by rfl) ⟨123440, by rfl⟩ : syracuseStep 658349 = 246881) (by norm_num)
theorem B494509 : Blo 435777 494509 := bbase (se 3 (by rfl) ⟨92720, by rfl⟩ : syracuseStep 494509 = 185441) (by norm_num)
theorem B658373 : Blo 435777 658373 := bbase (se 4 (by rfl) ⟨61722, by rfl⟩ : syracuseStep 658373 = 123445) (by norm_num)
theorem B494545 : Blo 435777 494545 := bbase (se 2 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 494545 = 370909) (by norm_num)
theorem B658397 : Blo 435777 658397 := bbase (se 3 (by rfl) ⟨123449, by rfl⟩ : syracuseStep 658397 = 246899) (by norm_num)
theorem B986093 : Blo 435777 986093 := bbase (se 3 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 986093 = 369785) (by norm_num)
theorem B658421 : Blo 435777 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B494581 : Blo 435777 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B658445 : Blo 435777 658445 := bbase (se 3 (by rfl) ⟨123458, by rfl⟩ : syracuseStep 658445 = 246917) (by norm_num)
theorem B494617 : Blo 435777 494617 := bbase (se 2 (by rfl) ⟨185481, by rfl⟩ : syracuseStep 494617 = 370963) (by norm_num)
theorem B1575973 : Blo 435777 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B658469 : Blo 435777 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B986165 : Blo 435777 986165 := bbase (se 5 (by rfl) ⟨46226, by rfl⟩ : syracuseStep 986165 = 92453) (by norm_num)
theorem B756797 : Blo 435777 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B658493 : Blo 435777 658493 := bbase (se 3 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 658493 = 246935) (by norm_num)
theorem B494653 : Blo 435777 494653 := bbase (se 3 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 494653 = 185495) (by norm_num)
theorem B658517 : Blo 435777 658517 := bbase (se 8 (by rfl) ⟨3858, by rfl⟩ : syracuseStep 658517 = 7717) (by norm_num)
theorem B494689 : Blo 435777 494689 := bbase (se 2 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 494689 = 371017) (by norm_num)
theorem B658541 : Blo 435777 658541 := bbase (se 3 (by rfl) ⟨123476, by rfl⟩ : syracuseStep 658541 = 246953) (by norm_num)
theorem B527477 : Blo 435777 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B986237 : Blo 435777 986237 := bbase (se 3 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 986237 = 369839) (by norm_num)
theorem B658565 : Blo 435777 658565 := bbase (se 4 (by rfl) ⟨61740, by rfl⟩ : syracuseStep 658565 = 123481) (by norm_num)
theorem B494725 : Blo 435777 494725 := bbase (se 4 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 494725 = 92761) (by norm_num)
theorem B658589 : Blo 435777 658589 := bbase (se 3 (by rfl) ⟨123485, by rfl⟩ : syracuseStep 658589 = 246971) (by norm_num)
theorem B658613 : Blo 435777 658613 := bbase (se 5 (by rfl) ⟨30872, by rfl⟩ : syracuseStep 658613 = 61745) (by norm_num)
theorem B986309 : Blo 435777 986309 := bbase (se 4 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 986309 = 184933) (by norm_num)
theorem B593093 : Blo 435777 593093 := bbase (se 4 (by rfl) ⟨55602, by rfl⟩ : syracuseStep 593093 = 111205) (by norm_num)
theorem B658637 : Blo 435777 658637 := bbase (se 3 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 658637 = 246989) (by norm_num)
theorem B658661 : Blo 435777 658661 := bbase (se 4 (by rfl) ⟨61749, by rfl⟩ : syracuseStep 658661 = 123499) (by norm_num)
theorem B658685 : Blo 435777 658685 := bbase (se 3 (by rfl) ⟨123503, by rfl⟩ : syracuseStep 658685 = 247007) (by norm_num)
theorem B986381 : Blo 435777 986381 := bbase (se 3 (by rfl) ⟨184946, by rfl⟩ : syracuseStep 986381 = 369893) (by norm_num)
theorem B658709 : Blo 435777 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B1477925 : Blo 435777 1477925 := bbase (se 4 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 1477925 = 277111) (by norm_num)
theorem B658733 : Blo 435777 658733 := bbase (se 3 (by rfl) ⟨123512, by rfl⟩ : syracuseStep 658733 = 247025) (by norm_num)
theorem B658757 : Blo 435777 658757 := bbase (se 4 (by rfl) ⟨61758, by rfl⟩ : syracuseStep 658757 = 123517) (by norm_num)
theorem B986453 : Blo 435777 986453 := bbase (se 11 (by rfl) ⟨722, by rfl⟩ : syracuseStep 986453 = 1445) (by norm_num)
theorem B658781 : Blo 435777 658781 := bbase (se 3 (by rfl) ⟨123521, by rfl⟩ : syracuseStep 658781 = 247043) (by norm_num)
theorem B888173 : Blo 435777 888173 := bbase (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) (by norm_num)
theorem B658805 : Blo 435777 658805 := bbase (se 5 (by rfl) ⟨30881, by rfl⟩ : syracuseStep 658805 = 61763) (by norm_num)
theorem B658829 : Blo 435777 658829 := bbase (se 3 (by rfl) ⟨123530, by rfl⟩ : syracuseStep 658829 = 247061) (by norm_num)
theorem B626069 : Blo 435777 626069 := bbase (se 6 (by rfl) ⟨14673, by rfl⟩ : syracuseStep 626069 = 29347) (by norm_num)
theorem B986525 : Blo 435777 986525 := bbase (se 3 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 986525 = 369947) (by norm_num)
theorem B658853 : Blo 435777 658853 := bbase (se 4 (by rfl) ⟨61767, by rfl⟩ : syracuseStep 658853 = 123535) (by norm_num)
theorem B658877 : Blo 435777 658877 := bbase (se 3 (by rfl) ⟨123539, by rfl⟩ : syracuseStep 658877 = 247079) (by norm_num)
theorem B527809 : Blo 435777 527809 := bbase (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) (by norm_num)
theorem B1248709 : Blo 435777 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B658901 : Blo 435777 658901 := bbase (se 7 (by rfl) ⟨7721, by rfl⟩ : syracuseStep 658901 = 15443) (by norm_num)
theorem B855517 : Blo 435777 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B986597 : Blo 435777 986597 := bbase (se 4 (by rfl) ⟨92493, by rfl⟩ : syracuseStep 986597 = 184987) (by norm_num)
theorem B658925 : Blo 435777 658925 := bbase (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) (by norm_num)
theorem B658949 : Blo 435777 658949 := bbase (se 4 (by rfl) ⟨61776, by rfl⟩ : syracuseStep 658949 = 123553) (by norm_num)
theorem B658973 : Blo 435777 658973 := bbase (se 3 (by rfl) ⟨123557, by rfl⟩ : syracuseStep 658973 = 247115) (by norm_num)
theorem B986669 : Blo 435777 986669 := bbase (se 3 (by rfl) ⟨185000, by rfl⟩ : syracuseStep 986669 = 370001) (by norm_num)
theorem B658997 : Blo 435777 658997 := bbase (se 5 (by rfl) ⟨30890, by rfl⟩ : syracuseStep 658997 = 61781) (by norm_num)
theorem B659021 : Blo 435777 659021 := bbase (se 3 (by rfl) ⟨123566, by rfl⟩ : syracuseStep 659021 = 247133) (by norm_num)
theorem B527953 : Blo 435777 527953 := bbase (se 2 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 527953 = 395965) (by norm_num)
theorem B659045 : Blo 435777 659045 := bbase (se 4 (by rfl) ⟨61785, by rfl⟩ : syracuseStep 659045 = 123571) (by norm_num)
theorem B2100853 : Blo 435777 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B986741 : Blo 435777 986741 := bbase (se 5 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 986741 = 92507) (by norm_num)
theorem B659069 : Blo 435777 659069 := bbase (se 3 (by rfl) ⟨123575, by rfl⟩ : syracuseStep 659069 = 247151) (by norm_num)
theorem B790157 : Blo 435777 790157 := bbase (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) (by norm_num)
theorem B659093 : Blo 435777 659093 := bbase (se 6 (by rfl) ⟨15447, by rfl⟩ : syracuseStep 659093 = 30895) (by norm_num)
theorem B1871525 : Blo 435777 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B1085093 : Blo 435777 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B659117 : Blo 435777 659117 := bbase (se 3 (by rfl) ⟨123584, by rfl⟩ : syracuseStep 659117 = 247169) (by norm_num)
theorem B986813 : Blo 435777 986813 := bbase (se 3 (by rfl) ⟨185027, by rfl⟩ : syracuseStep 986813 = 370055) (by norm_num)
theorem B659141 : Blo 435777 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B1478357 : Blo 435777 1478357 := bbase (se 7 (by rfl) ⟨17324, by rfl⟩ : syracuseStep 1478357 = 34649) (by norm_num)
theorem B659165 : Blo 435777 659165 := bbase (se 3 (by rfl) ⟨123593, by rfl⟩ : syracuseStep 659165 = 247187) (by norm_num)
theorem B1347317 : Blo 435777 1347317 := bbase (se 5 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 1347317 = 126311) (by norm_num)
theorem B659189 : Blo 435777 659189 := bbase (se 5 (by rfl) ⟨30899, by rfl⟩ : syracuseStep 659189 = 61799) (by norm_num)
theorem B1576709 : Blo 435777 1576709 := bbase (se 4 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 1576709 = 295633) (by norm_num)
theorem B986885 : Blo 435777 986885 := bbase (se 4 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 986885 = 185041) (by norm_num)
theorem B593677 : Blo 435777 593677 := bbase (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) (by norm_num)
theorem B659213 : Blo 435777 659213 := bbase (se 3 (by rfl) ⟨123602, by rfl⟩ : syracuseStep 659213 = 247205) (by norm_num)
theorem B659237 : Blo 435777 659237 := bbase (se 4 (by rfl) ⟨61803, by rfl⟩ : syracuseStep 659237 = 123607) (by norm_num)
theorem B659261 : Blo 435777 659261 := bbase (se 3 (by rfl) ⟨123611, by rfl⟩ : syracuseStep 659261 = 247223) (by norm_num)
theorem B986957 : Blo 435777 986957 := bbase (se 3 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 986957 = 370109) (by norm_num)
theorem B659285 : Blo 435777 659285 := bbase (se 9 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 659285 = 3863) (by norm_num)
theorem B790373 : Blo 435777 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B659309 : Blo 435777 659309 := bbase (se 3 (by rfl) ⟨123620, by rfl⟩ : syracuseStep 659309 = 247241) (by norm_num)
theorem B659333 : Blo 435777 659333 := bbase (se 4 (by rfl) ⟨61812, by rfl⟩ : syracuseStep 659333 = 123625) (by norm_num)
theorem B987029 : Blo 435777 987029 := bbase (se 6 (by rfl) ⟨23133, by rfl⟩ : syracuseStep 987029 = 46267) (by norm_num)
theorem B659357 : Blo 435777 659357 := bbase (se 3 (by rfl) ⟨123629, by rfl⟩ : syracuseStep 659357 = 247259) (by norm_num)
theorem B659381 : Blo 435777 659381 := bbase (se 5 (by rfl) ⟨30908, by rfl⟩ : syracuseStep 659381 = 61817) (by norm_num)
theorem B659405 : Blo 435777 659405 := bbase (se 3 (by rfl) ⟨123638, by rfl⟩ : syracuseStep 659405 = 247277) (by norm_num)
theorem B987101 : Blo 435777 987101 := bbase (se 3 (by rfl) ⟨185081, by rfl⟩ : syracuseStep 987101 = 370163) (by norm_num)
theorem B659429 : Blo 435777 659429 := bbase (se 4 (by rfl) ⟨61821, by rfl⟩ : syracuseStep 659429 = 123643) (by norm_num)
theorem B659453 : Blo 435777 659453 := bbase (se 3 (by rfl) ⟨123647, by rfl⟩ : syracuseStep 659453 = 247295) (by norm_num)
theorem B659477 : Blo 435777 659477 := bbase (se 6 (by rfl) ⟨15456, by rfl⟩ : syracuseStep 659477 = 30913) (by norm_num)
theorem B987173 : Blo 435777 987173 := bbase (se 4 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 987173 = 185095) (by norm_num)
theorem B659501 : Blo 435777 659501 := bbase (se 3 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 659501 = 247313) (by norm_num)
theorem B659525 : Blo 435777 659525 := bbase (se 4 (by rfl) ⟨61830, by rfl⟩ : syracuseStep 659525 = 123661) (by norm_num)
theorem B659549 : Blo 435777 659549 := bbase (se 3 (by rfl) ⟨123665, by rfl⟩ : syracuseStep 659549 = 247331) (by norm_num)
theorem B987245 : Blo 435777 987245 := bbase (se 3 (by rfl) ⟨185108, by rfl⟩ : syracuseStep 987245 = 370217) (by norm_num)
theorem B659573 : Blo 435777 659573 := bbase (se 5 (by rfl) ⟨30917, by rfl⟩ : syracuseStep 659573 = 61835) (by norm_num)
theorem B1478789 : Blo 435777 1478789 := bbase (se 4 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 1478789 = 277273) (by norm_num)
theorem B790661 : Blo 435777 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B659597 : Blo 435777 659597 := bbase (se 3 (by rfl) ⟨123674, by rfl⟩ : syracuseStep 659597 = 247349) (by norm_num)
theorem B659621 : Blo 435777 659621 := bbase (se 4 (by rfl) ⟨61839, by rfl⟩ : syracuseStep 659621 = 123679) (by norm_num)
theorem B987317 : Blo 435777 987317 := bbase (se 5 (by rfl) ⟨46280, by rfl⟩ : syracuseStep 987317 = 92561) (by norm_num)
theorem B659645 : Blo 435777 659645 := bbase (se 3 (by rfl) ⟨123683, by rfl⟩ : syracuseStep 659645 = 247367) (by norm_num)
theorem B8523989 : Blo 435777 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B987389 : Blo 435777 987389 := bbase (se 3 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 987389 = 370271) (by norm_num)
theorem B1773893 : Blo 435777 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B987461 : Blo 435777 987461 := bbase (se 4 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 987461 = 185149) (by norm_num)
theorem B987533 : Blo 435777 987533 := bbase (se 3 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 987533 = 370325) (by norm_num)
theorem B1053109 : Blo 435777 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B987605 : Blo 435777 987605 := bbase (se 7 (by rfl) ⟨11573, by rfl⟩ : syracuseStep 987605 = 23147) (by norm_num)
theorem B1053157 : Blo 435777 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B1217045 : Blo 435777 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B987677 : Blo 435777 987677 := bbase (se 3 (by rfl) ⟨185189, by rfl⟩ : syracuseStep 987677 = 370379) (by norm_num)
theorem B1479221 : Blo 435777 1479221 := bbase (se 5 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 1479221 = 138677) (by norm_num)
theorem B987749 : Blo 435777 987749 := bbase (se 4 (by rfl) ⟨92601, by rfl⟩ : syracuseStep 987749 = 185203) (by norm_num)
theorem B1872517 : Blo 435777 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B987821 : Blo 435777 987821 := bbase (se 3 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 987821 = 370433) (by norm_num)
theorem B987893 : Blo 435777 987893 := bbase (se 5 (by rfl) ⟨46307, by rfl⟩ : syracuseStep 987893 = 92615) (by norm_num)
theorem B987965 : Blo 435777 987965 := bbase (se 3 (by rfl) ⟨185243, by rfl⟩ : syracuseStep 987965 = 370487) (by norm_num)
theorem B988037 : Blo 435777 988037 := bbase (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) (by norm_num)
theorem B988109 : Blo 435777 988109 := bbase (se 3 (by rfl) ⟨185270, by rfl⟩ : syracuseStep 988109 = 370541) (by norm_num)
theorem B1479653 : Blo 435777 1479653 := bbase (se 4 (by rfl) ⟨138717, by rfl⟩ : syracuseStep 1479653 = 277435) (by norm_num)
theorem B988181 : Blo 435777 988181 := bbase (se 6 (by rfl) ⟨23160, by rfl⟩ : syracuseStep 988181 = 46321) (by norm_num)
theorem B1053773 : Blo 435777 1053773 := bbase (se 3 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 1053773 = 395165) (by norm_num)
theorem B988253 : Blo 435777 988253 := bbase (se 3 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 988253 = 370595) (by norm_num)
theorem B791677 : Blo 435777 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B2135173 : Blo 435777 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B988325 : Blo 435777 988325 := bbase (se 4 (by rfl) ⟨92655, by rfl⟩ : syracuseStep 988325 = 185311) (by norm_num)
theorem B988397 : Blo 435777 988397 := bbase (se 3 (by rfl) ⟨185324, by rfl⟩ : syracuseStep 988397 = 370649) (by norm_num)
theorem B1578293 : Blo 435777 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B988469 : Blo 435777 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B988541 : Blo 435777 988541 := bbase (se 3 (by rfl) ⟨185351, by rfl⟩ : syracuseStep 988541 = 370703) (by norm_num)
theorem B1480085 : Blo 435777 1480085 := bbase (se 6 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 1480085 = 69379) (by norm_num)
theorem B1054117 : Blo 435777 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B2004389 : Blo 435777 2004389 := bbase (se 4 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 2004389 = 375823) (by norm_num)
theorem B988613 : Blo 435777 988613 := bbase (se 4 (by rfl) ⟨92682, by rfl⟩ : syracuseStep 988613 = 185365) (by norm_num)
theorem B988685 : Blo 435777 988685 := bbase (se 3 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 988685 = 370757) (by norm_num)
theorem B988757 : Blo 435777 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B1054349 : Blo 435777 1054349 := bbase (se 3 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 1054349 = 395381) (by norm_num)
theorem B988829 : Blo 435777 988829 := bbase (se 3 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 988829 = 370811) (by norm_num)
theorem B988901 : Blo 435777 988901 := bbase (se 4 (by rfl) ⟨92709, by rfl⟩ : syracuseStep 988901 = 185419) (by norm_num)
theorem B988973 : Blo 435777 988973 := bbase (se 3 (by rfl) ⟨185432, by rfl⟩ : syracuseStep 988973 = 370865) (by norm_num)
theorem B1480517 : Blo 435777 1480517 := bbase (se 4 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 1480517 = 277597) (by norm_num)
theorem B1054541 : Blo 435777 1054541 := bbase (se 3 (by rfl) ⟨197726, by rfl⟩ : syracuseStep 1054541 = 395453) (by norm_num)
theorem B989045 : Blo 435777 989045 := bbase (se 5 (by rfl) ⟨46361, by rfl⟩ : syracuseStep 989045 = 92723) (by norm_num)
theorem B989117 : Blo 435777 989117 := bbase (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) (by norm_num)
theorem B2660309 : Blo 435777 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B989189 : Blo 435777 989189 := bbase (se 4 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 989189 = 185473) (by norm_num)
theorem B989261 : Blo 435777 989261 := bbase (se 3 (by rfl) ⟨185486, by rfl⟩ : syracuseStep 989261 = 370973) (by norm_num)
theorem B1054829 : Blo 435777 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B989333 : Blo 435777 989333 := bbase (se 6 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 989333 = 46375) (by norm_num)
theorem B989405 : Blo 435777 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B1251557 : Blo 435777 1251557 := bbase (se 4 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 1251557 = 234667) (by norm_num)
theorem B1480949 : Blo 435777 1480949 := bbase (se 5 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 1480949 = 138839) (by norm_num)
theorem B989477 : Blo 435777 989477 := bbase (se 4 (by rfl) ⟨92763, by rfl⟩ : syracuseStep 989477 = 185527) (by norm_num)
theorem B3807701 : Blo 435777 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B563689 : Blo 435777 563689 := bbase (se 2 (by rfl) ⟨211383, by rfl⟩ : syracuseStep 563689 = 422767) (by norm_num)
theorem B1481381 : Blo 435777 1481381 := bbase (se 4 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 1481381 = 277759) (by norm_num)
theorem B498361 : Blo 435777 498361 := bbase (se 2 (by rfl) ⟨186885, by rfl⟩ : syracuseStep 498361 = 373771) (by norm_num)
theorem B498397 : Blo 435777 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B465797 : Blo 435777 465797 := bbase (se 4 (by rfl) ⟨43668, by rfl⟩ : syracuseStep 465797 = 87337) (by norm_num)
theorem B2104373 : Blo 435777 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B1481813 : Blo 435777 1481813 := bbase (se 8 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 1481813 = 17365) (by norm_num)
theorem B3316949 : Blo 435777 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B1187093 : Blo 435777 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B466241 : Blo 435777 466241 := bbase (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) (by norm_num)
theorem B1482245 : Blo 435777 1482245 := bbase (se 4 (by rfl) ⟨138960, by rfl⟩ : syracuseStep 1482245 = 277921) (by norm_num)
theorem B466489 : Blo 435777 466489 := bbase (se 2 (by rfl) ⟨174933, by rfl⟩ : syracuseStep 466489 = 349867) (by norm_num)
theorem B2989781 : Blo 435777 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B827309 : Blo 435777 827309 := bbase (se 3 (by rfl) ⟨155120, by rfl⟩ : syracuseStep 827309 = 310241) (by norm_num)
theorem B1482677 : Blo 435777 1482677 := bbase (se 5 (by rfl) ⟨69500, by rfl⟩ : syracuseStep 1482677 = 139001) (by norm_num)
theorem B466921 : Blo 435777 466921 := bbase (se 2 (by rfl) ⟨175095, by rfl⟩ : syracuseStep 466921 = 350191) (by norm_num)
theorem B1581061 : Blo 435777 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B466993 : Blo 435777 466993 := bbase (se 2 (by rfl) ⟨175122, by rfl⟩ : syracuseStep 466993 = 350245) (by norm_num)
theorem B499889 : Blo 435777 499889 := bbase (se 2 (by rfl) ⟨187458, by rfl⟩ : syracuseStep 499889 = 374917) (by norm_num)
theorem B827597 : Blo 435777 827597 := bbase (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) (by norm_num)
theorem B2367701 : Blo 435777 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B2105621 : Blo 435777 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B532765 : Blo 435777 532765 := bbase (se 3 (by rfl) ⟨99893, by rfl⟩ : syracuseStep 532765 = 199787) (by norm_num)
theorem B12165461 : Blo 435777 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B827749 : Blo 435777 827749 := bbase (se 4 (by rfl) ⟨77601, by rfl⟩ : syracuseStep 827749 = 155203) (by norm_num)
theorem B1483109 : Blo 435777 1483109 := bbase (se 4 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 1483109 = 278083) (by norm_num)
theorem B467365 : Blo 435777 467365 := bbase (se 4 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 467365 = 87631) (by norm_num)
theorem B828053 : Blo 435777 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B664237 : Blo 435777 664237 := bbase (se 3 (by rfl) ⟨124544, by rfl⟩ : syracuseStep 664237 = 249089) (by norm_num)
theorem B500473 : Blo 435777 500473 := bbase (se 2 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 500473 = 375355) (by norm_num)
theorem B1483541 : Blo 435777 1483541 := bbase (se 6 (by rfl) ⟨34770, by rfl⟩ : syracuseStep 1483541 = 69541) (by norm_num)
theorem B467741 : Blo 435777 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B500513 : Blo 435777 500513 := bbase (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) (by norm_num)
theorem B467813 : Blo 435777 467813 := bbase (se 4 (by rfl) ⟨43857, by rfl⟩ : syracuseStep 467813 = 87715) (by norm_num)
theorem B2499605 : Blo 435777 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B468001 : Blo 435777 468001 := bbase (se 2 (by rfl) ⟨175500, by rfl⟩ : syracuseStep 468001 = 351001) (by norm_num)
theorem B1483973 : Blo 435777 1483973 := bbase (se 4 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 1483973 = 278245) (by norm_num)
theorem B468185 : Blo 435777 468185 := bbase (se 2 (by rfl) ⟨175569, by rfl⟩ : syracuseStep 468185 = 351139) (by norm_num)
theorem B828805 : Blo 435777 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B599509 : Blo 435777 599509 := bbase (se 7 (by rfl) ⟨7025, by rfl⟩ : syracuseStep 599509 = 14051) (by norm_num)
theorem B3745237 : Blo 435777 3745237 := bbase (se 7 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 3745237 = 87779) (by norm_num)
theorem B828949 : Blo 435777 828949 := bbase (se 6 (by rfl) ⟨19428, by rfl⟩ : syracuseStep 828949 = 38857) (by norm_num)
theorem B1877525 : Blo 435777 1877525 := bbase (se 6 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 1877525 = 88009) (by norm_num)
theorem B829109 : Blo 435777 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B501481 : Blo 435777 501481 := bbase (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) (by norm_num)
theorem B1877813 : Blo 435777 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B829253 : Blo 435777 829253 := bbase (se 4 (by rfl) ⟨77742, by rfl⟩ : syracuseStep 829253 = 155485) (by norm_num)
theorem B468937 : Blo 435777 468937 := bbase (se 2 (by rfl) ⟨175851, by rfl⟩ : syracuseStep 468937 = 351703) (by norm_num)
theorem B469009 : Blo 435777 469009 := bbase (se 2 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 469009 = 351757) (by norm_num)
theorem B698453 : Blo 435777 698453 := bbase (se 8 (by rfl) ⟨4092, by rfl⟩ : syracuseStep 698453 = 8185) (by norm_num)
theorem B829541 : Blo 435777 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B698485 : Blo 435777 698485 := bbase (se 5 (by rfl) ⟨32741, by rfl⟩ : syracuseStep 698485 = 65483) (by norm_num)
theorem B469189 : Blo 435777 469189 := bbase (se 4 (by rfl) ⟨43986, by rfl⟩ : syracuseStep 469189 = 87973) (by norm_num)
theorem B1124597 : Blo 435777 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B829693 : Blo 435777 829693 := bbase (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) (by norm_num)
theorem B7317845 : Blo 435777 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B829997 : Blo 435777 829997 := bbase (se 3 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 829997 = 311249) (by norm_num)
theorem B2206277 : Blo 435777 2206277 := bbase (se 4 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 2206277 = 413677) (by norm_num)
theorem B993941 : Blo 435777 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B4107125 : Blo 435777 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B994277 : Blo 435777 994277 := bbase (se 4 (by rfl) ⟨93213, by rfl⟩ : syracuseStep 994277 = 186427) (by norm_num)
theorem B2108389 : Blo 435777 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B699413 : Blo 435777 699413 := bbase (se 6 (by rfl) ⟨16392, by rfl⟩ : syracuseStep 699413 = 32785) (by norm_num)
theorem B830749 : Blo 435777 830749 := bbase (se 3 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 830749 = 311531) (by norm_num)
theorem B3747221 : Blo 435777 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B830893 : Blo 435777 830893 := bbase (se 3 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 830893 = 311585) (by norm_num)
theorem B831053 : Blo 435777 831053 := bbase (se 3 (by rfl) ⟨155822, by rfl⟩ : syracuseStep 831053 = 311645) (by norm_num)
theorem B700093 : Blo 435777 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B831197 : Blo 435777 831197 := bbase (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) (by norm_num)
theorem B700157 : Blo 435777 700157 := bbase (se 3 (by rfl) ⟨131279, by rfl⟩ : syracuseStep 700157 = 262559) (by norm_num)
theorem B2207573 : Blo 435777 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B831485 : Blo 435777 831485 := bbase (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) (by norm_num)
theorem B831637 : Blo 435777 831637 := bbase (se 6 (by rfl) ⟨19491, by rfl⟩ : syracuseStep 831637 = 38983) (by norm_num)
theorem B1618165 : Blo 435777 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B1782101 : Blo 435777 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B668093 : Blo 435777 668093 := bbase (se 3 (by rfl) ⟨125267, by rfl⟩ : syracuseStep 668093 = 250535) (by norm_num)
theorem B831941 : Blo 435777 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B5681621 : Blo 435777 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B2798165 : Blo 435777 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B504505 : Blo 435777 504505 := bbase (se 2 (by rfl) ⟨189189, by rfl⟩ : syracuseStep 504505 = 378379) (by norm_num)
theorem B1127141 : Blo 435777 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B799621 : Blo 435777 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B3978197 : Blo 435777 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B701477 : Blo 435777 701477 := bbase (se 4 (by rfl) ⟨65763, by rfl⟩ : syracuseStep 701477 = 131527) (by norm_num)
theorem B2208869 : Blo 435777 2208869 := bbase (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) (by norm_num)
theorem B832693 : Blo 435777 832693 := bbase (se 5 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 832693 = 78065) (by norm_num)
theorem B701669 : Blo 435777 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B832837 : Blo 435777 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B701797 : Blo 435777 701797 := bbase (se 4 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 701797 = 131587) (by norm_num)
theorem B832997 : Blo 435777 832997 := bbase (se 4 (by rfl) ⟨78093, by rfl⟩ : syracuseStep 832997 = 156187) (by norm_num)
theorem B833141 : Blo 435777 833141 := bbase (se 5 (by rfl) ⟨39053, by rfl⟩ : syracuseStep 833141 = 78107) (by norm_num)
theorem B472717 : Blo 435777 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B3192533 : Blo 435777 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B833429 : Blo 435777 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B2537365 : Blo 435777 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B931765 : Blo 435777 931765 := bbase (se 5 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 931765 = 87353) (by norm_num)
theorem B702437 : Blo 435777 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B833581 : Blo 435777 833581 := bbase (se 3 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 833581 = 312593) (by norm_num)
theorem B997469 : Blo 435777 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B997589 : Blo 435777 997589 := bbase (se 7 (by rfl) ⟨11690, by rfl⟩ : syracuseStep 997589 = 23381) (by norm_num)
theorem B735493 : Blo 435777 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B932141 : Blo 435777 932141 := bbase (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) (by norm_num)
theorem B538969 : Blo 435777 538969 := bbase (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) (by norm_num)
theorem B735581 : Blo 435777 735581 := bbase (se 3 (by rfl) ⟨137921, by rfl⟩ : syracuseStep 735581 = 275843) (by norm_num)
theorem B833885 : Blo 435777 833885 := bbase (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) (by norm_num)
theorem B2210165 : Blo 435777 2210165 := bbase (se 5 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 2210165 = 207203) (by norm_num)
theorem B702893 : Blo 435777 702893 := bbase (se 3 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 702893 = 263585) (by norm_num)
theorem B735709 : Blo 435777 735709 := bbase (se 3 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 735709 = 275891) (by norm_num)
theorem B1325605 : Blo 435777 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B735797 : Blo 435777 735797 := bbase (se 5 (by rfl) ⟨34490, by rfl⟩ : syracuseStep 735797 = 68981) (by norm_num)
theorem B703117 : Blo 435777 703117 := bbase (se 3 (by rfl) ⟨131834, by rfl⟩ : syracuseStep 703117 = 263669) (by norm_num)
theorem B1325749 : Blo 435777 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B735925 : Blo 435777 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B703181 : Blo 435777 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B473833 : Blo 435777 473833 := bbase (se 2 (by rfl) ⟨177687, by rfl⟩ : syracuseStep 473833 = 355375) (by norm_num)
theorem B736013 : Blo 435777 736013 := bbase (se 3 (by rfl) ⟨138002, by rfl⟩ : syracuseStep 736013 = 276005) (by norm_num)
theorem B3160853 : Blo 435777 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B473881 : Blo 435777 473881 := bbase (se 2 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 473881 = 355411) (by norm_num)
theorem B3324725 : Blo 435777 3324725 := bbase (se 5 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 3324725 = 311693) (by norm_num)
theorem B703309 : Blo 435777 703309 := bbase (se 3 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 703309 = 263741) (by norm_num)
theorem B736141 : Blo 435777 736141 := bbase (se 3 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 736141 = 276053) (by norm_num)
theorem B736229 : Blo 435777 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B2112581 : Blo 435777 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B834637 : Blo 435777 834637 := bbase (se 3 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 834637 = 312989) (by norm_num)
theorem B736357 : Blo 435777 736357 := bbase (se 4 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 736357 = 138067) (by norm_num)
theorem B736445 : Blo 435777 736445 := bbase (se 3 (by rfl) ⟨138083, by rfl⟩ : syracuseStep 736445 = 276167) (by norm_num)
theorem B11943125 : Blo 435777 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B834781 : Blo 435777 834781 := bbase (se 3 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 834781 = 313043) (by norm_num)
theorem B933125 : Blo 435777 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B736573 : Blo 435777 736573 := bbase (se 3 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 736573 = 276215) (by norm_num)
theorem B2571605 : Blo 435777 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B736661 : Blo 435777 736661 := bbase (se 6 (by rfl) ⟨17265, by rfl⟩ : syracuseStep 736661 = 34531) (by norm_num)
theorem B4996565 : Blo 435777 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B736789 : Blo 435777 736789 := bbase (se 6 (by rfl) ⟨17268, by rfl⟩ : syracuseStep 736789 = 34537) (by norm_num)
theorem B736877 : Blo 435777 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B2211461 : Blo 435777 2211461 := bbase (se 4 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 2211461 = 414649) (by norm_num)
theorem B737005 : Blo 435777 737005 := bbase (se 3 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 737005 = 276377) (by norm_num)
theorem B1326869 : Blo 435777 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B835373 : Blo 435777 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B1326917 : Blo 435777 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B737093 : Blo 435777 737093 := bbase (se 4 (by rfl) ⟨69102, by rfl⟩ : syracuseStep 737093 = 138205) (by norm_num)
theorem B933781 : Blo 435777 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B737221 : Blo 435777 737221 := bbase (se 4 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 737221 = 138229) (by norm_num)
theorem B507917 : Blo 435777 507917 := bbase (se 3 (by rfl) ⟨95234, by rfl⟩ : syracuseStep 507917 = 190469) (by norm_num)
theorem B737309 : Blo 435777 737309 := bbase (se 3 (by rfl) ⟨138245, by rfl⟩ : syracuseStep 737309 = 276491) (by norm_num)
theorem B1491029 : Blo 435777 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B737437 : Blo 435777 737437 := bbase (se 3 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 737437 = 276539) (by norm_num)
theorem B442541 : Blo 435777 442541 := bbase (se 3 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 442541 = 165953) (by norm_num)
theorem B737525 : Blo 435777 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B737653 : Blo 435777 737653 := bbase (se 5 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 737653 = 69155) (by norm_num)
theorem B737741 : Blo 435777 737741 := bbase (se 3 (by rfl) ⟨138326, by rfl⟩ : syracuseStep 737741 = 276653) (by norm_num)
theorem B3228149 : Blo 435777 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B541225 : Blo 435777 541225 := bbase (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) (by norm_num)
theorem B737869 : Blo 435777 737869 := bbase (se 3 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 737869 = 276701) (by norm_num)
theorem B737957 : Blo 435777 737957 := bbase (se 4 (by rfl) ⟨69183, by rfl⟩ : syracuseStep 737957 = 138367) (by norm_num)
theorem B934669 : Blo 435777 934669 := bbase (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) (by norm_num)
theorem B738085 : Blo 435777 738085 := bbase (se 4 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 738085 = 138391) (by norm_num)
theorem B738173 : Blo 435777 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B2212757 : Blo 435777 2212757 := bbase (se 6 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 2212757 = 103723) (by norm_num)
theorem B738301 : Blo 435777 738301 := bbase (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) (by norm_num)
theorem B738389 : Blo 435777 738389 := bbase (se 8 (by rfl) ⟨4326, by rfl⟩ : syracuseStep 738389 = 8653) (by norm_num)
theorem B1655909 : Blo 435777 1655909 := bbase (se 4 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 1655909 = 310483) (by norm_num)
theorem B1688741 : Blo 435777 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B738517 : Blo 435777 738517 := bbase (se 7 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 738517 = 17309) (by norm_num)
theorem B935165 : Blo 435777 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B738605 : Blo 435777 738605 := bbase (se 3 (by rfl) ⟨138488, by rfl⟩ : syracuseStep 738605 = 276977) (by norm_num)
theorem B1656197 : Blo 435777 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B738733 : Blo 435777 738733 := bbase (se 3 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 738733 = 277025) (by norm_num)
theorem B738821 : Blo 435777 738821 := bbase (se 4 (by rfl) ⟨69264, by rfl⟩ : syracuseStep 738821 = 138529) (by norm_num)
theorem B738949 : Blo 435777 738949 := bbase (se 4 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 738949 = 138553) (by norm_num)
theorem B1492661 : Blo 435777 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B1001173 : Blo 435777 1001173 := bbase (se 7 (by rfl) ⟨11732, by rfl⟩ : syracuseStep 1001173 = 23465) (by norm_num)
theorem B739037 : Blo 435777 739037 := bbase (se 3 (by rfl) ⟨138569, by rfl⟩ : syracuseStep 739037 = 277139) (by norm_num)
theorem B739165 : Blo 435777 739165 := bbase (se 3 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 739165 = 277187) (by norm_num)
theorem B739253 : Blo 435777 739253 := bbase (se 5 (by rfl) ⟨34652, by rfl⟩ : syracuseStep 739253 = 69305) (by norm_num)
theorem B739381 : Blo 435777 739381 := bbase (se 5 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 739381 = 69317) (by norm_num)
theorem B936029 : Blo 435777 936029 := bbase (se 3 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 936029 = 351011) (by norm_num)
theorem B739469 : Blo 435777 739469 := bbase (se 3 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 739469 = 277301) (by norm_num)
theorem B2214053 : Blo 435777 2214053 := bbase (se 4 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 2214053 = 415135) (by norm_num)
theorem B936173 : Blo 435777 936173 := bbase (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) (by norm_num)
theorem B739597 : Blo 435777 739597 := bbase (se 3 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 739597 = 277349) (by norm_num)
theorem B739685 : Blo 435777 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B739813 : Blo 435777 739813 := bbase (se 4 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 739813 = 138715) (by norm_num)
theorem B903653 : Blo 435777 903653 := bbase (se 4 (by rfl) ⟨84717, by rfl⟩ : syracuseStep 903653 = 169435) (by norm_num)
theorem B2804213 : Blo 435777 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B1657381 : Blo 435777 1657381 := bbase (se 4 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 1657381 = 310759) (by norm_num)
theorem B739901 : Blo 435777 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B1428101 : Blo 435777 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B740029 : Blo 435777 740029 := bbase (se 3 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 740029 = 277511) (by norm_num)
theorem B740117 : Blo 435777 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B445225 : Blo 435777 445225 := bbase (se 2 (by rfl) ⟨166959, by rfl⟩ : syracuseStep 445225 = 333919) (by norm_num)
theorem B1657685 : Blo 435777 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B1002341 : Blo 435777 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B740245 : Blo 435777 740245 := bbase (se 6 (by rfl) ⟨17349, by rfl⟩ : syracuseStep 740245 = 34699) (by norm_num)
theorem B936917 : Blo 435777 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B740333 : Blo 435777 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B4213781 : Blo 435777 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B740461 : Blo 435777 740461 := bbase (se 3 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 740461 = 277673) (by norm_num)
theorem B740549 : Blo 435777 740549 := bbase (se 4 (by rfl) ⟨69426, by rfl⟩ : syracuseStep 740549 = 138853) (by norm_num)
theorem B1002725 : Blo 435777 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B740677 : Blo 435777 740677 := bbase (se 4 (by rfl) ⟨69438, by rfl⟩ : syracuseStep 740677 = 138877) (by norm_num)
theorem B740765 : Blo 435777 740765 := bbase (se 3 (by rfl) ⟨138893, by rfl⟩ : syracuseStep 740765 = 277787) (by norm_num)
theorem B2215349 : Blo 435777 2215349 := bbase (se 5 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 2215349 = 207689) (by norm_num)
theorem B740893 : Blo 435777 740893 := bbase (se 3 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 740893 = 277835) (by norm_num)
theorem B740981 : Blo 435777 740981 := bbase (se 5 (by rfl) ⟨34733, by rfl⟩ : syracuseStep 740981 = 69467) (by norm_num)
theorem B708277 : Blo 435777 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B937669 : Blo 435777 937669 := bbase (se 4 (by rfl) ⟨87906, by rfl⟩ : syracuseStep 937669 = 175813) (by norm_num)
theorem B741109 : Blo 435777 741109 := bbase (se 5 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 741109 = 69479) (by norm_num)
theorem B741197 : Blo 435777 741197 := bbase (se 3 (by rfl) ⟨138974, by rfl⟩ : syracuseStep 741197 = 277949) (by norm_num)
theorem B937813 : Blo 435777 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B1396597 : Blo 435777 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B741325 : Blo 435777 741325 := bbase (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) (by norm_num)
theorem B741413 : Blo 435777 741413 := bbase (se 4 (by rfl) ⟨69507, by rfl⟩ : syracuseStep 741413 = 139015) (by norm_num)
theorem B741541 : Blo 435777 741541 := bbase (se 4 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 741541 = 139039) (by norm_num)
theorem B938189 : Blo 435777 938189 := bbase (se 3 (by rfl) ⟨175910, by rfl⟩ : syracuseStep 938189 = 351821) (by norm_num)
theorem B741629 : Blo 435777 741629 := bbase (se 3 (by rfl) ⟨139055, by rfl⟩ : syracuseStep 741629 = 278111) (by norm_num)
theorem B3985685 : Blo 435777 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B840061 : Blo 435777 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B741757 : Blo 435777 741757 := bbase (se 3 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 741757 = 278159) (by norm_num)
theorem B741845 : Blo 435777 741845 := bbase (se 7 (by rfl) ⟨8693, by rfl⟩ : syracuseStep 741845 = 17387) (by norm_num)
theorem B938557 : Blo 435777 938557 := bbase (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) (by norm_num)
theorem B3986005 : Blo 435777 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B741973 : Blo 435777 741973 := bbase (se 8 (by rfl) ⟨4347, by rfl⟩ : syracuseStep 741973 = 8695) (by norm_num)
theorem B742061 : Blo 435777 742061 := bbase (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) (by norm_num)
theorem B2216645 : Blo 435777 2216645 := bbase (se 4 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 2216645 = 415621) (by norm_num)
theorem B4477781 : Blo 435777 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B1659797 : Blo 435777 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B2249845 : Blo 435777 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B1660085 : Blo 435777 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B840917 : Blo 435777 840917 := bbase (se 7 (by rfl) ⟨9854, by rfl⟩ : syracuseStep 840917 = 19709) (by norm_num)
theorem B1103341 : Blo 435777 1103341 := bbase (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) (by norm_num)
theorem B1103453 : Blo 435777 1103453 := bbase (se 3 (by rfl) ⟨206897, by rfl⟩ : syracuseStep 1103453 = 413795) (by norm_num)
theorem B4511477 : Blo 435777 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B710405 : Blo 435777 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B1103645 : Blo 435777 1103645 := bbase (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) (by norm_num)
theorem B2217941 : Blo 435777 2217941 := bbase (se 7 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 2217941 = 51983) (by norm_num)
theorem B1103989 : Blo 435777 1103989 := bbase (se 5 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 1103989 = 103499) (by norm_num)
theorem B1104101 : Blo 435777 1104101 := bbase (se 4 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 1104101 = 207019) (by norm_num)
theorem B1661269 : Blo 435777 1661269 := bbase (se 10 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 1661269 = 4867) (by norm_num)
theorem B3332501 : Blo 435777 3332501 := bbase (se 6 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 3332501 = 156211) (by norm_num)
theorem B1104293 : Blo 435777 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B3201589 : Blo 435777 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B1661573 : Blo 435777 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B1399493 : Blo 435777 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B1104637 : Blo 435777 1104637 := bbase (se 3 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 1104637 = 414239) (by norm_num)
theorem B3726101 : Blo 435777 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B1104749 : Blo 435777 1104749 := bbase (se 3 (by rfl) ⟨207140, by rfl⟩ : syracuseStep 1104749 = 414281) (by norm_num)
theorem B842645 : Blo 435777 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B1104941 : Blo 435777 1104941 := bbase (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) (by norm_num)
theorem B2219237 : Blo 435777 2219237 := bbase (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) (by norm_num)
theorem B1105285 : Blo 435777 1105285 := bbase (se 4 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 1105285 = 207241) (by norm_num)
theorem B9493973 : Blo 435777 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B1105397 : Blo 435777 1105397 := bbase (se 5 (by rfl) ⟨51815, by rfl⟩ : syracuseStep 1105397 = 103631) (by norm_num)
theorem B1105589 : Blo 435777 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B1105933 : Blo 435777 1105933 := bbase (se 3 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 1105933 = 414725) (by norm_num)
theorem B1106045 : Blo 435777 1106045 := bbase (se 3 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 1106045 = 414767) (by norm_num)
theorem B1106237 : Blo 435777 1106237 := bbase (se 3 (by rfl) ⟨207419, by rfl⟩ : syracuseStep 1106237 = 414839) (by norm_num)
theorem B2220533 : Blo 435777 2220533 := bbase (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) (by norm_num)
theorem B1106581 : Blo 435777 1106581 := bbase (se 6 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 1106581 = 51871) (by norm_num)
theorem B1663685 : Blo 435777 1663685 := bbase (se 4 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 1663685 = 311941) (by norm_num)
theorem B1106693 : Blo 435777 1106693 := bbase (se 4 (by rfl) ⟨103752, by rfl⟩ : syracuseStep 1106693 = 207505) (by norm_num)
theorem B1401749 : Blo 435777 1401749 := bbase (se 6 (by rfl) ⟨32853, by rfl⟩ : syracuseStep 1401749 = 65707) (by norm_num)
theorem B1106885 : Blo 435777 1106885 := bbase (se 4 (by rfl) ⟨103770, by rfl⟩ : syracuseStep 1106885 = 207541) (by norm_num)
theorem B1663973 : Blo 435777 1663973 := bbase (se 4 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 1663973 = 311995) (by norm_num)
theorem B1107229 : Blo 435777 1107229 := bbase (se 3 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 1107229 = 415211) (by norm_num)
theorem B1107341 : Blo 435777 1107341 := bbase (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) (by norm_num)
theorem B681485 : Blo 435777 681485 := bbase (se 3 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 681485 = 255557) (by norm_num)
theorem B1107533 : Blo 435777 1107533 := bbase (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) (by norm_num)
theorem B1402517 : Blo 435777 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B1926805 : Blo 435777 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B3729077 : Blo 435777 3729077 := bbase (se 5 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 3729077 = 349601) (by norm_num)
theorem B2221829 : Blo 435777 2221829 := bbase (se 4 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 2221829 = 416593) (by norm_num)
theorem B1107877 : Blo 435777 1107877 := bbase (se 4 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 1107877 = 207727) (by norm_num)
theorem B1107989 : Blo 435777 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B2484341 : Blo 435777 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B1665157 : Blo 435777 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B1403029 : Blo 435777 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B1108181 : Blo 435777 1108181 := bbase (se 7 (by rfl) ⟨12986, by rfl⟩ : syracuseStep 1108181 = 25973) (by norm_num)
theorem B1861957 : Blo 435777 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B1665461 : Blo 435777 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B1108525 : Blo 435777 1108525 := bbase (se 3 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 1108525 = 415697) (by norm_num)
theorem B551549 : Blo 435777 551549 := bbase (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) (by norm_num)
theorem B1108637 : Blo 435777 1108637 := bbase (se 3 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 1108637 = 415739) (by norm_num)
theorem B551605 : Blo 435777 551605 := bbase (se 5 (by rfl) ⟨25856, by rfl⟩ : syracuseStep 551605 = 51713) (by norm_num)
theorem B551701 : Blo 435777 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B1108829 : Blo 435777 1108829 := bbase (se 3 (by rfl) ⟨207905, by rfl⟩ : syracuseStep 1108829 = 415811) (by norm_num)
theorem B551873 : Blo 435777 551873 := bbase (se 2 (by rfl) ⟨206952, by rfl⟩ : syracuseStep 551873 = 413905) (by norm_num)
theorem B2255845 : Blo 435777 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B551929 : Blo 435777 551929 := bbase (se 2 (by rfl) ⟨206973, by rfl⟩ : syracuseStep 551929 = 413947) (by norm_num)
theorem B2223125 : Blo 435777 2223125 := bbase (se 6 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 2223125 = 104209) (by norm_num)
theorem B552025 : Blo 435777 552025 := bbase (se 2 (by rfl) ⟨207009, by rfl⟩ : syracuseStep 552025 = 414019) (by norm_num)
theorem B1109173 : Blo 435777 1109173 := bbase (se 5 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 1109173 = 103985) (by norm_num)
theorem B552197 : Blo 435777 552197 := bbase (se 4 (by rfl) ⟨51768, by rfl⟩ : syracuseStep 552197 = 103537) (by norm_num)
theorem B945413 : Blo 435777 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B3534101 : Blo 435777 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B2485525 : Blo 435777 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B1109285 : Blo 435777 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B552253 : Blo 435777 552253 := bbase (se 3 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 552253 = 207095) (by norm_num)
theorem B552349 : Blo 435777 552349 := bbase (se 3 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 552349 = 207131) (by norm_num)
theorem B1011133 : Blo 435777 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1109477 : Blo 435777 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B552521 : Blo 435777 552521 := bbase (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) (by norm_num)
theorem B552577 : Blo 435777 552577 := bbase (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) (by norm_num)
theorem B552673 : Blo 435777 552673 := bbase (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) (by norm_num)
theorem B1863445 : Blo 435777 1863445 := bbase (se 6 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 1863445 = 87349) (by norm_num)
theorem B1863461 : Blo 435777 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B1109821 : Blo 435777 1109821 := bbase (se 3 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 1109821 = 416183) (by norm_num)
theorem B1404773 : Blo 435777 1404773 := bbase (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) (by norm_num)
theorem B552845 : Blo 435777 552845 := bbase (se 3 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 552845 = 207317) (by norm_num)
theorem B1109933 : Blo 435777 1109933 := bbase (se 3 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 1109933 = 416225) (by norm_num)
theorem B552901 : Blo 435777 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B1241077 : Blo 435777 1241077 := bbase (se 5 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 1241077 = 116351) (by norm_num)
theorem B552997 : Blo 435777 552997 := bbase (se 4 (by rfl) ⟨51843, by rfl⟩ : syracuseStep 552997 = 103687) (by norm_num)
theorem B1404965 : Blo 435777 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B1110125 : Blo 435777 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1241237 : Blo 435777 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B1896629 : Blo 435777 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B553169 : Blo 435777 553169 := bbase (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) (by norm_num)
theorem B553225 : Blo 435777 553225 := bbase (se 2 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 553225 = 414919) (by norm_num)
theorem B2224421 : Blo 435777 2224421 := bbase (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) (by norm_num)
theorem B782669 : Blo 435777 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B553321 : Blo 435777 553321 := bbase (se 2 (by rfl) ⟨207495, by rfl⟩ : syracuseStep 553321 = 414991) (by norm_num)
theorem B1241477 : Blo 435777 1241477 := bbase (se 4 (by rfl) ⟨116388, by rfl⟩ : syracuseStep 1241477 = 232777) (by norm_num)
theorem B1110469 : Blo 435777 1110469 := bbase (se 4 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 1110469 = 208213) (by norm_num)
theorem B1667573 : Blo 435777 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B553493 : Blo 435777 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B1471013 : Blo 435777 1471013 := bbase (se 4 (by rfl) ⟨137907, by rfl⟩ : syracuseStep 1471013 = 275815) (by norm_num)
theorem B1110581 : Blo 435777 1110581 := bbase (se 5 (by rfl) ⟨52058, by rfl⟩ : syracuseStep 1110581 = 104117) (by norm_num)
theorem B1241669 : Blo 435777 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B553549 : Blo 435777 553549 := bbase (se 3 (by rfl) ⟨103790, by rfl⟩ : syracuseStep 553549 = 207581) (by norm_num)
theorem B553645 : Blo 435777 553645 := bbase (se 3 (by rfl) ⟨103808, by rfl⟩ : syracuseStep 553645 = 207617) (by norm_num)
theorem B1110773 : Blo 435777 1110773 := bbase (se 5 (by rfl) ⟨52067, by rfl⟩ : syracuseStep 1110773 = 104135) (by norm_num)
theorem B1667861 : Blo 435777 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B553817 : Blo 435777 553817 := bbase (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) (by norm_num)
theorem B914309 : Blo 435777 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B553873 : Blo 435777 553873 := bbase (se 2 (by rfl) ⟨207702, by rfl⟩ : syracuseStep 553873 = 415405) (by norm_num)
theorem B1078181 : Blo 435777 1078181 := bbase (se 4 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 1078181 = 202159) (by norm_num)
theorem B1471445 : Blo 435777 1471445 := bbase (se 7 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 1471445 = 34487) (by norm_num)
theorem B553969 : Blo 435777 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B1111117 : Blo 435777 1111117 := bbase (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) (by norm_num)
theorem B947285 : Blo 435777 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B521321 : Blo 435777 521321 := bbase (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) (by norm_num)
theorem B554141 : Blo 435777 554141 := bbase (se 3 (by rfl) ⟨103901, by rfl⟩ : syracuseStep 554141 = 207803) (by norm_num)
theorem B1111229 : Blo 435777 1111229 := bbase (se 3 (by rfl) ⟨208355, by rfl⟩ : syracuseStep 1111229 = 416711) (by norm_num)
theorem B2487509 : Blo 435777 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B554197 : Blo 435777 554197 := bbase (se 7 (by rfl) ⟨6494, by rfl⟩ : syracuseStep 554197 = 12989) (by norm_num)
theorem B554293 : Blo 435777 554293 := bbase (se 5 (by rfl) ⟨25982, by rfl⟩ : syracuseStep 554293 = 51965) (by norm_num)
theorem B1111421 : Blo 435777 1111421 := bbase (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) (by norm_num)
theorem B1471877 : Blo 435777 1471877 := bbase (se 4 (by rfl) ⟨137988, by rfl⟩ : syracuseStep 1471877 = 275977) (by norm_num)
theorem B554465 : Blo 435777 554465 := bbase (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) (by norm_num)
theorem B554521 : Blo 435777 554521 := bbase (se 2 (by rfl) ⟨207945, by rfl⟩ : syracuseStep 554521 = 415891) (by norm_num)
theorem B1242661 : Blo 435777 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B2225717 : Blo 435777 2225717 := bbase (se 5 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 2225717 = 208661) (by norm_num)
theorem B980549 : Blo 435777 980549 := bbase (se 4 (by rfl) ⟨91926, by rfl⟩ : syracuseStep 980549 = 183853) (by norm_num)
theorem B1898101 : Blo 435777 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B554617 : Blo 435777 554617 := bbase (se 2 (by rfl) ⟨207981, by rfl⟩ : syracuseStep 554617 = 415963) (by norm_num)
theorem B980621 : Blo 435777 980621 := bbase (se 3 (by rfl) ⟨183866, by rfl⟩ : syracuseStep 980621 = 367733) (by norm_num)
theorem B980693 : Blo 435777 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B1111765 : Blo 435777 1111765 := bbase (se 7 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 1111765 = 26057) (by norm_num)
theorem B980765 : Blo 435777 980765 := bbase (se 3 (by rfl) ⟨183893, by rfl⟩ : syracuseStep 980765 = 367787) (by norm_num)
theorem B554789 : Blo 435777 554789 := bbase (se 4 (by rfl) ⟨52011, by rfl⟩ : syracuseStep 554789 = 104023) (by norm_num)
theorem B1472309 : Blo 435777 1472309 := bbase (se 5 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 1472309 = 138029) (by norm_num)
theorem B1111877 : Blo 435777 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B554845 : Blo 435777 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B980837 : Blo 435777 980837 := bbase (se 4 (by rfl) ⟨91953, by rfl⟩ : syracuseStep 980837 = 183907) (by norm_num)
theorem B980909 : Blo 435777 980909 := bbase (se 3 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 980909 = 367841) (by norm_num)
theorem B1669045 : Blo 435777 1669045 := bbase (se 5 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 1669045 = 156473) (by norm_num)
theorem B554941 : Blo 435777 554941 := bbase (se 3 (by rfl) ⟨104051, by rfl⟩ : syracuseStep 554941 = 208103) (by norm_num)
theorem B980981 : Blo 435777 980981 := bbase (se 5 (by rfl) ⟨45983, by rfl⟩ : syracuseStep 980981 = 91967) (by norm_num)
theorem B1865717 : Blo 435777 1865717 := bbase (se 5 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 1865717 = 174911) (by norm_num)
theorem B1112069 : Blo 435777 1112069 := bbase (se 4 (by rfl) ⟨104256, by rfl⟩ : syracuseStep 1112069 = 208513) (by norm_num)
theorem B981053 : Blo 435777 981053 := bbase (se 3 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 981053 = 367895) (by norm_num)
theorem B555113 : Blo 435777 555113 := bbase (se 2 (by rfl) ⟨208167, by rfl⟩ : syracuseStep 555113 = 416335) (by norm_num)
theorem B2652277 : Blo 435777 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B981125 : Blo 435777 981125 := bbase (se 4 (by rfl) ⟨91980, by rfl⟩ : syracuseStep 981125 = 183961) (by norm_num)
theorem B555169 : Blo 435777 555169 := bbase (se 2 (by rfl) ⟨208188, by rfl⟩ : syracuseStep 555169 = 416377) (by norm_num)
theorem B981197 : Blo 435777 981197 := bbase (se 3 (by rfl) ⟨183974, by rfl⟩ : syracuseStep 981197 = 367949) (by norm_num)
theorem B1472741 : Blo 435777 1472741 := bbase (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) (by norm_num)
theorem B1669349 : Blo 435777 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B620789 : Blo 435777 620789 := bbase (se 5 (by rfl) ⟨29099, by rfl⟩ : syracuseStep 620789 = 58199) (by norm_num)
theorem B555265 : Blo 435777 555265 := bbase (se 2 (by rfl) ⟨208224, by rfl⟩ : syracuseStep 555265 = 416449) (by norm_num)
theorem B981269 : Blo 435777 981269 := bbase (se 6 (by rfl) ⟨22998, by rfl⟩ : syracuseStep 981269 = 45997) (by norm_num)
theorem B2816309 : Blo 435777 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B981341 : Blo 435777 981341 := bbase (se 3 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 981341 = 368003) (by norm_num)
theorem B1112413 : Blo 435777 1112413 := bbase (se 3 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 1112413 = 417155) (by norm_num)
theorem B653669 : Blo 435777 653669 := bbase (se 4 (by rfl) ⟨61281, by rfl⟩ : syracuseStep 653669 = 122563) (by norm_num)
theorem B653693 : Blo 435777 653693 := bbase (se 3 (by rfl) ⟨122567, by rfl⟩ : syracuseStep 653693 = 245135) (by norm_num)
theorem B653717 : Blo 435777 653717 := bbase (se 6 (by rfl) ⟨15321, by rfl⟩ : syracuseStep 653717 = 30643) (by norm_num)
theorem B981413 : Blo 435777 981413 := bbase (se 4 (by rfl) ⟨92007, by rfl⟩ : syracuseStep 981413 = 184015) (by norm_num)
theorem B653741 : Blo 435777 653741 := bbase (se 3 (by rfl) ⟨122576, by rfl⟩ : syracuseStep 653741 = 245153) (by norm_num)
theorem B555437 : Blo 435777 555437 := bbase (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) (by norm_num)
theorem B1800629 : Blo 435777 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B653765 : Blo 435777 653765 := bbase (se 4 (by rfl) ⟨61290, by rfl⟩ : syracuseStep 653765 = 122581) (by norm_num)
theorem B1112525 : Blo 435777 1112525 := bbase (se 3 (by rfl) ⟨208598, by rfl⟩ : syracuseStep 1112525 = 417197) (by norm_num)
theorem B653789 : Blo 435777 653789 := bbase (se 3 (by rfl) ⟨122585, by rfl⟩ : syracuseStep 653789 = 245171) (by norm_num)
theorem B555493 : Blo 435777 555493 := bbase (se 4 (by rfl) ⟨52077, by rfl⟩ : syracuseStep 555493 = 104155) (by norm_num)
theorem B981485 : Blo 435777 981485 := bbase (se 3 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 981485 = 368057) (by norm_num)
theorem B653813 : Blo 435777 653813 := bbase (se 5 (by rfl) ⟨30647, by rfl⟩ : syracuseStep 653813 = 61295) (by norm_num)
theorem B653837 : Blo 435777 653837 := bbase (se 3 (by rfl) ⟨122594, by rfl⟩ : syracuseStep 653837 = 245189) (by norm_num)
theorem B653861 : Blo 435777 653861 := bbase (se 4 (by rfl) ⟨61299, by rfl⟩ : syracuseStep 653861 = 122599) (by norm_num)
theorem B981557 : Blo 435777 981557 := bbase (se 5 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 981557 = 92021) (by norm_num)
theorem B653885 : Blo 435777 653885 := bbase (se 3 (by rfl) ⟨122603, by rfl⟩ : syracuseStep 653885 = 245207) (by norm_num)
theorem B555589 : Blo 435777 555589 := bbase (se 4 (by rfl) ⟨52086, by rfl⟩ : syracuseStep 555589 = 104173) (by norm_num)
theorem B653909 : Blo 435777 653909 := bbase (se 8 (by rfl) ⟨3831, by rfl⟩ : syracuseStep 653909 = 7663) (by norm_num)
theorem B653933 : Blo 435777 653933 := bbase (se 3 (by rfl) ⟨122612, by rfl⟩ : syracuseStep 653933 = 245225) (by norm_num)
theorem B1243765 : Blo 435777 1243765 := bbase (se 5 (by rfl) ⟨58301, by rfl⟩ : syracuseStep 1243765 = 116603) (by norm_num)
theorem B981629 : Blo 435777 981629 := bbase (se 3 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 981629 = 368111) (by norm_num)
theorem B653957 : Blo 435777 653957 := bbase (se 4 (by rfl) ⟨61308, by rfl⟩ : syracuseStep 653957 = 122617) (by norm_num)
theorem B1112717 : Blo 435777 1112717 := bbase (se 3 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 1112717 = 417269) (by norm_num)
theorem B1473173 : Blo 435777 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B653981 : Blo 435777 653981 := bbase (se 3 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 653981 = 245243) (by norm_num)
theorem B654005 : Blo 435777 654005 := bbase (se 5 (by rfl) ⟨30656, by rfl⟩ : syracuseStep 654005 = 61313) (by norm_num)
theorem B981701 : Blo 435777 981701 := bbase (se 4 (by rfl) ⟨92034, by rfl⟩ : syracuseStep 981701 = 184069) (by norm_num)
theorem B654029 : Blo 435777 654029 := bbase (se 3 (by rfl) ⟨122630, by rfl⟩ : syracuseStep 654029 = 245261) (by norm_num)
theorem B654053 : Blo 435777 654053 := bbase (se 4 (by rfl) ⟨61317, by rfl⟩ : syracuseStep 654053 = 122635) (by norm_num)
theorem B555761 : Blo 435777 555761 := bbase (se 2 (by rfl) ⟨208410, by rfl⟩ : syracuseStep 555761 = 416821) (by norm_num)
theorem B654077 : Blo 435777 654077 := bbase (se 3 (by rfl) ⟨122639, by rfl⟩ : syracuseStep 654077 = 245279) (by norm_num)
theorem B981773 : Blo 435777 981773 := bbase (se 3 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 981773 = 368165) (by norm_num)
theorem B490261 : Blo 435777 490261 := bbase (se 6 (by rfl) ⟨11490, by rfl⟩ : syracuseStep 490261 = 22981) (by norm_num)
theorem B654101 : Blo 435777 654101 := bbase (se 6 (by rfl) ⟨15330, by rfl⟩ : syracuseStep 654101 = 30661) (by norm_num)
theorem B555817 : Blo 435777 555817 := bbase (se 2 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 555817 = 416863) (by norm_num)
theorem B654125 : Blo 435777 654125 := bbase (se 3 (by rfl) ⟨122648, by rfl⟩ : syracuseStep 654125 = 245297) (by norm_num)
theorem B490297 : Blo 435777 490297 := bbase (se 2 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 490297 = 367723) (by norm_num)
theorem B654149 : Blo 435777 654149 := bbase (se 4 (by rfl) ⟨61326, by rfl⟩ : syracuseStep 654149 = 122653) (by norm_num)
theorem B981845 : Blo 435777 981845 := bbase (se 9 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 981845 = 5753) (by norm_num)
theorem B490333 : Blo 435777 490333 := bbase (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) (by norm_num)
theorem B654173 : Blo 435777 654173 := bbase (se 3 (by rfl) ⟨122657, by rfl⟩ : syracuseStep 654173 = 245315) (by norm_num)
theorem B654197 : Blo 435777 654197 := bbase (se 5 (by rfl) ⟨30665, by rfl⟩ : syracuseStep 654197 = 61331) (by norm_num)
theorem B490369 : Blo 435777 490369 := bbase (se 2 (by rfl) ⟨183888, by rfl⟩ : syracuseStep 490369 = 367777) (by norm_num)
theorem B555913 : Blo 435777 555913 := bbase (se 2 (by rfl) ⟨208467, by rfl⟩ : syracuseStep 555913 = 416935) (by norm_num)
theorem B654221 : Blo 435777 654221 := bbase (se 3 (by rfl) ⟨122666, by rfl⟩ : syracuseStep 654221 = 245333) (by norm_num)
theorem B981917 : Blo 435777 981917 := bbase (se 3 (by rfl) ⟨184109, by rfl⟩ : syracuseStep 981917 = 368219) (by norm_num)
theorem B490405 : Blo 435777 490405 := bbase (se 4 (by rfl) ⟨45975, by rfl⟩ : syracuseStep 490405 = 91951) (by norm_num)
theorem B654245 : Blo 435777 654245 := bbase (se 4 (by rfl) ⟨61335, by rfl⟩ : syracuseStep 654245 = 122671) (by norm_num)
theorem B654269 : Blo 435777 654269 := bbase (se 3 (by rfl) ⟨122675, by rfl⟩ : syracuseStep 654269 = 245351) (by norm_num)
theorem B490441 : Blo 435777 490441 := bbase (se 2 (by rfl) ⟨183915, by rfl⟩ : syracuseStep 490441 = 367831) (by norm_num)
theorem B654293 : Blo 435777 654293 := bbase (se 7 (by rfl) ⟨7667, by rfl⟩ : syracuseStep 654293 = 15335) (by norm_num)
theorem B981989 : Blo 435777 981989 := bbase (se 4 (by rfl) ⟨92061, by rfl⟩ : syracuseStep 981989 = 184123) (by norm_num)
theorem B621541 : Blo 435777 621541 := bbase (se 4 (by rfl) ⟨58269, by rfl⟩ : syracuseStep 621541 = 116539) (by norm_num)
theorem B1113061 : Blo 435777 1113061 := bbase (se 4 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 1113061 = 208699) (by norm_num)
theorem B490477 : Blo 435777 490477 := bbase (se 3 (by rfl) ⟨91964, by rfl⟩ : syracuseStep 490477 = 183929) (by norm_num)
theorem B654317 : Blo 435777 654317 := bbase (se 3 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 654317 = 245369) (by norm_num)
theorem B654341 : Blo 435777 654341 := bbase (se 4 (by rfl) ⟨61344, by rfl⟩ : syracuseStep 654341 = 122689) (by norm_num)
theorem B490513 : Blo 435777 490513 := bbase (se 2 (by rfl) ⟨183942, by rfl⟩ : syracuseStep 490513 = 367885) (by norm_num)
theorem B654365 : Blo 435777 654365 := bbase (se 3 (by rfl) ⟨122693, by rfl⟩ : syracuseStep 654365 = 245387) (by norm_num)
theorem B982061 : Blo 435777 982061 := bbase (se 3 (by rfl) ⟨184136, by rfl⟩ : syracuseStep 982061 = 368273) (by norm_num)
theorem B490549 : Blo 435777 490549 := bbase (se 5 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 490549 = 45989) (by norm_num)
theorem B654389 : Blo 435777 654389 := bbase (se 5 (by rfl) ⟨30674, by rfl⟩ : syracuseStep 654389 = 61349) (by norm_num)
theorem B556085 : Blo 435777 556085 := bbase (se 5 (by rfl) ⟨26066, by rfl⟩ : syracuseStep 556085 = 52133) (by norm_num)
theorem B1473605 : Blo 435777 1473605 := bbase (se 4 (by rfl) ⟨138150, by rfl⟩ : syracuseStep 1473605 = 276301) (by norm_num)
theorem B1997893 : Blo 435777 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B654413 : Blo 435777 654413 := bbase (se 3 (by rfl) ⟨122702, by rfl⟩ : syracuseStep 654413 = 245405) (by norm_num)
theorem B1113173 : Blo 435777 1113173 := bbase (se 8 (by rfl) ⟨6522, by rfl⟩ : syracuseStep 1113173 = 13045) (by norm_num)
theorem B490585 : Blo 435777 490585 := bbase (se 2 (by rfl) ⟨183969, by rfl⟩ : syracuseStep 490585 = 367939) (by norm_num)
theorem B654437 : Blo 435777 654437 := bbase (se 4 (by rfl) ⟨61353, by rfl⟩ : syracuseStep 654437 = 122707) (by norm_num)
theorem B556141 : Blo 435777 556141 := bbase (se 3 (by rfl) ⟨104276, by rfl⟩ : syracuseStep 556141 = 208553) (by norm_num)
theorem B982133 : Blo 435777 982133 := bbase (se 5 (by rfl) ⟨46037, by rfl⟩ : syracuseStep 982133 = 92075) (by norm_num)
theorem B490621 : Blo 435777 490621 := bbase (se 3 (by rfl) ⟨91991, by rfl⟩ : syracuseStep 490621 = 183983) (by norm_num)
theorem B654461 : Blo 435777 654461 := bbase (se 3 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 654461 = 245423) (by norm_num)
theorem B654485 : Blo 435777 654485 := bbase (se 6 (by rfl) ⟨15339, by rfl⟩ : syracuseStep 654485 = 30679) (by norm_num)
theorem B2522261 : Blo 435777 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B490657 : Blo 435777 490657 := bbase (se 2 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 490657 = 367993) (by norm_num)
theorem B654509 : Blo 435777 654509 := bbase (se 3 (by rfl) ⟨122720, by rfl⟩ : syracuseStep 654509 = 245441) (by norm_num)
theorem B982205 : Blo 435777 982205 := bbase (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) (by norm_num)
theorem B490693 : Blo 435777 490693 := bbase (se 4 (by rfl) ⟨46002, by rfl⟩ : syracuseStep 490693 = 92005) (by norm_num)
theorem B654533 : Blo 435777 654533 := bbase (se 4 (by rfl) ⟨61362, by rfl⟩ : syracuseStep 654533 = 122725) (by norm_num)
theorem B556237 : Blo 435777 556237 := bbase (se 3 (by rfl) ⟨104294, by rfl⟩ : syracuseStep 556237 = 208589) (by norm_num)
theorem B654557 : Blo 435777 654557 := bbase (se 3 (by rfl) ⟨122729, by rfl⟩ : syracuseStep 654557 = 245459) (by norm_num)
theorem B490729 : Blo 435777 490729 := bbase (se 2 (by rfl) ⟨184023, by rfl⟩ : syracuseStep 490729 = 368047) (by norm_num)
theorem B654581 : Blo 435777 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B982277 : Blo 435777 982277 := bbase (se 4 (by rfl) ⟨92088, by rfl⟩ : syracuseStep 982277 = 184177) (by norm_num)
theorem B490765 : Blo 435777 490765 := bbase (se 3 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 490765 = 184037) (by norm_num)
theorem B654605 : Blo 435777 654605 := bbase (se 3 (by rfl) ⟨122738, by rfl⟩ : syracuseStep 654605 = 245477) (by norm_num)
theorem B654629 : Blo 435777 654629 := bbase (se 4 (by rfl) ⟨61371, by rfl⟩ : syracuseStep 654629 = 122743) (by norm_num)
theorem B490801 : Blo 435777 490801 := bbase (se 2 (by rfl) ⟨184050, by rfl⟩ : syracuseStep 490801 = 368101) (by norm_num)
theorem B654653 : Blo 435777 654653 := bbase (se 3 (by rfl) ⟨122747, by rfl⟩ : syracuseStep 654653 = 245495) (by norm_num)
theorem B982349 : Blo 435777 982349 := bbase (se 3 (by rfl) ⟨184190, by rfl⟩ : syracuseStep 982349 = 368381) (by norm_num)
theorem B490837 : Blo 435777 490837 := bbase (se 11 (by rfl) ⟨359, by rfl⟩ : syracuseStep 490837 = 719) (by norm_num)
theorem B654677 : Blo 435777 654677 := bbase (se 11 (by rfl) ⟨479, by rfl⟩ : syracuseStep 654677 = 959) (by norm_num)
theorem B654701 : Blo 435777 654701 := bbase (se 3 (by rfl) ⟨122756, by rfl⟩ : syracuseStep 654701 = 245513) (by norm_num)
theorem B523633 : Blo 435777 523633 := bbase (se 2 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 523633 = 392725) (by norm_num)
theorem B2489717 : Blo 435777 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B490873 : Blo 435777 490873 := bbase (se 2 (by rfl) ⟨184077, by rfl⟩ : syracuseStep 490873 = 368155) (by norm_num)
theorem B556409 : Blo 435777 556409 := bbase (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) (by norm_num)
theorem B654725 : Blo 435777 654725 := bbase (se 4 (by rfl) ⟨61380, by rfl⟩ : syracuseStep 654725 = 122761) (by norm_num)
theorem B982421 : Blo 435777 982421 := bbase (se 6 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 982421 = 46051) (by norm_num)
theorem B490909 : Blo 435777 490909 := bbase (se 3 (by rfl) ⟨92045, by rfl⟩ : syracuseStep 490909 = 184091) (by norm_num)
theorem B654749 : Blo 435777 654749 := bbase (se 3 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 654749 = 245531) (by norm_num)
theorem B2096549 : Blo 435777 2096549 := bbase (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) (by norm_num)
theorem B556465 : Blo 435777 556465 := bbase (se 2 (by rfl) ⟨208674, by rfl⟩ : syracuseStep 556465 = 417349) (by norm_num)
theorem B654773 : Blo 435777 654773 := bbase (se 5 (by rfl) ⟨30692, by rfl⟩ : syracuseStep 654773 = 61385) (by norm_num)
theorem B490945 : Blo 435777 490945 := bbase (se 2 (by rfl) ⟨184104, by rfl⟩ : syracuseStep 490945 = 368209) (by norm_num)
theorem B654797 : Blo 435777 654797 := bbase (se 3 (by rfl) ⟨122774, by rfl⟩ : syracuseStep 654797 = 245549) (by norm_num)
theorem B982493 : Blo 435777 982493 := bbase (se 3 (by rfl) ⟨184217, by rfl⟩ : syracuseStep 982493 = 368435) (by norm_num)
theorem B490981 : Blo 435777 490981 := bbase (se 4 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 490981 = 92059) (by norm_num)
theorem B654821 : Blo 435777 654821 := bbase (se 4 (by rfl) ⟨61389, by rfl⟩ : syracuseStep 654821 = 122779) (by norm_num)
theorem B1474037 : Blo 435777 1474037 := bbase (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) (by norm_num)
theorem B654845 : Blo 435777 654845 := bbase (se 3 (by rfl) ⟨122783, by rfl⟩ : syracuseStep 654845 = 245567) (by norm_num)
theorem B491017 : Blo 435777 491017 := bbase (se 2 (by rfl) ⟨184131, by rfl⟩ : syracuseStep 491017 = 368263) (by norm_num)
theorem B785933 : Blo 435777 785933 := bbase (se 3 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 785933 = 294725) (by norm_num)
theorem B556561 : Blo 435777 556561 := bbase (se 2 (by rfl) ⟨208710, by rfl⟩ : syracuseStep 556561 = 417421) (by norm_num)
theorem B654869 : Blo 435777 654869 := bbase (se 6 (by rfl) ⟨15348, by rfl⟩ : syracuseStep 654869 = 30697) (by norm_num)
theorem B982565 : Blo 435777 982565 := bbase (se 4 (by rfl) ⟨92115, by rfl⟩ : syracuseStep 982565 = 184231) (by norm_num)
theorem B491053 : Blo 435777 491053 := bbase (se 3 (by rfl) ⟨92072, by rfl⟩ : syracuseStep 491053 = 184145) (by norm_num)
theorem B654893 : Blo 435777 654893 := bbase (se 3 (by rfl) ⟨122792, by rfl⟩ : syracuseStep 654893 = 245585) (by norm_num)
theorem B1408565 : Blo 435777 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B654917 : Blo 435777 654917 := bbase (se 4 (by rfl) ⟨61398, by rfl⟩ : syracuseStep 654917 = 122797) (by norm_num)
theorem B491089 : Blo 435777 491089 := bbase (se 2 (by rfl) ⟨184158, by rfl⟩ : syracuseStep 491089 = 368317) (by norm_num)
theorem B654941 : Blo 435777 654941 := bbase (se 3 (by rfl) ⟨122801, by rfl⟩ : syracuseStep 654941 = 245603) (by norm_num)
theorem B2096741 : Blo 435777 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B982637 : Blo 435777 982637 := bbase (se 3 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 982637 = 368489) (by norm_num)
theorem B491125 : Blo 435777 491125 := bbase (se 5 (by rfl) ⟨23021, by rfl⟩ : syracuseStep 491125 = 46043) (by norm_num)
theorem B654965 : Blo 435777 654965 := bbase (se 5 (by rfl) ⟨30701, by rfl⟩ : syracuseStep 654965 = 61403) (by norm_num)
theorem B654989 : Blo 435777 654989 := bbase (se 3 (by rfl) ⟨122810, by rfl⟩ : syracuseStep 654989 = 245621) (by norm_num)
theorem B491161 : Blo 435777 491161 := bbase (se 2 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 491161 = 368371) (by norm_num)
theorem B655013 : Blo 435777 655013 := bbase (se 4 (by rfl) ⟨61407, by rfl⟩ : syracuseStep 655013 = 122815) (by norm_num)
theorem B523945 : Blo 435777 523945 := bbase (se 2 (by rfl) ⟨196479, by rfl⟩ : syracuseStep 523945 = 392959) (by norm_num)
theorem B982709 : Blo 435777 982709 := bbase (se 5 (by rfl) ⟨46064, by rfl⟩ : syracuseStep 982709 = 92129) (by norm_num)
theorem B491197 : Blo 435777 491197 := bbase (se 3 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 491197 = 184199) (by norm_num)
theorem B655037 : Blo 435777 655037 := bbase (se 3 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 655037 = 245639) (by norm_num)
theorem B655061 : Blo 435777 655061 := bbase (se 7 (by rfl) ⟨7676, by rfl⟩ : syracuseStep 655061 = 15353) (by norm_num)
theorem B491233 : Blo 435777 491233 := bbase (se 2 (by rfl) ⟨184212, by rfl⟩ : syracuseStep 491233 = 368425) (by norm_num)
theorem B655085 : Blo 435777 655085 := bbase (se 3 (by rfl) ⟨122828, by rfl⟩ : syracuseStep 655085 = 245657) (by norm_num)
theorem B982781 : Blo 435777 982781 := bbase (se 3 (by rfl) ⟨184271, by rfl⟩ : syracuseStep 982781 = 368543) (by norm_num)
theorem B622333 : Blo 435777 622333 := bbase (se 3 (by rfl) ⟨116687, by rfl⟩ : syracuseStep 622333 = 233375) (by norm_num)
theorem B491269 : Blo 435777 491269 := bbase (se 4 (by rfl) ⟨46056, by rfl⟩ : syracuseStep 491269 = 92113) (by norm_num)
theorem B655109 : Blo 435777 655109 := bbase (se 4 (by rfl) ⟨61416, by rfl⟩ : syracuseStep 655109 = 122833) (by norm_num)
theorem B655133 : Blo 435777 655133 := bbase (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) (by norm_num)
theorem B491305 : Blo 435777 491305 := bbase (se 2 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 491305 = 368479) (by norm_num)
theorem B655157 : Blo 435777 655157 := bbase (se 5 (by rfl) ⟨30710, by rfl⟩ : syracuseStep 655157 = 61421) (by norm_num)
theorem B982853 : Blo 435777 982853 := bbase (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) (by norm_num)
theorem B491341 : Blo 435777 491341 := bbase (se 3 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 491341 = 184253) (by norm_num)
theorem B655181 : Blo 435777 655181 := bbase (se 3 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 655181 = 245693) (by norm_num)
theorem B655205 : Blo 435777 655205 := bbase (se 4 (by rfl) ⟨61425, by rfl⟩ : syracuseStep 655205 = 122851) (by norm_num)
theorem B491377 : Blo 435777 491377 := bbase (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) (by norm_num)
theorem B655229 : Blo 435777 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B982925 : Blo 435777 982925 := bbase (se 3 (by rfl) ⟨184298, by rfl⟩ : syracuseStep 982925 = 368597) (by norm_num)
theorem B491413 : Blo 435777 491413 := bbase (se 6 (by rfl) ⟨11517, by rfl⟩ : syracuseStep 491413 = 23035) (by norm_num)
theorem B655253 : Blo 435777 655253 := bbase (se 6 (by rfl) ⟨15357, by rfl⟩ : syracuseStep 655253 = 30715) (by norm_num)
theorem B1474469 : Blo 435777 1474469 := bbase (se 4 (by rfl) ⟨138231, by rfl⟩ : syracuseStep 1474469 = 276463) (by norm_num)
theorem B655277 : Blo 435777 655277 := bbase (se 3 (by rfl) ⟨122864, by rfl⟩ : syracuseStep 655277 = 245729) (by norm_num)
theorem B491449 : Blo 435777 491449 := bbase (se 2 (by rfl) ⟨184293, by rfl⟩ : syracuseStep 491449 = 368587) (by norm_num)
theorem B655301 : Blo 435777 655301 := bbase (se 4 (by rfl) ⟨61434, by rfl⟩ : syracuseStep 655301 = 122869) (by norm_num)
theorem B884693 : Blo 435777 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B982997 : Blo 435777 982997 := bbase (se 7 (by rfl) ⟨11519, by rfl⟩ : syracuseStep 982997 = 23039) (by norm_num)
theorem B491485 : Blo 435777 491485 := bbase (se 3 (by rfl) ⟨92153, by rfl⟩ : syracuseStep 491485 = 184307) (by norm_num)
theorem B655325 : Blo 435777 655325 := bbase (se 3 (by rfl) ⟨122873, by rfl⟩ : syracuseStep 655325 = 245747) (by norm_num)
theorem B655349 : Blo 435777 655349 := bbase (se 5 (by rfl) ⟨30719, by rfl⟩ : syracuseStep 655349 = 61439) (by norm_num)
theorem B655361 : Blo 435777 655361 := bstep (se 2 (by rfl) ⟨245760, by rfl⟩ : syracuseStep 655361 = 491521) B491521
theorem B1474577 : Blo 435777 1474577 := bstep (se 2 (by rfl) ⟨552966, by rfl⟩ : syracuseStep 1474577 = 1105933) B1105933
theorem B655379 : Blo 435777 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B491539 : Blo 435777 491539 := bstep (se 1 (by rfl) ⟨368654, by rfl⟩ : syracuseStep 491539 = 737309) B737309
theorem B655409 : Blo 435777 655409 := bstep (se 2 (by rfl) ⟨245778, by rfl⟩ : syracuseStep 655409 = 491557) B491557
theorem B622657 : Blo 435777 622657 := bstep (se 2 (by rfl) ⟨233496, by rfl⟩ : syracuseStep 622657 = 466993) B466993
theorem B655427 : Blo 435777 655427 := bstep (se 1 (by rfl) ⟨491570, by rfl⟩ : syracuseStep 655427 = 983141) B983141
theorem B655457 : Blo 435777 655457 := bstep (se 2 (by rfl) ⟨245796, by rfl⟩ : syracuseStep 655457 = 491593) B491593
theorem B655475 : Blo 435777 655475 := bstep (se 1 (by rfl) ⟨491606, by rfl⟩ : syracuseStep 655475 = 983213) B983213
theorem B655505 : Blo 435777 655505 := bstep (se 2 (by rfl) ⟨245814, by rfl⟩ : syracuseStep 655505 = 491629) B491629
theorem B655523 : Blo 435777 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B491683 : Blo 435777 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B655553 : Blo 435777 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B983249 : Blo 435777 983249 := bstep (se 2 (by rfl) ⟨368718, by rfl⟩ : syracuseStep 983249 = 737437) B737437
theorem B655571 : Blo 435777 655571 := bstep (se 1 (by rfl) ⟨491678, by rfl⟩ : syracuseStep 655571 = 983357) B983357
theorem B40337621 : Blo 435777 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B1573091 : Blo 435777 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B983267 : Blo 435777 983267 := bstep (se 1 (by rfl) ⟨737450, by rfl⟩ : syracuseStep 983267 = 1474901) B1474901
theorem B655601 : Blo 435777 655601 := bstep (se 2 (by rfl) ⟨245850, by rfl⟩ : syracuseStep 655601 = 491701) B491701
theorem B655619 : Blo 435777 655619 := bstep (se 1 (by rfl) ⟨491714, by rfl⟩ : syracuseStep 655619 = 983429) B983429
theorem B655649 : Blo 435777 655649 := bstep (se 2 (by rfl) ⟨245868, by rfl⟩ : syracuseStep 655649 = 491737) B491737
theorem B655667 : Blo 435777 655667 := bstep (se 1 (by rfl) ⟨491750, by rfl⟩ : syracuseStep 655667 = 983501) B983501
theorem B491827 : Blo 435777 491827 := bstep (se 1 (by rfl) ⟨368870, by rfl⟩ : syracuseStep 491827 = 737741) B737741
theorem B655697 : Blo 435777 655697 := bstep (se 2 (by rfl) ⟨245886, by rfl⟩ : syracuseStep 655697 = 491773) B491773
theorem B655715 : Blo 435777 655715 := bstep (se 1 (by rfl) ⟨491786, by rfl⟩ : syracuseStep 655715 = 983573) B983573
theorem B655745 : Blo 435777 655745 := bstep (se 2 (by rfl) ⟨245904, by rfl⟩ : syracuseStep 655745 = 491809) B491809
theorem B655763 : Blo 435777 655763 := bstep (se 1 (by rfl) ⟨491822, by rfl⟩ : syracuseStep 655763 = 983645) B983645
theorem B655793 : Blo 435777 655793 := bstep (se 2 (by rfl) ⟨245922, by rfl⟩ : syracuseStep 655793 = 491845) B491845
theorem B655811 : Blo 435777 655811 := bstep (se 1 (by rfl) ⟨491858, by rfl⟩ : syracuseStep 655811 = 983717) B983717
theorem B491971 : Blo 435777 491971 := bstep (se 1 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 491971 = 737957) B737957
theorem B1180109 : Blo 435777 1180109 := bstep (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) B442541
theorem B655841 : Blo 435777 655841 := bstep (se 2 (by rfl) ⟨245940, by rfl⟩ : syracuseStep 655841 = 491881) B491881
theorem B4194787 : Blo 435777 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B983537 : Blo 435777 983537 := bstep (se 2 (by rfl) ⟨368826, by rfl⟩ : syracuseStep 983537 = 737653) B737653
theorem B655859 : Blo 435777 655859 := bstep (se 1 (by rfl) ⟨491894, by rfl⟩ : syracuseStep 655859 = 983789) B983789
theorem B983555 : Blo 435777 983555 := bstep (se 1 (by rfl) ⟨737666, by rfl⟩ : syracuseStep 983555 = 1475333) B1475333
theorem B655889 : Blo 435777 655889 := bstep (se 2 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 655889 = 491917) B491917
theorem B655907 : Blo 435777 655907 := bstep (se 1 (by rfl) ⟨491930, by rfl⟩ : syracuseStep 655907 = 983861) B983861
theorem B1475117 : Blo 435777 1475117 := bstep (se 3 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 1475117 = 553169) B553169
theorem B623153 : Blo 435777 623153 := bstep (se 2 (by rfl) ⟨233682, by rfl⟩ : syracuseStep 623153 = 467365) B467365
theorem B655937 : Blo 435777 655937 := bstep (se 2 (by rfl) ⟨245976, by rfl⟩ : syracuseStep 655937 = 491953) B491953
theorem B655955 : Blo 435777 655955 := bstep (se 1 (by rfl) ⟨491966, by rfl⟩ : syracuseStep 655955 = 983933) B983933
theorem B492115 : Blo 435777 492115 := bstep (se 1 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 492115 = 738173) B738173
theorem B1475171 : Blo 435777 1475171 := bstep (se 1 (by rfl) ⟨1106378, by rfl⟩ : syracuseStep 1475171 = 2212757) B2212757
theorem B655985 : Blo 435777 655985 := bstep (se 2 (by rfl) ⟨245994, by rfl⟩ : syracuseStep 655985 = 491989) B491989
theorem B656003 : Blo 435777 656003 := bstep (se 1 (by rfl) ⟨492002, by rfl⟩ : syracuseStep 656003 = 984005) B984005
theorem B656033 : Blo 435777 656033 := bstep (se 2 (by rfl) ⟨246012, by rfl⟩ : syracuseStep 656033 = 492025) B492025
theorem B656051 : Blo 435777 656051 := bstep (se 1 (by rfl) ⟨492038, by rfl⟩ : syracuseStep 656051 = 984077) B984077
theorem B656081 : Blo 435777 656081 := bstep (se 2 (by rfl) ⟨246030, by rfl⟩ : syracuseStep 656081 = 492061) B492061
theorem B656099 : Blo 435777 656099 := bstep (se 1 (by rfl) ⟨492074, by rfl⟩ : syracuseStep 656099 = 984149) B984149
theorem B492259 : Blo 435777 492259 := bstep (se 1 (by rfl) ⟨369194, by rfl⟩ : syracuseStep 492259 = 738389) B738389
theorem B656129 : Blo 435777 656129 := bstep (se 2 (by rfl) ⟨246048, by rfl⟩ : syracuseStep 656129 = 492097) B492097
theorem B983825 : Blo 435777 983825 := bstep (se 2 (by rfl) ⟨368934, by rfl⟩ : syracuseStep 983825 = 737869) B737869
theorem B656147 : Blo 435777 656147 := bstep (se 1 (by rfl) ⟨492110, by rfl⟩ : syracuseStep 656147 = 984221) B984221
theorem B983843 : Blo 435777 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B656177 : Blo 435777 656177 := bstep (se 2 (by rfl) ⟨246066, by rfl⟩ : syracuseStep 656177 = 492133) B492133
theorem B656195 : Blo 435777 656195 := bstep (se 1 (by rfl) ⟨492146, by rfl⟩ : syracuseStep 656195 = 984293) B984293
theorem B656225 : Blo 435777 656225 := bstep (se 2 (by rfl) ⟨246084, by rfl⟩ : syracuseStep 656225 = 492169) B492169
theorem B1475441 : Blo 435777 1475441 := bstep (se 2 (by rfl) ⟨553290, by rfl⟩ : syracuseStep 1475441 = 1106581) B1106581
theorem B656243 : Blo 435777 656243 := bstep (se 1 (by rfl) ⟨492182, by rfl⟩ : syracuseStep 656243 = 984365) B984365
theorem B492403 : Blo 435777 492403 := bstep (se 1 (by rfl) ⟨369302, by rfl⟩ : syracuseStep 492403 = 738605) B738605
theorem B4752269 : Blo 435777 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B885649 : Blo 435777 885649 := bstep (se 2 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 885649 = 664237) B664237
theorem B656273 : Blo 435777 656273 := bstep (se 2 (by rfl) ⟨246102, by rfl⟩ : syracuseStep 656273 = 492205) B492205
theorem B656291 : Blo 435777 656291 := bstep (se 1 (by rfl) ⟨492218, by rfl⟩ : syracuseStep 656291 = 984437) B984437
theorem B656321 : Blo 435777 656321 := bstep (se 2 (by rfl) ⟨246120, by rfl⟩ : syracuseStep 656321 = 492241) B492241
theorem B656339 : Blo 435777 656339 := bstep (se 1 (by rfl) ⟨492254, by rfl⟩ : syracuseStep 656339 = 984509) B984509
theorem B656369 : Blo 435777 656369 := bstep (se 2 (by rfl) ⟨246138, by rfl⟩ : syracuseStep 656369 = 492277) B492277
theorem B656387 : Blo 435777 656387 := bstep (se 1 (by rfl) ⟨492290, by rfl⟩ : syracuseStep 656387 = 984581) B984581
theorem B492547 : Blo 435777 492547 := bstep (se 1 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 492547 = 738821) B738821
theorem B656417 : Blo 435777 656417 := bstep (se 2 (by rfl) ⟨246156, by rfl⟩ : syracuseStep 656417 = 492313) B492313
theorem B984113 : Blo 435777 984113 := bstep (se 2 (by rfl) ⟨369042, by rfl⟩ : syracuseStep 984113 = 738085) B738085
theorem B656435 : Blo 435777 656435 := bstep (se 1 (by rfl) ⟨492326, by rfl⟩ : syracuseStep 656435 = 984653) B984653
theorem B984131 : Blo 435777 984131 := bstep (se 1 (by rfl) ⟨738098, by rfl⟩ : syracuseStep 984131 = 1476197) B1476197
theorem B656465 : Blo 435777 656465 := bstep (se 2 (by rfl) ⟨246174, by rfl⟩ : syracuseStep 656465 = 492349) B492349
theorem B656483 : Blo 435777 656483 := bstep (se 1 (by rfl) ⟨492362, by rfl⟩ : syracuseStep 656483 = 984725) B984725
theorem B656513 : Blo 435777 656513 := bstep (se 2 (by rfl) ⟨246192, by rfl⟩ : syracuseStep 656513 = 492385) B492385
theorem B590995 : Blo 435777 590995 := bstep (se 1 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 590995 = 886493) B886493
theorem B656531 : Blo 435777 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B492691 : Blo 435777 492691 := bstep (se 1 (by rfl) ⟨369518, by rfl⟩ : syracuseStep 492691 = 739037) B739037
theorem B656561 : Blo 435777 656561 := bstep (se 2 (by rfl) ⟨246210, by rfl⟩ : syracuseStep 656561 = 492421) B492421
theorem B656579 : Blo 435777 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B656609 : Blo 435777 656609 := bstep (se 2 (by rfl) ⟨246228, by rfl⟩ : syracuseStep 656609 = 492457) B492457
theorem B656627 : Blo 435777 656627 := bstep (se 1 (by rfl) ⟨492470, by rfl⟩ : syracuseStep 656627 = 984941) B984941
theorem B656657 : Blo 435777 656657 := bstep (se 2 (by rfl) ⟨246246, by rfl⟩ : syracuseStep 656657 = 492493) B492493
theorem B1246499 : Blo 435777 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B656675 : Blo 435777 656675 := bstep (se 1 (by rfl) ⟨492506, by rfl⟩ : syracuseStep 656675 = 985013) B985013
theorem B492835 : Blo 435777 492835 := bstep (se 1 (by rfl) ⟨369626, by rfl⟩ : syracuseStep 492835 = 739253) B739253
theorem B656705 : Blo 435777 656705 := bstep (se 2 (by rfl) ⟨246264, by rfl⟩ : syracuseStep 656705 = 492529) B492529
theorem B984401 : Blo 435777 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B656723 : Blo 435777 656723 := bstep (se 1 (by rfl) ⟨492542, by rfl⟩ : syracuseStep 656723 = 985085) B985085
theorem B984419 : Blo 435777 984419 := bstep (se 1 (by rfl) ⟨738314, by rfl⟩ : syracuseStep 984419 = 1476629) B1476629
theorem B656753 : Blo 435777 656753 := bstep (se 2 (by rfl) ⟨246282, by rfl⟩ : syracuseStep 656753 = 492565) B492565
theorem B656771 : Blo 435777 656771 := bstep (se 1 (by rfl) ⟨492578, by rfl⟩ : syracuseStep 656771 = 985157) B985157
theorem B1475981 : Blo 435777 1475981 := bstep (se 3 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 1475981 = 553493) B553493
theorem B624019 : Blo 435777 624019 := bstep (se 1 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 624019 = 936029) B936029
theorem B656801 : Blo 435777 656801 := bstep (se 2 (by rfl) ⟨246300, by rfl⟩ : syracuseStep 656801 = 492601) B492601
theorem B656819 : Blo 435777 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B492979 : Blo 435777 492979 := bstep (se 1 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 492979 = 739469) B739469
theorem B787907 : Blo 435777 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1476035 : Blo 435777 1476035 := bstep (se 1 (by rfl) ⟨1107026, by rfl⟩ : syracuseStep 1476035 = 2214053) B2214053
theorem B656849 : Blo 435777 656849 := bstep (se 2 (by rfl) ⟨246318, by rfl⟩ : syracuseStep 656849 = 492637) B492637
theorem B656867 : Blo 435777 656867 := bstep (se 1 (by rfl) ⟨492650, by rfl⟩ : syracuseStep 656867 = 985301) B985301
theorem B624115 : Blo 435777 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B656897 : Blo 435777 656897 := bstep (se 2 (by rfl) ⟨246336, by rfl⟩ : syracuseStep 656897 = 492673) B492673
theorem B3311117 : Blo 435777 3311117 := bstep (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) B1241669
theorem B656915 : Blo 435777 656915 := bstep (se 1 (by rfl) ⟨492686, by rfl⟩ : syracuseStep 656915 = 985373) B985373
theorem B656945 : Blo 435777 656945 := bstep (se 2 (by rfl) ⟨246354, by rfl⟩ : syracuseStep 656945 = 492709) B492709
theorem B656963 : Blo 435777 656963 := bstep (se 1 (by rfl) ⟨492722, by rfl⟩ : syracuseStep 656963 = 985445) B985445
theorem B493123 : Blo 435777 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B656993 : Blo 435777 656993 := bstep (se 2 (by rfl) ⟨246372, by rfl⟩ : syracuseStep 656993 = 492745) B492745
theorem B984689 : Blo 435777 984689 := bstep (se 2 (by rfl) ⟨369258, by rfl⟩ : syracuseStep 984689 = 738517) B738517
theorem B657011 : Blo 435777 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B984707 : Blo 435777 984707 := bstep (se 1 (by rfl) ⟨738530, by rfl⟩ : syracuseStep 984707 = 1477061) B1477061
theorem B657041 : Blo 435777 657041 := bstep (se 2 (by rfl) ⟨246390, by rfl⟩ : syracuseStep 657041 = 492781) B492781
theorem B1869475 : Blo 435777 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B657059 : Blo 435777 657059 := bstep (se 1 (by rfl) ⟨492794, by rfl⟩ : syracuseStep 657059 = 985589) B985589
theorem B657089 : Blo 435777 657089 := bstep (se 2 (by rfl) ⟨246408, by rfl⟩ : syracuseStep 657089 = 492817) B492817
theorem B1476305 : Blo 435777 1476305 := bstep (se 2 (by rfl) ⟨553614, by rfl⟩ : syracuseStep 1476305 = 1107229) B1107229
theorem B657107 : Blo 435777 657107 := bstep (se 1 (by rfl) ⟨492830, by rfl⟩ : syracuseStep 657107 = 985661) B985661
theorem B493267 : Blo 435777 493267 := bstep (se 1 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 493267 = 739901) B739901
theorem B657137 : Blo 435777 657137 := bstep (se 2 (by rfl) ⟨246426, by rfl⟩ : syracuseStep 657137 = 492853) B492853
theorem B1050371 : Blo 435777 1050371 := bstep (se 1 (by rfl) ⟨787778, by rfl⟩ : syracuseStep 1050371 = 1575557) B1575557
theorem B657155 : Blo 435777 657155 := bstep (se 1 (by rfl) ⟨492866, by rfl⟩ : syracuseStep 657155 = 985733) B985733
theorem B952067 : Blo 435777 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B657185 : Blo 435777 657185 := bstep (se 2 (by rfl) ⟨246444, by rfl⟩ : syracuseStep 657185 = 492889) B492889
theorem B657203 : Blo 435777 657203 := bstep (se 1 (by rfl) ⟨492902, by rfl⟩ : syracuseStep 657203 = 985805) B985805
theorem B3147589 : Blo 435777 3147589 := bstep (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) B590173
theorem B657233 : Blo 435777 657233 := bstep (se 2 (by rfl) ⟨246462, by rfl⟩ : syracuseStep 657233 = 492925) B492925
theorem B493411 : Blo 435777 493411 := bstep (se 1 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 493411 = 740117) B740117
theorem B657251 : Blo 435777 657251 := bstep (se 1 (by rfl) ⟨492938, by rfl⟩ : syracuseStep 657251 = 985877) B985877
theorem B657281 : Blo 435777 657281 := bstep (se 2 (by rfl) ⟨246480, by rfl⟩ : syracuseStep 657281 = 492961) B492961
theorem B984977 : Blo 435777 984977 := bstep (se 2 (by rfl) ⟨369366, by rfl⟩ : syracuseStep 984977 = 738733) B738733
theorem B657299 : Blo 435777 657299 := bstep (se 1 (by rfl) ⟨492974, by rfl⟩ : syracuseStep 657299 = 985949) B985949
theorem B984995 : Blo 435777 984995 := bstep (se 1 (by rfl) ⟨738746, by rfl⟩ : syracuseStep 984995 = 1477493) B1477493
theorem B657329 : Blo 435777 657329 := bstep (se 2 (by rfl) ⟨246498, by rfl⟩ : syracuseStep 657329 = 492997) B492997
theorem B657347 : Blo 435777 657347 := bstep (se 1 (by rfl) ⟨493010, by rfl⟩ : syracuseStep 657347 = 986021) B986021
theorem B657377 : Blo 435777 657377 := bstep (se 2 (by rfl) ⟨246516, by rfl⟩ : syracuseStep 657377 = 493033) B493033
theorem B624611 : Blo 435777 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B657395 : Blo 435777 657395 := bstep (se 1 (by rfl) ⟨493046, by rfl⟩ : syracuseStep 657395 = 986093) B986093
theorem B493555 : Blo 435777 493555 := bstep (se 1 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 493555 = 740333) B740333
theorem B657425 : Blo 435777 657425 := bstep (se 2 (by rfl) ⟨246534, by rfl⟩ : syracuseStep 657425 = 493069) B493069
theorem B657443 : Blo 435777 657443 := bstep (se 1 (by rfl) ⟨493082, by rfl⟩ : syracuseStep 657443 = 986165) B986165
theorem B657473 : Blo 435777 657473 := bstep (se 2 (by rfl) ⟨246552, by rfl⟩ : syracuseStep 657473 = 493105) B493105
theorem B1247309 : Blo 435777 1247309 := bstep (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) B467741
theorem B657491 : Blo 435777 657491 := bstep (se 1 (by rfl) ⟨493118, by rfl⟩ : syracuseStep 657491 = 986237) B986237
theorem B657521 : Blo 435777 657521 := bstep (se 2 (by rfl) ⟨246570, by rfl⟩ : syracuseStep 657521 = 493141) B493141
theorem B657539 : Blo 435777 657539 := bstep (se 1 (by rfl) ⟨493154, by rfl⟩ : syracuseStep 657539 = 986309) B986309
theorem B493699 : Blo 435777 493699 := bstep (se 1 (by rfl) ⟨370274, by rfl⟩ : syracuseStep 493699 = 740549) B740549
theorem B657569 : Blo 435777 657569 := bstep (se 2 (by rfl) ⟨246588, by rfl⟩ : syracuseStep 657569 = 493177) B493177
theorem B985265 : Blo 435777 985265 := bstep (se 2 (by rfl) ⟨369474, by rfl⟩ : syracuseStep 985265 = 738949) B738949
theorem B657587 : Blo 435777 657587 := bstep (se 1 (by rfl) ⟨493190, by rfl⟩ : syracuseStep 657587 = 986381) B986381
theorem B985283 : Blo 435777 985283 := bstep (se 1 (by rfl) ⟨738962, by rfl⟩ : syracuseStep 985283 = 1477925) B1477925
theorem B657617 : Blo 435777 657617 := bstep (se 2 (by rfl) ⟨246606, by rfl⟩ : syracuseStep 657617 = 493213) B493213
theorem B657635 : Blo 435777 657635 := bstep (se 1 (by rfl) ⟨493226, by rfl⟩ : syracuseStep 657635 = 986453) B986453
theorem B1476845 : Blo 435777 1476845 := bstep (se 3 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 1476845 = 553817) B553817
theorem B592115 : Blo 435777 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B657665 : Blo 435777 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B1247501 : Blo 435777 1247501 := bstep (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) B467813
theorem B657683 : Blo 435777 657683 := bstep (se 1 (by rfl) ⟨493262, by rfl⟩ : syracuseStep 657683 = 986525) B986525
theorem B493843 : Blo 435777 493843 := bstep (se 1 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 493843 = 740765) B740765
theorem B1476899 : Blo 435777 1476899 := bstep (se 1 (by rfl) ⟨1107674, by rfl⟩ : syracuseStep 1476899 = 2215349) B2215349
theorem B657713 : Blo 435777 657713 := bstep (se 2 (by rfl) ⟨246642, by rfl⟩ : syracuseStep 657713 = 493285) B493285
theorem B657731 : Blo 435777 657731 := bstep (se 1 (by rfl) ⟨493298, by rfl⟩ : syracuseStep 657731 = 986597) B986597
theorem B657761 : Blo 435777 657761 := bstep (se 2 (by rfl) ⟨246660, by rfl⟩ : syracuseStep 657761 = 493321) B493321
theorem B657779 : Blo 435777 657779 := bstep (se 1 (by rfl) ⟨493334, by rfl⟩ : syracuseStep 657779 = 986669) B986669
theorem B657809 : Blo 435777 657809 := bstep (se 2 (by rfl) ⟨246678, by rfl⟩ : syracuseStep 657809 = 493357) B493357
theorem B657827 : Blo 435777 657827 := bstep (se 1 (by rfl) ⟨493370, by rfl⟩ : syracuseStep 657827 = 986741) B986741
theorem B493987 : Blo 435777 493987 := bstep (se 1 (by rfl) ⟨370490, by rfl⟩ : syracuseStep 493987 = 740981) B740981
theorem B526771 : Blo 435777 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B657857 : Blo 435777 657857 := bstep (se 2 (by rfl) ⟨246696, by rfl⟩ : syracuseStep 657857 = 493393) B493393
theorem B723395 : Blo 435777 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B788945 : Blo 435777 788945 := bstep (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) B591709
theorem B985553 : Blo 435777 985553 := bstep (se 2 (by rfl) ⟨369582, by rfl⟩ : syracuseStep 985553 = 739165) B739165
theorem B657875 : Blo 435777 657875 := bstep (se 1 (by rfl) ⟨493406, by rfl⟩ : syracuseStep 657875 = 986813) B986813
theorem B985571 : Blo 435777 985571 := bstep (se 1 (by rfl) ⟨739178, by rfl⟩ : syracuseStep 985571 = 1478357) B1478357
theorem B657905 : Blo 435777 657905 := bstep (se 2 (by rfl) ⟨246714, by rfl⟩ : syracuseStep 657905 = 493429) B493429
theorem B1051139 : Blo 435777 1051139 := bstep (se 1 (by rfl) ⟨788354, by rfl⟩ : syracuseStep 1051139 = 1576709) B1576709
theorem B657923 : Blo 435777 657923 := bstep (se 1 (by rfl) ⟨493442, by rfl⟩ : syracuseStep 657923 = 986885) B986885
theorem B657953 : Blo 435777 657953 := bstep (se 2 (by rfl) ⟨246732, by rfl⟩ : syracuseStep 657953 = 493465) B493465
theorem B2361905 : Blo 435777 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1477169 : Blo 435777 1477169 := bstep (se 2 (by rfl) ⟨553938, by rfl⟩ : syracuseStep 1477169 = 1107877) B1107877
theorem B657971 : Blo 435777 657971 := bstep (se 1 (by rfl) ⟨493478, by rfl⟩ : syracuseStep 657971 = 986957) B986957
theorem B494131 : Blo 435777 494131 := bstep (se 1 (by rfl) ⟨370598, by rfl⟩ : syracuseStep 494131 = 741197) B741197
theorem B526915 : Blo 435777 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B658001 : Blo 435777 658001 := bstep (se 2 (by rfl) ⟨246750, by rfl⟩ : syracuseStep 658001 = 493501) B493501
theorem B625249 : Blo 435777 625249 := bstep (se 2 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 625249 = 468937) B468937
theorem B658019 : Blo 435777 658019 := bstep (se 1 (by rfl) ⟨493514, by rfl⟩ : syracuseStep 658019 = 987029) B987029
theorem B658049 : Blo 435777 658049 := bstep (se 2 (by rfl) ⟨246768, by rfl⟩ : syracuseStep 658049 = 493537) B493537
theorem B658067 : Blo 435777 658067 := bstep (se 1 (by rfl) ⟨493550, by rfl⟩ : syracuseStep 658067 = 987101) B987101
theorem B658097 : Blo 435777 658097 := bstep (se 2 (by rfl) ⟨246786, by rfl⟩ : syracuseStep 658097 = 493573) B493573
theorem B658115 : Blo 435777 658115 := bstep (se 1 (by rfl) ⟨493586, by rfl⟩ : syracuseStep 658115 = 987173) B987173
theorem B494275 : Blo 435777 494275 := bstep (se 1 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 494275 = 741413) B741413
theorem B658145 : Blo 435777 658145 := bstep (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) B493609
theorem B985841 : Blo 435777 985841 := bstep (se 2 (by rfl) ⟨369690, by rfl⟩ : syracuseStep 985841 = 739381) B739381
theorem B658163 : Blo 435777 658163 := bstep (se 1 (by rfl) ⟨493622, by rfl⟩ : syracuseStep 658163 = 987245) B987245
theorem B985859 : Blo 435777 985859 := bstep (se 1 (by rfl) ⟨739394, by rfl⟩ : syracuseStep 985859 = 1478789) B1478789
theorem B658193 : Blo 435777 658193 := bstep (se 2 (by rfl) ⟨246822, by rfl⟩ : syracuseStep 658193 = 493645) B493645
theorem B658211 : Blo 435777 658211 := bstep (se 1 (by rfl) ⟨493658, by rfl⟩ : syracuseStep 658211 = 987317) B987317
theorem B658241 : Blo 435777 658241 := bstep (se 2 (by rfl) ⟨246840, by rfl⟩ : syracuseStep 658241 = 493681) B493681
theorem B658259 : Blo 435777 658259 := bstep (se 1 (by rfl) ⟨493694, by rfl⟩ : syracuseStep 658259 = 987389) B987389
theorem B494419 : Blo 435777 494419 := bstep (se 1 (by rfl) ⟨370814, by rfl⟩ : syracuseStep 494419 = 741629) B741629
theorem B2657123 : Blo 435777 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B1870705 : Blo 435777 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B658289 : Blo 435777 658289 := bstep (se 2 (by rfl) ⟨246858, by rfl⟩ : syracuseStep 658289 = 493717) B493717
theorem B1182595 : Blo 435777 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B658307 : Blo 435777 658307 := bstep (se 1 (by rfl) ⟨493730, by rfl⟩ : syracuseStep 658307 = 987461) B987461
theorem B2886533 : Blo 435777 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B658337 : Blo 435777 658337 := bstep (se 2 (by rfl) ⟨246876, by rfl⟩ : syracuseStep 658337 = 493753) B493753
theorem B625585 : Blo 435777 625585 := bstep (se 2 (by rfl) ⟨234594, by rfl⟩ : syracuseStep 625585 = 469189) B469189
theorem B658355 : Blo 435777 658355 := bstep (se 1 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 658355 = 987533) B987533
theorem B658385 : Blo 435777 658385 := bstep (se 2 (by rfl) ⟨246894, by rfl⟩ : syracuseStep 658385 = 493789) B493789
theorem B658403 : Blo 435777 658403 := bstep (se 1 (by rfl) ⟨493802, by rfl⟩ : syracuseStep 658403 = 987605) B987605
theorem B494563 : Blo 435777 494563 := bstep (se 1 (by rfl) ⟨370922, by rfl⟩ : syracuseStep 494563 = 741845) B741845
theorem B658433 : Blo 435777 658433 := bstep (se 2 (by rfl) ⟨246912, by rfl⟩ : syracuseStep 658433 = 493825) B493825
theorem B986129 : Blo 435777 986129 := bstep (se 2 (by rfl) ⟨369798, by rfl⟩ : syracuseStep 986129 = 739597) B739597
theorem B658451 : Blo 435777 658451 := bstep (se 1 (by rfl) ⟨493838, by rfl⟩ : syracuseStep 658451 = 987677) B987677
theorem B986147 : Blo 435777 986147 := bstep (se 1 (by rfl) ⟨739610, by rfl⟩ : syracuseStep 986147 = 1479221) B1479221
theorem B1051697 : Blo 435777 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B658481 : Blo 435777 658481 := bstep (se 2 (by rfl) ⟨246930, by rfl⟩ : syracuseStep 658481 = 493861) B493861
theorem B658499 : Blo 435777 658499 := bstep (se 1 (by rfl) ⟨493874, by rfl⟩ : syracuseStep 658499 = 987749) B987749
theorem B1477709 : Blo 435777 1477709 := bstep (se 3 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 1477709 = 554141) B554141
theorem B658529 : Blo 435777 658529 := bstep (se 2 (by rfl) ⟨246948, by rfl⟩ : syracuseStep 658529 = 493897) B493897
theorem B658547 : Blo 435777 658547 := bstep (se 1 (by rfl) ⟨493910, by rfl⟩ : syracuseStep 658547 = 987821) B987821
theorem B494707 : Blo 435777 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B1477763 : Blo 435777 1477763 := bstep (se 1 (by rfl) ⟨1108322, by rfl⟩ : syracuseStep 1477763 = 2216645) B2216645
theorem B658577 : Blo 435777 658577 := bstep (se 2 (by rfl) ⟨246966, by rfl⟩ : syracuseStep 658577 = 493933) B493933
theorem B658595 : Blo 435777 658595 := bstep (se 1 (by rfl) ⟨493946, by rfl⟩ : syracuseStep 658595 = 987893) B987893
theorem B658625 : Blo 435777 658625 := bstep (se 2 (by rfl) ⟨246984, by rfl⟩ : syracuseStep 658625 = 493969) B493969
theorem B658643 : Blo 435777 658643 := bstep (se 1 (by rfl) ⟨493982, by rfl⟩ : syracuseStep 658643 = 987965) B987965
theorem B2985187 : Blo 435777 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B1248493 : Blo 435777 1248493 := bstep (se 3 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 1248493 = 468185) B468185
theorem B658673 : Blo 435777 658673 := bstep (se 2 (by rfl) ⟨247002, by rfl⟩ : syracuseStep 658673 = 494005) B494005
theorem B658691 : Blo 435777 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B1576205 : Blo 435777 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B658721 : Blo 435777 658721 := bstep (se 2 (by rfl) ⟨247020, by rfl⟩ : syracuseStep 658721 = 494041) B494041
theorem B986417 : Blo 435777 986417 := bstep (se 2 (by rfl) ⟨369906, by rfl⟩ : syracuseStep 986417 = 739813) B739813
theorem B658739 : Blo 435777 658739 := bstep (se 1 (by rfl) ⟨494054, by rfl⟩ : syracuseStep 658739 = 988109) B988109
theorem B986435 : Blo 435777 986435 := bstep (se 1 (by rfl) ⟨739826, by rfl⟩ : syracuseStep 986435 = 1479653) B1479653
theorem B2493773 : Blo 435777 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B658769 : Blo 435777 658769 := bstep (se 2 (by rfl) ⟨247038, by rfl⟩ : syracuseStep 658769 = 494077) B494077
theorem B658787 : Blo 435777 658787 := bstep (se 1 (by rfl) ⟨494090, by rfl⟩ : syracuseStep 658787 = 988181) B988181
theorem B658817 : Blo 435777 658817 := bstep (se 2 (by rfl) ⟨247056, by rfl⟩ : syracuseStep 658817 = 494113) B494113
theorem B1478033 : Blo 435777 1478033 := bstep (se 2 (by rfl) ⟨554262, by rfl⟩ : syracuseStep 1478033 = 1108525) B1108525
theorem B658835 : Blo 435777 658835 := bstep (se 1 (by rfl) ⟨494126, by rfl⟩ : syracuseStep 658835 = 988253) B988253
theorem B1052081 : Blo 435777 1052081 := bstep (se 2 (by rfl) ⟨394530, by rfl⟩ : syracuseStep 1052081 = 789061) B789061
theorem B658865 : Blo 435777 658865 := bstep (se 2 (by rfl) ⟨247074, by rfl⟩ : syracuseStep 658865 = 494149) B494149
theorem B658883 : Blo 435777 658883 := bstep (se 1 (by rfl) ⟨494162, by rfl⟩ : syracuseStep 658883 = 988325) B988325
theorem B658913 : Blo 435777 658913 := bstep (se 2 (by rfl) ⟨247092, by rfl⟩ : syracuseStep 658913 = 494185) B494185
theorem B560611 : Blo 435777 560611 := bstep (se 1 (by rfl) ⟨420458, by rfl⟩ : syracuseStep 560611 = 840917) B840917
theorem B658931 : Blo 435777 658931 := bstep (se 1 (by rfl) ⟨494198, by rfl⟩ : syracuseStep 658931 = 988397) B988397
theorem B658961 : Blo 435777 658961 := bstep (se 2 (by rfl) ⟨247110, by rfl⟩ : syracuseStep 658961 = 494221) B494221
theorem B1052195 : Blo 435777 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B658979 : Blo 435777 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B659009 : Blo 435777 659009 := bstep (se 2 (by rfl) ⟨247128, by rfl⟩ : syracuseStep 659009 = 494257) B494257
theorem B986705 : Blo 435777 986705 := bstep (se 2 (by rfl) ⟨370014, by rfl⟩ : syracuseStep 986705 = 740029) B740029
theorem B659027 : Blo 435777 659027 := bstep (se 1 (by rfl) ⟨494270, by rfl⟩ : syracuseStep 659027 = 988541) B988541
theorem B986723 : Blo 435777 986723 := bstep (se 1 (by rfl) ⟨740042, by rfl⟩ : syracuseStep 986723 = 1480085) B1480085
theorem B659057 : Blo 435777 659057 := bstep (se 2 (by rfl) ⟨247146, by rfl⟩ : syracuseStep 659057 = 494293) B494293
theorem B659075 : Blo 435777 659075 := bstep (se 1 (by rfl) ⟨494306, by rfl⟩ : syracuseStep 659075 = 988613) B988613
theorem B659105 : Blo 435777 659105 := bstep (se 2 (by rfl) ⟨247164, by rfl⟩ : syracuseStep 659105 = 494329) B494329
theorem B659123 : Blo 435777 659123 := bstep (se 1 (by rfl) ⟨494342, by rfl⟩ : syracuseStep 659123 = 988685) B988685
theorem B1052369 : Blo 435777 1052369 := bstep (se 2 (by rfl) ⟨394638, by rfl⟩ : syracuseStep 1052369 = 789277) B789277
theorem B659153 : Blo 435777 659153 := bstep (se 2 (by rfl) ⟨247182, by rfl⟩ : syracuseStep 659153 = 494365) B494365
theorem B593633 : Blo 435777 593633 := bstep (se 2 (by rfl) ⟨222612, by rfl⟩ : syracuseStep 593633 = 445225) B445225
theorem B659171 : Blo 435777 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B659201 : Blo 435777 659201 := bstep (se 2 (by rfl) ⟨247200, by rfl⟩ : syracuseStep 659201 = 494401) B494401
theorem B659219 : Blo 435777 659219 := bstep (se 1 (by rfl) ⟨494414, by rfl⟩ : syracuseStep 659219 = 988829) B988829
theorem B659249 : Blo 435777 659249 := bstep (se 2 (by rfl) ⟨247218, by rfl⟩ : syracuseStep 659249 = 494437) B494437
theorem B659267 : Blo 435777 659267 := bstep (se 1 (by rfl) ⟨494450, by rfl⟩ : syracuseStep 659267 = 988901) B988901
theorem B659297 : Blo 435777 659297 := bstep (se 2 (by rfl) ⟨247236, by rfl⟩ : syracuseStep 659297 = 494473) B494473
theorem B986993 : Blo 435777 986993 := bstep (se 2 (by rfl) ⟨370122, by rfl⟩ : syracuseStep 986993 = 740245) B740245
theorem B659315 : Blo 435777 659315 := bstep (se 1 (by rfl) ⟨494486, by rfl⟩ : syracuseStep 659315 = 988973) B988973
theorem B987011 : Blo 435777 987011 := bstep (se 1 (by rfl) ⟨740258, by rfl⟩ : syracuseStep 987011 = 1480517) B1480517
theorem B2527109 : Blo 435777 2527109 := bstep (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) B473833
theorem B659345 : Blo 435777 659345 := bstep (se 2 (by rfl) ⟨247254, by rfl⟩ : syracuseStep 659345 = 494509) B494509
theorem B659363 : Blo 435777 659363 := bstep (se 1 (by rfl) ⟨494522, by rfl⟩ : syracuseStep 659363 = 989045) B989045
theorem B1478573 : Blo 435777 1478573 := bstep (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) B554465
theorem B659393 : Blo 435777 659393 := bstep (se 2 (by rfl) ⟨247272, by rfl⟩ : syracuseStep 659393 = 494545) B494545
theorem B659411 : Blo 435777 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B1773539 : Blo 435777 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B1478627 : Blo 435777 1478627 := bstep (se 1 (by rfl) ⟨1108970, by rfl⟩ : syracuseStep 1478627 = 2217941) B2217941
theorem B659441 : Blo 435777 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B659459 : Blo 435777 659459 := bstep (se 1 (by rfl) ⟨494594, by rfl⟩ : syracuseStep 659459 = 989189) B989189
theorem B659489 : Blo 435777 659489 := bstep (se 2 (by rfl) ⟨247308, by rfl⟩ : syracuseStep 659489 = 494617) B494617
theorem B2101297 : Blo 435777 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B659507 : Blo 435777 659507 := bstep (se 1 (by rfl) ⟨494630, by rfl⟩ : syracuseStep 659507 = 989261) B989261
theorem B4984901 : Blo 435777 4984901 := bstep (se 4 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 4984901 = 934669) B934669
theorem B659537 : Blo 435777 659537 := bstep (se 2 (by rfl) ⟨247326, by rfl⟩ : syracuseStep 659537 = 494653) B494653
theorem B659555 : Blo 435777 659555 := bstep (se 1 (by rfl) ⟨494666, by rfl⟩ : syracuseStep 659555 = 989333) B989333
theorem B659585 : Blo 435777 659585 := bstep (se 2 (by rfl) ⟨247344, by rfl⟩ : syracuseStep 659585 = 494689) B494689
theorem B987281 : Blo 435777 987281 := bstep (se 2 (by rfl) ⟨370230, by rfl⟩ : syracuseStep 987281 = 740461) B740461
theorem B659603 : Blo 435777 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B987299 : Blo 435777 987299 := bstep (se 1 (by rfl) ⟨740474, by rfl⟩ : syracuseStep 987299 = 1480949) B1480949
theorem B659633 : Blo 435777 659633 := bstep (se 2 (by rfl) ⟨247362, by rfl⟩ : syracuseStep 659633 = 494725) B494725
theorem B659651 : Blo 435777 659651 := bstep (se 1 (by rfl) ⟨494738, by rfl⟩ : syracuseStep 659651 = 989477) B989477
theorem B1478897 : Blo 435777 1478897 := bstep (se 2 (by rfl) ⟨554586, by rfl⟩ : syracuseStep 1478897 = 1109173) B1109173
theorem B3314033 : Blo 435777 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B987569 : Blo 435777 987569 := bstep (se 2 (by rfl) ⟨370338, by rfl⟩ : syracuseStep 987569 = 740677) B740677
theorem B987587 : Blo 435777 987587 := bstep (se 1 (by rfl) ⟨740690, by rfl⟩ : syracuseStep 987587 = 1481381) B1481381
theorem B1577485 : Blo 435777 1577485 := bstep (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) B591557
theorem B1348177 : Blo 435777 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B12030605 : Blo 435777 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B4264645 : Blo 435777 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B987857 : Blo 435777 987857 := bstep (se 2 (by rfl) ⟨370446, by rfl⟩ : syracuseStep 987857 = 740893) B740893
theorem B987875 : Blo 435777 987875 := bstep (se 1 (by rfl) ⟨740906, by rfl⟩ : syracuseStep 987875 = 1481813) B1481813
theorem B1479437 : Blo 435777 1479437 := bstep (se 3 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 1479437 = 554789) B554789
theorem B1479491 : Blo 435777 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B1250225 : Blo 435777 1250225 := bstep (se 2 (by rfl) ⟨468834, by rfl⟩ : syracuseStep 1250225 = 937669) B937669
theorem B6329315 : Blo 435777 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B988145 : Blo 435777 988145 := bstep (se 2 (by rfl) ⟨370554, by rfl⟩ : syracuseStep 988145 = 741109) B741109
theorem B988163 : Blo 435777 988163 := bstep (se 1 (by rfl) ⟨741122, by rfl⟩ : syracuseStep 988163 = 1482245) B1482245
theorem B791569 : Blo 435777 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B1479761 : Blo 435777 1479761 := bstep (se 2 (by rfl) ⟨554910, by rfl⟩ : syracuseStep 1479761 = 1109821) B1109821
theorem B1250417 : Blo 435777 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B988433 : Blo 435777 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B988451 : Blo 435777 988451 := bstep (se 1 (by rfl) ⟨741338, by rfl⟩ : syracuseStep 988451 = 1482677) B1482677
theorem B1578467 : Blo 435777 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B2496005 : Blo 435777 2496005 := bstep (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) B468001
theorem B988721 : Blo 435777 988721 := bstep (se 2 (by rfl) ⟨370770, by rfl⟩ : syracuseStep 988721 = 741541) B741541
theorem B988739 : Blo 435777 988739 := bstep (se 1 (by rfl) ⟨741554, by rfl⟩ : syracuseStep 988739 = 1483109) B1483109
theorem B1480301 : Blo 435777 1480301 := bstep (se 3 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 1480301 = 555113) B555113
theorem B1480355 : Blo 435777 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B4200133 : Blo 435777 4200133 := bstep (se 4 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 4200133 = 787525) B787525
theorem B1120081 : Blo 435777 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B989009 : Blo 435777 989009 := bstep (se 2 (by rfl) ⟨370878, by rfl⟩ : syracuseStep 989009 = 741757) B741757
theorem B989027 : Blo 435777 989027 := bstep (se 1 (by rfl) ⟨741770, by rfl⟩ : syracuseStep 989027 = 1483541) B1483541
theorem B1480625 : Blo 435777 1480625 := bstep (se 2 (by rfl) ⟨555234, by rfl⟩ : syracuseStep 1480625 = 1110469) B1110469
theorem B11999173 : Blo 435777 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B1251409 : Blo 435777 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B5314673 : Blo 435777 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B989297 : Blo 435777 989297 := bstep (se 2 (by rfl) ⟨370986, by rfl⟩ : syracuseStep 989297 = 741973) B741973
theorem B989315 : Blo 435777 989315 := bstep (se 1 (by rfl) ⟨741986, by rfl⟩ : syracuseStep 989315 = 1483973) B1483973
theorem B7510157 : Blo 435777 7510157 := bstep (se 3 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 7510157 = 2816309) B2816309
theorem B2496689 : Blo 435777 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B1251683 : Blo 435777 1251683 := bstep (se 1 (by rfl) ⟨938762, by rfl⟩ : syracuseStep 1251683 = 1877525) B1877525
theorem B1481165 : Blo 435777 1481165 := bstep (se 3 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 1481165 = 555437) B555437
theorem B1481219 : Blo 435777 1481219 := bstep (se 1 (by rfl) ⟨1110914, by rfl⟩ : syracuseStep 1481219 = 2221829) B2221829
theorem B1251875 : Blo 435777 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B465635 : Blo 435777 465635 := bstep (se 1 (by rfl) ⟨349226, by rfl⟩ : syracuseStep 465635 = 698453) B698453
theorem B1481489 : Blo 435777 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B662627 : Blo 435777 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B1875149 : Blo 435777 1875149 := bstep (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) B703181
theorem B1482029 : Blo 435777 1482029 := bstep (se 3 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 1482029 = 555761) B555761
theorem B662851 : Blo 435777 662851 := bstep (se 1 (by rfl) ⟨497138, by rfl⟩ : syracuseStep 662851 = 994277) B994277
theorem B1482083 : Blo 435777 1482083 := bstep (se 1 (by rfl) ⟨1111562, by rfl⟩ : syracuseStep 1482083 = 2223125) B2223125
theorem B2530801 : Blo 435777 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B630289 : Blo 435777 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B2498147 : Blo 435777 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B1482353 : Blo 435777 1482353 := bstep (se 2 (by rfl) ⟨555882, by rfl⟩ : syracuseStep 1482353 = 1111765) B1111765
theorem B466771 : Blo 435777 466771 := bstep (se 1 (by rfl) ⟨350078, by rfl⟩ : syracuseStep 466771 = 700157) B700157
theorem B3383153 : Blo 435777 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B827491 : Blo 435777 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B1482893 : Blo 435777 1482893 := bstep (se 3 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 1482893 = 556085) B556085
theorem B1482947 : Blo 435777 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B827651 : Blo 435777 827651 := bstep (se 1 (by rfl) ⟨620738, by rfl⟩ : syracuseStep 827651 = 1241477) B1241477
theorem B1483217 : Blo 435777 1483217 := bstep (se 2 (by rfl) ⟨556206, by rfl⟩ : syracuseStep 1483217 = 1112413) B1112413
theorem B1581581 : Blo 435777 1581581 := bstep (se 3 (by rfl) ⟨296546, by rfl⟩ : syracuseStep 1581581 = 593093) B593093
theorem B467651 : Blo 435777 467651 := bstep (se 1 (by rfl) ⟨350738, by rfl⟩ : syracuseStep 467651 = 701477) B701477
theorem B631523 : Blo 435777 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B4268785 : Blo 435777 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B467779 : Blo 435777 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B664481 : Blo 435777 664481 := bstep (se 2 (by rfl) ⟨249180, by rfl⟩ : syracuseStep 664481 = 498361) B498361
theorem B664529 : Blo 435777 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B1483757 : Blo 435777 1483757 := bstep (se 3 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 1483757 = 556409) B556409
theorem B631841 : Blo 435777 631841 := bstep (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) B473881
theorem B1483811 : Blo 435777 1483811 := bstep (se 1 (by rfl) ⟨1112858, by rfl⟩ : syracuseStep 1483811 = 2225717) B2225717
theorem B828721 : Blo 435777 828721 := bstep (se 2 (by rfl) ⟨310770, by rfl⟩ : syracuseStep 828721 = 621541) B621541
theorem B1484081 : Blo 435777 1484081 := bstep (se 2 (by rfl) ⟨556530, by rfl⟩ : syracuseStep 1484081 = 1113061) B1113061
theorem B664979 : Blo 435777 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B2663857 : Blo 435777 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B665059 : Blo 435777 665059 := bstep (se 1 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 665059 = 997589) B997589
theorem B435779 : Blo 435777 435779 := bstep (se 1 (by rfl) ⟨326834, by rfl⟩ : syracuseStep 435779 = 653669) B653669
theorem B435795 : Blo 435777 435795 := bstep (se 1 (by rfl) ⟨326846, by rfl⟩ : syracuseStep 435795 = 653693) B653693
theorem B435811 : Blo 435777 435811 := bstep (se 1 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 435811 = 653717) B653717
theorem B435827 : Blo 435777 435827 := bstep (se 1 (by rfl) ⟨326870, by rfl⟩ : syracuseStep 435827 = 653741) B653741
theorem B468595 : Blo 435777 468595 := bstep (se 1 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 468595 = 702893) B702893
theorem B435843 : Blo 435777 435843 := bstep (se 1 (by rfl) ⟨326882, by rfl⟩ : syracuseStep 435843 = 653765) B653765
theorem B435859 : Blo 435777 435859 := bstep (se 1 (by rfl) ⟨326894, by rfl⟩ : syracuseStep 435859 = 653789) B653789
theorem B435875 : Blo 435777 435875 := bstep (se 1 (by rfl) ⟨326906, by rfl⟩ : syracuseStep 435875 = 653813) B653813
theorem B435891 : Blo 435777 435891 := bstep (se 1 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 435891 = 653837) B653837
theorem B435907 : Blo 435777 435907 := bstep (se 1 (by rfl) ⟨326930, by rfl⟩ : syracuseStep 435907 = 653861) B653861
theorem B435923 : Blo 435777 435923 := bstep (se 1 (by rfl) ⟨326942, by rfl⟩ : syracuseStep 435923 = 653885) B653885
theorem B435939 : Blo 435777 435939 := bstep (se 1 (by rfl) ⟨326954, by rfl⟩ : syracuseStep 435939 = 653909) B653909
theorem B435955 : Blo 435777 435955 := bstep (se 1 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 435955 = 653933) B653933
theorem B435971 : Blo 435777 435971 := bstep (se 1 (by rfl) ⟨326978, by rfl⟩ : syracuseStep 435971 = 653957) B653957
theorem B4990733 : Blo 435777 4990733 := bstep (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) B1871525
theorem B435987 : Blo 435777 435987 := bstep (se 1 (by rfl) ⟨326990, by rfl⟩ : syracuseStep 435987 = 653981) B653981
theorem B436003 : Blo 435777 436003 := bstep (se 1 (by rfl) ⟨327002, by rfl⟩ : syracuseStep 436003 = 654005) B654005
theorem B436019 : Blo 435777 436019 := bstep (se 1 (by rfl) ⟨327014, by rfl⟩ : syracuseStep 436019 = 654029) B654029
theorem B698177 : Blo 435777 698177 := bstep (se 2 (by rfl) ⟨261816, by rfl⟩ : syracuseStep 698177 = 523633) B523633
theorem B436035 : Blo 435777 436035 := bstep (se 1 (by rfl) ⟨327026, by rfl⟩ : syracuseStep 436035 = 654053) B654053
theorem B436051 : Blo 435777 436051 := bstep (se 1 (by rfl) ⟨327038, by rfl⟩ : syracuseStep 436051 = 654077) B654077
theorem B2107235 : Blo 435777 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B436067 : Blo 435777 436067 := bstep (se 1 (by rfl) ⟨327050, by rfl⟩ : syracuseStep 436067 = 654101) B654101
theorem B436083 : Blo 435777 436083 := bstep (se 1 (by rfl) ⟨327062, by rfl⟩ : syracuseStep 436083 = 654125) B654125
theorem B436099 : Blo 435777 436099 := bstep (se 1 (by rfl) ⟨327074, by rfl⟩ : syracuseStep 436099 = 654149) B654149
theorem B436115 : Blo 435777 436115 := bstep (se 1 (by rfl) ⟨327086, by rfl⟩ : syracuseStep 436115 = 654173) B654173
theorem B436131 : Blo 435777 436131 := bstep (se 1 (by rfl) ⟨327098, by rfl⟩ : syracuseStep 436131 = 654197) B654197
theorem B436147 : Blo 435777 436147 := bstep (se 1 (by rfl) ⟨327110, by rfl⟩ : syracuseStep 436147 = 654221) B654221
theorem B436163 : Blo 435777 436163 := bstep (se 1 (by rfl) ⟨327122, by rfl⟩ : syracuseStep 436163 = 654245) B654245
theorem B6301637 : Blo 435777 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B436179 : Blo 435777 436179 := bstep (se 1 (by rfl) ⟨327134, by rfl⟩ : syracuseStep 436179 = 654269) B654269
theorem B436195 : Blo 435777 436195 := bstep (se 1 (by rfl) ⟨327146, by rfl⟩ : syracuseStep 436195 = 654293) B654293
theorem B436211 : Blo 435777 436211 := bstep (se 1 (by rfl) ⟨327158, by rfl⟩ : syracuseStep 436211 = 654317) B654317
theorem B436227 : Blo 435777 436227 := bstep (se 1 (by rfl) ⟨327170, by rfl⟩ : syracuseStep 436227 = 654341) B654341
theorem B436243 : Blo 435777 436243 := bstep (se 1 (by rfl) ⟨327182, by rfl⟩ : syracuseStep 436243 = 654365) B654365
theorem B436259 : Blo 435777 436259 := bstep (se 1 (by rfl) ⟨327194, by rfl⟩ : syracuseStep 436259 = 654389) B654389
theorem B436275 : Blo 435777 436275 := bstep (se 1 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 436275 = 654413) B654413
theorem B436291 : Blo 435777 436291 := bstep (se 1 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 436291 = 654437) B654437
theorem B436307 : Blo 435777 436307 := bstep (se 1 (by rfl) ⟨327230, by rfl⟩ : syracuseStep 436307 = 654461) B654461
theorem B436323 : Blo 435777 436323 := bstep (se 1 (by rfl) ⟨327242, by rfl⟩ : syracuseStep 436323 = 654485) B654485
theorem B1681507 : Blo 435777 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B436339 : Blo 435777 436339 := bstep (se 1 (by rfl) ⟨327254, by rfl⟩ : syracuseStep 436339 = 654509) B654509
theorem B436355 : Blo 435777 436355 := bstep (se 1 (by rfl) ⟨327266, by rfl⟩ : syracuseStep 436355 = 654533) B654533
theorem B436371 : Blo 435777 436371 := bstep (se 1 (by rfl) ⟨327278, by rfl⟩ : syracuseStep 436371 = 654557) B654557
theorem B436387 : Blo 435777 436387 := bstep (se 1 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 436387 = 654581) B654581
theorem B436403 : Blo 435777 436403 := bstep (se 1 (by rfl) ⟨327302, by rfl⟩ : syracuseStep 436403 = 654605) B654605
theorem B436419 : Blo 435777 436419 := bstep (se 1 (by rfl) ⟨327314, by rfl⟩ : syracuseStep 436419 = 654629) B654629
theorem B436435 : Blo 435777 436435 := bstep (se 1 (by rfl) ⟨327326, by rfl⟩ : syracuseStep 436435 = 654653) B654653
theorem B698593 : Blo 435777 698593 := bstep (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) B523945
theorem B436451 : Blo 435777 436451 := bstep (se 1 (by rfl) ⟨327338, by rfl⟩ : syracuseStep 436451 = 654677) B654677
theorem B1714403 : Blo 435777 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B436467 : Blo 435777 436467 := bstep (se 1 (by rfl) ⟨327350, by rfl⟩ : syracuseStep 436467 = 654701) B654701
theorem B436483 : Blo 435777 436483 := bstep (se 1 (by rfl) ⟨327362, by rfl⟩ : syracuseStep 436483 = 654725) B654725
theorem B436499 : Blo 435777 436499 := bstep (se 1 (by rfl) ⟨327374, by rfl⟩ : syracuseStep 436499 = 654749) B654749
theorem B436515 : Blo 435777 436515 := bstep (se 1 (by rfl) ⟨327386, by rfl⟩ : syracuseStep 436515 = 654773) B654773
theorem B436531 : Blo 435777 436531 := bstep (se 1 (by rfl) ⟨327398, by rfl⟩ : syracuseStep 436531 = 654797) B654797
theorem B436547 : Blo 435777 436547 := bstep (se 1 (by rfl) ⟨327410, by rfl⟩ : syracuseStep 436547 = 654821) B654821
theorem B829777 : Blo 435777 829777 := bstep (se 2 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 829777 = 622333) B622333
theorem B436563 : Blo 435777 436563 := bstep (se 1 (by rfl) ⟨327422, by rfl⟩ : syracuseStep 436563 = 654845) B654845
theorem B436579 : Blo 435777 436579 := bstep (se 1 (by rfl) ⟨327434, by rfl⟩ : syracuseStep 436579 = 654869) B654869
theorem B436595 : Blo 435777 436595 := bstep (se 1 (by rfl) ⟨327446, by rfl⟩ : syracuseStep 436595 = 654893) B654893
theorem B436611 : Blo 435777 436611 := bstep (se 1 (by rfl) ⟨327458, by rfl⟩ : syracuseStep 436611 = 654917) B654917
theorem B436627 : Blo 435777 436627 := bstep (se 1 (by rfl) ⟨327470, by rfl⟩ : syracuseStep 436627 = 654941) B654941
theorem B436643 : Blo 435777 436643 := bstep (se 1 (by rfl) ⟨327482, by rfl⟩ : syracuseStep 436643 = 654965) B654965
theorem B436659 : Blo 435777 436659 := bstep (se 1 (by rfl) ⟨327494, by rfl⟩ : syracuseStep 436659 = 654989) B654989
theorem B436675 : Blo 435777 436675 := bstep (se 1 (by rfl) ⟨327506, by rfl⟩ : syracuseStep 436675 = 655013) B655013
theorem B436691 : Blo 435777 436691 := bstep (se 1 (by rfl) ⟨327518, by rfl⟩ : syracuseStep 436691 = 655037) B655037
theorem B436707 : Blo 435777 436707 := bstep (se 1 (by rfl) ⟨327530, by rfl⟩ : syracuseStep 436707 = 655061) B655061
theorem B436723 : Blo 435777 436723 := bstep (se 1 (by rfl) ⟨327542, by rfl⟩ : syracuseStep 436723 = 655085) B655085
theorem B436739 : Blo 435777 436739 := bstep (se 1 (by rfl) ⟨327554, by rfl⟩ : syracuseStep 436739 = 655109) B655109
theorem B436755 : Blo 435777 436755 := bstep (se 1 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 436755 = 655133) B655133
theorem B436771 : Blo 435777 436771 := bstep (se 1 (by rfl) ⟨327578, by rfl⟩ : syracuseStep 436771 = 655157) B655157
theorem B436787 : Blo 435777 436787 := bstep (se 1 (by rfl) ⟨327590, by rfl⟩ : syracuseStep 436787 = 655181) B655181
theorem B436803 : Blo 435777 436803 := bstep (se 1 (by rfl) ⟨327602, by rfl⟩ : syracuseStep 436803 = 655205) B655205
theorem B436819 : Blo 435777 436819 := bstep (se 1 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 436819 = 655229) B655229
theorem B436835 : Blo 435777 436835 := bstep (se 1 (by rfl) ⟨327626, by rfl⟩ : syracuseStep 436835 = 655253) B655253
theorem B436851 : Blo 435777 436851 := bstep (se 1 (by rfl) ⟨327638, by rfl⟩ : syracuseStep 436851 = 655277) B655277
theorem B436867 : Blo 435777 436867 := bstep (se 1 (by rfl) ⟨327650, by rfl⟩ : syracuseStep 436867 = 655301) B655301
theorem B436883 : Blo 435777 436883 := bstep (se 1 (by rfl) ⟨327662, by rfl⟩ : syracuseStep 436883 = 655325) B655325
theorem B436899 : Blo 435777 436899 := bstep (se 1 (by rfl) ⟨327674, by rfl⟩ : syracuseStep 436899 = 655349) B655349
theorem B2108081 : Blo 435777 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B436915 : Blo 435777 436915 := bstep (se 1 (by rfl) ⟨327686, by rfl⟩ : syracuseStep 436915 = 655373) B655373
theorem B436931 : Blo 435777 436931 := bstep (se 1 (by rfl) ⟨327698, by rfl⟩ : syracuseStep 436931 = 655397) B655397
theorem B1354445 : Blo 435777 1354445 := bstep (se 3 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 1354445 = 507917) B507917
theorem B436947 : Blo 435777 436947 := bstep (se 1 (by rfl) ⟨327710, by rfl⟩ : syracuseStep 436947 = 655421) B655421
theorem B436963 : Blo 435777 436963 := bstep (se 1 (by rfl) ⟨327722, by rfl⟩ : syracuseStep 436963 = 655445) B655445
theorem B830179 : Blo 435777 830179 := bstep (se 1 (by rfl) ⟨622634, by rfl⟩ : syracuseStep 830179 = 1245269) B1245269
theorem B436979 : Blo 435777 436979 := bstep (se 1 (by rfl) ⟨327734, by rfl⟩ : syracuseStep 436979 = 655469) B655469
theorem B436995 : Blo 435777 436995 := bstep (se 1 (by rfl) ⟨327746, by rfl⟩ : syracuseStep 436995 = 655493) B655493
theorem B2501381 : Blo 435777 2501381 := bstep (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) B469009
theorem B3746573 : Blo 435777 3746573 := bstep (se 3 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 3746573 = 1404965) B1404965
theorem B830225 : Blo 435777 830225 := bstep (se 2 (by rfl) ⟨311334, by rfl⟩ : syracuseStep 830225 = 622669) B622669
theorem B437011 : Blo 435777 437011 := bstep (se 1 (by rfl) ⟨327758, by rfl⟩ : syracuseStep 437011 = 655517) B655517
theorem B437027 : Blo 435777 437027 := bstep (se 1 (by rfl) ⟨327770, by rfl⟩ : syracuseStep 437027 = 655541) B655541
theorem B437043 : Blo 435777 437043 := bstep (se 1 (by rfl) ⟨327782, by rfl⟩ : syracuseStep 437043 = 655565) B655565
theorem B437059 : Blo 435777 437059 := bstep (se 1 (by rfl) ⟨327794, by rfl⟩ : syracuseStep 437059 = 655589) B655589
theorem B437075 : Blo 435777 437075 := bstep (se 1 (by rfl) ⟨327806, by rfl⟩ : syracuseStep 437075 = 655613) B655613
theorem B437091 : Blo 435777 437091 := bstep (se 1 (by rfl) ⟨327818, by rfl⟩ : syracuseStep 437091 = 655637) B655637
theorem B437107 : Blo 435777 437107 := bstep (se 1 (by rfl) ⟨327830, by rfl⟩ : syracuseStep 437107 = 655661) B655661
theorem B437123 : Blo 435777 437123 := bstep (se 1 (by rfl) ⟨327842, by rfl⟩ : syracuseStep 437123 = 655685) B655685
theorem B437139 : Blo 435777 437139 := bstep (se 1 (by rfl) ⟨327854, by rfl⟩ : syracuseStep 437139 = 655709) B655709
theorem B437155 : Blo 435777 437155 := bstep (se 1 (by rfl) ⟨327866, by rfl⟩ : syracuseStep 437155 = 655733) B655733
theorem B437171 : Blo 435777 437171 := bstep (se 1 (by rfl) ⟨327878, by rfl⟩ : syracuseStep 437171 = 655757) B655757
theorem B437187 : Blo 435777 437187 := bstep (se 1 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 437187 = 655781) B655781
theorem B437203 : Blo 435777 437203 := bstep (se 1 (by rfl) ⟨327902, by rfl⟩ : syracuseStep 437203 = 655805) B655805
theorem B437219 : Blo 435777 437219 := bstep (se 1 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 437219 = 655829) B655829
theorem B437235 : Blo 435777 437235 := bstep (se 1 (by rfl) ⟨327926, by rfl⟩ : syracuseStep 437235 = 655853) B655853
theorem B437251 : Blo 435777 437251 := bstep (se 1 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 437251 = 655877) B655877
theorem B2108429 : Blo 435777 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B437267 : Blo 435777 437267 := bstep (se 1 (by rfl) ⟨327950, by rfl⟩ : syracuseStep 437267 = 655901) B655901
theorem B437283 : Blo 435777 437283 := bstep (se 1 (by rfl) ⟨327962, by rfl⟩ : syracuseStep 437283 = 655925) B655925
theorem B830513 : Blo 435777 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B437299 : Blo 435777 437299 := bstep (se 1 (by rfl) ⟨327974, by rfl⟩ : syracuseStep 437299 = 655949) B655949
theorem B437315 : Blo 435777 437315 := bstep (se 1 (by rfl) ⟨327986, by rfl⟩ : syracuseStep 437315 = 655973) B655973
theorem B437331 : Blo 435777 437331 := bstep (se 1 (by rfl) ⟨327998, by rfl⟩ : syracuseStep 437331 = 655997) B655997
theorem B699491 : Blo 435777 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B437347 : Blo 435777 437347 := bstep (se 1 (by rfl) ⟨328010, by rfl⟩ : syracuseStep 437347 = 656021) B656021
theorem B437363 : Blo 435777 437363 := bstep (se 1 (by rfl) ⟨328022, by rfl⟩ : syracuseStep 437363 = 656045) B656045
theorem B437379 : Blo 435777 437379 := bstep (se 1 (by rfl) ⟨328034, by rfl⟩ : syracuseStep 437379 = 656069) B656069
theorem B5057677 : Blo 435777 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B437395 : Blo 435777 437395 := bstep (se 1 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 437395 = 656093) B656093
theorem B437411 : Blo 435777 437411 := bstep (se 1 (by rfl) ⟨328058, by rfl⟩ : syracuseStep 437411 = 656117) B656117
theorem B437427 : Blo 435777 437427 := bstep (se 1 (by rfl) ⟨328070, by rfl⟩ : syracuseStep 437427 = 656141) B656141
theorem B437443 : Blo 435777 437443 := bstep (se 1 (by rfl) ⟨328082, by rfl⟩ : syracuseStep 437443 = 656165) B656165
theorem B2206925 : Blo 435777 2206925 := bstep (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) B827597
theorem B2501837 : Blo 435777 2501837 := bstep (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) B938189
theorem B437459 : Blo 435777 437459 := bstep (se 1 (by rfl) ⟨328094, by rfl⟩ : syracuseStep 437459 = 656189) B656189
theorem B437475 : Blo 435777 437475 := bstep (se 1 (by rfl) ⟨328106, by rfl⟩ : syracuseStep 437475 = 656213) B656213
theorem B437491 : Blo 435777 437491 := bstep (se 1 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 437491 = 656237) B656237
theorem B437507 : Blo 435777 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B437523 : Blo 435777 437523 := bstep (se 1 (by rfl) ⟨328142, by rfl⟩ : syracuseStep 437523 = 656285) B656285
theorem B437539 : Blo 435777 437539 := bstep (se 1 (by rfl) ⟨328154, by rfl⟩ : syracuseStep 437539 = 656309) B656309
theorem B437555 : Blo 435777 437555 := bstep (se 1 (by rfl) ⟨328166, by rfl⟩ : syracuseStep 437555 = 656333) B656333
theorem B699715 : Blo 435777 699715 := bstep (se 1 (by rfl) ⟨524786, by rfl⟩ : syracuseStep 699715 = 1049573) B1049573
theorem B437571 : Blo 435777 437571 := bstep (se 1 (by rfl) ⟨328178, by rfl⟩ : syracuseStep 437571 = 656357) B656357
theorem B437587 : Blo 435777 437587 := bstep (se 1 (by rfl) ⟨328190, by rfl⟩ : syracuseStep 437587 = 656381) B656381
theorem B437603 : Blo 435777 437603 := bstep (se 1 (by rfl) ⟨328202, by rfl⟩ : syracuseStep 437603 = 656405) B656405
theorem B437619 : Blo 435777 437619 := bstep (se 1 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 437619 = 656429) B656429
theorem B437635 : Blo 435777 437635 := bstep (se 1 (by rfl) ⟨328226, by rfl⟩ : syracuseStep 437635 = 656453) B656453
theorem B437651 : Blo 435777 437651 := bstep (se 1 (by rfl) ⟨328238, by rfl⟩ : syracuseStep 437651 = 656477) B656477
theorem B437667 : Blo 435777 437667 := bstep (se 1 (by rfl) ⟨328250, by rfl⟩ : syracuseStep 437667 = 656501) B656501
theorem B437683 : Blo 435777 437683 := bstep (se 1 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 437683 = 656525) B656525
theorem B437699 : Blo 435777 437699 := bstep (se 1 (by rfl) ⟨328274, by rfl⟩ : syracuseStep 437699 = 656549) B656549
theorem B1125827 : Blo 435777 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B437715 : Blo 435777 437715 := bstep (se 1 (by rfl) ⟨328286, by rfl⟩ : syracuseStep 437715 = 656573) B656573
theorem B437731 : Blo 435777 437731 := bstep (se 1 (by rfl) ⟨328298, by rfl⟩ : syracuseStep 437731 = 656597) B656597
theorem B437747 : Blo 435777 437747 := bstep (se 1 (by rfl) ⟨328310, by rfl⟩ : syracuseStep 437747 = 656621) B656621
theorem B437763 : Blo 435777 437763 := bstep (se 1 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 437763 = 656645) B656645
theorem B437779 : Blo 435777 437779 := bstep (se 1 (by rfl) ⟨328334, by rfl⟩ : syracuseStep 437779 = 656669) B656669
theorem B2797091 : Blo 435777 2797091 := bstep (se 1 (by rfl) ⟨2097818, by rfl⟩ : syracuseStep 2797091 = 4195637) B4195637
theorem B437795 : Blo 435777 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B437811 : Blo 435777 437811 := bstep (se 1 (by rfl) ⟨328358, by rfl⟩ : syracuseStep 437811 = 656717) B656717
theorem B15904309 : Blo 435777 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B437827 : Blo 435777 437827 := bstep (se 1 (by rfl) ⟨328370, by rfl⟩ : syracuseStep 437827 = 656741) B656741
theorem B437843 : Blo 435777 437843 := bstep (se 1 (by rfl) ⟨328382, by rfl⟩ : syracuseStep 437843 = 656765) B656765
theorem B437859 : Blo 435777 437859 := bstep (se 1 (by rfl) ⟨328394, by rfl⟩ : syracuseStep 437859 = 656789) B656789
theorem B437875 : Blo 435777 437875 := bstep (se 1 (by rfl) ⟨328406, by rfl⟩ : syracuseStep 437875 = 656813) B656813
theorem B437891 : Blo 435777 437891 := bstep (se 1 (by rfl) ⟨328418, by rfl⟩ : syracuseStep 437891 = 656837) B656837
theorem B437907 : Blo 435777 437907 := bstep (se 1 (by rfl) ⟨328430, by rfl⟩ : syracuseStep 437907 = 656861) B656861
theorem B667297 : Blo 435777 667297 := bstep (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) B500473
theorem B437923 : Blo 435777 437923 := bstep (se 1 (by rfl) ⟨328442, by rfl⟩ : syracuseStep 437923 = 656885) B656885
theorem B437939 : Blo 435777 437939 := bstep (se 1 (by rfl) ⟨328454, by rfl⟩ : syracuseStep 437939 = 656909) B656909
theorem B437955 : Blo 435777 437955 := bstep (se 1 (by rfl) ⟨328466, by rfl⟩ : syracuseStep 437955 = 656933) B656933
theorem B437971 : Blo 435777 437971 := bstep (se 1 (by rfl) ⟨328478, by rfl⟩ : syracuseStep 437971 = 656957) B656957
theorem B437987 : Blo 435777 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B438003 : Blo 435777 438003 := bstep (se 1 (by rfl) ⟨328502, by rfl⟩ : syracuseStep 438003 = 657005) B657005
theorem B831235 : Blo 435777 831235 := bstep (se 1 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 831235 = 1246853) B1246853
theorem B438019 : Blo 435777 438019 := bstep (se 1 (by rfl) ⟨328514, by rfl⟩ : syracuseStep 438019 = 657029) B657029
theorem B438035 : Blo 435777 438035 := bstep (se 1 (by rfl) ⟨328526, by rfl⟩ : syracuseStep 438035 = 657053) B657053
theorem B995107 : Blo 435777 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B438051 : Blo 435777 438051 := bstep (se 1 (by rfl) ⟨328538, by rfl⟩ : syracuseStep 438051 = 657077) B657077
theorem B438067 : Blo 435777 438067 := bstep (se 1 (by rfl) ⟨328550, by rfl⟩ : syracuseStep 438067 = 657101) B657101
theorem B438083 : Blo 435777 438083 := bstep (se 1 (by rfl) ⟨328562, by rfl⟩ : syracuseStep 438083 = 657125) B657125
theorem B438099 : Blo 435777 438099 := bstep (se 1 (by rfl) ⟨328574, by rfl⟩ : syracuseStep 438099 = 657149) B657149
theorem B438115 : Blo 435777 438115 := bstep (se 1 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 438115 = 657173) B657173
theorem B438131 : Blo 435777 438131 := bstep (se 1 (by rfl) ⟨328598, by rfl⟩ : syracuseStep 438131 = 657197) B657197
theorem B438147 : Blo 435777 438147 := bstep (se 1 (by rfl) ⟨328610, by rfl⟩ : syracuseStep 438147 = 657221) B657221
theorem B15150989 : Blo 435777 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B438163 : Blo 435777 438163 := bstep (se 1 (by rfl) ⟨328622, by rfl⟩ : syracuseStep 438163 = 657245) B657245
theorem B438179 : Blo 435777 438179 := bstep (se 1 (by rfl) ⟨328634, by rfl⟩ : syracuseStep 438179 = 657269) B657269
theorem B438195 : Blo 435777 438195 := bstep (se 1 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 438195 = 657293) B657293
theorem B438211 : Blo 435777 438211 := bstep (se 1 (by rfl) ⟨328658, by rfl⟩ : syracuseStep 438211 = 657317) B657317
theorem B438227 : Blo 435777 438227 := bstep (se 1 (by rfl) ⟨328670, by rfl⟩ : syracuseStep 438227 = 657341) B657341
theorem B438243 : Blo 435777 438243 := bstep (se 1 (by rfl) ⟨328682, by rfl⟩ : syracuseStep 438243 = 657365) B657365
theorem B438259 : Blo 435777 438259 := bstep (se 1 (by rfl) ⟨328694, by rfl⟩ : syracuseStep 438259 = 657389) B657389
theorem B438275 : Blo 435777 438275 := bstep (se 1 (by rfl) ⟨328706, by rfl⟩ : syracuseStep 438275 = 657413) B657413
theorem B438291 : Blo 435777 438291 := bstep (se 1 (by rfl) ⟨328718, by rfl⟩ : syracuseStep 438291 = 657437) B657437
theorem B438307 : Blo 435777 438307 := bstep (se 1 (by rfl) ⟨328730, by rfl⟩ : syracuseStep 438307 = 657461) B657461
theorem B438323 : Blo 435777 438323 := bstep (se 1 (by rfl) ⟨328742, by rfl⟩ : syracuseStep 438323 = 657485) B657485
theorem B438339 : Blo 435777 438339 := bstep (se 1 (by rfl) ⟨328754, by rfl⟩ : syracuseStep 438339 = 657509) B657509
theorem B438355 : Blo 435777 438355 := bstep (se 1 (by rfl) ⟨328766, by rfl⟩ : syracuseStep 438355 = 657533) B657533
theorem B438371 : Blo 435777 438371 := bstep (se 1 (by rfl) ⟨328778, by rfl⟩ : syracuseStep 438371 = 657557) B657557
theorem B438387 : Blo 435777 438387 := bstep (se 1 (by rfl) ⟨328790, by rfl⟩ : syracuseStep 438387 = 657581) B657581
theorem B438403 : Blo 435777 438403 := bstep (se 1 (by rfl) ⟨328802, by rfl⟩ : syracuseStep 438403 = 657605) B657605
theorem B438419 : Blo 435777 438419 := bstep (se 1 (by rfl) ⟨328814, by rfl⟩ : syracuseStep 438419 = 657629) B657629
theorem B438435 : Blo 435777 438435 := bstep (se 1 (by rfl) ⟨328826, by rfl⟩ : syracuseStep 438435 = 657653) B657653
theorem B438451 : Blo 435777 438451 := bstep (se 1 (by rfl) ⟨328838, by rfl⟩ : syracuseStep 438451 = 657677) B657677
theorem B831683 : Blo 435777 831683 := bstep (se 1 (by rfl) ⟨623762, by rfl⟩ : syracuseStep 831683 = 1247525) B1247525
theorem B438467 : Blo 435777 438467 := bstep (se 1 (by rfl) ⟨328850, by rfl⟩ : syracuseStep 438467 = 657701) B657701
theorem B438483 : Blo 435777 438483 := bstep (se 1 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 438483 = 657725) B657725
theorem B438499 : Blo 435777 438499 := bstep (se 1 (by rfl) ⟨328874, by rfl⟩ : syracuseStep 438499 = 657749) B657749
theorem B438515 : Blo 435777 438515 := bstep (se 1 (by rfl) ⟨328886, by rfl⟩ : syracuseStep 438515 = 657773) B657773
theorem B438531 : Blo 435777 438531 := bstep (se 1 (by rfl) ⟨328898, by rfl⟩ : syracuseStep 438531 = 657797) B657797
theorem B438547 : Blo 435777 438547 := bstep (se 1 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 438547 = 657821) B657821
theorem B438563 : Blo 435777 438563 := bstep (se 1 (by rfl) ⟨328922, by rfl⟩ : syracuseStep 438563 = 657845) B657845
theorem B700721 : Blo 435777 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B438579 : Blo 435777 438579 := bstep (se 1 (by rfl) ⟨328934, by rfl⟩ : syracuseStep 438579 = 657869) B657869
theorem B438595 : Blo 435777 438595 := bstep (se 1 (by rfl) ⟨328946, by rfl⟩ : syracuseStep 438595 = 657893) B657893
theorem B602435 : Blo 435777 602435 := bstep (se 1 (by rfl) ⟨451826, by rfl⟩ : syracuseStep 602435 = 903653) B903653
theorem B438611 : Blo 435777 438611 := bstep (se 1 (by rfl) ⟨328958, by rfl⟩ : syracuseStep 438611 = 657917) B657917
theorem B438627 : Blo 435777 438627 := bstep (se 1 (by rfl) ⟨328970, by rfl⟩ : syracuseStep 438627 = 657941) B657941
theorem B438643 : Blo 435777 438643 := bstep (se 1 (by rfl) ⟨328982, by rfl⟩ : syracuseStep 438643 = 657965) B657965
theorem B438659 : Blo 435777 438659 := bstep (se 1 (by rfl) ⟨328994, by rfl⟩ : syracuseStep 438659 = 657989) B657989
theorem B438675 : Blo 435777 438675 := bstep (se 1 (by rfl) ⟨329006, by rfl⟩ : syracuseStep 438675 = 658013) B658013
theorem B438691 : Blo 435777 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B438707 : Blo 435777 438707 := bstep (se 1 (by rfl) ⟨329030, by rfl⟩ : syracuseStep 438707 = 658061) B658061
theorem B438723 : Blo 435777 438723 := bstep (se 1 (by rfl) ⟨329042, by rfl⟩ : syracuseStep 438723 = 658085) B658085
theorem B438739 : Blo 435777 438739 := bstep (se 1 (by rfl) ⟨329054, by rfl⟩ : syracuseStep 438739 = 658109) B658109
theorem B831971 : Blo 435777 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B438755 : Blo 435777 438755 := bstep (se 1 (by rfl) ⟨329066, by rfl⟩ : syracuseStep 438755 = 658133) B658133
theorem B700913 : Blo 435777 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B438771 : Blo 435777 438771 := bstep (se 1 (by rfl) ⟨329078, by rfl⟩ : syracuseStep 438771 = 658157) B658157
theorem B438787 : Blo 435777 438787 := bstep (se 1 (by rfl) ⟨329090, by rfl⟩ : syracuseStep 438787 = 658181) B658181
theorem B438803 : Blo 435777 438803 := bstep (se 1 (by rfl) ⟨329102, by rfl⟩ : syracuseStep 438803 = 658205) B658205
theorem B438819 : Blo 435777 438819 := bstep (se 1 (by rfl) ⟨329114, by rfl⟩ : syracuseStep 438819 = 658229) B658229
theorem B438835 : Blo 435777 438835 := bstep (se 1 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 438835 = 658253) B658253
theorem B438851 : Blo 435777 438851 := bstep (se 1 (by rfl) ⟨329138, by rfl⟩ : syracuseStep 438851 = 658277) B658277
theorem B438867 : Blo 435777 438867 := bstep (se 1 (by rfl) ⟨329150, by rfl⟩ : syracuseStep 438867 = 658301) B658301
theorem B438883 : Blo 435777 438883 := bstep (se 1 (by rfl) ⟨329162, by rfl⟩ : syracuseStep 438883 = 658325) B658325
theorem B799345 : Blo 435777 799345 := bstep (se 2 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 799345 = 599509) B599509
theorem B4993649 : Blo 435777 4993649 := bstep (se 2 (by rfl) ⟨1872618, by rfl⟩ : syracuseStep 4993649 = 3745237) B3745237
theorem B438899 : Blo 435777 438899 := bstep (se 1 (by rfl) ⟨329174, by rfl⟩ : syracuseStep 438899 = 658349) B658349
theorem B438915 : Blo 435777 438915 := bstep (se 1 (by rfl) ⟨329186, by rfl⟩ : syracuseStep 438915 = 658373) B658373
theorem B438931 : Blo 435777 438931 := bstep (se 1 (by rfl) ⟨329198, by rfl⟩ : syracuseStep 438931 = 658397) B658397
theorem B438947 : Blo 435777 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B438963 : Blo 435777 438963 := bstep (se 1 (by rfl) ⟨329222, by rfl⟩ : syracuseStep 438963 = 658445) B658445
theorem B438979 : Blo 435777 438979 := bstep (se 1 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 438979 = 658469) B658469
theorem B438995 : Blo 435777 438995 := bstep (se 1 (by rfl) ⟨329246, by rfl⟩ : syracuseStep 438995 = 658493) B658493
theorem B439011 : Blo 435777 439011 := bstep (se 1 (by rfl) ⟨329258, by rfl⟩ : syracuseStep 439011 = 658517) B658517
theorem B439027 : Blo 435777 439027 := bstep (se 1 (by rfl) ⟨329270, by rfl⟩ : syracuseStep 439027 = 658541) B658541
theorem B439043 : Blo 435777 439043 := bstep (se 1 (by rfl) ⟨329282, by rfl⟩ : syracuseStep 439043 = 658565) B658565
theorem B439059 : Blo 435777 439059 := bstep (se 1 (by rfl) ⟨329294, by rfl⟩ : syracuseStep 439059 = 658589) B658589
theorem B439075 : Blo 435777 439075 := bstep (se 1 (by rfl) ⟨329306, by rfl⟩ : syracuseStep 439075 = 658613) B658613
theorem B439091 : Blo 435777 439091 := bstep (se 1 (by rfl) ⟨329318, by rfl⟩ : syracuseStep 439091 = 658637) B658637
theorem B439107 : Blo 435777 439107 := bstep (se 1 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 439107 = 658661) B658661
theorem B668483 : Blo 435777 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B439123 : Blo 435777 439123 := bstep (se 1 (by rfl) ⟨329342, by rfl⟩ : syracuseStep 439123 = 658685) B658685
theorem B439139 : Blo 435777 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B2569073 : Blo 435777 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B439155 : Blo 435777 439155 := bstep (se 1 (by rfl) ⟨329366, by rfl⟩ : syracuseStep 439155 = 658733) B658733
theorem B439171 : Blo 435777 439171 := bstep (se 1 (by rfl) ⟨329378, by rfl⟩ : syracuseStep 439171 = 658757) B658757
theorem B439187 : Blo 435777 439187 := bstep (se 1 (by rfl) ⟨329390, by rfl⟩ : syracuseStep 439187 = 658781) B658781
theorem B439203 : Blo 435777 439203 := bstep (se 1 (by rfl) ⟨329402, by rfl⟩ : syracuseStep 439203 = 658805) B658805
theorem B439219 : Blo 435777 439219 := bstep (se 1 (by rfl) ⟨329414, by rfl⟩ : syracuseStep 439219 = 658829) B658829
theorem B439235 : Blo 435777 439235 := bstep (se 1 (by rfl) ⟨329426, by rfl⟩ : syracuseStep 439235 = 658853) B658853
theorem B439251 : Blo 435777 439251 := bstep (se 1 (by rfl) ⟨329438, by rfl⟩ : syracuseStep 439251 = 658877) B658877
theorem B439267 : Blo 435777 439267 := bstep (se 1 (by rfl) ⟨329450, by rfl⟩ : syracuseStep 439267 = 658901) B658901
theorem B439283 : Blo 435777 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B439299 : Blo 435777 439299 := bstep (se 1 (by rfl) ⟨329474, by rfl⟩ : syracuseStep 439299 = 658949) B658949
theorem B439315 : Blo 435777 439315 := bstep (se 1 (by rfl) ⟨329486, by rfl⟩ : syracuseStep 439315 = 658973) B658973
theorem B439331 : Blo 435777 439331 := bstep (se 1 (by rfl) ⟨329498, by rfl⟩ : syracuseStep 439331 = 658997) B658997
theorem B439347 : Blo 435777 439347 := bstep (se 1 (by rfl) ⟨329510, by rfl⟩ : syracuseStep 439347 = 659021) B659021
theorem B439363 : Blo 435777 439363 := bstep (se 1 (by rfl) ⟨329522, by rfl⟩ : syracuseStep 439363 = 659045) B659045
theorem B439379 : Blo 435777 439379 := bstep (se 1 (by rfl) ⟨329534, by rfl⟩ : syracuseStep 439379 = 659069) B659069
theorem B439395 : Blo 435777 439395 := bstep (se 1 (by rfl) ⟨329546, by rfl⟩ : syracuseStep 439395 = 659093) B659093
theorem B12629105 : Blo 435777 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B439411 : Blo 435777 439411 := bstep (se 1 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 439411 = 659117) B659117
theorem B439427 : Blo 435777 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B439443 : Blo 435777 439443 := bstep (se 1 (by rfl) ⟨329582, by rfl⟩ : syracuseStep 439443 = 659165) B659165
theorem B898211 : Blo 435777 898211 := bstep (se 1 (by rfl) ⟨673658, by rfl⟩ : syracuseStep 898211 = 1347317) B1347317
theorem B439459 : Blo 435777 439459 := bstep (se 1 (by rfl) ⟨329594, by rfl⟩ : syracuseStep 439459 = 659189) B659189
theorem B439475 : Blo 435777 439475 := bstep (se 1 (by rfl) ⟨329606, by rfl⟩ : syracuseStep 439475 = 659213) B659213
theorem B439491 : Blo 435777 439491 := bstep (se 1 (by rfl) ⟨329618, by rfl⟩ : syracuseStep 439491 = 659237) B659237
theorem B439507 : Blo 435777 439507 := bstep (se 1 (by rfl) ⟨329630, by rfl⟩ : syracuseStep 439507 = 659261) B659261
theorem B439523 : Blo 435777 439523 := bstep (se 1 (by rfl) ⟨329642, by rfl⟩ : syracuseStep 439523 = 659285) B659285
theorem B439539 : Blo 435777 439539 := bstep (se 1 (by rfl) ⟨329654, by rfl⟩ : syracuseStep 439539 = 659309) B659309
theorem B439555 : Blo 435777 439555 := bstep (se 1 (by rfl) ⟨329666, by rfl⟩ : syracuseStep 439555 = 659333) B659333
theorem B439571 : Blo 435777 439571 := bstep (se 1 (by rfl) ⟨329678, by rfl⟩ : syracuseStep 439571 = 659357) B659357
theorem B439587 : Blo 435777 439587 := bstep (se 1 (by rfl) ⟨329690, by rfl⟩ : syracuseStep 439587 = 659381) B659381
theorem B439603 : Blo 435777 439603 := bstep (se 1 (by rfl) ⟨329702, by rfl⟩ : syracuseStep 439603 = 659405) B659405
theorem B439619 : Blo 435777 439619 := bstep (se 1 (by rfl) ⟨329714, by rfl⟩ : syracuseStep 439619 = 659429) B659429
theorem B439635 : Blo 435777 439635 := bstep (se 1 (by rfl) ⟨329726, by rfl⟩ : syracuseStep 439635 = 659453) B659453
theorem B439651 : Blo 435777 439651 := bstep (se 1 (by rfl) ⟨329738, by rfl⟩ : syracuseStep 439651 = 659477) B659477
theorem B439667 : Blo 435777 439667 := bstep (se 1 (by rfl) ⟨329750, by rfl⟩ : syracuseStep 439667 = 659501) B659501
theorem B439683 : Blo 435777 439683 := bstep (se 1 (by rfl) ⟨329762, by rfl⟩ : syracuseStep 439683 = 659525) B659525
theorem B832913 : Blo 435777 832913 := bstep (se 2 (by rfl) ⟨312342, by rfl⟩ : syracuseStep 832913 = 624685) B624685
theorem B439699 : Blo 435777 439699 := bstep (se 1 (by rfl) ⟨329774, by rfl⟩ : syracuseStep 439699 = 659549) B659549
theorem B439715 : Blo 435777 439715 := bstep (se 1 (by rfl) ⟨329786, by rfl⟩ : syracuseStep 439715 = 659573) B659573
theorem B439731 : Blo 435777 439731 := bstep (se 1 (by rfl) ⟨329798, by rfl⟩ : syracuseStep 439731 = 659597) B659597
theorem B439747 : Blo 435777 439747 := bstep (se 1 (by rfl) ⟨329810, by rfl⟩ : syracuseStep 439747 = 659621) B659621
theorem B439763 : Blo 435777 439763 := bstep (se 1 (by rfl) ⟨329822, by rfl⟩ : syracuseStep 439763 = 659645) B659645
theorem B5682659 : Blo 435777 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B931313 : Blo 435777 931313 := bstep (se 2 (by rfl) ⟨349242, by rfl⟩ : syracuseStep 931313 = 698485) B698485
theorem B1390189 : Blo 435777 1390189 := bstep (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) B521321
theorem B2209841 : Blo 435777 2209841 := bstep (se 2 (by rfl) ⟨828690, by rfl⟩ : syracuseStep 2209841 = 1657381) B1657381
theorem B702515 : Blo 435777 702515 := bstep (se 1 (by rfl) ⟨526886, by rfl⟩ : syracuseStep 702515 = 1053773) B1053773
theorem B735473 : Blo 435777 735473 := bstep (se 2 (by rfl) ⟨275802, by rfl⟩ : syracuseStep 735473 = 551605) B551605
theorem B833809 : Blo 435777 833809 := bstep (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) B625357
theorem B735601 : Blo 435777 735601 := bstep (se 2 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 735601 = 551701) B551701
theorem B735635 : Blo 435777 735635 := bstep (se 1 (by rfl) ⟨551726, by rfl⟩ : syracuseStep 735635 = 1103453) B1103453
theorem B833969 : Blo 435777 833969 := bstep (se 2 (by rfl) ⟨312738, by rfl⟩ : syracuseStep 833969 = 625477) B625477
theorem B702899 : Blo 435777 702899 := bstep (se 1 (by rfl) ⟨527174, by rfl⟩ : syracuseStep 702899 = 1054349) B1054349
theorem B473603 : Blo 435777 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B735763 : Blo 435777 735763 := bstep (se 1 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 735763 = 1103645) B1103645
theorem B703027 : Blo 435777 703027 := bstep (se 1 (by rfl) ⟨527270, by rfl⟩ : syracuseStep 703027 = 1054541) B1054541
theorem B735905 : Blo 435777 735905 := bstep (se 2 (by rfl) ⟨275964, by rfl⟩ : syracuseStep 735905 = 551929) B551929
theorem B736033 : Blo 435777 736033 := bstep (se 2 (by rfl) ⟨276012, by rfl⟩ : syracuseStep 736033 = 552025) B552025
theorem B736067 : Blo 435777 736067 := bstep (se 1 (by rfl) ⟨552050, by rfl⟩ : syracuseStep 736067 = 1104101) B1104101
theorem B834371 : Blo 435777 834371 := bstep (se 1 (by rfl) ⟨625778, by rfl⟩ : syracuseStep 834371 = 1251557) B1251557
theorem B736195 : Blo 435777 736195 := bstep (se 1 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 736195 = 1104293) B1104293
theorem B2538467 : Blo 435777 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B736337 : Blo 435777 736337 := bstep (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) B552253
theorem B932995 : Blo 435777 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B736465 : Blo 435777 736465 := bstep (se 2 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 736465 = 552349) B552349
theorem B736499 : Blo 435777 736499 := bstep (se 1 (by rfl) ⟨552374, by rfl⟩ : syracuseStep 736499 = 1104749) B1104749
theorem B703745 : Blo 435777 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B7126325 : Blo 435777 7126325 := bstep (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) B668093
theorem B736627 : Blo 435777 736627 := bstep (se 1 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 736627 = 1104941) B1104941
theorem B703937 : Blo 435777 703937 := bstep (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) B527953
theorem B2211299 : Blo 435777 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B2801137 : Blo 435777 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B736769 : Blo 435777 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B933457 : Blo 435777 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B736897 : Blo 435777 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B736931 : Blo 435777 736931 := bstep (se 1 (by rfl) ⟨552698, by rfl⟩ : syracuseStep 736931 = 1105397) B1105397
theorem B737059 : Blo 435777 737059 := bstep (se 1 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 737059 = 1105589) B1105589
theorem B737201 : Blo 435777 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B1654769 : Blo 435777 1654769 := bstep (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) B1241077
theorem B737329 : Blo 435777 737329 := bstep (se 2 (by rfl) ⟨276498, by rfl⟩ : syracuseStep 737329 = 552997) B552997
theorem B737363 : Blo 435777 737363 := bstep (se 1 (by rfl) ⟨553022, by rfl⟩ : syracuseStep 737363 = 1106045) B1106045
theorem B737491 : Blo 435777 737491 := bstep (se 1 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 737491 = 1106237) B1106237
theorem B8110307 : Blo 435777 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B2212109 : Blo 435777 2212109 := bstep (se 3 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 2212109 = 829541) B829541
theorem B737633 : Blo 435777 737633 := bstep (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) B553225
theorem B737761 : Blo 435777 737761 := bstep (se 2 (by rfl) ⟨276660, by rfl⟩ : syracuseStep 737761 = 553321) B553321
theorem B737795 : Blo 435777 737795 := bstep (se 1 (by rfl) ⟨553346, by rfl⟩ : syracuseStep 737795 = 1106693) B1106693
theorem B934499 : Blo 435777 934499 := bstep (se 1 (by rfl) ⟨700874, by rfl⟩ : syracuseStep 934499 = 1401749) B1401749
theorem B737923 : Blo 435777 737923 := bstep (se 1 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 737923 = 1106885) B1106885
theorem B1655437 : Blo 435777 1655437 := bstep (se 3 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 1655437 = 620789) B620789
theorem B738065 : Blo 435777 738065 := bstep (se 2 (by rfl) ⟨276774, by rfl⟩ : syracuseStep 738065 = 553549) B553549
theorem B1491853 : Blo 435777 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B738193 : Blo 435777 738193 := bstep (se 2 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 738193 = 553645) B553645
theorem B672673 : Blo 435777 672673 := bstep (se 2 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 672673 = 504505) B504505
theorem B738227 : Blo 435777 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B738355 : Blo 435777 738355 := bstep (se 1 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 738355 = 1107533) B1107533
theorem B935011 : Blo 435777 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B738497 : Blo 435777 738497 := bstep (se 2 (by rfl) ⟨276936, by rfl⟩ : syracuseStep 738497 = 553873) B553873
theorem B738625 : Blo 435777 738625 := bstep (se 2 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 738625 = 553969) B553969
theorem B738659 : Blo 435777 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B1656227 : Blo 435777 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B738787 : Blo 435777 738787 := bstep (se 1 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 738787 = 1108181) B1108181
theorem B738929 : Blo 435777 738929 := bstep (se 2 (by rfl) ⟨277098, by rfl⟩ : syracuseStep 738929 = 554197) B554197
theorem B739057 : Blo 435777 739057 := bstep (se 2 (by rfl) ⟨277146, by rfl⟩ : syracuseStep 739057 = 554293) B554293
theorem B739091 : Blo 435777 739091 := bstep (se 1 (by rfl) ⟨554318, by rfl⟩ : syracuseStep 739091 = 1108637) B1108637
theorem B935729 : Blo 435777 935729 := bstep (se 2 (by rfl) ⟨350898, by rfl⟩ : syracuseStep 935729 = 701797) B701797
theorem B739219 : Blo 435777 739219 := bstep (se 1 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 739219 = 1108829) B1108829
theorem B2738083 : Blo 435777 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B739361 : Blo 435777 739361 := bstep (se 2 (by rfl) ⟨277260, by rfl⟩ : syracuseStep 739361 = 554521) B554521
theorem B1656881 : Blo 435777 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B739489 : Blo 435777 739489 := bstep (se 2 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 739489 = 554617) B554617
theorem B739523 : Blo 435777 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B5621957 : Blo 435777 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B2672909 : Blo 435777 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B739651 : Blo 435777 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B2247053 : Blo 435777 2247053 := bstep (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) B842645
theorem B739793 : Blo 435777 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B936515 : Blo 435777 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B739921 : Blo 435777 739921 := bstep (se 2 (by rfl) ⟨277470, by rfl⟩ : syracuseStep 739921 = 554941) B554941
theorem B739955 : Blo 435777 739955 := bstep (se 1 (by rfl) ⟨554966, by rfl⟩ : syracuseStep 739955 = 1109933) B1109933
theorem B740083 : Blo 435777 740083 := bstep (se 1 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 740083 = 1110125) B1110125
theorem B2018125 : Blo 435777 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B740225 : Blo 435777 740225 := bstep (se 2 (by rfl) ⟨277584, by rfl⟩ : syracuseStep 740225 = 555169) B555169
theorem B740353 : Blo 435777 740353 := bstep (se 2 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 740353 = 555265) B555265
theorem B740387 : Blo 435777 740387 := bstep (se 1 (by rfl) ⟨555290, by rfl⟩ : syracuseStep 740387 = 1110581) B1110581
theorem B2215025 : Blo 435777 2215025 := bstep (se 2 (by rfl) ⟨830634, by rfl⟩ : syracuseStep 2215025 = 1661269) B1661269
theorem B740515 : Blo 435777 740515 := bstep (se 1 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 740515 = 1110773) B1110773
theorem B609539 : Blo 435777 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B740657 : Blo 435777 740657 := bstep (se 2 (by rfl) ⟨277746, by rfl⟩ : syracuseStep 740657 = 555493) B555493
theorem B3165581 : Blo 435777 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B740785 : Blo 435777 740785 := bstep (se 2 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 740785 = 555589) B555589
theorem B740819 : Blo 435777 740819 := bstep (se 1 (by rfl) ⟨555614, by rfl⟩ : syracuseStep 740819 = 1111229) B1111229
theorem B1658339 : Blo 435777 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B1658353 : Blo 435777 1658353 := bstep (se 2 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 1658353 = 1243765) B1243765
theorem B937489 : Blo 435777 937489 := bstep (se 2 (by rfl) ⟨351558, by rfl⟩ : syracuseStep 937489 = 703117) B703117
theorem B740947 : Blo 435777 740947 := bstep (se 1 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 740947 = 1111421) B1111421
theorem B741089 : Blo 435777 741089 := bstep (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) B555817
theorem B937745 : Blo 435777 937745 := bstep (se 2 (by rfl) ⟨351654, by rfl⟩ : syracuseStep 937745 = 703309) B703309
theorem B741217 : Blo 435777 741217 := bstep (se 2 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 741217 = 555913) B555913
theorem B741251 : Blo 435777 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B2674565 : Blo 435777 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B741379 : Blo 435777 741379 := bstep (se 1 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 741379 = 1112069) B1112069
theorem B741521 : Blo 435777 741521 := bstep (se 2 (by rfl) ⟨278070, by rfl⟩ : syracuseStep 741521 = 556141) B556141
theorem B741649 : Blo 435777 741649 := bstep (se 2 (by rfl) ⟨278118, by rfl⟩ : syracuseStep 741649 = 556237) B556237
theorem B1200419 : Blo 435777 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B741683 : Blo 435777 741683 := bstep (se 1 (by rfl) ⟨556262, by rfl⟩ : syracuseStep 741683 = 1112525) B1112525
theorem B741811 : Blo 435777 741811 := bstep (se 1 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 741811 = 1112717) B1112717
theorem B2216483 : Blo 435777 2216483 := bstep (se 1 (by rfl) ⟨1662362, by rfl⟩ : syracuseStep 2216483 = 3324725) B3324725
theorem B741953 : Blo 435777 741953 := bstep (se 2 (by rfl) ⟨278232, by rfl⟩ : syracuseStep 741953 = 556465) B556465
theorem B742081 : Blo 435777 742081 := bstep (se 2 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 742081 = 556561) B556561
theorem B742115 : Blo 435777 742115 := bstep (se 1 (by rfl) ⟨556586, by rfl⟩ : syracuseStep 742115 = 1113173) B1113173
theorem B1659811 : Blo 435777 1659811 := bstep (se 1 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 1659811 = 2489717) B2489717
theorem B1397699 : Blo 435777 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B3331043 : Blo 435777 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B939043 : Blo 435777 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B7492661 : Blo 435777 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B1397827 : Blo 435777 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B2217293 : Blo 435777 2217293 := bstep (se 3 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 2217293 = 831485) B831485
theorem B1398161 : Blo 435777 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B5199331 : Blo 435777 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B2152099 : Blo 435777 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1333037 : Blo 435777 1333037 := bstep (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) B499889
theorem B1103665 : Blo 435777 1103665 := bstep (se 2 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 1103665 = 827749) B827749
theorem B1103939 : Blo 435777 1103939 := bstep (se 1 (by rfl) ⟨827954, by rfl⟩ : syracuseStep 1103939 = 1655909) B1655909
theorem B4216931 : Blo 435777 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2087117 : Blo 435777 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1104131 : Blo 435777 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B5626421 : Blo 435777 5626421 := bstep (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) B527477
theorem B2841413 : Blo 435777 2841413 := bstep (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) B532765
theorem B1662029 : Blo 435777 1662029 := bstep (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) B623261
theorem B1105073 : Blo 435777 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B1105123 : Blo 435777 1105123 := bstep (se 1 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 1105123 = 1657685) B1657685
theorem B2809187 : Blo 435777 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B1105265 : Blo 435777 1105265 := bstep (se 2 (by rfl) ⟨414474, by rfl⟩ : syracuseStep 1105265 = 828949) B828949
theorem B1334701 : Blo 435777 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B1334897 : Blo 435777 1334897 := bstep (se 2 (by rfl) ⟨500586, by rfl⟩ : syracuseStep 1334897 = 1001173) B1001173
theorem B3006341 : Blo 435777 3006341 := bstep (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) B563689
theorem B2220209 : Blo 435777 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B1401133 : Blo 435777 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B1106257 : Blo 435777 1106257 := bstep (se 2 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 1106257 = 829693) B829693
theorem B811363 : Blo 435777 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B2482609 : Blo 435777 2482609 := bstep (se 2 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 2482609 = 1861957) B1861957
theorem B1401389 : Blo 435777 1401389 := bstep (se 3 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 1401389 = 525521) B525521
theorem B1106531 : Blo 435777 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B4973237 : Blo 435777 4973237 := bstep (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) B466241
theorem B1106723 : Blo 435777 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B1336259 : Blo 435777 1336259 := bstep (se 1 (by rfl) ⟨1002194, by rfl⟩ : syracuseStep 1336259 = 2004389) B2004389
theorem B2811185 : Blo 435777 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B3007793 : Blo 435777 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B2221667 : Blo 435777 2221667 := bstep (se 1 (by rfl) ⟨1666250, by rfl⟩ : syracuseStep 2221667 = 3332501) B3332501
theorem B1107665 : Blo 435777 1107665 := bstep (se 2 (by rfl) ⟨415374, by rfl⟩ : syracuseStep 1107665 = 830749) B830749
theorem B1107715 : Blo 435777 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B2484067 : Blo 435777 2484067 := bstep (se 1 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 2484067 = 3726101) B3726101
theorem B1107857 : Blo 435777 1107857 := bstep (se 2 (by rfl) ⟨415446, by rfl⟩ : syracuseStep 1107857 = 830893) B830893
theorem B1664945 : Blo 435777 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B1140689 : Blo 435777 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1402915 : Blo 435777 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B3336389 : Blo 435777 3336389 := bstep (se 4 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 3336389 = 625573) B625573
theorem B944369 : Blo 435777 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B2484593 : Blo 435777 2484593 := bstep (se 2 (by rfl) ⟨931722, by rfl⟩ : syracuseStep 2484593 = 1863445) B1863445
theorem B2222477 : Blo 435777 2222477 := bstep (se 3 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 2222477 = 833429) B833429
theorem B1993187 : Blo 435777 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1862129 : Blo 435777 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B551539 : Blo 435777 551539 := bstep (se 1 (by rfl) ⟨413654, by rfl⟩ : syracuseStep 551539 = 827309) B827309
theorem B7269173 : Blo 435777 7269173 := bstep (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) B681485
theorem B1403747 : Blo 435777 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B1108849 : Blo 435777 1108849 := bstep (se 2 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 1108849 = 831637) B831637
theorem B2812877 : Blo 435777 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B2157553 : Blo 435777 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B552035 : Blo 435777 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B1109123 : Blo 435777 1109123 := bstep (se 1 (by rfl) ⟨831842, by rfl⟩ : syracuseStep 1109123 = 1663685) B1663685
theorem B1404145 : Blo 435777 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B1404209 : Blo 435777 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B1109315 : Blo 435777 1109315 := bstep (se 1 (by rfl) ⟨831986, by rfl⟩ : syracuseStep 1109315 = 1663973) B1663973
theorem B4222277 : Blo 435777 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B1666403 : Blo 435777 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B2486051 : Blo 435777 2486051 := bstep (se 1 (by rfl) ⟨1864538, by rfl⟩ : syracuseStep 2486051 = 3729077) B3729077
theorem B552739 : Blo 435777 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B552835 : Blo 435777 552835 := bstep (se 1 (by rfl) ⟨414626, by rfl⟩ : syracuseStep 552835 = 829253) B829253
theorem B749731 : Blo 435777 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B2846897 : Blo 435777 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B4878563 : Blo 435777 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1110257 : Blo 435777 1110257 := bstep (se 2 (by rfl) ⟨416346, by rfl⟩ : syracuseStep 1110257 = 832693) B832693
theorem B1110307 : Blo 435777 1110307 := bstep (se 1 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 1110307 = 1665461) B1665461
theorem B1470797 : Blo 435777 1470797 := bstep (se 3 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 1470797 = 551549) B551549
theorem B1667405 : Blo 435777 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B553331 : Blo 435777 553331 := bstep (se 1 (by rfl) ⟨414998, by rfl⟩ : syracuseStep 553331 = 829997) B829997
theorem B1470851 : Blo 435777 1470851 := bstep (se 1 (by rfl) ⟨1103138, by rfl⟩ : syracuseStep 1470851 = 2206277) B2206277
theorem B1110449 : Blo 435777 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B5599813 : Blo 435777 5599813 := bstep (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) B1049965
theorem B1471121 : Blo 435777 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B2356067 : Blo 435777 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1242125 : Blo 435777 1242125 := bstep (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) B465797
theorem B554035 : Blo 435777 554035 := bstep (se 1 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 554035 = 831053) B831053
theorem B554131 : Blo 435777 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B1471661 : Blo 435777 1471661 := bstep (se 3 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 1471661 = 551873) B551873
theorem B1242307 : Blo 435777 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B1471715 : Blo 435777 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B1242353 : Blo 435777 1242353 := bstep (se 2 (by rfl) ⟨465882, by rfl⟩ : syracuseStep 1242353 = 931765) B931765
theorem B2225393 : Blo 435777 2225393 := bstep (se 2 (by rfl) ⟨834522, by rfl⟩ : syracuseStep 2225393 = 1669045) B1669045
theorem B1865101 : Blo 435777 1865101 := bstep (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) B699413
theorem B1111441 : Blo 435777 1111441 := bstep (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) B833581
theorem B3536369 : Blo 435777 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B1471985 : Blo 435777 1471985 := bstep (se 2 (by rfl) ⟨551994, by rfl⟩ : syracuseStep 1471985 = 1103989) B1103989
theorem B554627 : Blo 435777 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B2487941 : Blo 435777 2487941 := bstep (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) B466489
theorem B1111715 : Blo 435777 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B980657 : Blo 435777 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B980675 : Blo 435777 980675 := bstep (se 1 (by rfl) ⟨735506, by rfl⟩ : syracuseStep 980675 = 1471013) B1471013
theorem B1865443 : Blo 435777 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B718625 : Blo 435777 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B751427 : Blo 435777 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B1111907 : Blo 435777 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B718787 : Blo 435777 718787 := bstep (se 1 (by rfl) ⟨539090, by rfl⟩ : syracuseStep 718787 = 1078181) B1078181
theorem B980945 : Blo 435777 980945 := bstep (se 2 (by rfl) ⟨367854, by rfl⟩ : syracuseStep 980945 = 735709) B735709
theorem B980963 : Blo 435777 980963 := bstep (se 1 (by rfl) ⟨735722, by rfl⟩ : syracuseStep 980963 = 1471445) B1471445
theorem B2652131 : Blo 435777 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B2488333 : Blo 435777 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1472525 : Blo 435777 1472525 := bstep (se 3 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 1472525 = 552197) B552197
theorem B1767473 : Blo 435777 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B1472579 : Blo 435777 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B1767665 : Blo 435777 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B981233 : Blo 435777 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B981251 : Blo 435777 981251 := bstep (se 1 (by rfl) ⟨735938, by rfl⟩ : syracuseStep 981251 = 1471877) B1471877
theorem B555331 : Blo 435777 555331 := bstep (se 1 (by rfl) ⟨416498, by rfl⟩ : syracuseStep 555331 = 832997) B832997
theorem B1472849 : Blo 435777 1472849 := bstep (se 2 (by rfl) ⟨552318, by rfl⟩ : syracuseStep 1472849 = 1104637) B1104637
theorem B653681 : Blo 435777 653681 := bstep (se 2 (by rfl) ⟨245130, by rfl⟩ : syracuseStep 653681 = 490261) B490261
theorem B653699 : Blo 435777 653699 := bstep (se 1 (by rfl) ⟨490274, by rfl⟩ : syracuseStep 653699 = 980549) B980549
theorem B1669517 : Blo 435777 1669517 := bstep (se 3 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 1669517 = 626069) B626069
theorem B653729 : Blo 435777 653729 := bstep (se 2 (by rfl) ⟨245148, by rfl⟩ : syracuseStep 653729 = 490297) B490297
theorem B555427 : Blo 435777 555427 := bstep (se 1 (by rfl) ⟨416570, by rfl⟩ : syracuseStep 555427 = 833141) B833141
theorem B653747 : Blo 435777 653747 := bstep (se 1 (by rfl) ⟨490310, by rfl⟩ : syracuseStep 653747 = 980621) B980621
theorem B653777 : Blo 435777 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B653795 : Blo 435777 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B2128355 : Blo 435777 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B653825 : Blo 435777 653825 := bstep (se 2 (by rfl) ⟨245184, by rfl⟩ : syracuseStep 653825 = 490369) B490369
theorem B981521 : Blo 435777 981521 := bstep (se 2 (by rfl) ⟨368070, by rfl⟩ : syracuseStep 981521 = 736141) B736141
theorem B653843 : Blo 435777 653843 := bstep (se 1 (by rfl) ⟨490382, by rfl⟩ : syracuseStep 653843 = 980765) B980765
theorem B981539 : Blo 435777 981539 := bstep (se 1 (by rfl) ⟨736154, by rfl⟩ : syracuseStep 981539 = 1472309) B1472309
theorem B653873 : Blo 435777 653873 := bstep (se 2 (by rfl) ⟨245202, by rfl⟩ : syracuseStep 653873 = 490405) B490405
theorem B653891 : Blo 435777 653891 := bstep (se 1 (by rfl) ⟨490418, by rfl⟩ : syracuseStep 653891 = 980837) B980837
theorem B653921 : Blo 435777 653921 := bstep (se 2 (by rfl) ⟨245220, by rfl⟩ : syracuseStep 653921 = 490441) B490441
theorem B653939 : Blo 435777 653939 := bstep (se 1 (by rfl) ⟨490454, by rfl⟩ : syracuseStep 653939 = 980909) B980909
theorem B653969 : Blo 435777 653969 := bstep (se 2 (by rfl) ⟨245238, by rfl⟩ : syracuseStep 653969 = 490477) B490477
theorem B653987 : Blo 435777 653987 := bstep (se 1 (by rfl) ⟨490490, by rfl⟩ : syracuseStep 653987 = 980981) B980981
theorem B1243811 : Blo 435777 1243811 := bstep (se 1 (by rfl) ⟨932858, by rfl⟩ : syracuseStep 1243811 = 1865717) B1865717
theorem B654017 : Blo 435777 654017 := bstep (se 2 (by rfl) ⟨245256, by rfl⟩ : syracuseStep 654017 = 490513) B490513
theorem B654035 : Blo 435777 654035 := bstep (se 1 (by rfl) ⟨490526, by rfl⟩ : syracuseStep 654035 = 981053) B981053
theorem B654065 : Blo 435777 654065 := bstep (se 2 (by rfl) ⟨245274, by rfl⟩ : syracuseStep 654065 = 490549) B490549
theorem B654083 : Blo 435777 654083 := bstep (se 1 (by rfl) ⟨490562, by rfl⟩ : syracuseStep 654083 = 981125) B981125
theorem B1112849 : Blo 435777 1112849 := bstep (se 2 (by rfl) ⟨417318, by rfl⟩ : syracuseStep 1112849 = 834637) B834637
theorem B654113 : Blo 435777 654113 := bstep (se 2 (by rfl) ⟨245292, by rfl⟩ : syracuseStep 654113 = 490585) B490585
theorem B981809 : Blo 435777 981809 := bstep (se 2 (by rfl) ⟨368178, by rfl⟩ : syracuseStep 981809 = 736357) B736357
theorem B654131 : Blo 435777 654131 := bstep (se 1 (by rfl) ⟨490598, by rfl⟩ : syracuseStep 654131 = 981197) B981197
theorem B981827 : Blo 435777 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B1112899 : Blo 435777 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B654161 : Blo 435777 654161 := bstep (se 2 (by rfl) ⟨245310, by rfl⟩ : syracuseStep 654161 = 490621) B490621
theorem B654179 : Blo 435777 654179 := bstep (se 1 (by rfl) ⟨490634, by rfl⟩ : syracuseStep 654179 = 981269) B981269
theorem B1473389 : Blo 435777 1473389 := bstep (se 3 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 1473389 = 552521) B552521
theorem B621427 : Blo 435777 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B654209 : Blo 435777 654209 := bstep (se 2 (by rfl) ⟨245328, by rfl⟩ : syracuseStep 654209 = 490657) B490657
theorem B490387 : Blo 435777 490387 := bstep (se 1 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 490387 = 735581) B735581
theorem B654227 : Blo 435777 654227 := bstep (se 1 (by rfl) ⟨490670, by rfl⟩ : syracuseStep 654227 = 981341) B981341
theorem B555923 : Blo 435777 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B1473443 : Blo 435777 1473443 := bstep (se 1 (by rfl) ⟨1105082, by rfl⟩ : syracuseStep 1473443 = 2210165) B2210165
theorem B654257 : Blo 435777 654257 := bstep (se 2 (by rfl) ⟨245346, by rfl⟩ : syracuseStep 654257 = 490693) B490693
theorem B654275 : Blo 435777 654275 := bstep (se 1 (by rfl) ⟨490706, by rfl⟩ : syracuseStep 654275 = 981413) B981413
theorem B1113041 : Blo 435777 1113041 := bstep (se 2 (by rfl) ⟨417390, by rfl⟩ : syracuseStep 1113041 = 834781) B834781
theorem B654305 : Blo 435777 654305 := bstep (se 2 (by rfl) ⟨245364, by rfl⟩ : syracuseStep 654305 = 490729) B490729
theorem B654323 : Blo 435777 654323 := bstep (se 1 (by rfl) ⟨490742, by rfl⟩ : syracuseStep 654323 = 981485) B981485
theorem B654353 : Blo 435777 654353 := bstep (se 2 (by rfl) ⟨245382, by rfl⟩ : syracuseStep 654353 = 490765) B490765
theorem B490531 : Blo 435777 490531 := bstep (se 1 (by rfl) ⟨367898, by rfl⟩ : syracuseStep 490531 = 735797) B735797
theorem B654371 : Blo 435777 654371 := bstep (se 1 (by rfl) ⟨490778, by rfl⟩ : syracuseStep 654371 = 981557) B981557
theorem B654401 : Blo 435777 654401 := bstep (se 2 (by rfl) ⟨245400, by rfl⟩ : syracuseStep 654401 = 490801) B490801
theorem B982097 : Blo 435777 982097 := bstep (se 2 (by rfl) ⟨368286, by rfl⟩ : syracuseStep 982097 = 736573) B736573
theorem B654419 : Blo 435777 654419 := bstep (se 1 (by rfl) ⟨490814, by rfl⟩ : syracuseStep 654419 = 981629) B981629
theorem B982115 : Blo 435777 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B654449 : Blo 435777 654449 := bstep (se 2 (by rfl) ⟨245418, by rfl⟩ : syracuseStep 654449 = 490837) B490837
theorem B654467 : Blo 435777 654467 := bstep (se 1 (by rfl) ⟨490850, by rfl⟩ : syracuseStep 654467 = 981701) B981701
theorem B654497 : Blo 435777 654497 := bstep (se 2 (by rfl) ⟨245436, by rfl⟩ : syracuseStep 654497 = 490873) B490873
theorem B1473713 : Blo 435777 1473713 := bstep (se 2 (by rfl) ⟨552642, by rfl⟩ : syracuseStep 1473713 = 1105285) B1105285
theorem B490675 : Blo 435777 490675 := bstep (se 1 (by rfl) ⟨368006, by rfl⟩ : syracuseStep 490675 = 736013) B736013
theorem B654515 : Blo 435777 654515 := bstep (se 1 (by rfl) ⟨490886, by rfl⟩ : syracuseStep 654515 = 981773) B981773
theorem B654545 : Blo 435777 654545 := bstep (se 2 (by rfl) ⟨245454, by rfl⟩ : syracuseStep 654545 = 490909) B490909
theorem B654563 : Blo 435777 654563 := bstep (se 1 (by rfl) ⟨490922, by rfl⟩ : syracuseStep 654563 = 981845) B981845
theorem B654593 : Blo 435777 654593 := bstep (se 2 (by rfl) ⟨245472, by rfl⟩ : syracuseStep 654593 = 490945) B490945
theorem B654611 : Blo 435777 654611 := bstep (se 1 (by rfl) ⟨490958, by rfl⟩ : syracuseStep 654611 = 981917) B981917
theorem B654641 : Blo 435777 654641 := bstep (se 2 (by rfl) ⟨245490, by rfl⟩ : syracuseStep 654641 = 490981) B490981
theorem B490819 : Blo 435777 490819 := bstep (se 1 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 490819 = 736229) B736229
theorem B654659 : Blo 435777 654659 := bstep (se 1 (by rfl) ⟨490994, by rfl⟩ : syracuseStep 654659 = 981989) B981989
theorem B654689 : Blo 435777 654689 := bstep (se 2 (by rfl) ⟨245508, by rfl⟩ : syracuseStep 654689 = 491017) B491017
theorem B982385 : Blo 435777 982385 := bstep (se 2 (by rfl) ⟨368394, by rfl⟩ : syracuseStep 982385 = 736789) B736789
theorem B654707 : Blo 435777 654707 := bstep (se 1 (by rfl) ⟨491030, by rfl⟩ : syracuseStep 654707 = 982061) B982061
theorem B982403 : Blo 435777 982403 := bstep (se 1 (by rfl) ⟨736802, by rfl⟩ : syracuseStep 982403 = 1473605) B1473605
theorem B1408387 : Blo 435777 1408387 := bstep (se 1 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 1408387 = 2112581) B2112581
theorem B654737 : Blo 435777 654737 := bstep (se 2 (by rfl) ⟨245526, by rfl⟩ : syracuseStep 654737 = 491053) B491053
theorem B654755 : Blo 435777 654755 := bstep (se 1 (by rfl) ⟨491066, by rfl⟩ : syracuseStep 654755 = 982133) B982133
theorem B654785 : Blo 435777 654785 := bstep (se 2 (by rfl) ⟨245544, by rfl⟩ : syracuseStep 654785 = 491089) B491089
theorem B490963 : Blo 435777 490963 := bstep (se 1 (by rfl) ⟨368222, by rfl⟩ : syracuseStep 490963 = 736445) B736445
theorem B654803 : Blo 435777 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B7962083 : Blo 435777 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B654833 : Blo 435777 654833 := bstep (se 2 (by rfl) ⟨245562, by rfl⟩ : syracuseStep 654833 = 491125) B491125
theorem B654851 : Blo 435777 654851 := bstep (se 1 (by rfl) ⟨491138, by rfl⟩ : syracuseStep 654851 = 982277) B982277
theorem B654881 : Blo 435777 654881 := bstep (se 2 (by rfl) ⟨245580, by rfl⟩ : syracuseStep 654881 = 491161) B491161
theorem B654899 : Blo 435777 654899 := bstep (se 1 (by rfl) ⟨491174, by rfl⟩ : syracuseStep 654899 = 982349) B982349
theorem B654929 : Blo 435777 654929 := bstep (se 2 (by rfl) ⟨245598, by rfl⟩ : syracuseStep 654929 = 491197) B491197
theorem B491107 : Blo 435777 491107 := bstep (se 1 (by rfl) ⟨368330, by rfl⟩ : syracuseStep 491107 = 736661) B736661
theorem B654947 : Blo 435777 654947 := bstep (se 1 (by rfl) ⟨491210, by rfl⟩ : syracuseStep 654947 = 982421) B982421
theorem B654977 : Blo 435777 654977 := bstep (se 2 (by rfl) ⟨245616, by rfl⟩ : syracuseStep 654977 = 491233) B491233
theorem B982673 : Blo 435777 982673 := bstep (se 2 (by rfl) ⟨368502, by rfl⟩ : syracuseStep 982673 = 737005) B737005
theorem B654995 : Blo 435777 654995 := bstep (se 1 (by rfl) ⟨491246, by rfl⟩ : syracuseStep 654995 = 982493) B982493
theorem B982691 : Blo 435777 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B655025 : Blo 435777 655025 := bstep (se 2 (by rfl) ⟨245634, by rfl⟩ : syracuseStep 655025 = 491269) B491269
theorem B523955 : Blo 435777 523955 := bstep (se 1 (by rfl) ⟨392966, by rfl⟩ : syracuseStep 523955 = 785933) B785933
theorem B655043 : Blo 435777 655043 := bstep (se 1 (by rfl) ⟨491282, by rfl⟩ : syracuseStep 655043 = 982565) B982565
theorem B1474253 : Blo 435777 1474253 := bstep (se 3 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 1474253 = 552845) B552845
theorem B655073 : Blo 435777 655073 := bstep (se 2 (by rfl) ⟨245652, by rfl⟩ : syracuseStep 655073 = 491305) B491305
theorem B491251 : Blo 435777 491251 := bstep (se 1 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 491251 = 736877) B736877
theorem B655091 : Blo 435777 655091 := bstep (se 1 (by rfl) ⟨491318, by rfl⟩ : syracuseStep 655091 = 982637) B982637
theorem B1474307 : Blo 435777 1474307 := bstep (se 1 (by rfl) ⟨1105730, by rfl⟩ : syracuseStep 1474307 = 2211461) B2211461
theorem B655121 : Blo 435777 655121 := bstep (se 2 (by rfl) ⟨245670, by rfl⟩ : syracuseStep 655121 = 491341) B491341
theorem B655139 : Blo 435777 655139 := bstep (se 1 (by rfl) ⟨491354, by rfl⟩ : syracuseStep 655139 = 982709) B982709
theorem B655169 : Blo 435777 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B655187 : Blo 435777 655187 := bstep (se 1 (by rfl) ⟨491390, by rfl⟩ : syracuseStep 655187 = 982781) B982781
theorem B884579 : Blo 435777 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B655217 : Blo 435777 655217 := bstep (se 2 (by rfl) ⟨245706, by rfl⟩ : syracuseStep 655217 = 491413) B491413
theorem B1245041 : Blo 435777 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B556915 : Blo 435777 556915 := bstep (se 1 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 556915 = 835373) B835373
theorem B884611 : Blo 435777 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B491395 : Blo 435777 491395 := bstep (se 1 (by rfl) ⟨368546, by rfl⟩ : syracuseStep 491395 = 737093) B737093
theorem B655235 : Blo 435777 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B2359181 : Blo 435777 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B655265 : Blo 435777 655265 := bstep (se 2 (by rfl) ⟨245724, by rfl⟩ : syracuseStep 655265 = 491449) B491449
theorem B982961 : Blo 435777 982961 := bstep (se 2 (by rfl) ⟨368610, by rfl⟩ : syracuseStep 982961 = 737221) B737221
theorem B655283 : Blo 435777 655283 := bstep (se 1 (by rfl) ⟨491462, by rfl⟩ : syracuseStep 655283 = 982925) B982925
theorem B982979 : Blo 435777 982979 := bstep (se 1 (by rfl) ⟨737234, by rfl⟩ : syracuseStep 982979 = 1474469) B1474469
theorem B655313 : Blo 435777 655313 := bstep (se 2 (by rfl) ⟨245742, by rfl⟩ : syracuseStep 655313 = 491485) B491485
theorem B622561 : Blo 435777 622561 := bstep (se 2 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 622561 = 466921) B466921
theorem B655331 : Blo 435777 655331 := bstep (se 1 (by rfl) ⟨491498, by rfl⟩ : syracuseStep 655331 = 982997) B982997
theorem B983051 : Blo 435777 983051 := bstep (se 1 (by rfl) ⟨737288, by rfl⟩ : syracuseStep 983051 = 1474577) B1474577
theorem B655385 : Blo 435777 655385 := bstep (se 2 (by rfl) ⟨245769, by rfl⟩ : syracuseStep 655385 = 491539) B491539
theorem B491575 : Blo 435777 491575 := bstep (se 1 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 491575 = 737363) B737363
theorem B983105 : Blo 435777 983105 := bstep (se 2 (by rfl) ⟨368664, by rfl⟩ : syracuseStep 983105 = 737329) B737329
theorem B655499 : Blo 435777 655499 := bstep (se 1 (by rfl) ⟨491624, by rfl⟩ : syracuseStep 655499 = 983249) B983249
theorem B1048727 : Blo 435777 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B655511 : Blo 435777 655511 := bstep (se 1 (by rfl) ⟨491633, by rfl⟩ : syracuseStep 655511 = 983267) B983267
theorem B1474739 : Blo 435777 1474739 := bstep (se 1 (by rfl) ⟨1106054, by rfl⟩ : syracuseStep 1474739 = 2212109) B2212109
theorem B655577 : Blo 435777 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B491755 : Blo 435777 491755 := bstep (se 1 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 491755 = 737633) B737633
theorem B983321 : Blo 435777 983321 := bstep (se 2 (by rfl) ⟨368745, by rfl⟩ : syracuseStep 983321 = 737491) B737491
theorem B655691 : Blo 435777 655691 := bstep (se 1 (by rfl) ⟨491768, by rfl⟩ : syracuseStep 655691 = 983537) B983537
theorem B655703 : Blo 435777 655703 := bstep (se 1 (by rfl) ⟨491777, by rfl⟩ : syracuseStep 655703 = 983555) B983555
theorem B491863 : Blo 435777 491863 := bstep (se 1 (by rfl) ⟨368897, by rfl⟩ : syracuseStep 491863 = 737795) B737795
theorem B983411 : Blo 435777 983411 := bstep (se 1 (by rfl) ⟨737558, by rfl⟩ : syracuseStep 983411 = 1475117) B1475117
theorem B1868177 : Blo 435777 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B983447 : Blo 435777 983447 := bstep (se 1 (by rfl) ⟨737585, by rfl⟩ : syracuseStep 983447 = 1475171) B1475171
theorem B622999 : Blo 435777 622999 := bstep (se 1 (by rfl) ⟨467249, by rfl⟩ : syracuseStep 622999 = 934499) B934499
theorem B655769 : Blo 435777 655769 := bstep (se 2 (by rfl) ⟨245913, by rfl⟩ : syracuseStep 655769 = 491827) B491827
theorem B1475009 : Blo 435777 1475009 := bstep (se 2 (by rfl) ⟨553128, by rfl⟩ : syracuseStep 1475009 = 1106257) B1106257
theorem B1081817 : Blo 435777 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B655883 : Blo 435777 655883 := bstep (se 1 (by rfl) ⟨491912, by rfl⟩ : syracuseStep 655883 = 983825) B983825
theorem B492043 : Blo 435777 492043 := bstep (se 1 (by rfl) ⟨369032, by rfl⟩ : syracuseStep 492043 = 738065) B738065
theorem B655895 : Blo 435777 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B3310145 : Blo 435777 3310145 := bstep (se 2 (by rfl) ⟨1241304, by rfl⟩ : syracuseStep 3310145 = 2482609) B2482609
theorem B983627 : Blo 435777 983627 := bstep (se 1 (by rfl) ⟨737720, by rfl⟩ : syracuseStep 983627 = 1475441) B1475441
theorem B655961 : Blo 435777 655961 := bstep (se 2 (by rfl) ⟨245985, by rfl⟩ : syracuseStep 655961 = 491971) B491971
theorem B21627485 : Blo 435777 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B13009501 : Blo 435777 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B492151 : Blo 435777 492151 := bstep (se 1 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 492151 = 738227) B738227
theorem B983681 : Blo 435777 983681 := bstep (se 2 (by rfl) ⟨368880, by rfl⟩ : syracuseStep 983681 = 737761) B737761
theorem B656075 : Blo 435777 656075 := bstep (se 1 (by rfl) ⟨492056, by rfl⟩ : syracuseStep 656075 = 984113) B984113
theorem B656087 : Blo 435777 656087 := bstep (se 1 (by rfl) ⟨492065, by rfl⟩ : syracuseStep 656087 = 984131) B984131
theorem B656153 : Blo 435777 656153 := bstep (se 2 (by rfl) ⟨246057, by rfl⟩ : syracuseStep 656153 = 492115) B492115
theorem B492331 : Blo 435777 492331 := bstep (se 1 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 492331 = 738497) B738497
theorem B983897 : Blo 435777 983897 := bstep (se 2 (by rfl) ⟨368961, by rfl⟩ : syracuseStep 983897 = 737923) B737923
theorem B1606493 : Blo 435777 1606493 := bstep (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) B602435
theorem B656267 : Blo 435777 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B656279 : Blo 435777 656279 := bstep (se 1 (by rfl) ⟨492209, by rfl⟩ : syracuseStep 656279 = 984419) B984419
theorem B492439 : Blo 435777 492439 := bstep (se 1 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 492439 = 738659) B738659
theorem B983987 : Blo 435777 983987 := bstep (se 1 (by rfl) ⟨737990, by rfl⟩ : syracuseStep 983987 = 1475981) B1475981
theorem B984023 : Blo 435777 984023 := bstep (se 1 (by rfl) ⟨738017, by rfl⟩ : syracuseStep 984023 = 1476035) B1476035
theorem B656345 : Blo 435777 656345 := bstep (se 2 (by rfl) ⟨246129, by rfl⟩ : syracuseStep 656345 = 492259) B492259
theorem B1475549 : Blo 435777 1475549 := bstep (se 3 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 1475549 = 553331) B553331
theorem B656459 : Blo 435777 656459 := bstep (se 1 (by rfl) ⟨492344, by rfl⟩ : syracuseStep 656459 = 984689) B984689
theorem B492619 : Blo 435777 492619 := bstep (se 1 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 492619 = 738929) B738929
theorem B656471 : Blo 435777 656471 := bstep (se 1 (by rfl) ⟨492353, by rfl⟩ : syracuseStep 656471 = 984707) B984707
theorem B623705 : Blo 435777 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B984203 : Blo 435777 984203 := bstep (se 1 (by rfl) ⟨738152, by rfl⟩ : syracuseStep 984203 = 1476305) B1476305
theorem B656537 : Blo 435777 656537 := bstep (se 2 (by rfl) ⟨246201, by rfl⟩ : syracuseStep 656537 = 492403) B492403
theorem B492727 : Blo 435777 492727 := bstep (se 1 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 492727 = 739091) B739091
theorem B1180865 : Blo 435777 1180865 := bstep (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) B885649
theorem B984257 : Blo 435777 984257 := bstep (se 2 (by rfl) ⟨369096, by rfl⟩ : syracuseStep 984257 = 738193) B738193
theorem B623819 : Blo 435777 623819 := bstep (se 1 (by rfl) ⟨467864, by rfl⟩ : syracuseStep 623819 = 935729) B935729
theorem B3146957 : Blo 435777 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B656651 : Blo 435777 656651 := bstep (se 1 (by rfl) ⟨492488, by rfl⟩ : syracuseStep 656651 = 984977) B984977
theorem B656663 : Blo 435777 656663 := bstep (se 1 (by rfl) ⟨492497, by rfl⟩ : syracuseStep 656663 = 984995) B984995
theorem B1869101 : Blo 435777 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B656729 : Blo 435777 656729 := bstep (se 2 (by rfl) ⟨246273, by rfl⟩ : syracuseStep 656729 = 492547) B492547
theorem B492907 : Blo 435777 492907 := bstep (se 1 (by rfl) ⟨369680, by rfl⟩ : syracuseStep 492907 = 739361) B739361
theorem B984473 : Blo 435777 984473 := bstep (se 2 (by rfl) ⟨369177, by rfl⟩ : syracuseStep 984473 = 738355) B738355
theorem B656843 : Blo 435777 656843 := bstep (se 1 (by rfl) ⟨492632, by rfl⟩ : syracuseStep 656843 = 985265) B985265
theorem B656855 : Blo 435777 656855 := bstep (se 1 (by rfl) ⟨492641, by rfl⟩ : syracuseStep 656855 = 985283) B985283
theorem B493015 : Blo 435777 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B1246681 : Blo 435777 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B984563 : Blo 435777 984563 := bstep (se 1 (by rfl) ⟨738422, by rfl⟩ : syracuseStep 984563 = 1476845) B1476845
theorem B984599 : Blo 435777 984599 := bstep (se 1 (by rfl) ⟨738449, by rfl⟩ : syracuseStep 984599 = 1476899) B1476899
theorem B656921 : Blo 435777 656921 := bstep (se 2 (by rfl) ⟨246345, by rfl⟩ : syracuseStep 656921 = 492691) B492691
theorem B657035 : Blo 435777 657035 := bstep (se 1 (by rfl) ⟨492776, by rfl⟩ : syracuseStep 657035 = 985553) B985553
theorem B493195 : Blo 435777 493195 := bstep (se 1 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 493195 = 739793) B739793
theorem B657047 : Blo 435777 657047 := bstep (se 1 (by rfl) ⟨492785, by rfl⟩ : syracuseStep 657047 = 985571) B985571
theorem B1574603 : Blo 435777 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B984779 : Blo 435777 984779 := bstep (se 1 (by rfl) ⟨738584, by rfl⟩ : syracuseStep 984779 = 1477169) B1477169
theorem B624343 : Blo 435777 624343 := bstep (se 1 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 624343 = 936515) B936515
theorem B657113 : Blo 435777 657113 := bstep (se 2 (by rfl) ⟨246417, by rfl⟩ : syracuseStep 657113 = 492835) B492835
theorem B493303 : Blo 435777 493303 := bstep (se 1 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 493303 = 739955) B739955
theorem B984833 : Blo 435777 984833 := bstep (se 2 (by rfl) ⟨369312, by rfl⟩ : syracuseStep 984833 = 738625) B738625
theorem B657227 : Blo 435777 657227 := bstep (se 1 (by rfl) ⟨492920, by rfl⟩ : syracuseStep 657227 = 985841) B985841
theorem B657239 : Blo 435777 657239 := bstep (se 1 (by rfl) ⟨492929, by rfl⟩ : syracuseStep 657239 = 985859) B985859
theorem B1247069 : Blo 435777 1247069 := bstep (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) B467651
theorem B1771415 : Blo 435777 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B657305 : Blo 435777 657305 := bstep (se 2 (by rfl) ⟨246489, by rfl⟩ : syracuseStep 657305 = 492979) B492979
theorem B493483 : Blo 435777 493483 := bstep (se 1 (by rfl) ⟨370112, by rfl⟩ : syracuseStep 493483 = 740225) B740225
theorem B886745 : Blo 435777 886745 := bstep (se 2 (by rfl) ⟨332529, by rfl⟩ : syracuseStep 886745 = 665059) B665059
theorem B985049 : Blo 435777 985049 := bstep (se 2 (by rfl) ⟨369393, by rfl⟩ : syracuseStep 985049 = 738787) B738787
theorem B657419 : Blo 435777 657419 := bstep (se 1 (by rfl) ⟨493064, by rfl⟩ : syracuseStep 657419 = 986129) B986129
theorem B657431 : Blo 435777 657431 := bstep (se 1 (by rfl) ⟨493073, by rfl⟩ : syracuseStep 657431 = 986147) B986147
theorem B493591 : Blo 435777 493591 := bstep (se 1 (by rfl) ⟨370193, by rfl⟩ : syracuseStep 493591 = 740387) B740387
theorem B985139 : Blo 435777 985139 := bstep (se 1 (by rfl) ⟨738854, by rfl⟩ : syracuseStep 985139 = 1477709) B1477709
theorem B1476683 : Blo 435777 1476683 := bstep (se 1 (by rfl) ⟨1107512, by rfl⟩ : syracuseStep 1476683 = 2215025) B2215025
theorem B985175 : Blo 435777 985175 := bstep (se 1 (by rfl) ⟨738881, by rfl⟩ : syracuseStep 985175 = 1477763) B1477763
theorem B657497 : Blo 435777 657497 := bstep (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) B493123
theorem B1050803 : Blo 435777 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B657611 : Blo 435777 657611 := bstep (se 1 (by rfl) ⟨493208, by rfl⟩ : syracuseStep 657611 = 986417) B986417
theorem B493771 : Blo 435777 493771 := bstep (se 1 (by rfl) ⟨370328, by rfl⟩ : syracuseStep 493771 = 740657) B740657
theorem B657623 : Blo 435777 657623 := bstep (se 1 (by rfl) ⟨493217, by rfl⟩ : syracuseStep 657623 = 986435) B986435
theorem B2492633 : Blo 435777 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B985355 : Blo 435777 985355 := bstep (se 1 (by rfl) ⟨739016, by rfl⟩ : syracuseStep 985355 = 1478033) B1478033
theorem B657689 : Blo 435777 657689 := bstep (se 2 (by rfl) ⟨246633, by rfl⟩ : syracuseStep 657689 = 493267) B493267
theorem B6850861 : Blo 435777 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B493879 : Blo 435777 493879 := bstep (se 1 (by rfl) ⟨370409, by rfl⟩ : syracuseStep 493879 = 740819) B740819
theorem B985409 : Blo 435777 985409 := bstep (se 2 (by rfl) ⟨369528, by rfl⟩ : syracuseStep 985409 = 739057) B739057
theorem B1476953 : Blo 435777 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B657803 : Blo 435777 657803 := bstep (se 1 (by rfl) ⟨493352, by rfl⟩ : syracuseStep 657803 = 986705) B986705
theorem B657815 : Blo 435777 657815 := bstep (se 1 (by rfl) ⟨493361, by rfl⟩ : syracuseStep 657815 = 986723) B986723
theorem B1771949 : Blo 435777 1771949 := bstep (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) B664481
theorem B4196785 : Blo 435777 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B3312089 : Blo 435777 3312089 := bstep (se 2 (by rfl) ⟨1242033, by rfl⟩ : syracuseStep 3312089 = 2484067) B2484067
theorem B657881 : Blo 435777 657881 := bstep (se 2 (by rfl) ⟨246705, by rfl⟩ : syracuseStep 657881 = 493411) B493411
theorem B494059 : Blo 435777 494059 := bstep (se 1 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 494059 = 741089) B741089
theorem B625163 : Blo 435777 625163 := bstep (se 1 (by rfl) ⟨468872, by rfl⟩ : syracuseStep 625163 = 937745) B937745
theorem B985625 : Blo 435777 985625 := bstep (se 2 (by rfl) ⟨369609, by rfl⟩ : syracuseStep 985625 = 739219) B739219
theorem B657995 : Blo 435777 657995 := bstep (se 1 (by rfl) ⟨493496, by rfl⟩ : syracuseStep 657995 = 986993) B986993
theorem B658007 : Blo 435777 658007 := bstep (se 1 (by rfl) ⟨493505, by rfl⟩ : syracuseStep 658007 = 987011) B987011
theorem B494167 : Blo 435777 494167 := bstep (se 1 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 494167 = 741251) B741251
theorem B985715 : Blo 435777 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B1182359 : Blo 435777 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B985751 : Blo 435777 985751 := bstep (se 1 (by rfl) ⟨739313, by rfl⟩ : syracuseStep 985751 = 1478627) B1478627
theorem B658073 : Blo 435777 658073 := bstep (se 2 (by rfl) ⟨246777, by rfl⟩ : syracuseStep 658073 = 493555) B493555
theorem B1870553 : Blo 435777 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B658187 : Blo 435777 658187 := bstep (se 1 (by rfl) ⟨493640, by rfl⟩ : syracuseStep 658187 = 987281) B987281
theorem B494347 : Blo 435777 494347 := bstep (se 1 (by rfl) ⟨370760, by rfl⟩ : syracuseStep 494347 = 741521) B741521
theorem B658199 : Blo 435777 658199 := bstep (se 1 (by rfl) ⟨493649, by rfl⟩ : syracuseStep 658199 = 987299) B987299
theorem B985931 : Blo 435777 985931 := bstep (se 1 (by rfl) ⟨739448, by rfl⟩ : syracuseStep 985931 = 1478897) B1478897
theorem B658265 : Blo 435777 658265 := bstep (se 2 (by rfl) ⟨246849, by rfl⟩ : syracuseStep 658265 = 493699) B493699
theorem B494455 : Blo 435777 494455 := bstep (se 1 (by rfl) ⟨370841, by rfl⟩ : syracuseStep 494455 = 741683) B741683
theorem B985985 : Blo 435777 985985 := bstep (se 2 (by rfl) ⟨369744, by rfl⟩ : syracuseStep 985985 = 739489) B739489
theorem B658379 : Blo 435777 658379 := bstep (se 1 (by rfl) ⟨493784, by rfl⟩ : syracuseStep 658379 = 987569) B987569
theorem B658391 : Blo 435777 658391 := bstep (se 1 (by rfl) ⟨493793, by rfl⟩ : syracuseStep 658391 = 987587) B987587
theorem B1477655 : Blo 435777 1477655 := bstep (se 1 (by rfl) ⟨1108241, by rfl⟩ : syracuseStep 1477655 = 2216483) B2216483
theorem B658457 : Blo 435777 658457 := bstep (se 2 (by rfl) ⟨246921, by rfl⟩ : syracuseStep 658457 = 493843) B493843
theorem B494635 : Blo 435777 494635 := bstep (se 1 (by rfl) ⟨370976, by rfl⟩ : syracuseStep 494635 = 741953) B741953
theorem B986201 : Blo 435777 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B658571 : Blo 435777 658571 := bstep (se 1 (by rfl) ⟨493928, by rfl⟩ : syracuseStep 658571 = 987857) B987857
theorem B658583 : Blo 435777 658583 := bstep (se 1 (by rfl) ⟨493937, by rfl⟩ : syracuseStep 658583 = 987875) B987875
theorem B494743 : Blo 435777 494743 := bstep (se 1 (by rfl) ⟨371057, by rfl⟩ : syracuseStep 494743 = 742115) B742115
theorem B986291 : Blo 435777 986291 := bstep (se 1 (by rfl) ⟨739718, by rfl⟩ : syracuseStep 986291 = 1479437) B1479437
theorem B986327 : Blo 435777 986327 := bstep (se 1 (by rfl) ⟨739745, by rfl⟩ : syracuseStep 986327 = 1479491) B1479491
theorem B658649 : Blo 435777 658649 := bstep (se 2 (by rfl) ⟨246993, by rfl⟩ : syracuseStep 658649 = 493987) B493987
theorem B658763 : Blo 435777 658763 := bstep (se 1 (by rfl) ⟨494072, by rfl⟩ : syracuseStep 658763 = 988145) B988145
theorem B658775 : Blo 435777 658775 := bstep (se 1 (by rfl) ⟨494081, by rfl⟩ : syracuseStep 658775 = 988163) B988163
theorem B986507 : Blo 435777 986507 := bstep (se 1 (by rfl) ⟨739880, by rfl⟩ : syracuseStep 986507 = 1479761) B1479761
theorem B658841 : Blo 435777 658841 := bstep (se 2 (by rfl) ⟨247065, by rfl⟩ : syracuseStep 658841 = 494131) B494131
theorem B986561 : Blo 435777 986561 := bstep (se 2 (by rfl) ⟨369960, by rfl⟩ : syracuseStep 986561 = 739921) B739921
theorem B658955 : Blo 435777 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B658967 : Blo 435777 658967 := bstep (se 1 (by rfl) ⟨494225, by rfl⟩ : syracuseStep 658967 = 988451) B988451
theorem B1478195 : Blo 435777 1478195 := bstep (se 1 (by rfl) ⟨1108646, by rfl⟩ : syracuseStep 1478195 = 2217293) B2217293
theorem B659033 : Blo 435777 659033 := bstep (se 2 (by rfl) ⟨247137, by rfl⟩ : syracuseStep 659033 = 494275) B494275
theorem B986777 : Blo 435777 986777 := bstep (se 2 (by rfl) ⟨370041, by rfl⟩ : syracuseStep 986777 = 740083) B740083
theorem B659147 : Blo 435777 659147 := bstep (se 1 (by rfl) ⟨494360, by rfl⟩ : syracuseStep 659147 = 988721) B988721
theorem B659159 : Blo 435777 659159 := bstep (se 1 (by rfl) ⟨494369, by rfl⟩ : syracuseStep 659159 = 988739) B988739
theorem B986867 : Blo 435777 986867 := bstep (se 1 (by rfl) ⟨740150, by rfl⟩ : syracuseStep 986867 = 1480301) B1480301
theorem B2690833 : Blo 435777 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B986903 : Blo 435777 986903 := bstep (se 1 (by rfl) ⟨740177, by rfl⟩ : syracuseStep 986903 = 1480355) B1480355
theorem B659225 : Blo 435777 659225 := bstep (se 2 (by rfl) ⟨247209, by rfl⟩ : syracuseStep 659225 = 494419) B494419
theorem B2494273 : Blo 435777 2494273 := bstep (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) B1870705
theorem B1478465 : Blo 435777 1478465 := bstep (se 2 (by rfl) ⟨554424, by rfl⟩ : syracuseStep 1478465 = 1108849) B1108849
theorem B1576793 : Blo 435777 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B2101085 : Blo 435777 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B659339 : Blo 435777 659339 := bstep (se 1 (by rfl) ⟨494504, by rfl⟩ : syracuseStep 659339 = 989009) B989009
theorem B659351 : Blo 435777 659351 := bstep (se 1 (by rfl) ⟨494513, by rfl⟩ : syracuseStep 659351 = 989027) B989027
theorem B987083 : Blo 435777 987083 := bstep (se 1 (by rfl) ⟨740312, by rfl⟩ : syracuseStep 987083 = 1480625) B1480625
theorem B659417 : Blo 435777 659417 := bstep (se 2 (by rfl) ⟨247281, by rfl⟩ : syracuseStep 659417 = 494563) B494563
theorem B987137 : Blo 435777 987137 := bstep (se 2 (by rfl) ⟨370176, by rfl⟩ : syracuseStep 987137 = 740353) B740353
theorem B3543115 : Blo 435777 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B659531 : Blo 435777 659531 := bstep (se 1 (by rfl) ⟨494648, by rfl⟩ : syracuseStep 659531 = 989297) B989297
theorem B659543 : Blo 435777 659543 := bstep (se 1 (by rfl) ⟨494657, by rfl⟩ : syracuseStep 659543 = 989315) B989315
theorem B659609 : Blo 435777 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B987353 : Blo 435777 987353 := bstep (se 2 (by rfl) ⟨370257, by rfl⟩ : syracuseStep 987353 = 740515) B740515
theorem B987443 : Blo 435777 987443 := bstep (se 1 (by rfl) ⟨740582, by rfl⟩ : syracuseStep 987443 = 1481165) B1481165
theorem B1872193 : Blo 435777 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B987479 : Blo 435777 987479 := bstep (se 1 (by rfl) ⟨740609, by rfl⟩ : syracuseStep 987479 = 1481219) B1481219
theorem B1479005 : Blo 435777 1479005 := bstep (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) B554627
theorem B987659 : Blo 435777 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B987713 : Blo 435777 987713 := bstep (se 2 (by rfl) ⟨370392, by rfl⟩ : syracuseStep 987713 = 740785) B740785
theorem B1249985 : Blo 435777 1249985 := bstep (se 2 (by rfl) ⟨468744, by rfl⟩ : syracuseStep 1249985 = 937489) B937489
theorem B21205745 : Blo 435777 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B987929 : Blo 435777 987929 := bstep (se 2 (by rfl) ⟨370473, by rfl⟩ : syracuseStep 987929 = 740947) B740947
theorem B1250099 : Blo 435777 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B988019 : Blo 435777 988019 := bstep (se 1 (by rfl) ⟨741014, by rfl⟩ : syracuseStep 988019 = 1482029) B1482029
theorem B1872791 : Blo 435777 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B988055 : Blo 435777 988055 := bstep (se 1 (by rfl) ⟨741041, by rfl⟩ : syracuseStep 988055 = 1482083) B1482083
theorem B889931 : Blo 435777 889931 := bstep (se 1 (by rfl) ⟨667448, by rfl⟩ : syracuseStep 889931 = 1334897) B1334897
theorem B988235 : Blo 435777 988235 := bstep (se 1 (by rfl) ⟨741176, by rfl⟩ : syracuseStep 988235 = 1482353) B1482353
theorem B988289 : Blo 435777 988289 := bstep (se 2 (by rfl) ⟨370608, by rfl⟩ : syracuseStep 988289 = 741217) B741217
theorem B2004227 : Blo 435777 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B988505 : Blo 435777 988505 := bstep (se 2 (by rfl) ⟨370689, by rfl⟩ : syracuseStep 988505 = 741379) B741379
theorem B5051765 : Blo 435777 5051765 := bstep (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) B473603
theorem B988595 : Blo 435777 988595 := bstep (se 1 (by rfl) ⟨741446, by rfl⟩ : syracuseStep 988595 = 1482893) B1482893
theorem B1480139 : Blo 435777 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B988631 : Blo 435777 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B988811 : Blo 435777 988811 := bstep (se 1 (by rfl) ⟨741608, by rfl⟩ : syracuseStep 988811 = 1483217) B1483217
theorem B1054387 : Blo 435777 1054387 := bstep (se 1 (by rfl) ⟨790790, by rfl⟩ : syracuseStep 1054387 = 1581581) B1581581
theorem B988865 : Blo 435777 988865 := bstep (se 2 (by rfl) ⟨370824, by rfl⟩ : syracuseStep 988865 = 741649) B741649
theorem B1480409 : Blo 435777 1480409 := bstep (se 2 (by rfl) ⟨555153, by rfl⟩ : syracuseStep 1480409 = 1110307) B1110307
theorem B3315491 : Blo 435777 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B989081 : Blo 435777 989081 := bstep (se 2 (by rfl) ⟨370905, by rfl⟩ : syracuseStep 989081 = 741811) B741811
theorem B890839 : Blo 435777 890839 := bstep (se 1 (by rfl) ⟨668129, by rfl⟩ : syracuseStep 890839 = 1336259) B1336259
theorem B1578973 : Blo 435777 1578973 := bstep (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) B592115
theorem B989171 : Blo 435777 989171 := bstep (se 1 (by rfl) ⟨741878, by rfl⟩ : syracuseStep 989171 = 1483757) B1483757
theorem B989207 : Blo 435777 989207 := bstep (se 1 (by rfl) ⟨741905, by rfl⟩ : syracuseStep 989207 = 1483811) B1483811
theorem B3151973 : Blo 435777 3151973 := bstep (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) B590995
theorem B1874123 : Blo 435777 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B2005195 : Blo 435777 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B989387 : Blo 435777 989387 := bstep (se 1 (by rfl) ⟨742040, by rfl⟩ : syracuseStep 989387 = 1484081) B1484081
theorem B989441 : Blo 435777 989441 := bstep (se 2 (by rfl) ⟨371040, by rfl⟩ : syracuseStep 989441 = 742081) B742081
theorem B1481111 : Blo 435777 1481111 := bstep (se 1 (by rfl) ⟨1110833, by rfl⟩ : syracuseStep 1481111 = 2221667) B2221667
theorem B2103853 : Blo 435777 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B4201091 : Blo 435777 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B1055425 : Blo 435777 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B629579 : Blo 435777 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B1481651 : Blo 435777 1481651 := bstep (se 1 (by rfl) ⟨1111238, by rfl⟩ : syracuseStep 1481651 = 2222477) B2222477
theorem B2497715 : Blo 435777 2497715 := bstep (se 1 (by rfl) ⟨1873286, by rfl⟩ : syracuseStep 2497715 = 3746573) B3746573
theorem B1481921 : Blo 435777 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B1875251 : Blo 435777 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B466327 : Blo 435777 466327 := bstep (se 1 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 466327 = 699491) B699491
theorem B7577101 : Blo 435777 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B7118405 : Blo 435777 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1482461 : Blo 435777 1482461 := bstep (se 3 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 1482461 = 555923) B555923
theorem B15998897 : Blo 435777 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B3317777 : Blo 435777 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B467147 : Blo 435777 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B77537845 : Blo 435777 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B2499173 : Blo 435777 2499173 := bstep (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) B468595
theorem B828083 : Blo 435777 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B598807 : Blo 435777 598807 := bstep (se 1 (by rfl) ⟨449105, by rfl⟩ : syracuseStep 598807 = 898211) B898211
theorem B828235 : Blo 435777 828235 := bstep (se 1 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 828235 = 1242353) B1242353
theorem B1483595 : Blo 435777 1483595 := bstep (se 1 (by rfl) ⟨1112696, by rfl⟩ : syracuseStep 1483595 = 2225393) B2225393
theorem B1483865 : Blo 435777 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B828569 : Blo 435777 828569 := bstep (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) B621427
theorem B1877165 : Blo 435777 1877165 := bstep (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) B703937
theorem B500951 : Blo 435777 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B468343 : Blo 435777 468343 := bstep (se 1 (by rfl) ⟨351257, by rfl⟩ : syracuseStep 468343 = 702515) B702515
theorem B435787 : Blo 435777 435787 := bstep (se 1 (by rfl) ⟨326840, by rfl⟩ : syracuseStep 435787 = 653681) B653681
theorem B435799 : Blo 435777 435799 := bstep (se 1 (by rfl) ⟨326849, by rfl⟩ : syracuseStep 435799 = 653699) B653699
theorem B435819 : Blo 435777 435819 := bstep (se 1 (by rfl) ⟨326864, by rfl⟩ : syracuseStep 435819 = 653729) B653729
theorem B435831 : Blo 435777 435831 := bstep (se 1 (by rfl) ⟨326873, by rfl⟩ : syracuseStep 435831 = 653747) B653747
theorem B468599 : Blo 435777 468599 := bstep (se 1 (by rfl) ⟨351449, by rfl⟩ : syracuseStep 468599 = 702899) B702899
theorem B435851 : Blo 435777 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B435863 : Blo 435777 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B1418903 : Blo 435777 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B435883 : Blo 435777 435883 := bstep (se 1 (by rfl) ⟨326912, by rfl⟩ : syracuseStep 435883 = 653825) B653825
theorem B435895 : Blo 435777 435895 := bstep (se 1 (by rfl) ⟨326921, by rfl⟩ : syracuseStep 435895 = 653843) B653843
theorem B435915 : Blo 435777 435915 := bstep (se 1 (by rfl) ⟨326936, by rfl⟩ : syracuseStep 435915 = 653873) B653873
theorem B435927 : Blo 435777 435927 := bstep (se 1 (by rfl) ⟨326945, by rfl⟩ : syracuseStep 435927 = 653891) B653891
theorem B435947 : Blo 435777 435947 := bstep (se 1 (by rfl) ⟨326960, by rfl⟩ : syracuseStep 435947 = 653921) B653921
theorem B435959 : Blo 435777 435959 := bstep (se 1 (by rfl) ⟨326969, by rfl⟩ : syracuseStep 435959 = 653939) B653939
theorem B435979 : Blo 435777 435979 := bstep (se 1 (by rfl) ⟨326984, by rfl⟩ : syracuseStep 435979 = 653969) B653969
theorem B435991 : Blo 435777 435991 := bstep (se 1 (by rfl) ⟨326993, by rfl⟩ : syracuseStep 435991 = 653987) B653987
theorem B829207 : Blo 435777 829207 := bstep (se 1 (by rfl) ⟨621905, by rfl⟩ : syracuseStep 829207 = 1243811) B1243811
theorem B436011 : Blo 435777 436011 := bstep (se 1 (by rfl) ⟨327008, by rfl⟩ : syracuseStep 436011 = 654017) B654017
theorem B436023 : Blo 435777 436023 := bstep (se 1 (by rfl) ⟨327017, by rfl⟩ : syracuseStep 436023 = 654035) B654035
theorem B436043 : Blo 435777 436043 := bstep (se 1 (by rfl) ⟨327032, by rfl⟩ : syracuseStep 436043 = 654065) B654065
theorem B436055 : Blo 435777 436055 := bstep (se 1 (by rfl) ⟨327041, by rfl⟩ : syracuseStep 436055 = 654083) B654083
theorem B1877849 : Blo 435777 1877849 := bstep (se 2 (by rfl) ⟨704193, by rfl⟩ : syracuseStep 1877849 = 1408387) B1408387
theorem B436075 : Blo 435777 436075 := bstep (se 1 (by rfl) ⟨327056, by rfl⟩ : syracuseStep 436075 = 654113) B654113
theorem B436087 : Blo 435777 436087 := bstep (se 1 (by rfl) ⟨327065, by rfl⟩ : syracuseStep 436087 = 654131) B654131
theorem B436107 : Blo 435777 436107 := bstep (se 1 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 436107 = 654161) B654161
theorem B436119 : Blo 435777 436119 := bstep (se 1 (by rfl) ⟨327089, by rfl⟩ : syracuseStep 436119 = 654179) B654179
theorem B436139 : Blo 435777 436139 := bstep (se 1 (by rfl) ⟨327104, by rfl⟩ : syracuseStep 436139 = 654209) B654209
theorem B1583021 : Blo 435777 1583021 := bstep (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) B593633
theorem B436151 : Blo 435777 436151 := bstep (se 1 (by rfl) ⟨327113, by rfl⟩ : syracuseStep 436151 = 654227) B654227
theorem B436171 : Blo 435777 436171 := bstep (se 1 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 436171 = 654257) B654257
theorem B436183 : Blo 435777 436183 := bstep (se 1 (by rfl) ⟨327137, by rfl⟩ : syracuseStep 436183 = 654275) B654275
theorem B436203 : Blo 435777 436203 := bstep (se 1 (by rfl) ⟨327152, by rfl⟩ : syracuseStep 436203 = 654305) B654305
theorem B436215 : Blo 435777 436215 := bstep (se 1 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 436215 = 654323) B654323
theorem B436235 : Blo 435777 436235 := bstep (se 1 (by rfl) ⟨327176, by rfl⟩ : syracuseStep 436235 = 654353) B654353
theorem B436247 : Blo 435777 436247 := bstep (se 1 (by rfl) ⟨327185, by rfl⟩ : syracuseStep 436247 = 654371) B654371
theorem B436267 : Blo 435777 436267 := bstep (se 1 (by rfl) ⟨327200, by rfl⟩ : syracuseStep 436267 = 654401) B654401
theorem B436279 : Blo 435777 436279 := bstep (se 1 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 436279 = 654419) B654419
theorem B436299 : Blo 435777 436299 := bstep (se 1 (by rfl) ⟨327224, by rfl⟩ : syracuseStep 436299 = 654449) B654449
theorem B436311 : Blo 435777 436311 := bstep (se 1 (by rfl) ⟨327233, by rfl⟩ : syracuseStep 436311 = 654467) B654467
theorem B436331 : Blo 435777 436331 := bstep (se 1 (by rfl) ⟨327248, by rfl⟩ : syracuseStep 436331 = 654497) B654497
theorem B436343 : Blo 435777 436343 := bstep (se 1 (by rfl) ⟨327257, by rfl⟩ : syracuseStep 436343 = 654515) B654515
theorem B436363 : Blo 435777 436363 := bstep (se 1 (by rfl) ⟨327272, by rfl⟩ : syracuseStep 436363 = 654545) B654545
theorem B436375 : Blo 435777 436375 := bstep (se 1 (by rfl) ⟨327281, by rfl⟩ : syracuseStep 436375 = 654563) B654563
theorem B436395 : Blo 435777 436395 := bstep (se 1 (by rfl) ⟨327296, by rfl⟩ : syracuseStep 436395 = 654593) B654593
theorem B469163 : Blo 435777 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B7088309 : Blo 435777 7088309 := bstep (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) B664529
theorem B436407 : Blo 435777 436407 := bstep (se 1 (by rfl) ⟨327305, by rfl⟩ : syracuseStep 436407 = 654611) B654611
theorem B436427 : Blo 435777 436427 := bstep (se 1 (by rfl) ⟨327320, by rfl⟩ : syracuseStep 436427 = 654641) B654641
theorem B436439 : Blo 435777 436439 := bstep (se 1 (by rfl) ⟨327329, by rfl⟩ : syracuseStep 436439 = 654659) B654659
theorem B436459 : Blo 435777 436459 := bstep (se 1 (by rfl) ⟨327344, by rfl⟩ : syracuseStep 436459 = 654689) B654689
theorem B436471 : Blo 435777 436471 := bstep (se 1 (by rfl) ⟨327353, by rfl⟩ : syracuseStep 436471 = 654707) B654707
theorem B436491 : Blo 435777 436491 := bstep (se 1 (by rfl) ⟨327368, by rfl⟩ : syracuseStep 436491 = 654737) B654737
theorem B436503 : Blo 435777 436503 := bstep (se 1 (by rfl) ⟨327377, by rfl⟩ : syracuseStep 436503 = 654755) B654755
theorem B436523 : Blo 435777 436523 := bstep (se 1 (by rfl) ⟨327392, by rfl⟩ : syracuseStep 436523 = 654785) B654785
theorem B436535 : Blo 435777 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B436555 : Blo 435777 436555 := bstep (se 1 (by rfl) ⟨327416, by rfl⟩ : syracuseStep 436555 = 654833) B654833
theorem B436567 : Blo 435777 436567 := bstep (se 1 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 436567 = 654851) B654851
theorem B436587 : Blo 435777 436587 := bstep (se 1 (by rfl) ⟨327440, by rfl⟩ : syracuseStep 436587 = 654881) B654881
theorem B436599 : Blo 435777 436599 := bstep (se 1 (by rfl) ⟨327449, by rfl⟩ : syracuseStep 436599 = 654899) B654899
theorem B436619 : Blo 435777 436619 := bstep (se 1 (by rfl) ⟨327464, by rfl⟩ : syracuseStep 436619 = 654929) B654929
theorem B436631 : Blo 435777 436631 := bstep (se 1 (by rfl) ⟨327473, by rfl⟩ : syracuseStep 436631 = 654947) B654947
theorem B436651 : Blo 435777 436651 := bstep (se 1 (by rfl) ⟨327488, by rfl⟩ : syracuseStep 436651 = 654977) B654977
theorem B436663 : Blo 435777 436663 := bstep (se 1 (by rfl) ⟨327497, by rfl⟩ : syracuseStep 436663 = 654995) B654995
theorem B436683 : Blo 435777 436683 := bstep (se 1 (by rfl) ⟨327512, by rfl⟩ : syracuseStep 436683 = 655025) B655025
theorem B436695 : Blo 435777 436695 := bstep (se 1 (by rfl) ⟨327521, by rfl⟩ : syracuseStep 436695 = 655043) B655043
theorem B436715 : Blo 435777 436715 := bstep (se 1 (by rfl) ⟨327536, by rfl⟩ : syracuseStep 436715 = 655073) B655073
theorem B436727 : Blo 435777 436727 := bstep (se 1 (by rfl) ⟨327545, by rfl⟩ : syracuseStep 436727 = 655091) B655091
theorem B436747 : Blo 435777 436747 := bstep (se 1 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 436747 = 655121) B655121
theorem B436759 : Blo 435777 436759 := bstep (se 1 (by rfl) ⟨327569, by rfl⟩ : syracuseStep 436759 = 655139) B655139
theorem B436779 : Blo 435777 436779 := bstep (se 1 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 436779 = 655169) B655169
theorem B436791 : Blo 435777 436791 := bstep (se 1 (by rfl) ⟨327593, by rfl⟩ : syracuseStep 436791 = 655187) B655187
theorem B436811 : Blo 435777 436811 := bstep (se 1 (by rfl) ⟨327608, by rfl⟩ : syracuseStep 436811 = 655217) B655217
theorem B830027 : Blo 435777 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B436823 : Blo 435777 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B436843 : Blo 435777 436843 := bstep (se 1 (by rfl) ⟨327632, by rfl⟩ : syracuseStep 436843 = 655265) B655265
theorem B436855 : Blo 435777 436855 := bstep (se 1 (by rfl) ⟨327641, by rfl⟩ : syracuseStep 436855 = 655283) B655283
theorem B830081 : Blo 435777 830081 := bstep (se 2 (by rfl) ⟨311280, by rfl⟩ : syracuseStep 830081 = 622561) B622561
theorem B436875 : Blo 435777 436875 := bstep (se 1 (by rfl) ⟨327656, by rfl⟩ : syracuseStep 436875 = 655313) B655313
theorem B436887 : Blo 435777 436887 := bstep (se 1 (by rfl) ⟨327665, by rfl⟩ : syracuseStep 436887 = 655331) B655331
theorem B436907 : Blo 435777 436907 := bstep (se 1 (by rfl) ⟨327680, by rfl⟩ : syracuseStep 436907 = 655361) B655361
theorem B436919 : Blo 435777 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B436939 : Blo 435777 436939 := bstep (se 1 (by rfl) ⟨327704, by rfl⟩ : syracuseStep 436939 = 655409) B655409
theorem B436951 : Blo 435777 436951 := bstep (se 1 (by rfl) ⟨327713, by rfl⟩ : syracuseStep 436951 = 655427) B655427
theorem B436971 : Blo 435777 436971 := bstep (se 1 (by rfl) ⟨327728, by rfl⟩ : syracuseStep 436971 = 655457) B655457
theorem B436983 : Blo 435777 436983 := bstep (se 1 (by rfl) ⟨327737, by rfl⟩ : syracuseStep 436983 = 655475) B655475
theorem B437003 : Blo 435777 437003 := bstep (se 1 (by rfl) ⟨327752, by rfl⟩ : syracuseStep 437003 = 655505) B655505
theorem B437015 : Blo 435777 437015 := bstep (se 1 (by rfl) ⟨327761, by rfl⟩ : syracuseStep 437015 = 655523) B655523
theorem B437035 : Blo 435777 437035 := bstep (se 1 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 437035 = 655553) B655553
theorem B437047 : Blo 435777 437047 := bstep (se 1 (by rfl) ⟨327785, by rfl⟩ : syracuseStep 437047 = 655571) B655571
theorem B437067 : Blo 435777 437067 := bstep (se 1 (by rfl) ⟨327800, by rfl⟩ : syracuseStep 437067 = 655601) B655601
theorem B437079 : Blo 435777 437079 := bstep (se 1 (by rfl) ⟨327809, by rfl⟩ : syracuseStep 437079 = 655619) B655619
theorem B437099 : Blo 435777 437099 := bstep (se 1 (by rfl) ⟨327824, by rfl⟩ : syracuseStep 437099 = 655649) B655649
theorem B437111 : Blo 435777 437111 := bstep (se 1 (by rfl) ⟨327833, by rfl⟩ : syracuseStep 437111 = 655667) B655667
theorem B437131 : Blo 435777 437131 := bstep (se 1 (by rfl) ⟨327848, by rfl⟩ : syracuseStep 437131 = 655697) B655697
theorem B437143 : Blo 435777 437143 := bstep (se 1 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 437143 = 655715) B655715
theorem B437163 : Blo 435777 437163 := bstep (se 1 (by rfl) ⟨327872, by rfl⟩ : syracuseStep 437163 = 655745) B655745
theorem B437175 : Blo 435777 437175 := bstep (se 1 (by rfl) ⟨327881, by rfl⟩ : syracuseStep 437175 = 655763) B655763
theorem B437195 : Blo 435777 437195 := bstep (se 1 (by rfl) ⟨327896, by rfl⟩ : syracuseStep 437195 = 655793) B655793
theorem B437207 : Blo 435777 437207 := bstep (se 1 (by rfl) ⟨327905, by rfl⟩ : syracuseStep 437207 = 655811) B655811
theorem B437227 : Blo 435777 437227 := bstep (se 1 (by rfl) ⟨327920, by rfl⟩ : syracuseStep 437227 = 655841) B655841
theorem B437239 : Blo 435777 437239 := bstep (se 1 (by rfl) ⟨327929, by rfl⟩ : syracuseStep 437239 = 655859) B655859
theorem B3320837 : Blo 435777 3320837 := bstep (se 4 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 3320837 = 622657) B622657
theorem B437259 : Blo 435777 437259 := bstep (se 1 (by rfl) ⟨327944, by rfl⟩ : syracuseStep 437259 = 655889) B655889
theorem B437271 : Blo 435777 437271 := bstep (se 1 (by rfl) ⟨327953, by rfl⟩ : syracuseStep 437271 = 655907) B655907
theorem B437291 : Blo 435777 437291 := bstep (se 1 (by rfl) ⟨327968, by rfl⟩ : syracuseStep 437291 = 655937) B655937
theorem B437303 : Blo 435777 437303 := bstep (se 1 (by rfl) ⟨327977, by rfl⟩ : syracuseStep 437303 = 655955) B655955
theorem B437323 : Blo 435777 437323 := bstep (se 1 (by rfl) ⟨327992, by rfl⟩ : syracuseStep 437323 = 655985) B655985
theorem B437335 : Blo 435777 437335 := bstep (se 1 (by rfl) ⟨328001, by rfl⟩ : syracuseStep 437335 = 656003) B656003
theorem B437355 : Blo 435777 437355 := bstep (se 1 (by rfl) ⟨328016, by rfl⟩ : syracuseStep 437355 = 656033) B656033
theorem B437367 : Blo 435777 437367 := bstep (se 1 (by rfl) ⟨328025, by rfl⟩ : syracuseStep 437367 = 656051) B656051
theorem B437387 : Blo 435777 437387 := bstep (se 1 (by rfl) ⟨328040, by rfl⟩ : syracuseStep 437387 = 656081) B656081
theorem B437399 : Blo 435777 437399 := bstep (se 1 (by rfl) ⟨328049, by rfl⟩ : syracuseStep 437399 = 656099) B656099
theorem B437419 : Blo 435777 437419 := bstep (se 1 (by rfl) ⟨328064, by rfl⟩ : syracuseStep 437419 = 656129) B656129
theorem B437431 : Blo 435777 437431 := bstep (se 1 (by rfl) ⟨328073, by rfl⟩ : syracuseStep 437431 = 656147) B656147
theorem B437451 : Blo 435777 437451 := bstep (se 1 (by rfl) ⟨328088, by rfl⟩ : syracuseStep 437451 = 656177) B656177
theorem B437463 : Blo 435777 437463 := bstep (se 1 (by rfl) ⟨328097, by rfl⟩ : syracuseStep 437463 = 656195) B656195
theorem B437483 : Blo 435777 437483 := bstep (se 1 (by rfl) ⟨328112, by rfl⟩ : syracuseStep 437483 = 656225) B656225
theorem B437495 : Blo 435777 437495 := bstep (se 1 (by rfl) ⟨328121, by rfl⟩ : syracuseStep 437495 = 656243) B656243
theorem B437515 : Blo 435777 437515 := bstep (se 1 (by rfl) ⟨328136, by rfl⟩ : syracuseStep 437515 = 656273) B656273
theorem B437527 : Blo 435777 437527 := bstep (se 1 (by rfl) ⟨328145, by rfl⟩ : syracuseStep 437527 = 656291) B656291
theorem B437547 : Blo 435777 437547 := bstep (se 1 (by rfl) ⟨328160, by rfl⟩ : syracuseStep 437547 = 656321) B656321
theorem B437559 : Blo 435777 437559 := bstep (se 1 (by rfl) ⟨328169, by rfl⟩ : syracuseStep 437559 = 656339) B656339
theorem B437579 : Blo 435777 437579 := bstep (se 1 (by rfl) ⟨328184, by rfl⟩ : syracuseStep 437579 = 656369) B656369
theorem B437591 : Blo 435777 437591 := bstep (se 1 (by rfl) ⟨328193, by rfl⟩ : syracuseStep 437591 = 656387) B656387
theorem B437611 : Blo 435777 437611 := bstep (se 1 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 437611 = 656417) B656417
theorem B437623 : Blo 435777 437623 := bstep (se 1 (by rfl) ⟨328217, by rfl⟩ : syracuseStep 437623 = 656435) B656435
theorem B437643 : Blo 435777 437643 := bstep (se 1 (by rfl) ⟨328232, by rfl⟩ : syracuseStep 437643 = 656465) B656465
theorem B437655 : Blo 435777 437655 := bstep (se 1 (by rfl) ⟨328241, by rfl⟩ : syracuseStep 437655 = 656483) B656483
theorem B437675 : Blo 435777 437675 := bstep (se 1 (by rfl) ⟨328256, by rfl⟩ : syracuseStep 437675 = 656513) B656513
theorem B437687 : Blo 435777 437687 := bstep (se 1 (by rfl) ⟨328265, by rfl⟩ : syracuseStep 437687 = 656531) B656531
theorem B437707 : Blo 435777 437707 := bstep (se 1 (by rfl) ⟨328280, by rfl⟩ : syracuseStep 437707 = 656561) B656561
theorem B437719 : Blo 435777 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B437739 : Blo 435777 437739 := bstep (se 1 (by rfl) ⟨328304, by rfl⟩ : syracuseStep 437739 = 656609) B656609
theorem B437751 : Blo 435777 437751 := bstep (se 1 (by rfl) ⟨328313, by rfl⟩ : syracuseStep 437751 = 656627) B656627
theorem B437771 : Blo 435777 437771 := bstep (se 1 (by rfl) ⟨328328, by rfl⟩ : syracuseStep 437771 = 656657) B656657
theorem B2207249 : Blo 435777 2207249 := bstep (se 2 (by rfl) ⟨827718, by rfl⟩ : syracuseStep 2207249 = 1655437) B1655437
theorem B830999 : Blo 435777 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B437783 : Blo 435777 437783 := bstep (se 1 (by rfl) ⟨328337, by rfl⟩ : syracuseStep 437783 = 656675) B656675
theorem B437803 : Blo 435777 437803 := bstep (se 1 (by rfl) ⟨328352, by rfl⟩ : syracuseStep 437803 = 656705) B656705
theorem B437815 : Blo 435777 437815 := bstep (se 1 (by rfl) ⟨328361, by rfl⟩ : syracuseStep 437815 = 656723) B656723
theorem B437835 : Blo 435777 437835 := bstep (se 1 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 437835 = 656753) B656753
theorem B437847 : Blo 435777 437847 := bstep (se 1 (by rfl) ⟨328385, by rfl⟩ : syracuseStep 437847 = 656771) B656771
theorem B437867 : Blo 435777 437867 := bstep (se 1 (by rfl) ⟨328400, by rfl⟩ : syracuseStep 437867 = 656801) B656801
theorem B437879 : Blo 435777 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B437899 : Blo 435777 437899 := bstep (se 1 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 437899 = 656849) B656849
theorem B437911 : Blo 435777 437911 := bstep (se 1 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 437911 = 656867) B656867
theorem B437931 : Blo 435777 437931 := bstep (se 1 (by rfl) ⟨328448, by rfl⟩ : syracuseStep 437931 = 656897) B656897
theorem B2207411 : Blo 435777 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B437943 : Blo 435777 437943 := bstep (se 1 (by rfl) ⟨328457, by rfl⟩ : syracuseStep 437943 = 656915) B656915
theorem B437963 : Blo 435777 437963 := bstep (se 1 (by rfl) ⟨328472, by rfl⟩ : syracuseStep 437963 = 656945) B656945
theorem B437975 : Blo 435777 437975 := bstep (se 1 (by rfl) ⟨328481, by rfl⟩ : syracuseStep 437975 = 656963) B656963
theorem B437995 : Blo 435777 437995 := bstep (se 1 (by rfl) ⟨328496, by rfl⟩ : syracuseStep 437995 = 656993) B656993
theorem B438007 : Blo 435777 438007 := bstep (se 1 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 438007 = 657011) B657011
theorem B438027 : Blo 435777 438027 := bstep (se 1 (by rfl) ⟨328520, by rfl⟩ : syracuseStep 438027 = 657041) B657041
theorem B438039 : Blo 435777 438039 := bstep (se 1 (by rfl) ⟨328529, by rfl⟩ : syracuseStep 438039 = 657059) B657059
theorem B438059 : Blo 435777 438059 := bstep (se 1 (by rfl) ⟨328544, by rfl⟩ : syracuseStep 438059 = 657089) B657089
theorem B438071 : Blo 435777 438071 := bstep (se 1 (by rfl) ⟨328553, by rfl⟩ : syracuseStep 438071 = 657107) B657107
theorem B438091 : Blo 435777 438091 := bstep (se 1 (by rfl) ⟨328568, by rfl⟩ : syracuseStep 438091 = 657137) B657137
theorem B700247 : Blo 435777 700247 := bstep (se 1 (by rfl) ⟨525185, by rfl⟩ : syracuseStep 700247 = 1050371) B1050371
theorem B438103 : Blo 435777 438103 := bstep (se 1 (by rfl) ⟨328577, by rfl⟩ : syracuseStep 438103 = 657155) B657155
theorem B634711 : Blo 435777 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B438123 : Blo 435777 438123 := bstep (se 1 (by rfl) ⟨328592, by rfl⟩ : syracuseStep 438123 = 657185) B657185
theorem B438135 : Blo 435777 438135 := bstep (se 1 (by rfl) ⟨328601, by rfl⟩ : syracuseStep 438135 = 657203) B657203
theorem B896897 : Blo 435777 896897 := bstep (se 2 (by rfl) ⟨336336, by rfl⟩ : syracuseStep 896897 = 672673) B672673
theorem B438155 : Blo 435777 438155 := bstep (se 1 (by rfl) ⟨328616, by rfl⟩ : syracuseStep 438155 = 657233) B657233
theorem B438167 : Blo 435777 438167 := bstep (se 1 (by rfl) ⟨328625, by rfl⟩ : syracuseStep 438167 = 657251) B657251
theorem B438187 : Blo 435777 438187 := bstep (se 1 (by rfl) ⟨328640, by rfl⟩ : syracuseStep 438187 = 657281) B657281
theorem B438199 : Blo 435777 438199 := bstep (se 1 (by rfl) ⟨328649, by rfl⟩ : syracuseStep 438199 = 657299) B657299
theorem B438219 : Blo 435777 438219 := bstep (se 1 (by rfl) ⟨328664, by rfl⟩ : syracuseStep 438219 = 657329) B657329
theorem B438231 : Blo 435777 438231 := bstep (se 1 (by rfl) ⟨328673, by rfl⟩ : syracuseStep 438231 = 657347) B657347
theorem B438251 : Blo 435777 438251 := bstep (se 1 (by rfl) ⟨328688, by rfl⟩ : syracuseStep 438251 = 657377) B657377
theorem B438263 : Blo 435777 438263 := bstep (se 1 (by rfl) ⟨328697, by rfl⟩ : syracuseStep 438263 = 657395) B657395
theorem B438283 : Blo 435777 438283 := bstep (se 1 (by rfl) ⟨328712, by rfl⟩ : syracuseStep 438283 = 657425) B657425
theorem B438295 : Blo 435777 438295 := bstep (se 1 (by rfl) ⟨328721, by rfl⟩ : syracuseStep 438295 = 657443) B657443
theorem B438315 : Blo 435777 438315 := bstep (se 1 (by rfl) ⟨328736, by rfl⟩ : syracuseStep 438315 = 657473) B657473
theorem B831539 : Blo 435777 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B438327 : Blo 435777 438327 := bstep (se 1 (by rfl) ⟨328745, by rfl⟩ : syracuseStep 438327 = 657491) B657491
theorem B438347 : Blo 435777 438347 := bstep (se 1 (by rfl) ⟨328760, by rfl⟩ : syracuseStep 438347 = 657521) B657521
theorem B438359 : Blo 435777 438359 := bstep (se 1 (by rfl) ⟨328769, by rfl⟩ : syracuseStep 438359 = 657539) B657539
theorem B438379 : Blo 435777 438379 := bstep (se 1 (by rfl) ⟨328784, by rfl⟩ : syracuseStep 438379 = 657569) B657569
theorem B438391 : Blo 435777 438391 := bstep (se 1 (by rfl) ⟨328793, by rfl⟩ : syracuseStep 438391 = 657587) B657587
theorem B3747971 : Blo 435777 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B438411 : Blo 435777 438411 := bstep (se 1 (by rfl) ⟨328808, by rfl⟩ : syracuseStep 438411 = 657617) B657617
theorem B438423 : Blo 435777 438423 := bstep (se 1 (by rfl) ⟨328817, by rfl⟩ : syracuseStep 438423 = 657635) B657635
theorem B438443 : Blo 435777 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B1781939 : Blo 435777 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B438455 : Blo 435777 438455 := bstep (se 1 (by rfl) ⟨328841, by rfl⟩ : syracuseStep 438455 = 657683) B657683
theorem B438475 : Blo 435777 438475 := bstep (se 1 (by rfl) ⟨328856, by rfl⟩ : syracuseStep 438475 = 657713) B657713
theorem B438487 : Blo 435777 438487 := bstep (se 1 (by rfl) ⟨328865, by rfl⟩ : syracuseStep 438487 = 657731) B657731
theorem B438507 : Blo 435777 438507 := bstep (se 1 (by rfl) ⟨328880, by rfl⟩ : syracuseStep 438507 = 657761) B657761
theorem B438519 : Blo 435777 438519 := bstep (se 1 (by rfl) ⟨328889, by rfl⟩ : syracuseStep 438519 = 657779) B657779
theorem B438539 : Blo 435777 438539 := bstep (se 1 (by rfl) ⟨328904, by rfl⟩ : syracuseStep 438539 = 657809) B657809
theorem B438551 : Blo 435777 438551 := bstep (se 1 (by rfl) ⟨328913, by rfl⟩ : syracuseStep 438551 = 657827) B657827
theorem B438571 : Blo 435777 438571 := bstep (se 1 (by rfl) ⟨328928, by rfl⟩ : syracuseStep 438571 = 657857) B657857
theorem B438583 : Blo 435777 438583 := bstep (se 1 (by rfl) ⟨328937, by rfl⟩ : syracuseStep 438583 = 657875) B657875
theorem B438603 : Blo 435777 438603 := bstep (se 1 (by rfl) ⟨328952, by rfl⟩ : syracuseStep 438603 = 657905) B657905
theorem B700759 : Blo 435777 700759 := bstep (se 1 (by rfl) ⟨525569, by rfl⟩ : syracuseStep 700759 = 1051139) B1051139
theorem B438615 : Blo 435777 438615 := bstep (se 1 (by rfl) ⟨328961, by rfl⟩ : syracuseStep 438615 = 657923) B657923
theorem B438635 : Blo 435777 438635 := bstep (se 1 (by rfl) ⟨328976, by rfl⟩ : syracuseStep 438635 = 657953) B657953
theorem B438647 : Blo 435777 438647 := bstep (se 1 (by rfl) ⟨328985, by rfl⟩ : syracuseStep 438647 = 657971) B657971
theorem B438667 : Blo 435777 438667 := bstep (se 1 (by rfl) ⟨329000, by rfl⟩ : syracuseStep 438667 = 658001) B658001
theorem B438679 : Blo 435777 438679 := bstep (se 1 (by rfl) ⟨329009, by rfl⟩ : syracuseStep 438679 = 658019) B658019
theorem B438699 : Blo 435777 438699 := bstep (se 1 (by rfl) ⟨329024, by rfl⟩ : syracuseStep 438699 = 658049) B658049
theorem B438711 : Blo 435777 438711 := bstep (se 1 (by rfl) ⟨329033, by rfl⟩ : syracuseStep 438711 = 658067) B658067
theorem B438731 : Blo 435777 438731 := bstep (se 1 (by rfl) ⟨329048, by rfl⟩ : syracuseStep 438731 = 658097) B658097
theorem B438743 : Blo 435777 438743 := bstep (se 1 (by rfl) ⟨329057, by rfl⟩ : syracuseStep 438743 = 658115) B658115
theorem B438763 : Blo 435777 438763 := bstep (se 1 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 438763 = 658145) B658145
theorem B438775 : Blo 435777 438775 := bstep (se 1 (by rfl) ⟨329081, by rfl⟩ : syracuseStep 438775 = 658163) B658163
theorem B438795 : Blo 435777 438795 := bstep (se 1 (by rfl) ⟨329096, by rfl⟩ : syracuseStep 438795 = 658193) B658193
theorem B438807 : Blo 435777 438807 := bstep (se 1 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 438807 = 658211) B658211
theorem B832025 : Blo 435777 832025 := bstep (se 2 (by rfl) ⟨312009, by rfl⟩ : syracuseStep 832025 = 624019) B624019
theorem B438827 : Blo 435777 438827 := bstep (se 1 (by rfl) ⟨329120, by rfl⟩ : syracuseStep 438827 = 658241) B658241
theorem B438839 : Blo 435777 438839 := bstep (se 1 (by rfl) ⟨329129, by rfl⟩ : syracuseStep 438839 = 658259) B658259
theorem B3551809 : Blo 435777 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B438859 : Blo 435777 438859 := bstep (se 1 (by rfl) ⟨329144, by rfl⟩ : syracuseStep 438859 = 658289) B658289
theorem B438871 : Blo 435777 438871 := bstep (se 1 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 438871 = 658307) B658307
theorem B1684061 : Blo 435777 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B438891 : Blo 435777 438891 := bstep (se 1 (by rfl) ⟨329168, by rfl⟩ : syracuseStep 438891 = 658337) B658337
theorem B438903 : Blo 435777 438903 := bstep (se 1 (by rfl) ⟨329177, by rfl⟩ : syracuseStep 438903 = 658355) B658355
theorem B438923 : Blo 435777 438923 := bstep (se 1 (by rfl) ⟨329192, by rfl⟩ : syracuseStep 438923 = 658385) B658385
theorem B438935 : Blo 435777 438935 := bstep (se 1 (by rfl) ⟨329201, by rfl⟩ : syracuseStep 438935 = 658403) B658403
theorem B438955 : Blo 435777 438955 := bstep (se 1 (by rfl) ⟨329216, by rfl⟩ : syracuseStep 438955 = 658433) B658433
theorem B438967 : Blo 435777 438967 := bstep (se 1 (by rfl) ⟨329225, by rfl⟩ : syracuseStep 438967 = 658451) B658451
theorem B701131 : Blo 435777 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B438987 : Blo 435777 438987 := bstep (se 1 (by rfl) ⟨329240, by rfl⟩ : syracuseStep 438987 = 658481) B658481
theorem B438999 : Blo 435777 438999 := bstep (se 1 (by rfl) ⟨329249, by rfl⟩ : syracuseStep 438999 = 658499) B658499
theorem B439019 : Blo 435777 439019 := bstep (se 1 (by rfl) ⟨329264, by rfl⟩ : syracuseStep 439019 = 658529) B658529
theorem B439031 : Blo 435777 439031 := bstep (se 1 (by rfl) ⟨329273, by rfl⟩ : syracuseStep 439031 = 658547) B658547
theorem B439051 : Blo 435777 439051 := bstep (se 1 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 439051 = 658577) B658577
theorem B439063 : Blo 435777 439063 := bstep (se 1 (by rfl) ⟨329297, by rfl⟩ : syracuseStep 439063 = 658595) B658595
theorem B439083 : Blo 435777 439083 := bstep (se 1 (by rfl) ⟨329312, by rfl⟩ : syracuseStep 439083 = 658625) B658625
theorem B439095 : Blo 435777 439095 := bstep (se 1 (by rfl) ⟨329321, by rfl⟩ : syracuseStep 439095 = 658643) B658643
theorem B439115 : Blo 435777 439115 := bstep (se 1 (by rfl) ⟨329336, by rfl⟩ : syracuseStep 439115 = 658673) B658673
theorem B439127 : Blo 435777 439127 := bstep (se 1 (by rfl) ⟨329345, by rfl⟩ : syracuseStep 439127 = 658691) B658691
theorem B439147 : Blo 435777 439147 := bstep (se 1 (by rfl) ⟨329360, by rfl⟩ : syracuseStep 439147 = 658721) B658721
theorem B439159 : Blo 435777 439159 := bstep (se 1 (by rfl) ⟨329369, by rfl⟩ : syracuseStep 439159 = 658739) B658739
theorem B439179 : Blo 435777 439179 := bstep (se 1 (by rfl) ⟨329384, by rfl⟩ : syracuseStep 439179 = 658769) B658769
theorem B439191 : Blo 435777 439191 := bstep (se 1 (by rfl) ⟨329393, by rfl⟩ : syracuseStep 439191 = 658787) B658787
theorem B439211 : Blo 435777 439211 := bstep (se 1 (by rfl) ⟨329408, by rfl⟩ : syracuseStep 439211 = 658817) B658817
theorem B2110387 : Blo 435777 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B439223 : Blo 435777 439223 := bstep (se 1 (by rfl) ⟨329417, by rfl⟩ : syracuseStep 439223 = 658835) B658835
theorem B701387 : Blo 435777 701387 := bstep (se 1 (by rfl) ⟨526040, by rfl⟩ : syracuseStep 701387 = 1052081) B1052081
theorem B439243 : Blo 435777 439243 := bstep (se 1 (by rfl) ⟨329432, by rfl⟩ : syracuseStep 439243 = 658865) B658865
theorem B439255 : Blo 435777 439255 := bstep (se 1 (by rfl) ⟨329441, by rfl⟩ : syracuseStep 439255 = 658883) B658883
theorem B439275 : Blo 435777 439275 := bstep (se 1 (by rfl) ⟨329456, by rfl⟩ : syracuseStep 439275 = 658913) B658913
theorem B439287 : Blo 435777 439287 := bstep (se 1 (by rfl) ⟨329465, by rfl⟩ : syracuseStep 439287 = 658931) B658931
theorem B439307 : Blo 435777 439307 := bstep (se 1 (by rfl) ⟨329480, by rfl⟩ : syracuseStep 439307 = 658961) B658961
theorem B439319 : Blo 435777 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B439339 : Blo 435777 439339 := bstep (se 1 (by rfl) ⟨329504, by rfl⟩ : syracuseStep 439339 = 659009) B659009
theorem B439351 : Blo 435777 439351 := bstep (se 1 (by rfl) ⟨329513, by rfl⟩ : syracuseStep 439351 = 659027) B659027
theorem B439371 : Blo 435777 439371 := bstep (se 1 (by rfl) ⟨329528, by rfl⟩ : syracuseStep 439371 = 659057) B659057
theorem B439383 : Blo 435777 439383 := bstep (se 1 (by rfl) ⟨329537, by rfl⟩ : syracuseStep 439383 = 659075) B659075
theorem B439403 : Blo 435777 439403 := bstep (se 1 (by rfl) ⟨329552, by rfl⟩ : syracuseStep 439403 = 659105) B659105
theorem B439415 : Blo 435777 439415 := bstep (se 1 (by rfl) ⟨329561, by rfl⟩ : syracuseStep 439415 = 659123) B659123
theorem B701579 : Blo 435777 701579 := bstep (se 1 (by rfl) ⟨526184, by rfl⟩ : syracuseStep 701579 = 1052369) B1052369
theorem B439435 : Blo 435777 439435 := bstep (se 1 (by rfl) ⟨329576, by rfl⟩ : syracuseStep 439435 = 659153) B659153
theorem B439447 : Blo 435777 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B439467 : Blo 435777 439467 := bstep (se 1 (by rfl) ⟨329600, by rfl⟩ : syracuseStep 439467 = 659201) B659201
theorem B439479 : Blo 435777 439479 := bstep (se 1 (by rfl) ⟨329609, by rfl⟩ : syracuseStep 439479 = 659219) B659219
theorem B439499 : Blo 435777 439499 := bstep (se 1 (by rfl) ⟨329624, by rfl⟩ : syracuseStep 439499 = 659249) B659249
theorem B439511 : Blo 435777 439511 := bstep (se 1 (by rfl) ⟨329633, by rfl⟩ : syracuseStep 439511 = 659267) B659267
theorem B3650777 : Blo 435777 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B439531 : Blo 435777 439531 := bstep (se 1 (by rfl) ⟨329648, by rfl⟩ : syracuseStep 439531 = 659297) B659297
theorem B439543 : Blo 435777 439543 := bstep (se 1 (by rfl) ⟨329657, by rfl⟩ : syracuseStep 439543 = 659315) B659315
theorem B1684739 : Blo 435777 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B1783043 : Blo 435777 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B439563 : Blo 435777 439563 := bstep (se 1 (by rfl) ⟨329672, by rfl⟩ : syracuseStep 439563 = 659345) B659345
theorem B439575 : Blo 435777 439575 := bstep (se 1 (by rfl) ⟨329681, by rfl⟩ : syracuseStep 439575 = 659363) B659363
theorem B439595 : Blo 435777 439595 := bstep (se 1 (by rfl) ⟨329696, by rfl⟩ : syracuseStep 439595 = 659393) B659393
theorem B439607 : Blo 435777 439607 := bstep (se 1 (by rfl) ⟨329705, by rfl⟩ : syracuseStep 439607 = 659411) B659411
theorem B439627 : Blo 435777 439627 := bstep (se 1 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 439627 = 659441) B659441
theorem B439639 : Blo 435777 439639 := bstep (se 1 (by rfl) ⟨329729, by rfl⟩ : syracuseStep 439639 = 659459) B659459
theorem B439659 : Blo 435777 439659 := bstep (se 1 (by rfl) ⟨329744, by rfl⟩ : syracuseStep 439659 = 659489) B659489
theorem B439671 : Blo 435777 439671 := bstep (se 1 (by rfl) ⟨329753, by rfl⟩ : syracuseStep 439671 = 659507) B659507
theorem B3323267 : Blo 435777 3323267 := bstep (se 1 (by rfl) ⟨2492450, by rfl⟩ : syracuseStep 3323267 = 4984901) B4984901
theorem B439691 : Blo 435777 439691 := bstep (se 1 (by rfl) ⟨329768, by rfl⟩ : syracuseStep 439691 = 659537) B659537
theorem B439703 : Blo 435777 439703 := bstep (se 1 (by rfl) ⟨329777, by rfl⟩ : syracuseStep 439703 = 659555) B659555
theorem B439723 : Blo 435777 439723 := bstep (se 1 (by rfl) ⟨329792, by rfl⟩ : syracuseStep 439723 = 659585) B659585
theorem B1684909 : Blo 435777 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B439735 : Blo 435777 439735 := bstep (se 1 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 439735 = 659603) B659603
theorem B439755 : Blo 435777 439755 := bstep (se 1 (by rfl) ⟨329816, by rfl⟩ : syracuseStep 439755 = 659633) B659633
theorem B439767 : Blo 435777 439767 := bstep (se 1 (by rfl) ⟨329825, by rfl⟩ : syracuseStep 439767 = 659651) B659651
theorem B2242009 : Blo 435777 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B800279 : Blo 435777 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B2209355 : Blo 435777 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B931457 : Blo 435777 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B702361 : Blo 435777 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B833483 : Blo 435777 833483 := bstep (se 1 (by rfl) ⟨625112, by rfl⟩ : syracuseStep 833483 = 1250225) B1250225
theorem B931799 : Blo 435777 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B4995107 : Blo 435777 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B833665 : Blo 435777 833665 := bstep (se 2 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 833665 = 625249) B625249
theorem B735385 : Blo 435777 735385 := bstep (se 2 (by rfl) ⟨275769, by rfl⟩ : syracuseStep 735385 = 551539) B551539
theorem B932107 : Blo 435777 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B834113 : Blo 435777 834113 := bstep (se 2 (by rfl) ⟨312792, by rfl⟩ : syracuseStep 834113 = 625585) B625585
theorem B4209245 : Blo 435777 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B735959 : Blo 435777 735959 := bstep (se 1 (by rfl) ⟨551969, by rfl⟩ : syracuseStep 735959 = 1103939) B1103939
theorem B1391411 : Blo 435777 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B736087 : Blo 435777 736087 := bstep (se 1 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 736087 = 1104131) B1104131
theorem B7093109 : Blo 435777 7093109 := bstep (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) B664979
theorem B834455 : Blo 435777 834455 := bstep (se 1 (by rfl) ⟨625841, by rfl⟩ : syracuseStep 834455 = 1251683) B1251683
theorem B3980249 : Blo 435777 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B3750947 : Blo 435777 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B932953 : Blo 435777 932953 := bstep (se 2 (by rfl) ⟨349857, by rfl⟩ : syracuseStep 932953 = 699715) B699715
theorem B2211137 : Blo 435777 2211137 := bstep (se 2 (by rfl) ⟨829176, by rfl⟩ : syracuseStep 2211137 = 1658353) B1658353
theorem B736715 : Blo 435777 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B3554765 : Blo 435777 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B736843 : Blo 435777 736843 := bstep (se 1 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 736843 = 1105265) B1105265
theorem B5619293 : Blo 435777 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B1326809 : Blo 435777 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B736985 : Blo 435777 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B737113 : Blo 435777 737113 := bstep (se 2 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 737113 = 552835) B552835
theorem B2801729 : Blo 435777 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B999641 : Blo 435777 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B934259 : Blo 435777 934259 := bstep (se 1 (by rfl) ⟨700694, by rfl⟩ : syracuseStep 934259 = 1401389) B1401389
theorem B737687 : Blo 435777 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B737815 : Blo 435777 737815 := bstep (se 1 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 737815 = 1106723) B1106723
theorem B4571741 : Blo 435777 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B3326669 : Blo 435777 3326669 := bstep (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) B1247501
theorem B1065793 : Blo 435777 1065793 := bstep (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) B799345
theorem B5686193 : Blo 435777 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B738443 : Blo 435777 738443 := bstep (se 1 (by rfl) ⟨553832, by rfl⟩ : syracuseStep 738443 = 1107665) B1107665
theorem B3327155 : Blo 435777 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B2213081 : Blo 435777 2213081 := bstep (se 2 (by rfl) ⟨829905, by rfl⟩ : syracuseStep 2213081 = 1659811) B1659811
theorem B738571 : Blo 435777 738571 := bstep (se 1 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 738571 = 1107857) B1107857
theorem B738713 : Blo 435777 738713 := bstep (se 2 (by rfl) ⟨277017, by rfl⟩ : syracuseStep 738713 = 554035) B554035
theorem B738841 : Blo 435777 738841 := bstep (se 2 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 738841 = 554131) B554131
theorem B1656395 : Blo 435777 1656395 := bstep (se 1 (by rfl) ⟨1242296, by rfl⟩ : syracuseStep 1656395 = 2484593) B2484593
theorem B1656409 : Blo 435777 1656409 := bstep (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) B1242307
theorem B1328791 : Blo 435777 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B902963 : Blo 435777 902963 := bstep (se 1 (by rfl) ⟨677222, by rfl⟩ : syracuseStep 902963 = 1354445) B1354445
theorem B935831 : Blo 435777 935831 := bstep (se 1 (by rfl) ⟨701873, by rfl⟩ : syracuseStep 935831 = 1403747) B1403747
theorem B6932441 : Blo 435777 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B739415 : Blo 435777 739415 := bstep (se 1 (by rfl) ⟨554561, by rfl⟩ : syracuseStep 739415 = 1109123) B1109123
theorem B1853585 : Blo 435777 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B936139 : Blo 435777 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B739543 : Blo 435777 739543 := bstep (se 1 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 739543 = 1109315) B1109315
theorem B2869465 : Blo 435777 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1493441 : Blo 435777 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B1657367 : Blo 435777 1657367 := bstep (se 1 (by rfl) ⟨1243025, by rfl⟩ : syracuseStep 1657367 = 2486051) B2486051
theorem B3328613 : Blo 435777 3328613 := bstep (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) B624115
theorem B2214701 : Blo 435777 2214701 := bstep (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) B830513
theorem B740171 : Blo 435777 740171 := bstep (se 1 (by rfl) ⟨555128, by rfl⟩ : syracuseStep 740171 = 1110257) B1110257
theorem B740299 : Blo 435777 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B3329099 : Blo 435777 3329099 := bstep (se 1 (by rfl) ⟨2496824, by rfl⟩ : syracuseStep 3329099 = 4993649) B4993649
theorem B740441 : Blo 435777 740441 := bstep (se 2 (by rfl) ⟨277665, by rfl⟩ : syracuseStep 740441 = 555331) B555331
theorem B445655 : Blo 435777 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B740569 : Blo 435777 740569 := bstep (se 2 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 740569 = 555427) B555427
theorem B1625437 : Blo 435777 1625437 := bstep (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) B609539
theorem B937369 : Blo 435777 937369 := bstep (se 2 (by rfl) ⟨351513, by rfl⟩ : syracuseStep 937369 = 703027) B703027
theorem B3558917 : Blo 435777 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B1658627 : Blo 435777 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B741143 : Blo 435777 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B479083 : Blo 435777 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B741271 : Blo 435777 741271 := bstep (se 1 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 741271 = 1111907) B1111907
theorem B479191 : Blo 435777 479191 := bstep (se 1 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 479191 = 718787) B718787
theorem B2805853 : Blo 435777 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B1397213 : Blo 435777 1397213 := bstep (se 3 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 1397213 = 523955) B523955
theorem B741899 : Blo 435777 741899 := bstep (se 1 (by rfl) ⟨556424, by rfl⟩ : syracuseStep 741899 = 1112849) B1112849
theorem B742027 : Blo 435777 742027 := bstep (se 1 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 742027 = 1113041) B1113041
theorem B1692311 : Blo 435777 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B840385 : Blo 435777 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B742553 : Blo 435777 742553 := bstep (se 2 (by rfl) ⟨278457, by rfl⟩ : syracuseStep 742553 = 556915) B556915
theorem B1103179 : Blo 435777 1103179 := bstep (se 1 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 1103179 = 1654769) B1654769
theorem B1103321 : Blo 435777 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B26891747 : Blo 435777 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B3168179 : Blo 435777 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B5593049 : Blo 435777 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B1104151 : Blo 435777 1104151 := bstep (se 1 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 1104151 = 1656227) B1656227
theorem B5691713 : Blo 435777 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B1989137 : Blo 435777 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B2218589 : Blo 435777 2218589 := bstep (se 3 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 2218589 = 831971) B831971
theorem B1104587 : Blo 435777 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B1661741 : Blo 435777 1661741 := bstep (se 3 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 1661741 = 623153) B623153
theorem B1104961 : Blo 435777 1104961 := bstep (se 2 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 1104961 = 828721) B828721
theorem B1924355 : Blo 435777 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1662515 : Blo 435777 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B1105559 : Blo 435777 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B8413253 : Blo 435777 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B3334445 : Blo 435777 3334445 := bstep (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) B1250417
theorem B2810213 : Blo 435777 2810213 := bstep (se 4 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 2810213 = 526915) B526915
theorem B8020403 : Blo 435777 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B1106369 : Blo 435777 1106369 := bstep (se 2 (by rfl) ⟨414888, by rfl⟩ : syracuseStep 1106369 = 829777) B829777
theorem B2220695 : Blo 435777 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B4219543 : Blo 435777 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B1106905 : Blo 435777 1106905 := bstep (se 2 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 1106905 = 830179) B830179
theorem B1664003 : Blo 435777 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B2876737 : Blo 435777 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B2811287 : Blo 435777 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B5006771 : Blo 435777 5006771 := bstep (se 1 (by rfl) ⟨3755078, by rfl⟩ : syracuseStep 5006771 = 7510157) B7510157
theorem B1664459 : Blo 435777 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B6743569 : Blo 435777 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1664657 : Blo 435777 1664657 := bstep (se 2 (by rfl) ⟨624246, by rfl⟩ : syracuseStep 1664657 = 1248493) B1248493
theorem B747481 : Blo 435777 747481 := bstep (se 2 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 747481 = 560611) B560611
theorem B1108019 : Blo 435777 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B1861805 : Blo 435777 1861805 := bstep (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) B698177
theorem B1108313 : Blo 435777 1108313 := bstep (se 2 (by rfl) ⟨415617, by rfl⟩ : syracuseStep 1108313 = 831235) B831235
theorem B60615029 : Blo 435777 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B1665431 : Blo 435777 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B3041837 : Blo 435777 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B2255435 : Blo 435777 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B1665629 : Blo 435777 1665629 := bstep (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) B624611
theorem B551767 : Blo 435777 551767 := bstep (se 1 (by rfl) ⟨413825, by rfl⟩ : syracuseStep 551767 = 827651) B827651
theorem B5008229 : Blo 435777 5008229 := bstep (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) B939043
theorem B7466417 : Blo 435777 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B1797569 : Blo 435777 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B5992141 : Blo 435777 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B1929053 : Blo 435777 1929053 := bstep (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) B723395
theorem B1109963 : Blo 435777 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B1863769 : Blo 435777 1863769 := bstep (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) B1397827
theorem B3338333 : Blo 435777 3338333 := bstep (se 3 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 3338333 = 1251875) B1251875
theorem B2224259 : Blo 435777 2224259 := bstep (se 1 (by rfl) ⟨1668194, by rfl⟩ : syracuseStep 2224259 = 3336389) B3336389
theorem B1241419 : Blo 435777 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B1405387 : Blo 435777 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B1667587 : Blo 435777 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B553483 : Blo 435777 553483 := bstep (se 1 (by rfl) ⟨415112, by rfl⟩ : syracuseStep 553483 = 830225) B830225
theorem B2486801 : Blo 435777 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1241693 : Blo 435777 1241693 := bstep (se 3 (by rfl) ⟨232817, by rfl⟩ : syracuseStep 1241693 = 465635) B465635
theorem B1405619 : Blo 435777 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B1471283 : Blo 435777 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B1667891 : Blo 435777 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B2814851 : Blo 435777 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1110935 : Blo 435777 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B5600177 : Blo 435777 5600177 := bstep (se 2 (by rfl) ⟨2100066, by rfl⟩ : syracuseStep 5600177 = 4200133) B4200133
theorem B750551 : Blo 435777 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B2487257 : Blo 435777 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B1864727 : Blo 435777 1864727 := bstep (se 1 (by rfl) ⟨1398545, by rfl⟩ : syracuseStep 1864727 = 2797091) B2797091
theorem B1471553 : Blo 435777 1471553 := bstep (se 2 (by rfl) ⟨551832, by rfl⟩ : syracuseStep 1471553 = 1103665) B1103665
theorem B1668545 : Blo 435777 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B1897931 : Blo 435777 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B554455 : Blo 435777 554455 := bstep (se 1 (by rfl) ⟨415841, by rfl⟩ : syracuseStep 554455 = 831683) B831683
theorem B980531 : Blo 435777 980531 := bstep (se 1 (by rfl) ⟨735398, by rfl⟩ : syracuseStep 980531 = 1470797) B1470797
theorem B1111603 : Blo 435777 1111603 := bstep (se 1 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 1111603 = 1667405) B1667405
theorem B980567 : Blo 435777 980567 := bstep (se 1 (by rfl) ⟨735425, by rfl⟩ : syracuseStep 980567 = 1470851) B1470851
theorem B1767005 : Blo 435777 1767005 := bstep (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) B662627
theorem B1472093 : Blo 435777 1472093 := bstep (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) B552035
theorem B1111745 : Blo 435777 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B980747 : Blo 435777 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B980801 : Blo 435777 980801 := bstep (se 2 (by rfl) ⟨367800, by rfl⟩ : syracuseStep 980801 = 735601) B735601
theorem B1570711 : Blo 435777 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B981017 : Blo 435777 981017 := bstep (se 2 (by rfl) ⟨367881, by rfl⟩ : syracuseStep 981017 = 735763) B735763
theorem B8419403 : Blo 435777 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B981107 : Blo 435777 981107 := bstep (se 1 (by rfl) ⟨735830, by rfl⟩ : syracuseStep 981107 = 1471661) B1471661
theorem B981143 : Blo 435777 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B555275 : Blo 435777 555275 := bstep (se 1 (by rfl) ⟨416456, by rfl⟩ : syracuseStep 555275 = 832913) B832913
theorem B620875 : Blo 435777 620875 := bstep (se 1 (by rfl) ⟨465656, by rfl⟩ : syracuseStep 620875 = 931313) B931313
theorem B2357579 : Blo 435777 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B981323 : Blo 435777 981323 := bstep (se 1 (by rfl) ⟨735992, by rfl⟩ : syracuseStep 981323 = 1471985) B1471985
theorem B981377 : Blo 435777 981377 := bstep (se 2 (by rfl) ⟨368016, by rfl⟩ : syracuseStep 981377 = 736033) B736033
theorem B653771 : Blo 435777 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B653783 : Blo 435777 653783 := bstep (se 1 (by rfl) ⟨490337, by rfl⟩ : syracuseStep 653783 = 980675) B980675
theorem B653849 : Blo 435777 653849 := bstep (se 2 (by rfl) ⟨245193, by rfl⟩ : syracuseStep 653849 = 490387) B490387
theorem B981593 : Blo 435777 981593 := bstep (se 2 (by rfl) ⟨368097, by rfl⟩ : syracuseStep 981593 = 736195) B736195
theorem B653963 : Blo 435777 653963 := bstep (se 1 (by rfl) ⟨490472, by rfl⟩ : syracuseStep 653963 = 980945) B980945
theorem B653975 : Blo 435777 653975 := bstep (se 1 (by rfl) ⟨490481, by rfl⟩ : syracuseStep 653975 = 980963) B980963
theorem B1768087 : Blo 435777 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B981683 : Blo 435777 981683 := bstep (se 1 (by rfl) ⟨736262, by rfl⟩ : syracuseStep 981683 = 1472525) B1472525
theorem B1178315 : Blo 435777 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1473227 : Blo 435777 1473227 := bstep (se 1 (by rfl) ⟨1104920, by rfl⟩ : syracuseStep 1473227 = 2209841) B2209841
theorem B981719 : Blo 435777 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B654041 : Blo 435777 654041 := bstep (se 2 (by rfl) ⟨245265, by rfl⟩ : syracuseStep 654041 = 490531) B490531
theorem B490315 : Blo 435777 490315 := bstep (se 1 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 490315 = 735473) B735473
theorem B1178443 : Blo 435777 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B654155 : Blo 435777 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B654167 : Blo 435777 654167 := bstep (se 1 (by rfl) ⟨490625, by rfl⟩ : syracuseStep 654167 = 981251) B981251
theorem B1243993 : Blo 435777 1243993 := bstep (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) B932995
theorem B981899 : Blo 435777 981899 := bstep (se 1 (by rfl) ⟨736424, by rfl⟩ : syracuseStep 981899 = 1472849) B1472849
theorem B654233 : Blo 435777 654233 := bstep (se 2 (by rfl) ⟨245337, by rfl⟩ : syracuseStep 654233 = 490675) B490675
theorem B1113011 : Blo 435777 1113011 := bstep (se 1 (by rfl) ⟨834758, by rfl⟩ : syracuseStep 1113011 = 1669517) B1669517
theorem B490423 : Blo 435777 490423 := bstep (se 1 (by rfl) ⟨367817, by rfl⟩ : syracuseStep 490423 = 735635) B735635
theorem B981953 : Blo 435777 981953 := bstep (se 2 (by rfl) ⟨368232, by rfl⟩ : syracuseStep 981953 = 736465) B736465
theorem B555979 : Blo 435777 555979 := bstep (se 1 (by rfl) ⟨416984, by rfl⟩ : syracuseStep 555979 = 833969) B833969
theorem B1473497 : Blo 435777 1473497 := bstep (se 2 (by rfl) ⟨552561, by rfl⟩ : syracuseStep 1473497 = 1105123) B1105123
theorem B654347 : Blo 435777 654347 := bstep (se 1 (by rfl) ⟨490760, by rfl⟩ : syracuseStep 654347 = 981521) B981521
theorem B654359 : Blo 435777 654359 := bstep (se 1 (by rfl) ⟨490769, by rfl⟩ : syracuseStep 654359 = 981539) B981539
theorem B883801 : Blo 435777 883801 := bstep (se 2 (by rfl) ⟨331425, by rfl⟩ : syracuseStep 883801 = 662851) B662851
theorem B654425 : Blo 435777 654425 := bstep (se 2 (by rfl) ⟨245409, by rfl⟩ : syracuseStep 654425 = 490819) B490819
theorem B490603 : Blo 435777 490603 := bstep (se 1 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 490603 = 735905) B735905
theorem B982169 : Blo 435777 982169 := bstep (se 2 (by rfl) ⟨368313, by rfl⟩ : syracuseStep 982169 = 736627) B736627
theorem B654539 : Blo 435777 654539 := bstep (se 1 (by rfl) ⟨490904, by rfl⟩ : syracuseStep 654539 = 981809) B981809
theorem B490711 : Blo 435777 490711 := bstep (se 1 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 490711 = 736067) B736067
theorem B654551 : Blo 435777 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B556247 : Blo 435777 556247 := bstep (se 1 (by rfl) ⟨417185, by rfl⟩ : syracuseStep 556247 = 834371) B834371
theorem B982259 : Blo 435777 982259 := bstep (se 1 (by rfl) ⟨736694, by rfl⟩ : syracuseStep 982259 = 1473389) B1473389
theorem B982295 : Blo 435777 982295 := bstep (se 1 (by rfl) ⟨736721, by rfl⟩ : syracuseStep 982295 = 1473443) B1473443
theorem B654617 : Blo 435777 654617 := bstep (se 2 (by rfl) ⟨245481, by rfl⟩ : syracuseStep 654617 = 490963) B490963
theorem B3374401 : Blo 435777 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B3734849 : Blo 435777 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B4717925 : Blo 435777 4717925 := bstep (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) B884611
theorem B490891 : Blo 435777 490891 := bstep (se 1 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 490891 = 736337) B736337
theorem B654731 : Blo 435777 654731 := bstep (se 1 (by rfl) ⟨491048, by rfl⟩ : syracuseStep 654731 = 982097) B982097
theorem B654743 : Blo 435777 654743 := bstep (se 1 (by rfl) ⟨491057, by rfl⟩ : syracuseStep 654743 = 982115) B982115
theorem B1244609 : Blo 435777 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B982475 : Blo 435777 982475 := bstep (se 1 (by rfl) ⟨736856, by rfl⟩ : syracuseStep 982475 = 1473713) B1473713
theorem B654809 : Blo 435777 654809 := bstep (se 2 (by rfl) ⟨245553, by rfl⟩ : syracuseStep 654809 = 491107) B491107
theorem B490999 : Blo 435777 490999 := bstep (se 1 (by rfl) ⟨368249, by rfl⟩ : syracuseStep 490999 = 736499) B736499
theorem B982529 : Blo 435777 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B4750883 : Blo 435777 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B654923 : Blo 435777 654923 := bstep (se 1 (by rfl) ⟨491192, by rfl⟩ : syracuseStep 654923 = 982385) B982385
theorem B654935 : Blo 435777 654935 := bstep (se 1 (by rfl) ⟨491201, by rfl⟩ : syracuseStep 654935 = 982403) B982403
theorem B2358877 : Blo 435777 2358877 := bstep (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) B884579
theorem B5308055 : Blo 435777 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B1474199 : Blo 435777 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B655001 : Blo 435777 655001 := bstep (se 2 (by rfl) ⟨245625, by rfl⟩ : syracuseStep 655001 = 491251) B491251
theorem B491179 : Blo 435777 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B40402637 : Blo 435777 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B982745 : Blo 435777 982745 := bstep (se 2 (by rfl) ⟨368529, by rfl⟩ : syracuseStep 982745 = 737059) B737059
theorem B655115 : Blo 435777 655115 := bstep (se 1 (by rfl) ⟨491336, by rfl⟩ : syracuseStep 655115 = 982673) B982673
theorem B491287 : Blo 435777 491287 := bstep (se 1 (by rfl) ⟨368465, by rfl⟩ : syracuseStep 491287 = 736931) B736931
theorem B655127 : Blo 435777 655127 := bstep (se 1 (by rfl) ⟨491345, by rfl⟩ : syracuseStep 655127 = 982691) B982691
theorem B622361 : Blo 435777 622361 := bstep (se 2 (by rfl) ⟨233385, by rfl⟩ : syracuseStep 622361 = 466771) B466771
theorem B982835 : Blo 435777 982835 := bstep (se 1 (by rfl) ⟨737126, by rfl⟩ : syracuseStep 982835 = 1474253) B1474253
theorem B982871 : Blo 435777 982871 := bstep (se 1 (by rfl) ⟨737153, by rfl⟩ : syracuseStep 982871 = 1474307) B1474307
theorem B655193 : Blo 435777 655193 := bstep (se 2 (by rfl) ⟨245697, by rfl⟩ : syracuseStep 655193 = 491395) B491395
theorem B1572787 : Blo 435777 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B491467 : Blo 435777 491467 := bstep (se 1 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 491467 = 737201) B737201
theorem B655307 : Blo 435777 655307 := bstep (se 1 (by rfl) ⟨491480, by rfl⟩ : syracuseStep 655307 = 982961) B982961
theorem B655319 : Blo 435777 655319 := bstep (se 1 (by rfl) ⟨491489, by rfl⟩ : syracuseStep 655319 = 982979) B982979
theorem B655367 : Blo 435777 655367 := bstep (se 1 (by rfl) ⟨491525, by rfl⟩ : syracuseStep 655367 = 983051) B983051
theorem B655403 : Blo 435777 655403 := bstep (se 1 (by rfl) ⟨491552, by rfl⟩ : syracuseStep 655403 = 983105) B983105
theorem B1867819 : Blo 435777 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B655433 : Blo 435777 655433 := bstep (se 2 (by rfl) ⟨245787, by rfl⟩ : syracuseStep 655433 = 491575) B491575
theorem B983159 : Blo 435777 983159 := bstep (se 1 (by rfl) ⟨737369, by rfl⟩ : syracuseStep 983159 = 1474739) B1474739
theorem B655547 : Blo 435777 655547 := bstep (se 1 (by rfl) ⟨491660, by rfl⟩ : syracuseStep 655547 = 983321) B983321
theorem B655607 : Blo 435777 655607 := bstep (se 1 (by rfl) ⟨491705, by rfl⟩ : syracuseStep 655607 = 983411) B983411
theorem B1245451 : Blo 435777 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B655631 : Blo 435777 655631 := bstep (se 1 (by rfl) ⟨491723, by rfl⟩ : syracuseStep 655631 = 983447) B983447
theorem B491791 : Blo 435777 491791 := bstep (se 1 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 491791 = 737687) B737687
theorem B983339 : Blo 435777 983339 := bstep (se 1 (by rfl) ⟨737504, by rfl⟩ : syracuseStep 983339 = 1475009) B1475009
theorem B655673 : Blo 435777 655673 := bstep (se 2 (by rfl) ⟨245877, by rfl⟩ : syracuseStep 655673 = 491755) B491755
theorem B655751 : Blo 435777 655751 := bstep (se 1 (by rfl) ⟨491813, by rfl⟩ : syracuseStep 655751 = 983627) B983627
theorem B14418323 : Blo 435777 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B3047827 : Blo 435777 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B655787 : Blo 435777 655787 := bstep (se 1 (by rfl) ⟨491840, by rfl⟩ : syracuseStep 655787 = 983681) B983681
theorem B655817 : Blo 435777 655817 := bstep (se 2 (by rfl) ⟨245931, by rfl⟩ : syracuseStep 655817 = 491863) B491863
theorem B1245725 : Blo 435777 1245725 := bstep (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) B467147
theorem B655931 : Blo 435777 655931 := bstep (se 1 (by rfl) ⟨491948, by rfl⟩ : syracuseStep 655931 = 983897) B983897
theorem B655991 : Blo 435777 655991 := bstep (se 1 (by rfl) ⟨491993, by rfl⟩ : syracuseStep 655991 = 983987) B983987
theorem B656015 : Blo 435777 656015 := bstep (se 1 (by rfl) ⟨492011, by rfl⟩ : syracuseStep 656015 = 984023) B984023
theorem B983699 : Blo 435777 983699 := bstep (se 1 (by rfl) ⟨737774, by rfl⟩ : syracuseStep 983699 = 1475549) B1475549
theorem B656057 : Blo 435777 656057 := bstep (se 2 (by rfl) ⟨246021, by rfl⟩ : syracuseStep 656057 = 492043) B492043
theorem B983753 : Blo 435777 983753 := bstep (se 2 (by rfl) ⟨368907, by rfl⟩ : syracuseStep 983753 = 737815) B737815
theorem B103383793 : Blo 435777 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B656135 : Blo 435777 656135 := bstep (se 1 (by rfl) ⟨492101, by rfl⟩ : syracuseStep 656135 = 984203) B984203
theorem B492295 : Blo 435777 492295 := bstep (se 1 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 492295 = 738443) B738443
theorem B656171 : Blo 435777 656171 := bstep (se 1 (by rfl) ⟨492128, by rfl⟩ : syracuseStep 656171 = 984257) B984257
theorem B2097971 : Blo 435777 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1475387 : Blo 435777 1475387 := bstep (se 1 (by rfl) ⟨1106540, by rfl⟩ : syracuseStep 1475387 = 2213081) B2213081
theorem B656201 : Blo 435777 656201 := bstep (se 2 (by rfl) ⟨246075, by rfl⟩ : syracuseStep 656201 = 492151) B492151
theorem B1246067 : Blo 435777 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B656315 : Blo 435777 656315 := bstep (se 1 (by rfl) ⟨492236, by rfl⟩ : syracuseStep 656315 = 984473) B984473
theorem B492475 : Blo 435777 492475 := bstep (se 1 (by rfl) ⟨369356, by rfl⟩ : syracuseStep 492475 = 738713) B738713
theorem B2491357 : Blo 435777 2491357 := bstep (se 3 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 2491357 = 934259) B934259
theorem B656375 : Blo 435777 656375 := bstep (se 1 (by rfl) ⟨492281, by rfl⟩ : syracuseStep 656375 = 984563) B984563
theorem B656399 : Blo 435777 656399 := bstep (se 1 (by rfl) ⟨492299, by rfl⟩ : syracuseStep 656399 = 984599) B984599
theorem B656441 : Blo 435777 656441 := bstep (se 2 (by rfl) ⟨246165, by rfl⟩ : syracuseStep 656441 = 492331) B492331
theorem B1049735 : Blo 435777 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B656519 : Blo 435777 656519 := bstep (se 1 (by rfl) ⟨492389, by rfl⟩ : syracuseStep 656519 = 984779) B984779
theorem B656555 : Blo 435777 656555 := bstep (se 1 (by rfl) ⟨492416, by rfl⟩ : syracuseStep 656555 = 984833) B984833
theorem B656585 : Blo 435777 656585 := bstep (se 2 (by rfl) ⟨246219, by rfl⟩ : syracuseStep 656585 = 492439) B492439
theorem B1180943 : Blo 435777 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B1475873 : Blo 435777 1475873 := bstep (se 2 (by rfl) ⟨553452, by rfl⟩ : syracuseStep 1475873 = 1106905) B1106905
theorem B656699 : Blo 435777 656699 := bstep (se 1 (by rfl) ⟨492524, by rfl⟩ : syracuseStep 656699 = 985049) B985049
theorem B4621627 : Blo 435777 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B656759 : Blo 435777 656759 := bstep (se 1 (by rfl) ⟨492569, by rfl⟩ : syracuseStep 656759 = 985139) B985139
theorem B984455 : Blo 435777 984455 := bstep (se 1 (by rfl) ⟨738341, by rfl⟩ : syracuseStep 984455 = 1476683) B1476683
theorem B656783 : Blo 435777 656783 := bstep (se 1 (by rfl) ⟨492587, by rfl⟩ : syracuseStep 656783 = 985175) B985175
theorem B492943 : Blo 435777 492943 := bstep (se 1 (by rfl) ⟨369707, by rfl⟩ : syracuseStep 492943 = 739415) B739415
theorem B656825 : Blo 435777 656825 := bstep (se 2 (by rfl) ⟨246309, by rfl⟩ : syracuseStep 656825 = 492619) B492619
theorem B656903 : Blo 435777 656903 := bstep (se 1 (by rfl) ⟨492677, by rfl⟩ : syracuseStep 656903 = 985355) B985355
theorem B656939 : Blo 435777 656939 := bstep (se 1 (by rfl) ⟨492704, by rfl⟩ : syracuseStep 656939 = 985409) B985409
theorem B984635 : Blo 435777 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B36537925 : Blo 435777 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B656969 : Blo 435777 656969 := bstep (se 2 (by rfl) ⟨246363, by rfl⟩ : syracuseStep 656969 = 492727) B492727
theorem B1181299 : Blo 435777 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B984761 : Blo 435777 984761 := bstep (se 2 (by rfl) ⟨369285, by rfl⟩ : syracuseStep 984761 = 738571) B738571
theorem B657083 : Blo 435777 657083 := bstep (se 1 (by rfl) ⟨492812, by rfl⟩ : syracuseStep 657083 = 985625) B985625
theorem B657143 : Blo 435777 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B3835649 : Blo 435777 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B788239 : Blo 435777 788239 := bstep (se 1 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 788239 = 1182359) B1182359
theorem B657167 : Blo 435777 657167 := bstep (se 1 (by rfl) ⟨492875, by rfl⟩ : syracuseStep 657167 = 985751) B985751
theorem B657209 : Blo 435777 657209 := bstep (se 2 (by rfl) ⟨246453, by rfl⟩ : syracuseStep 657209 = 492907) B492907
theorem B1247035 : Blo 435777 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B624457 : Blo 435777 624457 := bstep (se 2 (by rfl) ⟨234171, by rfl⟩ : syracuseStep 624457 = 468343) B468343
theorem B1476467 : Blo 435777 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B657287 : Blo 435777 657287 := bstep (se 1 (by rfl) ⟨492965, by rfl⟩ : syracuseStep 657287 = 985931) B985931
theorem B493447 : Blo 435777 493447 := bstep (se 1 (by rfl) ⟨370085, by rfl⟩ : syracuseStep 493447 = 740171) B740171
theorem B657323 : Blo 435777 657323 := bstep (se 1 (by rfl) ⟨492992, by rfl⟩ : syracuseStep 657323 = 985985) B985985
theorem B657353 : Blo 435777 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B985103 : Blo 435777 985103 := bstep (se 1 (by rfl) ⟨738827, by rfl⟩ : syracuseStep 985103 = 1477655) B1477655
theorem B985121 : Blo 435777 985121 := bstep (se 2 (by rfl) ⟨369420, by rfl⟩ : syracuseStep 985121 = 738841) B738841
theorem B657467 : Blo 435777 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B493627 : Blo 435777 493627 := bstep (se 1 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 493627 = 740441) B740441
theorem B657527 : Blo 435777 657527 := bstep (se 1 (by rfl) ⟨493145, by rfl⟩ : syracuseStep 657527 = 986291) B986291
theorem B657551 : Blo 435777 657551 := bstep (se 1 (by rfl) ⟨493163, by rfl⟩ : syracuseStep 657551 = 986327) B986327
theorem B657593 : Blo 435777 657593 := bstep (se 2 (by rfl) ⟨246597, by rfl⟩ : syracuseStep 657593 = 493195) B493195
theorem B1771721 : Blo 435777 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B657671 : Blo 435777 657671 := bstep (se 1 (by rfl) ⟨493253, by rfl⟩ : syracuseStep 657671 = 986507) B986507
theorem B657707 : Blo 435777 657707 := bstep (se 1 (by rfl) ⟨493280, by rfl⟩ : syracuseStep 657707 = 986561) B986561
theorem B657737 : Blo 435777 657737 := bstep (se 2 (by rfl) ⟨246651, by rfl⟩ : syracuseStep 657737 = 493303) B493303
theorem B985463 : Blo 435777 985463 := bstep (se 1 (by rfl) ⟨739097, by rfl⟩ : syracuseStep 985463 = 1478195) B1478195
theorem B657851 : Blo 435777 657851 := bstep (se 1 (by rfl) ⟨493388, by rfl⟩ : syracuseStep 657851 = 986777) B986777
theorem B657911 : Blo 435777 657911 := bstep (se 1 (by rfl) ⟨493433, by rfl⟩ : syracuseStep 657911 = 986867) B986867
theorem B657935 : Blo 435777 657935 := bstep (se 1 (by rfl) ⟨493451, by rfl⟩ : syracuseStep 657935 = 986903) B986903
theorem B494095 : Blo 435777 494095 := bstep (se 1 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 494095 = 741143) B741143
theorem B985643 : Blo 435777 985643 := bstep (se 1 (by rfl) ⟨739232, by rfl⟩ : syracuseStep 985643 = 1478465) B1478465
theorem B657977 : Blo 435777 657977 := bstep (se 2 (by rfl) ⟨246741, by rfl⟩ : syracuseStep 657977 = 493483) B493483
theorem B2001469 : Blo 435777 2001469 := bstep (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) B750551
theorem B658055 : Blo 435777 658055 := bstep (se 1 (by rfl) ⟨493541, by rfl⟩ : syracuseStep 658055 = 987083) B987083
theorem B658091 : Blo 435777 658091 := bstep (se 1 (by rfl) ⟨493568, by rfl⟩ : syracuseStep 658091 = 987137) B987137
theorem B658121 : Blo 435777 658121 := bstep (se 2 (by rfl) ⟨246795, by rfl⟩ : syracuseStep 658121 = 493591) B493591
theorem B658235 : Blo 435777 658235 := bstep (se 1 (by rfl) ⟨493676, by rfl⟩ : syracuseStep 658235 = 987353) B987353
theorem B658295 : Blo 435777 658295 := bstep (se 1 (by rfl) ⟨493721, by rfl⟩ : syracuseStep 658295 = 987443) B987443
theorem B658319 : Blo 435777 658319 := bstep (se 1 (by rfl) ⟨493739, by rfl⟩ : syracuseStep 658319 = 987479) B987479
theorem B986003 : Blo 435777 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B658361 : Blo 435777 658361 := bstep (se 2 (by rfl) ⟨246885, by rfl⟩ : syracuseStep 658361 = 493771) B493771
theorem B1248185 : Blo 435777 1248185 := bstep (se 2 (by rfl) ⟨468069, by rfl⟩ : syracuseStep 1248185 = 936139) B936139
theorem B986057 : Blo 435777 986057 := bstep (se 2 (by rfl) ⟨369771, by rfl⟩ : syracuseStep 986057 = 739543) B739543
theorem B658439 : Blo 435777 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B494599 : Blo 435777 494599 := bstep (se 1 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 494599 = 741899) B741899
theorem B1870877 : Blo 435777 1870877 := bstep (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) B701579
theorem B658475 : Blo 435777 658475 := bstep (se 1 (by rfl) ⟨493856, by rfl⟩ : syracuseStep 658475 = 987713) B987713
theorem B658505 : Blo 435777 658505 := bstep (se 2 (by rfl) ⟨246939, by rfl⟩ : syracuseStep 658505 = 493879) B493879
theorem B3148973 : Blo 435777 3148973 := bstep (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) B1180865
theorem B658619 : Blo 435777 658619 := bstep (se 1 (by rfl) ⟨493964, by rfl⟩ : syracuseStep 658619 = 987929) B987929
theorem B658679 : Blo 435777 658679 := bstep (se 1 (by rfl) ⟨494009, by rfl⟩ : syracuseStep 658679 = 988019) B988019
theorem B1248527 : Blo 435777 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B658703 : Blo 435777 658703 := bstep (se 1 (by rfl) ⟨494027, by rfl⟩ : syracuseStep 658703 = 988055) B988055
theorem B658745 : Blo 435777 658745 := bstep (se 2 (by rfl) ⟨247029, by rfl⟩ : syracuseStep 658745 = 494059) B494059
theorem B593287 : Blo 435777 593287 := bstep (se 1 (by rfl) ⟨444965, by rfl⟩ : syracuseStep 593287 = 889931) B889931
theorem B658823 : Blo 435777 658823 := bstep (se 1 (by rfl) ⟨494117, by rfl⟩ : syracuseStep 658823 = 988235) B988235
theorem B658859 : Blo 435777 658859 := bstep (se 1 (by rfl) ⟨494144, by rfl⟩ : syracuseStep 658859 = 988289) B988289
theorem B495035 : Blo 435777 495035 := bstep (se 1 (by rfl) ⟨371276, by rfl⟩ : syracuseStep 495035 = 742553) B742553
theorem B658889 : Blo 435777 658889 := bstep (se 2 (by rfl) ⟨247083, by rfl⟩ : syracuseStep 658889 = 494167) B494167
theorem B659003 : Blo 435777 659003 := bstep (se 1 (by rfl) ⟨494252, by rfl⟩ : syracuseStep 659003 = 988505) B988505
theorem B659063 : Blo 435777 659063 := bstep (se 1 (by rfl) ⟨494297, by rfl⟩ : syracuseStep 659063 = 988595) B988595
theorem B986759 : Blo 435777 986759 := bstep (se 1 (by rfl) ⟨740069, by rfl⟩ : syracuseStep 986759 = 1480139) B1480139
theorem B13471373 : Blo 435777 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B659087 : Blo 435777 659087 := bstep (se 1 (by rfl) ⟨494315, by rfl⟩ : syracuseStep 659087 = 988631) B988631
theorem B17927831 : Blo 435777 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B659129 : Blo 435777 659129 := bstep (se 2 (by rfl) ⟨247173, by rfl⟩ : syracuseStep 659129 = 494347) B494347
theorem B659207 : Blo 435777 659207 := bstep (se 1 (by rfl) ⟨494405, by rfl⟩ : syracuseStep 659207 = 988811) B988811
theorem B659243 : Blo 435777 659243 := bstep (se 1 (by rfl) ⟨494432, by rfl⟩ : syracuseStep 659243 = 988865) B988865
theorem B986939 : Blo 435777 986939 := bstep (se 1 (by rfl) ⟨740204, by rfl⟩ : syracuseStep 986939 = 1480409) B1480409
theorem B659273 : Blo 435777 659273 := bstep (se 2 (by rfl) ⟨247227, by rfl⟩ : syracuseStep 659273 = 494455) B494455
theorem B987065 : Blo 435777 987065 := bstep (se 2 (by rfl) ⟨370149, by rfl⟩ : syracuseStep 987065 = 740299) B740299
theorem B659387 : Blo 435777 659387 := bstep (se 1 (by rfl) ⟨494540, by rfl⟩ : syracuseStep 659387 = 989081) B989081
theorem B659447 : Blo 435777 659447 := bstep (se 1 (by rfl) ⟨494585, by rfl⟩ : syracuseStep 659447 = 989171) B989171
theorem B659471 : Blo 435777 659471 := bstep (se 1 (by rfl) ⟨494603, by rfl⟩ : syracuseStep 659471 = 989207) B989207
theorem B659513 : Blo 435777 659513 := bstep (se 2 (by rfl) ⟨247317, by rfl⟩ : syracuseStep 659513 = 494635) B494635
theorem B2101315 : Blo 435777 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B1249415 : Blo 435777 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B659591 : Blo 435777 659591 := bstep (se 1 (by rfl) ⟨494693, by rfl⟩ : syracuseStep 659591 = 989387) B989387
theorem B659627 : Blo 435777 659627 := bstep (se 1 (by rfl) ⟨494720, by rfl⟩ : syracuseStep 659627 = 989441) B989441
theorem B659657 : Blo 435777 659657 := bstep (se 2 (by rfl) ⟨247371, by rfl⟩ : syracuseStep 659657 = 494743) B494743
theorem B987407 : Blo 435777 987407 := bstep (se 1 (by rfl) ⟨740555, by rfl⟩ : syracuseStep 987407 = 1481111) B1481111
theorem B987425 : Blo 435777 987425 := bstep (se 2 (by rfl) ⟨370284, by rfl⟩ : syracuseStep 987425 = 740569) B740569
theorem B1249597 : Blo 435777 1249597 := bstep (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) B468599
theorem B1479059 : Blo 435777 1479059 := bstep (se 1 (by rfl) ⟨1109294, by rfl⟩ : syracuseStep 1479059 = 2218589) B2218589
theorem B2167249 : Blo 435777 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B1249825 : Blo 435777 1249825 := bstep (se 2 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 1249825 = 937369) B937369
theorem B987767 : Blo 435777 987767 := bstep (se 1 (by rfl) ⟨740825, by rfl⟩ : syracuseStep 987767 = 1481651) B1481651
theorem B987947 : Blo 435777 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B1250167 : Blo 435777 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B11539381 : Blo 435777 11539381 := bstep (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) B1081817
theorem B2495549 : Blo 435777 2495549 := bstep (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) B935831
theorem B988307 : Blo 435777 988307 := bstep (se 1 (by rfl) ⟨741230, by rfl⟩ : syracuseStep 988307 = 1482461) B1482461
theorem B988361 : Blo 435777 988361 := bstep (se 2 (by rfl) ⟨370635, by rfl⟩ : syracuseStep 988361 = 741271) B741271
theorem B2364653 : Blo 435777 2364653 := bstep (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) B886745
theorem B5608835 : Blo 435777 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B4724153 : Blo 435777 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B3741137 : Blo 435777 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B1873475 : Blo 435777 1873475 := bstep (se 1 (by rfl) ⟨1405106, by rfl⟩ : syracuseStep 1873475 = 2810213) B2810213
theorem B5346935 : Blo 435777 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B2496257 : Blo 435777 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B1480463 : Blo 435777 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1251101 : Blo 435777 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B989063 : Blo 435777 989063 := bstep (se 1 (by rfl) ⟨741797, by rfl⟩ : syracuseStep 989063 = 1483595) B1483595
theorem B1873849 : Blo 435777 1873849 := bstep (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) B1405387
theorem B1480733 : Blo 435777 1480733 := bstep (se 3 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 1480733 = 555275) B555275
theorem B989243 : Blo 435777 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B1251443 : Blo 435777 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B15177901 : Blo 435777 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B989369 : Blo 435777 989369 := bstep (se 2 (by rfl) ⟨371013, by rfl⟩ : syracuseStep 989369 = 742027) B742027
theorem B1874191 : Blo 435777 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B1251899 : Blo 435777 1251899 := bstep (se 1 (by rfl) ⟨938924, by rfl⟩ : syracuseStep 1251899 = 1877849) B1877849
theorem B4725539 : Blo 435777 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B40410019 : Blo 435777 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B2989345 : Blo 435777 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B1482137 : Blo 435777 1482137 := bstep (se 2 (by rfl) ⟨555801, by rfl⟩ : syracuseStep 1482137 = 1111603) B1111603
theorem B1678877 : Blo 435777 1678877 := bstep (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) B629579
theorem B466831 : Blo 435777 466831 := bstep (se 1 (by rfl) ⟨350123, by rfl⟩ : syracuseStep 466831 = 700247) B700247
theorem B597931 : Blo 435777 597931 := bstep (se 1 (by rfl) ⟨448448, by rfl⟩ : syracuseStep 597931 = 896897) B896897
theorem B1187785 : Blo 435777 1187785 := bstep (se 2 (by rfl) ⟨445419, by rfl⟩ : syracuseStep 1187785 = 890839) B890839
theorem B2105297 : Blo 435777 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B2498647 : Blo 435777 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B1482839 : Blo 435777 1482839 := bstep (se 1 (by rfl) ⟨1112129, by rfl⟩ : syracuseStep 1482839 = 2224259) B2224259
theorem B1187959 : Blo 435777 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B827795 : Blo 435777 827795 := bstep (se 1 (by rfl) ⟨620846, by rfl⟩ : syracuseStep 827795 = 1241693) B1241693
theorem B1122707 : Blo 435777 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B827833 : Blo 435777 827833 := bstep (se 2 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 827833 = 620875) B620875
theorem B1483325 : Blo 435777 1483325 := bstep (se 3 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 1483325 = 556247) B556247
theorem B1188413 : Blo 435777 1188413 := bstep (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) B445655
theorem B1876567 : Blo 435777 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B467591 : Blo 435777 467591 := bstep (se 1 (by rfl) ⟨350693, by rfl⟩ : syracuseStep 467591 = 701387) B701387
theorem B2433851 : Blo 435777 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B1123159 : Blo 435777 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B1188695 : Blo 435777 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B533519 : Blo 435777 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B5612935 : Blo 435777 5612935 := bstep (se 1 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 5612935 = 8419403) B8419403
theorem B435847 : Blo 435777 435847 := bstep (se 1 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 435847 = 653771) B653771
theorem B435855 : Blo 435777 435855 := bstep (se 1 (by rfl) ⟨326891, by rfl⟩ : syracuseStep 435855 = 653783) B653783
theorem B435899 : Blo 435777 435899 := bstep (se 1 (by rfl) ⟨326924, by rfl⟩ : syracuseStep 435899 = 653849) B653849
theorem B4499201 : Blo 435777 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B435975 : Blo 435777 435975 := bstep (se 1 (by rfl) ⟨326981, by rfl⟩ : syracuseStep 435975 = 653963) B653963
theorem B435983 : Blo 435777 435983 := bstep (se 1 (by rfl) ⟨326987, by rfl⟩ : syracuseStep 435983 = 653975) B653975
theorem B436027 : Blo 435777 436027 := bstep (se 1 (by rfl) ⟨327020, by rfl⟩ : syracuseStep 436027 = 654041) B654041
theorem B927607 : Blo 435777 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B436103 : Blo 435777 436103 := bstep (se 1 (by rfl) ⟨327077, by rfl⟩ : syracuseStep 436103 = 654155) B654155
theorem B436111 : Blo 435777 436111 := bstep (se 1 (by rfl) ⟨327083, by rfl⟩ : syracuseStep 436111 = 654167) B654167
theorem B4728739 : Blo 435777 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B436155 : Blo 435777 436155 := bstep (se 1 (by rfl) ⟨327116, by rfl⟩ : syracuseStep 436155 = 654233) B654233
theorem B436231 : Blo 435777 436231 := bstep (se 1 (by rfl) ⟨327173, by rfl⟩ : syracuseStep 436231 = 654347) B654347
theorem B436239 : Blo 435777 436239 := bstep (se 1 (by rfl) ⟨327179, by rfl⟩ : syracuseStep 436239 = 654359) B654359
theorem B10102801 : Blo 435777 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B2500631 : Blo 435777 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B436283 : Blo 435777 436283 := bstep (se 1 (by rfl) ⟨327212, by rfl⟩ : syracuseStep 436283 = 654425) B654425
theorem B436359 : Blo 435777 436359 := bstep (se 1 (by rfl) ⟨327269, by rfl⟩ : syracuseStep 436359 = 654539) B654539
theorem B436367 : Blo 435777 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B436411 : Blo 435777 436411 := bstep (se 1 (by rfl) ⟨327308, by rfl⟩ : syracuseStep 436411 = 654617) B654617
theorem B4204781 : Blo 435777 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B436487 : Blo 435777 436487 := bstep (se 1 (by rfl) ⟨327365, by rfl⟩ : syracuseStep 436487 = 654731) B654731
theorem B436495 : Blo 435777 436495 := bstep (se 1 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 436495 = 654743) B654743
theorem B829739 : Blo 435777 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B2369843 : Blo 435777 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B436539 : Blo 435777 436539 := bstep (se 1 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 436539 = 654809) B654809
theorem B436615 : Blo 435777 436615 := bstep (se 1 (by rfl) ⟨327461, by rfl⟩ : syracuseStep 436615 = 654923) B654923
theorem B436623 : Blo 435777 436623 := bstep (se 1 (by rfl) ⟨327467, by rfl⟩ : syracuseStep 436623 = 654935) B654935
theorem B3746195 : Blo 435777 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B436667 : Blo 435777 436667 := bstep (se 1 (by rfl) ⟨327500, by rfl⟩ : syracuseStep 436667 = 655001) B655001
theorem B436743 : Blo 435777 436743 := bstep (se 1 (by rfl) ⟨327557, by rfl⟩ : syracuseStep 436743 = 655115) B655115
theorem B436751 : Blo 435777 436751 := bstep (se 1 (by rfl) ⟨327563, by rfl⟩ : syracuseStep 436751 = 655127) B655127
theorem B436795 : Blo 435777 436795 := bstep (se 1 (by rfl) ⟨327596, by rfl⟩ : syracuseStep 436795 = 655193) B655193
theorem B436871 : Blo 435777 436871 := bstep (se 1 (by rfl) ⟨327653, by rfl⟩ : syracuseStep 436871 = 655307) B655307
theorem B436879 : Blo 435777 436879 := bstep (se 1 (by rfl) ⟨327659, by rfl⟩ : syracuseStep 436879 = 655319) B655319
theorem B436923 : Blo 435777 436923 := bstep (se 1 (by rfl) ⟨327692, by rfl⟩ : syracuseStep 436923 = 655385) B655385
theorem B436999 : Blo 435777 436999 := bstep (se 1 (by rfl) ⟨327749, by rfl⟩ : syracuseStep 436999 = 655499) B655499
theorem B437007 : Blo 435777 437007 := bstep (se 1 (by rfl) ⟨327755, by rfl⟩ : syracuseStep 437007 = 655511) B655511
theorem B437051 : Blo 435777 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B437127 : Blo 435777 437127 := bstep (se 1 (by rfl) ⟨327845, by rfl⟩ : syracuseStep 437127 = 655691) B655691
theorem B437135 : Blo 435777 437135 := bstep (se 1 (by rfl) ⟨327851, by rfl⟩ : syracuseStep 437135 = 655703) B655703
theorem B437179 : Blo 435777 437179 := bstep (se 1 (by rfl) ⟨327884, by rfl⟩ : syracuseStep 437179 = 655769) B655769
theorem B437255 : Blo 435777 437255 := bstep (se 1 (by rfl) ⟨327941, by rfl⟩ : syracuseStep 437255 = 655883) B655883
theorem B437263 : Blo 435777 437263 := bstep (se 1 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 437263 = 655895) B655895
theorem B2206763 : Blo 435777 2206763 := bstep (se 1 (by rfl) ⟨1655072, by rfl⟩ : syracuseStep 2206763 = 3310145) B3310145
theorem B437307 : Blo 435777 437307 := bstep (se 1 (by rfl) ⟨327980, by rfl⟩ : syracuseStep 437307 = 655961) B655961
theorem B2796605 : Blo 435777 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B437383 : Blo 435777 437383 := bstep (se 1 (by rfl) ⟨328037, by rfl⟩ : syracuseStep 437383 = 656075) B656075
theorem B437391 : Blo 435777 437391 := bstep (se 1 (by rfl) ⟨328043, by rfl⟩ : syracuseStep 437391 = 656087) B656087
theorem B437435 : Blo 435777 437435 := bstep (se 1 (by rfl) ⟨328076, by rfl⟩ : syracuseStep 437435 = 656153) B656153
theorem B830665 : Blo 435777 830665 := bstep (se 2 (by rfl) ⟨311499, by rfl⟩ : syracuseStep 830665 = 622999) B622999
theorem B2665709 : Blo 435777 2665709 := bstep (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) B999641
theorem B437511 : Blo 435777 437511 := bstep (se 1 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 437511 = 656267) B656267
theorem B437519 : Blo 435777 437519 := bstep (se 1 (by rfl) ⟨328139, by rfl⟩ : syracuseStep 437519 = 656279) B656279
theorem B437563 : Blo 435777 437563 := bstep (se 1 (by rfl) ⟨328172, by rfl⟩ : syracuseStep 437563 = 656345) B656345
theorem B437639 : Blo 435777 437639 := bstep (se 1 (by rfl) ⟨328229, by rfl⟩ : syracuseStep 437639 = 656459) B656459
theorem B437647 : Blo 435777 437647 := bstep (se 1 (by rfl) ⟨328235, by rfl⟩ : syracuseStep 437647 = 656471) B656471
theorem B437691 : Blo 435777 437691 := bstep (se 1 (by rfl) ⟨328268, by rfl⟩ : syracuseStep 437691 = 656537) B656537
theorem B17346001 : Blo 435777 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B437767 : Blo 435777 437767 := bstep (se 1 (by rfl) ⟨328325, by rfl⟩ : syracuseStep 437767 = 656651) B656651
theorem B437775 : Blo 435777 437775 := bstep (se 1 (by rfl) ⟨328331, by rfl⟩ : syracuseStep 437775 = 656663) B656663
theorem B437819 : Blo 435777 437819 := bstep (se 1 (by rfl) ⟨328364, by rfl⟩ : syracuseStep 437819 = 656729) B656729
theorem B437895 : Blo 435777 437895 := bstep (se 1 (by rfl) ⟨328421, by rfl⟩ : syracuseStep 437895 = 656843) B656843
theorem B437903 : Blo 435777 437903 := bstep (se 1 (by rfl) ⟨328427, by rfl⟩ : syracuseStep 437903 = 656855) B656855
theorem B437947 : Blo 435777 437947 := bstep (se 1 (by rfl) ⟨328460, by rfl⟩ : syracuseStep 437947 = 656921) B656921
theorem B798409 : Blo 435777 798409 := bstep (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) B598807
theorem B1421057 : Blo 435777 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B438023 : Blo 435777 438023 := bstep (se 1 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 438023 = 657035) B657035
theorem B438031 : Blo 435777 438031 := bstep (se 1 (by rfl) ⟨328523, by rfl⟩ : syracuseStep 438031 = 657047) B657047
theorem B438075 : Blo 435777 438075 := bstep (se 1 (by rfl) ⟨328556, by rfl⟩ : syracuseStep 438075 = 657113) B657113
theorem B601975 : Blo 435777 601975 := bstep (se 1 (by rfl) ⟨451481, by rfl⟩ : syracuseStep 601975 = 902963) B902963
theorem B438151 : Blo 435777 438151 := bstep (se 1 (by rfl) ⟨328613, by rfl⟩ : syracuseStep 438151 = 657227) B657227
theorem B438159 : Blo 435777 438159 := bstep (se 1 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 438159 = 657239) B657239
theorem B831379 : Blo 435777 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B438203 : Blo 435777 438203 := bstep (se 1 (by rfl) ⟨328652, by rfl⟩ : syracuseStep 438203 = 657305) B657305
theorem B438279 : Blo 435777 438279 := bstep (se 1 (by rfl) ⟨328709, by rfl⟩ : syracuseStep 438279 = 657419) B657419
theorem B438287 : Blo 435777 438287 := bstep (se 1 (by rfl) ⟨328715, by rfl⟩ : syracuseStep 438287 = 657431) B657431
theorem B438331 : Blo 435777 438331 := bstep (se 1 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 438331 = 657497) B657497
theorem B700535 : Blo 435777 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B438407 : Blo 435777 438407 := bstep (se 1 (by rfl) ⟨328805, by rfl⟩ : syracuseStep 438407 = 657611) B657611
theorem B438415 : Blo 435777 438415 := bstep (se 1 (by rfl) ⟨328811, by rfl⟩ : syracuseStep 438415 = 657623) B657623
theorem B438459 : Blo 435777 438459 := bstep (se 1 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 438459 = 657689) B657689
theorem B438535 : Blo 435777 438535 := bstep (se 1 (by rfl) ⟨328901, by rfl⟩ : syracuseStep 438535 = 657803) B657803
theorem B438543 : Blo 435777 438543 := bstep (se 1 (by rfl) ⟨328907, by rfl⟩ : syracuseStep 438543 = 657815) B657815
theorem B995627 : Blo 435777 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B2208059 : Blo 435777 2208059 := bstep (se 1 (by rfl) ⟨1656044, by rfl⟩ : syracuseStep 2208059 = 3312089) B3312089
theorem B438587 : Blo 435777 438587 := bstep (se 1 (by rfl) ⟨328940, by rfl⟩ : syracuseStep 438587 = 657881) B657881
theorem B438663 : Blo 435777 438663 := bstep (se 1 (by rfl) ⟨328997, by rfl⟩ : syracuseStep 438663 = 657995) B657995
theorem B438671 : Blo 435777 438671 := bstep (se 1 (by rfl) ⟨329003, by rfl⟩ : syracuseStep 438671 = 658007) B658007
theorem B438715 : Blo 435777 438715 := bstep (se 1 (by rfl) ⟨329036, by rfl⟩ : syracuseStep 438715 = 658073) B658073
theorem B2208221 : Blo 435777 2208221 := bstep (se 3 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 2208221 = 828083) B828083
theorem B438791 : Blo 435777 438791 := bstep (se 1 (by rfl) ⟨329093, by rfl⟩ : syracuseStep 438791 = 658187) B658187
theorem B438799 : Blo 435777 438799 := bstep (se 1 (by rfl) ⟨329099, by rfl⟩ : syracuseStep 438799 = 658199) B658199
theorem B438843 : Blo 435777 438843 := bstep (se 1 (by rfl) ⟨329132, by rfl⟩ : syracuseStep 438843 = 658265) B658265
theorem B438919 : Blo 435777 438919 := bstep (se 1 (by rfl) ⟨329189, by rfl⟩ : syracuseStep 438919 = 658379) B658379
theorem B438927 : Blo 435777 438927 := bstep (se 1 (by rfl) ⟨329195, by rfl⟩ : syracuseStep 438927 = 658391) B658391
theorem B438971 : Blo 435777 438971 := bstep (se 1 (by rfl) ⟨329228, by rfl⟩ : syracuseStep 438971 = 658457) B658457
theorem B8991425 : Blo 435777 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B439047 : Blo 435777 439047 := bstep (se 1 (by rfl) ⟨329285, by rfl⟩ : syracuseStep 439047 = 658571) B658571
theorem B439055 : Blo 435777 439055 := bstep (se 1 (by rfl) ⟨329291, by rfl⟩ : syracuseStep 439055 = 658583) B658583
theorem B2208545 : Blo 435777 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B439099 : Blo 435777 439099 := bstep (se 1 (by rfl) ⟨329324, by rfl⟩ : syracuseStep 439099 = 658649) B658649
theorem B439175 : Blo 435777 439175 := bstep (se 1 (by rfl) ⟨329381, by rfl⟩ : syracuseStep 439175 = 658763) B658763
theorem B439183 : Blo 435777 439183 := bstep (se 1 (by rfl) ⟨329387, by rfl⟩ : syracuseStep 439183 = 658775) B658775
theorem B439227 : Blo 435777 439227 := bstep (se 1 (by rfl) ⟨329420, by rfl⟩ : syracuseStep 439227 = 658841) B658841
theorem B832457 : Blo 435777 832457 := bstep (se 2 (by rfl) ⟨312171, by rfl⟩ : syracuseStep 832457 = 624343) B624343
theorem B2372611 : Blo 435777 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B439303 : Blo 435777 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B439311 : Blo 435777 439311 := bstep (se 1 (by rfl) ⟨329483, by rfl⟩ : syracuseStep 439311 = 658967) B658967
theorem B439355 : Blo 435777 439355 := bstep (se 1 (by rfl) ⟨329516, by rfl⟩ : syracuseStep 439355 = 659033) B659033
theorem B439431 : Blo 435777 439431 := bstep (se 1 (by rfl) ⟨329573, by rfl⟩ : syracuseStep 439431 = 659147) B659147
theorem B439439 : Blo 435777 439439 := bstep (se 1 (by rfl) ⟨329579, by rfl⟩ : syracuseStep 439439 = 659159) B659159
theorem B439483 : Blo 435777 439483 := bstep (se 1 (by rfl) ⟨329612, by rfl⟩ : syracuseStep 439483 = 659225) B659225
theorem B439559 : Blo 435777 439559 := bstep (se 1 (by rfl) ⟨329669, by rfl⟩ : syracuseStep 439559 = 659339) B659339
theorem B439567 : Blo 435777 439567 := bstep (se 1 (by rfl) ⟨329675, by rfl⟩ : syracuseStep 439567 = 659351) B659351
theorem B996641 : Blo 435777 996641 := bstep (se 2 (by rfl) ⟨373740, by rfl⟩ : syracuseStep 996641 = 747481) B747481
theorem B439611 : Blo 435777 439611 := bstep (se 1 (by rfl) ⟨329708, by rfl⟩ : syracuseStep 439611 = 659417) B659417
theorem B439687 : Blo 435777 439687 := bstep (se 1 (by rfl) ⟨329765, by rfl⟩ : syracuseStep 439687 = 659531) B659531
theorem B439695 : Blo 435777 439695 := bstep (se 1 (by rfl) ⟨329771, by rfl⟩ : syracuseStep 439695 = 659543) B659543
theorem B439739 : Blo 435777 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B931475 : Blo 435777 931475 := bstep (se 1 (by rfl) ⟨698606, by rfl⟩ : syracuseStep 931475 = 1397213) B1397213
theorem B2209517 : Blo 435777 2209517 := bstep (se 3 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 2209517 = 828569) B828569
theorem B833323 : Blo 435777 833323 := bstep (se 1 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 833323 = 1249985) B1249985
theorem B14137163 : Blo 435777 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B833399 : Blo 435777 833399 := bstep (se 1 (by rfl) ⟨625049, by rfl⟩ : syracuseStep 833399 = 1250099) B1250099
theorem B735547 : Blo 435777 735547 := bstep (se 1 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 735547 = 1103321) B1103321
theorem B735689 : Blo 435777 735689 := bstep (se 2 (by rfl) ⟨275883, by rfl⟩ : syracuseStep 735689 = 551767) B551767
theorem B2210327 : Blo 435777 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B2112119 : Blo 435777 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B2800727 : Blo 435777 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B736391 : Blo 435777 736391 := bstep (se 1 (by rfl) ⟨552293, by rfl⟩ : syracuseStep 736391 = 1104587) B1104587
theorem B3587777 : Blo 435777 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B3325697 : Blo 435777 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B737039 : Blo 435777 737039 := bstep (se 1 (by rfl) ⟨552779, by rfl⟩ : syracuseStep 737039 = 1105559) B1105559
theorem B638777 : Blo 435777 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B638921 : Blo 435777 638921 := bstep (se 2 (by rfl) ⟨239595, by rfl⟩ : syracuseStep 638921 = 479191) B479191
theorem B10665931 : Blo 435777 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B2211851 : Blo 435777 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B737579 : Blo 435777 737579 := bstep (se 1 (by rfl) ⟨553184, by rfl⟩ : syracuseStep 737579 = 1106369) B1106369
theorem B1655225 : Blo 435777 1655225 := bstep (se 2 (by rfl) ⟨620709, by rfl⟩ : syracuseStep 1655225 = 1241419) B1241419
theorem B934345 : Blo 435777 934345 := bstep (se 2 (by rfl) ⟨350379, by rfl⟩ : syracuseStep 934345 = 700759) B700759
theorem B737977 : Blo 435777 737977 := bstep (se 2 (by rfl) ⟨276741, by rfl⟩ : syracuseStep 737977 = 553483) B553483
theorem B79086293 : Blo 435777 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B4735745 : Blo 435777 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B934841 : Blo 435777 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B738679 : Blo 435777 738679 := bstep (se 1 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 738679 = 1108019) B1108019
theorem B2213405 : Blo 435777 2213405 := bstep (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) B830027
theorem B738875 : Blo 435777 738875 := bstep (se 1 (by rfl) ⟨554156, by rfl⟩ : syracuseStep 738875 = 1108313) B1108313
theorem B2246545 : Blo 435777 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B739273 : Blo 435777 739273 := bstep (se 2 (by rfl) ⟨277227, by rfl⟩ : syracuseStep 739273 = 554455) B554455
theorem B2213891 : Blo 435777 2213891 := bstep (se 1 (by rfl) ⟨1660418, by rfl⟩ : syracuseStep 2213891 = 3320837) B3320837
theorem B1198379 : Blo 435777 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B936481 : Blo 435777 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B739975 : Blo 435777 739975 := bstep (se 1 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 739975 = 1109963) B1109963
theorem B2673593 : Blo 435777 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B1657867 : Blo 435777 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B937079 : Blo 435777 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B740623 : Blo 435777 740623 := bstep (se 1 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 740623 = 1110935) B1110935
theorem B1658171 : Blo 435777 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B5131613 : Blo 435777 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B2805137 : Blo 435777 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B2215511 : Blo 435777 2215511 := bstep (se 1 (by rfl) ⟨1661633, by rfl⟩ : syracuseStep 2215511 = 3323267) B3323267
theorem B1265287 : Blo 435777 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B1658657 : Blo 435777 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B741163 : Blo 435777 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B741305 : Blo 435777 741305 := bstep (se 2 (by rfl) ⟨277989, by rfl⟩ : syracuseStep 741305 = 555979) B555979
theorem B3330071 : Blo 435777 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B2215997 : Blo 435777 2215997 := bstep (se 3 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 2215997 = 830999) B830999
theorem B2806163 : Blo 435777 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B742007 : Blo 435777 742007 := bstep (se 1 (by rfl) ⟨556505, by rfl⟩ : syracuseStep 742007 = 1113011) B1113011
theorem B1659629 : Blo 435777 1659629 := bstep (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) B622361
theorem B3167255 : Blo 435777 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2217779 : Blo 435777 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B1070995 : Blo 435777 1070995 := bstep (se 1 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 1070995 = 1606493) B1606493
theorem B3790795 : Blo 435777 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B2218103 : Blo 435777 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B5626057 : Blo 435777 5626057 := bstep (se 2 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 5626057 = 4219543) B4219543
theorem B1104263 : Blo 435777 1104263 := bstep (se 1 (by rfl) ⟨828197, by rfl⟩ : syracuseStep 1104263 = 1656395) B1656395
theorem B1104313 : Blo 435777 1104313 := bstep (se 2 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 1104313 = 828235) B828235
theorem B1661755 : Blo 435777 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B1104911 : Blo 435777 1104911 := bstep (se 1 (by rfl) ⟨828683, by rfl⟩ : syracuseStep 1104911 = 1657367) B1657367
theorem B4512829 : Blo 435777 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B2219075 : Blo 435777 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B1662241 : Blo 435777 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B2219399 : Blo 435777 2219399 := bstep (se 1 (by rfl) ⟨1664549, by rfl⟩ : syracuseStep 2219399 = 3329099) B3329099
theorem B1105609 : Blo 435777 1105609 := bstep (se 2 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 1105609 = 829207) B829207
theorem B1105751 : Blo 435777 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B1400723 : Blo 435777 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B1663213 : Blo 435777 1663213 := bstep (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) B623705
theorem B3825953 : Blo 435777 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B1663517 : Blo 435777 1663517 := bstep (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) B623819
theorem B1335869 : Blo 435777 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B5595713 : Blo 435777 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B9429797 : Blo 435777 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B1336151 : Blo 435777 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B4482053 : Blo 435777 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B3728699 : Blo 435777 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B2483885 : Blo 435777 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B1107827 : Blo 435777 1107827 := bstep (se 1 (by rfl) ⟨830870, by rfl⟩ : syracuseStep 1107827 = 1661741) B1661741
theorem B1665143 : Blo 435777 1665143 := bstep (se 1 (by rfl) ⟨1248857, by rfl⟩ : syracuseStep 1665143 = 2497715) B2497715
theorem B7989521 : Blo 435777 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B1108343 : Blo 435777 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B4745603 : Blo 435777 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B846281 : Blo 435777 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B4221389 : Blo 435777 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B2485025 : Blo 435777 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B2222963 : Blo 435777 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B1666115 : Blo 435777 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B1109335 : Blo 435777 1109335 := bstep (se 1 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 1109335 = 1664003) B1664003
theorem B2223449 : Blo 435777 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B3337847 : Blo 435777 3337847 := bstep (se 1 (by rfl) ⟨2503385, by rfl⟩ : syracuseStep 3337847 = 5006771) B5006771
theorem B1109639 : Blo 435777 1109639 := bstep (se 1 (by rfl) ⟨832229, by rfl⟩ : syracuseStep 1109639 = 1664459) B1664459
theorem B1109771 : Blo 435777 1109771 := bstep (se 1 (by rfl) ⟨832328, by rfl⟩ : syracuseStep 1109771 = 1664657) B1664657
theorem B945935 : Blo 435777 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B2813849 : Blo 435777 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1667101 : Blo 435777 1667101 := bstep (se 3 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 1667101 = 625163) B625163
theorem B5304365 : Blo 435777 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1241203 : Blo 435777 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B1110287 : Blo 435777 1110287 := bstep (se 1 (by rfl) ⟨832715, by rfl⟩ : syracuseStep 1110287 = 1665431) B1665431
theorem B2027891 : Blo 435777 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B1503623 : Blo 435777 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1110419 : Blo 435777 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B553387 : Blo 435777 553387 := bstep (se 1 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 553387 = 830081) B830081
theorem B1470905 : Blo 435777 1470905 := bstep (se 2 (by rfl) ⟨551589, by rfl⟩ : syracuseStep 1470905 = 1103179) B1103179
theorem B3338819 : Blo 435777 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B1405849 : Blo 435777 1405849 := bstep (se 2 (by rfl) ⟨527193, by rfl⟩ : syracuseStep 1405849 = 1054387) B1054387
theorem B4977611 : Blo 435777 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B1471499 : Blo 435777 1471499 := bstep (se 1 (by rfl) ⟨1103624, by rfl⟩ : syracuseStep 1471499 = 2207249) B2207249
theorem B1471607 : Blo 435777 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B2094281 : Blo 435777 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B554359 : Blo 435777 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B2225555 : Blo 435777 2225555 := bstep (se 1 (by rfl) ⟨1669166, by rfl⟩ : syracuseStep 2225555 = 3338333) B3338333
theorem B1111553 : Blo 435777 1111553 := bstep (se 2 (by rfl) ⟨416832, by rfl⟩ : syracuseStep 1111553 = 833665) B833665
theorem B980513 : Blo 435777 980513 := bstep (se 2 (by rfl) ⟨367692, by rfl⟩ : syracuseStep 980513 = 735385) B735385
theorem B1242809 : Blo 435777 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B554683 : Blo 435777 554683 := bstep (se 1 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 554683 = 832025) B832025
theorem B1472201 : Blo 435777 1472201 := bstep (se 2 (by rfl) ⟨552075, by rfl⟩ : syracuseStep 1472201 = 1104151) B1104151
theorem B980855 : Blo 435777 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B1111927 : Blo 435777 1111927 := bstep (se 1 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 1111927 = 1667891) B1667891
theorem B3733451 : Blo 435777 3733451 := bstep (se 1 (by rfl) ⟨2800088, by rfl⟩ : syracuseStep 3733451 = 5600177) B5600177
theorem B1243151 : Blo 435777 1243151 := bstep (se 1 (by rfl) ⟨932363, by rfl⟩ : syracuseStep 1243151 = 1864727) B1864727
theorem B981035 : Blo 435777 981035 := bstep (se 1 (by rfl) ⟨735776, by rfl⟩ : syracuseStep 981035 = 1471553) B1471553
theorem B1407233 : Blo 435777 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B1112363 : Blo 435777 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B653687 : Blo 435777 653687 := bstep (se 1 (by rfl) ⟨490265, by rfl⟩ : syracuseStep 653687 = 980531) B980531
theorem B1472903 : Blo 435777 1472903 := bstep (se 1 (by rfl) ⟨1104677, by rfl⟩ : syracuseStep 1472903 = 2209355) B2209355
theorem B653711 : Blo 435777 653711 := bstep (se 1 (by rfl) ⟨490283, by rfl⟩ : syracuseStep 653711 = 980567) B980567
theorem B1178003 : Blo 435777 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B981395 : Blo 435777 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B653753 : Blo 435777 653753 := bstep (se 2 (by rfl) ⟨245157, by rfl⟩ : syracuseStep 653753 = 490315) B490315
theorem B1571257 : Blo 435777 1571257 := bstep (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) B1178443
theorem B981449 : Blo 435777 981449 := bstep (se 2 (by rfl) ⟨368043, by rfl⟩ : syracuseStep 981449 = 736087) B736087
theorem B653831 : Blo 435777 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B653867 : Blo 435777 653867 := bstep (se 1 (by rfl) ⟨490400, by rfl⟩ : syracuseStep 653867 = 980801) B980801
theorem B653897 : Blo 435777 653897 := bstep (se 2 (by rfl) ⟨245211, by rfl⟩ : syracuseStep 653897 = 490423) B490423
theorem B555655 : Blo 435777 555655 := bstep (se 1 (by rfl) ⟨416741, by rfl⟩ : syracuseStep 555655 = 833483) B833483
theorem B621199 : Blo 435777 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B654011 : Blo 435777 654011 := bstep (se 1 (by rfl) ⟨490508, by rfl⟩ : syracuseStep 654011 = 981017) B981017
theorem B654071 : Blo 435777 654071 := bstep (se 1 (by rfl) ⟨490553, by rfl⟩ : syracuseStep 654071 = 981107) B981107
theorem B1473281 : Blo 435777 1473281 := bstep (se 2 (by rfl) ⟨552480, by rfl⟩ : syracuseStep 1473281 = 1104961) B1104961
theorem B654095 : Blo 435777 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B1178401 : Blo 435777 1178401 := bstep (se 2 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 1178401 = 883801) B883801
theorem B1243937 : Blo 435777 1243937 := bstep (se 2 (by rfl) ⟨466476, by rfl⟩ : syracuseStep 1243937 = 932953) B932953
theorem B654137 : Blo 435777 654137 := bstep (se 2 (by rfl) ⟨245301, by rfl⟩ : syracuseStep 654137 = 490603) B490603
theorem B1571719 : Blo 435777 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B654215 : Blo 435777 654215 := bstep (se 1 (by rfl) ⟨490661, by rfl⟩ : syracuseStep 654215 = 981323) B981323
theorem B654251 : Blo 435777 654251 := bstep (se 1 (by rfl) ⟨490688, by rfl⟩ : syracuseStep 654251 = 981377) B981377
theorem B654281 : Blo 435777 654281 := bstep (se 2 (by rfl) ⟨245355, by rfl⟩ : syracuseStep 654281 = 490711) B490711
theorem B556075 : Blo 435777 556075 := bstep (se 1 (by rfl) ⟨417056, by rfl⟩ : syracuseStep 556075 = 834113) B834113
theorem B654395 : Blo 435777 654395 := bstep (se 1 (by rfl) ⟨490796, by rfl⟩ : syracuseStep 654395 = 981593) B981593
theorem B654455 : Blo 435777 654455 := bstep (se 1 (by rfl) ⟨490841, by rfl⟩ : syracuseStep 654455 = 981683) B981683
theorem B785543 : Blo 435777 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B982151 : Blo 435777 982151 := bstep (se 1 (by rfl) ⟨736613, by rfl⟩ : syracuseStep 982151 = 1473227) B1473227
theorem B490639 : Blo 435777 490639 := bstep (se 1 (by rfl) ⟨367979, by rfl⟩ : syracuseStep 490639 = 735959) B735959
theorem B654479 : Blo 435777 654479 := bstep (se 1 (by rfl) ⟨490859, by rfl⟩ : syracuseStep 654479 = 981719) B981719
theorem B654521 : Blo 435777 654521 := bstep (se 2 (by rfl) ⟨245445, by rfl⟩ : syracuseStep 654521 = 490891) B490891
theorem B621769 : Blo 435777 621769 := bstep (se 2 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 621769 = 466327) B466327
theorem B654599 : Blo 435777 654599 := bstep (se 1 (by rfl) ⟨490949, by rfl⟩ : syracuseStep 654599 = 981899) B981899
theorem B556303 : Blo 435777 556303 := bstep (se 1 (by rfl) ⟨417227, by rfl⟩ : syracuseStep 556303 = 834455) B834455
theorem B654635 : Blo 435777 654635 := bstep (se 1 (by rfl) ⟨490976, by rfl⟩ : syracuseStep 654635 = 981953) B981953
theorem B982331 : Blo 435777 982331 := bstep (se 1 (by rfl) ⟨736748, by rfl⟩ : syracuseStep 982331 = 1473497) B1473497
theorem B2653499 : Blo 435777 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B654665 : Blo 435777 654665 := bstep (se 2 (by rfl) ⟨245499, by rfl⟩ : syracuseStep 654665 = 490999) B490999
theorem B982457 : Blo 435777 982457 := bstep (se 2 (by rfl) ⟨368421, by rfl⟩ : syracuseStep 982457 = 736843) B736843
theorem B654779 : Blo 435777 654779 := bstep (se 1 (by rfl) ⟨491084, by rfl⟩ : syracuseStep 654779 = 982169) B982169
theorem B3145169 : Blo 435777 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B654839 : Blo 435777 654839 := bstep (se 1 (by rfl) ⟨491129, by rfl⟩ : syracuseStep 654839 = 982259) B982259
theorem B654863 : Blo 435777 654863 := bstep (se 1 (by rfl) ⟨491147, by rfl⟩ : syracuseStep 654863 = 982295) B982295
theorem B1474091 : Blo 435777 1474091 := bstep (se 1 (by rfl) ⟨1105568, by rfl⟩ : syracuseStep 1474091 = 2211137) B2211137
theorem B2489899 : Blo 435777 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B654905 : Blo 435777 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B3145283 : Blo 435777 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B5144141 : Blo 435777 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B491143 : Blo 435777 491143 := bstep (se 1 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 491143 = 736715) B736715
theorem B654983 : Blo 435777 654983 := bstep (se 1 (by rfl) ⟨491237, by rfl⟩ : syracuseStep 654983 = 982475) B982475
theorem B655019 : Blo 435777 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B655049 : Blo 435777 655049 := bstep (se 2 (by rfl) ⟨245643, by rfl⟩ : syracuseStep 655049 = 491287) B491287
theorem B3538703 : Blo 435777 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B982799 : Blo 435777 982799 := bstep (se 1 (by rfl) ⟨737099, by rfl⟩ : syracuseStep 982799 = 1474199) B1474199
theorem B982817 : Blo 435777 982817 := bstep (se 2 (by rfl) ⟨368556, by rfl⟩ : syracuseStep 982817 = 737113) B737113
theorem B26935091 : Blo 435777 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B884539 : Blo 435777 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B491323 : Blo 435777 491323 := bstep (se 1 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 491323 = 736985) B736985
theorem B655163 : Blo 435777 655163 := bstep (se 1 (by rfl) ⟨491372, by rfl⟩ : syracuseStep 655163 = 982745) B982745
theorem B655223 : Blo 435777 655223 := bstep (se 1 (by rfl) ⟨491417, by rfl⟩ : syracuseStep 655223 = 982835) B982835
theorem B655247 : Blo 435777 655247 := bstep (se 1 (by rfl) ⟨491435, by rfl⟩ : syracuseStep 655247 = 982871) B982871
theorem B2097049 : Blo 435777 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B655289 : Blo 435777 655289 := bstep (se 2 (by rfl) ⟨245733, by rfl⟩ : syracuseStep 655289 = 491467) B491467
theorem B5898269 : Blo 435777 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2490425 : Blo 435777 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B655439 : Blo 435777 655439 := bstep (se 1 (by rfl) ⟨491579, by rfl⟩ : syracuseStep 655439 = 983159) B983159
theorem B655559 : Blo 435777 655559 := bstep (se 1 (by rfl) ⟨491669, by rfl⟩ : syracuseStep 655559 = 983339) B983339
theorem B491719 : Blo 435777 491719 := bstep (se 1 (by rfl) ⟨368789, by rfl⟩ : syracuseStep 491719 = 737579) B737579
theorem B1868093 : Blo 435777 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B655721 : Blo 435777 655721 := bstep (se 2 (by rfl) ⟨245895, by rfl⟩ : syracuseStep 655721 = 491791) B491791
theorem B655799 : Blo 435777 655799 := bstep (se 1 (by rfl) ⟨491849, by rfl⟩ : syracuseStep 655799 = 983699) B983699
theorem B655835 : Blo 435777 655835 := bstep (se 1 (by rfl) ⟨491876, by rfl⟩ : syracuseStep 655835 = 983753) B983753
theorem B52724195 : Blo 435777 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B4063769 : Blo 435777 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B983591 : Blo 435777 983591 := bstep (se 1 (by rfl) ⟨737693, by rfl⟩ : syracuseStep 983591 = 1475387) B1475387
theorem B1245793 : Blo 435777 1245793 := bstep (se 2 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 1245793 = 934345) B934345
theorem B623227 : Blo 435777 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B787295 : Blo 435777 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B983915 : Blo 435777 983915 := bstep (se 1 (by rfl) ⟨737936, by rfl⟩ : syracuseStep 983915 = 1475873) B1475873
theorem B983969 : Blo 435777 983969 := bstep (se 2 (by rfl) ⟨368988, by rfl⟩ : syracuseStep 983969 = 737977) B737977
theorem B656303 : Blo 435777 656303 := bstep (se 1 (by rfl) ⟨492227, by rfl⟩ : syracuseStep 656303 = 984455) B984455
theorem B656393 : Blo 435777 656393 := bstep (se 2 (by rfl) ⟨246147, by rfl⟩ : syracuseStep 656393 = 492295) B492295
theorem B1475603 : Blo 435777 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B656423 : Blo 435777 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B492583 : Blo 435777 492583 := bstep (se 1 (by rfl) ⟨369437, by rfl⟩ : syracuseStep 492583 = 738875) B738875
theorem B656507 : Blo 435777 656507 := bstep (se 1 (by rfl) ⟨492380, by rfl⟩ : syracuseStep 656507 = 984761) B984761
theorem B2557099 : Blo 435777 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B984311 : Blo 435777 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B656633 : Blo 435777 656633 := bstep (se 2 (by rfl) ⟨246237, by rfl⟩ : syracuseStep 656633 = 492475) B492475
theorem B1475927 : Blo 435777 1475927 := bstep (se 1 (by rfl) ⟨1106945, by rfl⟩ : syracuseStep 1475927 = 2213891) B2213891
theorem B656735 : Blo 435777 656735 := bstep (se 1 (by rfl) ⟨492551, by rfl⟩ : syracuseStep 656735 = 985103) B985103
theorem B656747 : Blo 435777 656747 := bstep (se 1 (by rfl) ⟨492560, by rfl⟩ : syracuseStep 656747 = 985121) B985121
theorem B1181147 : Blo 435777 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B656975 : Blo 435777 656975 := bstep (se 1 (by rfl) ⟨492731, by rfl⟩ : syracuseStep 656975 = 985463) B985463
theorem B1246909 : Blo 435777 1246909 := bstep (se 3 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 1246909 = 467591) B467591
theorem B657095 : Blo 435777 657095 := bstep (se 1 (by rfl) ⟨492821, by rfl⟩ : syracuseStep 657095 = 985643) B985643
theorem B6162169 : Blo 435777 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B984905 : Blo 435777 984905 := bstep (se 2 (by rfl) ⟨369339, by rfl⟩ : syracuseStep 984905 = 738679) B738679
theorem B657257 : Blo 435777 657257 := bstep (se 2 (by rfl) ⟨246471, by rfl⟩ : syracuseStep 657257 = 492943) B492943
theorem B657335 : Blo 435777 657335 := bstep (se 1 (by rfl) ⟨493001, by rfl⟩ : syracuseStep 657335 = 986003) B986003
theorem B657371 : Blo 435777 657371 := bstep (se 1 (by rfl) ⟨493028, by rfl⟩ : syracuseStep 657371 = 986057) B986057
theorem B1247251 : Blo 435777 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B624719 : Blo 435777 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B2099315 : Blo 435777 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B1575065 : Blo 435777 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B1870091 : Blo 435777 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1050985 : Blo 435777 1050985 := bstep (se 2 (by rfl) ⟨394119, by rfl⟩ : syracuseStep 1050985 = 788239) B788239
theorem B1477007 : Blo 435777 1477007 := bstep (se 1 (by rfl) ⟨1107755, by rfl⟩ : syracuseStep 1477007 = 2215511) B2215511
theorem B657839 : Blo 435777 657839 := bstep (se 1 (by rfl) ⟨493379, by rfl⟩ : syracuseStep 657839 = 986759) B986759
theorem B657929 : Blo 435777 657929 := bstep (se 2 (by rfl) ⟨246723, by rfl⟩ : syracuseStep 657929 = 493447) B493447
theorem B657959 : Blo 435777 657959 := bstep (se 1 (by rfl) ⟨493469, by rfl⟩ : syracuseStep 657959 = 986939) B986939
theorem B985697 : Blo 435777 985697 := bstep (se 2 (by rfl) ⟨369636, by rfl⟩ : syracuseStep 985697 = 739273) B739273
theorem B658043 : Blo 435777 658043 := bstep (se 1 (by rfl) ⟨493532, by rfl⟩ : syracuseStep 658043 = 987065) B987065
theorem B494203 : Blo 435777 494203 := bstep (se 1 (by rfl) ⟨370652, by rfl⟩ : syracuseStep 494203 = 741305) B741305
theorem B13470401 : Blo 435777 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B1477331 : Blo 435777 1477331 := bstep (se 1 (by rfl) ⟨1107998, by rfl⟩ : syracuseStep 1477331 = 2215997) B2215997
theorem B658169 : Blo 435777 658169 := bstep (se 2 (by rfl) ⟨246813, by rfl⟩ : syracuseStep 658169 = 493627) B493627
theorem B658271 : Blo 435777 658271 := bstep (se 1 (by rfl) ⟨493703, by rfl⟩ : syracuseStep 658271 = 987407) B987407
theorem B658283 : Blo 435777 658283 := bstep (se 1 (by rfl) ⟨493712, by rfl⟩ : syracuseStep 658283 = 987425) B987425
theorem B1870775 : Blo 435777 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B986039 : Blo 435777 986039 := bstep (se 1 (by rfl) ⟨739529, by rfl⟩ : syracuseStep 986039 = 1479059) B1479059
theorem B658511 : Blo 435777 658511 := bstep (se 1 (by rfl) ⟨493883, by rfl⟩ : syracuseStep 658511 = 987767) B987767
theorem B494671 : Blo 435777 494671 := bstep (se 1 (by rfl) ⟨371003, by rfl⟩ : syracuseStep 494671 = 742007) B742007
theorem B658631 : Blo 435777 658631 := bstep (se 1 (by rfl) ⟨493973, by rfl⟩ : syracuseStep 658631 = 987947) B987947
theorem B658793 : Blo 435777 658793 := bstep (se 2 (by rfl) ⟨247047, by rfl⟩ : syracuseStep 658793 = 494095) B494095
theorem B1248641 : Blo 435777 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B3313061 : Blo 435777 3313061 := bstep (se 4 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 3313061 = 621199) B621199
theorem B658871 : Blo 435777 658871 := bstep (se 1 (by rfl) ⟨494153, by rfl⟩ : syracuseStep 658871 = 988307) B988307
theorem B658907 : Blo 435777 658907 := bstep (se 1 (by rfl) ⟨494180, by rfl⟩ : syracuseStep 658907 = 988361) B988361
theorem B1576435 : Blo 435777 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B986633 : Blo 435777 986633 := bstep (se 2 (by rfl) ⟨369987, by rfl⟩ : syracuseStep 986633 = 739975) B739975
theorem B3739223 : Blo 435777 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B3149435 : Blo 435777 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B2494091 : Blo 435777 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1248983 : Blo 435777 1248983 := bstep (se 1 (by rfl) ⟨936737, by rfl⟩ : syracuseStep 1248983 = 1873475) B1873475
theorem B986975 : Blo 435777 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B1478519 : Blo 435777 1478519 := bstep (se 1 (by rfl) ⟨1108889, by rfl⟩ : syracuseStep 1478519 = 2217779) B2217779
theorem B659375 : Blo 435777 659375 := bstep (se 1 (by rfl) ⟨494531, by rfl⟩ : syracuseStep 659375 = 989063) B989063
theorem B659465 : Blo 435777 659465 := bstep (se 2 (by rfl) ⟨247299, by rfl⟩ : syracuseStep 659465 = 494599) B494599
theorem B987155 : Blo 435777 987155 := bstep (se 1 (by rfl) ⟨740366, by rfl⟩ : syracuseStep 987155 = 1480733) B1480733
theorem B659495 : Blo 435777 659495 := bstep (se 1 (by rfl) ⟨494621, by rfl⟩ : syracuseStep 659495 = 989243) B989243
theorem B1478735 : Blo 435777 1478735 := bstep (se 1 (by rfl) ⟨1109051, by rfl⟩ : syracuseStep 1478735 = 2218103) B2218103
theorem B659579 : Blo 435777 659579 := bstep (se 1 (by rfl) ⟨494684, by rfl⟩ : syracuseStep 659579 = 989369) B989369
theorem B987497 : Blo 435777 987497 := bstep (se 2 (by rfl) ⟨370311, by rfl⟩ : syracuseStep 987497 = 740623) B740623
theorem B1479113 : Blo 435777 1479113 := bstep (se 2 (by rfl) ⟨554667, by rfl⟩ : syracuseStep 1479113 = 1109335) B1109335
theorem B3150359 : Blo 435777 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B1479383 : Blo 435777 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B1479599 : Blo 435777 1479599 := bstep (se 1 (by rfl) ⟨1109699, by rfl⟩ : syracuseStep 1479599 = 2219399) B2219399
theorem B988091 : Blo 435777 988091 := bstep (se 1 (by rfl) ⟨741068, by rfl⟩ : syracuseStep 988091 = 1482137) B1482137
theorem B1119251 : Blo 435777 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B988217 : Blo 435777 988217 := bstep (se 2 (by rfl) ⟨370581, by rfl⟩ : syracuseStep 988217 = 741163) B741163
theorem B988559 : Blo 435777 988559 := bstep (se 1 (by rfl) ⟨741419, by rfl⟩ : syracuseStep 988559 = 1482839) B1482839
theorem B890579 : Blo 435777 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B988883 : Blo 435777 988883 := bstep (se 1 (by rfl) ⟨741662, by rfl⟩ : syracuseStep 988883 = 1483325) B1483325
theorem B792275 : Blo 435777 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B890767 : Blo 435777 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B2889665 : Blo 435777 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B2988035 : Blo 435777 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B21305389 : Blo 435777 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B1874465 : Blo 435777 1874465 := bstep (se 2 (by rfl) ⟨702924, by rfl⟩ : syracuseStep 1874465 = 1405849) B1405849
theorem B1579895 : Blo 435777 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B2497463 : Blo 435777 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B564187 : Blo 435777 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B1481975 : Blo 435777 1481975 := bstep (se 1 (by rfl) ⟨1111481, by rfl⟩ : syracuseStep 1481975 = 2222963) B2222963
theorem B1777139 : Blo 435777 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B1482299 : Blo 435777 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B1482569 : Blo 435777 1482569 := bstep (se 2 (by rfl) ⟨555963, by rfl⟩ : syracuseStep 1482569 = 1111927) B1111927
theorem B630623 : Blo 435777 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B2498465 : Blo 435777 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B5054393 : Blo 435777 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1875899 : Blo 435777 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B663751 : Blo 435777 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B1351927 : Blo 435777 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2498921 : Blo 435777 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B3318407 : Blo 435777 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B664427 : Blo 435777 664427 := bstep (se 1 (by rfl) ⟨498320, by rfl⟩ : syracuseStep 664427 = 996641) B996641
theorem B1483703 : Blo 435777 1483703 := bstep (se 1 (by rfl) ⟨1112777, by rfl⟩ : syracuseStep 1483703 = 2225555) B2225555
theorem B828539 : Blo 435777 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B53880025 : Blo 435777 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B828767 : Blo 435777 828767 := bstep (se 1 (by rfl) ⟨621575, by rfl⟩ : syracuseStep 828767 = 1243151) B1243151
theorem B435791 : Blo 435777 435791 := bstep (se 1 (by rfl) ⟨326843, by rfl⟩ : syracuseStep 435791 = 653687) B653687
theorem B435807 : Blo 435777 435807 := bstep (se 1 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 435807 = 653711) B653711
theorem B829025 : Blo 435777 829025 := bstep (se 2 (by rfl) ⟨310884, by rfl⟩ : syracuseStep 829025 = 621769) B621769
theorem B435835 : Blo 435777 435835 := bstep (se 1 (by rfl) ⟨326876, by rfl⟩ : syracuseStep 435835 = 653753) B653753
theorem B435887 : Blo 435777 435887 := bstep (se 1 (by rfl) ⟨326915, by rfl⟩ : syracuseStep 435887 = 653831) B653831
theorem B435911 : Blo 435777 435911 := bstep (se 1 (by rfl) ⟨326933, by rfl⟩ : syracuseStep 435911 = 653867) B653867
theorem B35923661 : Blo 435777 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B435931 : Blo 435777 435931 := bstep (se 1 (by rfl) ⟨326948, by rfl⟩ : syracuseStep 435931 = 653897) B653897
theorem B436007 : Blo 435777 436007 := bstep (se 1 (by rfl) ⟨327005, by rfl⟩ : syracuseStep 436007 = 654011) B654011
theorem B436047 : Blo 435777 436047 := bstep (se 1 (by rfl) ⟨327035, by rfl⟩ : syracuseStep 436047 = 654071) B654071
theorem B436063 : Blo 435777 436063 := bstep (se 1 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 436063 = 654095) B654095
theorem B829291 : Blo 435777 829291 := bstep (se 1 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 829291 = 1243937) B1243937
theorem B436091 : Blo 435777 436091 := bstep (se 1 (by rfl) ⟨327068, by rfl⟩ : syracuseStep 436091 = 654137) B654137
theorem B436143 : Blo 435777 436143 := bstep (se 1 (by rfl) ⟨327107, by rfl⟩ : syracuseStep 436143 = 654215) B654215
theorem B436167 : Blo 435777 436167 := bstep (se 1 (by rfl) ⟨327125, by rfl⟩ : syracuseStep 436167 = 654251) B654251
theorem B436187 : Blo 435777 436187 := bstep (se 1 (by rfl) ⟨327140, by rfl⟩ : syracuseStep 436187 = 654281) B654281
theorem B436263 : Blo 435777 436263 := bstep (se 1 (by rfl) ⟨327197, by rfl⟩ : syracuseStep 436263 = 654395) B654395
theorem B3319865 : Blo 435777 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B436303 : Blo 435777 436303 := bstep (se 1 (by rfl) ⟨327227, by rfl⟩ : syracuseStep 436303 = 654455) B654455
theorem B436319 : Blo 435777 436319 := bstep (se 1 (by rfl) ⟨327239, by rfl⟩ : syracuseStep 436319 = 654479) B654479
theorem B436347 : Blo 435777 436347 := bstep (se 1 (by rfl) ⟨327260, by rfl⟩ : syracuseStep 436347 = 654521) B654521
theorem B436399 : Blo 435777 436399 := bstep (se 1 (by rfl) ⟨327299, by rfl⟩ : syracuseStep 436399 = 654599) B654599
theorem B436423 : Blo 435777 436423 := bstep (se 1 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 436423 = 654635) B654635
theorem B436443 : Blo 435777 436443 := bstep (se 1 (by rfl) ⟨327332, by rfl⟩ : syracuseStep 436443 = 654665) B654665
theorem B3188965 : Blo 435777 3188965 := bstep (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) B597931
theorem B436519 : Blo 435777 436519 := bstep (se 1 (by rfl) ⟨327389, by rfl⟩ : syracuseStep 436519 = 654779) B654779
theorem B436559 : Blo 435777 436559 := bstep (se 1 (by rfl) ⟨327419, by rfl⟩ : syracuseStep 436559 = 654839) B654839
theorem B436575 : Blo 435777 436575 := bstep (se 1 (by rfl) ⟨327431, by rfl⟩ : syracuseStep 436575 = 654863) B654863
theorem B436603 : Blo 435777 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B436655 : Blo 435777 436655 := bstep (se 1 (by rfl) ⟨327491, by rfl⟩ : syracuseStep 436655 = 654983) B654983
theorem B436679 : Blo 435777 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B436699 : Blo 435777 436699 := bstep (se 1 (by rfl) ⟨327524, by rfl⟩ : syracuseStep 436699 = 655049) B655049
theorem B2796065 : Blo 435777 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B436775 : Blo 435777 436775 := bstep (se 1 (by rfl) ⟨327581, by rfl⟩ : syracuseStep 436775 = 655163) B655163
theorem B436815 : Blo 435777 436815 := bstep (se 1 (by rfl) ⟨327611, by rfl⟩ : syracuseStep 436815 = 655223) B655223
theorem B436831 : Blo 435777 436831 := bstep (se 1 (by rfl) ⟨327623, by rfl⟩ : syracuseStep 436831 = 655247) B655247
theorem B1583713 : Blo 435777 1583713 := bstep (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) B1187785
theorem B436859 : Blo 435777 436859 := bstep (se 1 (by rfl) ⟨327644, by rfl⟩ : syracuseStep 436859 = 655289) B655289
theorem B436911 : Blo 435777 436911 := bstep (se 1 (by rfl) ⟨327683, by rfl⟩ : syracuseStep 436911 = 655367) B655367
theorem B436935 : Blo 435777 436935 := bstep (se 1 (by rfl) ⟨327701, by rfl⟩ : syracuseStep 436935 = 655403) B655403
theorem B436955 : Blo 435777 436955 := bstep (se 1 (by rfl) ⟨327716, by rfl⟩ : syracuseStep 436955 = 655433) B655433
theorem B437031 : Blo 435777 437031 := bstep (se 1 (by rfl) ⟨327773, by rfl⟩ : syracuseStep 437031 = 655547) B655547
theorem B1583945 : Blo 435777 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B437071 : Blo 435777 437071 := bstep (se 1 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 437071 = 655607) B655607
theorem B437087 : Blo 435777 437087 := bstep (se 1 (by rfl) ⟨327815, by rfl⟩ : syracuseStep 437087 = 655631) B655631
theorem B437115 : Blo 435777 437115 := bstep (se 1 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 437115 = 655673) B655673
theorem B437167 : Blo 435777 437167 := bstep (se 1 (by rfl) ⟨327875, by rfl⟩ : syracuseStep 437167 = 655751) B655751
theorem B9612215 : Blo 435777 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B437191 : Blo 435777 437191 := bstep (se 1 (by rfl) ⟨327893, by rfl⟩ : syracuseStep 437191 = 655787) B655787
theorem B437211 : Blo 435777 437211 := bstep (se 1 (by rfl) ⟨327908, by rfl⟩ : syracuseStep 437211 = 655817) B655817
theorem B830483 : Blo 435777 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B437287 : Blo 435777 437287 := bstep (se 1 (by rfl) ⟨327965, by rfl⟩ : syracuseStep 437287 = 655931) B655931
theorem B437327 : Blo 435777 437327 := bstep (se 1 (by rfl) ⟨327995, by rfl⟩ : syracuseStep 437327 = 655991) B655991
theorem B437343 : Blo 435777 437343 := bstep (se 1 (by rfl) ⟨328007, by rfl⟩ : syracuseStep 437343 = 656015) B656015
theorem B437371 : Blo 435777 437371 := bstep (se 1 (by rfl) ⟨328028, by rfl⟩ : syracuseStep 437371 = 656057) B656057
theorem B3157163 : Blo 435777 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B437423 : Blo 435777 437423 := bstep (se 1 (by rfl) ⟨328067, by rfl⟩ : syracuseStep 437423 = 656135) B656135
theorem B437447 : Blo 435777 437447 := bstep (se 1 (by rfl) ⟨328085, by rfl⟩ : syracuseStep 437447 = 656171) B656171
theorem B437467 : Blo 435777 437467 := bstep (se 1 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 437467 = 656201) B656201
theorem B830711 : Blo 435777 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B437543 : Blo 435777 437543 := bstep (se 1 (by rfl) ⟨328157, by rfl⟩ : syracuseStep 437543 = 656315) B656315
theorem B437583 : Blo 435777 437583 := bstep (se 1 (by rfl) ⟨328187, by rfl⟩ : syracuseStep 437583 = 656375) B656375
theorem B437599 : Blo 435777 437599 := bstep (se 1 (by rfl) ⟨328199, by rfl⟩ : syracuseStep 437599 = 656399) B656399
theorem B437627 : Blo 435777 437627 := bstep (se 1 (by rfl) ⟨328220, by rfl⟩ : syracuseStep 437627 = 656441) B656441
theorem B699823 : Blo 435777 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B437679 : Blo 435777 437679 := bstep (se 1 (by rfl) ⟨328259, by rfl⟩ : syracuseStep 437679 = 656519) B656519
theorem B437703 : Blo 435777 437703 := bstep (se 1 (by rfl) ⟨328277, by rfl⟩ : syracuseStep 437703 = 656555) B656555
theorem B2502089 : Blo 435777 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B437723 : Blo 435777 437723 := bstep (se 1 (by rfl) ⟨328292, by rfl⟩ : syracuseStep 437723 = 656585) B656585
theorem B437799 : Blo 435777 437799 := bstep (se 1 (by rfl) ⟨328349, by rfl⟩ : syracuseStep 437799 = 656699) B656699
theorem B437839 : Blo 435777 437839 := bstep (se 1 (by rfl) ⟨328379, by rfl⟩ : syracuseStep 437839 = 656759) B656759
theorem B437855 : Blo 435777 437855 := bstep (se 1 (by rfl) ⟨328391, by rfl⟩ : syracuseStep 437855 = 656783) B656783
theorem B437883 : Blo 435777 437883 := bstep (se 1 (by rfl) ⟨328412, by rfl⟩ : syracuseStep 437883 = 656825) B656825
theorem B437935 : Blo 435777 437935 := bstep (se 1 (by rfl) ⟨328451, by rfl⟩ : syracuseStep 437935 = 656903) B656903
theorem B4009661 : Blo 435777 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B437959 : Blo 435777 437959 := bstep (se 1 (by rfl) ⟨328469, by rfl⟩ : syracuseStep 437959 = 656939) B656939
theorem B437979 : Blo 435777 437979 := bstep (se 1 (by rfl) ⟨328484, by rfl⟩ : syracuseStep 437979 = 656969) B656969
theorem B2993885 : Blo 435777 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B438055 : Blo 435777 438055 := bstep (se 1 (by rfl) ⟨328541, by rfl⟩ : syracuseStep 438055 = 657083) B657083
theorem B438095 : Blo 435777 438095 := bstep (se 1 (by rfl) ⟨328571, by rfl⟩ : syracuseStep 438095 = 657143) B657143
theorem B438111 : Blo 435777 438111 := bstep (se 1 (by rfl) ⟨328583, by rfl⟩ : syracuseStep 438111 = 657167) B657167
theorem B438139 : Blo 435777 438139 := bstep (se 1 (by rfl) ⟨328604, by rfl⟩ : syracuseStep 438139 = 657209) B657209
theorem B438191 : Blo 435777 438191 := bstep (se 1 (by rfl) ⟨328643, by rfl⟩ : syracuseStep 438191 = 657287) B657287
theorem B438215 : Blo 435777 438215 := bstep (se 1 (by rfl) ⟨328661, by rfl⟩ : syracuseStep 438215 = 657323) B657323
theorem B3321809 : Blo 435777 3321809 := bstep (se 2 (by rfl) ⟨1245678, by rfl⟩ : syracuseStep 3321809 = 2491357) B2491357
theorem B438235 : Blo 435777 438235 := bstep (se 1 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 438235 = 657353) B657353
theorem B438311 : Blo 435777 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B438351 : Blo 435777 438351 := bstep (se 1 (by rfl) ⟨328763, by rfl⟩ : syracuseStep 438351 = 657527) B657527
theorem B438367 : Blo 435777 438367 := bstep (se 1 (by rfl) ⟨328775, by rfl⟩ : syracuseStep 438367 = 657551) B657551
theorem B438395 : Blo 435777 438395 := bstep (se 1 (by rfl) ⟨328796, by rfl⟩ : syracuseStep 438395 = 657593) B657593
theorem B438447 : Blo 435777 438447 := bstep (se 1 (by rfl) ⟨328835, by rfl⟩ : syracuseStep 438447 = 657671) B657671
theorem B438471 : Blo 435777 438471 := bstep (se 1 (by rfl) ⟨328853, by rfl⟩ : syracuseStep 438471 = 657707) B657707
theorem B438491 : Blo 435777 438491 := bstep (se 1 (by rfl) ⟨328868, by rfl⟩ : syracuseStep 438491 = 657737) B657737
theorem B438567 : Blo 435777 438567 := bstep (se 1 (by rfl) ⟨328925, by rfl⟩ : syracuseStep 438567 = 657851) B657851
theorem B438607 : Blo 435777 438607 := bstep (se 1 (by rfl) ⟨328955, by rfl⟩ : syracuseStep 438607 = 657911) B657911
theorem B438623 : Blo 435777 438623 := bstep (se 1 (by rfl) ⟨328967, by rfl⟩ : syracuseStep 438623 = 657935) B657935
theorem B438651 : Blo 435777 438651 := bstep (se 1 (by rfl) ⟨328988, by rfl⟩ : syracuseStep 438651 = 657977) B657977
theorem B438703 : Blo 435777 438703 := bstep (se 1 (by rfl) ⟨329027, by rfl⟩ : syracuseStep 438703 = 658055) B658055
theorem B438727 : Blo 435777 438727 := bstep (se 1 (by rfl) ⟨329045, by rfl⟩ : syracuseStep 438727 = 658091) B658091
theorem B438747 : Blo 435777 438747 := bstep (se 1 (by rfl) ⟨329060, by rfl⟩ : syracuseStep 438747 = 658121) B658121
theorem B7483913 : Blo 435777 7483913 := bstep (se 2 (by rfl) ⟨2806467, by rfl⟩ : syracuseStep 7483913 = 5612935) B5612935
theorem B438823 : Blo 435777 438823 := bstep (se 1 (by rfl) ⟨329117, by rfl⟩ : syracuseStep 438823 = 658235) B658235
theorem B438863 : Blo 435777 438863 := bstep (se 1 (by rfl) ⟨329147, by rfl⟩ : syracuseStep 438863 = 658295) B658295
theorem B438879 : Blo 435777 438879 := bstep (se 1 (by rfl) ⟨329159, by rfl⟩ : syracuseStep 438879 = 658319) B658319
theorem B832123 : Blo 435777 832123 := bstep (se 1 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 832123 = 1248185) B1248185
theorem B438907 : Blo 435777 438907 := bstep (se 1 (by rfl) ⟨329180, by rfl⟩ : syracuseStep 438907 = 658361) B658361
theorem B1782395 : Blo 435777 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B438959 : Blo 435777 438959 := bstep (se 1 (by rfl) ⟨329219, by rfl⟩ : syracuseStep 438959 = 658439) B658439
theorem B438983 : Blo 435777 438983 := bstep (se 1 (by rfl) ⟨329237, by rfl⟩ : syracuseStep 438983 = 658475) B658475
theorem B439003 : Blo 435777 439003 := bstep (se 1 (by rfl) ⟨329252, by rfl⟩ : syracuseStep 439003 = 658505) B658505
theorem B439079 : Blo 435777 439079 := bstep (se 1 (by rfl) ⟨329309, by rfl⟩ : syracuseStep 439079 = 658619) B658619
theorem B439119 : Blo 435777 439119 := bstep (se 1 (by rfl) ⟨329339, by rfl⟩ : syracuseStep 439119 = 658679) B658679
theorem B832351 : Blo 435777 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B439135 : Blo 435777 439135 := bstep (se 1 (by rfl) ⟨329351, by rfl⟩ : syracuseStep 439135 = 658703) B658703
theorem B439163 : Blo 435777 439163 := bstep (se 1 (by rfl) ⟨329372, by rfl⟩ : syracuseStep 439163 = 658745) B658745
theorem B439215 : Blo 435777 439215 := bstep (se 1 (by rfl) ⟨329411, by rfl⟩ : syracuseStep 439215 = 658823) B658823
theorem B439239 : Blo 435777 439239 := bstep (se 1 (by rfl) ⟨329429, by rfl⟩ : syracuseStep 439239 = 658859) B658859
theorem B439259 : Blo 435777 439259 := bstep (se 1 (by rfl) ⟨329444, by rfl⟩ : syracuseStep 439259 = 658889) B658889
theorem B439335 : Blo 435777 439335 := bstep (se 1 (by rfl) ⟨329501, by rfl⟩ : syracuseStep 439335 = 659003) B659003
theorem B439375 : Blo 435777 439375 := bstep (se 1 (by rfl) ⟨329531, by rfl⟩ : syracuseStep 439375 = 659063) B659063
theorem B439391 : Blo 435777 439391 := bstep (se 1 (by rfl) ⟨329543, by rfl⟩ : syracuseStep 439391 = 659087) B659087
theorem B832609 : Blo 435777 832609 := bstep (se 2 (by rfl) ⟨312228, by rfl⟩ : syracuseStep 832609 = 624457) B624457
theorem B439419 : Blo 435777 439419 := bstep (se 1 (by rfl) ⟨329564, by rfl⟩ : syracuseStep 439419 = 659129) B659129
theorem B439471 : Blo 435777 439471 := bstep (se 1 (by rfl) ⟨329603, by rfl⟩ : syracuseStep 439471 = 659207) B659207
theorem B2995393 : Blo 435777 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B439495 : Blo 435777 439495 := bstep (se 1 (by rfl) ⟨329621, by rfl⟩ : syracuseStep 439495 = 659243) B659243
theorem B6304985 : Blo 435777 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B439515 : Blo 435777 439515 := bstep (se 1 (by rfl) ⟨329636, by rfl⟩ : syracuseStep 439515 = 659273) B659273
theorem B439591 : Blo 435777 439591 := bstep (se 1 (by rfl) ⟨329693, by rfl⟩ : syracuseStep 439591 = 659387) B659387
theorem B439631 : Blo 435777 439631 := bstep (se 1 (by rfl) ⟨329723, by rfl⟩ : syracuseStep 439631 = 659447) B659447
theorem B439647 : Blo 435777 439647 := bstep (se 1 (by rfl) ⟨329735, by rfl⟩ : syracuseStep 439647 = 659471) B659471
theorem B439675 : Blo 435777 439675 := bstep (se 1 (by rfl) ⟨329756, by rfl⟩ : syracuseStep 439675 = 659513) B659513
theorem B832943 : Blo 435777 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B439727 : Blo 435777 439727 := bstep (se 1 (by rfl) ⟨329795, by rfl⟩ : syracuseStep 439727 = 659591) B659591
theorem B439751 : Blo 435777 439751 := bstep (se 1 (by rfl) ⟨329813, by rfl⟩ : syracuseStep 439751 = 659627) B659627
theorem B439771 : Blo 435777 439771 := bstep (se 1 (by rfl) ⟨329828, by rfl⟩ : syracuseStep 439771 = 659657) B659657
theorem B2111503 : Blo 435777 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B2668625 : Blo 435777 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B834067 : Blo 435777 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B2210489 : Blo 435777 2210489 := bstep (se 2 (by rfl) ⟨828933, by rfl⟩ : syracuseStep 2210489 = 1657867) B1657867
theorem B834295 : Blo 435777 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B736175 : Blo 435777 736175 := bstep (se 1 (by rfl) ⟨552131, by rfl⟩ : syracuseStep 736175 = 1104263) B1104263
theorem B834599 : Blo 435777 834599 := bstep (se 1 (by rfl) ⟨625949, by rfl⟩ : syracuseStep 834599 = 1251899) B1251899
theorem B736607 : Blo 435777 736607 := bstep (se 1 (by rfl) ⟨552455, by rfl⟩ : syracuseStep 736607 = 1104911) B1104911
theorem B1687049 : Blo 435777 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B1064545 : Blo 435777 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B802633 : Blo 435777 802633 := bstep (se 2 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 802633 = 601975) B601975
theorem B737167 : Blo 435777 737167 := bstep (se 1 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 737167 = 1105751) B1105751
theorem B933815 : Blo 435777 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B2801753 : Blo 435777 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B1654937 : Blo 435777 1654937 := bstep (se 2 (by rfl) ⟨620601, by rfl⟩ : syracuseStep 1654937 = 1241203) B1241203
theorem B1622567 : Blo 435777 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B737849 : Blo 435777 737849 := bstep (se 2 (by rfl) ⟨276693, by rfl⟩ : syracuseStep 737849 = 553387) B553387
theorem B3195677 : Blo 435777 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B1655923 : Blo 435777 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B2999467 : Blo 435777 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B15385841 : Blo 435777 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B738551 : Blo 435777 738551 := bstep (se 1 (by rfl) ⟨553913, by rfl⟩ : syracuseStep 738551 = 1107827) B1107827
theorem B3163481 : Blo 435777 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B2803187 : Blo 435777 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B738895 : Blo 435777 738895 := bstep (se 1 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 738895 = 1108343) B1108343
theorem B3163735 : Blo 435777 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B739145 : Blo 435777 739145 := bstep (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) B554359
theorem B1656683 : Blo 435777 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B3164197 : Blo 435777 3164197 := bstep (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) B593287
theorem B739577 : Blo 435777 739577 := bstep (se 2 (by rfl) ⟨277341, by rfl⟩ : syracuseStep 739577 = 554683) B554683
theorem B739759 : Blo 435777 739759 := bstep (se 1 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 739759 = 1109639) B1109639
theorem B21121493 : Blo 435777 21121493 := bstep (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) B495035
theorem B739847 : Blo 435777 739847 := bstep (se 1 (by rfl) ⟨554885, by rfl⟩ : syracuseStep 739847 = 1109771) B1109771
theorem B1427993 : Blo 435777 1427993 := bstep (se 2 (by rfl) ⟨535497, by rfl⟩ : syracuseStep 1427993 = 1070995) B1070995
theorem B740191 : Blo 435777 740191 := bstep (se 1 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 740191 = 1110287) B1110287
theorem B20237201 : Blo 435777 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B740279 : Blo 435777 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B1396187 : Blo 435777 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B740873 : Blo 435777 740873 := bstep (se 2 (by rfl) ⟨277827, by rfl⟩ : syracuseStep 740873 = 555655) B555655
theorem B13684301 : Blo 435777 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B741035 : Blo 435777 741035 := bstep (se 1 (by rfl) ⟨555776, by rfl⟩ : syracuseStep 741035 = 1111553) B1111553
theorem B2215673 : Blo 435777 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B9424775 : Blo 435777 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B741433 : Blo 435777 741433 := bstep (se 2 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 741433 = 556075) B556075
theorem B6017105 : Blo 435777 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B938155 : Blo 435777 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B741575 : Blo 435777 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B741737 : Blo 435777 741737 := bstep (se 2 (by rfl) ⟨278151, by rfl⟩ : syracuseStep 741737 = 556303) B556303
theorem B3985793 : Blo 435777 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B2216321 : Blo 435777 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B3429427 : Blo 435777 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B2217131 : Blo 435777 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B3331529 : Blo 435777 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B1103483 : Blo 435777 1103483 := bstep (se 1 (by rfl) ⟨827612, by rfl⟩ : syracuseStep 1103483 = 1655225) B1655225
theorem B2217617 : Blo 435777 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B1660601 : Blo 435777 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B1398647 : Blo 435777 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1103777 : Blo 435777 1103777 := bstep (se 2 (by rfl) ⟨413916, by rfl⟩ : syracuseStep 1103777 = 827833) B827833
theorem B22763477 : Blo 435777 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B1497545 : Blo 435777 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B48717233 : Blo 435777 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B1105447 : Blo 435777 1105447 := bstep (se 1 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 1105447 = 1658171) B1658171
theorem B3169853 : Blo 435777 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B8380037 : Blo 435777 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B1662713 : Blo 435777 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B11951887 : Blo 435777 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1236809 : Blo 435777 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1105771 : Blo 435777 1105771 := bstep (se 1 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 1105771 = 1658657) B1658657
theorem B2219885 : Blo 435777 2219885 := bstep (se 3 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 2219885 = 832457) B832457
theorem B2220047 : Blo 435777 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B1106419 : Blo 435777 1106419 := bstep (se 1 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 1106419 = 1659629) B1659629
theorem B1663699 : Blo 435777 1663699 := bstep (se 1 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 1663699 = 2495549) B2495549
theorem B3564623 : Blo 435777 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B1664171 : Blo 435777 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B551380229 : Blo 435777 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B1107553 : Blo 435777 1107553 := bstep (se 2 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 1107553 = 830665) B830665
theorem B23128001 : Blo 435777 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B1108505 : Blo 435777 1108505 := bstep (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) B831379
theorem B1403531 : Blo 435777 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B2222801 : Blo 435777 2222801 := bstep (se 2 (by rfl) ⟨833550, by rfl⟩ : syracuseStep 2222801 = 1667101) B1667101
theorem B2550635 : Blo 435777 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B551863 : Blo 435777 551863 := bstep (se 1 (by rfl) ⟨413897, by rfl⟩ : syracuseStep 551863 = 827795) B827795
theorem B1109011 : Blo 435777 1109011 := bstep (se 1 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 1109011 = 1663517) B1663517
theorem B3730475 : Blo 435777 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B1666129 : Blo 435777 1666129 := bstep (se 2 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 1666129 = 1249597) B1249597
theorem B6286531 : Blo 435777 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B1666433 : Blo 435777 1666433 := bstep (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) B1249825
theorem B2485799 : Blo 435777 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B1666889 : Blo 435777 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B1667087 : Blo 435777 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1110095 : Blo 435777 1110095 := bstep (se 1 (by rfl) ⟨832571, by rfl⟩ : syracuseStep 1110095 = 1665143) B1665143
theorem B553159 : Blo 435777 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B2814259 : Blo 435777 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B1471175 : Blo 435777 1471175 := bstep (se 1 (by rfl) ⟨1103381, by rfl⟩ : syracuseStep 1471175 = 2206763) B2206763
theorem B1864403 : Blo 435777 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B1110743 : Blo 435777 1110743 := bstep (se 1 (by rfl) ⟨833057, by rfl⟩ : syracuseStep 1110743 = 1666115) B1666115
theorem B1111097 : Blo 435777 1111097 := bstep (se 2 (by rfl) ⟨416661, by rfl⟩ : syracuseStep 1111097 = 833323) B833323
theorem B2225231 : Blo 435777 2225231 := bstep (se 1 (by rfl) ⟨1668923, by rfl⟩ : syracuseStep 2225231 = 3337847) B3337847
theorem B947371 : Blo 435777 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B3536243 : Blo 435777 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1472039 : Blo 435777 1472039 := bstep (se 1 (by rfl) ⟨1104029, by rfl⟩ : syracuseStep 1472039 = 2208059) B2208059
theorem B7501409 : Blo 435777 7501409 := bstep (se 2 (by rfl) ⟨2813028, by rfl⟩ : syracuseStep 7501409 = 5626057) B5626057
theorem B980603 : Blo 435777 980603 := bstep (se 1 (by rfl) ⟨735452, by rfl⟩ : syracuseStep 980603 = 1470905) B1470905
theorem B1472147 : Blo 435777 1472147 := bstep (se 1 (by rfl) ⟨1104110, by rfl⟩ : syracuseStep 1472147 = 2208221) B2208221
theorem B2094781 : Blo 435777 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B2225879 : Blo 435777 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B980729 : Blo 435777 980729 := bstep (se 2 (by rfl) ⟨367773, by rfl⟩ : syracuseStep 980729 = 735547) B735547
theorem B5994283 : Blo 435777 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1472363 : Blo 435777 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B1472417 : Blo 435777 1472417 := bstep (se 2 (by rfl) ⟨552156, by rfl⟩ : syracuseStep 1472417 = 1104313) B1104313
theorem B980999 : Blo 435777 980999 := bstep (se 1 (by rfl) ⟨735749, by rfl⟩ : syracuseStep 980999 = 1471499) B1471499
theorem B981071 : Blo 435777 981071 := bstep (se 1 (by rfl) ⟨735803, by rfl⟩ : syracuseStep 981071 = 1471607) B1471607
theorem B653675 : Blo 435777 653675 := bstep (se 1 (by rfl) ⟨490256, by rfl⟩ : syracuseStep 653675 = 980513) B980513
theorem B1571201 : Blo 435777 1571201 := bstep (se 2 (by rfl) ⟨589200, by rfl⟩ : syracuseStep 1571201 = 1178401) B1178401
theorem B620983 : Blo 435777 620983 := bstep (se 1 (by rfl) ⟨465737, by rfl⟩ : syracuseStep 620983 = 931475) B931475
theorem B981467 : Blo 435777 981467 := bstep (se 1 (by rfl) ⟨736100, by rfl⟩ : syracuseStep 981467 = 1472201) B1472201
theorem B1473011 : Blo 435777 1473011 := bstep (se 1 (by rfl) ⟨1104758, by rfl⟩ : syracuseStep 1473011 = 2209517) B2209517
theorem B2095625 : Blo 435777 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B653903 : Blo 435777 653903 := bstep (se 1 (by rfl) ⟨490427, by rfl⟩ : syracuseStep 653903 = 980855) B980855
theorem B555599 : Blo 435777 555599 := bstep (se 1 (by rfl) ⟨416699, by rfl⟩ : syracuseStep 555599 = 833399) B833399
theorem B2488967 : Blo 435777 2488967 := bstep (se 1 (by rfl) ⟨1866725, by rfl⟩ : syracuseStep 2488967 = 3733451) B3733451
theorem B654023 : Blo 435777 654023 := bstep (se 1 (by rfl) ⟨490517, by rfl⟩ : syracuseStep 654023 = 981035) B981035
theorem B654185 : Blo 435777 654185 := bstep (se 2 (by rfl) ⟨245319, by rfl⟩ : syracuseStep 654185 = 490639) B490639
theorem B981935 : Blo 435777 981935 := bstep (se 1 (by rfl) ⟨736451, by rfl⟩ : syracuseStep 981935 = 1472903) B1472903
theorem B785335 : Blo 435777 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B654263 : Blo 435777 654263 := bstep (se 1 (by rfl) ⟨490697, by rfl⟩ : syracuseStep 654263 = 981395) B981395
theorem B490459 : Blo 435777 490459 := bstep (se 1 (by rfl) ⟨367844, by rfl⟩ : syracuseStep 490459 = 735689) B735689
theorem B654299 : Blo 435777 654299 := bstep (se 1 (by rfl) ⟨490724, by rfl⟩ : syracuseStep 654299 = 981449) B981449
theorem B4717541 : Blo 435777 4717541 := bstep (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) B884539
theorem B1473551 : Blo 435777 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B1408079 : Blo 435777 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B982187 : Blo 435777 982187 := bstep (se 1 (by rfl) ⟨736640, by rfl⟩ : syracuseStep 982187 = 1473281) B1473281
theorem B1867151 : Blo 435777 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B490927 : Blo 435777 490927 := bstep (se 1 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 490927 = 736391) B736391
theorem B654767 : Blo 435777 654767 := bstep (se 1 (by rfl) ⟨491075, by rfl⟩ : syracuseStep 654767 = 982151) B982151
theorem B1703405 : Blo 435777 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B654857 : Blo 435777 654857 := bstep (se 2 (by rfl) ⟨245571, by rfl⟩ : syracuseStep 654857 = 491143) B491143
theorem B1768999 : Blo 435777 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B654887 : Blo 435777 654887 := bstep (se 1 (by rfl) ⟨491165, by rfl⟩ : syracuseStep 654887 = 982331) B982331
theorem B1474145 : Blo 435777 1474145 := bstep (se 2 (by rfl) ⟨552804, by rfl⟩ : syracuseStep 1474145 = 1105609) B1105609
theorem B654971 : Blo 435777 654971 := bstep (se 1 (by rfl) ⟨491228, by rfl⟩ : syracuseStep 654971 = 982457) B982457
theorem B2096779 : Blo 435777 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B982727 : Blo 435777 982727 := bstep (se 1 (by rfl) ⟨737045, by rfl⟩ : syracuseStep 982727 = 1474091) B1474091
theorem B2096855 : Blo 435777 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B655097 : Blo 435777 655097 := bstep (se 2 (by rfl) ⟨245661, by rfl⟩ : syracuseStep 655097 = 491323) B491323
theorem B2391851 : Blo 435777 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B2359135 : Blo 435777 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B491359 : Blo 435777 491359 := bstep (se 1 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 491359 = 737039) B737039
theorem B655199 : Blo 435777 655199 := bstep (se 1 (by rfl) ⟨491399, by rfl⟩ : syracuseStep 655199 = 982799) B982799
theorem B622441 : Blo 435777 622441 := bstep (se 2 (by rfl) ⟨233415, by rfl⟩ : syracuseStep 622441 = 466831) B466831
theorem B655211 : Blo 435777 655211 := bstep (se 1 (by rfl) ⟨491408, by rfl⟩ : syracuseStep 655211 = 982817) B982817
theorem B1703789 : Blo 435777 1703789 := bstep (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) B638921
theorem B17956727 : Blo 435777 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B14221241 : Blo 435777 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B1867835 : Blo 435777 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B15728717 : Blo 435777 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1245395 : Blo 435777 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B885001 : Blo 435777 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B655625 : Blo 435777 655625 := bstep (se 2 (by rfl) ⟨245859, by rfl⟩ : syracuseStep 655625 = 491719) B491719
theorem B1802569 : Blo 435777 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B655727 : Blo 435777 655727 := bstep (se 1 (by rfl) ⟨491795, by rfl⟩ : syracuseStep 655727 = 983591) B983591
theorem B1081711 : Blo 435777 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B491899 : Blo 435777 491899 := bstep (se 1 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 491899 = 737849) B737849
theorem B524863 : Blo 435777 524863 := bstep (se 1 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 524863 = 787295) B787295
theorem B655943 : Blo 435777 655943 := bstep (se 1 (by rfl) ⟨491957, by rfl⟩ : syracuseStep 655943 = 983915) B983915
theorem B655979 : Blo 435777 655979 := bstep (se 1 (by rfl) ⟨491984, by rfl⟩ : syracuseStep 655979 = 983969) B983969
theorem B1475225 : Blo 435777 1475225 := bstep (se 2 (by rfl) ⟨553209, by rfl⟩ : syracuseStep 1475225 = 1106419) B1106419
theorem B983735 : Blo 435777 983735 := bstep (se 1 (by rfl) ⟨737801, by rfl⟩ : syracuseStep 983735 = 1475603) B1475603
theorem B10257227 : Blo 435777 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B656207 : Blo 435777 656207 := bstep (se 1 (by rfl) ⟨492155, by rfl⟩ : syracuseStep 656207 = 984311) B984311
theorem B492367 : Blo 435777 492367 := bstep (se 1 (by rfl) ⟨369275, by rfl⟩ : syracuseStep 492367 = 738551) B738551
theorem B983951 : Blo 435777 983951 := bstep (se 1 (by rfl) ⟨737963, by rfl⟩ : syracuseStep 983951 = 1475927) B1475927
theorem B656603 : Blo 435777 656603 := bstep (se 1 (by rfl) ⟨492452, by rfl⟩ : syracuseStep 656603 = 984905) B984905
theorem B492763 : Blo 435777 492763 := bstep (se 1 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 492763 = 739145) B739145
theorem B656777 : Blo 435777 656777 := bstep (se 2 (by rfl) ⟨246291, by rfl⟩ : syracuseStep 656777 = 492583) B492583
theorem B1050043 : Blo 435777 1050043 := bstep (se 1 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 1050043 = 1575065) B1575065
theorem B493051 : Blo 435777 493051 := bstep (se 1 (by rfl) ⟨369788, by rfl⟩ : syracuseStep 493051 = 739577) B739577
theorem B1246727 : Blo 435777 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B3409465 : Blo 435777 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B3999289 : Blo 435777 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B984671 : Blo 435777 984671 := bstep (se 1 (by rfl) ⟨738503, by rfl⟩ : syracuseStep 984671 = 1477007) B1477007
theorem B493231 : Blo 435777 493231 := bstep (se 1 (by rfl) ⟨369923, by rfl⟩ : syracuseStep 493231 = 739847) B739847
theorem B951995 : Blo 435777 951995 := bstep (se 1 (by rfl) ⟨713996, by rfl⟩ : syracuseStep 951995 = 1427993) B1427993
theorem B657131 : Blo 435777 657131 := bstep (se 1 (by rfl) ⟨492848, by rfl⟩ : syracuseStep 657131 = 985697) B985697
theorem B8980267 : Blo 435777 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B984887 : Blo 435777 984887 := bstep (se 1 (by rfl) ⟨738665, by rfl⟩ : syracuseStep 984887 = 1477331) B1477331
theorem B1247183 : Blo 435777 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B657359 : Blo 435777 657359 := bstep (se 1 (by rfl) ⟨493019, by rfl⟩ : syracuseStep 657359 = 986039) B986039
theorem B493519 : Blo 435777 493519 := bstep (se 1 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 493519 = 740279) B740279
theorem B8521805 : Blo 435777 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B985193 : Blo 435777 985193 := bstep (se 2 (by rfl) ⟨369447, by rfl⟩ : syracuseStep 985193 = 738895) B738895
theorem B1476737 : Blo 435777 1476737 := bstep (se 2 (by rfl) ⟨553776, by rfl⟩ : syracuseStep 1476737 = 1107553) B1107553
theorem B657755 : Blo 435777 657755 := bstep (se 1 (by rfl) ⟨493316, by rfl⟩ : syracuseStep 657755 = 986633) B986633
theorem B493915 : Blo 435777 493915 := bstep (se 1 (by rfl) ⟨370436, by rfl⟩ : syracuseStep 493915 = 740873) B740873
theorem B2492815 : Blo 435777 2492815 := bstep (se 1 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 2492815 = 3739223) B3739223
theorem B2099623 : Blo 435777 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B494023 : Blo 435777 494023 := bstep (se 1 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 494023 = 741035) B741035
theorem B1477115 : Blo 435777 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B657983 : Blo 435777 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B985679 : Blo 435777 985679 := bstep (se 1 (by rfl) ⟨739259, by rfl⟩ : syracuseStep 985679 = 1478519) B1478519
theorem B658103 : Blo 435777 658103 := bstep (se 1 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 658103 = 987155) B987155
theorem B985823 : Blo 435777 985823 := bstep (se 1 (by rfl) ⟨739367, by rfl⟩ : syracuseStep 985823 = 1478735) B1478735
theorem B494383 : Blo 435777 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B658331 : Blo 435777 658331 := bstep (se 1 (by rfl) ⟨493748, by rfl⟩ : syracuseStep 658331 = 987497) B987497
theorem B494491 : Blo 435777 494491 := bstep (se 1 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 494491 = 741737) B741737
theorem B2657195 : Blo 435777 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B1477547 : Blo 435777 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B986075 : Blo 435777 986075 := bstep (se 1 (by rfl) ⟨739556, by rfl⟩ : syracuseStep 986075 = 1479113) B1479113
theorem B2100239 : Blo 435777 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B986255 : Blo 435777 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B986345 : Blo 435777 986345 := bstep (se 2 (by rfl) ⟨369879, by rfl⟩ : syracuseStep 986345 = 739759) B739759
theorem B986399 : Blo 435777 986399 := bstep (se 1 (by rfl) ⟨739799, by rfl⟩ : syracuseStep 986399 = 1479599) B1479599
theorem B658727 : Blo 435777 658727 := bstep (se 1 (by rfl) ⟨494045, by rfl⟩ : syracuseStep 658727 = 988091) B988091
theorem B658811 : Blo 435777 658811 := bstep (se 1 (by rfl) ⟨494108, by rfl⟩ : syracuseStep 658811 = 988217) B988217
theorem B1478087 : Blo 435777 1478087 := bstep (se 1 (by rfl) ⟨1108565, by rfl⟩ : syracuseStep 1478087 = 2217131) B2217131
theorem B658937 : Blo 435777 658937 := bstep (se 2 (by rfl) ⟨247101, by rfl⟩ : syracuseStep 658937 = 494203) B494203
theorem B659039 : Blo 435777 659039 := bstep (se 1 (by rfl) ⟨494279, by rfl⟩ : syracuseStep 659039 = 988559) B988559
theorem B1478411 : Blo 435777 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B986921 : Blo 435777 986921 := bstep (se 2 (by rfl) ⟨370095, by rfl⟩ : syracuseStep 986921 = 740191) B740191
theorem B659255 : Blo 435777 659255 := bstep (se 1 (by rfl) ⟨494441, by rfl⟩ : syracuseStep 659255 = 988883) B988883
theorem B3149725 : Blo 435777 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B7475165 : Blo 435777 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B1478681 : Blo 435777 1478681 := bstep (se 2 (by rfl) ⟨554505, by rfl⟩ : syracuseStep 1478681 = 1109011) B1109011
theorem B659561 : Blo 435777 659561 := bstep (se 2 (by rfl) ⟨247335, by rfl⟩ : syracuseStep 659561 = 494671) B494671
theorem B1249643 : Blo 435777 1249643 := bstep (se 1 (by rfl) ⟨937232, by rfl⟩ : syracuseStep 1249643 = 1874465) B1874465
theorem B1053263 : Blo 435777 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B2101913 : Blo 435777 2101913 := bstep (se 2 (by rfl) ⟨788217, by rfl⟩ : syracuseStep 2101913 = 1576435) B1576435
theorem B987983 : Blo 435777 987983 := bstep (se 1 (by rfl) ⟨740987, by rfl⟩ : syracuseStep 987983 = 1481975) B1481975
theorem B32478155 : Blo 435777 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B1184759 : Blo 435777 1184759 := bstep (se 1 (by rfl) ⟨888569, by rfl⟩ : syracuseStep 1184759 = 1777139) B1777139
theorem B988199 : Blo 435777 988199 := bstep (se 1 (by rfl) ⟨741149, by rfl⟩ : syracuseStep 988199 = 1482299) B1482299
theorem B988379 : Blo 435777 988379 := bstep (se 1 (by rfl) ⟨741284, by rfl⟩ : syracuseStep 988379 = 1482569) B1482569
theorem B1479923 : Blo 435777 1479923 := bstep (se 1 (by rfl) ⟨1109942, by rfl⟩ : syracuseStep 1479923 = 2219885) B2219885
theorem B1480031 : Blo 435777 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B988577 : Blo 435777 988577 := bstep (se 2 (by rfl) ⟨370716, by rfl⟩ : syracuseStep 988577 = 741433) B741433
theorem B1250873 : Blo 435777 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B989135 : Blo 435777 989135 := bstep (se 1 (by rfl) ⟨741851, by rfl⟩ : syracuseStep 989135 = 1483703) B1483703
theorem B1481597 : Blo 435777 1481597 := bstep (se 3 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 1481597 = 555599) B555599
theorem B1481867 : Blo 435777 1481867 := bstep (se 1 (by rfl) ⟨1111400, by rfl⟩ : syracuseStep 1481867 = 2222801) B2222801
theorem B1055963 : Blo 435777 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B2104775 : Blo 435777 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B2793041 : Blo 435777 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B4989275 : Blo 435777 4989275 := bstep (se 1 (by rfl) ⟨3741956, by rfl⟩ : syracuseStep 4989275 = 7483913) B7483913
theorem B1188263 : Blo 435777 1188263 := bstep (se 1 (by rfl) ⟨891197, by rfl⟩ : syracuseStep 1188263 = 1782395) B1782395
theorem B5677573 : Blo 435777 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B827977 : Blo 435777 827977 := bstep (se 2 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 827977 = 620983) B620983
theorem B1483487 : Blo 435777 1483487 := bstep (se 1 (by rfl) ⟨1112615, by rfl⟩ : syracuseStep 1483487 = 2225231) B2225231
theorem B4203323 : Blo 435777 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B1483919 : Blo 435777 1483919 := bstep (se 1 (by rfl) ⟨1112939, by rfl⟩ : syracuseStep 1483919 = 2225879) B2225879
theorem B1779083 : Blo 435777 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B435783 : Blo 435777 435783 := bstep (se 1 (by rfl) ⟨326837, by rfl⟩ : syracuseStep 435783 = 653675) B653675
theorem B435935 : Blo 435777 435935 := bstep (se 1 (by rfl) ⟨326951, by rfl⟩ : syracuseStep 435935 = 653903) B653903
theorem B436015 : Blo 435777 436015 := bstep (se 1 (by rfl) ⟨327011, by rfl⟩ : syracuseStep 436015 = 654023) B654023
theorem B436123 : Blo 435777 436123 := bstep (se 1 (by rfl) ⟨327092, by rfl⟩ : syracuseStep 436123 = 654185) B654185
theorem B436175 : Blo 435777 436175 := bstep (se 1 (by rfl) ⟨327131, by rfl⟩ : syracuseStep 436175 = 654263) B654263
theorem B436199 : Blo 435777 436199 := bstep (se 1 (by rfl) ⟨327149, by rfl⟩ : syracuseStep 436199 = 654299) B654299
theorem B2795705 : Blo 435777 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B1681661 : Blo 435777 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B436511 : Blo 435777 436511 := bstep (se 1 (by rfl) ⟨327383, by rfl⟩ : syracuseStep 436511 = 654767) B654767
theorem B436571 : Blo 435777 436571 := bstep (se 1 (by rfl) ⟨327428, by rfl⟩ : syracuseStep 436571 = 654857) B654857
theorem B1124699 : Blo 435777 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B15935849 : Blo 435777 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B436591 : Blo 435777 436591 := bstep (se 1 (by rfl) ⟨327443, by rfl⟩ : syracuseStep 436591 = 654887) B654887
theorem B436647 : Blo 435777 436647 := bstep (se 1 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 436647 = 654971) B654971
theorem B829921 : Blo 435777 829921 := bstep (se 2 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 829921 = 622441) B622441
theorem B436731 : Blo 435777 436731 := bstep (se 1 (by rfl) ⟨327548, by rfl⟩ : syracuseStep 436731 = 655097) B655097
theorem B436799 : Blo 435777 436799 := bstep (se 1 (by rfl) ⟨327599, by rfl⟩ : syracuseStep 436799 = 655199) B655199
theorem B436807 : Blo 435777 436807 := bstep (se 1 (by rfl) ⟨327605, by rfl⟩ : syracuseStep 436807 = 655211) B655211
theorem B11971151 : Blo 435777 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B9480827 : Blo 435777 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B436959 : Blo 435777 436959 := bstep (se 1 (by rfl) ⟨327719, by rfl⟩ : syracuseStep 436959 = 655439) B655439
theorem B437039 : Blo 435777 437039 := bstep (se 1 (by rfl) ⟨327779, by rfl⟩ : syracuseStep 437039 = 655559) B655559
theorem B437147 : Blo 435777 437147 := bstep (se 1 (by rfl) ⟨327860, by rfl⟩ : syracuseStep 437147 = 655721) B655721
theorem B437199 : Blo 435777 437199 := bstep (se 1 (by rfl) ⟨327899, by rfl⟩ : syracuseStep 437199 = 655799) B655799
theorem B437223 : Blo 435777 437223 := bstep (se 1 (by rfl) ⟨327917, by rfl⟩ : syracuseStep 437223 = 655835) B655835
theorem B437535 : Blo 435777 437535 := bstep (se 1 (by rfl) ⟨328151, by rfl⟩ : syracuseStep 437535 = 656303) B656303
theorem B437595 : Blo 435777 437595 := bstep (se 1 (by rfl) ⟨328196, by rfl⟩ : syracuseStep 437595 = 656393) B656393
theorem B437615 : Blo 435777 437615 := bstep (se 1 (by rfl) ⟨328211, by rfl⟩ : syracuseStep 437615 = 656423) B656423
theorem B437671 : Blo 435777 437671 := bstep (se 1 (by rfl) ⟨328253, by rfl⟩ : syracuseStep 437671 = 656507) B656507
theorem B830969 : Blo 435777 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B437755 : Blo 435777 437755 := bstep (se 1 (by rfl) ⟨328316, by rfl⟩ : syracuseStep 437755 = 656633) B656633
theorem B2108987 : Blo 435777 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B437823 : Blo 435777 437823 := bstep (se 1 (by rfl) ⟨328367, by rfl⟩ : syracuseStep 437823 = 656735) B656735
theorem B437831 : Blo 435777 437831 := bstep (se 1 (by rfl) ⟨328373, by rfl⟩ : syracuseStep 437831 = 656747) B656747
theorem B437983 : Blo 435777 437983 := bstep (se 1 (by rfl) ⟨328487, by rfl⟩ : syracuseStep 437983 = 656975) B656975
theorem B438063 : Blo 435777 438063 := bstep (se 1 (by rfl) ⟨328547, by rfl⟩ : syracuseStep 438063 = 657095) B657095
theorem B438171 : Blo 435777 438171 := bstep (se 1 (by rfl) ⟨328628, by rfl⟩ : syracuseStep 438171 = 657257) B657257
theorem B438223 : Blo 435777 438223 := bstep (se 1 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 438223 = 657335) B657335
theorem B438247 : Blo 435777 438247 := bstep (se 1 (by rfl) ⟨328685, by rfl⟩ : syracuseStep 438247 = 657371) B657371
theorem B2207897 : Blo 435777 2207897 := bstep (se 2 (by rfl) ⟨827961, by rfl⟩ : syracuseStep 2207897 = 1655923) B1655923
theorem B438559 : Blo 435777 438559 := bstep (se 1 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 438559 = 657839) B657839
theorem B71840033 : Blo 435777 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B438619 : Blo 435777 438619 := bstep (se 1 (by rfl) ⟨328964, by rfl⟩ : syracuseStep 438619 = 657929) B657929
theorem B438639 : Blo 435777 438639 := bstep (se 1 (by rfl) ⟨328979, by rfl⟩ : syracuseStep 438639 = 657959) B657959
theorem B438695 : Blo 435777 438695 := bstep (se 1 (by rfl) ⟨329021, by rfl⟩ : syracuseStep 438695 = 658043) B658043
theorem B438779 : Blo 435777 438779 := bstep (se 1 (by rfl) ⟨329084, by rfl⟩ : syracuseStep 438779 = 658169) B658169
theorem B438847 : Blo 435777 438847 := bstep (se 1 (by rfl) ⟨329135, by rfl⟩ : syracuseStep 438847 = 658271) B658271
theorem B438855 : Blo 435777 438855 := bstep (se 1 (by rfl) ⟨329141, by rfl⟩ : syracuseStep 438855 = 658283) B658283
theorem B439007 : Blo 435777 439007 := bstep (se 1 (by rfl) ⟨329255, by rfl⟩ : syracuseStep 439007 = 658511) B658511
theorem B439087 : Blo 435777 439087 := bstep (se 1 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 439087 = 658631) B658631
theorem B439195 : Blo 435777 439195 := bstep (se 1 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 439195 = 658793) B658793
theorem B832427 : Blo 435777 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B2208707 : Blo 435777 2208707 := bstep (se 1 (by rfl) ⟨1656530, by rfl⟩ : syracuseStep 2208707 = 3313061) B3313061
theorem B439247 : Blo 435777 439247 := bstep (se 1 (by rfl) ⟨329435, by rfl⟩ : syracuseStep 439247 = 658871) B658871
theorem B930791 : Blo 435777 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B439271 : Blo 435777 439271 := bstep (se 1 (by rfl) ⟨329453, by rfl⟩ : syracuseStep 439271 = 658907) B658907
theorem B9122867 : Blo 435777 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B832655 : Blo 435777 832655 := bstep (se 1 (by rfl) ⟨624491, by rfl⟩ : syracuseStep 832655 = 1248983) B1248983
theorem B439583 : Blo 435777 439583 := bstep (se 1 (by rfl) ⟨329687, by rfl⟩ : syracuseStep 439583 = 659375) B659375
theorem B439643 : Blo 435777 439643 := bstep (se 1 (by rfl) ⟨329732, by rfl⟩ : syracuseStep 439643 = 659465) B659465
theorem B439663 : Blo 435777 439663 := bstep (se 1 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 439663 = 659495) B659495
theorem B4011403 : Blo 435777 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B439719 : Blo 435777 439719 := bstep (se 1 (by rfl) ⟨329789, by rfl⟩ : syracuseStep 439719 = 659579) B659579
theorem B2111617 : Blo 435777 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B735655 : Blo 435777 735655 := bstep (se 1 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 735655 = 1103483) B1103483
theorem B735817 : Blo 435777 735817 := bstep (se 2 (by rfl) ⟨275931, by rfl⟩ : syracuseStep 735817 = 551863) B551863
theorem B735851 : Blo 435777 735851 := bstep (se 1 (by rfl) ⟨551888, by rfl⟩ : syracuseStep 735851 = 1103777) B1103777
theorem B998363 : Blo 435777 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B2374877 : Blo 435777 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2112733 : Blo 435777 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B2113235 : Blo 435777 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B5586691 : Blo 435777 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B60702605 : Blo 435777 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B737545 : Blo 435777 737545 := bstep (se 2 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 737545 = 553159) B553159
theorem B3752345 : Blo 435777 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B2212271 : Blo 435777 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B442951 : Blo 435777 442951 := bstep (se 1 (by rfl) ⟨332213, by rfl⟩ : syracuseStep 442951 = 664427) B664427
theorem B2376415 : Blo 435777 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B15418667 : Blo 435777 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B2213243 : Blo 435777 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B4572569 : Blo 435777 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B1263161 : Blo 435777 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B739003 : Blo 435777 739003 := bstep (se 1 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 739003 = 1108505) B1108505
theorem B935687 : Blo 435777 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B6408143 : Blo 435777 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B1657199 : Blo 435777 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B2673107 : Blo 435777 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B2214539 : Blo 435777 2214539 := bstep (se 1 (by rfl) ⟨1660904, by rfl⟩ : syracuseStep 2214539 = 3321809) B3321809
theorem B740063 : Blo 435777 740063 := bstep (se 1 (by rfl) ⟨555047, by rfl⟩ : syracuseStep 740063 = 1110095) B1110095
theorem B740495 : Blo 435777 740495 := bstep (se 1 (by rfl) ⟨555371, by rfl⟩ : syracuseStep 740495 = 1110743) B1110743
theorem B740731 : Blo 435777 740731 := bstep (se 1 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 740731 = 1111097) B1111097
theorem B5000939 : Blo 435777 5000939 := bstep (se 1 (by rfl) ⟨3750704, by rfl⟩ : syracuseStep 5000939 = 7501409) B7501409
theorem B1397083 : Blo 435777 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1659311 : Blo 435777 1659311 := bstep (se 1 (by rfl) ⟨1244483, by rfl⟩ : syracuseStep 1659311 = 2488967) B2488967
theorem B938719 : Blo 435777 938719 := bstep (se 1 (by rfl) ⟨704039, by rfl⟩ : syracuseStep 938719 = 1408079) B1408079
theorem B3298157 : Blo 435777 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1135603 : Blo 435777 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1070177 : Blo 435777 1070177 := bstep (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) B802633
theorem B1397903 : Blo 435777 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B5002397 : Blo 435777 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B1594567 : Blo 435777 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B1135859 : Blo 435777 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B1660283 : Blo 435777 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B1103291 : Blo 435777 1103291 := bstep (se 1 (by rfl) ⟨827468, by rfl⟩ : syracuseStep 1103291 = 1654937) B1654937
theorem B35149463 : Blo 435777 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B2709179 : Blo 435777 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B1661057 : Blo 435777 1661057 := bstep (se 2 (by rfl) ⟨622896, by rfl⟩ : syracuseStep 1661057 = 1245793) B1245793
theorem B2218265 : Blo 435777 2218265 := bstep (se 2 (by rfl) ⟨831849, by rfl⟩ : syracuseStep 2218265 = 1663699) B1663699
theorem B1104455 : Blo 435777 1104455 := bstep (se 1 (by rfl) ⟨828341, by rfl⟩ : syracuseStep 1104455 = 1656683) B1656683
theorem B13491467 : Blo 435777 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B4218313 : Blo 435777 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1662545 : Blo 435777 1662545 := bstep (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) B1246909
theorem B8216225 : Blo 435777 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B1662727 : Blo 435777 1662727 := bstep (se 1 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 1662727 = 2494091) B2494091
theorem B1105721 : Blo 435777 1105721 := bstep (se 2 (by rfl) ⟨414645, by rfl⟩ : syracuseStep 1105721 = 829291) B829291
theorem B6283183 : Blo 435777 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B1663001 : Blo 435777 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B4218929 : Blo 435777 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B4251953 : Blo 435777 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B1401313 : Blo 435777 1401313 := bstep (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) B1050985
theorem B746167 : Blo 435777 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B2221019 : Blo 435777 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B1107067 : Blo 435777 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B2221181 : Blo 435777 2221181 := bstep (se 3 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 2221181 = 832943) B832943
theorem B1926443 : Blo 435777 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B1992023 : Blo 435777 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B2221505 : Blo 435777 2221505 := bstep (se 2 (by rfl) ⟨833064, by rfl⟩ : syracuseStep 2221505 = 1666129) B1666129
theorem B8382041 : Blo 435777 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B1664975 : Blo 435777 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B3729725 : Blo 435777 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B1108475 : Blo 435777 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B1665643 : Blo 435777 1665643 := bstep (se 1 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 1665643 = 2498465) B2498465
theorem B3369595 : Blo 435777 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1665917 : Blo 435777 1665917 := bstep (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) B624719
theorem B1665947 : Blo 435777 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B5598173 : Blo 435777 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B552359 : Blo 435777 552359 := bstep (se 1 (by rfl) ⟨414269, by rfl⟩ : syracuseStep 552359 = 828539) B828539
theorem B1109447 : Blo 435777 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B1109497 : Blo 435777 1109497 := bstep (se 2 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 1109497 = 832123) B832123
theorem B367586819 : Blo 435777 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B552511 : Blo 435777 552511 := bstep (se 1 (by rfl) ⟨414383, by rfl⟩ : syracuseStep 552511 = 828767) B828767
theorem B552683 : Blo 435777 552683 := bstep (se 1 (by rfl) ⟨414512, by rfl⟩ : syracuseStep 552683 = 829025) B829025
theorem B1109801 : Blo 435777 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B23949107 : Blo 435777 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B56323981 : Blo 435777 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B1110145 : Blo 435777 1110145 := bstep (se 2 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 1110145 = 832609) B832609
theorem B3993857 : Blo 435777 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1864043 : Blo 435777 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B1700423 : Blo 435777 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B553655 : Blo 435777 553655 := bstep (se 1 (by rfl) ⟨415241, by rfl⟩ : syracuseStep 553655 = 830483) B830483
theorem B2486983 : Blo 435777 2486983 := bstep (se 1 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 2486983 = 3730475) B3730475
theorem B553807 : Blo 435777 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B3732389 : Blo 435777 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B1110955 : Blo 435777 1110955 := bstep (se 1 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 1110955 = 1666433) B1666433
theorem B1668059 : Blo 435777 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B7992377 : Blo 435777 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B1995923 : Blo 435777 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B1111259 : Blo 435777 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B1111391 : Blo 435777 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B2815337 : Blo 435777 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B28407185 : Blo 435777 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B980783 : Blo 435777 980783 := bstep (se 1 (by rfl) ⟨735587, by rfl⟩ : syracuseStep 980783 = 1471175) B1471175
theorem B1242935 : Blo 435777 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B1112089 : Blo 435777 1112089 := bstep (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) B834067
theorem B2357495 : Blo 435777 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1112393 : Blo 435777 1112393 := bstep (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) B834295
theorem B981359 : Blo 435777 981359 := bstep (se 1 (by rfl) ⟨736019, by rfl⟩ : syracuseStep 981359 = 1472039) B1472039
theorem B4979069 : Blo 435777 4979069 := bstep (se 3 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 4979069 = 1867151) B1867151
theorem B653735 : Blo 435777 653735 := bstep (se 1 (by rfl) ⟨490301, by rfl⟩ : syracuseStep 653735 = 980603) B980603
theorem B981431 : Blo 435777 981431 := bstep (se 1 (by rfl) ⟨736073, by rfl⟩ : syracuseStep 981431 = 1472147) B1472147
theorem B653819 : Blo 435777 653819 := bstep (se 1 (by rfl) ⟨490364, by rfl⟩ : syracuseStep 653819 = 980729) B980729
theorem B981575 : Blo 435777 981575 := bstep (se 1 (by rfl) ⟨736181, by rfl⟩ : syracuseStep 981575 = 1472363) B1472363
theorem B1047113 : Blo 435777 1047113 := bstep (se 2 (by rfl) ⟨392667, by rfl⟩ : syracuseStep 1047113 = 785335) B785335
theorem B981611 : Blo 435777 981611 := bstep (se 1 (by rfl) ⟨736208, by rfl⟩ : syracuseStep 981611 = 1472417) B1472417
theorem B653945 : Blo 435777 653945 := bstep (se 2 (by rfl) ⟨245229, by rfl⟩ : syracuseStep 653945 = 490459) B490459
theorem B752249 : Blo 435777 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B653999 : Blo 435777 653999 := bstep (se 1 (by rfl) ⟨490499, by rfl⟩ : syracuseStep 653999 = 980999) B980999
theorem B654047 : Blo 435777 654047 := bstep (se 1 (by rfl) ⟨490535, by rfl⟩ : syracuseStep 654047 = 981071) B981071
theorem B1047467 : Blo 435777 1047467 := bstep (se 1 (by rfl) ⟨785600, by rfl⟩ : syracuseStep 1047467 = 1571201) B1571201
theorem B654311 : Blo 435777 654311 := bstep (se 1 (by rfl) ⟨490733, by rfl⟩ : syracuseStep 654311 = 981467) B981467
theorem B982007 : Blo 435777 982007 := bstep (se 1 (by rfl) ⟨736505, by rfl⟩ : syracuseStep 982007 = 1473011) B1473011
theorem B1473659 : Blo 435777 1473659 := bstep (se 1 (by rfl) ⟨1105244, by rfl⟩ : syracuseStep 1473659 = 2210489) B2210489
theorem B12582053 : Blo 435777 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B654569 : Blo 435777 654569 := bstep (se 2 (by rfl) ⟨245463, by rfl⟩ : syracuseStep 654569 = 490927) B490927
theorem B490783 : Blo 435777 490783 := bstep (se 1 (by rfl) ⟨368087, by rfl⟩ : syracuseStep 490783 = 736175) B736175
theorem B654623 : Blo 435777 654623 := bstep (se 1 (by rfl) ⟨490967, by rfl⟩ : syracuseStep 654623 = 981935) B981935
theorem B3145027 : Blo 435777 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B982367 : Blo 435777 982367 := bstep (se 1 (by rfl) ⟨736775, by rfl⟩ : syracuseStep 982367 = 1473551) B1473551
theorem B556399 : Blo 435777 556399 := bstep (se 1 (by rfl) ⟨417299, by rfl⟩ : syracuseStep 556399 = 834599) B834599
theorem B2358665 : Blo 435777 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B1473929 : Blo 435777 1473929 := bstep (se 2 (by rfl) ⟨552723, by rfl⟩ : syracuseStep 1473929 = 1105447) B1105447
theorem B4750757 : Blo 435777 4750757 := bstep (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) B890767
theorem B654791 : Blo 435777 654791 := bstep (se 1 (by rfl) ⟨491093, by rfl⟩ : syracuseStep 654791 = 982187) B982187
theorem B491071 : Blo 435777 491071 := bstep (se 1 (by rfl) ⟨368303, by rfl⟩ : syracuseStep 491071 = 736607) B736607
theorem B982763 : Blo 435777 982763 := bstep (se 1 (by rfl) ⟨737072, by rfl⟩ : syracuseStep 982763 = 1474145) B1474145
theorem B655145 : Blo 435777 655145 := bstep (se 2 (by rfl) ⟨245679, by rfl⟩ : syracuseStep 655145 = 491359) B491359
theorem B655151 : Blo 435777 655151 := bstep (se 1 (by rfl) ⟨491363, by rfl⟩ : syracuseStep 655151 = 982727) B982727
theorem B1474361 : Blo 435777 1474361 := bstep (se 2 (by rfl) ⟨552885, by rfl⟩ : syracuseStep 1474361 = 1105771) B1105771
theorem B2490173 : Blo 435777 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B982889 : Blo 435777 982889 := bstep (se 2 (by rfl) ⟨368583, by rfl⟩ : syracuseStep 982889 = 737167) B737167
theorem B1245223 : Blo 435777 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B10485811 : Blo 435777 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B1474847 : Blo 435777 1474847 := bstep (se 1 (by rfl) ⟨1106135, by rfl⟩ : syracuseStep 1474847 = 2212271) B2212271
theorem B1180001 : Blo 435777 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B983393 : Blo 435777 983393 := bstep (se 2 (by rfl) ⟨368772, by rfl⟩ : syracuseStep 983393 = 737545) B737545
theorem B983483 : Blo 435777 983483 := bstep (se 1 (by rfl) ⟨737612, by rfl⟩ : syracuseStep 983483 = 1475225) B1475225
theorem B655823 : Blo 435777 655823 := bstep (se 1 (by rfl) ⟨491867, by rfl⟩ : syracuseStep 655823 = 983735) B983735
theorem B1442281 : Blo 435777 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B655865 : Blo 435777 655865 := bstep (se 2 (by rfl) ⟨245949, by rfl⟩ : syracuseStep 655865 = 491899) B491899
theorem B655967 : Blo 435777 655967 := bstep (se 1 (by rfl) ⟨491975, by rfl⟩ : syracuseStep 655967 = 983951) B983951
theorem B1868417 : Blo 435777 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B7570097 : Blo 435777 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1475495 : Blo 435777 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B656447 : Blo 435777 656447 := bstep (se 1 (by rfl) ⟨492335, by rfl⟩ : syracuseStep 656447 = 984671) B984671
theorem B656489 : Blo 435777 656489 := bstep (se 2 (by rfl) ⟨246183, by rfl⟩ : syracuseStep 656489 = 492367) B492367
theorem B623791 : Blo 435777 623791 := bstep (se 1 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 623791 = 935687) B935687
theorem B656591 : Blo 435777 656591 := bstep (se 1 (by rfl) ⟨492443, by rfl⟩ : syracuseStep 656591 = 984887) B984887
theorem B656795 : Blo 435777 656795 := bstep (se 1 (by rfl) ⟨492596, by rfl⟩ : syracuseStep 656795 = 985193) B985193
theorem B984491 : Blo 435777 984491 := bstep (se 1 (by rfl) ⟨738368, by rfl⟩ : syracuseStep 984491 = 1476737) B1476737
theorem B1476089 : Blo 435777 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B657017 : Blo 435777 657017 := bstep (se 2 (by rfl) ⟨246381, by rfl⟩ : syracuseStep 657017 = 492763) B492763
theorem B984743 : Blo 435777 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B657119 : Blo 435777 657119 := bstep (se 1 (by rfl) ⟨492839, by rfl⟩ : syracuseStep 657119 = 985679) B985679
theorem B1476359 : Blo 435777 1476359 := bstep (se 1 (by rfl) ⟨1107269, by rfl⟩ : syracuseStep 1476359 = 2214539) B2214539
theorem B1476413 : Blo 435777 1476413 := bstep (se 3 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 1476413 = 553655) B553655
theorem B657215 : Blo 435777 657215 := bstep (se 1 (by rfl) ⟨492911, by rfl⟩ : syracuseStep 657215 = 985823) B985823
theorem B493375 : Blo 435777 493375 := bstep (se 1 (by rfl) ⟨370031, by rfl⟩ : syracuseStep 493375 = 740063) B740063
theorem B1771463 : Blo 435777 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B985031 : Blo 435777 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B657383 : Blo 435777 657383 := bstep (se 1 (by rfl) ⟨493037, by rfl⟩ : syracuseStep 657383 = 986075) B986075
theorem B657401 : Blo 435777 657401 := bstep (se 2 (by rfl) ⟨246525, by rfl⟩ : syracuseStep 657401 = 493051) B493051
theorem B657503 : Blo 435777 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B493663 : Blo 435777 493663 := bstep (se 1 (by rfl) ⟨370247, by rfl⟩ : syracuseStep 493663 = 740495) B740495
theorem B657563 : Blo 435777 657563 := bstep (se 1 (by rfl) ⟨493172, by rfl⟩ : syracuseStep 657563 = 986345) B986345
theorem B657599 : Blo 435777 657599 := bstep (se 1 (by rfl) ⟨493199, by rfl⟩ : syracuseStep 657599 = 986399) B986399
theorem B657641 : Blo 435777 657641 := bstep (se 2 (by rfl) ⟨246615, by rfl⟩ : syracuseStep 657641 = 493231) B493231
theorem B985337 : Blo 435777 985337 := bstep (se 2 (by rfl) ⟨369501, by rfl⟩ : syracuseStep 985337 = 739003) B739003
theorem B985391 : Blo 435777 985391 := bstep (se 1 (by rfl) ⟨739043, by rfl⟩ : syracuseStep 985391 = 1478087) B1478087
theorem B985607 : Blo 435777 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B657947 : Blo 435777 657947 := bstep (se 1 (by rfl) ⟨493460, by rfl⟩ : syracuseStep 657947 = 986921) B986921
theorem B658025 : Blo 435777 658025 := bstep (se 2 (by rfl) ⟨246759, by rfl⟩ : syracuseStep 658025 = 493519) B493519
theorem B4983443 : Blo 435777 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B985787 : Blo 435777 985787 := bstep (se 1 (by rfl) ⟨739340, by rfl⟩ : syracuseStep 985787 = 1478681) B1478681
theorem B2853805 : Blo 435777 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B2362405 : Blo 435777 2362405 := bstep (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) B442951
theorem B658553 : Blo 435777 658553 := bstep (se 2 (by rfl) ⟨246957, by rfl⟩ : syracuseStep 658553 = 493915) B493915
theorem B658655 : Blo 435777 658655 := bstep (se 1 (by rfl) ⟨493991, by rfl⟩ : syracuseStep 658655 = 987983) B987983
theorem B2198771 : Blo 435777 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B658697 : Blo 435777 658697 := bstep (se 2 (by rfl) ⟨247011, by rfl⟩ : syracuseStep 658697 = 494023) B494023
theorem B789839 : Blo 435777 789839 := bstep (se 1 (by rfl) ⟨592379, by rfl⟩ : syracuseStep 789839 = 1184759) B1184759
theorem B658799 : Blo 435777 658799 := bstep (se 1 (by rfl) ⟨494099, by rfl⟩ : syracuseStep 658799 = 988199) B988199
theorem B658919 : Blo 435777 658919 := bstep (se 1 (by rfl) ⟨494189, by rfl⟩ : syracuseStep 658919 = 988379) B988379
theorem B986615 : Blo 435777 986615 := bstep (se 1 (by rfl) ⟨739961, by rfl⟩ : syracuseStep 986615 = 1479923) B1479923
theorem B4492793 : Blo 435777 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B986687 : Blo 435777 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B659051 : Blo 435777 659051 := bstep (se 1 (by rfl) ⟨494288, by rfl⟩ : syracuseStep 659051 = 988577) B988577
theorem B659177 : Blo 435777 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B12193517 : Blo 435777 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B23432975 : Blo 435777 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B1806119 : Blo 435777 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B659321 : Blo 435777 659321 := bstep (se 2 (by rfl) ⟨247245, by rfl⟩ : syracuseStep 659321 = 494491) B494491
theorem B659423 : Blo 435777 659423 := bstep (se 1 (by rfl) ⟨494567, by rfl⟩ : syracuseStep 659423 = 989135) B989135
theorem B1478843 : Blo 435777 1478843 := bstep (se 1 (by rfl) ⟨1109132, by rfl⟩ : syracuseStep 1478843 = 2218265) B2218265
theorem B987641 : Blo 435777 987641 := bstep (se 2 (by rfl) ⟨370365, by rfl⟩ : syracuseStep 987641 = 740731) B740731
theorem B987731 : Blo 435777 987731 := bstep (se 1 (by rfl) ⟨740798, by rfl⟩ : syracuseStep 987731 = 1481597) B1481597
theorem B1479329 : Blo 435777 1479329 := bstep (se 2 (by rfl) ⟨554748, by rfl⟩ : syracuseStep 1479329 = 1109497) B1109497
theorem B987911 : Blo 435777 987911 := bstep (se 1 (by rfl) ⟨740933, by rfl⟩ : syracuseStep 987911 = 1481867) B1481867
theorem B5477483 : Blo 435777 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B4199633 : Blo 435777 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1480193 : Blo 435777 1480193 := bstep (se 2 (by rfl) ⟨555072, by rfl⟩ : syracuseStep 1480193 = 1110145) B1110145
theorem B792175 : Blo 435777 792175 := bstep (se 1 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 792175 = 1188263) B1188263
theorem B988991 : Blo 435777 988991 := bstep (se 1 (by rfl) ⟨741743, by rfl⟩ : syracuseStep 988991 = 1483487) B1483487
theorem B1480679 : Blo 435777 1480679 := bstep (se 1 (by rfl) ⟨1110509, by rfl⟩ : syracuseStep 1480679 = 2221019) B2221019
theorem B1480787 : Blo 435777 1480787 := bstep (se 1 (by rfl) ⟨1110590, by rfl⟩ : syracuseStep 1480787 = 2221181) B2221181
theorem B989279 : Blo 435777 989279 := bstep (se 1 (by rfl) ⟨741959, by rfl⟩ : syracuseStep 989279 = 1483919) B1483919
theorem B1186055 : Blo 435777 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B3315977 : Blo 435777 3315977 := bstep (se 2 (by rfl) ⟨1243491, by rfl⟩ : syracuseStep 3315977 = 2486983) B2486983
theorem B1251625 : Blo 435777 1251625 := bstep (se 2 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 1251625 = 938719) B938719
theorem B1481003 : Blo 435777 1481003 := bstep (se 1 (by rfl) ⟨1110752, by rfl⟩ : syracuseStep 1481003 = 2221505) B2221505
theorem B1481273 : Blo 435777 1481273 := bstep (se 2 (by rfl) ⟨555477, by rfl⟩ : syracuseStep 1481273 = 1110955) B1110955
theorem B1514137 : Blo 435777 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B10623899 : Blo 435777 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B5348537 : Blo 435777 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B15966071 : Blo 435777 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B2662301 : Blo 435777 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B1482785 : Blo 435777 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B2662571 : Blo 435777 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B6333005 : Blo 435777 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B1876891 : Blo 435777 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B828623 : Blo 435777 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B3319379 : Blo 435777 3319379 := bstep (se 1 (by rfl) ⟨2489534, by rfl⟩ : syracuseStep 3319379 = 4979069) B4979069
theorem B435823 : Blo 435777 435823 := bstep (se 1 (by rfl) ⟨326867, by rfl⟩ : syracuseStep 435823 = 653735) B653735
theorem B435879 : Blo 435777 435879 := bstep (se 1 (by rfl) ⟨326909, by rfl⟩ : syracuseStep 435879 = 653819) B653819
theorem B698075 : Blo 435777 698075 := bstep (se 1 (by rfl) ⟨523556, by rfl⟩ : syracuseStep 698075 = 1047113) B1047113
theorem B435963 : Blo 435777 435963 := bstep (se 1 (by rfl) ⟨326972, by rfl⟩ : syracuseStep 435963 = 653945) B653945
theorem B501499 : Blo 435777 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B435999 : Blo 435777 435999 := bstep (se 1 (by rfl) ⟨326999, by rfl⟩ : syracuseStep 435999 = 653999) B653999
theorem B436031 : Blo 435777 436031 := bstep (se 1 (by rfl) ⟨327023, by rfl⟩ : syracuseStep 436031 = 654047) B654047
theorem B698311 : Blo 435777 698311 := bstep (se 1 (by rfl) ⟨523733, by rfl⟩ : syracuseStep 698311 = 1047467) B1047467
theorem B436207 : Blo 435777 436207 := bstep (se 1 (by rfl) ⟨327155, by rfl⟩ : syracuseStep 436207 = 654311) B654311
theorem B300394565 : Blo 435777 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B436379 : Blo 435777 436379 := bstep (se 1 (by rfl) ⟨327284, by rfl⟩ : syracuseStep 436379 = 654569) B654569
theorem B436415 : Blo 435777 436415 := bstep (se 1 (by rfl) ⟨327311, by rfl⟩ : syracuseStep 436415 = 654623) B654623
theorem B436527 : Blo 435777 436527 := bstep (se 1 (by rfl) ⟨327395, by rfl⟩ : syracuseStep 436527 = 654791) B654791
theorem B7448921 : Blo 435777 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B436763 : Blo 435777 436763 := bstep (se 1 (by rfl) ⟨327572, by rfl⟩ : syracuseStep 436763 = 655145) B655145
theorem B436767 : Blo 435777 436767 := bstep (se 1 (by rfl) ⟨327575, by rfl⟩ : syracuseStep 436767 = 655151) B655151
theorem B830263 : Blo 435777 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B437083 : Blo 435777 437083 := bstep (se 1 (by rfl) ⟨327812, by rfl⟩ : syracuseStep 437083 = 655625) B655625
theorem B437151 : Blo 435777 437151 := bstep (se 1 (by rfl) ⟨327863, by rfl⟩ : syracuseStep 437151 = 655727) B655727
theorem B2501563 : Blo 435777 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B437295 : Blo 435777 437295 := bstep (se 1 (by rfl) ⟨327971, by rfl⟩ : syracuseStep 437295 = 655943) B655943
theorem B437319 : Blo 435777 437319 := bstep (se 1 (by rfl) ⟨327989, by rfl⟩ : syracuseStep 437319 = 655979) B655979
theorem B2403425 : Blo 435777 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B437471 : Blo 435777 437471 := bstep (se 1 (by rfl) ⟨328103, by rfl⟩ : syracuseStep 437471 = 656207) B656207
theorem B437735 : Blo 435777 437735 := bstep (se 1 (by rfl) ⟨328301, by rfl⟩ : syracuseStep 437735 = 656603) B656603
theorem B994889 : Blo 435777 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B437851 : Blo 435777 437851 := bstep (se 1 (by rfl) ⟨328388, by rfl⟩ : syracuseStep 437851 = 656777) B656777
theorem B831151 : Blo 435777 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B634663 : Blo 435777 634663 := bstep (se 1 (by rfl) ⟨475997, by rfl⟩ : syracuseStep 634663 = 951995) B951995
theorem B438087 : Blo 435777 438087 := bstep (se 1 (by rfl) ⟨328565, by rfl⟩ : syracuseStep 438087 = 657131) B657131
theorem B831455 : Blo 435777 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B438239 : Blo 435777 438239 := bstep (se 1 (by rfl) ⟨328679, by rfl⟩ : syracuseStep 438239 = 657359) B657359
theorem B4272095 : Blo 435777 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B438503 : Blo 435777 438503 := bstep (se 1 (by rfl) ⟨328877, by rfl⟩ : syracuseStep 438503 = 657755) B657755
theorem B1782071 : Blo 435777 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B438655 : Blo 435777 438655 := bstep (se 1 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 438655 = 657983) B657983
theorem B438735 : Blo 435777 438735 := bstep (se 1 (by rfl) ⟨329051, by rfl⟩ : syracuseStep 438735 = 658103) B658103
theorem B438887 : Blo 435777 438887 := bstep (se 1 (by rfl) ⟨329165, by rfl⟩ : syracuseStep 438887 = 658331) B658331
theorem B439151 : Blo 435777 439151 := bstep (se 1 (by rfl) ⟨329363, by rfl⟩ : syracuseStep 439151 = 658727) B658727
theorem B439207 : Blo 435777 439207 := bstep (se 1 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 439207 = 658811) B658811
theorem B439291 : Blo 435777 439291 := bstep (se 1 (by rfl) ⟨329468, by rfl⟩ : syracuseStep 439291 = 658937) B658937
theorem B11973689 : Blo 435777 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B439359 : Blo 435777 439359 := bstep (se 1 (by rfl) ⟨329519, by rfl⟩ : syracuseStep 439359 = 659039) B659039
theorem B439503 : Blo 435777 439503 := bstep (se 1 (by rfl) ⟨329627, by rfl⟩ : syracuseStep 439503 = 659255) B659255
theorem B439707 : Blo 435777 439707 := bstep (se 1 (by rfl) ⟨329780, by rfl⟩ : syracuseStep 439707 = 659561) B659561
theorem B833095 : Blo 435777 833095 := bstep (se 1 (by rfl) ⟨624821, by rfl⟩ : syracuseStep 833095 = 1249643) B1249643
theorem B2799269 : Blo 435777 2799269 := bstep (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) B524863
theorem B3323753 : Blo 435777 3323753 := bstep (se 2 (by rfl) ⟨1246407, by rfl⟩ : syracuseStep 3323753 = 2492815) B2492815
theorem B2799497 : Blo 435777 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B735527 : Blo 435777 735527 := bstep (se 1 (by rfl) ⟨551645, by rfl⟩ : syracuseStep 735527 = 1103291) B1103291
theorem B833915 : Blo 435777 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B736303 : Blo 435777 736303 := bstep (se 1 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 736303 = 1104455) B1104455
theorem B736681 : Blo 435777 736681 := bstep (se 2 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 736681 = 552511) B552511
theorem B703975 : Blo 435777 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B8994311 : Blo 435777 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B737147 : Blo 435777 737147 := bstep (se 1 (by rfl) ⟨552860, by rfl⟩ : syracuseStep 737147 = 1105721) B1105721
theorem B2834635 : Blo 435777 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B22724813 : Blo 435777 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B3326183 : Blo 435777 3326183 := bstep (se 1 (by rfl) ⟨2494637, by rfl⟩ : syracuseStep 3326183 = 4989275) B4989275
theorem B2802215 : Blo 435777 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B1328015 : Blo 435777 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B2999197 : Blo 435777 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B5588027 : Blo 435777 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B738409 : Blo 435777 738409 := bstep (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) B553807
theorem B738983 : Blo 435777 738983 := bstep (se 1 (by rfl) ⟨554237, by rfl⟩ : syracuseStep 738983 = 1108475) B1108475
theorem B7980767 : Blo 435777 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B739631 : Blo 435777 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B245057879 : Blo 435777 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B739867 : Blo 435777 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B47893355 : Blo 435777 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B1133615 : Blo 435777 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B6081911 : Blo 435777 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B5328251 : Blo 435777 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B1330615 : Blo 435777 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B740839 : Blo 435777 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B740927 : Blo 435777 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B741595 : Blo 435777 741595 := bstep (se 1 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 741595 = 1112393) B1112393
theorem B741865 : Blo 435777 741865 := bstep (se 2 (by rfl) ⟨278199, by rfl⟩ : syracuseStep 741865 = 556399) B556399
theorem B5624417 : Blo 435777 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B3167171 : Blo 435777 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B2216969 : Blo 435777 2216969 := bstep (se 2 (by rfl) ⟨831363, by rfl⟩ : syracuseStep 2216969 = 1662727) B1662727
theorem B1660115 : Blo 435777 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B8377577 : Blo 435777 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B6838151 : Blo 435777 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B1103969 : Blo 435777 1103969 := bstep (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) B827977
theorem B10279111 : Blo 435777 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B3168553 : Blo 435777 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B2808701 : Blo 435777 2808701 := bstep (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) B1053263
theorem B1104799 : Blo 435777 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B1400057 : Blo 435777 1400057 := bstep (se 2 (by rfl) ⟨525021, by rfl⟩ : syracuseStep 1400057 = 1050043) B1050043
theorem B1400159 : Blo 435777 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B4545953 : Blo 435777 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B5332385 : Blo 435777 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B3333959 : Blo 435777 3333959 := bstep (se 1 (by rfl) ⟨2500469, by rfl⟩ : syracuseStep 3333959 = 5000939) B5000939
theorem B12115829 : Blo 435777 12115829 := bstep (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) B1135859
theorem B2482109 : Blo 435777 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B1106207 : Blo 435777 1106207 := bstep (se 1 (by rfl) ⟨829655, by rfl⟩ : syracuseStep 1106207 = 1659311) B1659311
theorem B3727741 : Blo 435777 3727741 := bstep (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) B1397903
theorem B1401275 : Blo 435777 1401275 := bstep (se 1 (by rfl) ⟨1050956, by rfl⟩ : syracuseStep 1401275 = 2101913) B2101913
theorem B1106561 : Blo 435777 1106561 := bstep (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) B829921
theorem B21652103 : Blo 435777 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B3334931 : Blo 435777 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B5137181 : Blo 435777 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B2220857 : Blo 435777 2220857 := bstep (se 2 (by rfl) ⟨832821, by rfl⟩ : syracuseStep 2220857 = 1665643) B1665643
theorem B1106855 : Blo 435777 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B1107371 : Blo 435777 1107371 := bstep (se 1 (by rfl) ⟨830528, by rfl⟩ : syracuseStep 1107371 = 1661057) B1661057
theorem B3368429 : Blo 435777 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B1403183 : Blo 435777 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B1862027 : Blo 435777 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1108363 : Blo 435777 1108363 := bstep (se 1 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 1108363 = 1662545) B1662545
theorem B1108667 : Blo 435777 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B2812619 : Blo 435777 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B1862777 : Blo 435777 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B4484429 : Blo 435777 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1109983 : Blo 435777 1109983 := bstep (se 1 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 1109983 = 1664975) B1664975
theorem B1863803 : Blo 435777 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B2486483 : Blo 435777 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B2126089 : Blo 435777 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B6320551 : Blo 435777 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B1110611 : Blo 435777 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B1110631 : Blo 435777 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B3732115 : Blo 435777 3732115 := bstep (se 1 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 3732115 = 5598173) B5598173
theorem B553979 : Blo 435777 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B1405991 : Blo 435777 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B1471931 : Blo 435777 1471931 := bstep (se 1 (by rfl) ⟨1103948, by rfl⟩ : syracuseStep 1471931 = 2207897) B2207897
theorem B2815489 : Blo 435777 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B1242695 : Blo 435777 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B980873 : Blo 435777 980873 := bstep (se 2 (by rfl) ⟨367827, by rfl⟩ : syracuseStep 980873 = 735655) B735655
theorem B2488259 : Blo 435777 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B554951 : Blo 435777 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B1472471 : Blo 435777 1472471 := bstep (se 1 (by rfl) ⟨1104353, by rfl⟩ : syracuseStep 1472471 = 2208707) B2208707
theorem B1112039 : Blo 435777 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B555103 : Blo 435777 555103 := bstep (se 1 (by rfl) ⟨416327, by rfl⟩ : syracuseStep 555103 = 832655) B832655
theorem B981089 : Blo 435777 981089 := bstep (se 2 (by rfl) ⟨367908, by rfl⟩ : syracuseStep 981089 = 735817) B735817
theorem B18938123 : Blo 435777 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B1472957 : Blo 435777 1472957 := bstep (se 3 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 1472957 = 552359) B552359
theorem B653855 : Blo 435777 653855 := bstep (se 1 (by rfl) ⟨490391, by rfl⟩ : syracuseStep 653855 = 980783) B980783
theorem B1571663 : Blo 435777 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B654239 : Blo 435777 654239 := bstep (se 1 (by rfl) ⟨490679, by rfl⟩ : syracuseStep 654239 = 981359) B981359
theorem B654287 : Blo 435777 654287 := bstep (se 1 (by rfl) ⟨490715, by rfl⟩ : syracuseStep 654287 = 981431) B981431
theorem B2816977 : Blo 435777 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B654377 : Blo 435777 654377 := bstep (se 2 (by rfl) ⟨245391, by rfl⟩ : syracuseStep 654377 = 490783) B490783
theorem B654383 : Blo 435777 654383 := bstep (se 1 (by rfl) ⟨490787, by rfl⟩ : syracuseStep 654383 = 981575) B981575
theorem B490567 : Blo 435777 490567 := bstep (se 1 (by rfl) ⟨367925, by rfl⟩ : syracuseStep 490567 = 735851) B735851
theorem B654407 : Blo 435777 654407 := bstep (se 1 (by rfl) ⟨490805, by rfl⟩ : syracuseStep 654407 = 981611) B981611
theorem B4193369 : Blo 435777 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B1473821 : Blo 435777 1473821 := bstep (se 3 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 1473821 = 552683) B552683
theorem B654671 : Blo 435777 654671 := bstep (se 1 (by rfl) ⟨491003, by rfl⟩ : syracuseStep 654671 = 982007) B982007
theorem B982439 : Blo 435777 982439 := bstep (se 1 (by rfl) ⟨736829, by rfl⟩ : syracuseStep 982439 = 1473659) B1473659
theorem B654761 : Blo 435777 654761 := bstep (se 2 (by rfl) ⟨245535, by rfl⟩ : syracuseStep 654761 = 491071) B491071
theorem B8388035 : Blo 435777 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B654911 : Blo 435777 654911 := bstep (se 1 (by rfl) ⟨491183, by rfl⟩ : syracuseStep 654911 = 982367) B982367
theorem B1572443 : Blo 435777 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B982619 : Blo 435777 982619 := bstep (se 1 (by rfl) ⟨736964, by rfl⟩ : syracuseStep 982619 = 1473929) B1473929
theorem B1408823 : Blo 435777 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B655175 : Blo 435777 655175 := bstep (se 1 (by rfl) ⟨491381, by rfl⟩ : syracuseStep 655175 = 982763) B982763
theorem B982907 : Blo 435777 982907 := bstep (se 1 (by rfl) ⟨737180, by rfl⟩ : syracuseStep 982907 = 1474361) B1474361
theorem B655259 : Blo 435777 655259 := bstep (se 1 (by rfl) ⟨491444, by rfl⟩ : syracuseStep 655259 = 982889) B982889
theorem B40468403 : Blo 435777 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B983231 : Blo 435777 983231 := bstep (se 1 (by rfl) ⟨737423, by rfl⟩ : syracuseStep 983231 = 1474847) B1474847
theorem B786667 : Blo 435777 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B655595 : Blo 435777 655595 := bstep (se 1 (by rfl) ⟨491696, by rfl⟩ : syracuseStep 655595 = 983393) B983393
theorem B655655 : Blo 435777 655655 := bstep (se 1 (by rfl) ⟨491741, by rfl⟩ : syracuseStep 655655 = 983483) B983483
theorem B1868143 : Blo 435777 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B1245611 : Blo 435777 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B5046731 : Blo 435777 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B885343 : Blo 435777 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B983663 : Blo 435777 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B656327 : Blo 435777 656327 := bstep (se 1 (by rfl) ⟨492245, by rfl⟩ : syracuseStep 656327 = 984491) B984491
theorem B984059 : Blo 435777 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B656495 : Blo 435777 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B492655 : Blo 435777 492655 := bstep (se 1 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 492655 = 738983) B738983
theorem B984239 : Blo 435777 984239 := bstep (se 1 (by rfl) ⟨738179, by rfl⟩ : syracuseStep 984239 = 1476359) B1476359
theorem B984275 : Blo 435777 984275 := bstep (se 1 (by rfl) ⟨738206, by rfl⟩ : syracuseStep 984275 = 1476413) B1476413
theorem B1180975 : Blo 435777 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B656687 : Blo 435777 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B984545 : Blo 435777 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B656891 : Blo 435777 656891 := bstep (se 1 (by rfl) ⟨492668, by rfl⟩ : syracuseStep 656891 = 985337) B985337
theorem B656927 : Blo 435777 656927 := bstep (se 1 (by rfl) ⟨492695, by rfl⟩ : syracuseStep 656927 = 985391) B985391
theorem B493087 : Blo 435777 493087 := bstep (se 1 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 493087 = 739631) B739631
theorem B657071 : Blo 435777 657071 := bstep (se 1 (by rfl) ⟨492803, by rfl⟩ : syracuseStep 657071 = 985607) B985607
theorem B657191 : Blo 435777 657191 := bstep (se 1 (by rfl) ⟨492893, by rfl⟩ : syracuseStep 657191 = 985787) B985787
theorem B755743 : Blo 435777 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B526559 : Blo 435777 526559 := bstep (se 1 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 526559 = 789839) B789839
theorem B657743 : Blo 435777 657743 := bstep (se 1 (by rfl) ⟨493307, by rfl⟩ : syracuseStep 657743 = 986615) B986615
theorem B657791 : Blo 435777 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B493951 : Blo 435777 493951 := bstep (se 1 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 493951 = 740927) B740927
theorem B657833 : Blo 435777 657833 := bstep (se 2 (by rfl) ⟨246687, by rfl⟩ : syracuseStep 657833 = 493375) B493375
theorem B8129011 : Blo 435777 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B1477277 : Blo 435777 1477277 := bstep (se 3 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 1477277 = 553979) B553979
theorem B985895 : Blo 435777 985895 := bstep (se 1 (by rfl) ⟨739421, by rfl⟩ : syracuseStep 985895 = 1478843) B1478843
theorem B658217 : Blo 435777 658217 := bstep (se 2 (by rfl) ⟨246831, by rfl⟩ : syracuseStep 658217 = 493663) B493663
theorem B658427 : Blo 435777 658427 := bstep (se 1 (by rfl) ⟨493820, by rfl⟩ : syracuseStep 658427 = 987641) B987641
theorem B658487 : Blo 435777 658487 := bstep (se 1 (by rfl) ⟨493865, by rfl⟩ : syracuseStep 658487 = 987731) B987731
theorem B986219 : Blo 435777 986219 := bstep (se 1 (by rfl) ⟨739664, by rfl⟩ : syracuseStep 986219 = 1479329) B1479329
theorem B658607 : Blo 435777 658607 := bstep (se 1 (by rfl) ⟨493955, by rfl⟩ : syracuseStep 658607 = 987911) B987911
theorem B1477817 : Blo 435777 1477817 := bstep (se 2 (by rfl) ⟨554181, by rfl⟩ : syracuseStep 1477817 = 1108363) B1108363
theorem B1477979 : Blo 435777 1477979 := bstep (se 1 (by rfl) ⟨1108484, by rfl⟩ : syracuseStep 1477979 = 2216969) B2216969
theorem B986489 : Blo 435777 986489 := bstep (se 2 (by rfl) ⟨369933, by rfl⟩ : syracuseStep 986489 = 739867) B739867
theorem B986795 : Blo 435777 986795 := bstep (se 1 (by rfl) ⟨740096, by rfl⟩ : syracuseStep 986795 = 1480193) B1480193
theorem B659327 : Blo 435777 659327 := bstep (se 1 (by rfl) ⟨494495, by rfl⟩ : syracuseStep 659327 = 988991) B988991
theorem B3805073 : Blo 435777 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B987119 : Blo 435777 987119 := bstep (se 1 (by rfl) ⟨740339, by rfl⟩ : syracuseStep 987119 = 1480679) B1480679
theorem B3149873 : Blo 435777 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B987191 : Blo 435777 987191 := bstep (se 1 (by rfl) ⟨740393, by rfl⟩ : syracuseStep 987191 = 1480787) B1480787
theorem B659519 : Blo 435777 659519 := bstep (se 1 (by rfl) ⟨494639, by rfl⟩ : syracuseStep 659519 = 989279) B989279
theorem B790703 : Blo 435777 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B987335 : Blo 435777 987335 := bstep (se 1 (by rfl) ⟨740501, by rfl⟩ : syracuseStep 987335 = 1481003) B1481003
theorem B987515 : Blo 435777 987515 := bstep (se 1 (by rfl) ⟨740636, by rfl⟩ : syracuseStep 987515 = 1481273) B1481273
theorem B1774153 : Blo 435777 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1872467 : Blo 435777 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B7082599 : Blo 435777 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B987785 : Blo 435777 987785 := bstep (se 2 (by rfl) ⟨370419, by rfl⟩ : syracuseStep 987785 = 740839) B740839
theorem B15995717 : Blo 435777 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B1479869 : Blo 435777 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B1774867 : Blo 435777 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1479977 : Blo 435777 1479977 := bstep (se 2 (by rfl) ⟨554991, by rfl⟩ : syracuseStep 1479977 = 1109983) B1109983
theorem B988523 : Blo 435777 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B1775047 : Blo 435777 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B988793 : Blo 435777 988793 := bstep (se 2 (by rfl) ⟨370797, by rfl⟩ : syracuseStep 988793 = 741595) B741595
theorem B1480571 : Blo 435777 1480571 := bstep (se 1 (by rfl) ⟨1110428, by rfl⟩ : syracuseStep 1480571 = 2220857) B2220857
theorem B8427401 : Blo 435777 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B989153 : Blo 435777 989153 := bstep (se 2 (by rfl) ⟨370932, by rfl⟩ : syracuseStep 989153 = 741865) B741865
theorem B3741821 : Blo 435777 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B1480841 : Blo 435777 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B465383 : Blo 435777 465383 := bstep (se 1 (by rfl) ⟨349037, by rfl⟩ : syracuseStep 465383 = 698075) B698075
theorem B1875079 : Blo 435777 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1056233 : Blo 435777 1056233 := bstep (se 2 (by rfl) ⟨396087, by rfl⟩ : syracuseStep 1056233 = 792175) B792175
theorem B2989619 : Blo 435777 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B1188047 : Blo 435777 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B13705481 : Blo 435777 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B828463 : Blo 435777 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B12625415 : Blo 435777 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B435903 : Blo 435777 435903 := bstep (se 1 (by rfl) ⟨326927, by rfl⟩ : syracuseStep 435903 = 653855) B653855
theorem B436159 : Blo 435777 436159 := bstep (se 1 (by rfl) ⟨327119, by rfl⟩ : syracuseStep 436159 = 654239) B654239
theorem B436191 : Blo 435777 436191 := bstep (se 1 (by rfl) ⟨327143, by rfl⟩ : syracuseStep 436191 = 654287) B654287
theorem B436251 : Blo 435777 436251 := bstep (se 1 (by rfl) ⟨327188, by rfl⟩ : syracuseStep 436251 = 654377) B654377
theorem B436255 : Blo 435777 436255 := bstep (se 1 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 436255 = 654383) B654383
theorem B436271 : Blo 435777 436271 := bstep (se 1 (by rfl) ⟨327203, by rfl⟩ : syracuseStep 436271 = 654407) B654407
theorem B2795579 : Blo 435777 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B436447 : Blo 435777 436447 := bstep (se 1 (by rfl) ⟨327335, by rfl⟩ : syracuseStep 436447 = 654671) B654671
theorem B436507 : Blo 435777 436507 := bstep (se 1 (by rfl) ⟨327380, by rfl⟩ : syracuseStep 436507 = 654761) B654761
theorem B436607 : Blo 435777 436607 := bstep (se 1 (by rfl) ⟨327455, by rfl⟩ : syracuseStep 436607 = 654911) B654911
theorem B436783 : Blo 435777 436783 := bstep (se 1 (by rfl) ⟨327587, by rfl⟩ : syracuseStep 436783 = 655175) B655175
theorem B436839 : Blo 435777 436839 := bstep (se 1 (by rfl) ⟨327629, by rfl⟩ : syracuseStep 436839 = 655259) B655259
theorem B26978935 : Blo 435777 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B3779513 : Blo 435777 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B437215 : Blo 435777 437215 := bstep (se 1 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 437215 = 655823) B655823
theorem B437243 : Blo 435777 437243 := bstep (se 1 (by rfl) ⟨327932, by rfl⟩ : syracuseStep 437243 = 655865) B655865
theorem B437311 : Blo 435777 437311 := bstep (se 1 (by rfl) ⟨327983, by rfl⟩ : syracuseStep 437311 = 655967) B655967
theorem B60599501 : Blo 435777 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B437631 : Blo 435777 437631 := bstep (se 1 (by rfl) ⟨328223, by rfl⟩ : syracuseStep 437631 = 656447) B656447
theorem B437659 : Blo 435777 437659 := bstep (se 1 (by rfl) ⟨328244, by rfl⟩ : syracuseStep 437659 = 656489) B656489
theorem B437727 : Blo 435777 437727 := bstep (se 1 (by rfl) ⟨328295, by rfl⟩ : syracuseStep 437727 = 656591) B656591
theorem B437863 : Blo 435777 437863 := bstep (se 1 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 437863 = 656795) B656795
theorem B438011 : Blo 435777 438011 := bstep (se 1 (by rfl) ⟨328508, by rfl⟩ : syracuseStep 438011 = 657017) B657017
theorem B5320511 : Blo 435777 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B438079 : Blo 435777 438079 := bstep (se 1 (by rfl) ⟨328559, by rfl⟩ : syracuseStep 438079 = 657119) B657119
theorem B2502521 : Blo 435777 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B438143 : Blo 435777 438143 := bstep (se 1 (by rfl) ⟨328607, by rfl⟩ : syracuseStep 438143 = 657215) B657215
theorem B438255 : Blo 435777 438255 := bstep (se 1 (by rfl) ⟨328691, by rfl⟩ : syracuseStep 438255 = 657383) B657383
theorem B438267 : Blo 435777 438267 := bstep (se 1 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 438267 = 657401) B657401
theorem B438335 : Blo 435777 438335 := bstep (se 1 (by rfl) ⟨328751, by rfl⟩ : syracuseStep 438335 = 657503) B657503
theorem B438375 : Blo 435777 438375 := bstep (se 1 (by rfl) ⟨328781, by rfl⟩ : syracuseStep 438375 = 657563) B657563
theorem B438399 : Blo 435777 438399 := bstep (se 1 (by rfl) ⟨328799, by rfl⟩ : syracuseStep 438399 = 657599) B657599
theorem B438427 : Blo 435777 438427 := bstep (se 1 (by rfl) ⟨328820, by rfl⟩ : syracuseStep 438427 = 657641) B657641
theorem B16888013 : Blo 435777 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B831721 : Blo 435777 831721 := bstep (se 2 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 831721 = 623791) B623791
theorem B438631 : Blo 435777 438631 := bstep (se 1 (by rfl) ⟨328973, by rfl⟩ : syracuseStep 438631 = 657947) B657947
theorem B438683 : Blo 435777 438683 := bstep (se 1 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 438683 = 658025) B658025
theorem B3322295 : Blo 435777 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B31928903 : Blo 435777 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B439035 : Blo 435777 439035 := bstep (se 1 (by rfl) ⟨329276, by rfl⟩ : syracuseStep 439035 = 658553) B658553
theorem B439103 : Blo 435777 439103 := bstep (se 1 (by rfl) ⟨329327, by rfl⟩ : syracuseStep 439103 = 658655) B658655
theorem B439131 : Blo 435777 439131 := bstep (se 1 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 439131 = 658697) B658697
theorem B439199 : Blo 435777 439199 := bstep (se 1 (by rfl) ⟨329399, by rfl⟩ : syracuseStep 439199 = 658799) B658799
theorem B3552167 : Blo 435777 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B439279 : Blo 435777 439279 := bstep (se 1 (by rfl) ⟨329459, by rfl⟩ : syracuseStep 439279 = 658919) B658919
theorem B668665 : Blo 435777 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B439367 : Blo 435777 439367 := bstep (se 1 (by rfl) ⟨329525, by rfl⟩ : syracuseStep 439367 = 659051) B659051
theorem B439451 : Blo 435777 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B439547 : Blo 435777 439547 := bstep (se 1 (by rfl) ⟨329660, by rfl⟩ : syracuseStep 439547 = 659321) B659321
theorem B439615 : Blo 435777 439615 := bstep (se 1 (by rfl) ⟨329711, by rfl⟩ : syracuseStep 439615 = 659423) B659423
theorem B3749611 : Blo 435777 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B2111447 : Blo 435777 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B3651655 : Blo 435777 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B2799755 : Blo 435777 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B5585051 : Blo 435777 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B735979 : Blo 435777 735979 := bstep (se 1 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 735979 = 1103969) B1103969
theorem B2210651 : Blo 435777 2210651 := bstep (se 1 (by rfl) ⟨1657988, by rfl⟩ : syracuseStep 2210651 = 3315977) B3315977
theorem B933371 : Blo 435777 933371 := bstep (se 1 (by rfl) ⟨700028, by rfl⟩ : syracuseStep 933371 = 1400057) B1400057
theorem B933439 : Blo 435777 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B3030635 : Blo 435777 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B3554923 : Blo 435777 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B8077219 : Blo 435777 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B1654739 : Blo 435777 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B737471 : Blo 435777 737471 := bstep (se 1 (by rfl) ⟨553103, by rfl⟩ : syracuseStep 737471 = 1106207) B1106207
theorem B934183 : Blo 435777 934183 := bstep (se 1 (by rfl) ⟨700637, by rfl⟩ : syracuseStep 934183 = 1401275) B1401275
theorem B2834785 : Blo 435777 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B737707 : Blo 435777 737707 := bstep (se 1 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 737707 = 1106561) B1106561
theorem B14434735 : Blo 435777 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B3424787 : Blo 435777 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B737903 : Blo 435777 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B738247 : Blo 435777 738247 := bstep (se 1 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 738247 = 1107371) B1107371
theorem B2245619 : Blo 435777 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B2212919 : Blo 435777 2212919 := bstep (se 1 (by rfl) ⟨1659689, by rfl⟩ : syracuseStep 2212919 = 3319379) B3319379
theorem B200263043 : Blo 435777 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B4965947 : Blo 435777 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B739111 : Blo 435777 739111 := bstep (se 1 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 739111 = 1108667) B1108667
theorem B3753985 : Blo 435777 3753985 := bstep (se 2 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 3753985 = 2815489) B2815489
theorem B740137 : Blo 435777 740137 := bstep (se 2 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 740137 = 555103) B555103
theorem B1657655 : Blo 435777 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B4967405 : Blo 435777 4967405 := bstep (se 3 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 4967405 = 1862777) B1862777
theorem B740407 : Blo 435777 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B937327 : Blo 435777 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B7982459 : Blo 435777 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B2018849 : Blo 435777 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B2215835 : Blo 435777 2215835 := bstep (se 1 (by rfl) ⟨1661876, by rfl⟩ : syracuseStep 2215835 = 3323753) B3323753
theorem B3755969 : Blo 435777 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B1658839 : Blo 435777 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B11980781 : Blo 435777 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B741359 : Blo 435777 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B938633 : Blo 435777 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B5592023 : Blo 435777 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B3724325 : Blo 435777 3724325 := bstep (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) B698311
theorem B939215 : Blo 435777 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B1660297 : Blo 435777 1660297 := bstep (se 2 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 1660297 = 1245223) B1245223
theorem B13981081 : Blo 435777 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B2217455 : Blo 435777 2217455 := bstep (se 1 (by rfl) ⟨1663091, by rfl⟩ : syracuseStep 2217455 = 3326183) B3326183
theorem B4970321 : Blo 435777 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B1923041 : Blo 435777 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B3725351 : Blo 435777 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B163371919 : Blo 435777 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B1465847 : Blo 435777 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B4054607 : Blo 435777 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B15621983 : Blo 435777 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B1204079 : Blo 435777 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B1106743 : Blo 435777 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B1107017 : Blo 435777 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B3335417 : Blo 435777 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B3565691 : Blo 435777 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B1108201 : Blo 435777 1108201 := bstep (se 2 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 1108201 = 831151) B831151
theorem B846217 : Blo 435777 846217 := bstep (se 2 (by rfl) ⟨317331, by rfl⟩ : syracuseStep 846217 = 634663) B634663
theorem B2222639 : Blo 435777 2222639 := bstep (se 1 (by rfl) ⟨1666979, by rfl⟩ : syracuseStep 2222639 = 3333959) B3333959
theorem B10644047 : Blo 435777 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B2223287 : Blo 435777 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B552415 : Blo 435777 552415 := bstep (se 1 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 552415 = 828623) B828623
theorem B4976153 : Blo 435777 4976153 := bstep (se 2 (by rfl) ⟨1866057, by rfl⟩ : syracuseStep 4976153 = 3732115) B3732115
theorem B2223773 : Blo 435777 2223773 := bstep (se 3 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 2223773 = 833915) B833915
theorem B1241351 : Blo 435777 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B1602283 : Blo 435777 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1110793 : Blo 435777 1110793 := bstep (se 2 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 1110793 = 833095) B833095
theorem B554303 : Blo 435777 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B2848063 : Blo 435777 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B1242535 : Blo 435777 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B1668833 : Blo 435777 1668833 := bstep (se 2 (by rfl) ⟨625812, by rfl⟩ : syracuseStep 1668833 = 1251625) B1251625
theorem B4224737 : Blo 435777 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B981287 : Blo 435777 981287 := bstep (se 1 (by rfl) ⟨735965, by rfl⟩ : syracuseStep 981287 = 1471931) B1471931
theorem B1866179 : Blo 435777 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1473065 : Blo 435777 1473065 := bstep (se 2 (by rfl) ⟨552399, by rfl⟩ : syracuseStep 1473065 = 1104799) B1104799
theorem B653915 : Blo 435777 653915 := bstep (se 1 (by rfl) ⟨490436, by rfl⟩ : syracuseStep 653915 = 980873) B980873
theorem B1866331 : Blo 435777 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B981647 : Blo 435777 981647 := bstep (se 1 (by rfl) ⟨736235, by rfl⟩ : syracuseStep 981647 = 1472471) B1472471
theorem B981737 : Blo 435777 981737 := bstep (se 2 (by rfl) ⟨368151, by rfl⟩ : syracuseStep 981737 = 736303) B736303
theorem B654059 : Blo 435777 654059 := bstep (se 1 (by rfl) ⟨490544, by rfl⟩ : syracuseStep 654059 = 981089) B981089
theorem B72940277 : Blo 435777 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B654089 : Blo 435777 654089 := bstep (se 2 (by rfl) ⟨245283, by rfl⟩ : syracuseStep 654089 = 490567) B490567
theorem B2653037 : Blo 435777 2653037 := bstep (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) B994889
theorem B490351 : Blo 435777 490351 := bstep (se 1 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 490351 = 735527) B735527
theorem B981971 : Blo 435777 981971 := bstep (se 1 (by rfl) ⟨736478, by rfl⟩ : syracuseStep 981971 = 1472957) B1472957
theorem B1047775 : Blo 435777 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B982241 : Blo 435777 982241 := bstep (se 2 (by rfl) ⟨368340, by rfl⟩ : syracuseStep 982241 = 736681) B736681
theorem B982547 : Blo 435777 982547 := bstep (se 1 (by rfl) ⟨736910, by rfl⟩ : syracuseStep 982547 = 1473821) B1473821
theorem B654959 : Blo 435777 654959 := bstep (se 1 (by rfl) ⟨491219, by rfl⟩ : syracuseStep 654959 = 982439) B982439
theorem B5996207 : Blo 435777 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B1048295 : Blo 435777 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B655079 : Blo 435777 655079 := bstep (se 1 (by rfl) ⟨491309, by rfl⟩ : syracuseStep 655079 = 982619) B982619
theorem B491431 : Blo 435777 491431 := bstep (se 1 (by rfl) ⟨368573, by rfl⟩ : syracuseStep 491431 = 737147) B737147
theorem B655271 : Blo 435777 655271 := bstep (se 1 (by rfl) ⟨491453, by rfl⟩ : syracuseStep 655271 = 982907) B982907
theorem B655487 : Blo 435777 655487 := bstep (se 1 (by rfl) ⟨491615, by rfl⟩ : syracuseStep 655487 = 983231) B983231
theorem B491647 : Blo 435777 491647 := bstep (se 1 (by rfl) ⟨368735, by rfl⟩ : syracuseStep 491647 = 737471) B737471
theorem B1048889 : Blo 435777 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B1245577 : Blo 435777 1245577 := bstep (se 2 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 1245577 = 934183) B934183
theorem B655775 : Blo 435777 655775 := bstep (se 1 (by rfl) ⟨491831, by rfl⟩ : syracuseStep 655775 = 983663) B983663
theorem B491935 : Blo 435777 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B2490857 : Blo 435777 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B983609 : Blo 435777 983609 := bstep (se 2 (by rfl) ⟨368853, by rfl⟩ : syracuseStep 983609 = 737707) B737707
theorem B656039 : Blo 435777 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B1475279 : Blo 435777 1475279 := bstep (se 1 (by rfl) ⟨1106459, by rfl⟩ : syracuseStep 1475279 = 2212919) B2212919
theorem B656159 : Blo 435777 656159 := bstep (se 1 (by rfl) ⟨492119, by rfl⟩ : syracuseStep 656159 = 984239) B984239
theorem B1180457 : Blo 435777 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B656183 : Blo 435777 656183 := bstep (se 1 (by rfl) ⟨492137, by rfl⟩ : syracuseStep 656183 = 984275) B984275
theorem B656363 : Blo 435777 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B3310631 : Blo 435777 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B1475657 : Blo 435777 1475657 := bstep (se 2 (by rfl) ⟨553371, by rfl⟩ : syracuseStep 1475657 = 1106743) B1106743
theorem B984329 : Blo 435777 984329 := bstep (se 2 (by rfl) ⟨369123, by rfl⟩ : syracuseStep 984329 = 738247) B738247
theorem B656873 : Blo 435777 656873 := bstep (se 2 (by rfl) ⟨246327, by rfl⟩ : syracuseStep 656873 = 492655) B492655
theorem B1574633 : Blo 435777 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B984851 : Blo 435777 984851 := bstep (se 1 (by rfl) ⟨738638, by rfl⟩ : syracuseStep 984851 = 1477277) B1477277
theorem B657263 : Blo 435777 657263 := bstep (se 1 (by rfl) ⟨492947, by rfl⟩ : syracuseStep 657263 = 985895) B985895
theorem B3311603 : Blo 435777 3311603 := bstep (se 1 (by rfl) ⟨2483702, by rfl⟩ : syracuseStep 3311603 = 4967405) B4967405
theorem B657449 : Blo 435777 657449 := bstep (se 2 (by rfl) ⟨246543, by rfl⟩ : syracuseStep 657449 = 493087) B493087
theorem B657479 : Blo 435777 657479 := bstep (se 1 (by rfl) ⟨493109, by rfl⟩ : syracuseStep 657479 = 986219) B986219
theorem B985211 : Blo 435777 985211 := bstep (se 1 (by rfl) ⟨738908, by rfl⟩ : syracuseStep 985211 = 1477817) B1477817
theorem B985319 : Blo 435777 985319 := bstep (se 1 (by rfl) ⟨738989, by rfl⟩ : syracuseStep 985319 = 1477979) B1477979
theorem B657659 : Blo 435777 657659 := bstep (se 1 (by rfl) ⟨493244, by rfl⟩ : syracuseStep 657659 = 986489) B986489
theorem B985481 : Blo 435777 985481 := bstep (se 2 (by rfl) ⟨369555, by rfl⟩ : syracuseStep 985481 = 739111) B739111
theorem B657863 : Blo 435777 657863 := bstep (se 1 (by rfl) ⟨493397, by rfl⟩ : syracuseStep 657863 = 986795) B986795
theorem B1477223 : Blo 435777 1477223 := bstep (se 1 (by rfl) ⟨1107917, by rfl⟩ : syracuseStep 1477223 = 2215835) B2215835
theorem B658079 : Blo 435777 658079 := bstep (se 1 (by rfl) ⟨493559, by rfl⟩ : syracuseStep 658079 = 987119) B987119
theorem B494239 : Blo 435777 494239 := bstep (se 1 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 494239 = 741359) B741359
theorem B2099915 : Blo 435777 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B658127 : Blo 435777 658127 := bstep (se 1 (by rfl) ⟨493595, by rfl⟩ : syracuseStep 658127 = 987191) B987191
theorem B658223 : Blo 435777 658223 := bstep (se 1 (by rfl) ⟨493667, by rfl⟩ : syracuseStep 658223 = 987335) B987335
theorem B658343 : Blo 435777 658343 := bstep (se 1 (by rfl) ⟨493757, by rfl⟩ : syracuseStep 658343 = 987515) B987515
theorem B1477601 : Blo 435777 1477601 := bstep (se 2 (by rfl) ⟨554100, by rfl⟩ : syracuseStep 1477601 = 1108201) B1108201
theorem B1248311 : Blo 435777 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B658523 : Blo 435777 658523 := bstep (se 1 (by rfl) ⟨493892, by rfl⟩ : syracuseStep 658523 = 987785) B987785
theorem B658601 : Blo 435777 658601 := bstep (se 2 (by rfl) ⟨246975, by rfl⟩ : syracuseStep 658601 = 493951) B493951
theorem B986579 : Blo 435777 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B626143 : Blo 435777 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B1478141 : Blo 435777 1478141 := bstep (se 3 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 1478141 = 554303) B554303
theorem B986651 : Blo 435777 986651 := bstep (se 1 (by rfl) ⟨739988, by rfl⟩ : syracuseStep 986651 = 1479977) B1479977
theorem B659015 : Blo 435777 659015 := bstep (se 1 (by rfl) ⟨494261, by rfl⟩ : syracuseStep 659015 = 988523) B988523
theorem B1478303 : Blo 435777 1478303 := bstep (se 1 (by rfl) ⟨1108727, by rfl⟩ : syracuseStep 1478303 = 2217455) B2217455
theorem B986849 : Blo 435777 986849 := bstep (se 2 (by rfl) ⟨370068, by rfl⟩ : syracuseStep 986849 = 740137) B740137
theorem B659195 : Blo 435777 659195 := bstep (se 1 (by rfl) ⟨494396, by rfl⟩ : syracuseStep 659195 = 988793) B988793
theorem B3313547 : Blo 435777 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B987047 : Blo 435777 987047 := bstep (se 1 (by rfl) ⟨740285, by rfl⟩ : syracuseStep 987047 = 1480571) B1480571
theorem B1282027 : Blo 435777 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B659435 : Blo 435777 659435 := bstep (se 1 (by rfl) ⟨494576, by rfl⟩ : syracuseStep 659435 = 989153) B989153
theorem B987209 : Blo 435777 987209 := bstep (se 2 (by rfl) ⟨370203, by rfl⟩ : syracuseStep 987209 = 740407) B740407
theorem B2494547 : Blo 435777 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B987227 : Blo 435777 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B1249769 : Blo 435777 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B792031 : Blo 435777 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B2365537 : Blo 435777 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B9443465 : Blo 435777 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B2136377 : Blo 435777 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1481057 : Blo 435777 1481057 := bstep (se 2 (by rfl) ⟨555396, by rfl⟩ : syracuseStep 1481057 = 1110793) B1110793
theorem B2366489 : Blo 435777 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B1481759 : Blo 435777 1481759 := bstep (se 1 (by rfl) ⟨1111319, by rfl⟩ : syracuseStep 1481759 = 2222639) B2222639
theorem B2366729 : Blo 435777 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B1482191 : Blo 435777 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B3317435 : Blo 435777 3317435 := bstep (se 1 (by rfl) ⟨2488076, by rfl⟩ : syracuseStep 3317435 = 4976153) B4976153
theorem B1482515 : Blo 435777 1482515 := bstep (se 1 (by rfl) ⟨1111886, by rfl⟩ : syracuseStep 1482515 = 2223773) B2223773
theorem B3547007 : Blo 435777 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B827567 : Blo 435777 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B2368111 : Blo 435777 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B5383597 : Blo 435777 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B2500105 : Blo 435777 2500105 := bstep (se 2 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 2500105 = 1875079) B1875079
theorem B435943 : Blo 435777 435943 := bstep (se 1 (by rfl) ⟨326957, by rfl⟩ : syracuseStep 435943 = 653915) B653915
theorem B436039 : Blo 435777 436039 := bstep (se 1 (by rfl) ⟨327029, by rfl⟩ : syracuseStep 436039 = 654059) B654059
theorem B436059 : Blo 435777 436059 := bstep (se 1 (by rfl) ⟨327044, by rfl⟩ : syracuseStep 436059 = 654089) B654089
theorem B436639 : Blo 435777 436639 := bstep (se 1 (by rfl) ⟨327479, by rfl⟩ : syracuseStep 436639 = 654959) B654959
theorem B698863 : Blo 435777 698863 := bstep (se 1 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 698863 = 1048295) B1048295
theorem B436719 : Blo 435777 436719 := bstep (se 1 (by rfl) ⟨327539, by rfl⟩ : syracuseStep 436719 = 655079) B655079
theorem B436847 : Blo 435777 436847 := bstep (se 1 (by rfl) ⟨327635, by rfl⟩ : syracuseStep 436847 = 655271) B655271
theorem B437063 : Blo 435777 437063 := bstep (se 1 (by rfl) ⟨327797, by rfl⟩ : syracuseStep 437063 = 655595) B655595
theorem B437103 : Blo 435777 437103 := bstep (se 1 (by rfl) ⟨327827, by rfl⟩ : syracuseStep 437103 = 655655) B655655
theorem B830407 : Blo 435777 830407 := bstep (se 1 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 830407 = 1245611) B1245611
theorem B3779713 : Blo 435777 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B19246313 : Blo 435777 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B437551 : Blo 435777 437551 := bstep (se 1 (by rfl) ⟨328163, by rfl⟩ : syracuseStep 437551 = 656327) B656327
theorem B36547949 : Blo 435777 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B437663 : Blo 435777 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B437791 : Blo 435777 437791 := bstep (se 1 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 437791 = 656687) B656687
theorem B437927 : Blo 435777 437927 := bstep (se 1 (by rfl) ⟨328445, by rfl⟩ : syracuseStep 437927 = 656891) B656891
theorem B437951 : Blo 435777 437951 := bstep (se 1 (by rfl) ⟨328463, by rfl⟩ : syracuseStep 437951 = 656927) B656927
theorem B438047 : Blo 435777 438047 := bstep (se 1 (by rfl) ⟨328535, by rfl⟩ : syracuseStep 438047 = 657071) B657071
theorem B438127 : Blo 435777 438127 := bstep (se 1 (by rfl) ⟨328595, by rfl⟩ : syracuseStep 438127 = 657191) B657191
theorem B438495 : Blo 435777 438495 := bstep (se 1 (by rfl) ⟨328871, by rfl⟩ : syracuseStep 438495 = 657743) B657743
theorem B438527 : Blo 435777 438527 := bstep (se 1 (by rfl) ⟨328895, by rfl⟩ : syracuseStep 438527 = 657791) B657791
theorem B438555 : Blo 435777 438555 := bstep (se 1 (by rfl) ⟨328916, by rfl⟩ : syracuseStep 438555 = 657833) B657833
theorem B2503021 : Blo 435777 2503021 := bstep (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) B938633
theorem B8434165 : Blo 435777 8434165 := bstep (se 5 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 8434165 = 790703) B790703
theorem B438811 : Blo 435777 438811 := bstep (se 1 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 438811 = 658217) B658217
theorem B438951 : Blo 435777 438951 := bstep (se 1 (by rfl) ⟨329213, by rfl⟩ : syracuseStep 438951 = 658427) B658427
theorem B438991 : Blo 435777 438991 := bstep (se 1 (by rfl) ⟨329243, by rfl⟩ : syracuseStep 438991 = 658487) B658487
theorem B439071 : Blo 435777 439071 := bstep (se 1 (by rfl) ⟨329303, by rfl⟩ : syracuseStep 439071 = 658607) B658607
theorem B5321639 : Blo 435777 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B439551 : Blo 435777 439551 := bstep (se 1 (by rfl) ⟨329663, by rfl⟩ : syracuseStep 439551 = 659327) B659327
theorem B2536715 : Blo 435777 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B2503979 : Blo 435777 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B439679 : Blo 435777 439679 := bstep (se 1 (by rfl) ⟨329759, by rfl⟩ : syracuseStep 439679 = 659519) B659519
theorem B10663811 : Blo 435777 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B534034781 : Blo 435777 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B5618267 : Blo 435777 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B736553 : Blo 435777 736553 := bstep (se 2 (by rfl) ⟨276207, by rfl⟩ : syracuseStep 736553 = 552415) B552415
theorem B704155 : Blo 435777 704155 := bstep (se 1 (by rfl) ⟨528116, by rfl⟩ : syracuseStep 704155 = 1056233) B1056233
theorem B2703071 : Blo 435777 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B2211785 : Blo 435777 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B738011 : Blo 435777 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B2377127 : Blo 435777 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B7096031 : Blo 435777 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B2213729 : Blo 435777 2213729 := bstep (se 2 (by rfl) ⟨830148, by rfl⟩ : syracuseStep 2213729 = 1660297) B1660297
theorem B1656713 : Blo 435777 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B4999481 : Blo 435777 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B4868873 : Blo 435777 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B11258675 : Blo 435777 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B2214863 : Blo 435777 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B21285935 : Blo 435777 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B217829225 : Blo 435777 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B3723367 : Blo 435777 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B1397033 : Blo 435777 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B4739897 : Blo 435777 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B43078501 : Blo 435777 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B2020423 : Blo 435777 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B1103159 : Blo 435777 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B3364487 : Blo 435777 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2283191 : Blo 435777 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B1497079 : Blo 435777 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B1104617 : Blo 435777 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B1105103 : Blo 435777 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B4513157 : Blo 435777 4513157 := bstep (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) B846217
theorem B7987187 : Blo 435777 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B5005313 : Blo 435777 5005313 := bstep (se 2 (by rfl) ⟨1876992, by rfl⟩ : syracuseStep 5005313 = 3753985) B3753985
theorem B1007657 : Blo 435777 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B3728015 : Blo 435777 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B10838681 : Blo 435777 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B2482883 : Blo 435777 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B35971913 : Blo 435777 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B2483567 : Blo 435777 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B977231 : Blo 435777 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1993079 : Blo 435777 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B10414655 : Blo 435777 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B3566213 : Blo 435777 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B1108961 : Blo 435777 1108961 := bstep (se 2 (by rfl) ⟨415860, by rfl⟩ : syracuseStep 1108961 = 831721) B831721
theorem B1404157 : Blo 435777 1404157 := bstep (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) B526559
theorem B2223611 : Blo 435777 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B8416943 : Blo 435777 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B1241021 : Blo 435777 1241021 := bstep (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) B465383
theorem B1863719 : Blo 435777 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B3797417 : Blo 435777 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B18641441 : Blo 435777 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2519675 : Blo 435777 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B40399667 : Blo 435777 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B1668347 : Blo 435777 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B2488441 : Blo 435777 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B981305 : Blo 435777 981305 := bstep (se 2 (by rfl) ⟨367989, by rfl⟩ : syracuseStep 981305 = 735979) B735979
theorem B653801 : Blo 435777 653801 := bstep (se 2 (by rfl) ⟨245175, by rfl⟩ : syracuseStep 653801 = 490351) B490351
theorem B1112555 : Blo 435777 1112555 := bstep (se 1 (by rfl) ⟨834416, by rfl⟩ : syracuseStep 1112555 = 1668833) B1668833
theorem B2816491 : Blo 435777 2816491 := bstep (se 1 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 2816491 = 4224737) B4224737
theorem B1407631 : Blo 435777 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B1866503 : Blo 435777 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B654191 : Blo 435777 654191 := bstep (se 1 (by rfl) ⟨490643, by rfl⟩ : syracuseStep 654191 = 981287) B981287
theorem B1244119 : Blo 435777 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B982043 : Blo 435777 982043 := bstep (se 1 (by rfl) ⟨736532, by rfl⟩ : syracuseStep 982043 = 1473065) B1473065
theorem B654431 : Blo 435777 654431 := bstep (se 1 (by rfl) ⟨490823, by rfl⟩ : syracuseStep 654431 = 981647) B981647
theorem B654491 : Blo 435777 654491 := bstep (se 1 (by rfl) ⟨490868, by rfl⟩ : syracuseStep 654491 = 981737) B981737
theorem B48626851 : Blo 435777 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B1473767 : Blo 435777 1473767 := bstep (se 1 (by rfl) ⟨1105325, by rfl⟩ : syracuseStep 1473767 = 2210651) B2210651
theorem B1768691 : Blo 435777 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B654647 : Blo 435777 654647 := bstep (se 1 (by rfl) ⟨490985, by rfl⟩ : syracuseStep 654647 = 981971) B981971
theorem B1244585 : Blo 435777 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B654827 : Blo 435777 654827 := bstep (se 1 (by rfl) ⟨491120, by rfl⟩ : syracuseStep 654827 = 982241) B982241
theorem B3210877 : Blo 435777 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B622247 : Blo 435777 622247 := bstep (se 1 (by rfl) ⟨466685, by rfl⟩ : syracuseStep 622247 = 933371) B933371
theorem B655031 : Blo 435777 655031 := bstep (se 1 (by rfl) ⟨491273, by rfl⟩ : syracuseStep 655031 = 982547) B982547
theorem B3997471 : Blo 435777 3997471 := bstep (se 1 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 3997471 = 5996207) B5996207
theorem B655241 : Blo 435777 655241 := bstep (se 2 (by rfl) ⟨245715, by rfl⟩ : syracuseStep 655241 = 491431) B491431
theorem B655529 : Blo 435777 655529 := bstep (se 2 (by rfl) ⟨245823, by rfl⟩ : syracuseStep 655529 = 491647) B491647
theorem B655739 : Blo 435777 655739 := bstep (se 1 (by rfl) ⟨491804, by rfl⟩ : syracuseStep 655739 = 983609) B983609
theorem B983519 : Blo 435777 983519 := bstep (se 1 (by rfl) ⟨737639, by rfl⟩ : syracuseStep 983519 = 1475279) B1475279
theorem B492007 : Blo 435777 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B786971 : Blo 435777 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B655913 : Blo 435777 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B983771 : Blo 435777 983771 := bstep (se 1 (by rfl) ⟨737828, by rfl⟩ : syracuseStep 983771 = 1475657) B1475657
theorem B656219 : Blo 435777 656219 := bstep (se 1 (by rfl) ⟨492164, by rfl⟩ : syracuseStep 656219 = 984329) B984329
theorem B1049755 : Blo 435777 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B656567 : Blo 435777 656567 := bstep (se 1 (by rfl) ⟨492425, by rfl⟩ : syracuseStep 656567 = 984851) B984851
theorem B1475819 : Blo 435777 1475819 := bstep (se 1 (by rfl) ⟨1106864, by rfl⟩ : syracuseStep 1475819 = 2213729) B2213729
theorem B656807 : Blo 435777 656807 := bstep (se 1 (by rfl) ⟨492605, by rfl⟩ : syracuseStep 656807 = 985211) B985211
theorem B656879 : Blo 435777 656879 := bstep (se 1 (by rfl) ⟨492659, by rfl⟩ : syracuseStep 656879 = 985319) B985319
theorem B656987 : Blo 435777 656987 := bstep (se 1 (by rfl) ⟨492740, by rfl⟩ : syracuseStep 656987 = 985481) B985481
theorem B984815 : Blo 435777 984815 := bstep (se 1 (by rfl) ⟨738611, by rfl⟩ : syracuseStep 984815 = 1477223) B1477223
theorem B3245915 : Blo 435777 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B7505783 : Blo 435777 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B7178129 : Blo 435777 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1476575 : Blo 435777 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B985067 : Blo 435777 985067 := bstep (se 1 (by rfl) ⟨738800, by rfl⟩ : syracuseStep 985067 = 1477601) B1477601
theorem B14190623 : Blo 435777 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B657719 : Blo 435777 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B985427 : Blo 435777 985427 := bstep (se 1 (by rfl) ⟨739070, by rfl⟩ : syracuseStep 985427 = 1478141) B1478141
theorem B657767 : Blo 435777 657767 := bstep (se 1 (by rfl) ⟨493325, by rfl⟩ : syracuseStep 657767 = 986651) B986651
theorem B985535 : Blo 435777 985535 := bstep (se 1 (by rfl) ⟨739151, by rfl⟩ : syracuseStep 985535 = 1478303) B1478303
theorem B657899 : Blo 435777 657899 := bstep (se 1 (by rfl) ⟨493424, by rfl⟩ : syracuseStep 657899 = 986849) B986849
theorem B658031 : Blo 435777 658031 := bstep (se 1 (by rfl) ⟨493523, by rfl⟩ : syracuseStep 658031 = 987047) B987047
theorem B658139 : Blo 435777 658139 := bstep (se 1 (by rfl) ⟨493604, by rfl⟩ : syracuseStep 658139 = 987209) B987209
theorem B658151 : Blo 435777 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B658985 : Blo 435777 658985 := bstep (se 2 (by rfl) ⟨247119, by rfl⟩ : syracuseStep 658985 = 494239) B494239
theorem B6295643 : Blo 435777 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B987371 : Blo 435777 987371 := bstep (se 1 (by rfl) ⟨740528, by rfl⟩ : syracuseStep 987371 = 1481057) B1481057
theorem B1872209 : Blo 435777 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B1577659 : Blo 435777 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B987839 : Blo 435777 987839 := bstep (se 1 (by rfl) ⟨740879, by rfl⟩ : syracuseStep 987839 = 1481759) B1481759
theorem B1577819 : Blo 435777 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B988127 : Blo 435777 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B988343 : Blo 435777 988343 := bstep (se 1 (by rfl) ⟨741257, by rfl⟩ : syracuseStep 988343 = 1482515) B1482515
theorem B2364671 : Blo 435777 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B1709369 : Blo 435777 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B11245553 : Blo 435777 11245553 := bstep (se 2 (by rfl) ⟨4217082, by rfl⟩ : syracuseStep 11245553 = 8434165) B8434165
theorem B20158469 : Blo 435777 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B2693897 : Blo 435777 2693897 := bstep (se 2 (by rfl) ⟨1010211, by rfl⟩ : syracuseStep 2693897 = 2020423) B2020423
theorem B1056041 : Blo 435777 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B1482407 : Blo 435777 1482407 := bstep (se 1 (by rfl) ⟨1111805, by rfl⟩ : syracuseStep 1482407 = 2223611) B2223611
theorem B5611295 : Blo 435777 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B827347 : Blo 435777 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B3154049 : Blo 435777 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B3317921 : Blo 435777 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B2531611 : Blo 435777 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B12427627 : Blo 435777 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B1679783 : Blo 435777 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B3547759 : Blo 435777 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B1876841 : Blo 435777 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B3318893 : Blo 435777 3318893 := bstep (se 3 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 3318893 = 1244585) B1244585
theorem B435867 : Blo 435777 435867 := bstep (se 1 (by rfl) ⟨326900, by rfl⟩ : syracuseStep 435867 = 653801) B653801
theorem B3745511 : Blo 435777 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B436127 : Blo 435777 436127 := bstep (se 1 (by rfl) ⟨327095, by rfl⟩ : syracuseStep 436127 = 654191) B654191
theorem B436287 : Blo 435777 436287 := bstep (se 1 (by rfl) ⟨327215, by rfl⟩ : syracuseStep 436287 = 654431) B654431
theorem B436327 : Blo 435777 436327 := bstep (se 1 (by rfl) ⟨327245, by rfl⟩ : syracuseStep 436327 = 654491) B654491
theorem B436431 : Blo 435777 436431 := bstep (se 1 (by rfl) ⟨327323, by rfl⟩ : syracuseStep 436431 = 654647) B654647
theorem B436551 : Blo 435777 436551 := bstep (se 1 (by rfl) ⟨327413, by rfl⟩ : syracuseStep 436551 = 654827) B654827
theorem B436687 : Blo 435777 436687 := bstep (se 1 (by rfl) ⟨327515, by rfl⟩ : syracuseStep 436687 = 655031) B655031
theorem B436827 : Blo 435777 436827 := bstep (se 1 (by rfl) ⟨327620, by rfl⟩ : syracuseStep 436827 = 655241) B655241
theorem B436991 : Blo 435777 436991 := bstep (se 1 (by rfl) ⟨327743, by rfl⟩ : syracuseStep 436991 = 655487) B655487
theorem B437183 : Blo 435777 437183 := bstep (se 1 (by rfl) ⟨327887, by rfl⟩ : syracuseStep 437183 = 655775) B655775
theorem B437359 : Blo 435777 437359 := bstep (se 1 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 437359 = 656039) B656039
theorem B437439 : Blo 435777 437439 := bstep (se 1 (by rfl) ⟨328079, by rfl⟩ : syracuseStep 437439 = 656159) B656159
theorem B437455 : Blo 435777 437455 := bstep (se 1 (by rfl) ⟨328091, by rfl⟩ : syracuseStep 437455 = 656183) B656183
theorem B437575 : Blo 435777 437575 := bstep (se 1 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 437575 = 656363) B656363
theorem B2207087 : Blo 435777 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B3157481 : Blo 435777 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B2797037 : Blo 435777 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B437915 : Blo 435777 437915 := bstep (se 1 (by rfl) ⟨328436, by rfl⟩ : syracuseStep 437915 = 656873) B656873
theorem B4730687 : Blo 435777 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B438175 : Blo 435777 438175 := bstep (se 1 (by rfl) ⟨328631, by rfl⟩ : syracuseStep 438175 = 657263) B657263
theorem B2207735 : Blo 435777 2207735 := bstep (se 1 (by rfl) ⟨1655801, by rfl⟩ : syracuseStep 2207735 = 3311603) B3311603
theorem B438299 : Blo 435777 438299 := bstep (se 1 (by rfl) ⟨328724, by rfl⟩ : syracuseStep 438299 = 657449) B657449
theorem B438319 : Blo 435777 438319 := bstep (se 1 (by rfl) ⟨328739, by rfl⟩ : syracuseStep 438319 = 657479) B657479
theorem B438439 : Blo 435777 438439 := bstep (se 1 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 438439 = 657659) B657659
theorem B438575 : Blo 435777 438575 := bstep (se 1 (by rfl) ⟨328931, by rfl⟩ : syracuseStep 438575 = 657863) B657863
theorem B438719 : Blo 435777 438719 := bstep (se 1 (by rfl) ⟨329039, by rfl⟩ : syracuseStep 438719 = 658079) B658079
theorem B438751 : Blo 435777 438751 := bstep (se 1 (by rfl) ⟨329063, by rfl⟩ : syracuseStep 438751 = 658127) B658127
theorem B438815 : Blo 435777 438815 := bstep (se 1 (by rfl) ⟨329111, by rfl⟩ : syracuseStep 438815 = 658223) B658223
theorem B438895 : Blo 435777 438895 := bstep (se 1 (by rfl) ⟨329171, by rfl⟩ : syracuseStep 438895 = 658343) B658343
theorem B832207 : Blo 435777 832207 := bstep (se 1 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 832207 = 1248311) B1248311
theorem B439015 : Blo 435777 439015 := bstep (se 1 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 439015 = 658523) B658523
theorem B439067 : Blo 435777 439067 := bstep (se 1 (by rfl) ⟨329300, by rfl⟩ : syracuseStep 439067 = 658601) B658601
theorem B439343 : Blo 435777 439343 := bstep (se 1 (by rfl) ⟨329507, by rfl⟩ : syracuseStep 439343 = 659015) B659015
theorem B439463 : Blo 435777 439463 := bstep (se 1 (by rfl) ⟨329597, by rfl⟩ : syracuseStep 439463 = 659195) B659195
theorem B2209031 : Blo 435777 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B439623 : Blo 435777 439623 := bstep (se 1 (by rfl) ⟨329717, by rfl⟩ : syracuseStep 439623 = 659435) B659435
theorem B931355 : Blo 435777 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B833179 : Blo 435777 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B3159931 : Blo 435777 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B931817 : Blo 435777 931817 := bstep (se 2 (by rfl) ⟨349431, by rfl⟩ : syracuseStep 931817 = 698863) B698863
theorem B6764573 : Blo 435777 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B735439 : Blo 435777 735439 := bstep (se 1 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 735439 = 1103159) B1103159
theorem B2242991 : Blo 435777 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B6339005 : Blo 435777 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B1522127 : Blo 435777 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B1424251 : Blo 435777 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B736411 : Blo 435777 736411 := bstep (se 1 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 736411 = 1104617) B1104617
theorem B834857 : Blo 435777 834857 := bstep (se 2 (by rfl) ⟨313071, by rfl⟩ : syracuseStep 834857 = 626143) B626143
theorem B736735 : Blo 435777 736735 := bstep (se 1 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 736735 = 1105103) B1105103
theorem B2211623 : Blo 435777 2211623 := bstep (se 1 (by rfl) ⟨1658717, by rfl⟩ : syracuseStep 2211623 = 3317435) B3317435
theorem B5324791 : Blo 435777 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B671771 : Blo 435777 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B4964489 : Blo 435777 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B7225787 : Blo 435777 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B1655255 : Blo 435777 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B1655711 : Blo 435777 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B1328719 : Blo 435777 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B2377475 : Blo 435777 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B739307 : Blo 435777 739307 := bstep (se 1 (by rfl) ⟨554480, by rfl⟩ : syracuseStep 739307 = 1108961) B1108961
theorem B12830875 : Blo 435777 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B24365299 : Blo 435777 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B3755321 : Blo 435777 3755321 := bstep (se 2 (by rfl) ⟨1408245, by rfl⟩ : syracuseStep 3755321 = 2816491) B2816491
theorem B1658825 : Blo 435777 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B64835801 : Blo 435777 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B741703 : Blo 435777 741703 := bstep (se 1 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 741703 = 1112555) B1112555
theorem B1659325 : Blo 435777 1659325 := bstep (se 3 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 1659325 = 622247) B622247
theorem B4281169 : Blo 435777 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B938873 : Blo 435777 938873 := bstep (se 2 (by rfl) ⟨352077, by rfl⟩ : syracuseStep 938873 = 704155) B704155
theorem B5329961 : Blo 435777 5329961 := bstep (se 2 (by rfl) ⟨1998735, by rfl⟩ : syracuseStep 5329961 = 3997471) B3997471
theorem B1660571 : Blo 435777 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B1660769 : Blo 435777 1660769 := bstep (se 2 (by rfl) ⟨622788, by rfl⟩ : syracuseStep 1660769 = 1245577) B1245577
theorem B1104475 : Blo 435777 1104475 := bstep (se 1 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 1104475 = 1656713) B1656713
theorem B3332987 : Blo 435777 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B1399943 : Blo 435777 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B3333473 : Blo 435777 3333473 := bstep (se 2 (by rfl) ⟨1250052, by rfl⟩ : syracuseStep 3333473 = 2500105) B2500105
theorem B145219483 : Blo 435777 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B1663031 : Blo 435777 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B1107209 : Blo 435777 1107209 := bstep (se 2 (by rfl) ⟨415203, by rfl⟩ : syracuseStep 1107209 = 830407) B830407
theorem B3008771 : Blo 435777 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B3336875 : Blo 435777 3336875 := bstep (se 1 (by rfl) ⟨2502656, by rfl⟩ : syracuseStep 3336875 = 5005313) B5005313
theorem B551711 : Blo 435777 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B2485343 : Blo 435777 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B3337361 : Blo 435777 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B23981275 : Blo 435777 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B57438001 : Blo 435777 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B651487 : Blo 435777 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B6943103 : Blo 435777 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B1996105 : Blo 435777 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B1242479 : Blo 435777 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B26933111 : Blo 435777 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B1112231 : Blo 435777 1112231 := bstep (se 1 (by rfl) ⟨834173, by rfl⟩ : syracuseStep 1112231 = 1668347) B1668347
theorem B1669319 : Blo 435777 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B7109207 : Blo 435777 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B654203 : Blo 435777 654203 := bstep (se 1 (by rfl) ⟨490652, by rfl⟩ : syracuseStep 654203 = 981305) B981305
theorem B356023187 : Blo 435777 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B1244335 : Blo 435777 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B654695 : Blo 435777 654695 := bstep (se 1 (by rfl) ⟨491021, by rfl⟩ : syracuseStep 654695 = 982043) B982043
theorem B982511 : Blo 435777 982511 := bstep (se 1 (by rfl) ⟨736883, by rfl⟩ : syracuseStep 982511 = 1473767) B1473767
theorem B1179127 : Blo 435777 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B491035 : Blo 435777 491035 := bstep (se 1 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 491035 = 736553) B736553
theorem B1802047 : Blo 435777 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B1474523 : Blo 435777 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B3309659 : Blo 435777 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B4817191 : Blo 435777 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B655679 : Blo 435777 655679 := bstep (se 1 (by rfl) ⟨491759, by rfl⟩ : syracuseStep 655679 = 983519) B983519
theorem B524647 : Blo 435777 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B3375481 : Blo 435777 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B655847 : Blo 435777 655847 := bstep (se 1 (by rfl) ⟨491885, by rfl⟩ : syracuseStep 655847 = 983771) B983771
theorem B656009 : Blo 435777 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B983879 : Blo 435777 983879 := bstep (se 1 (by rfl) ⟨737909, by rfl⟩ : syracuseStep 983879 = 1475819) B1475819
theorem B656543 : Blo 435777 656543 := bstep (se 1 (by rfl) ⟨492407, by rfl⟩ : syracuseStep 656543 = 984815) B984815
theorem B2163943 : Blo 435777 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B4785419 : Blo 435777 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B984383 : Blo 435777 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B656711 : Blo 435777 656711 := bstep (se 1 (by rfl) ⟨492533, by rfl⟩ : syracuseStep 656711 = 985067) B985067
theorem B492871 : Blo 435777 492871 := bstep (se 1 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 492871 = 739307) B739307
theorem B656951 : Blo 435777 656951 := bstep (se 1 (by rfl) ⟨492713, by rfl⟩ : syracuseStep 656951 = 985427) B985427
theorem B657023 : Blo 435777 657023 := bstep (se 1 (by rfl) ⟨492767, by rfl⟩ : syracuseStep 657023 = 985535) B985535
theorem B1771625 : Blo 435777 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B4197095 : Blo 435777 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B43223867 : Blo 435777 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B658247 : Blo 435777 658247 := bstep (se 1 (by rfl) ⟨493685, by rfl⟩ : syracuseStep 658247 = 987371) B987371
theorem B1248139 : Blo 435777 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B658559 : Blo 435777 658559 := bstep (se 1 (by rfl) ⟨493919, by rfl⟩ : syracuseStep 658559 = 987839) B987839
theorem B1051879 : Blo 435777 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B625915 : Blo 435777 625915 := bstep (se 1 (by rfl) ⟨469436, by rfl⟩ : syracuseStep 625915 = 938873) B938873
theorem B658751 : Blo 435777 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B658895 : Blo 435777 658895 := bstep (se 1 (by rfl) ⟨494171, by rfl⟩ : syracuseStep 658895 = 988343) B988343
theorem B13438979 : Blo 435777 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B76584001 : Blo 435777 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B988271 : Blo 435777 988271 := bstep (se 1 (by rfl) ⟨741203, by rfl⟩ : syracuseStep 988271 = 1482407) B1482407
theorem B3740863 : Blo 435777 3740863 := bstep (se 1 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 3740863 = 5611295) B5611295
theorem B2102699 : Blo 435777 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B988937 : Blo 435777 988937 := bstep (se 2 (by rfl) ⟨370851, by rfl⟩ : syracuseStep 988937 = 741703) B741703
theorem B1251227 : Blo 435777 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B2103545 : Blo 435777 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B5708225 : Blo 435777 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B2497007 : Blo 435777 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B2005847 : Blo 435777 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B2661473 : Blo 435777 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B3153791 : Blo 435777 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B4628735 : Blo 435777 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B828319 : Blo 435777 828319 := bstep (se 1 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 828319 = 1242479) B1242479
theorem B436135 : Blo 435777 436135 := bstep (se 1 (by rfl) ⟨327101, by rfl⟩ : syracuseStep 436135 = 654203) B654203
theorem B237348791 : Blo 435777 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B436463 : Blo 435777 436463 := bstep (se 1 (by rfl) ⟨327347, by rfl⟩ : syracuseStep 436463 = 654695) B654695
theorem B2402729 : Blo 435777 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B437019 : Blo 435777 437019 := bstep (se 1 (by rfl) ⟨327764, by rfl⟩ : syracuseStep 437019 = 655529) B655529
theorem B437159 : Blo 435777 437159 := bstep (se 1 (by rfl) ⟨327869, by rfl⟩ : syracuseStep 437159 = 655739) B655739
theorem B437275 : Blo 435777 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B437479 : Blo 435777 437479 := bstep (se 1 (by rfl) ⟨328109, by rfl⟩ : syracuseStep 437479 = 656219) B656219
theorem B437711 : Blo 435777 437711 := bstep (se 1 (by rfl) ⟨328283, by rfl⟩ : syracuseStep 437711 = 656567) B656567
theorem B68431333 : Blo 435777 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B4730345 : Blo 435777 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B437871 : Blo 435777 437871 := bstep (se 1 (by rfl) ⟨328403, by rfl⟩ : syracuseStep 437871 = 656807) B656807
theorem B437919 : Blo 435777 437919 := bstep (se 1 (by rfl) ⟨328439, by rfl⟩ : syracuseStep 437919 = 656879) B656879
theorem B437991 : Blo 435777 437991 := bstep (se 1 (by rfl) ⟨328493, by rfl⟩ : syracuseStep 437991 = 656987) B656987
theorem B1584983 : Blo 435777 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B438479 : Blo 435777 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B438511 : Blo 435777 438511 := bstep (se 1 (by rfl) ⟨328883, by rfl⟩ : syracuseStep 438511 = 657767) B657767
theorem B438599 : Blo 435777 438599 := bstep (se 1 (by rfl) ⟨328949, by rfl⟩ : syracuseStep 438599 = 657899) B657899
theorem B438687 : Blo 435777 438687 := bstep (se 1 (by rfl) ⟨329015, by rfl⟩ : syracuseStep 438687 = 658031) B658031
theorem B438759 : Blo 435777 438759 := bstep (se 1 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 438759 = 658139) B658139
theorem B438767 : Blo 435777 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B2503547 : Blo 435777 2503547 := bstep (se 1 (by rfl) ⟨1877660, by rfl⟩ : syracuseStep 2503547 = 3755321) B3755321
theorem B439323 : Blo 435777 439323 := bstep (se 1 (by rfl) ⟨329492, by rfl⟩ : syracuseStep 439323 = 658985) B658985
theorem B32487065 : Blo 435777 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B6305789 : Blo 435777 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B3553307 : Blo 435777 3553307 := bstep (se 1 (by rfl) ⟨2664980, by rfl⟩ : syracuseStep 3553307 = 5329961) B5329961
theorem B933295 : Blo 435777 933295 := bstep (se 1 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 933295 = 1399943) B1399943
theorem B704027 : Blo 435777 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B2211947 : Blo 435777 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B868649 : Blo 435777 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B2212433 : Blo 435777 2212433 := bstep (se 2 (by rfl) ⟨829662, by rfl⟩ : syracuseStep 2212433 = 1659325) B1659325
theorem B2212595 : Blo 435777 2212595 := bstep (se 1 (by rfl) ⟨1659446, by rfl⟩ : syracuseStep 2212595 = 3318893) B3318893
theorem B738139 : Blo 435777 738139 := bstep (se 1 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 738139 = 1107209) B1107209
theorem B5981309 : Blo 435777 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B1656895 : Blo 435777 1656895 := bstep (se 1 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 1656895 = 2485343) B2485343
theorem B4213241 : Blo 435777 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B4509715 : Blo 435777 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B741487 : Blo 435777 741487 := bstep (se 1 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 741487 = 1112231) B1112231
theorem B1659113 : Blo 435777 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B4739471 : Blo 435777 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B1103129 : Blo 435777 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B7099721 : Blo 435777 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B1791389 : Blo 435777 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B1103503 : Blo 435777 1103503 := bstep (se 1 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 1103503 = 1655255) B1655255
theorem B16570169 : Blo 435777 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B1103807 : Blo 435777 1103807 := bstep (se 1 (by rfl) ⟨827855, by rfl⟩ : syracuseStep 1103807 = 1655711) B1655711
theorem B4479421 : Blo 435777 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B5003855 : Blo 435777 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B9460415 : Blo 435777 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B1399673 : Blo 435777 1399673 := bstep (se 2 (by rfl) ⟨524877, by rfl⟩ : syracuseStep 1399673 = 1049755) B1049755
theorem B1105883 : Blo 435777 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B1139579 : Blo 435777 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B1107047 : Blo 435777 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B1107179 : Blo 435777 1107179 := bstep (se 1 (by rfl) ⟨830384, by rfl⟩ : syracuseStep 1107179 = 1660769) B1660769
theorem B7497035 : Blo 435777 7497035 := bstep (se 1 (by rfl) ⟨5622776, by rfl⟩ : syracuseStep 7497035 = 11245553) B11245553
theorem B31975033 : Blo 435777 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1795931 : Blo 435777 1795931 := bstep (se 1 (by rfl) ⟨1346948, by rfl⟩ : syracuseStep 1795931 = 2693897) B2693897
theorem B2221991 : Blo 435777 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B2222315 : Blo 435777 2222315 := bstep (se 1 (by rfl) ⟨1666736, by rfl⟩ : syracuseStep 2222315 = 3333473) B3333473
theorem B1108687 : Blo 435777 1108687 := bstep (se 1 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 1108687 = 1663031) B1663031
theorem B1109609 : Blo 435777 1109609 := bstep (se 2 (by rfl) ⟨416103, by rfl⟩ : syracuseStep 1109609 = 832207) B832207
theorem B2224583 : Blo 435777 2224583 := bstep (se 1 (by rfl) ⟨1668437, by rfl⟩ : syracuseStep 2224583 = 3336875) B3336875
theorem B1471229 : Blo 435777 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B2224907 : Blo 435777 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B1110905 : Blo 435777 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B1471391 : Blo 435777 1471391 := bstep (se 1 (by rfl) ⟨1103543, by rfl⟩ : syracuseStep 1471391 = 2207087) B2207087
theorem B1864691 : Blo 435777 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B1471823 : Blo 435777 1471823 := bstep (se 1 (by rfl) ⟨1103867, by rfl⟩ : syracuseStep 1471823 = 2207735) B2207735
theorem B980585 : Blo 435777 980585 := bstep (se 2 (by rfl) ⟨367719, by rfl⟩ : syracuseStep 980585 = 735439) B735439
theorem B1472633 : Blo 435777 1472633 := bstep (se 2 (by rfl) ⟨552237, by rfl⟩ : syracuseStep 1472633 = 1104475) B1104475
theorem B1472687 : Blo 435777 1472687 := bstep (se 1 (by rfl) ⟨1104515, by rfl⟩ : syracuseStep 1472687 = 2209031) B2209031
theorem B620903 : Blo 435777 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B1899001 : Blo 435777 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B17955407 : Blo 435777 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B8419949 : Blo 435777 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B621211 : Blo 435777 621211 := bstep (se 1 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 621211 = 931817) B931817
theorem B1112879 : Blo 435777 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B981881 : Blo 435777 981881 := bstep (se 2 (by rfl) ⟨368205, by rfl⟩ : syracuseStep 981881 = 736411) B736411
theorem B4226003 : Blo 435777 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B1014751 : Blo 435777 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B982313 : Blo 435777 982313 := bstep (se 2 (by rfl) ⟨368367, by rfl⟩ : syracuseStep 982313 = 736735) B736735
theorem B1572169 : Blo 435777 1572169 := bstep (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) B1179127
theorem B654713 : Blo 435777 654713 := bstep (se 2 (by rfl) ⟨245517, by rfl⟩ : syracuseStep 654713 = 491035) B491035
theorem B556571 : Blo 435777 556571 := bstep (se 1 (by rfl) ⟨417428, by rfl⟩ : syracuseStep 556571 = 834857) B834857
theorem B655007 : Blo 435777 655007 := bstep (se 1 (by rfl) ⟨491255, by rfl⟩ : syracuseStep 655007 = 982511) B982511
theorem B1474415 : Blo 435777 1474415 := bstep (se 1 (by rfl) ⟨1105811, by rfl⟩ : syracuseStep 1474415 = 2211623) B2211623
theorem B193625977 : Blo 435777 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B983015 : Blo 435777 983015 := bstep (se 1 (by rfl) ⟨737261, by rfl⟩ : syracuseStep 983015 = 1474523) B1474523
theorem B1474631 : Blo 435777 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B6422921 : Blo 435777 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B1474955 : Blo 435777 1474955 := bstep (se 1 (by rfl) ⟨1106216, by rfl⟩ : syracuseStep 1474955 = 2212433) B2212433
theorem B1475063 : Blo 435777 1475063 := bstep (se 1 (by rfl) ⟨1106297, by rfl⟩ : syracuseStep 1475063 = 2212595) B2212595
theorem B655919 : Blo 435777 655919 := bstep (se 1 (by rfl) ⟨491939, by rfl⟩ : syracuseStep 655919 = 983879) B983879
theorem B656255 : Blo 435777 656255 := bstep (se 1 (by rfl) ⟨492191, by rfl⟩ : syracuseStep 656255 = 984383) B984383
theorem B984185 : Blo 435777 984185 := bstep (se 2 (by rfl) ⟨369069, by rfl⟩ : syracuseStep 984185 = 738139) B738139
theorem B1181083 : Blo 435777 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B2885257 : Blo 435777 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B657161 : Blo 435777 657161 := bstep (se 2 (by rfl) ⟨246435, by rfl⟩ : syracuseStep 657161 = 492871) B492871
theorem B42633377 : Blo 435777 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B658847 : Blo 435777 658847 := bstep (se 1 (by rfl) ⟨494135, by rfl⟩ : syracuseStep 658847 = 988271) B988271
theorem B1478249 : Blo 435777 1478249 := bstep (se 2 (by rfl) ⟨554343, by rfl⟩ : syracuseStep 1478249 = 1108687) B1108687
theorem B659291 : Blo 435777 659291 := bstep (se 1 (by rfl) ⟨494468, by rfl⟩ : syracuseStep 659291 = 988937) B988937
theorem B11046779 : Blo 435777 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B3805483 : Blo 435777 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B1774315 : Blo 435777 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B5412005 : Blo 435777 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B2102527 : Blo 435777 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B988649 : Blo 435777 988649 := bstep (se 2 (by rfl) ⟨370743, by rfl⟩ : syracuseStep 988649 = 741487) B741487
theorem B3085823 : Blo 435777 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B759719 : Blo 435777 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B1481327 : Blo 435777 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B102112001 : Blo 435777 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B1481543 : Blo 435777 1481543 := bstep (se 1 (by rfl) ⟨1111157, by rfl⟩ : syracuseStep 1481543 = 2222315) B2222315
theorem B4987817 : Blo 435777 4987817 := bstep (se 2 (by rfl) ⟨1870431, by rfl⟩ : syracuseStep 4987817 = 3740863) B3740863
theorem B3153563 : Blo 435777 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B1056655 : Blo 435777 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B1483055 : Blo 435777 1483055 := bstep (se 1 (by rfl) ⟨1112291, by rfl⟩ : syracuseStep 1483055 = 2224583) B2224583
theorem B1483271 : Blo 435777 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B5972561 : Blo 435777 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B2532001 : Blo 435777 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B828281 : Blo 435777 828281 := bstep (se 2 (by rfl) ⟨310605, by rfl⟩ : syracuseStep 828281 = 621211) B621211
theorem B4203859 : Blo 435777 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B2368871 : Blo 435777 2368871 := bstep (se 1 (by rfl) ⟨1776653, by rfl⟩ : syracuseStep 2368871 = 3553307) B3553307
theorem B1484189 : Blo 435777 1484189 := bstep (se 3 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 1484189 = 556571) B556571
theorem B11970271 : Blo 435777 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B5613299 : Blo 435777 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B436475 : Blo 435777 436475 := bstep (se 1 (by rfl) ⟨327356, by rfl⟩ : syracuseStep 436475 = 654713) B654713
theorem B469351 : Blo 435777 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B436671 : Blo 435777 436671 := bstep (se 1 (by rfl) ⟨327503, by rfl⟩ : syracuseStep 436671 = 655007) B655007
theorem B2206439 : Blo 435777 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B437119 : Blo 435777 437119 := bstep (se 1 (by rfl) ⟨327839, by rfl⟩ : syracuseStep 437119 = 655679) B655679
theorem B437231 : Blo 435777 437231 := bstep (se 1 (by rfl) ⟨327923, by rfl⟩ : syracuseStep 437231 = 655847) B655847
theorem B437339 : Blo 435777 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B699529 : Blo 435777 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B4500641 : Blo 435777 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B437695 : Blo 435777 437695 := bstep (se 1 (by rfl) ⟨328271, by rfl⟩ : syracuseStep 437695 = 656543) B656543
theorem B3190279 : Blo 435777 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B437807 : Blo 435777 437807 := bstep (se 1 (by rfl) ⟨328355, by rfl⟩ : syracuseStep 437807 = 656711) B656711
theorem B437967 : Blo 435777 437967 := bstep (se 1 (by rfl) ⟨328475, by rfl⟩ : syracuseStep 437967 = 656951) B656951
theorem B438015 : Blo 435777 438015 := bstep (se 1 (by rfl) ⟨328511, by rfl⟩ : syracuseStep 438015 = 657023) B657023
theorem B2798063 : Blo 435777 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B28815911 : Blo 435777 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B438831 : Blo 435777 438831 := bstep (se 1 (by rfl) ⟨329123, by rfl⟩ : syracuseStep 438831 = 658247) B658247
theorem B439039 : Blo 435777 439039 := bstep (se 1 (by rfl) ⟨329279, by rfl⟩ : syracuseStep 439039 = 658559) B658559
theorem B439167 : Blo 435777 439167 := bstep (se 1 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 439167 = 658751) B658751
theorem B439263 : Blo 435777 439263 := bstep (se 1 (by rfl) ⟨329447, by rfl⟩ : syracuseStep 439263 = 658895) B658895
theorem B8959319 : Blo 435777 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B2209193 : Blo 435777 2209193 := bstep (se 2 (by rfl) ⟨828447, by rfl⟩ : syracuseStep 2209193 = 1656895) B1656895
theorem B3159647 : Blo 435777 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B735419 : Blo 435777 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B4733147 : Blo 435777 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B1194259 : Blo 435777 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B834151 : Blo 435777 834151 := bstep (se 1 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 834151 = 1251227) B1251227
theorem B735871 : Blo 435777 735871 := bstep (se 1 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 735871 = 1103807) B1103807
theorem B834553 : Blo 435777 834553 := bstep (se 2 (by rfl) ⟨312957, by rfl⟩ : syracuseStep 834553 = 625915) B625915
theorem B6306943 : Blo 435777 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B933115 : Blo 435777 933115 := bstep (se 1 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 933115 = 1399673) B1399673
theorem B91241777 : Blo 435777 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B737255 : Blo 435777 737255 := bstep (se 1 (by rfl) ⟨552941, by rfl⟩ : syracuseStep 737255 = 1105883) B1105883
theorem B6012953 : Blo 435777 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B738031 : Blo 435777 738031 := bstep (se 1 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 738031 = 1107047) B1107047
theorem B738119 : Blo 435777 738119 := bstep (se 1 (by rfl) ⟨553589, by rfl⟩ : syracuseStep 738119 = 1107179) B1107179
theorem B4998023 : Blo 435777 4998023 := bstep (se 1 (by rfl) ⟨3748517, by rfl⟩ : syracuseStep 4998023 = 7497035) B7497035
theorem B1655741 : Blo 435777 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B1197287 : Blo 435777 1197287 := bstep (se 1 (by rfl) ⟨897965, by rfl⟩ : syracuseStep 1197287 = 1795931) B1795931
theorem B739739 : Blo 435777 739739 := bstep (se 1 (by rfl) ⟨554804, by rfl⟩ : syracuseStep 739739 = 1109609) B1109609
theorem B740603 : Blo 435777 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B741919 : Blo 435777 741919 := bstep (se 1 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 741919 = 1112879) B1112879
theorem B258167969 : Blo 435777 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B3987539 : Blo 435777 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B1104425 : Blo 435777 1104425 := bstep (se 2 (by rfl) ⟨414159, by rfl⟩ : syracuseStep 1104425 = 828319) B828319
theorem B2808827 : Blo 435777 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B1106075 : Blo 435777 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B9265589 : Blo 435777 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1401799 : Blo 435777 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1664185 : Blo 435777 1664185 := bstep (se 2 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 1664185 = 1248139) B1248139
theorem B1402363 : Blo 435777 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1402505 : Blo 435777 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B1664671 : Blo 435777 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B3335903 : Blo 435777 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B1337231 : Blo 435777 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B158232527 : Blo 435777 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B1601819 : Blo 435777 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B1471337 : Blo 435777 1471337 := bstep (se 2 (by rfl) ⟨551751, by rfl⟩ : syracuseStep 1471337 = 1103503) B1103503
theorem B980819 : Blo 435777 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B1669031 : Blo 435777 1669031 := bstep (se 1 (by rfl) ⟨1251773, by rfl⟩ : syracuseStep 1669031 = 2503547) B2503547
theorem B980927 : Blo 435777 980927 := bstep (se 1 (by rfl) ⟨735695, by rfl⟩ : syracuseStep 980927 = 1471391) B1471391
theorem B1243127 : Blo 435777 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B981215 : Blo 435777 981215 := bstep (se 1 (by rfl) ⟨735911, by rfl⟩ : syracuseStep 981215 = 1471823) B1471823
theorem B653723 : Blo 435777 653723 := bstep (se 1 (by rfl) ⟨490292, by rfl⟩ : syracuseStep 653723 = 980585) B980585
theorem B21658043 : Blo 435777 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B981755 : Blo 435777 981755 := bstep (se 1 (by rfl) ⟨736316, by rfl⟩ : syracuseStep 981755 = 1472633) B1472633
theorem B981791 : Blo 435777 981791 := bstep (se 1 (by rfl) ⟨736343, by rfl⟩ : syracuseStep 981791 = 1472687) B1472687
theorem B2096225 : Blo 435777 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B1244393 : Blo 435777 1244393 := bstep (se 2 (by rfl) ⟨466647, by rfl⟩ : syracuseStep 1244393 = 933295) B933295
theorem B654587 : Blo 435777 654587 := bstep (se 1 (by rfl) ⟨490940, by rfl⟩ : syracuseStep 654587 = 981881) B981881
theorem B2817335 : Blo 435777 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B654875 : Blo 435777 654875 := bstep (se 1 (by rfl) ⟨491156, by rfl⟩ : syracuseStep 654875 = 982313) B982313
theorem B982943 : Blo 435777 982943 := bstep (se 1 (by rfl) ⟨737207, by rfl⟩ : syracuseStep 982943 = 1474415) B1474415
theorem B655343 : Blo 435777 655343 := bstep (se 1 (by rfl) ⟨491507, by rfl⟩ : syracuseStep 655343 = 983015) B983015
theorem B983087 : Blo 435777 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B983303 : Blo 435777 983303 := bstep (se 1 (by rfl) ⟨737477, by rfl⟩ : syracuseStep 983303 = 1474955) B1474955
theorem B983375 : Blo 435777 983375 := bstep (se 1 (by rfl) ⟨737531, by rfl⟩ : syracuseStep 983375 = 1475063) B1475063
theorem B492079 : Blo 435777 492079 := bstep (se 1 (by rfl) ⟨369059, by rfl⟩ : syracuseStep 492079 = 738119) B738119
theorem B656123 : Blo 435777 656123 := bstep (se 1 (by rfl) ⟨492092, by rfl⟩ : syracuseStep 656123 = 984185) B984185
theorem B3376001 : Blo 435777 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B984041 : Blo 435777 984041 := bstep (se 2 (by rfl) ⟨369015, by rfl⟩ : syracuseStep 984041 = 738031) B738031
theorem B1869065 : Blo 435777 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B493159 : Blo 435777 493159 := bstep (se 1 (by rfl) ⟨369869, by rfl⟩ : syracuseStep 493159 = 739739) B739739
theorem B5605145 : Blo 435777 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B1574777 : Blo 435777 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B1869817 : Blo 435777 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B493735 : Blo 435777 493735 := bstep (se 1 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 493735 = 740603) B740603
theorem B15960361 : Blo 435777 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B985499 : Blo 435777 985499 := bstep (se 1 (by rfl) ⟨739124, by rfl⟩ : syracuseStep 985499 = 1478249) B1478249
theorem B625801 : Blo 435777 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B3608003 : Blo 435777 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B659099 : Blo 435777 659099 := bstep (se 1 (by rfl) ⟨494324, by rfl⟩ : syracuseStep 659099 = 988649) B988649
theorem B8228861 : Blo 435777 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B2658359 : Blo 435777 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B987551 : Blo 435777 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B987695 : Blo 435777 987695 := bstep (se 1 (by rfl) ⟨740771, by rfl⟩ : syracuseStep 987695 = 1481543) B1481543
theorem B1872551 : Blo 435777 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B2102375 : Blo 435777 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B3315005 : Blo 435777 3315005 := bstep (se 3 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 3315005 = 1243127) B1243127
theorem B988703 : Blo 435777 988703 := bstep (se 1 (by rfl) ⟨741527, by rfl⟩ : syracuseStep 988703 = 1483055) B1483055
theorem B988847 : Blo 435777 988847 := bstep (se 1 (by rfl) ⟨741635, by rfl⟩ : syracuseStep 988847 = 1483271) B1483271
theorem B989225 : Blo 435777 989225 := bstep (se 2 (by rfl) ⟨370959, by rfl⟩ : syracuseStep 989225 = 741919) B741919
theorem B1579247 : Blo 435777 1579247 := bstep (se 1 (by rfl) ⟨1184435, by rfl⟩ : syracuseStep 1579247 = 2368871) B2368871
theorem B989459 : Blo 435777 989459 := bstep (se 1 (by rfl) ⟨742094, by rfl⟩ : syracuseStep 989459 = 1484189) B1484189
theorem B3742199 : Blo 435777 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B105488351 : Blo 435777 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B19210607 : Blo 435777 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B12001709 : Blo 435777 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B5972879 : Blo 435777 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B2106431 : Blo 435777 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B3155431 : Blo 435777 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B435815 : Blo 435777 435815 := bstep (se 1 (by rfl) ⟨326861, by rfl⟩ : syracuseStep 435815 = 653723) B653723
theorem B829595 : Blo 435777 829595 := bstep (se 1 (by rfl) ⟨622196, by rfl⟩ : syracuseStep 829595 = 1244393) B1244393
theorem B436391 : Blo 435777 436391 := bstep (se 1 (by rfl) ⟨327293, by rfl⟩ : syracuseStep 436391 = 654587) B654587
theorem B60827851 : Blo 435777 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B1878223 : Blo 435777 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B436583 : Blo 435777 436583 := bstep (se 1 (by rfl) ⟨327437, by rfl⟩ : syracuseStep 436583 = 654875) B654875
theorem B436895 : Blo 435777 436895 := bstep (se 1 (by rfl) ⟨327671, by rfl⟩ : syracuseStep 436895 = 655343) B655343
theorem B4008635 : Blo 435777 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B437279 : Blo 435777 437279 := bstep (se 1 (by rfl) ⟨327959, by rfl⟩ : syracuseStep 437279 = 655919) B655919
theorem B437503 : Blo 435777 437503 := bstep (se 1 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 437503 = 656255) B656255
theorem B798191 : Blo 435777 798191 := bstep (se 1 (by rfl) ⟨598643, by rfl⟩ : syracuseStep 798191 = 1197287) B1197287
theorem B438107 : Blo 435777 438107 := bstep (se 1 (by rfl) ⟨328580, by rfl⟩ : syracuseStep 438107 = 657161) B657161
theorem B28422251 : Blo 435777 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B3847009 : Blo 435777 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B439231 : Blo 435777 439231 := bstep (se 1 (by rfl) ⟨329423, by rfl⟩ : syracuseStep 439231 = 658847) B658847
theorem B439527 : Blo 435777 439527 := bstep (se 1 (by rfl) ⟨329645, by rfl⟩ : syracuseStep 439527 = 659291) B659291
theorem B172111979 : Blo 435777 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B506479 : Blo 435777 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B932705 : Blo 435777 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B736283 : Blo 435777 736283 := bstep (se 1 (by rfl) ⟨552212, by rfl⟩ : syracuseStep 736283 = 1104425) B1104425
theorem B68074667 : Blo 435777 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B3325211 : Blo 435777 3325211 := bstep (se 1 (by rfl) ⟨2493908, by rfl⟩ : syracuseStep 3325211 = 4987817) B4987817
theorem B737383 : Blo 435777 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B6177059 : Blo 435777 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B3981707 : Blo 435777 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B935003 : Blo 435777 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B2803369 : Blo 435777 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B1067879 : Blo 435777 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B1592345 : Blo 435777 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B8409257 : Blo 435777 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B14438695 : Blo 435777 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B1397483 : Blo 435777 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B4281947 : Blo 435777 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B3332015 : Blo 435777 3332015 := bstep (se 1 (by rfl) ⟨2499011, by rfl⟩ : syracuseStep 3332015 = 4998023) B4998023
theorem B1103827 : Blo 435777 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B2218913 : Blo 435777 2218913 := bstep (se 2 (by rfl) ⟨832092, by rfl⟩ : syracuseStep 2218913 = 1664185) B1664185
theorem B2219561 : Blo 435777 2219561 := bstep (se 2 (by rfl) ⟨832335, by rfl⟩ : syracuseStep 2219561 = 1664671) B1664671
theorem B7364519 : Blo 435777 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B9463013 : Blo 435777 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B4253705 : Blo 435777 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B3565949 : Blo 435777 3565949 := bstep (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) B1337231
theorem B5073977 : Blo 435777 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B552187 : Blo 435777 552187 := bstep (se 1 (by rfl) ⟨414140, by rfl⟩ : syracuseStep 552187 = 828281) B828281
theorem B2223935 : Blo 435777 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B1470959 : Blo 435777 1470959 := bstep (se 1 (by rfl) ⟨1103219, by rfl⟩ : syracuseStep 1470959 = 2206439) B2206439
theorem B1865375 : Blo 435777 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B980891 : Blo 435777 980891 := bstep (se 1 (by rfl) ⟨735668, by rfl⟩ : syracuseStep 980891 = 1471337) B1471337
theorem B1112201 : Blo 435777 1112201 := bstep (se 2 (by rfl) ⟨417075, by rfl⟩ : syracuseStep 1112201 = 834151) B834151
theorem B981161 : Blo 435777 981161 := bstep (se 2 (by rfl) ⟨367935, by rfl⟩ : syracuseStep 981161 = 735871) B735871
theorem B1472795 : Blo 435777 1472795 := bstep (se 1 (by rfl) ⟨1104596, by rfl⟩ : syracuseStep 1472795 = 2209193) B2209193
theorem B653879 : Blo 435777 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B1112687 : Blo 435777 1112687 := bstep (se 1 (by rfl) ⟨834515, by rfl⟩ : syracuseStep 1112687 = 1669031) B1669031
theorem B653951 : Blo 435777 653951 := bstep (se 1 (by rfl) ⟨490463, by rfl⟩ : syracuseStep 653951 = 980927) B980927
theorem B1112737 : Blo 435777 1112737 := bstep (se 2 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 1112737 = 834553) B834553
theorem B490279 : Blo 435777 490279 := bstep (se 1 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 490279 = 735419) B735419
theorem B654143 : Blo 435777 654143 := bstep (se 1 (by rfl) ⟨490607, by rfl⟩ : syracuseStep 654143 = 981215) B981215
theorem B1244153 : Blo 435777 1244153 := bstep (se 2 (by rfl) ⟨466557, by rfl⟩ : syracuseStep 1244153 = 933115) B933115
theorem B654503 : Blo 435777 654503 := bstep (se 1 (by rfl) ⟨490877, by rfl⟩ : syracuseStep 654503 = 981755) B981755
theorem B654527 : Blo 435777 654527 := bstep (se 1 (by rfl) ⟨490895, by rfl⟩ : syracuseStep 654527 = 981791) B981791
theorem B1408873 : Blo 435777 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B655295 : Blo 435777 655295 := bstep (se 1 (by rfl) ⟨491471, by rfl⟩ : syracuseStep 655295 = 982943) B982943
theorem B491503 : Blo 435777 491503 := bstep (se 1 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 491503 = 737255) B737255
theorem B655391 : Blo 435777 655391 := bstep (se 1 (by rfl) ⟨491543, by rfl⟩ : syracuseStep 655391 = 983087) B983087
theorem B983177 : Blo 435777 983177 := bstep (se 2 (by rfl) ⟨368691, by rfl⟩ : syracuseStep 983177 = 737383) B737383
theorem B655535 : Blo 435777 655535 := bstep (se 1 (by rfl) ⟨491651, by rfl⟩ : syracuseStep 655535 = 983303) B983303
theorem B655583 : Blo 435777 655583 := bstep (se 1 (by rfl) ⟨491687, by rfl⟩ : syracuseStep 655583 = 983375) B983375
theorem B2654471 : Blo 435777 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B656027 : Blo 435777 656027 := bstep (se 1 (by rfl) ⟨492020, by rfl⟩ : syracuseStep 656027 = 984041) B984041
theorem B656105 : Blo 435777 656105 := bstep (se 2 (by rfl) ⟨246039, by rfl⟩ : syracuseStep 656105 = 492079) B492079
theorem B1246043 : Blo 435777 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B3736763 : Blo 435777 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B1049851 : Blo 435777 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B656999 : Blo 435777 656999 := bstep (se 1 (by rfl) ⟨492749, by rfl⟩ : syracuseStep 656999 = 985499) B985499
theorem B657545 : Blo 435777 657545 := bstep (se 2 (by rfl) ⟨246579, by rfl⟩ : syracuseStep 657545 = 493159) B493159
theorem B3737825 : Blo 435777 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B2493089 : Blo 435777 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B5606171 : Blo 435777 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B658313 : Blo 435777 658313 := bstep (se 2 (by rfl) ⟨246867, by rfl⟩ : syracuseStep 658313 = 493735) B493735
theorem B2493341 : Blo 435777 2493341 := bstep (se 3 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 2493341 = 935003) B935003
theorem B81103801 : Blo 435777 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B658367 : Blo 435777 658367 := bstep (se 1 (by rfl) ⟨493775, by rfl⟩ : syracuseStep 658367 = 987551) B987551
theorem B658463 : Blo 435777 658463 := bstep (se 1 (by rfl) ⟨493847, by rfl⟩ : syracuseStep 658463 = 987695) B987695
theorem B1248367 : Blo 435777 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B659135 : Blo 435777 659135 := bstep (se 1 (by rfl) ⟨494351, by rfl⟩ : syracuseStep 659135 = 988703) B988703
theorem B2854631 : Blo 435777 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B659231 : Blo 435777 659231 := bstep (se 1 (by rfl) ⟨494423, by rfl⟩ : syracuseStep 659231 = 988847) B988847
theorem B659483 : Blo 435777 659483 := bstep (se 1 (by rfl) ⟨494612, by rfl⟩ : syracuseStep 659483 = 989225) B989225
theorem B1052831 : Blo 435777 1052831 := bstep (se 1 (by rfl) ⟨789623, by rfl⟩ : syracuseStep 1052831 = 1579247) B1579247
theorem B659639 : Blo 435777 659639 := bstep (se 1 (by rfl) ⟨494729, by rfl⟩ : syracuseStep 659639 = 989459) B989459
theorem B2494799 : Blo 435777 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B1479275 : Blo 435777 1479275 := bstep (se 1 (by rfl) ⟨1109456, by rfl⟩ : syracuseStep 1479275 = 2218913) B2218913
theorem B1479707 : Blo 435777 1479707 := bstep (se 1 (by rfl) ⟨1109780, by rfl⟩ : syracuseStep 1479707 = 2219561) B2219561
theorem B70325567 : Blo 435777 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B9509197 : Blo 435777 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B3382651 : Blo 435777 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B532127 : Blo 435777 532127 := bstep (se 1 (by rfl) ⟨399095, by rfl⟩ : syracuseStep 532127 = 798191) B798191
theorem B1482623 : Blo 435777 1482623 := bstep (se 1 (by rfl) ⟨1111967, by rfl⟩ : syracuseStep 1482623 = 2223935) B2223935
theorem B18948167 : Blo 435777 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B1483649 : Blo 435777 1483649 := bstep (se 2 (by rfl) ⟨556368, by rfl⟩ : syracuseStep 1483649 = 1112737) B1112737
theorem B435919 : Blo 435777 435919 := bstep (se 1 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 435919 = 653879) B653879
theorem B435967 : Blo 435777 435967 := bstep (se 1 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 435967 = 653951) B653951
theorem B436095 : Blo 435777 436095 := bstep (se 1 (by rfl) ⟨327071, by rfl⟩ : syracuseStep 436095 = 654143) B654143
theorem B829435 : Blo 435777 829435 := bstep (se 1 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 829435 = 1244153) B1244153
theorem B436335 : Blo 435777 436335 := bstep (se 1 (by rfl) ⟨327251, by rfl⟩ : syracuseStep 436335 = 654503) B654503
theorem B436351 : Blo 435777 436351 := bstep (se 1 (by rfl) ⟨327263, by rfl⟩ : syracuseStep 436351 = 654527) B654527
theorem B1878497 : Blo 435777 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B436863 : Blo 435777 436863 := bstep (se 1 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 436863 = 655295) B655295
theorem B7088957 : Blo 435777 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B437415 : Blo 435777 437415 := bstep (se 1 (by rfl) ⟨328061, by rfl⟩ : syracuseStep 437415 = 656123) B656123
theorem B4207241 : Blo 435777 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B2405335 : Blo 435777 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B439399 : Blo 435777 439399 := bstep (se 1 (by rfl) ⟨329549, by rfl⟩ : syracuseStep 439399 = 659099) B659099
theorem B5485907 : Blo 435777 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B2504297 : Blo 435777 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B21280481 : Blo 435777 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B931655 : Blo 435777 931655 := bstep (se 1 (by rfl) ⟨698741, by rfl⟩ : syracuseStep 931655 = 1397483) B1397483
theorem B2210003 : Blo 435777 2210003 := bstep (se 1 (by rfl) ⟨1657502, by rfl⟩ : syracuseStep 2210003 = 3315005) B3315005
theorem B834401 : Blo 435777 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B736249 : Blo 435777 736249 := bstep (se 2 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 736249 = 552187) B552187
theorem B458965277 : Blo 435777 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B19251593 : Blo 435777 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B3981919 : Blo 435777 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B6308675 : Blo 435777 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B5129345 : Blo 435777 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B2835803 : Blo 435777 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B2672423 : Blo 435777 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B4246253 : Blo 435777 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B675305 : Blo 435777 675305 := bstep (se 2 (by rfl) ⟨253239, by rfl⟩ : syracuseStep 675305 = 506479) B506479
theorem B741467 : Blo 435777 741467 := bstep (se 1 (by rfl) ⟨556100, by rfl⟩ : syracuseStep 741467 = 1112201) B1112201
theorem B741791 : Blo 435777 741791 := bstep (se 1 (by rfl) ⟨556343, by rfl⟩ : syracuseStep 741791 = 1112687) B1112687
theorem B2216807 : Blo 435777 2216807 := bstep (se 1 (by rfl) ⟨1662605, by rfl⟩ : syracuseStep 2216807 = 3325211) B3325211
theorem B4118039 : Blo 435777 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B2250667 : Blo 435777 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B32004557 : Blo 435777 32004557 := bstep (se 3 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 32004557 = 12001709) B12001709
theorem B711919 : Blo 435777 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B1401583 : Blo 435777 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B2221343 : Blo 435777 2221343 := bstep (se 1 (by rfl) ⟨1666007, by rfl⟩ : syracuseStep 2221343 = 3332015) B3332015
theorem B4909679 : Blo 435777 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B12807071 : Blo 435777 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B1404287 : Blo 435777 1404287 := bstep (se 1 (by rfl) ⟨1053215, by rfl⟩ : syracuseStep 1404287 = 2106431) B2106431
theorem B553063 : Blo 435777 553063 := bstep (se 1 (by rfl) ⟨414797, by rfl⟩ : syracuseStep 553063 = 829595) B829595
theorem B1471769 : Blo 435777 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B980639 : Blo 435777 980639 := bstep (se 1 (by rfl) ⟨735479, by rfl⟩ : syracuseStep 980639 = 1470959) B1470959
theorem B653705 : Blo 435777 653705 := bstep (se 2 (by rfl) ⟨245139, by rfl⟩ : syracuseStep 653705 = 490279) B490279
theorem B1243583 : Blo 435777 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B653927 : Blo 435777 653927 := bstep (se 1 (by rfl) ⟨490445, by rfl⟩ : syracuseStep 653927 = 980891) B980891
theorem B654107 : Blo 435777 654107 := bstep (se 1 (by rfl) ⟨490580, by rfl⟩ : syracuseStep 654107 = 981161) B981161
theorem B981863 : Blo 435777 981863 := bstep (se 1 (by rfl) ⟨736397, by rfl⟩ : syracuseStep 981863 = 1472795) B1472795
theorem B621803 : Blo 435777 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B490855 : Blo 435777 490855 := bstep (se 1 (by rfl) ⟨368141, by rfl⟩ : syracuseStep 490855 = 736283) B736283
theorem B45383111 : Blo 435777 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B655337 : Blo 435777 655337 := bstep (se 2 (by rfl) ⟨245751, by rfl⟩ : syracuseStep 655337 = 491503) B491503
theorem B655451 : Blo 435777 655451 := bstep (se 1 (by rfl) ⟨491588, by rfl⟩ : syracuseStep 655451 = 983177) B983177
theorem B1769647 : Blo 435777 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B2491175 : Blo 435777 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B5309225 : Blo 435777 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B1868777 : Blo 435777 1868777 := bstep (se 2 (by rfl) ⟨700791, by rfl⟩ : syracuseStep 1868777 = 1401583) B1401583
theorem B2491883 : Blo 435777 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B3737447 : Blo 435777 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B1903087 : Blo 435777 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B494311 : Blo 435777 494311 := bstep (se 1 (by rfl) ⟨370733, by rfl⟩ : syracuseStep 494311 = 741467) B741467
theorem B494527 : Blo 435777 494527 := bstep (se 1 (by rfl) ⟨370895, by rfl⟩ : syracuseStep 494527 = 741791) B741791
theorem B986183 : Blo 435777 986183 := bstep (se 1 (by rfl) ⟨739637, by rfl⟩ : syracuseStep 986183 = 1479275) B1479275
theorem B1477871 : Blo 435777 1477871 := bstep (se 1 (by rfl) ⟨1108403, by rfl⟩ : syracuseStep 1477871 = 2216807) B2216807
theorem B986471 : Blo 435777 986471 := bstep (se 1 (by rfl) ⟨739853, by rfl⟩ : syracuseStep 986471 = 1479707) B1479707
theorem B108138401 : Blo 435777 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B21336371 : Blo 435777 21336371 := bstep (se 1 (by rfl) ⟨16002278, by rfl⟩ : syracuseStep 21336371 = 32004557) B32004557
theorem B988415 : Blo 435777 988415 := bstep (se 1 (by rfl) ⟨741311, by rfl⟩ : syracuseStep 988415 = 1482623) B1482623
theorem B989099 : Blo 435777 989099 := bstep (se 1 (by rfl) ⟨741824, by rfl⟩ : syracuseStep 989099 = 1483649) B1483649
theorem B1480895 : Blo 435777 1480895 := bstep (se 1 (by rfl) ⟨1110671, by rfl⟩ : syracuseStep 1480895 = 2221343) B2221343
theorem B1252331 : Blo 435777 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B4725971 : Blo 435777 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B435803 : Blo 435777 435803 := bstep (se 1 (by rfl) ⟨326852, by rfl⟩ : syracuseStep 435803 = 653705) B653705
theorem B829055 : Blo 435777 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B435951 : Blo 435777 435951 := bstep (se 1 (by rfl) ⟨326963, by rfl⟩ : syracuseStep 435951 = 653927) B653927
theorem B1419005 : Blo 435777 1419005 := bstep (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) B532127
theorem B436071 : Blo 435777 436071 := bstep (se 1 (by rfl) ⟨327053, by rfl⟩ : syracuseStep 436071 = 654107) B654107
theorem B30255407 : Blo 435777 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B436891 : Blo 435777 436891 := bstep (se 1 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 436891 = 655337) B655337
theorem B436927 : Blo 435777 436927 := bstep (se 1 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 436927 = 655391) B655391
theorem B437023 : Blo 435777 437023 := bstep (se 1 (by rfl) ⟨327767, by rfl⟩ : syracuseStep 437023 = 655535) B655535
theorem B437055 : Blo 435777 437055 := bstep (se 1 (by rfl) ⟨327791, by rfl⟩ : syracuseStep 437055 = 655583) B655583
theorem B437351 : Blo 435777 437351 := bstep (se 1 (by rfl) ⟨328013, by rfl⟩ : syracuseStep 437351 = 656027) B656027
theorem B437403 : Blo 435777 437403 := bstep (se 1 (by rfl) ⟨328052, by rfl⟩ : syracuseStep 437403 = 656105) B656105
theorem B4205783 : Blo 435777 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B3419563 : Blo 435777 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B437999 : Blo 435777 437999 := bstep (se 1 (by rfl) ⟨328499, by rfl⟩ : syracuseStep 437999 = 656999) B656999
theorem B1781615 : Blo 435777 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B438363 : Blo 435777 438363 := bstep (se 1 (by rfl) ⟨328772, by rfl⟩ : syracuseStep 438363 = 657545) B657545
theorem B11219309 : Blo 435777 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B2830835 : Blo 435777 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B438875 : Blo 435777 438875 := bstep (se 1 (by rfl) ⟨329156, by rfl⟩ : syracuseStep 438875 = 658313) B658313
theorem B438911 : Blo 435777 438911 := bstep (se 1 (by rfl) ⟨329183, by rfl⟩ : syracuseStep 438911 = 658367) B658367
theorem B438975 : Blo 435777 438975 := bstep (se 1 (by rfl) ⟨329231, by rfl⟩ : syracuseStep 438975 = 658463) B658463
theorem B3322781 : Blo 435777 3322781 := bstep (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) B1246043
theorem B439423 : Blo 435777 439423 := bstep (se 1 (by rfl) ⟨329567, by rfl⟩ : syracuseStep 439423 = 659135) B659135
theorem B439487 : Blo 435777 439487 := bstep (se 1 (by rfl) ⟨329615, by rfl⟩ : syracuseStep 439487 = 659231) B659231
theorem B439655 : Blo 435777 439655 := bstep (se 1 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 439655 = 659483) B659483
theorem B701887 : Blo 435777 701887 := bstep (se 1 (by rfl) ⟨526415, by rfl⟩ : syracuseStep 701887 = 1052831) B1052831
theorem B439759 : Blo 435777 439759 := bstep (se 1 (by rfl) ⟨329819, by rfl⟩ : syracuseStep 439759 = 659639) B659639
theorem B14629085 : Blo 435777 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B12632111 : Blo 435777 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B737417 : Blo 435777 737417 := bstep (se 2 (by rfl) ⟨276531, by rfl⟩ : syracuseStep 737417 = 553063) B553063
theorem B8538047 : Blo 435777 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B18040805 : Blo 435777 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B936191 : Blo 435777 936191 := bstep (se 1 (by rfl) ⟨702143, by rfl⟩ : syracuseStep 936191 = 1404287) B1404287
theorem B3000889 : Blo 435777 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B1658141 : Blo 435777 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B305976851 : Blo 435777 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B12834395 : Blo 435777 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B1890535 : Blo 435777 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1399801 : Blo 435777 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B1662059 : Blo 435777 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B1662227 : Blo 435777 1662227 := bstep (se 1 (by rfl) ⟨1246670, by rfl⟩ : syracuseStep 1662227 = 2493341) B2493341
theorem B450203 : Blo 435777 450203 := bstep (se 1 (by rfl) ⟨337652, by rfl⟩ : syracuseStep 450203 = 675305) B675305
theorem B1105913 : Blo 435777 1105913 := bstep (se 2 (by rfl) ⟨414717, by rfl⟩ : syracuseStep 1105913 = 829435) B829435
theorem B1663199 : Blo 435777 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B46883711 : Blo 435777 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B2745359 : Blo 435777 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B1664489 : Blo 435777 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B3207113 : Blo 435777 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B3273119 : Blo 435777 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B2225069 : Blo 435777 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B12678929 : Blo 435777 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B981179 : Blo 435777 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B1669531 : Blo 435777 1669531 := bstep (se 1 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 1669531 = 2504297) B2504297
theorem B653759 : Blo 435777 653759 := bstep (se 1 (by rfl) ⟨490319, by rfl⟩ : syracuseStep 653759 = 980639) B980639
theorem B14186987 : Blo 435777 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B621103 : Blo 435777 621103 := bstep (se 1 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 621103 = 931655) B931655
theorem B981665 : Blo 435777 981665 := bstep (se 2 (by rfl) ⟨368124, by rfl⟩ : syracuseStep 981665 = 736249) B736249
theorem B1473335 : Blo 435777 1473335 := bstep (se 1 (by rfl) ⟨1105001, by rfl⟩ : syracuseStep 1473335 = 2210003) B2210003
theorem B949225 : Blo 435777 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B654473 : Blo 435777 654473 := bstep (se 2 (by rfl) ⟨245427, by rfl⟩ : syracuseStep 654473 = 490855) B490855
theorem B654575 : Blo 435777 654575 := bstep (se 1 (by rfl) ⟨490931, by rfl⟩ : syracuseStep 654575 = 981863) B981863
theorem B8421407 : Blo 435777 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B491611 : Blo 435777 491611 := bstep (se 1 (by rfl) ⟨368708, by rfl⟩ : syracuseStep 491611 = 737417) B737417
theorem B2359529 : Blo 435777 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B3539483 : Blo 435777 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B1245851 : Blo 435777 1245851 := bstep (se 1 (by rfl) ⟨934388, by rfl⟩ : syracuseStep 1245851 = 1868777) B1868777
theorem B2491631 : Blo 435777 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B12027203 : Blo 435777 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B624127 : Blo 435777 624127 := bstep (se 1 (by rfl) ⟨468095, by rfl⟩ : syracuseStep 624127 = 936191) B936191
theorem B657455 : Blo 435777 657455 := bstep (se 1 (by rfl) ⟨493091, by rfl⟩ : syracuseStep 657455 = 986183) B986183
theorem B985247 : Blo 435777 985247 := bstep (se 1 (by rfl) ⟨738935, by rfl⟩ : syracuseStep 985247 = 1477871) B1477871
theorem B657647 : Blo 435777 657647 := bstep (se 1 (by rfl) ⟨493235, by rfl⟩ : syracuseStep 657647 = 986471) B986471
theorem B72092267 : Blo 435777 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B14224247 : Blo 435777 14224247 := bstep (se 1 (by rfl) ⟨10668185, by rfl⟩ : syracuseStep 14224247 = 21336371) B21336371
theorem B4001185 : Blo 435777 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B658943 : Blo 435777 658943 := bstep (se 1 (by rfl) ⟨494207, by rfl⟩ : syracuseStep 658943 = 988415) B988415
theorem B659081 : Blo 435777 659081 := bstep (se 2 (by rfl) ⟨247155, by rfl⟩ : syracuseStep 659081 = 494311) B494311
theorem B203984567 : Blo 435777 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B8556263 : Blo 435777 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B659369 : Blo 435777 659369 := bstep (se 2 (by rfl) ⟨247263, by rfl⟩ : syracuseStep 659369 = 494527) B494527
theorem B659399 : Blo 435777 659399 := bstep (se 1 (by rfl) ⟨494549, by rfl⟩ : syracuseStep 659399 = 989099) B989099
theorem B987263 : Blo 435777 987263 := bstep (se 1 (by rfl) ⟨740447, by rfl⟩ : syracuseStep 987263 = 1480895) B1480895
theorem B4559417 : Blo 435777 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3150647 : Blo 435777 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1187743 : Blo 435777 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B2138075 : Blo 435777 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B7479539 : Blo 435777 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B1483379 : Blo 435777 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B828137 : Blo 435777 828137 := bstep (se 2 (by rfl) ⟨310551, by rfl⟩ : syracuseStep 828137 = 621103) B621103
theorem B435839 : Blo 435777 435839 := bstep (se 1 (by rfl) ⟨326879, by rfl⟩ : syracuseStep 435839 = 653759) B653759
theorem B436315 : Blo 435777 436315 := bstep (se 1 (by rfl) ⟨327236, by rfl⟩ : syracuseStep 436315 = 654473) B654473
theorem B436383 : Blo 435777 436383 := bstep (se 1 (by rfl) ⟨327287, by rfl⟩ : syracuseStep 436383 = 654575) B654575
theorem B436967 : Blo 435777 436967 := bstep (se 1 (by rfl) ⟨327725, by rfl⟩ : syracuseStep 436967 = 655451) B655451
theorem B7548893 : Blo 435777 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B2210813 : Blo 435777 2210813 := bstep (se 3 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 2210813 = 829055) B829055
theorem B834887 : Blo 435777 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B737275 : Blo 435777 737275 := bstep (se 1 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 737275 = 1105913) B1105913
theorem B20170271 : Blo 435777 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B935849 : Blo 435777 935849 := bstep (se 2 (by rfl) ⟨350943, by rfl⟩ : syracuseStep 935849 = 701887) B701887
theorem B2803855 : Blo 435777 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B2182079 : Blo 435777 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B2215187 : Blo 435777 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B1265633 : Blo 435777 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B9752723 : Blo 435777 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B9457991 : Blo 435777 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B1200541 : Blo 435777 1200541 := bstep (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) B450203
theorem B1660783 : Blo 435777 1660783 := bstep (se 1 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 1660783 = 2491175) B2491175
theorem B1661255 : Blo 435777 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B5692031 : Blo 435777 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B1105427 : Blo 435777 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B10149797 : Blo 435777 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B1108039 : Blo 435777 1108039 := bstep (se 1 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 1108039 = 1662059) B1662059
theorem B1108151 : Blo 435777 1108151 := bstep (se 1 (by rfl) ⟨831113, by rfl⟩ : syracuseStep 1108151 = 1662227) B1662227
theorem B1108799 : Blo 435777 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B31255807 : Blo 435777 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B1830239 : Blo 435777 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1109659 : Blo 435777 1109659 := bstep (se 1 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 1109659 = 1664489) B1664489
theorem B946003 : Blo 435777 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B2520713 : Blo 435777 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B2226041 : Blo 435777 2226041 := bstep (se 2 (by rfl) ⟨834765, by rfl⟩ : syracuseStep 2226041 = 1669531) B1669531
theorem B8452619 : Blo 435777 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B1866401 : Blo 435777 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B654119 : Blo 435777 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B654443 : Blo 435777 654443 := bstep (se 1 (by rfl) ⟨490832, by rfl⟩ : syracuseStep 654443 = 981665) B981665
theorem B982223 : Blo 435777 982223 := bstep (se 1 (by rfl) ⟨736667, by rfl⟩ : syracuseStep 982223 = 1473335) B1473335
theorem B655481 : Blo 435777 655481 := bstep (se 2 (by rfl) ⟨245805, by rfl⟩ : syracuseStep 655481 = 491611) B491611
theorem B1573019 : Blo 435777 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B2359655 : Blo 435777 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B623899 : Blo 435777 623899 := bstep (se 1 (by rfl) ⟨467924, by rfl⟩ : syracuseStep 623899 = 935849) B935849
theorem B656831 : Blo 435777 656831 := bstep (se 1 (by rfl) ⟨492623, by rfl⟩ : syracuseStep 656831 = 985247) B985247
theorem B1476791 : Blo 435777 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B135989711 : Blo 435777 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B5704175 : Blo 435777 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B658175 : Blo 435777 658175 := bstep (se 1 (by rfl) ⟨493631, by rfl⟩ : syracuseStep 658175 = 987263) B987263
theorem B1477385 : Blo 435777 1477385 := bstep (se 2 (by rfl) ⟨554019, by rfl⟩ : syracuseStep 1477385 = 1108039) B1108039
theorem B3738473 : Blo 435777 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B2100431 : Blo 435777 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B1479545 : Blo 435777 1479545 := bstep (se 2 (by rfl) ⟨554829, by rfl⟩ : syracuseStep 1479545 = 1109659) B1109659
theorem B4986359 : Blo 435777 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B988919 : Blo 435777 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1220159 : Blo 435777 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1680475 : Blo 435777 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B1484027 : Blo 435777 1484027 := bstep (se 1 (by rfl) ⟨1113020, by rfl⟩ : syracuseStep 1484027 = 2226041) B2226041
theorem B436079 : Blo 435777 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B436295 : Blo 435777 436295 := bstep (se 1 (by rfl) ⟨327221, by rfl⟩ : syracuseStep 436295 = 654443) B654443
theorem B1583657 : Blo 435777 1583657 := bstep (se 2 (by rfl) ⟨593871, by rfl⟩ : syracuseStep 1583657 = 1187743) B1187743
theorem B5614271 : Blo 435777 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B830567 : Blo 435777 830567 := bstep (se 1 (by rfl) ⟨622925, by rfl⟩ : syracuseStep 830567 = 1245851) B1245851
theorem B13446847 : Blo 435777 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B438303 : Blo 435777 438303 := bstep (se 1 (by rfl) ⟨328727, by rfl⟩ : syracuseStep 438303 = 657455) B657455
theorem B438431 : Blo 435777 438431 := bstep (se 1 (by rfl) ⟨328823, by rfl⟩ : syracuseStep 438431 = 657647) B657647
theorem B9482831 : Blo 435777 9482831 := bstep (se 1 (by rfl) ⟨7112123, by rfl⟩ : syracuseStep 9482831 = 14224247) B14224247
theorem B832169 : Blo 435777 832169 := bstep (se 2 (by rfl) ⟨312063, by rfl⟩ : syracuseStep 832169 = 624127) B624127
theorem B439295 : Blo 435777 439295 := bstep (se 1 (by rfl) ⟨329471, by rfl⟩ : syracuseStep 439295 = 658943) B658943
theorem B439387 : Blo 435777 439387 := bstep (se 1 (by rfl) ⟨329540, by rfl⟩ : syracuseStep 439387 = 659081) B659081
theorem B439579 : Blo 435777 439579 := bstep (se 1 (by rfl) ⟨329684, by rfl⟩ : syracuseStep 439579 = 659369) B659369
theorem B439599 : Blo 435777 439599 := bstep (se 1 (by rfl) ⟨329699, by rfl⟩ : syracuseStep 439599 = 659399) B659399
theorem B6501815 : Blo 435777 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B6305327 : Blo 435777 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B736951 : Blo 435777 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B1261337 : Blo 435777 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B1425383 : Blo 435777 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B738767 : Blo 435777 738767 := bstep (se 1 (by rfl) ⟨554075, by rfl⟩ : syracuseStep 738767 = 1108151) B1108151
theorem B739199 : Blo 435777 739199 := bstep (se 1 (by rfl) ⟨554399, by rfl⟩ : syracuseStep 739199 = 1108799) B1108799
theorem B2214377 : Blo 435777 2214377 := bstep (se 2 (by rfl) ⟨830391, by rfl⟩ : syracuseStep 2214377 = 1660783) B1660783
theorem B5818877 : Blo 435777 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B5032595 : Blo 435777 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B1661087 : Blo 435777 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B8018135 : Blo 435777 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B48061511 : Blo 435777 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B843755 : Blo 435777 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B3039611 : Blo 435777 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B1107503 : Blo 435777 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B41674409 : Blo 435777 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B3794687 : Blo 435777 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B5334913 : Blo 435777 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B552091 : Blo 435777 552091 := bstep (se 1 (by rfl) ⟨414068, by rfl⟩ : syracuseStep 552091 = 828137) B828137
theorem B1600721 : Blo 435777 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B2226365 : Blo 435777 2226365 := bstep (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) B834887
theorem B5635079 : Blo 435777 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B1244267 : Blo 435777 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B1473875 : Blo 435777 1473875 := bstep (se 1 (by rfl) ⟨1105406, by rfl⟩ : syracuseStep 1473875 = 2210813) B2210813
theorem B654815 : Blo 435777 654815 := bstep (se 1 (by rfl) ⟨491111, by rfl⟩ : syracuseStep 654815 = 982223) B982223
theorem B27066125 : Blo 435777 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B983033 : Blo 435777 983033 := bstep (se 2 (by rfl) ⟨368637, by rfl⟩ : syracuseStep 983033 = 737275) B737275
theorem B1048679 : Blo 435777 1048679 := bstep (se 1 (by rfl) ⟨786509, by rfl⟩ : syracuseStep 1048679 = 1573019) B1573019
theorem B1573103 : Blo 435777 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B492511 : Blo 435777 492511 := bstep (se 1 (by rfl) ⟨369383, by rfl⟩ : syracuseStep 492511 = 738767) B738767
theorem B492799 : Blo 435777 492799 := bstep (se 1 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 492799 = 739199) B739199
theorem B984527 : Blo 435777 984527 := bstep (se 1 (by rfl) ⟨738395, by rfl⟩ : syracuseStep 984527 = 1476791) B1476791
theorem B1476251 : Blo 435777 1476251 := bstep (se 1 (by rfl) ⟨1107188, by rfl⟩ : syracuseStep 1476251 = 2214377) B2214377
theorem B3802783 : Blo 435777 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B984923 : Blo 435777 984923 := bstep (se 1 (by rfl) ⟨738692, by rfl⟩ : syracuseStep 984923 = 1477385) B1477385
theorem B2492315 : Blo 435777 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B7113217 : Blo 435777 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B986363 : Blo 435777 986363 := bstep (se 1 (by rfl) ⟨739772, by rfl⟩ : syracuseStep 986363 = 1479545) B1479545
theorem B659279 : Blo 435777 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B5345423 : Blo 435777 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B17929129 : Blo 435777 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B989351 : Blo 435777 989351 := bstep (se 1 (by rfl) ⟨742013, by rfl⟩ : syracuseStep 989351 = 1484027) B1484027
theorem B2529791 : Blo 435777 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B1055771 : Blo 435777 1055771 := bstep (se 1 (by rfl) ⟨791828, by rfl⟩ : syracuseStep 1055771 = 1583657) B1583657
theorem B3742847 : Blo 435777 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B4334543 : Blo 435777 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B4203551 : Blo 435777 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B1484243 : Blo 435777 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B829511 : Blo 435777 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B436543 : Blo 435777 436543 := bstep (se 1 (by rfl) ⟨327407, by rfl⟩ : syracuseStep 436543 = 654815) B654815
theorem B436987 : Blo 435777 436987 := bstep (se 1 (by rfl) ⟨327740, by rfl⟩ : syracuseStep 436987 = 655481) B655481
theorem B437887 : Blo 435777 437887 := bstep (se 1 (by rfl) ⟨328415, by rfl⟩ : syracuseStep 437887 = 656831) B656831
theorem B2240633 : Blo 435777 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B3879251 : Blo 435777 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B831865 : Blo 435777 831865 := bstep (se 2 (by rfl) ⟨311949, by rfl⟩ : syracuseStep 831865 = 623899) B623899
theorem B3355063 : Blo 435777 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B438783 : Blo 435777 438783 := bstep (se 1 (by rfl) ⟨329087, by rfl⟩ : syracuseStep 438783 = 658175) B658175
theorem B3324239 : Blo 435777 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B32422517 : Blo 435777 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B736121 : Blo 435777 736121 := bstep (se 2 (by rfl) ⟨276045, by rfl⟩ : syracuseStep 736121 = 552091) B552091
theorem B738335 : Blo 435777 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B1067147 : Blo 435777 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B3756719 : Blo 435777 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B3363565 : Blo 435777 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B18044083 : Blo 435777 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B2250013 : Blo 435777 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B90659807 : Blo 435777 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B1107391 : Blo 435777 1107391 := bstep (se 1 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 1107391 = 1661087) B1661087
theorem B32041007 : Blo 435777 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B813439 : Blo 435777 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B27782939 : Blo 435777 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B553711 : Blo 435777 553711 := bstep (se 1 (by rfl) ⟨415283, by rfl⟩ : syracuseStep 553711 = 830567) B830567
theorem B6321887 : Blo 435777 6321887 := bstep (se 1 (by rfl) ⟨4741415, by rfl⟩ : syracuseStep 6321887 = 9482831) B9482831
theorem B554779 : Blo 435777 554779 := bstep (se 1 (by rfl) ⟨416084, by rfl⟩ : syracuseStep 554779 = 832169) B832169
theorem B5601149 : Blo 435777 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B982583 : Blo 435777 982583 := bstep (se 1 (by rfl) ⟨736937, by rfl⟩ : syracuseStep 982583 = 1473875) B1473875
theorem B982601 : Blo 435777 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B950255 : Blo 435777 950255 := bstep (se 1 (by rfl) ⟨712691, by rfl⟩ : syracuseStep 950255 = 1425383) B1425383
theorem B655355 : Blo 435777 655355 := bstep (se 1 (by rfl) ⟨491516, by rfl⟩ : syracuseStep 655355 = 983033) B983033
theorem B1048735 : Blo 435777 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B492223 : Blo 435777 492223 := bstep (se 1 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 492223 = 738335) B738335
theorem B656351 : Blo 435777 656351 := bstep (se 1 (by rfl) ⟨492263, by rfl⟩ : syracuseStep 656351 = 984527) B984527
theorem B984167 : Blo 435777 984167 := bstep (se 1 (by rfl) ⟨738125, by rfl⟩ : syracuseStep 984167 = 1476251) B1476251
theorem B656615 : Blo 435777 656615 := bstep (se 1 (by rfl) ⟨492461, by rfl⟩ : syracuseStep 656615 = 984923) B984923
theorem B656681 : Blo 435777 656681 := bstep (se 2 (by rfl) ⟨246255, by rfl⟩ : syracuseStep 656681 = 492511) B492511
theorem B657065 : Blo 435777 657065 := bstep (se 2 (by rfl) ⟨246399, by rfl⟩ : syracuseStep 657065 = 492799) B492799
theorem B1476521 : Blo 435777 1476521 := bstep (se 2 (by rfl) ⟨553695, by rfl⟩ : syracuseStep 1476521 = 1107391) B1107391
theorem B657575 : Blo 435777 657575 := bstep (se 1 (by rfl) ⟨493181, by rfl⟩ : syracuseStep 657575 = 986363) B986363
theorem B17893669 : Blo 435777 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B1084585 : Blo 435777 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B659567 : Blo 435777 659567 := bstep (se 1 (by rfl) ⟨494675, by rfl⟩ : syracuseStep 659567 = 989351) B989351
theorem B2495231 : Blo 435777 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B2889695 : Blo 435777 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B989495 : Blo 435777 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B24058777 : Blo 435777 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B18521959 : Blo 435777 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B633503 : Blo 435777 633503 := bstep (se 1 (by rfl) ⟨475127, by rfl⟩ : syracuseStep 633503 = 950255) B950255
theorem B436903 : Blo 435777 436903 := bstep (se 1 (by rfl) ⟨327677, by rfl⟩ : syracuseStep 436903 = 655355) B655355
theorem B699119 : Blo 435777 699119 := bstep (se 1 (by rfl) ⟨524339, by rfl⟩ : syracuseStep 699119 = 1048679) B1048679
theorem B5975021 : Blo 435777 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B439519 : Blo 435777 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B2504479 : Blo 435777 2504479 := bstep (se 1 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 2504479 = 3756719) B3756719
theorem B9484289 : Blo 435777 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B1686527 : Blo 435777 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B60439871 : Blo 435777 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B703847 : Blo 435777 703847 := bstep (se 1 (by rfl) ⟨527885, by rfl⟩ : syracuseStep 703847 = 1055771) B1055771
theorem B2802367 : Blo 435777 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B738281 : Blo 435777 738281 := bstep (se 2 (by rfl) ⟨276855, by rfl⟩ : syracuseStep 738281 = 553711) B553711
theorem B23905505 : Blo 435777 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B3000017 : Blo 435777 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B739705 : Blo 435777 739705 := bstep (se 2 (by rfl) ⟨277389, by rfl⟩ : syracuseStep 739705 = 554779) B554779
theorem B4214591 : Blo 435777 4214591 := bstep (se 1 (by rfl) ⟨3160943, by rfl⟩ : syracuseStep 4214591 = 6321887) B6321887
theorem B2216159 : Blo 435777 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B21615011 : Blo 435777 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B1661543 : Blo 435777 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B711431 : Blo 435777 711431 := bstep (se 1 (by rfl) ⟨533573, by rfl⟩ : syracuseStep 711431 = 1067147) B1067147
theorem B5070377 : Blo 435777 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B3563615 : Blo 435777 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B1109153 : Blo 435777 1109153 := bstep (se 2 (by rfl) ⟨415932, by rfl⟩ : syracuseStep 1109153 = 831865) B831865
theorem B4484753 : Blo 435777 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B21360671 : Blo 435777 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B553007 : Blo 435777 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B2586167 : Blo 435777 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B3734099 : Blo 435777 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B490747 : Blo 435777 490747 := bstep (se 1 (by rfl) ⟨368060, by rfl⟩ : syracuseStep 490747 = 736121) B736121
theorem B655055 : Blo 435777 655055 := bstep (se 1 (by rfl) ⟨491291, by rfl⟩ : syracuseStep 655055 = 982583) B982583
theorem B655067 : Blo 435777 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B1474685 : Blo 435777 1474685 := bstep (se 3 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 1474685 = 553007) B553007
theorem B492187 : Blo 435777 492187 := bstep (se 1 (by rfl) ⟨369140, by rfl⟩ : syracuseStep 492187 = 738281) B738281
theorem B656111 : Blo 435777 656111 := bstep (se 1 (by rfl) ⟨492083, by rfl⟩ : syracuseStep 656111 = 984167) B984167
theorem B3736489 : Blo 435777 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B656297 : Blo 435777 656297 := bstep (se 2 (by rfl) ⟨246111, by rfl⟩ : syracuseStep 656297 = 492223) B492223
theorem B984347 : Blo 435777 984347 := bstep (se 1 (by rfl) ⟨738260, by rfl⟩ : syracuseStep 984347 = 1476521) B1476521
theorem B1477439 : Blo 435777 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B23858225 : Blo 435777 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B986273 : Blo 435777 986273 := bstep (se 2 (by rfl) ⟨369852, by rfl⟩ : syracuseStep 986273 = 739705) B739705
theorem B659663 : Blo 435777 659663 := bstep (se 1 (by rfl) ⟨494747, by rfl⟩ : syracuseStep 659663 = 989495) B989495
theorem B1446113 : Blo 435777 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B8000045 : Blo 435777 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B466079 : Blo 435777 466079 := bstep (se 1 (by rfl) ⟨349559, by rfl⟩ : syracuseStep 466079 = 699119) B699119
theorem B2989835 : Blo 435777 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B1876925 : Blo 435777 1876925 := bstep (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) B703847
theorem B1124351 : Blo 435777 1124351 := bstep (se 1 (by rfl) ⟨843263, by rfl⟩ : syracuseStep 1124351 = 1686527) B1686527
theorem B436703 : Blo 435777 436703 := bstep (se 1 (by rfl) ⟨327527, by rfl⟩ : syracuseStep 436703 = 655055) B655055
theorem B436711 : Blo 435777 436711 := bstep (se 1 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 436711 = 655067) B655067
theorem B437567 : Blo 435777 437567 := bstep (se 1 (by rfl) ⟨328175, by rfl⟩ : syracuseStep 437567 = 656351) B656351
theorem B15937003 : Blo 435777 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B437743 : Blo 435777 437743 := bstep (se 1 (by rfl) ⟨328307, by rfl⟩ : syracuseStep 437743 = 656615) B656615
theorem B437787 : Blo 435777 437787 := bstep (se 1 (by rfl) ⟨328340, by rfl⟩ : syracuseStep 437787 = 656681) B656681
theorem B438043 : Blo 435777 438043 := bstep (se 1 (by rfl) ⟨328532, by rfl⟩ : syracuseStep 438043 = 657065) B657065
theorem B438383 : Blo 435777 438383 := bstep (se 1 (by rfl) ⟨328787, by rfl⟩ : syracuseStep 438383 = 657575) B657575
theorem B439711 : Blo 435777 439711 := bstep (se 1 (by rfl) ⟨329783, by rfl⟩ : syracuseStep 439711 = 659567) B659567
theorem B474287 : Blo 435777 474287 := bstep (se 1 (by rfl) ⟨355715, by rfl⟩ : syracuseStep 474287 = 711431) B711431
theorem B2375743 : Blo 435777 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B1689341 : Blo 435777 1689341 := bstep (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) B633503
theorem B3983347 : Blo 435777 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B739435 : Blo 435777 739435 := bstep (se 1 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 739435 = 1109153) B1109153
theorem B14240447 : Blo 435777 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B1724111 : Blo 435777 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B13521005 : Blo 435777 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B40293247 : Blo 435777 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B24695945 : Blo 435777 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B1398313 : Blo 435777 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B2809727 : Blo 435777 2809727 := bstep (se 1 (by rfl) ⟨2107295, by rfl⟩ : syracuseStep 2809727 = 4214591) B4214591
theorem B14410007 : Blo 435777 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B1663487 : Blo 435777 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B1926463 : Blo 435777 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B1107695 : Blo 435777 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B3339305 : Blo 435777 3339305 := bstep (se 2 (by rfl) ⟨1252239, by rfl⟩ : syracuseStep 3339305 = 2504479) B2504479
theorem B32078369 : Blo 435777 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B6322859 : Blo 435777 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B654329 : Blo 435777 654329 := bstep (se 2 (by rfl) ⟨245373, by rfl⟩ : syracuseStep 654329 = 490747) B490747
theorem B2489399 : Blo 435777 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B983123 : Blo 435777 983123 := bstep (se 1 (by rfl) ⟨737342, by rfl⟩ : syracuseStep 983123 = 1474685) B1474685
theorem B656231 : Blo 435777 656231 := bstep (se 1 (by rfl) ⟨492173, by rfl⟩ : syracuseStep 656231 = 984347) B984347
theorem B656249 : Blo 435777 656249 := bstep (se 2 (by rfl) ⟨246093, by rfl⟩ : syracuseStep 656249 = 492187) B492187
theorem B4981985 : Blo 435777 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B984959 : Blo 435777 984959 := bstep (se 1 (by rfl) ⟨738719, by rfl⟩ : syracuseStep 984959 = 1477439) B1477439
theorem B657515 : Blo 435777 657515 := bstep (se 1 (by rfl) ⟨493136, by rfl⟩ : syracuseStep 657515 = 986273) B986273
theorem B1149407 : Blo 435777 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B5311129 : Blo 435777 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B9014003 : Blo 435777 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B985913 : Blo 435777 985913 := bstep (se 2 (by rfl) ⟨369717, by rfl⟩ : syracuseStep 985913 = 739435) B739435
theorem B1873151 : Blo 435777 1873151 := bstep (se 1 (by rfl) ⟨1404863, by rfl⟩ : syracuseStep 1873151 = 2809727) B2809727
theorem B9606671 : Blo 435777 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B1251283 : Blo 435777 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B436219 : Blo 435777 436219 := bstep (se 1 (by rfl) ⟨327164, by rfl⟩ : syracuseStep 436219 = 654329) B654329
theorem B437407 : Blo 435777 437407 := bstep (se 1 (by rfl) ⟨328055, by rfl⟩ : syracuseStep 437407 = 656111) B656111
theorem B437531 : Blo 435777 437531 := bstep (se 1 (by rfl) ⟨328148, by rfl⟩ : syracuseStep 437531 = 656297) B656297
theorem B2568617 : Blo 435777 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B15905483 : Blo 435777 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B439775 : Blo 435777 439775 := bstep (se 1 (by rfl) ⟨329831, by rfl⟩ : syracuseStep 439775 = 659663) B659663
theorem B964075 : Blo 435777 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B16463963 : Blo 435777 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B21249337 : Blo 435777 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B4504909 : Blo 435777 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B738463 : Blo 435777 738463 := bstep (se 1 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 738463 = 1107695) B1107695
theorem B53724329 : Blo 435777 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B7457669 : Blo 435777 7457669 := bstep (se 4 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 7457669 = 1398313) B1398313
theorem B1264765 : Blo 435777 1264765 := bstep (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) B474287
theorem B21385579 : Blo 435777 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B4215239 : Blo 435777 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B1659599 : Blo 435777 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B3167657 : Blo 435777 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B9493631 : Blo 435777 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B5333363 : Blo 435777 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B1993223 : Blo 435777 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B1108991 : Blo 435777 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B749567 : Blo 435777 749567 := bstep (se 1 (by rfl) ⟨562175, by rfl⟩ : syracuseStep 749567 = 1124351) B1124351
theorem B1242877 : Blo 435777 1242877 := bstep (se 3 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 1242877 = 466079) B466079
theorem B2226203 : Blo 435777 2226203 := bstep (se 1 (by rfl) ⟨1669652, by rfl⟩ : syracuseStep 2226203 = 3339305) B3339305
theorem B655415 : Blo 435777 655415 := bstep (se 1 (by rfl) ⟨491561, by rfl⟩ : syracuseStep 655415 = 983123) B983123
theorem B35816219 : Blo 435777 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B656639 : Blo 435777 656639 := bstep (se 1 (by rfl) ⟨492479, by rfl⟩ : syracuseStep 656639 = 984959) B984959
theorem B984617 : Blo 435777 984617 := bstep (se 2 (by rfl) ⟨369231, by rfl⟩ : syracuseStep 984617 = 738463) B738463
theorem B657275 : Blo 435777 657275 := bstep (se 1 (by rfl) ⟨492956, by rfl⟩ : syracuseStep 657275 = 985913) B985913
theorem B1248767 : Blo 435777 1248767 := bstep (se 1 (by rfl) ⟨936575, by rfl⟩ : syracuseStep 1248767 = 1873151) B1873151
theorem B7081505 : Blo 435777 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B6329087 : Blo 435777 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B28514105 : Blo 435777 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B1285433 : Blo 435777 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B499711 : Blo 435777 499711 := bstep (se 1 (by rfl) ⟨374783, by rfl⟩ : syracuseStep 499711 = 749567) B749567
theorem B1712411 : Blo 435777 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B1484135 : Blo 435777 1484135 := bstep (se 1 (by rfl) ⟨1113101, by rfl⟩ : syracuseStep 1484135 = 2226203) B2226203
theorem B6006545 : Blo 435777 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B437487 : Blo 435777 437487 := bstep (se 1 (by rfl) ⟨328115, by rfl⟩ : syracuseStep 437487 = 656231) B656231
theorem B437499 : Blo 435777 437499 := bstep (se 1 (by rfl) ⟨328124, by rfl⟩ : syracuseStep 437499 = 656249) B656249
theorem B3321323 : Blo 435777 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B438343 : Blo 435777 438343 := bstep (se 1 (by rfl) ⟨328757, by rfl⟩ : syracuseStep 438343 = 657515) B657515
theorem B766271 : Blo 435777 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B6009335 : Blo 435777 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B2111771 : Blo 435777 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B6404447 : Blo 435777 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B1686353 : Blo 435777 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B3555575 : Blo 435777 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B1328815 : Blo 435777 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B739327 : Blo 435777 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B1657169 : Blo 435777 1657169 := bstep (se 2 (by rfl) ⟨621438, by rfl⟩ : syracuseStep 1657169 = 1242877) B1242877
theorem B10603655 : Blo 435777 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B28332449 : Blo 435777 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B4971779 : Blo 435777 4971779 := bstep (se 1 (by rfl) ⟨3728834, by rfl⟩ : syracuseStep 4971779 = 7457669) B7457669
theorem B2810159 : Blo 435777 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B1106399 : Blo 435777 1106399 := bstep (se 1 (by rfl) ⟨829799, by rfl⟩ : syracuseStep 1106399 = 1659599) B1659599
theorem B1668377 : Blo 435777 1668377 := bstep (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) B1251283
theorem B10975975 : Blo 435777 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B656411 : Blo 435777 656411 := bstep (se 1 (by rfl) ⟨492308, by rfl⟩ : syracuseStep 656411 = 984617) B984617
theorem B1771753 : Blo 435777 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B4721003 : Blo 435777 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B985769 : Blo 435777 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B19009403 : Blo 435777 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B3314519 : Blo 435777 3314519 := bstep (se 1 (by rfl) ⟨2485889, by rfl⟩ : syracuseStep 3314519 = 4971779) B4971779
theorem B856955 : Blo 435777 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B1873439 : Blo 435777 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B989423 : Blo 435777 989423 := bstep (se 1 (by rfl) ⟨742067, by rfl⟩ : syracuseStep 989423 = 1484135) B1484135
theorem B17078525 : Blo 435777 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B4004363 : Blo 435777 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B4496941 : Blo 435777 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B4006223 : Blo 435777 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B666281 : Blo 435777 666281 := bstep (se 2 (by rfl) ⟨249855, by rfl⟩ : syracuseStep 666281 = 499711) B499711
theorem B436943 : Blo 435777 436943 := bstep (se 1 (by rfl) ⟨327707, by rfl⟩ : syracuseStep 436943 = 655415) B655415
theorem B2370383 : Blo 435777 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B2043389 : Blo 435777 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B437759 : Blo 435777 437759 := bstep (se 1 (by rfl) ⟨328319, by rfl⟩ : syracuseStep 437759 = 656639) B656639
theorem B438183 : Blo 435777 438183 := bstep (se 1 (by rfl) ⟨328637, by rfl⟩ : syracuseStep 438183 = 657275) B657275
theorem B832511 : Blo 435777 832511 := bstep (se 1 (by rfl) ⟨624383, by rfl⟩ : syracuseStep 832511 = 1248767) B1248767
theorem B18888299 : Blo 435777 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B58538533 : Blo 435777 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B737599 : Blo 435777 737599 := bstep (se 1 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 737599 = 1106399) B1106399
theorem B2214215 : Blo 435777 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B23877479 : Blo 435777 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B1104779 : Blo 435777 1104779 := bstep (se 1 (by rfl) ⟨828584, by rfl⟩ : syracuseStep 1104779 = 1657169) B1657169
theorem B7069103 : Blo 435777 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B4219391 : Blo 435777 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B1141607 : Blo 435777 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B5631389 : Blo 435777 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B1112251 : Blo 435777 1112251 := bstep (se 1 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 1112251 = 1668377) B1668377
theorem B983465 : Blo 435777 983465 := bstep (se 2 (by rfl) ⟨368799, by rfl⟩ : syracuseStep 983465 = 737599) B737599
theorem B1476143 : Blo 435777 1476143 := bstep (se 1 (by rfl) ⟨1107107, by rfl⟩ : syracuseStep 1476143 = 2214215) B2214215
theorem B3147335 : Blo 435777 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B657179 : Blo 435777 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B2362337 : Blo 435777 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B1248959 : Blo 435777 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B659615 : Blo 435777 659615 := bstep (se 1 (by rfl) ⟨494711, by rfl⟩ : syracuseStep 659615 = 989423) B989423
theorem B1580255 : Blo 435777 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B761071 : Blo 435777 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B1483001 : Blo 435777 1483001 := bstep (se 2 (by rfl) ⟨556125, by rfl⟩ : syracuseStep 1483001 = 1112251) B1112251
theorem B12592199 : Blo 435777 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B5449037 : Blo 435777 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B437607 : Blo 435777 437607 := bstep (se 1 (by rfl) ⟨328205, by rfl⟩ : syracuseStep 437607 = 656411) B656411
theorem B2209679 : Blo 435777 2209679 := bstep (se 1 (by rfl) ⟨1657259, by rfl⟩ : syracuseStep 2209679 = 3314519) B3314519
theorem B571303 : Blo 435777 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B11385683 : Blo 435777 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B736519 : Blo 435777 736519 := bstep (se 1 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 736519 = 1104779) B1104779
theorem B2670815 : Blo 435777 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B444187 : Blo 435777 444187 := bstep (se 1 (by rfl) ⟨333140, by rfl⟩ : syracuseStep 444187 = 666281) B666281
theorem B3754259 : Blo 435777 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B12672935 : Blo 435777 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B15918319 : Blo 435777 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B4712735 : Blo 435777 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B2812927 : Blo 435777 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B10678301 : Blo 435777 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B23983685 : Blo 435777 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B555007 : Blo 435777 555007 := bstep (se 1 (by rfl) ⟨416255, by rfl⟩ : syracuseStep 555007 = 832511) B832511
theorem B78051377 : Blo 435777 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B655643 : Blo 435777 655643 := bstep (se 1 (by rfl) ⟨491732, by rfl⟩ : syracuseStep 655643 = 983465) B983465
theorem B984095 : Blo 435777 984095 := bstep (se 1 (by rfl) ⟨738071, by rfl⟩ : syracuseStep 984095 = 1476143) B1476143
theorem B2098223 : Blo 435777 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B1574891 : Blo 435777 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1053503 : Blo 435777 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B988667 : Blo 435777 988667 := bstep (se 1 (by rfl) ⟨741500, by rfl⟩ : syracuseStep 988667 = 1483001) B1483001
theorem B8394799 : Blo 435777 8394799 := bstep (se 1 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 8394799 = 12592199) B12592199
theorem B761737 : Blo 435777 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B7118867 : Blo 435777 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B2368997 : Blo 435777 2368997 := bstep (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) B444187
theorem B1780543 : Blo 435777 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B438119 : Blo 435777 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B2502839 : Blo 435777 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B439743 : Blo 435777 439743 := bstep (se 1 (by rfl) ⟨329807, by rfl⟩ : syracuseStep 439743 = 659615) B659615
theorem B14530765 : Blo 435777 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B3750569 : Blo 435777 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B740009 : Blo 435777 740009 := bstep (se 2 (by rfl) ⟨277503, by rfl⟩ : syracuseStep 740009 = 555007) B555007
theorem B3330557 : Blo 435777 3330557 := bstep (se 3 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 3330557 = 1248959) B1248959
theorem B7590455 : Blo 435777 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B21224425 : Blo 435777 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B8448623 : Blo 435777 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B3141823 : Blo 435777 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B15989123 : Blo 435777 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B1473119 : Blo 435777 1473119 := bstep (se 1 (by rfl) ⟨1104839, by rfl⟩ : syracuseStep 1473119 = 2209679) B2209679
theorem B52034251 : Blo 435777 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B1014761 : Blo 435777 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B982025 : Blo 435777 982025 := bstep (se 2 (by rfl) ⟨368259, by rfl⟩ : syracuseStep 982025 = 736519) B736519
theorem B656063 : Blo 435777 656063 := bstep (se 1 (by rfl) ⟨492047, by rfl⟩ : syracuseStep 656063 = 984095) B984095
theorem B1049927 : Blo 435777 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B493339 : Blo 435777 493339 := bstep (se 1 (by rfl) ⟨370004, by rfl⟩ : syracuseStep 493339 = 740009) B740009
theorem B659111 : Blo 435777 659111 := bstep (se 1 (by rfl) ⟨494333, by rfl⟩ : syracuseStep 659111 = 988667) B988667
theorem B1579331 : Blo 435777 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B42637661 : Blo 435777 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B19374353 : Blo 435777 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B69379001 : Blo 435777 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B2500379 : Blo 435777 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B437095 : Blo 435777 437095 := bstep (se 1 (by rfl) ⟨327821, by rfl⟩ : syracuseStep 437095 = 655643) B655643
theorem B5060303 : Blo 435777 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B702335 : Blo 435777 702335 := bstep (se 1 (by rfl) ⟨526751, by rfl⟩ : syracuseStep 702335 = 1053503) B1053503
theorem B2374057 : Blo 435777 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B11193065 : Blo 435777 11193065 := bstep (se 2 (by rfl) ⟨4197399, by rfl⟩ : syracuseStep 11193065 = 8394799) B8394799
theorem B28299233 : Blo 435777 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B676507 : Blo 435777 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B1398815 : Blo 435777 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B2220371 : Blo 435777 2220371 := bstep (se 1 (by rfl) ⟨1665278, by rfl⟩ : syracuseStep 2220371 = 3330557) B3330557
theorem B4745911 : Blo 435777 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B4189097 : Blo 435777 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B5632415 : Blo 435777 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B1668559 : Blo 435777 1668559 := bstep (se 1 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 1668559 = 2502839) B2502839
theorem B982079 : Blo 435777 982079 := bstep (se 1 (by rfl) ⟨736559, by rfl⟩ : syracuseStep 982079 = 1473119) B1473119
theorem B654683 : Blo 435777 654683 := bstep (se 1 (by rfl) ⟨491012, by rfl⟩ : syracuseStep 654683 = 982025) B982025
theorem B1015649 : Blo 435777 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B657785 : Blo 435777 657785 := bstep (se 2 (by rfl) ⟨246669, by rfl⟩ : syracuseStep 657785 = 493339) B493339
theorem B6327881 : Blo 435777 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B1052887 : Blo 435777 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B12916235 : Blo 435777 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B1480247 : Blo 435777 1480247 := bstep (se 1 (by rfl) ⟨1110185, by rfl⟩ : syracuseStep 1480247 = 2220371) B2220371
theorem B2792731 : Blo 435777 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B468223 : Blo 435777 468223 := bstep (se 1 (by rfl) ⟨351167, by rfl⟩ : syracuseStep 468223 = 702335) B702335
theorem B436455 : Blo 435777 436455 := bstep (se 1 (by rfl) ⟨327341, by rfl⟩ : syracuseStep 436455 = 654683) B654683
theorem B437375 : Blo 435777 437375 := bstep (se 1 (by rfl) ⟨328031, by rfl⟩ : syracuseStep 437375 = 656063) B656063
theorem B439407 : Blo 435777 439407 := bstep (se 1 (by rfl) ⟨329555, by rfl⟩ : syracuseStep 439407 = 659111) B659111
theorem B2799805 : Blo 435777 2799805 := bstep (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) B1049927
theorem B932543 : Blo 435777 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B28425107 : Blo 435777 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B46252667 : Blo 435777 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B902009 : Blo 435777 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B3754943 : Blo 435777 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B3165409 : Blo 435777 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B677099 : Blo 435777 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B7462043 : Blo 435777 7462043 := bstep (se 1 (by rfl) ⟨5596532, by rfl⟩ : syracuseStep 7462043 = 11193065) B11193065
theorem B18866155 : Blo 435777 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B1666919 : Blo 435777 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B2224745 : Blo 435777 2224745 := bstep (se 2 (by rfl) ⟨834279, by rfl⟩ : syracuseStep 2224745 = 1668559) B1668559
theorem B3373535 : Blo 435777 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B654719 : Blo 435777 654719 := bstep (se 1 (by rfl) ⟨491039, by rfl⟩ : syracuseStep 654719 = 982079) B982079
theorem B123340445 : Blo 435777 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B1805597 : Blo 435777 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B986831 : Blo 435777 986831 := bstep (se 1 (by rfl) ⟨740123, by rfl⟩ : syracuseStep 986831 = 1480247) B1480247
theorem B2497189 : Blo 435777 2497189 := bstep (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) B468223
theorem B1483163 : Blo 435777 1483163 := bstep (se 1 (by rfl) ⟨1112372, by rfl⟩ : syracuseStep 1483163 = 2224745) B2224745
theorem B18950071 : Blo 435777 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B436479 : Blo 435777 436479 := bstep (se 1 (by rfl) ⟨327359, by rfl⟩ : syracuseStep 436479 = 654719) B654719
theorem B601339 : Blo 435777 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B438523 : Blo 435777 438523 := bstep (se 1 (by rfl) ⟨328892, by rfl⟩ : syracuseStep 438523 = 657785) B657785
theorem B2503295 : Blo 435777 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B8996093 : Blo 435777 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B3723641 : Blo 435777 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B25154873 : Blo 435777 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B4218587 : Blo 435777 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B8610823 : Blo 435777 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B4220545 : Blo 435777 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B4974695 : Blo 435777 4974695 := bstep (se 1 (by rfl) ⟨3731021, by rfl⟩ : syracuseStep 4974695 = 7462043) B7462043
theorem B1403849 : Blo 435777 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B1111279 : Blo 435777 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B3733073 : Blo 435777 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B621695 : Blo 435777 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B5997395 : Blo 435777 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B657887 : Blo 435777 657887 := bstep (se 1 (by rfl) ⟨493415, by rfl⟩ : syracuseStep 657887 = 986831) B986831
theorem B25266761 : Blo 435777 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B988775 : Blo 435777 988775 := bstep (se 1 (by rfl) ⟨741581, by rfl⟩ : syracuseStep 988775 = 1483163) B1483163
theorem B3316463 : Blo 435777 3316463 := bstep (se 1 (by rfl) ⟨2487347, by rfl⟩ : syracuseStep 3316463 = 4974695) B4974695
theorem B1481705 : Blo 435777 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B3743597 : Blo 435777 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B82226963 : Blo 435777 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B11481097 : Blo 435777 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B801785 : Blo 435777 801785 := bstep (se 2 (by rfl) ⟨300669, by rfl⟩ : syracuseStep 801785 = 601339) B601339
theorem B1657853 : Blo 435777 1657853 := bstep (se 3 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 1657853 = 621695) B621695
theorem B3329585 : Blo 435777 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B5627393 : Blo 435777 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B1203731 : Blo 435777 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B2482427 : Blo 435777 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B16769915 : Blo 435777 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B2812391 : Blo 435777 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B1668863 : Blo 435777 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B2488715 : Blo 435777 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B16844507 : Blo 435777 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B15993053 : Blo 435777 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B659183 : Blo 435777 659183 := bstep (se 1 (by rfl) ⟨494387, by rfl⟩ : syracuseStep 659183 = 988775) B988775
theorem B987803 : Blo 435777 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B2495731 : Blo 435777 2495731 := bstep (se 1 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 2495731 = 3743597) B3743597
theorem B15308129 : Blo 435777 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B11179943 : Blo 435777 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B1874927 : Blo 435777 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B534523 : Blo 435777 534523 := bstep (se 1 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 534523 = 801785) B801785
theorem B438591 : Blo 435777 438591 := bstep (se 1 (by rfl) ⟨328943, by rfl⟩ : syracuseStep 438591 = 657887) B657887
theorem B2210975 : Blo 435777 2210975 := bstep (se 1 (by rfl) ⟨1658231, by rfl⟩ : syracuseStep 2210975 = 3316463) B3316463
theorem B3751595 : Blo 435777 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B802487 : Blo 435777 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B1654951 : Blo 435777 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B1659143 : Blo 435777 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B1105235 : Blo 435777 1105235 := bstep (se 1 (by rfl) ⟨828926, by rfl⟩ : syracuseStep 1105235 = 1657853) B1657853
theorem B2219723 : Blo 435777 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B54817975 : Blo 435777 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B1112575 : Blo 435777 1112575 := bstep (se 1 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 1112575 = 1668863) B1668863
theorem B658535 : Blo 435777 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B1249951 : Blo 435777 1249951 := bstep (se 1 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 1249951 = 1874927) B1874927
theorem B1479815 : Blo 435777 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B1483433 : Blo 435777 1483433 := bstep (se 2 (by rfl) ⟨556287, by rfl⟩ : syracuseStep 1483433 = 1112575) B1112575
theorem B2139965 : Blo 435777 2139965 := bstep (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) B802487
theorem B2501063 : Blo 435777 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B2206601 : Blo 435777 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B10662035 : Blo 435777 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B439455 : Blo 435777 439455 := bstep (se 1 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 439455 = 659183) B659183
theorem B7453295 : Blo 435777 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B736823 : Blo 435777 736823 := bstep (se 1 (by rfl) ⟨552617, by rfl⟩ : syracuseStep 736823 = 1105235) B1105235
theorem B73090633 : Blo 435777 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B3327641 : Blo 435777 3327641 := bstep (se 2 (by rfl) ⟨1247865, by rfl⟩ : syracuseStep 3327641 = 2495731) B2495731
theorem B11229671 : Blo 435777 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B712697 : Blo 435777 712697 := bstep (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) B534523
theorem B1106095 : Blo 435777 1106095 := bstep (se 1 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 1106095 = 1659143) B1659143
theorem B40821677 : Blo 435777 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B1473983 : Blo 435777 1473983 := bstep (se 1 (by rfl) ⟨1105487, by rfl⟩ : syracuseStep 1473983 = 2210975) B2210975
theorem B1474793 : Blo 435777 1474793 := bstep (se 2 (by rfl) ⟨553047, by rfl⟩ : syracuseStep 1474793 = 1106095) B1106095
theorem B97454177 : Blo 435777 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B986543 : Blo 435777 986543 := bstep (se 1 (by rfl) ⟨739907, by rfl⟩ : syracuseStep 986543 = 1479815) B1479815
theorem B988955 : Blo 435777 988955 := bstep (se 1 (by rfl) ⟨741716, by rfl⟩ : syracuseStep 988955 = 1483433) B1483433
theorem B439023 : Blo 435777 439023 := bstep (se 1 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 439023 = 658535) B658535
theorem B7486447 : Blo 435777 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B27214451 : Blo 435777 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B1426643 : Blo 435777 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B4968863 : Blo 435777 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B28432093 : Blo 435777 28432093 := bstep (se 3 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 28432093 = 10662035) B10662035
theorem B2218427 : Blo 435777 2218427 := bstep (se 1 (by rfl) ⟨1663820, by rfl⟩ : syracuseStep 2218427 = 3327641) B3327641
theorem B1666601 : Blo 435777 1666601 := bstep (se 2 (by rfl) ⟨624975, by rfl⟩ : syracuseStep 1666601 = 1249951) B1249951
theorem B1667375 : Blo 435777 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B1471067 : Blo 435777 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B982655 : Blo 435777 982655 := bstep (se 1 (by rfl) ⟨736991, by rfl⟩ : syracuseStep 982655 = 1473983) B1473983
theorem B491215 : Blo 435777 491215 := bstep (se 1 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 491215 = 736823) B736823
theorem B1900525 : Blo 435777 1900525 := bstep (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) B712697
theorem B983195 : Blo 435777 983195 := bstep (se 1 (by rfl) ⟨737396, by rfl⟩ : syracuseStep 983195 = 1474793) B1474793
theorem B951095 : Blo 435777 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B657695 : Blo 435777 657695 := bstep (se 1 (by rfl) ⟨493271, by rfl⟩ : syracuseStep 657695 = 986543) B986543
theorem B3312575 : Blo 435777 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B659303 : Blo 435777 659303 := bstep (se 1 (by rfl) ⟨494477, by rfl⟩ : syracuseStep 659303 = 988955) B988955
theorem B1478951 : Blo 435777 1478951 := bstep (se 1 (by rfl) ⟨1109213, by rfl⟩ : syracuseStep 1478951 = 2218427) B2218427
theorem B2534033 : Blo 435777 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B9981929 : Blo 435777 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B18142967 : Blo 435777 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B64969451 : Blo 435777 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B37909457 : Blo 435777 37909457 := bstep (se 2 (by rfl) ⟨14216046, by rfl⟩ : syracuseStep 37909457 = 28432093) B28432093
theorem B1111067 : Blo 435777 1111067 := bstep (se 1 (by rfl) ⟨833300, by rfl⟩ : syracuseStep 1111067 = 1666601) B1666601
theorem B1111583 : Blo 435777 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B980711 : Blo 435777 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B654953 : Blo 435777 654953 := bstep (se 2 (by rfl) ⟨245607, by rfl⟩ : syracuseStep 654953 = 491215) B491215
theorem B655103 : Blo 435777 655103 := bstep (se 1 (by rfl) ⟨491327, by rfl⟩ : syracuseStep 655103 = 982655) B982655
theorem B655463 : Blo 435777 655463 := bstep (se 1 (by rfl) ⟨491597, by rfl⟩ : syracuseStep 655463 = 983195) B983195
theorem B6654619 : Blo 435777 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B985967 : Blo 435777 985967 := bstep (se 1 (by rfl) ⟨739475, by rfl⟩ : syracuseStep 985967 = 1478951) B1478951
theorem B25272971 : Blo 435777 25272971 := bstep (se 1 (by rfl) ⟨18954728, by rfl⟩ : syracuseStep 25272971 = 37909457) B37909457
theorem B436635 : Blo 435777 436635 := bstep (se 1 (by rfl) ⟨327476, by rfl⟩ : syracuseStep 436635 = 654953) B654953
theorem B436735 : Blo 435777 436735 := bstep (se 1 (by rfl) ⟨327551, by rfl⟩ : syracuseStep 436735 = 655103) B655103
theorem B634063 : Blo 435777 634063 := bstep (se 1 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 634063 = 951095) B951095
theorem B438463 : Blo 435777 438463 := bstep (se 1 (by rfl) ⟨328847, by rfl⟩ : syracuseStep 438463 = 657695) B657695
theorem B2208383 : Blo 435777 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B439535 : Blo 435777 439535 := bstep (se 1 (by rfl) ⟨329651, by rfl⟩ : syracuseStep 439535 = 659303) B659303
theorem B48381245 : Blo 435777 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1689355 : Blo 435777 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B740711 : Blo 435777 740711 := bstep (se 1 (by rfl) ⟨555533, by rfl⟩ : syracuseStep 740711 = 1111067) B1111067
theorem B741055 : Blo 435777 741055 := bstep (se 1 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 741055 = 1111583) B1111583
theorem B43312967 : Blo 435777 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B653807 : Blo 435777 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B657311 : Blo 435777 657311 := bstep (se 1 (by rfl) ⟨492983, by rfl⟩ : syracuseStep 657311 = 985967) B985967
theorem B493807 : Blo 435777 493807 := bstep (se 1 (by rfl) ⟨370355, by rfl⟩ : syracuseStep 493807 = 740711) B740711
theorem B35491301 : Blo 435777 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B988073 : Blo 435777 988073 := bstep (se 2 (by rfl) ⟨370527, by rfl⟩ : syracuseStep 988073 = 741055) B741055
theorem B16848647 : Blo 435777 16848647 := bstep (se 1 (by rfl) ⟨12636485, by rfl⟩ : syracuseStep 16848647 = 25272971) B25272971
theorem B28875311 : Blo 435777 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B435871 : Blo 435777 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B32254163 : Blo 435777 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B436975 : Blo 435777 436975 := bstep (se 1 (by rfl) ⟨327731, by rfl⟩ : syracuseStep 436975 = 655463) B655463
theorem B845417 : Blo 435777 845417 := bstep (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) B634063
theorem B1472255 : Blo 435777 1472255 := bstep (se 1 (by rfl) ⟨1104191, by rfl⟩ : syracuseStep 1472255 = 2208383) B2208383
theorem B9009893 : Blo 435777 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B23660867 : Blo 435777 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B658409 : Blo 435777 658409 := bstep (se 2 (by rfl) ⟨246903, by rfl⟩ : syracuseStep 658409 = 493807) B493807
theorem B658715 : Blo 435777 658715 := bstep (se 1 (by rfl) ⟨494036, by rfl⟩ : syracuseStep 658715 = 988073) B988073
theorem B21502775 : Blo 435777 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B24026381 : Blo 435777 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B438207 : Blo 435777 438207 := bstep (se 1 (by rfl) ⟨328655, by rfl⟩ : syracuseStep 438207 = 657311) B657311
theorem B19250207 : Blo 435777 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B11232431 : Blo 435777 11232431 := bstep (se 1 (by rfl) ⟨8424323, by rfl⟩ : syracuseStep 11232431 = 16848647) B16848647
theorem B2254445 : Blo 435777 2254445 := bstep (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) B845417
theorem B981503 : Blo 435777 981503 := bstep (se 1 (by rfl) ⟨736127, by rfl⟩ : syracuseStep 981503 = 1472255) B1472255
theorem B438939 : Blo 435777 438939 := bstep (se 1 (by rfl) ⟨329204, by rfl⟩ : syracuseStep 438939 = 658409) B658409
theorem B439143 : Blo 435777 439143 := bstep (se 1 (by rfl) ⟨329357, by rfl⟩ : syracuseStep 439143 = 658715) B658715
theorem B14335183 : Blo 435777 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B7488287 : Blo 435777 7488287 := bstep (se 1 (by rfl) ⟨5616215, by rfl⟩ : syracuseStep 7488287 = 11232431) B11232431
theorem B63095645 : Blo 435777 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B12833471 : Blo 435777 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B16017587 : Blo 435777 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B1502963 : Blo 435777 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B654335 : Blo 435777 654335 := bstep (se 1 (by rfl) ⟨490751, by rfl⟩ : syracuseStep 654335 = 981503) B981503
theorem B8555647 : Blo 435777 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B19113577 : Blo 435777 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B436223 : Blo 435777 436223 := bstep (se 1 (by rfl) ⟨327167, by rfl⟩ : syracuseStep 436223 = 654335) B654335
theorem B4992191 : Blo 435777 4992191 := bstep (se 1 (by rfl) ⟨3744143, by rfl⟩ : syracuseStep 4992191 = 7488287) B7488287
theorem B1001975 : Blo 435777 1001975 := bstep (se 1 (by rfl) ⟨751481, by rfl⟩ : syracuseStep 1001975 = 1502963) B1502963
theorem B168255053 : Blo 435777 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B10678391 : Blo 435777 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B11407529 : Blo 435777 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B112170035 : Blo 435777 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B10687733 : Blo 435777 10687733 := bstep (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) B1001975
theorem B7118927 : Blo 435777 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B3328127 : Blo 435777 3328127 := bstep (se 1 (by rfl) ⟨2496095, by rfl⟩ : syracuseStep 3328127 = 4992191) B4992191
theorem B101939077 : Blo 435777 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B7605019 : Blo 435777 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B74780023 : Blo 435777 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B7125155 : Blo 435777 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B2218751 : Blo 435777 2218751 := bstep (se 1 (by rfl) ⟨1664063, by rfl⟩ : syracuseStep 2218751 = 3328127) B3328127
theorem B4745951 : Blo 435777 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B135918769 : Blo 435777 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B1479167 : Blo 435777 1479167 := bstep (se 1 (by rfl) ⟨1109375, by rfl⟩ : syracuseStep 1479167 = 2218751) B2218751
theorem B181225025 : Blo 435777 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B3163967 : Blo 435777 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B40560101 : Blo 435777 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B99706697 : Blo 435777 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B4750103 : Blo 435777 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B120816683 : Blo 435777 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B986111 : Blo 435777 986111 := bstep (se 1 (by rfl) ⟨739583, by rfl⟩ : syracuseStep 986111 = 1479167) B1479167
theorem B27040067 : Blo 435777 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B2109311 : Blo 435777 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B66471131 : Blo 435777 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B3166735 : Blo 435777 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B80544455 : Blo 435777 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B657407 : Blo 435777 657407 := bstep (se 1 (by rfl) ⟨493055, by rfl⟩ : syracuseStep 657407 = 986111) B986111
theorem B18026711 : Blo 435777 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B44314087 : Blo 435777 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B4222313 : Blo 435777 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B1406207 : Blo 435777 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B59085449 : Blo 435777 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B438271 : Blo 435777 438271 := bstep (se 1 (by rfl) ⟨328703, by rfl⟩ : syracuseStep 438271 = 657407) B657407
theorem B3749885 : Blo 435777 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B53696303 : Blo 435777 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B12017807 : Blo 435777 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B2814875 : Blo 435777 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B39390299 : Blo 435777 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B1876583 : Blo 435777 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B2499923 : Blo 435777 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B35797535 : Blo 435777 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B8011871 : Blo 435777 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B5341247 : Blo 435777 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B1251055 : Blo 435777 1251055 := bstep (se 1 (by rfl) ⟨938291, by rfl⟩ : syracuseStep 1251055 = 1876583) B1876583
theorem B23865023 : Blo 435777 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B26260199 : Blo 435777 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B1666615 : Blo 435777 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B17506799 : Blo 435777 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B15910015 : Blo 435777 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B3560831 : Blo 435777 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B2222153 : Blo 435777 2222153 := bstep (se 2 (by rfl) ⟨833307, by rfl⟩ : syracuseStep 2222153 = 1666615) B1666615
theorem B1668073 : Blo 435777 1668073 := bstep (se 2 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 1668073 = 1251055) B1251055
theorem B11671199 : Blo 435777 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B1481435 : Blo 435777 1481435 := bstep (se 1 (by rfl) ⟨1111076, by rfl⟩ : syracuseStep 1481435 = 2222153) B2222153
theorem B21213353 : Blo 435777 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B2373887 : Blo 435777 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B2224097 : Blo 435777 2224097 := bstep (se 2 (by rfl) ⟨834036, by rfl⟩ : syracuseStep 2224097 = 1668073) B1668073
theorem B987623 : Blo 435777 987623 := bstep (se 1 (by rfl) ⟨740717, by rfl⟩ : syracuseStep 987623 = 1481435) B1481435
theorem B1482731 : Blo 435777 1482731 := bstep (se 1 (by rfl) ⟨1112048, by rfl⟩ : syracuseStep 1482731 = 2224097) B2224097
theorem B1582591 : Blo 435777 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B7780799 : Blo 435777 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B14142235 : Blo 435777 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B658415 : Blo 435777 658415 := bstep (se 1 (by rfl) ⟨493811, by rfl⟩ : syracuseStep 658415 = 987623) B987623
theorem B988487 : Blo 435777 988487 := bstep (se 1 (by rfl) ⟨741365, by rfl⟩ : syracuseStep 988487 = 1482731) B1482731
theorem B5187199 : Blo 435777 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B2110121 : Blo 435777 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B18856313 : Blo 435777 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B6916265 : Blo 435777 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B658991 : Blo 435777 658991 := bstep (se 1 (by rfl) ⟨494243, by rfl⟩ : syracuseStep 658991 = 988487) B988487
theorem B438943 : Blo 435777 438943 := bstep (se 1 (by rfl) ⟨329207, by rfl⟩ : syracuseStep 438943 = 658415) B658415
theorem B12570875 : Blo 435777 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B1406747 : Blo 435777 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B439327 : Blo 435777 439327 := bstep (se 1 (by rfl) ⟨329495, by rfl⟩ : syracuseStep 439327 = 658991) B658991
theorem B937831 : Blo 435777 937831 := bstep (se 1 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 937831 = 1406747) B1406747
theorem B4610843 : Blo 435777 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B8380583 : Blo 435777 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B1250441 : Blo 435777 1250441 := bstep (se 2 (by rfl) ⟨468915, by rfl⟩ : syracuseStep 1250441 = 937831) B937831
theorem B5587055 : Blo 435777 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B3073895 : Blo 435777 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B833627 : Blo 435777 833627 := bstep (se 1 (by rfl) ⟨625220, by rfl⟩ : syracuseStep 833627 = 1250441) B1250441
theorem B2049263 : Blo 435777 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B3724703 : Blo 435777 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B1366175 : Blo 435777 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B2483135 : Blo 435777 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B555751 : Blo 435777 555751 := bstep (se 1 (by rfl) ⟨416813, by rfl⟩ : syracuseStep 555751 = 833627) B833627
theorem B1655423 : Blo 435777 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B741001 : Blo 435777 741001 := bstep (se 2 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 741001 = 555751) B555751
theorem B910783 : Blo 435777 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B988001 : Blo 435777 988001 := bstep (se 2 (by rfl) ⟨370500, by rfl⟩ : syracuseStep 988001 = 741001) B741001
theorem B4857509 : Blo 435777 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B1103615 : Blo 435777 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B658667 : Blo 435777 658667 := bstep (se 1 (by rfl) ⟨494000, by rfl⟩ : syracuseStep 658667 = 988001) B988001
theorem B735743 : Blo 435777 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B3238339 : Blo 435777 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B439111 : Blo 435777 439111 := bstep (se 1 (by rfl) ⟨329333, by rfl⟩ : syracuseStep 439111 = 658667) B658667
theorem B4317785 : Blo 435777 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B490495 : Blo 435777 490495 := bstep (se 1 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 490495 = 735743) B735743
theorem B2878523 : Blo 435777 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B653993 : Blo 435777 653993 := bstep (se 2 (by rfl) ⟨245247, by rfl⟩ : syracuseStep 653993 = 490495) B490495
theorem B435995 : Blo 435777 435995 := bstep (se 1 (by rfl) ⟨326996, by rfl⟩ : syracuseStep 435995 = 653993) B653993
theorem B1919015 : Blo 435777 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B1279343 : Blo 435777 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B852895 : Blo 435777 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B4548773 : Blo 435777 4548773 := bstep (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) B852895
theorem B3032515 : Blo 435777 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B4043353 : Blo 435777 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B5391137 : Blo 435777 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B3594091 : Blo 435777 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B4792121 : Blo 435777 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B3194747 : Blo 435777 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2129831 : Blo 435777 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1419887 : Blo 435777 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B3786365 : Blo 435777 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B2524243 : Blo 435777 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B3365657 : Blo 435777 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B2243771 : Blo 435777 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1495847 : Blo 435777 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B997231 : Blo 435777 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B1329641 : Blo 435777 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B886427 : Blo 435777 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B9455221 : Blo 435777 9455221 := bstep (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) B886427
theorem B12606961 : Blo 435777 12606961 := bstep (se 2 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 12606961 = 9455221) B9455221
theorem B16809281 : Blo 435777 16809281 := bstep (se 2 (by rfl) ⟨6303480, by rfl⟩ : syracuseStep 16809281 = 12606961) B12606961
theorem B11206187 : Blo 435777 11206187 := bstep (se 1 (by rfl) ⟨8404640, by rfl⟩ : syracuseStep 11206187 = 16809281) B16809281
theorem B7470791 : Blo 435777 7470791 := bstep (se 1 (by rfl) ⟨5603093, by rfl⟩ : syracuseStep 7470791 = 11206187) B11206187
theorem B4980527 : Blo 435777 4980527 := bstep (se 1 (by rfl) ⟨3735395, by rfl⟩ : syracuseStep 4980527 = 7470791) B7470791
theorem B3320351 : Blo 435777 3320351 := bstep (se 1 (by rfl) ⟨2490263, by rfl⟩ : syracuseStep 3320351 = 4980527) B4980527
theorem B2213567 : Blo 435777 2213567 := bstep (se 1 (by rfl) ⟨1660175, by rfl⟩ : syracuseStep 2213567 = 3320351) B3320351
theorem B1475711 : Blo 435777 1475711 := bstep (se 1 (by rfl) ⟨1106783, by rfl⟩ : syracuseStep 1475711 = 2213567) B2213567
theorem B983807 : Blo 435777 983807 := bstep (se 1 (by rfl) ⟨737855, by rfl⟩ : syracuseStep 983807 = 1475711) B1475711
theorem B655871 : Blo 435777 655871 := bstep (se 1 (by rfl) ⟨491903, by rfl⟩ : syracuseStep 655871 = 983807) B983807
theorem B437247 : Blo 435777 437247 := bstep (se 1 (by rfl) ⟨327935, by rfl⟩ : syracuseStep 437247 = 655871) B655871

theorem C0 (j : ℕ) (h1 : 108944 ≤ j) (h2 : j ≤ 109643) : Blo 435777 (4 * j + 3) := by
  interval_cases j
  · exact B435779
  · exact B435783
  · exact B435787
  · exact B435791
  · exact B435795
  · exact B435799
  · exact B435803
  · exact B435807
  · exact B435811
  · exact B435815
  · exact B435819
  · exact B435823
  · exact B435827
  · exact B435831
  · exact B435835
  · exact B435839
  · exact B435843
  · exact B435847
  · exact B435851
  · exact B435855
  · exact B435859
  · exact B435863
  · exact B435867
  · exact B435871
  · exact B435875
  · exact B435879
  · exact B435883
  · exact B435887
  · exact B435891
  · exact B435895
  · exact B435899
  · exact B435903
  · exact B435907
  · exact B435911
  · exact B435915
  · exact B435919
  · exact B435923
  · exact B435927
  · exact B435931
  · exact B435935
  · exact B435939
  · exact B435943
  · exact B435947
  · exact B435951
  · exact B435955
  · exact B435959
  · exact B435963
  · exact B435967
  · exact B435971
  · exact B435975
  · exact B435979
  · exact B435983
  · exact B435987
  · exact B435991
  · exact B435995
  · exact B435999
  · exact B436003
  · exact B436007
  · exact B436011
  · exact B436015
  · exact B436019
  · exact B436023
  · exact B436027
  · exact B436031
  · exact B436035
  · exact B436039
  · exact B436043
  · exact B436047
  · exact B436051
  · exact B436055
  · exact B436059
  · exact B436063
  · exact B436067
  · exact B436071
  · exact B436075
  · exact B436079
  · exact B436083
  · exact B436087
  · exact B436091
  · exact B436095
  · exact B436099
  · exact B436103
  · exact B436107
  · exact B436111
  · exact B436115
  · exact B436119
  · exact B436123
  · exact B436127
  · exact B436131
  · exact B436135
  · exact B436139
  · exact B436143
  · exact B436147
  · exact B436151
  · exact B436155
  · exact B436159
  · exact B436163
  · exact B436167
  · exact B436171
  · exact B436175
  · exact B436179
  · exact B436183
  · exact B436187
  · exact B436191
  · exact B436195
  · exact B436199
  · exact B436203
  · exact B436207
  · exact B436211
  · exact B436215
  · exact B436219
  · exact B436223
  · exact B436227
  · exact B436231
  · exact B436235
  · exact B436239
  · exact B436243
  · exact B436247
  · exact B436251
  · exact B436255
  · exact B436259
  · exact B436263
  · exact B436267
  · exact B436271
  · exact B436275
  · exact B436279
  · exact B436283
  · exact B436287
  · exact B436291
  · exact B436295
  · exact B436299
  · exact B436303
  · exact B436307
  · exact B436311
  · exact B436315
  · exact B436319
  · exact B436323
  · exact B436327
  · exact B436331
  · exact B436335
  · exact B436339
  · exact B436343
  · exact B436347
  · exact B436351
  · exact B436355
  · exact B436359
  · exact B436363
  · exact B436367
  · exact B436371
  · exact B436375
  · exact B436379
  · exact B436383
  · exact B436387
  · exact B436391
  · exact B436395
  · exact B436399
  · exact B436403
  · exact B436407
  · exact B436411
  · exact B436415
  · exact B436419
  · exact B436423
  · exact B436427
  · exact B436431
  · exact B436435
  · exact B436439
  · exact B436443
  · exact B436447
  · exact B436451
  · exact B436455
  · exact B436459
  · exact B436463
  · exact B436467
  · exact B436471
  · exact B436475
  · exact B436479
  · exact B436483
  · exact B436487
  · exact B436491
  · exact B436495
  · exact B436499
  · exact B436503
  · exact B436507
  · exact B436511
  · exact B436515
  · exact B436519
  · exact B436523
  · exact B436527
  · exact B436531
  · exact B436535
  · exact B436539
  · exact B436543
  · exact B436547
  · exact B436551
  · exact B436555
  · exact B436559
  · exact B436563
  · exact B436567
  · exact B436571
  · exact B436575
  · exact B436579
  · exact B436583
  · exact B436587
  · exact B436591
  · exact B436595
  · exact B436599
  · exact B436603
  · exact B436607
  · exact B436611
  · exact B436615
  · exact B436619
  · exact B436623
  · exact B436627
  · exact B436631
  · exact B436635
  · exact B436639
  · exact B436643
  · exact B436647
  · exact B436651
  · exact B436655
  · exact B436659
  · exact B436663
  · exact B436667
  · exact B436671
  · exact B436675
  · exact B436679
  · exact B436683
  · exact B436687
  · exact B436691
  · exact B436695
  · exact B436699
  · exact B436703
  · exact B436707
  · exact B436711
  · exact B436715
  · exact B436719
  · exact B436723
  · exact B436727
  · exact B436731
  · exact B436735
  · exact B436739
  · exact B436743
  · exact B436747
  · exact B436751
  · exact B436755
  · exact B436759
  · exact B436763
  · exact B436767
  · exact B436771
  · exact B436775
  · exact B436779
  · exact B436783
  · exact B436787
  · exact B436791
  · exact B436795
  · exact B436799
  · exact B436803
  · exact B436807
  · exact B436811
  · exact B436815
  · exact B436819
  · exact B436823
  · exact B436827
  · exact B436831
  · exact B436835
  · exact B436839
  · exact B436843
  · exact B436847
  · exact B436851
  · exact B436855
  · exact B436859
  · exact B436863
  · exact B436867
  · exact B436871
  · exact B436875
  · exact B436879
  · exact B436883
  · exact B436887
  · exact B436891
  · exact B436895
  · exact B436899
  · exact B436903
  · exact B436907
  · exact B436911
  · exact B436915
  · exact B436919
  · exact B436923
  · exact B436927
  · exact B436931
  · exact B436935
  · exact B436939
  · exact B436943
  · exact B436947
  · exact B436951
  · exact B436955
  · exact B436959
  · exact B436963
  · exact B436967
  · exact B436971
  · exact B436975
  · exact B436979
  · exact B436983
  · exact B436987
  · exact B436991
  · exact B436995
  · exact B436999
  · exact B437003
  · exact B437007
  · exact B437011
  · exact B437015
  · exact B437019
  · exact B437023
  · exact B437027
  · exact B437031
  · exact B437035
  · exact B437039
  · exact B437043
  · exact B437047
  · exact B437051
  · exact B437055
  · exact B437059
  · exact B437063
  · exact B437067
  · exact B437071
  · exact B437075
  · exact B437079
  · exact B437083
  · exact B437087
  · exact B437091
  · exact B437095
  · exact B437099
  · exact B437103
  · exact B437107
  · exact B437111
  · exact B437115
  · exact B437119
  · exact B437123
  · exact B437127
  · exact B437131
  · exact B437135
  · exact B437139
  · exact B437143
  · exact B437147
  · exact B437151
  · exact B437155
  · exact B437159
  · exact B437163
  · exact B437167
  · exact B437171
  · exact B437175
  · exact B437179
  · exact B437183
  · exact B437187
  · exact B437191
  · exact B437195
  · exact B437199
  · exact B437203
  · exact B437207
  · exact B437211
  · exact B437215
  · exact B437219
  · exact B437223
  · exact B437227
  · exact B437231
  · exact B437235
  · exact B437239
  · exact B437243
  · exact B437247
  · exact B437251
  · exact B437255
  · exact B437259
  · exact B437263
  · exact B437267
  · exact B437271
  · exact B437275
  · exact B437279
  · exact B437283
  · exact B437287
  · exact B437291
  · exact B437295
  · exact B437299
  · exact B437303
  · exact B437307
  · exact B437311
  · exact B437315
  · exact B437319
  · exact B437323
  · exact B437327
  · exact B437331
  · exact B437335
  · exact B437339
  · exact B437343
  · exact B437347
  · exact B437351
  · exact B437355
  · exact B437359
  · exact B437363
  · exact B437367
  · exact B437371
  · exact B437375
  · exact B437379
  · exact B437383
  · exact B437387
  · exact B437391
  · exact B437395
  · exact B437399
  · exact B437403
  · exact B437407
  · exact B437411
  · exact B437415
  · exact B437419
  · exact B437423
  · exact B437427
  · exact B437431
  · exact B437435
  · exact B437439
  · exact B437443
  · exact B437447
  · exact B437451
  · exact B437455
  · exact B437459
  · exact B437463
  · exact B437467
  · exact B437471
  · exact B437475
  · exact B437479
  · exact B437483
  · exact B437487
  · exact B437491
  · exact B437495
  · exact B437499
  · exact B437503
  · exact B437507
  · exact B437511
  · exact B437515
  · exact B437519
  · exact B437523
  · exact B437527
  · exact B437531
  · exact B437535
  · exact B437539
  · exact B437543
  · exact B437547
  · exact B437551
  · exact B437555
  · exact B437559
  · exact B437563
  · exact B437567
  · exact B437571
  · exact B437575
  · exact B437579
  · exact B437583
  · exact B437587
  · exact B437591
  · exact B437595
  · exact B437599
  · exact B437603
  · exact B437607
  · exact B437611
  · exact B437615
  · exact B437619
  · exact B437623
  · exact B437627
  · exact B437631
  · exact B437635
  · exact B437639
  · exact B437643
  · exact B437647
  · exact B437651
  · exact B437655
  · exact B437659
  · exact B437663
  · exact B437667
  · exact B437671
  · exact B437675
  · exact B437679
  · exact B437683
  · exact B437687
  · exact B437691
  · exact B437695
  · exact B437699
  · exact B437703
  · exact B437707
  · exact B437711
  · exact B437715
  · exact B437719
  · exact B437723
  · exact B437727
  · exact B437731
  · exact B437735
  · exact B437739
  · exact B437743
  · exact B437747
  · exact B437751
  · exact B437755
  · exact B437759
  · exact B437763
  · exact B437767
  · exact B437771
  · exact B437775
  · exact B437779
  · exact B437783
  · exact B437787
  · exact B437791
  · exact B437795
  · exact B437799
  · exact B437803
  · exact B437807
  · exact B437811
  · exact B437815
  · exact B437819
  · exact B437823
  · exact B437827
  · exact B437831
  · exact B437835
  · exact B437839
  · exact B437843
  · exact B437847
  · exact B437851
  · exact B437855
  · exact B437859
  · exact B437863
  · exact B437867
  · exact B437871
  · exact B437875
  · exact B437879
  · exact B437883
  · exact B437887
  · exact B437891
  · exact B437895
  · exact B437899
  · exact B437903
  · exact B437907
  · exact B437911
  · exact B437915
  · exact B437919
  · exact B437923
  · exact B437927
  · exact B437931
  · exact B437935
  · exact B437939
  · exact B437943
  · exact B437947
  · exact B437951
  · exact B437955
  · exact B437959
  · exact B437963
  · exact B437967
  · exact B437971
  · exact B437975
  · exact B437979
  · exact B437983
  · exact B437987
  · exact B437991
  · exact B437995
  · exact B437999
  · exact B438003
  · exact B438007
  · exact B438011
  · exact B438015
  · exact B438019
  · exact B438023
  · exact B438027
  · exact B438031
  · exact B438035
  · exact B438039
  · exact B438043
  · exact B438047
  · exact B438051
  · exact B438055
  · exact B438059
  · exact B438063
  · exact B438067
  · exact B438071
  · exact B438075
  · exact B438079
  · exact B438083
  · exact B438087
  · exact B438091
  · exact B438095
  · exact B438099
  · exact B438103
  · exact B438107
  · exact B438111
  · exact B438115
  · exact B438119
  · exact B438123
  · exact B438127
  · exact B438131
  · exact B438135
  · exact B438139
  · exact B438143
  · exact B438147
  · exact B438151
  · exact B438155
  · exact B438159
  · exact B438163
  · exact B438167
  · exact B438171
  · exact B438175
  · exact B438179
  · exact B438183
  · exact B438187
  · exact B438191
  · exact B438195
  · exact B438199
  · exact B438203
  · exact B438207
  · exact B438211
  · exact B438215
  · exact B438219
  · exact B438223
  · exact B438227
  · exact B438231
  · exact B438235
  · exact B438239
  · exact B438243
  · exact B438247
  · exact B438251
  · exact B438255
  · exact B438259
  · exact B438263
  · exact B438267
  · exact B438271
  · exact B438275
  · exact B438279
  · exact B438283
  · exact B438287
  · exact B438291
  · exact B438295
  · exact B438299
  · exact B438303
  · exact B438307
  · exact B438311
  · exact B438315
  · exact B438319
  · exact B438323
  · exact B438327
  · exact B438331
  · exact B438335
  · exact B438339
  · exact B438343
  · exact B438347
  · exact B438351
  · exact B438355
  · exact B438359
  · exact B438363
  · exact B438367
  · exact B438371
  · exact B438375
  · exact B438379
  · exact B438383
  · exact B438387
  · exact B438391
  · exact B438395
  · exact B438399
  · exact B438403
  · exact B438407
  · exact B438411
  · exact B438415
  · exact B438419
  · exact B438423
  · exact B438427
  · exact B438431
  · exact B438435
  · exact B438439
  · exact B438443
  · exact B438447
  · exact B438451
  · exact B438455
  · exact B438459
  · exact B438463
  · exact B438467
  · exact B438471
  · exact B438475
  · exact B438479
  · exact B438483
  · exact B438487
  · exact B438491
  · exact B438495
  · exact B438499
  · exact B438503
  · exact B438507
  · exact B438511
  · exact B438515
  · exact B438519
  · exact B438523
  · exact B438527
  · exact B438531
  · exact B438535
  · exact B438539
  · exact B438543
  · exact B438547
  · exact B438551
  · exact B438555
  · exact B438559
  · exact B438563
  · exact B438567
  · exact B438571
  · exact B438575

theorem C1 (j : ℕ) (h1 : 109644 ≤ j) (h2 : j ≤ 109943) : Blo 435777 (4 * j + 3) := by
  interval_cases j
  · exact B438579
  · exact B438583
  · exact B438587
  · exact B438591
  · exact B438595
  · exact B438599
  · exact B438603
  · exact B438607
  · exact B438611
  · exact B438615
  · exact B438619
  · exact B438623
  · exact B438627
  · exact B438631
  · exact B438635
  · exact B438639
  · exact B438643
  · exact B438647
  · exact B438651
  · exact B438655
  · exact B438659
  · exact B438663
  · exact B438667
  · exact B438671
  · exact B438675
  · exact B438679
  · exact B438683
  · exact B438687
  · exact B438691
  · exact B438695
  · exact B438699
  · exact B438703
  · exact B438707
  · exact B438711
  · exact B438715
  · exact B438719
  · exact B438723
  · exact B438727
  · exact B438731
  · exact B438735
  · exact B438739
  · exact B438743
  · exact B438747
  · exact B438751
  · exact B438755
  · exact B438759
  · exact B438763
  · exact B438767
  · exact B438771
  · exact B438775
  · exact B438779
  · exact B438783
  · exact B438787
  · exact B438791
  · exact B438795
  · exact B438799
  · exact B438803
  · exact B438807
  · exact B438811
  · exact B438815
  · exact B438819
  · exact B438823
  · exact B438827
  · exact B438831
  · exact B438835
  · exact B438839
  · exact B438843
  · exact B438847
  · exact B438851
  · exact B438855
  · exact B438859
  · exact B438863
  · exact B438867
  · exact B438871
  · exact B438875
  · exact B438879
  · exact B438883
  · exact B438887
  · exact B438891
  · exact B438895
  · exact B438899
  · exact B438903
  · exact B438907
  · exact B438911
  · exact B438915
  · exact B438919
  · exact B438923
  · exact B438927
  · exact B438931
  · exact B438935
  · exact B438939
  · exact B438943
  · exact B438947
  · exact B438951
  · exact B438955
  · exact B438959
  · exact B438963
  · exact B438967
  · exact B438971
  · exact B438975
  · exact B438979
  · exact B438983
  · exact B438987
  · exact B438991
  · exact B438995
  · exact B438999
  · exact B439003
  · exact B439007
  · exact B439011
  · exact B439015
  · exact B439019
  · exact B439023
  · exact B439027
  · exact B439031
  · exact B439035
  · exact B439039
  · exact B439043
  · exact B439047
  · exact B439051
  · exact B439055
  · exact B439059
  · exact B439063
  · exact B439067
  · exact B439071
  · exact B439075
  · exact B439079
  · exact B439083
  · exact B439087
  · exact B439091
  · exact B439095
  · exact B439099
  · exact B439103
  · exact B439107
  · exact B439111
  · exact B439115
  · exact B439119
  · exact B439123
  · exact B439127
  · exact B439131
  · exact B439135
  · exact B439139
  · exact B439143
  · exact B439147
  · exact B439151
  · exact B439155
  · exact B439159
  · exact B439163
  · exact B439167
  · exact B439171
  · exact B439175
  · exact B439179
  · exact B439183
  · exact B439187
  · exact B439191
  · exact B439195
  · exact B439199
  · exact B439203
  · exact B439207
  · exact B439211
  · exact B439215
  · exact B439219
  · exact B439223
  · exact B439227
  · exact B439231
  · exact B439235
  · exact B439239
  · exact B439243
  · exact B439247
  · exact B439251
  · exact B439255
  · exact B439259
  · exact B439263
  · exact B439267
  · exact B439271
  · exact B439275
  · exact B439279
  · exact B439283
  · exact B439287
  · exact B439291
  · exact B439295
  · exact B439299
  · exact B439303
  · exact B439307
  · exact B439311
  · exact B439315
  · exact B439319
  · exact B439323
  · exact B439327
  · exact B439331
  · exact B439335
  · exact B439339
  · exact B439343
  · exact B439347
  · exact B439351
  · exact B439355
  · exact B439359
  · exact B439363
  · exact B439367
  · exact B439371
  · exact B439375
  · exact B439379
  · exact B439383
  · exact B439387
  · exact B439391
  · exact B439395
  · exact B439399
  · exact B439403
  · exact B439407
  · exact B439411
  · exact B439415
  · exact B439419
  · exact B439423
  · exact B439427
  · exact B439431
  · exact B439435
  · exact B439439
  · exact B439443
  · exact B439447
  · exact B439451
  · exact B439455
  · exact B439459
  · exact B439463
  · exact B439467
  · exact B439471
  · exact B439475
  · exact B439479
  · exact B439483
  · exact B439487
  · exact B439491
  · exact B439495
  · exact B439499
  · exact B439503
  · exact B439507
  · exact B439511
  · exact B439515
  · exact B439519
  · exact B439523
  · exact B439527
  · exact B439531
  · exact B439535
  · exact B439539
  · exact B439543
  · exact B439547
  · exact B439551
  · exact B439555
  · exact B439559
  · exact B439563
  · exact B439567
  · exact B439571
  · exact B439575
  · exact B439579
  · exact B439583
  · exact B439587
  · exact B439591
  · exact B439595
  · exact B439599
  · exact B439603
  · exact B439607
  · exact B439611
  · exact B439615
  · exact B439619
  · exact B439623
  · exact B439627
  · exact B439631
  · exact B439635
  · exact B439639
  · exact B439643
  · exact B439647
  · exact B439651
  · exact B439655
  · exact B439659
  · exact B439663
  · exact B439667
  · exact B439671
  · exact B439675
  · exact B439679
  · exact B439683
  · exact B439687
  · exact B439691
  · exact B439695
  · exact B439699
  · exact B439703
  · exact B439707
  · exact B439711
  · exact B439715
  · exact B439719
  · exact B439723
  · exact B439727
  · exact B439731
  · exact B439735
  · exact B439739
  · exact B439743
  · exact B439747
  · exact B439751
  · exact B439755
  · exact B439759
  · exact B439763
  · exact B439767
  · exact B439771
  · exact B439775

theorem solution (m : ℕ) (hlo : 435777 ≤ m) (hhi : m ≤ 439777) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 108944 ≤ j := by omega
    have hj2 : j ≤ 109943 := by omega
    have hb : Blo 435777 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 109644 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
