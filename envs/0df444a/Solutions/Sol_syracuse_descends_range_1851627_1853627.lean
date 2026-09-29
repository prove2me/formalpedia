-- Prove2me | solution 1 for syracuse_descends_range_1851627_1853627
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:07:22.297237+00:00
-- url     : https://prove2.me/submissions/19368b4a-55a4-4967-a2d6-7469462b31cc

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


theorem B4169789 : Blo 1851627 4169789 := bbase (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) (by norm_num)
theorem B4120645 : Blo 1851627 4120645 := bbase (se 4 (by rfl) ⟨386310, by rfl⟩ : syracuseStep 4120645 = 772621) (by norm_num)
theorem B4169861 : Blo 1851627 4169861 := bbase (se 4 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 4169861 = 781849) (by norm_num)
theorem B2818189 : Blo 1851627 2818189 := bbase (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) (by norm_num)
theorem B6250661 : Blo 1851627 6250661 := bbase (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) (by norm_num)
theorem B10018997 : Blo 1851627 10018997 := bbase (se 5 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 10018997 = 939281) (by norm_num)
theorem B3956933 : Blo 1851627 3956933 := bbase (se 4 (by rfl) ⟨370962, by rfl⟩ : syracuseStep 3956933 = 741925) (by norm_num)
theorem B4169933 : Blo 1851627 4169933 := bbase (se 3 (by rfl) ⟨781862, by rfl⟩ : syracuseStep 4169933 = 1563725) (by norm_num)
theorem B7037189 : Blo 1851627 7037189 := bbase (se 4 (by rfl) ⟨659736, by rfl⟩ : syracuseStep 7037189 = 1319473) (by norm_num)
theorem B4170005 : Blo 1851627 4170005 := bbase (se 6 (by rfl) ⟨97734, by rfl⟩ : syracuseStep 4170005 = 195469) (by norm_num)
theorem B2638109 : Blo 1851627 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B5636405 : Blo 1851627 5636405 := bbase (se 5 (by rfl) ⟨264206, by rfl⟩ : syracuseStep 5636405 = 528413) (by norm_num)
theorem B6676805 : Blo 1851627 6676805 := bbase (se 4 (by rfl) ⟨625950, by rfl⟩ : syracuseStep 6676805 = 1251901) (by norm_num)
theorem B7127381 : Blo 1851627 7127381 := bbase (se 10 (by rfl) ⟨10440, by rfl⟩ : syracuseStep 7127381 = 20881) (by norm_num)
theorem B33497429 : Blo 1851627 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B4170077 : Blo 1851627 4170077 := bbase (se 3 (by rfl) ⟨781889, by rfl⟩ : syracuseStep 4170077 = 1563779) (by norm_num)
theorem B2777453 : Blo 1851627 2777453 := bbase (se 3 (by rfl) ⟨520772, by rfl⟩ : syracuseStep 2777453 = 1041545) (by norm_num)
theorem B12034421 : Blo 1851627 12034421 := bbase (se 5 (by rfl) ⟨564113, by rfl⟩ : syracuseStep 12034421 = 1128227) (by norm_num)
theorem B2777477 : Blo 1851627 2777477 := bbase (se 4 (by rfl) ⟨260388, by rfl⟩ : syracuseStep 2777477 = 520777) (by norm_num)
theorem B2777501 : Blo 1851627 2777501 := bbase (se 3 (by rfl) ⟨520781, by rfl⟩ : syracuseStep 2777501 = 1041563) (by norm_num)
theorem B4170149 : Blo 1851627 4170149 := bbase (se 4 (by rfl) ⟨390951, by rfl⟩ : syracuseStep 4170149 = 781903) (by norm_num)
theorem B2777525 : Blo 1851627 2777525 := bbase (se 5 (by rfl) ⟨130196, by rfl⟩ : syracuseStep 2777525 = 260393) (by norm_num)
theorem B2777549 : Blo 1851627 2777549 := bbase (se 3 (by rfl) ⟨520790, by rfl⟩ : syracuseStep 2777549 = 1041581) (by norm_num)
theorem B2777573 : Blo 1851627 2777573 := bbase (se 4 (by rfl) ⟨260397, by rfl⟩ : syracuseStep 2777573 = 520795) (by norm_num)
theorem B4170221 : Blo 1851627 4170221 := bbase (se 3 (by rfl) ⟨781916, by rfl⟩ : syracuseStep 4170221 = 1563833) (by norm_num)
theorem B15024629 : Blo 1851627 15024629 := bbase (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) (by norm_num)
theorem B2777597 : Blo 1851627 2777597 := bbase (se 3 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 2777597 = 1041599) (by norm_num)
theorem B2777621 : Blo 1851627 2777621 := bbase (se 6 (by rfl) ⟨65100, by rfl⟩ : syracuseStep 2777621 = 130201) (by norm_num)
theorem B7225877 : Blo 1851627 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B2777645 : Blo 1851627 2777645 := bbase (se 3 (by rfl) ⟨520808, by rfl⟩ : syracuseStep 2777645 = 1041617) (by norm_num)
theorem B4170293 : Blo 1851627 4170293 := bbase (se 5 (by rfl) ⟨195482, by rfl⟩ : syracuseStep 4170293 = 390965) (by norm_num)
theorem B2777669 : Blo 1851627 2777669 := bbase (se 4 (by rfl) ⟨260406, by rfl⟩ : syracuseStep 2777669 = 520813) (by norm_num)
theorem B6251093 : Blo 1851627 6251093 := bbase (se 8 (by rfl) ⟨36627, by rfl⟩ : syracuseStep 6251093 = 73255) (by norm_num)
theorem B2777693 : Blo 1851627 2777693 := bbase (se 3 (by rfl) ⟨520817, by rfl⟩ : syracuseStep 2777693 = 1041635) (by norm_num)
theorem B2777717 : Blo 1851627 2777717 := bbase (se 5 (by rfl) ⟨130205, by rfl⟩ : syracuseStep 2777717 = 260411) (by norm_num)
theorem B6955637 : Blo 1851627 6955637 := bbase (se 5 (by rfl) ⟨326045, by rfl⟩ : syracuseStep 6955637 = 652091) (by norm_num)
theorem B4170365 : Blo 1851627 4170365 := bbase (se 3 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 4170365 = 1563887) (by norm_num)
theorem B2966149 : Blo 1851627 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B2777741 : Blo 1851627 2777741 := bbase (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) (by norm_num)
theorem B2777765 : Blo 1851627 2777765 := bbase (se 4 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 2777765 = 520831) (by norm_num)
theorem B2343593 : Blo 1851627 2343593 := bbase (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) (by norm_num)
theorem B2777789 : Blo 1851627 2777789 := bbase (se 3 (by rfl) ⟨520835, by rfl⟩ : syracuseStep 2777789 = 1041671) (by norm_num)
theorem B3957437 : Blo 1851627 3957437 := bbase (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) (by norm_num)
theorem B3957445 : Blo 1851627 3957445 := bbase (se 4 (by rfl) ⟨371010, by rfl⟩ : syracuseStep 3957445 = 742021) (by norm_num)
theorem B4170437 : Blo 1851627 4170437 := bbase (se 4 (by rfl) ⟨390978, by rfl⟩ : syracuseStep 4170437 = 781957) (by norm_num)
theorem B2777813 : Blo 1851627 2777813 := bbase (se 7 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 2777813 = 65105) (by norm_num)
theorem B2343649 : Blo 1851627 2343649 := bbase (se 2 (by rfl) ⟨878868, by rfl⟩ : syracuseStep 2343649 = 1757737) (by norm_num)
theorem B2777837 : Blo 1851627 2777837 := bbase (se 3 (by rfl) ⟨520844, by rfl⟩ : syracuseStep 2777837 = 1041689) (by norm_num)
theorem B2777861 : Blo 1851627 2777861 := bbase (se 4 (by rfl) ⟨260424, by rfl⟩ : syracuseStep 2777861 = 520849) (by norm_num)
theorem B4170509 : Blo 1851627 4170509 := bbase (se 3 (by rfl) ⟨781970, by rfl⟩ : syracuseStep 4170509 = 1563941) (by norm_num)
theorem B2777885 : Blo 1851627 2777885 := bbase (se 3 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 2777885 = 1041707) (by norm_num)
theorem B2777909 : Blo 1851627 2777909 := bbase (se 5 (by rfl) ⟨130214, by rfl⟩ : syracuseStep 2777909 = 260429) (by norm_num)
theorem B2343745 : Blo 1851627 2343745 := bbase (se 2 (by rfl) ⟨878904, by rfl⟩ : syracuseStep 2343745 = 1757809) (by norm_num)
theorem B2638661 : Blo 1851627 2638661 := bbase (se 4 (by rfl) ⟨247374, by rfl⟩ : syracuseStep 2638661 = 494749) (by norm_num)
theorem B2777933 : Blo 1851627 2777933 := bbase (se 3 (by rfl) ⟨520862, by rfl⟩ : syracuseStep 2777933 = 1041725) (by norm_num)
theorem B4170581 : Blo 1851627 4170581 := bbase (se 9 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 4170581 = 24437) (by norm_num)
theorem B2777957 : Blo 1851627 2777957 := bbase (se 4 (by rfl) ⟨260433, by rfl⟩ : syracuseStep 2777957 = 520867) (by norm_num)
theorem B4752245 : Blo 1851627 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B2777981 : Blo 1851627 2777981 := bbase (se 3 (by rfl) ⟨520871, by rfl⟩ : syracuseStep 2777981 = 1041743) (by norm_num)
theorem B2778005 : Blo 1851627 2778005 := bbase (se 6 (by rfl) ⟨65109, by rfl⟩ : syracuseStep 2778005 = 130219) (by norm_num)
theorem B4170653 : Blo 1851627 4170653 := bbase (se 3 (by rfl) ⟨781997, by rfl⟩ : syracuseStep 4170653 = 1563995) (by norm_num)
theorem B2778029 : Blo 1851627 2778029 := bbase (se 3 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 2778029 = 1041761) (by norm_num)
theorem B11871157 : Blo 1851627 11871157 := bbase (se 5 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 11871157 = 1112921) (by norm_num)
theorem B15229877 : Blo 1851627 15229877 := bbase (se 5 (by rfl) ⟨713900, by rfl⟩ : syracuseStep 15229877 = 1427801) (by norm_num)
theorem B2778053 : Blo 1851627 2778053 := bbase (se 4 (by rfl) ⟨260442, by rfl⟩ : syracuseStep 2778053 = 520885) (by norm_num)
theorem B2778077 : Blo 1851627 2778077 := bbase (se 3 (by rfl) ⟨520889, by rfl⟩ : syracuseStep 2778077 = 1041779) (by norm_num)
theorem B2343917 : Blo 1851627 2343917 := bbase (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) (by norm_num)
theorem B2778101 : Blo 1851627 2778101 := bbase (se 5 (by rfl) ⟨130223, by rfl⟩ : syracuseStep 2778101 = 260447) (by norm_num)
theorem B6251525 : Blo 1851627 6251525 := bbase (se 4 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 6251525 = 1172161) (by norm_num)
theorem B2778125 : Blo 1851627 2778125 := bbase (se 3 (by rfl) ⟨520898, by rfl⟩ : syracuseStep 2778125 = 1041797) (by norm_num)
theorem B3515413 : Blo 1851627 3515413 := bbase (se 6 (by rfl) ⟨82392, by rfl⟩ : syracuseStep 3515413 = 164785) (by norm_num)
theorem B2343973 : Blo 1851627 2343973 := bbase (se 4 (by rfl) ⟨219747, by rfl⟩ : syracuseStep 2343973 = 439495) (by norm_num)
theorem B2778149 : Blo 1851627 2778149 := bbase (se 4 (by rfl) ⟨260451, by rfl⟩ : syracuseStep 2778149 = 520903) (by norm_num)
theorem B2778173 : Blo 1851627 2778173 := bbase (se 3 (by rfl) ⟨520907, by rfl⟩ : syracuseStep 2778173 = 1041815) (by norm_num)
theorem B9380933 : Blo 1851627 9380933 := bbase (se 4 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 9380933 = 1758925) (by norm_num)
theorem B2778197 : Blo 1851627 2778197 := bbase (se 8 (by rfl) ⟨16278, by rfl⟩ : syracuseStep 2778197 = 32557) (by norm_num)
theorem B4752485 : Blo 1851627 4752485 := bbase (se 4 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 4752485 = 891091) (by norm_num)
theorem B2778221 : Blo 1851627 2778221 := bbase (se 3 (by rfl) ⟨520916, by rfl⟩ : syracuseStep 2778221 = 1041833) (by norm_num)
theorem B2344069 : Blo 1851627 2344069 := bbase (se 4 (by rfl) ⟨219756, by rfl⟩ : syracuseStep 2344069 = 439513) (by norm_num)
theorem B2778245 : Blo 1851627 2778245 := bbase (se 4 (by rfl) ⟨260460, by rfl⟩ : syracuseStep 2778245 = 520921) (by norm_num)
theorem B5276821 : Blo 1851627 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B2778269 : Blo 1851627 2778269 := bbase (se 3 (by rfl) ⟨520925, by rfl⟩ : syracuseStep 2778269 = 1041851) (by norm_num)
theorem B3515557 : Blo 1851627 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B2778293 : Blo 1851627 2778293 := bbase (se 5 (by rfl) ⟨130232, by rfl⟩ : syracuseStep 2778293 = 260465) (by norm_num)
theorem B2778317 : Blo 1851627 2778317 := bbase (se 3 (by rfl) ⟨520934, by rfl⟩ : syracuseStep 2778317 = 1041869) (by norm_num)
theorem B2778341 : Blo 1851627 2778341 := bbase (se 4 (by rfl) ⟨260469, by rfl⟩ : syracuseStep 2778341 = 520939) (by norm_num)
theorem B4687085 : Blo 1851627 4687085 := bbase (se 3 (by rfl) ⟨878828, by rfl⟩ : syracuseStep 4687085 = 1757657) (by norm_num)
theorem B2778365 : Blo 1851627 2778365 := bbase (se 3 (by rfl) ⟨520943, by rfl⟩ : syracuseStep 2778365 = 1041887) (by norm_num)
theorem B2966797 : Blo 1851627 2966797 := bbase (se 3 (by rfl) ⟨556274, by rfl⟩ : syracuseStep 2966797 = 1112549) (by norm_num)
theorem B2778389 : Blo 1851627 2778389 := bbase (se 6 (by rfl) ⟨65118, by rfl⟩ : syracuseStep 2778389 = 130237) (by norm_num)
theorem B2778413 : Blo 1851627 2778413 := bbase (se 3 (by rfl) ⟨520952, by rfl⟩ : syracuseStep 2778413 = 1041905) (by norm_num)
theorem B2344241 : Blo 1851627 2344241 := bbase (se 2 (by rfl) ⟨879090, by rfl⟩ : syracuseStep 2344241 = 1758181) (by norm_num)
theorem B5276981 : Blo 1851627 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B3515717 : Blo 1851627 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B2778437 : Blo 1851627 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B1877329 : Blo 1851627 1877329 := bbase (se 2 (by rfl) ⟨703998, by rfl⟩ : syracuseStep 1877329 = 1407997) (by norm_num)
theorem B2778461 : Blo 1851627 2778461 := bbase (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) (by norm_num)
theorem B2344297 : Blo 1851627 2344297 := bbase (se 2 (by rfl) ⟨879111, by rfl⟩ : syracuseStep 2344297 = 1758223) (by norm_num)
theorem B2778485 : Blo 1851627 2778485 := bbase (se 5 (by rfl) ⟨130241, by rfl⟩ : syracuseStep 2778485 = 260483) (by norm_num)
theorem B2778509 : Blo 1851627 2778509 := bbase (se 3 (by rfl) ⟨520970, by rfl⟩ : syracuseStep 2778509 = 1041941) (by norm_num)
theorem B2778533 : Blo 1851627 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B6251957 : Blo 1851627 6251957 := bbase (se 5 (by rfl) ⟨293060, by rfl⟩ : syracuseStep 6251957 = 586121) (by norm_num)
theorem B2778557 : Blo 1851627 2778557 := bbase (se 3 (by rfl) ⟨520979, by rfl⟩ : syracuseStep 2778557 = 1041959) (by norm_num)
theorem B2344393 : Blo 1851627 2344393 := bbase (se 2 (by rfl) ⟨879147, by rfl⟩ : syracuseStep 2344393 = 1758295) (by norm_num)
theorem B3515861 : Blo 1851627 3515861 := bbase (se 7 (by rfl) ⟨41201, by rfl⟩ : syracuseStep 3515861 = 82403) (by norm_num)
theorem B2778581 : Blo 1851627 2778581 := bbase (se 7 (by rfl) ⟨32561, by rfl⟩ : syracuseStep 2778581 = 65123) (by norm_num)
theorem B2778605 : Blo 1851627 2778605 := bbase (se 3 (by rfl) ⟨520988, by rfl⟩ : syracuseStep 2778605 = 1041977) (by norm_num)
theorem B4752901 : Blo 1851627 4752901 := bbase (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) (by norm_num)
theorem B2778629 : Blo 1851627 2778629 := bbase (se 4 (by rfl) ⟨260496, by rfl⟩ : syracuseStep 2778629 = 520993) (by norm_num)
theorem B2778653 : Blo 1851627 2778653 := bbase (se 3 (by rfl) ⟨520997, by rfl⟩ : syracuseStep 2778653 = 1041995) (by norm_num)
theorem B5277221 : Blo 1851627 5277221 := bbase (se 4 (by rfl) ⟨494739, by rfl⟩ : syracuseStep 5277221 = 989479) (by norm_num)
theorem B2778677 : Blo 1851627 2778677 := bbase (se 5 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 2778677 = 260501) (by norm_num)
theorem B4687429 : Blo 1851627 4687429 := bbase (se 4 (by rfl) ⟨439446, by rfl⟩ : syracuseStep 4687429 = 878893) (by norm_num)
theorem B2778701 : Blo 1851627 2778701 := bbase (se 3 (by rfl) ⟨521006, by rfl⟩ : syracuseStep 2778701 = 1042013) (by norm_num)
theorem B2778725 : Blo 1851627 2778725 := bbase (se 4 (by rfl) ⟨260505, by rfl⟩ : syracuseStep 2778725 = 521011) (by norm_num)
theorem B2344565 : Blo 1851627 2344565 := bbase (se 5 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 2344565 = 219803) (by norm_num)
theorem B2778749 : Blo 1851627 2778749 := bbase (se 3 (by rfl) ⟨521015, by rfl⟩ : syracuseStep 2778749 = 1042031) (by norm_num)
theorem B2778773 : Blo 1851627 2778773 := bbase (se 6 (by rfl) ⟨65127, by rfl⟩ : syracuseStep 2778773 = 130255) (by norm_num)
theorem B5932709 : Blo 1851627 5932709 := bbase (se 4 (by rfl) ⟨556191, by rfl⟩ : syracuseStep 5932709 = 1112383) (by norm_num)
theorem B2778797 : Blo 1851627 2778797 := bbase (se 3 (by rfl) ⟨521024, by rfl⟩ : syracuseStep 2778797 = 1042049) (by norm_num)
theorem B2344621 : Blo 1851627 2344621 := bbase (se 3 (by rfl) ⟨439616, by rfl⟩ : syracuseStep 2344621 = 879233) (by norm_num)
theorem B4687541 : Blo 1851627 4687541 := bbase (se 5 (by rfl) ⟨219728, by rfl⟩ : syracuseStep 4687541 = 439457) (by norm_num)
theorem B4449973 : Blo 1851627 4449973 := bbase (se 5 (by rfl) ⟨208592, by rfl⟩ : syracuseStep 4449973 = 417185) (by norm_num)
theorem B2778821 : Blo 1851627 2778821 := bbase (se 4 (by rfl) ⟨260514, by rfl⟩ : syracuseStep 2778821 = 521029) (by norm_num)
theorem B2778845 : Blo 1851627 2778845 := bbase (se 3 (by rfl) ⟨521033, by rfl⟩ : syracuseStep 2778845 = 1042067) (by norm_num)
theorem B3385061 : Blo 1851627 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B5277413 : Blo 1851627 5277413 := bbase (se 4 (by rfl) ⟨494757, by rfl⟩ : syracuseStep 5277413 = 989515) (by norm_num)
theorem B3516149 : Blo 1851627 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B2778869 : Blo 1851627 2778869 := bbase (se 5 (by rfl) ⟨130259, by rfl⟩ : syracuseStep 2778869 = 260519) (by norm_num)
theorem B2778893 : Blo 1851627 2778893 := bbase (se 3 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 2778893 = 1042085) (by norm_num)
theorem B2344717 : Blo 1851627 2344717 := bbase (se 3 (by rfl) ⟨439634, by rfl⟩ : syracuseStep 2344717 = 879269) (by norm_num)
theorem B2778917 : Blo 1851627 2778917 := bbase (se 4 (by rfl) ⟨260523, by rfl⟩ : syracuseStep 2778917 = 521047) (by norm_num)
theorem B3958573 : Blo 1851627 3958573 := bbase (se 3 (by rfl) ⟨742232, by rfl⟩ : syracuseStep 3958573 = 1484465) (by norm_num)
theorem B2778941 : Blo 1851627 2778941 := bbase (se 3 (by rfl) ⟨521051, by rfl⟩ : syracuseStep 2778941 = 1042103) (by norm_num)
theorem B7030597 : Blo 1851627 7030597 := bbase (se 4 (by rfl) ⟨659118, by rfl⟩ : syracuseStep 7030597 = 1318237) (by norm_num)
theorem B2778965 : Blo 1851627 2778965 := bbase (se 9 (by rfl) ⟨8141, by rfl⟩ : syracuseStep 2778965 = 16283) (by norm_num)
theorem B6252389 : Blo 1851627 6252389 := bbase (se 4 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 6252389 = 1172323) (by norm_num)
theorem B2778989 : Blo 1851627 2778989 := bbase (se 3 (by rfl) ⟨521060, by rfl⟩ : syracuseStep 2778989 = 1042121) (by norm_num)
theorem B4687733 : Blo 1851627 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B2779013 : Blo 1851627 2779013 := bbase (se 4 (by rfl) ⟨260532, by rfl⟩ : syracuseStep 2779013 = 521065) (by norm_num)
theorem B3516301 : Blo 1851627 3516301 := bbase (se 3 (by rfl) ⟨659306, by rfl⟩ : syracuseStep 3516301 = 1318613) (by norm_num)
theorem B2779037 : Blo 1851627 2779037 := bbase (se 3 (by rfl) ⟨521069, by rfl⟩ : syracuseStep 2779037 = 1042139) (by norm_num)
theorem B2779061 : Blo 1851627 2779061 := bbase (se 5 (by rfl) ⟨130268, by rfl⟩ : syracuseStep 2779061 = 260537) (by norm_num)
theorem B2344889 : Blo 1851627 2344889 := bbase (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) (by norm_num)
theorem B2779085 : Blo 1851627 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B3008477 : Blo 1851627 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B2779109 : Blo 1851627 2779109 := bbase (se 4 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 2779109 = 521083) (by norm_num)
theorem B2344945 : Blo 1851627 2344945 := bbase (se 2 (by rfl) ⟨879354, by rfl⟩ : syracuseStep 2344945 = 1758709) (by norm_num)
theorem B2779133 : Blo 1851627 2779133 := bbase (se 3 (by rfl) ⟨521087, by rfl⟩ : syracuseStep 2779133 = 1042175) (by norm_num)
theorem B2779157 : Blo 1851627 2779157 := bbase (se 6 (by rfl) ⟨65136, by rfl⟩ : syracuseStep 2779157 = 130273) (by norm_num)
theorem B2779181 : Blo 1851627 2779181 := bbase (se 3 (by rfl) ⟨521096, by rfl⟩ : syracuseStep 2779181 = 1042193) (by norm_num)
theorem B7915573 : Blo 1851627 7915573 := bbase (se 5 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 7915573 = 742085) (by norm_num)
theorem B2779205 : Blo 1851627 2779205 := bbase (se 4 (by rfl) ⟨260550, by rfl⟩ : syracuseStep 2779205 = 521101) (by norm_num)
theorem B2345041 : Blo 1851627 2345041 := bbase (se 2 (by rfl) ⟨879390, by rfl⟩ : syracuseStep 2345041 = 1758781) (by norm_num)
theorem B2779229 : Blo 1851627 2779229 := bbase (se 3 (by rfl) ⟨521105, by rfl⟩ : syracuseStep 2779229 = 1042211) (by norm_num)
theorem B7030901 : Blo 1851627 7030901 := bbase (se 5 (by rfl) ⟨329573, by rfl⟩ : syracuseStep 7030901 = 659147) (by norm_num)
theorem B2779253 : Blo 1851627 2779253 := bbase (se 5 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 2779253 = 260555) (by norm_num)
theorem B2779277 : Blo 1851627 2779277 := bbase (se 3 (by rfl) ⟨521114, by rfl⟩ : syracuseStep 2779277 = 1042229) (by norm_num)
theorem B2779301 : Blo 1851627 2779301 := bbase (se 4 (by rfl) ⟨260559, by rfl⟩ : syracuseStep 2779301 = 521119) (by norm_num)
theorem B1878185 : Blo 1851627 1878185 := bbase (se 2 (by rfl) ⟨704319, by rfl⟩ : syracuseStep 1878185 = 1408639) (by norm_num)
theorem B2967725 : Blo 1851627 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B7514293 : Blo 1851627 7514293 := bbase (se 5 (by rfl) ⟨352232, by rfl⟩ : syracuseStep 7514293 = 704465) (by norm_num)
theorem B3516605 : Blo 1851627 3516605 := bbase (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) (by norm_num)
theorem B2779325 : Blo 1851627 2779325 := bbase (se 3 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 2779325 = 1042247) (by norm_num)
theorem B4688077 : Blo 1851627 4688077 := bbase (se 3 (by rfl) ⟨879014, by rfl⟩ : syracuseStep 4688077 = 1758029) (by norm_num)
theorem B2779349 : Blo 1851627 2779349 := bbase (se 7 (by rfl) ⟨32570, by rfl⟩ : syracuseStep 2779349 = 65141) (by norm_num)
theorem B2779373 : Blo 1851627 2779373 := bbase (se 3 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 2779373 = 1042265) (by norm_num)
theorem B2345213 : Blo 1851627 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B2779397 : Blo 1851627 2779397 := bbase (se 4 (by rfl) ⟨260568, by rfl⟩ : syracuseStep 2779397 = 521137) (by norm_num)
theorem B2083081 : Blo 1851627 2083081 := bbase (se 2 (by rfl) ⟨781155, by rfl⟩ : syracuseStep 2083081 = 1562311) (by norm_num)
theorem B6252821 : Blo 1851627 6252821 := bbase (se 6 (by rfl) ⟨146550, by rfl⟩ : syracuseStep 6252821 = 293101) (by norm_num)
theorem B4450589 : Blo 1851627 4450589 := bbase (se 3 (by rfl) ⟨834485, by rfl⟩ : syracuseStep 4450589 = 1668971) (by norm_num)
theorem B2779421 : Blo 1851627 2779421 := bbase (se 3 (by rfl) ⟨521141, by rfl⟩ : syracuseStep 2779421 = 1042283) (by norm_num)
theorem B2083117 : Blo 1851627 2083117 := bbase (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) (by norm_num)
theorem B13347125 : Blo 1851627 13347125 := bbase (se 5 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 13347125 = 1251293) (by norm_num)
theorem B8898869 : Blo 1851627 8898869 := bbase (se 5 (by rfl) ⟨417134, by rfl⟩ : syracuseStep 8898869 = 834269) (by norm_num)
theorem B2779445 : Blo 1851627 2779445 := bbase (se 5 (by rfl) ⟨130286, by rfl⟩ : syracuseStep 2779445 = 260573) (by norm_num)
theorem B2345269 : Blo 1851627 2345269 := bbase (se 5 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 2345269 = 219869) (by norm_num)
theorem B4688189 : Blo 1851627 4688189 := bbase (se 3 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 4688189 = 1758071) (by norm_num)
theorem B2779469 : Blo 1851627 2779469 := bbase (se 3 (by rfl) ⟨521150, by rfl⟩ : syracuseStep 2779469 = 1042301) (by norm_num)
theorem B2083153 : Blo 1851627 2083153 := bbase (se 2 (by rfl) ⟨781182, by rfl⟩ : syracuseStep 2083153 = 1562365) (by norm_num)
theorem B9382229 : Blo 1851627 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B2779493 : Blo 1851627 2779493 := bbase (se 4 (by rfl) ⟨260577, by rfl⟩ : syracuseStep 2779493 = 521155) (by norm_num)
theorem B2083189 : Blo 1851627 2083189 := bbase (se 5 (by rfl) ⟨97649, by rfl⟩ : syracuseStep 2083189 = 195299) (by norm_num)
theorem B2779517 : Blo 1851627 2779517 := bbase (se 3 (by rfl) ⟨521159, by rfl⟩ : syracuseStep 2779517 = 1042319) (by norm_num)
theorem B2779541 : Blo 1851627 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B2345365 : Blo 1851627 2345365 := bbase (se 6 (by rfl) ⟨54969, by rfl⟩ : syracuseStep 2345365 = 109939) (by norm_num)
theorem B2083225 : Blo 1851627 2083225 := bbase (se 2 (by rfl) ⟨781209, by rfl⟩ : syracuseStep 2083225 = 1562419) (by norm_num)
theorem B8907173 : Blo 1851627 8907173 := bbase (se 4 (by rfl) ⟨835047, by rfl⟩ : syracuseStep 8907173 = 1670095) (by norm_num)
theorem B2779565 : Blo 1851627 2779565 := bbase (se 3 (by rfl) ⟨521168, by rfl⟩ : syracuseStep 2779565 = 1042337) (by norm_num)
theorem B2083261 : Blo 1851627 2083261 := bbase (se 3 (by rfl) ⟨390611, by rfl⟩ : syracuseStep 2083261 = 781223) (by norm_num)
theorem B2779589 : Blo 1851627 2779589 := bbase (se 4 (by rfl) ⟨260586, by rfl⟩ : syracuseStep 2779589 = 521173) (by norm_num)
theorem B4450781 : Blo 1851627 4450781 := bbase (se 3 (by rfl) ⟨834521, by rfl⟩ : syracuseStep 4450781 = 1669043) (by norm_num)
theorem B2779613 : Blo 1851627 2779613 := bbase (se 3 (by rfl) ⟨521177, by rfl⟩ : syracuseStep 2779613 = 1042355) (by norm_num)
theorem B2083297 : Blo 1851627 2083297 := bbase (se 2 (by rfl) ⟨781236, by rfl⟩ : syracuseStep 2083297 = 1562473) (by norm_num)
theorem B2779637 : Blo 1851627 2779637 := bbase (se 5 (by rfl) ⟨130295, by rfl⟩ : syracuseStep 2779637 = 260591) (by norm_num)
theorem B4688381 : Blo 1851627 4688381 := bbase (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) (by norm_num)
theorem B2083333 : Blo 1851627 2083333 := bbase (se 4 (by rfl) ⟨195312, by rfl⟩ : syracuseStep 2083333 = 390625) (by norm_num)
theorem B2779661 : Blo 1851627 2779661 := bbase (se 3 (by rfl) ⟨521186, by rfl⟩ : syracuseStep 2779661 = 1042373) (by norm_num)
theorem B2779685 : Blo 1851627 2779685 := bbase (se 4 (by rfl) ⟨260595, by rfl⟩ : syracuseStep 2779685 = 521191) (by norm_num)
theorem B2083369 : Blo 1851627 2083369 := bbase (se 2 (by rfl) ⟨781263, by rfl⟩ : syracuseStep 2083369 = 1562527) (by norm_num)
theorem B2779709 : Blo 1851627 2779709 := bbase (se 3 (by rfl) ⟨521195, by rfl⟩ : syracuseStep 2779709 = 1042391) (by norm_num)
theorem B2345537 : Blo 1851627 2345537 := bbase (se 2 (by rfl) ⟨879576, by rfl⟩ : syracuseStep 2345537 = 1759153) (by norm_num)
theorem B2083405 : Blo 1851627 2083405 := bbase (se 3 (by rfl) ⟨390638, by rfl⟩ : syracuseStep 2083405 = 781277) (by norm_num)
theorem B10152533 : Blo 1851627 10152533 := bbase (se 8 (by rfl) ⟨59487, by rfl⟩ : syracuseStep 10152533 = 118975) (by norm_num)
theorem B2779733 : Blo 1851627 2779733 := bbase (se 8 (by rfl) ⟨16287, by rfl⟩ : syracuseStep 2779733 = 32575) (by norm_num)
theorem B2779757 : Blo 1851627 2779757 := bbase (se 3 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 2779757 = 1042409) (by norm_num)
theorem B2083441 : Blo 1851627 2083441 := bbase (se 2 (by rfl) ⟨781290, by rfl⟩ : syracuseStep 2083441 = 1562581) (by norm_num)
theorem B2968181 : Blo 1851627 2968181 := bbase (se 5 (by rfl) ⟨139133, by rfl⟩ : syracuseStep 2968181 = 278267) (by norm_num)
theorem B2345593 : Blo 1851627 2345593 := bbase (se 2 (by rfl) ⟨879597, by rfl⟩ : syracuseStep 2345593 = 1759195) (by norm_num)
theorem B2779781 : Blo 1851627 2779781 := bbase (se 4 (by rfl) ⟨260604, by rfl⟩ : syracuseStep 2779781 = 521209) (by norm_num)
theorem B2083477 : Blo 1851627 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B2779805 : Blo 1851627 2779805 := bbase (se 3 (by rfl) ⟨521213, by rfl⟩ : syracuseStep 2779805 = 1042427) (by norm_num)
theorem B2779829 : Blo 1851627 2779829 := bbase (se 5 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 2779829 = 260609) (by norm_num)
theorem B2083513 : Blo 1851627 2083513 := bbase (se 2 (by rfl) ⟨781317, by rfl⟩ : syracuseStep 2083513 = 1562635) (by norm_num)
theorem B6253253 : Blo 1851627 6253253 := bbase (se 4 (by rfl) ⟨586242, by rfl⟩ : syracuseStep 6253253 = 1172485) (by norm_num)
theorem B5278405 : Blo 1851627 5278405 := bbase (se 4 (by rfl) ⟨494850, by rfl⟩ : syracuseStep 5278405 = 989701) (by norm_num)
theorem B2779853 : Blo 1851627 2779853 := bbase (se 3 (by rfl) ⟨521222, by rfl⟩ : syracuseStep 2779853 = 1042445) (by norm_num)
theorem B2345689 : Blo 1851627 2345689 := bbase (se 2 (by rfl) ⟨879633, by rfl⟩ : syracuseStep 2345689 = 1759267) (by norm_num)
theorem B2083549 : Blo 1851627 2083549 := bbase (se 3 (by rfl) ⟨390665, by rfl⟩ : syracuseStep 2083549 = 781331) (by norm_num)
theorem B2779877 : Blo 1851627 2779877 := bbase (se 4 (by rfl) ⟨260613, by rfl⟩ : syracuseStep 2779877 = 521227) (by norm_num)
theorem B9374453 : Blo 1851627 9374453 := bbase (se 5 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 9374453 = 878855) (by norm_num)
theorem B4451069 : Blo 1851627 4451069 := bbase (se 3 (by rfl) ⟨834575, by rfl⟩ : syracuseStep 4451069 = 1669151) (by norm_num)
theorem B2779901 : Blo 1851627 2779901 := bbase (se 3 (by rfl) ⟨521231, by rfl⟩ : syracuseStep 2779901 = 1042463) (by norm_num)
theorem B2083585 : Blo 1851627 2083585 := bbase (se 2 (by rfl) ⟨781344, by rfl⟩ : syracuseStep 2083585 = 1562689) (by norm_num)
theorem B17795861 : Blo 1851627 17795861 := bbase (se 6 (by rfl) ⟨417090, by rfl⟩ : syracuseStep 17795861 = 834181) (by norm_num)
theorem B2779925 : Blo 1851627 2779925 := bbase (se 6 (by rfl) ⟨65154, by rfl⟩ : syracuseStep 2779925 = 130309) (by norm_num)
theorem B2083621 : Blo 1851627 2083621 := bbase (se 4 (by rfl) ⟨195339, by rfl⟩ : syracuseStep 2083621 = 390679) (by norm_num)
theorem B2779949 : Blo 1851627 2779949 := bbase (se 3 (by rfl) ⟨521240, by rfl⟩ : syracuseStep 2779949 = 1042481) (by norm_num)
theorem B1878833 : Blo 1851627 1878833 := bbase (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) (by norm_num)
theorem B3337013 : Blo 1851627 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B1878841 : Blo 1851627 1878841 := bbase (se 2 (by rfl) ⟨704565, by rfl⟩ : syracuseStep 1878841 = 1409131) (by norm_num)
theorem B2779973 : Blo 1851627 2779973 := bbase (se 4 (by rfl) ⟨260622, by rfl⟩ : syracuseStep 2779973 = 521245) (by norm_num)
theorem B2083657 : Blo 1851627 2083657 := bbase (se 2 (by rfl) ⟨781371, by rfl⟩ : syracuseStep 2083657 = 1562743) (by norm_num)
theorem B4688725 : Blo 1851627 4688725 := bbase (se 9 (by rfl) ⟨13736, by rfl⟩ : syracuseStep 4688725 = 27473) (by norm_num)
theorem B2779997 : Blo 1851627 2779997 := bbase (se 3 (by rfl) ⟨521249, by rfl⟩ : syracuseStep 2779997 = 1042499) (by norm_num)
theorem B7129957 : Blo 1851627 7129957 := bbase (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) (by norm_num)
theorem B2083693 : Blo 1851627 2083693 := bbase (se 3 (by rfl) ⟨390692, by rfl⟩ : syracuseStep 2083693 = 781385) (by norm_num)
theorem B2780021 : Blo 1851627 2780021 := bbase (se 5 (by rfl) ⟨130313, by rfl⟩ : syracuseStep 2780021 = 260627) (by norm_num)
theorem B2345861 : Blo 1851627 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B2780045 : Blo 1851627 2780045 := bbase (se 3 (by rfl) ⟨521258, by rfl⟩ : syracuseStep 2780045 = 1042517) (by norm_num)
theorem B2083729 : Blo 1851627 2083729 := bbase (se 2 (by rfl) ⟨781398, by rfl⟩ : syracuseStep 2083729 = 1562797) (by norm_num)
theorem B2780069 : Blo 1851627 2780069 := bbase (se 4 (by rfl) ⟨260631, by rfl⟩ : syracuseStep 2780069 = 521263) (by norm_num)
theorem B3517357 : Blo 1851627 3517357 := bbase (se 3 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 3517357 = 1319009) (by norm_num)
theorem B2083765 : Blo 1851627 2083765 := bbase (se 5 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 2083765 = 195353) (by norm_num)
theorem B2780093 : Blo 1851627 2780093 := bbase (se 3 (by rfl) ⟨521267, by rfl⟩ : syracuseStep 2780093 = 1042535) (by norm_num)
theorem B2345917 : Blo 1851627 2345917 := bbase (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) (by norm_num)
theorem B4688837 : Blo 1851627 4688837 := bbase (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) (by norm_num)
theorem B2780117 : Blo 1851627 2780117 := bbase (se 7 (by rfl) ⟨32579, by rfl⟩ : syracuseStep 2780117 = 65159) (by norm_num)
theorem B2083801 : Blo 1851627 2083801 := bbase (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) (by norm_num)
theorem B2780141 : Blo 1851627 2780141 := bbase (se 3 (by rfl) ⟨521276, by rfl⟩ : syracuseStep 2780141 = 1042553) (by norm_num)
theorem B2083837 : Blo 1851627 2083837 := bbase (se 3 (by rfl) ⟨390719, by rfl⟩ : syracuseStep 2083837 = 781439) (by norm_num)
theorem B2780165 : Blo 1851627 2780165 := bbase (se 4 (by rfl) ⟨260640, by rfl⟩ : syracuseStep 2780165 = 521281) (by norm_num)
theorem B1977373 : Blo 1851627 1977373 := bbase (se 3 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 1977373 = 741515) (by norm_num)
theorem B2780189 : Blo 1851627 2780189 := bbase (se 3 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 2780189 = 1042571) (by norm_num)
theorem B2083873 : Blo 1851627 2083873 := bbase (se 2 (by rfl) ⟨781452, by rfl⟩ : syracuseStep 2083873 = 1562905) (by norm_num)
theorem B2780213 : Blo 1851627 2780213 := bbase (se 5 (by rfl) ⟨130322, by rfl⟩ : syracuseStep 2780213 = 260645) (by norm_num)
theorem B3517501 : Blo 1851627 3517501 := bbase (se 3 (by rfl) ⟨659531, by rfl⟩ : syracuseStep 3517501 = 1319063) (by norm_num)
theorem B2083909 : Blo 1851627 2083909 := bbase (se 4 (by rfl) ⟨195366, by rfl⟩ : syracuseStep 2083909 = 390733) (by norm_num)
theorem B2780237 : Blo 1851627 2780237 := bbase (se 3 (by rfl) ⟨521294, by rfl⟩ : syracuseStep 2780237 = 1042589) (by norm_num)
theorem B2780261 : Blo 1851627 2780261 := bbase (se 4 (by rfl) ⟨260649, by rfl⟩ : syracuseStep 2780261 = 521299) (by norm_num)
theorem B2083945 : Blo 1851627 2083945 := bbase (se 2 (by rfl) ⟨781479, by rfl⟩ : syracuseStep 2083945 = 1562959) (by norm_num)
theorem B6253685 : Blo 1851627 6253685 := bbase (se 5 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 6253685 = 586283) (by norm_num)
theorem B2780285 : Blo 1851627 2780285 := bbase (se 3 (by rfl) ⟨521303, by rfl⟩ : syracuseStep 2780285 = 1042607) (by norm_num)
theorem B4689029 : Blo 1851627 4689029 := bbase (se 4 (by rfl) ⟨439596, by rfl⟩ : syracuseStep 4689029 = 879193) (by norm_num)
theorem B2083981 : Blo 1851627 2083981 := bbase (se 3 (by rfl) ⟨390746, by rfl⟩ : syracuseStep 2083981 = 781493) (by norm_num)
theorem B2780309 : Blo 1851627 2780309 := bbase (se 6 (by rfl) ⟨65163, by rfl⟩ : syracuseStep 2780309 = 130327) (by norm_num)
theorem B2780333 : Blo 1851627 2780333 := bbase (se 3 (by rfl) ⟨521312, by rfl⟩ : syracuseStep 2780333 = 1042625) (by norm_num)
theorem B2084017 : Blo 1851627 2084017 := bbase (se 2 (by rfl) ⟨781506, by rfl⟩ : syracuseStep 2084017 = 1563013) (by norm_num)
theorem B2780357 : Blo 1851627 2780357 := bbase (se 4 (by rfl) ⟨260658, by rfl⟩ : syracuseStep 2780357 = 521317) (by norm_num)
theorem B2084053 : Blo 1851627 2084053 := bbase (se 7 (by rfl) ⟨24422, by rfl⟩ : syracuseStep 2084053 = 48845) (by norm_num)
theorem B3517661 : Blo 1851627 3517661 := bbase (se 3 (by rfl) ⟨659561, by rfl⟩ : syracuseStep 3517661 = 1319123) (by norm_num)
theorem B2780381 : Blo 1851627 2780381 := bbase (se 3 (by rfl) ⟨521321, by rfl⟩ : syracuseStep 2780381 = 1042643) (by norm_num)
theorem B5631221 : Blo 1851627 5631221 := bbase (se 5 (by rfl) ⟨263963, by rfl⟩ : syracuseStep 5631221 = 527927) (by norm_num)
theorem B2780405 : Blo 1851627 2780405 := bbase (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) (by norm_num)
theorem B2084089 : Blo 1851627 2084089 := bbase (se 2 (by rfl) ⟨781533, by rfl⟩ : syracuseStep 2084089 = 1563067) (by norm_num)
theorem B2780429 : Blo 1851627 2780429 := bbase (se 3 (by rfl) ⟨521330, by rfl⟩ : syracuseStep 2780429 = 1042661) (by norm_num)
theorem B11865365 : Blo 1851627 11865365 := bbase (se 6 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 11865365 = 556189) (by norm_num)
theorem B1977625 : Blo 1851627 1977625 := bbase (se 2 (by rfl) ⟨741609, by rfl⟩ : syracuseStep 1977625 = 1483219) (by norm_num)
theorem B1977629 : Blo 1851627 1977629 := bbase (se 3 (by rfl) ⟨370805, by rfl⟩ : syracuseStep 1977629 = 741611) (by norm_num)
theorem B2084125 : Blo 1851627 2084125 := bbase (se 3 (by rfl) ⟨390773, by rfl⟩ : syracuseStep 2084125 = 781547) (by norm_num)
theorem B2084161 : Blo 1851627 2084161 := bbase (se 2 (by rfl) ⟨781560, by rfl⟩ : syracuseStep 2084161 = 1563121) (by norm_num)
theorem B2084197 : Blo 1851627 2084197 := bbase (se 4 (by rfl) ⟨195393, by rfl⟩ : syracuseStep 2084197 = 390787) (by norm_num)
theorem B3517805 : Blo 1851627 3517805 := bbase (se 3 (by rfl) ⟨659588, by rfl⟩ : syracuseStep 3517805 = 1319177) (by norm_num)
theorem B2084233 : Blo 1851627 2084233 := bbase (se 2 (by rfl) ⟨781587, by rfl⟩ : syracuseStep 2084233 = 1563175) (by norm_num)
theorem B2084269 : Blo 1851627 2084269 := bbase (se 3 (by rfl) ⟨390800, by rfl⟩ : syracuseStep 2084269 = 781601) (by norm_num)
theorem B3124669 : Blo 1851627 3124669 := bbase (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) (by norm_num)
theorem B2256317 : Blo 1851627 2256317 := bbase (se 3 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 2256317 = 846119) (by norm_num)
theorem B2084305 : Blo 1851627 2084305 := bbase (se 2 (by rfl) ⟨781614, by rfl⟩ : syracuseStep 2084305 = 1563229) (by norm_num)
theorem B4009429 : Blo 1851627 4009429 := bbase (se 7 (by rfl) ⟨46985, by rfl⟩ : syracuseStep 4009429 = 93971) (by norm_num)
theorem B4689373 : Blo 1851627 4689373 := bbase (se 3 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 4689373 = 1758515) (by norm_num)
theorem B2084341 : Blo 1851627 2084341 := bbase (se 5 (by rfl) ⟨97703, by rfl⟩ : syracuseStep 2084341 = 195407) (by norm_num)
theorem B7917061 : Blo 1851627 7917061 := bbase (se 4 (by rfl) ⟨742224, by rfl⟩ : syracuseStep 7917061 = 1484449) (by norm_num)
theorem B3124757 : Blo 1851627 3124757 := bbase (se 6 (by rfl) ⟨73236, by rfl⟩ : syracuseStep 3124757 = 146473) (by norm_num)
theorem B7917077 : Blo 1851627 7917077 := bbase (se 6 (by rfl) ⟨185556, by rfl⟩ : syracuseStep 7917077 = 371113) (by norm_num)
theorem B2084377 : Blo 1851627 2084377 := bbase (se 2 (by rfl) ⟨781641, by rfl⟩ : syracuseStep 2084377 = 1563283) (by norm_num)
theorem B6254117 : Blo 1851627 6254117 := bbase (se 4 (by rfl) ⟨586323, by rfl⟩ : syracuseStep 6254117 = 1172647) (by norm_num)
theorem B2084413 : Blo 1851627 2084413 := bbase (se 3 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 2084413 = 781655) (by norm_num)
theorem B4689485 : Blo 1851627 4689485 := bbase (se 3 (by rfl) ⟨879278, by rfl⟩ : syracuseStep 4689485 = 1758557) (by norm_num)
theorem B2084449 : Blo 1851627 2084449 := bbase (se 2 (by rfl) ⟨781668, by rfl⟩ : syracuseStep 2084449 = 1563337) (by norm_num)
theorem B9383525 : Blo 1851627 9383525 := bbase (se 4 (by rfl) ⟨879705, by rfl⟩ : syracuseStep 9383525 = 1759411) (by norm_num)
theorem B2084485 : Blo 1851627 2084485 := bbase (se 4 (by rfl) ⟨195420, by rfl⟩ : syracuseStep 2084485 = 390841) (by norm_num)
theorem B3518093 : Blo 1851627 3518093 := bbase (se 3 (by rfl) ⟨659642, by rfl⟩ : syracuseStep 3518093 = 1319285) (by norm_num)
theorem B3124885 : Blo 1851627 3124885 := bbase (se 6 (by rfl) ⟨73239, by rfl⟩ : syracuseStep 3124885 = 146479) (by norm_num)
theorem B3526301 : Blo 1851627 3526301 := bbase (se 3 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 3526301 = 1322363) (by norm_num)
theorem B2084521 : Blo 1851627 2084521 := bbase (se 2 (by rfl) ⟨781695, by rfl⟩ : syracuseStep 2084521 = 1563391) (by norm_num)
theorem B8900293 : Blo 1851627 8900293 := bbase (se 4 (by rfl) ⟨834402, by rfl⟩ : syracuseStep 8900293 = 1668805) (by norm_num)
theorem B2084557 : Blo 1851627 2084557 := bbase (se 3 (by rfl) ⟨390854, by rfl⟩ : syracuseStep 2084557 = 781709) (by norm_num)
theorem B3124973 : Blo 1851627 3124973 := bbase (se 3 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 3124973 = 1171865) (by norm_num)
theorem B2084593 : Blo 1851627 2084593 := bbase (se 2 (by rfl) ⟨781722, by rfl⟩ : syracuseStep 2084593 = 1563445) (by norm_num)
theorem B4689677 : Blo 1851627 4689677 := bbase (se 3 (by rfl) ⟨879314, by rfl⟩ : syracuseStep 4689677 = 1758629) (by norm_num)
theorem B2084629 : Blo 1851627 2084629 := bbase (se 6 (by rfl) ⟨48858, by rfl⟩ : syracuseStep 2084629 = 97717) (by norm_num)
theorem B3518245 : Blo 1851627 3518245 := bbase (se 4 (by rfl) ⟨329835, by rfl⟩ : syracuseStep 3518245 = 659671) (by norm_num)
theorem B2748205 : Blo 1851627 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B2084665 : Blo 1851627 2084665 := bbase (se 2 (by rfl) ⟨781749, by rfl⟩ : syracuseStep 2084665 = 1563499) (by norm_num)
theorem B1978193 : Blo 1851627 1978193 := bbase (se 2 (by rfl) ⟨741822, by rfl⟩ : syracuseStep 1978193 = 1483645) (by norm_num)
theorem B2084701 : Blo 1851627 2084701 := bbase (se 3 (by rfl) ⟨390881, by rfl⟩ : syracuseStep 2084701 = 781763) (by norm_num)
theorem B3125101 : Blo 1851627 3125101 := bbase (se 3 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 3125101 = 1171913) (by norm_num)
theorem B2854765 : Blo 1851627 2854765 := bbase (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) (by norm_num)
theorem B2084737 : Blo 1851627 2084737 := bbase (se 2 (by rfl) ⟨781776, by rfl⟩ : syracuseStep 2084737 = 1563553) (by norm_num)
theorem B2084773 : Blo 1851627 2084773 := bbase (se 4 (by rfl) ⟨195447, by rfl⟩ : syracuseStep 2084773 = 390895) (by norm_num)
theorem B3125189 : Blo 1851627 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B2084809 : Blo 1851627 2084809 := bbase (se 2 (by rfl) ⟨781803, by rfl⟩ : syracuseStep 2084809 = 1563607) (by norm_num)
theorem B4009933 : Blo 1851627 4009933 := bbase (se 3 (by rfl) ⟨751862, by rfl⟩ : syracuseStep 4009933 = 1503725) (by norm_num)
theorem B6254549 : Blo 1851627 6254549 := bbase (se 7 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 6254549 = 146591) (by norm_num)
theorem B2084845 : Blo 1851627 2084845 := bbase (se 3 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 2084845 = 781817) (by norm_num)
theorem B9375749 : Blo 1851627 9375749 := bbase (se 4 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 9375749 = 1757953) (by norm_num)
theorem B1978381 : Blo 1851627 1978381 := bbase (se 3 (by rfl) ⟨370946, by rfl⟩ : syracuseStep 1978381 = 741893) (by norm_num)
theorem B2084881 : Blo 1851627 2084881 := bbase (se 2 (by rfl) ⟨781830, by rfl⟩ : syracuseStep 2084881 = 1563661) (by norm_num)
theorem B2084917 : Blo 1851627 2084917 := bbase (se 5 (by rfl) ⟨97730, by rfl⟩ : syracuseStep 2084917 = 195461) (by norm_num)
theorem B3125317 : Blo 1851627 3125317 := bbase (se 4 (by rfl) ⟨292998, by rfl⟩ : syracuseStep 3125317 = 585997) (by norm_num)
theorem B3518549 : Blo 1851627 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1929305 : Blo 1851627 1929305 := bbase (se 2 (by rfl) ⟨723489, by rfl⟩ : syracuseStep 1929305 = 1446979) (by norm_num)
theorem B2084953 : Blo 1851627 2084953 := bbase (se 2 (by rfl) ⟨781857, by rfl⟩ : syracuseStep 2084953 = 1563715) (by norm_num)
theorem B4690021 : Blo 1851627 4690021 := bbase (se 4 (by rfl) ⟨439689, by rfl⟩ : syracuseStep 4690021 = 879379) (by norm_num)
theorem B2084989 : Blo 1851627 2084989 := bbase (se 3 (by rfl) ⟨390935, by rfl⟩ : syracuseStep 2084989 = 781871) (by norm_num)
theorem B4509829 : Blo 1851627 4509829 := bbase (se 4 (by rfl) ⟨422796, by rfl⟩ : syracuseStep 4509829 = 845593) (by norm_num)
theorem B3125405 : Blo 1851627 3125405 := bbase (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) (by norm_num)
theorem B2085025 : Blo 1851627 2085025 := bbase (se 2 (by rfl) ⟨781884, by rfl⟩ : syracuseStep 2085025 = 1563769) (by norm_num)
theorem B7033013 : Blo 1851627 7033013 := bbase (se 5 (by rfl) ⟨329672, by rfl⟩ : syracuseStep 7033013 = 659345) (by norm_num)
theorem B2085061 : Blo 1851627 2085061 := bbase (se 4 (by rfl) ⟨195474, by rfl⟩ : syracuseStep 2085061 = 390949) (by norm_num)
theorem B4690133 : Blo 1851627 4690133 := bbase (se 7 (by rfl) ⟨54962, by rfl⟩ : syracuseStep 4690133 = 109925) (by norm_num)
theorem B2085097 : Blo 1851627 2085097 := bbase (se 2 (by rfl) ⟨781911, by rfl⟩ : syracuseStep 2085097 = 1563823) (by norm_num)
theorem B2085133 : Blo 1851627 2085133 := bbase (se 3 (by rfl) ⟨390962, by rfl⟩ : syracuseStep 2085133 = 781925) (by norm_num)
theorem B3125533 : Blo 1851627 3125533 := bbase (se 3 (by rfl) ⟨586037, by rfl⟩ : syracuseStep 3125533 = 1172075) (by norm_num)
theorem B3338533 : Blo 1851627 3338533 := bbase (se 4 (by rfl) ⟨312987, by rfl⟩ : syracuseStep 3338533 = 625975) (by norm_num)
theorem B2674981 : Blo 1851627 2674981 := bbase (se 4 (by rfl) ⟨250779, by rfl⟩ : syracuseStep 2674981 = 501559) (by norm_num)
theorem B2085169 : Blo 1851627 2085169 := bbase (se 2 (by rfl) ⟨781938, by rfl⟩ : syracuseStep 2085169 = 1563877) (by norm_num)
theorem B2085205 : Blo 1851627 2085205 := bbase (se 10 (by rfl) ⟨3054, by rfl⟩ : syracuseStep 2085205 = 6109) (by norm_num)
theorem B3125621 : Blo 1851627 3125621 := bbase (se 5 (by rfl) ⟨146513, by rfl⟩ : syracuseStep 3125621 = 293027) (by norm_num)
theorem B5935477 : Blo 1851627 5935477 := bbase (se 5 (by rfl) ⟨278225, by rfl⟩ : syracuseStep 5935477 = 556451) (by norm_num)
theorem B2085241 : Blo 1851627 2085241 := bbase (se 2 (by rfl) ⟨781965, by rfl⟩ : syracuseStep 2085241 = 1563931) (by norm_num)
theorem B6254981 : Blo 1851627 6254981 := bbase (se 4 (by rfl) ⟨586404, by rfl⟩ : syracuseStep 6254981 = 1172809) (by norm_num)
theorem B4690325 : Blo 1851627 4690325 := bbase (se 6 (by rfl) ⟨109929, by rfl⟩ : syracuseStep 4690325 = 219859) (by norm_num)
theorem B2085277 : Blo 1851627 2085277 := bbase (se 3 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 2085277 = 781979) (by norm_num)
theorem B10555829 : Blo 1851627 10555829 := bbase (se 5 (by rfl) ⟨494804, by rfl⟩ : syracuseStep 10555829 = 989609) (by norm_num)
theorem B2085313 : Blo 1851627 2085313 := bbase (se 2 (by rfl) ⟨781992, by rfl⟩ : syracuseStep 2085313 = 1563985) (by norm_num)
theorem B7033301 : Blo 1851627 7033301 := bbase (se 7 (by rfl) ⟨82421, by rfl⟩ : syracuseStep 7033301 = 164843) (by norm_num)
theorem B3125749 : Blo 1851627 3125749 := bbase (se 5 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 3125749 = 293039) (by norm_num)
theorem B17814005 : Blo 1851627 17814005 := bbase (se 5 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 17814005 = 1670063) (by norm_num)
theorem B4166189 : Blo 1851627 4166189 := bbase (se 3 (by rfl) ⟨781160, by rfl⟩ : syracuseStep 4166189 = 1562321) (by norm_num)
theorem B10547765 : Blo 1851627 10547765 := bbase (se 5 (by rfl) ⟨494426, by rfl⟩ : syracuseStep 10547765 = 988853) (by norm_num)
theorem B3125837 : Blo 1851627 3125837 := bbase (se 3 (by rfl) ⟨586094, by rfl⟩ : syracuseStep 3125837 = 1172189) (by norm_num)
theorem B4223597 : Blo 1851627 4223597 := bbase (se 3 (by rfl) ⟨791924, by rfl⟩ : syracuseStep 4223597 = 1583849) (by norm_num)
theorem B4166261 : Blo 1851627 4166261 := bbase (se 5 (by rfl) ⟨195293, by rfl⟩ : syracuseStep 4166261 = 390587) (by norm_num)
theorem B4166333 : Blo 1851627 4166333 := bbase (se 3 (by rfl) ⟨781187, by rfl⟩ : syracuseStep 4166333 = 1562375) (by norm_num)
theorem B3125965 : Blo 1851627 3125965 := bbase (se 3 (by rfl) ⟨586118, by rfl⟩ : syracuseStep 3125965 = 1172237) (by norm_num)
theorem B4453069 : Blo 1851627 4453069 := bbase (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) (by norm_num)
theorem B22852309 : Blo 1851627 22852309 := bbase (se 7 (by rfl) ⟨267800, by rfl⟩ : syracuseStep 22852309 = 535601) (by norm_num)
theorem B4690669 : Blo 1851627 4690669 := bbase (se 3 (by rfl) ⟨879500, by rfl⟩ : syracuseStep 4690669 = 1759001) (by norm_num)
theorem B10695413 : Blo 1851627 10695413 := bbase (se 5 (by rfl) ⟨501347, by rfl⟩ : syracuseStep 10695413 = 1002695) (by norm_num)
theorem B4166405 : Blo 1851627 4166405 := bbase (se 4 (by rfl) ⟨390600, by rfl⟩ : syracuseStep 4166405 = 781201) (by norm_num)
theorem B3126053 : Blo 1851627 3126053 := bbase (se 4 (by rfl) ⟨293067, by rfl⟩ : syracuseStep 3126053 = 586135) (by norm_num)
theorem B6255413 : Blo 1851627 6255413 := bbase (se 5 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 6255413 = 586445) (by norm_num)
theorem B1979201 : Blo 1851627 1979201 := bbase (se 2 (by rfl) ⟨742200, by rfl⟩ : syracuseStep 1979201 = 1484401) (by norm_num)
theorem B4166477 : Blo 1851627 4166477 := bbase (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) (by norm_num)
theorem B10695509 : Blo 1851627 10695509 := bbase (se 9 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 10695509 = 62669) (by norm_num)
theorem B4690781 : Blo 1851627 4690781 := bbase (se 3 (by rfl) ⟨879521, by rfl⟩ : syracuseStep 4690781 = 1759043) (by norm_num)
theorem B4166549 : Blo 1851627 4166549 := bbase (se 6 (by rfl) ⟨97653, by rfl⟩ : syracuseStep 4166549 = 195307) (by norm_num)
theorem B3126181 : Blo 1851627 3126181 := bbase (se 4 (by rfl) ⟨293079, by rfl⟩ : syracuseStep 3126181 = 586159) (by norm_num)
theorem B4166621 : Blo 1851627 4166621 := bbase (se 3 (by rfl) ⟨781241, by rfl⟩ : syracuseStep 4166621 = 1562483) (by norm_num)
theorem B3126269 : Blo 1851627 3126269 := bbase (se 3 (by rfl) ⟨586175, by rfl⟩ : syracuseStep 3126269 = 1172351) (by norm_num)
theorem B4690973 : Blo 1851627 4690973 := bbase (se 3 (by rfl) ⟨879557, by rfl⟩ : syracuseStep 4690973 = 1759115) (by norm_num)
theorem B4166693 : Blo 1851627 4166693 := bbase (se 4 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 4166693 = 781255) (by norm_num)
theorem B2225189 : Blo 1851627 2225189 := bbase (se 4 (by rfl) ⟨208611, by rfl⟩ : syracuseStep 2225189 = 417223) (by norm_num)
theorem B4510765 : Blo 1851627 4510765 := bbase (se 3 (by rfl) ⟨845768, by rfl⟩ : syracuseStep 4510765 = 1691537) (by norm_num)
theorem B3339325 : Blo 1851627 3339325 := bbase (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) (by norm_num)
theorem B4166765 : Blo 1851627 4166765 := bbase (se 3 (by rfl) ⟨781268, by rfl⟩ : syracuseStep 4166765 = 1562537) (by norm_num)
theorem B3126397 : Blo 1851627 3126397 := bbase (se 3 (by rfl) ⟨586199, by rfl⟩ : syracuseStep 3126397 = 1172399) (by norm_num)
theorem B4166837 : Blo 1851627 4166837 := bbase (se 5 (by rfl) ⟨195320, by rfl⟩ : syracuseStep 4166837 = 390641) (by norm_num)
theorem B3757261 : Blo 1851627 3757261 := bbase (se 3 (by rfl) ⟨704486, by rfl⟩ : syracuseStep 3757261 = 1408973) (by norm_num)
theorem B3126485 : Blo 1851627 3126485 := bbase (se 7 (by rfl) ⟨36638, by rfl⟩ : syracuseStep 3126485 = 73277) (by norm_num)
theorem B6255845 : Blo 1851627 6255845 := bbase (se 4 (by rfl) ⟨586485, by rfl⟩ : syracuseStep 6255845 = 1172971) (by norm_num)
theorem B4166909 : Blo 1851627 4166909 := bbase (se 3 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 4166909 = 1562591) (by norm_num)
theorem B9377045 : Blo 1851627 9377045 := bbase (se 6 (by rfl) ⟨219774, by rfl⟩ : syracuseStep 9377045 = 439549) (by norm_num)
theorem B4166981 : Blo 1851627 4166981 := bbase (se 4 (by rfl) ⟨390654, by rfl⟩ : syracuseStep 4166981 = 781309) (by norm_num)
theorem B3126613 : Blo 1851627 3126613 := bbase (se 13 (by rfl) ⟨572, by rfl⟩ : syracuseStep 3126613 = 1145) (by norm_num)
theorem B2225497 : Blo 1851627 2225497 := bbase (se 2 (by rfl) ⟨834561, by rfl⟩ : syracuseStep 2225497 = 1669123) (by norm_num)
theorem B14071157 : Blo 1851627 14071157 := bbase (se 5 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 14071157 = 1319171) (by norm_num)
theorem B4691317 : Blo 1851627 4691317 := bbase (se 5 (by rfl) ⟨219905, by rfl⟩ : syracuseStep 4691317 = 439811) (by norm_num)
theorem B4167053 : Blo 1851627 4167053 := bbase (se 3 (by rfl) ⟨781322, by rfl⟩ : syracuseStep 4167053 = 1562645) (by norm_num)
theorem B3126701 : Blo 1851627 3126701 := bbase (se 3 (by rfl) ⟨586256, by rfl⟩ : syracuseStep 3126701 = 1172513) (by norm_num)
theorem B3339701 : Blo 1851627 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B4167125 : Blo 1851627 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B4691429 : Blo 1851627 4691429 := bbase (se 4 (by rfl) ⟨439821, by rfl⟩ : syracuseStep 4691429 = 879643) (by norm_num)
theorem B4167197 : Blo 1851627 4167197 := bbase (se 3 (by rfl) ⟨781349, by rfl⟩ : syracuseStep 4167197 = 1562699) (by norm_num)
theorem B3126829 : Blo 1851627 3126829 := bbase (se 3 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 3126829 = 1172561) (by norm_num)
theorem B2225713 : Blo 1851627 2225713 := bbase (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) (by norm_num)
theorem B4167269 : Blo 1851627 4167269 := bbase (se 4 (by rfl) ⟨390681, by rfl⟩ : syracuseStep 4167269 = 781363) (by norm_num)
theorem B7034485 : Blo 1851627 7034485 := bbase (se 5 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 7034485 = 659483) (by norm_num)
theorem B3126917 : Blo 1851627 3126917 := bbase (se 4 (by rfl) ⟨293148, by rfl⟩ : syracuseStep 3126917 = 586297) (by norm_num)
theorem B3167885 : Blo 1851627 3167885 := bbase (se 3 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 3167885 = 1187957) (by norm_num)
theorem B4691621 : Blo 1851627 4691621 := bbase (se 4 (by rfl) ⟨439839, by rfl⟩ : syracuseStep 4691621 = 879679) (by norm_num)
theorem B4167341 : Blo 1851627 4167341 := bbase (se 3 (by rfl) ⟨781376, by rfl⟩ : syracuseStep 4167341 = 1562753) (by norm_num)
theorem B4167413 : Blo 1851627 4167413 := bbase (se 5 (by rfl) ⟨195347, by rfl⟩ : syracuseStep 4167413 = 390695) (by norm_num)
theorem B3127045 : Blo 1851627 3127045 := bbase (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) (by norm_num)
theorem B14063381 : Blo 1851627 14063381 := bbase (se 6 (by rfl) ⟨329610, by rfl⟩ : syracuseStep 14063381 = 659221) (by norm_num)
theorem B20035349 : Blo 1851627 20035349 := bbase (se 6 (by rfl) ⟨469578, by rfl⟩ : syracuseStep 20035349 = 939157) (by norm_num)
theorem B4167485 : Blo 1851627 4167485 := bbase (se 3 (by rfl) ⟨781403, by rfl⟩ : syracuseStep 4167485 = 1562807) (by norm_num)
theorem B3127133 : Blo 1851627 3127133 := bbase (se 3 (by rfl) ⟨586337, by rfl⟩ : syracuseStep 3127133 = 1172675) (by norm_num)
theorem B7911269 : Blo 1851627 7911269 := bbase (se 4 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 7911269 = 1483363) (by norm_num)
theorem B4167557 : Blo 1851627 4167557 := bbase (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) (by norm_num)
theorem B4511621 : Blo 1851627 4511621 := bbase (se 4 (by rfl) ⟨422964, by rfl⟩ : syracuseStep 4511621 = 845929) (by norm_num)
theorem B7034789 : Blo 1851627 7034789 := bbase (se 4 (by rfl) ⟨659511, by rfl⟩ : syracuseStep 7034789 = 1319023) (by norm_num)
theorem B4167629 : Blo 1851627 4167629 := bbase (se 3 (by rfl) ⟨781430, by rfl⟩ : syracuseStep 4167629 = 1562861) (by norm_num)
theorem B3127261 : Blo 1851627 3127261 := bbase (se 3 (by rfl) ⟨586361, by rfl⟩ : syracuseStep 3127261 = 1172723) (by norm_num)
theorem B4691965 : Blo 1851627 4691965 := bbase (se 3 (by rfl) ⟨879743, by rfl⟩ : syracuseStep 4691965 = 1759487) (by norm_num)
theorem B4167701 : Blo 1851627 4167701 := bbase (se 6 (by rfl) ⟨97680, by rfl⟩ : syracuseStep 4167701 = 195361) (by norm_num)
theorem B3127349 : Blo 1851627 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B4167773 : Blo 1851627 4167773 := bbase (se 3 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 4167773 = 1562915) (by norm_num)
theorem B2226313 : Blo 1851627 2226313 := bbase (se 2 (by rfl) ⟨834867, by rfl⟩ : syracuseStep 2226313 = 1669735) (by norm_num)
theorem B4167845 : Blo 1851627 4167845 := bbase (se 4 (by rfl) ⟨390735, by rfl⟩ : syracuseStep 4167845 = 781471) (by norm_num)
theorem B3127477 : Blo 1851627 3127477 := bbase (se 5 (by rfl) ⟨146600, by rfl⟩ : syracuseStep 3127477 = 293201) (by norm_num)
theorem B4167917 : Blo 1851627 4167917 := bbase (se 3 (by rfl) ⟨781484, by rfl⟩ : syracuseStep 4167917 = 1562969) (by norm_num)
theorem B15833333 : Blo 1851627 15833333 := bbase (se 5 (by rfl) ⟨742187, by rfl⟩ : syracuseStep 15833333 = 1484375) (by norm_num)
theorem B3127565 : Blo 1851627 3127565 := bbase (se 3 (by rfl) ⟨586418, by rfl⟩ : syracuseStep 3127565 = 1172837) (by norm_num)
theorem B4167989 : Blo 1851627 4167989 := bbase (se 5 (by rfl) ⟨195374, by rfl⟩ : syracuseStep 4167989 = 390749) (by norm_num)
theorem B9509237 : Blo 1851627 9509237 := bbase (se 5 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 9509237 = 891491) (by norm_num)
theorem B4168061 : Blo 1851627 4168061 := bbase (se 3 (by rfl) ⟨781511, by rfl⟩ : syracuseStep 4168061 = 1563023) (by norm_num)
theorem B3127693 : Blo 1851627 3127693 := bbase (se 3 (by rfl) ⟨586442, by rfl⟩ : syracuseStep 3127693 = 1172885) (by norm_num)
theorem B2816437 : Blo 1851627 2816437 := bbase (se 5 (by rfl) ⟨132020, by rfl⟩ : syracuseStep 2816437 = 264041) (by norm_num)
theorem B4168133 : Blo 1851627 4168133 := bbase (se 4 (by rfl) ⟨390762, by rfl⟩ : syracuseStep 4168133 = 781525) (by norm_num)
theorem B3127781 : Blo 1851627 3127781 := bbase (se 4 (by rfl) ⟨293229, by rfl⟩ : syracuseStep 3127781 = 586459) (by norm_num)
theorem B4168205 : Blo 1851627 4168205 := bbase (se 3 (by rfl) ⟨781538, by rfl⟩ : syracuseStep 4168205 = 1563077) (by norm_num)
theorem B21092885 : Blo 1851627 21092885 := bbase (se 6 (by rfl) ⟨494364, by rfl⟩ : syracuseStep 21092885 = 988729) (by norm_num)
theorem B9378341 : Blo 1851627 9378341 := bbase (se 4 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 9378341 = 1758439) (by norm_num)
theorem B3168821 : Blo 1851627 3168821 := bbase (se 5 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 3168821 = 297077) (by norm_num)
theorem B4168277 : Blo 1851627 4168277 := bbase (se 8 (by rfl) ⟨24423, by rfl⟩ : syracuseStep 4168277 = 48847) (by norm_num)
theorem B7223909 : Blo 1851627 7223909 := bbase (se 4 (by rfl) ⟨677241, by rfl⟩ : syracuseStep 7223909 = 1354483) (by norm_num)
theorem B3127909 : Blo 1851627 3127909 := bbase (se 4 (by rfl) ⟨293241, by rfl⟩ : syracuseStep 3127909 = 586483) (by norm_num)
theorem B4168349 : Blo 1851627 4168349 := bbase (se 3 (by rfl) ⟨781565, by rfl⟩ : syracuseStep 4168349 = 1563131) (by norm_num)
theorem B2005669 : Blo 1851627 2005669 := bbase (se 4 (by rfl) ⟨188031, by rfl⟩ : syracuseStep 2005669 = 376063) (by norm_num)
theorem B3127997 : Blo 1851627 3127997 := bbase (se 3 (by rfl) ⟨586499, by rfl⟩ : syracuseStep 3127997 = 1172999) (by norm_num)
theorem B3955429 : Blo 1851627 3955429 := bbase (se 4 (by rfl) ⟨370821, by rfl⟩ : syracuseStep 3955429 = 741643) (by norm_num)
theorem B4168421 : Blo 1851627 4168421 := bbase (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) (by norm_num)
theorem B7133941 : Blo 1851627 7133941 := bbase (se 5 (by rfl) ⟨334403, by rfl⟩ : syracuseStep 7133941 = 668807) (by norm_num)
theorem B4168493 : Blo 1851627 4168493 := bbase (se 3 (by rfl) ⟨781592, by rfl⟩ : syracuseStep 4168493 = 1563185) (by norm_num)
theorem B4225861 : Blo 1851627 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B3955549 : Blo 1851627 3955549 := bbase (se 3 (by rfl) ⟨741665, by rfl⟩ : syracuseStep 3955549 = 1483331) (by norm_num)
theorem B2112365 : Blo 1851627 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B4168565 : Blo 1851627 4168565 := bbase (se 5 (by rfl) ⟨195401, by rfl⟩ : syracuseStep 4168565 = 390803) (by norm_num)
theorem B6249365 : Blo 1851627 6249365 := bbase (se 6 (by rfl) ⟨146469, by rfl⟩ : syracuseStep 6249365 = 292939) (by norm_num)
theorem B2636725 : Blo 1851627 2636725 := bbase (se 5 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 2636725 = 247193) (by norm_num)
theorem B4168637 : Blo 1851627 4168637 := bbase (se 3 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 4168637 = 1563239) (by norm_num)
theorem B4168709 : Blo 1851627 4168709 := bbase (se 4 (by rfl) ⟨390816, by rfl⟩ : syracuseStep 4168709 = 781633) (by norm_num)
theorem B4168781 : Blo 1851627 4168781 := bbase (se 3 (by rfl) ⟨781646, by rfl⟩ : syracuseStep 4168781 = 1563293) (by norm_num)
theorem B9501781 : Blo 1851627 9501781 := bbase (se 8 (by rfl) ⟨55674, by rfl⟩ : syracuseStep 9501781 = 111349) (by norm_num)
theorem B3955805 : Blo 1851627 3955805 := bbase (se 3 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 3955805 = 1483427) (by norm_num)
theorem B4168853 : Blo 1851627 4168853 := bbase (se 6 (by rfl) ⟨97707, by rfl⟩ : syracuseStep 4168853 = 195415) (by norm_num)
theorem B3169477 : Blo 1851627 3169477 := bbase (se 4 (by rfl) ⟨297138, by rfl⟩ : syracuseStep 3169477 = 594277) (by norm_num)
theorem B4168925 : Blo 1851627 4168925 := bbase (se 3 (by rfl) ⟨781673, by rfl⟩ : syracuseStep 4168925 = 1563347) (by norm_num)
theorem B4168997 : Blo 1851627 4168997 := bbase (se 4 (by rfl) ⟨390843, by rfl⟩ : syracuseStep 4168997 = 781687) (by norm_num)
theorem B6249797 : Blo 1851627 6249797 := bbase (se 4 (by rfl) ⟨585918, by rfl⟩ : syracuseStep 6249797 = 1171837) (by norm_num)
theorem B4169069 : Blo 1851627 4169069 := bbase (se 3 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 4169069 = 1563401) (by norm_num)
theorem B5709221 : Blo 1851627 5709221 := bbase (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) (by norm_num)
theorem B4169141 : Blo 1851627 4169141 := bbase (se 5 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 4169141 = 390857) (by norm_num)
theorem B17800661 : Blo 1851627 17800661 := bbase (se 7 (by rfl) ⟨208601, by rfl⟩ : syracuseStep 17800661 = 417203) (by norm_num)
theorem B4169213 : Blo 1851627 4169213 := bbase (se 3 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 4169213 = 1563455) (by norm_num)
theorem B2637317 : Blo 1851627 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B3382813 : Blo 1851627 3382813 := bbase (se 3 (by rfl) ⟨634277, by rfl⟩ : syracuseStep 3382813 = 1268555) (by norm_num)
theorem B4169285 : Blo 1851627 4169285 := bbase (se 4 (by rfl) ⟨390870, by rfl⟩ : syracuseStep 4169285 = 781741) (by norm_num)
theorem B4513357 : Blo 1851627 4513357 := bbase (se 3 (by rfl) ⟨846254, by rfl⟩ : syracuseStep 4513357 = 1692509) (by norm_num)
theorem B2637397 : Blo 1851627 2637397 := bbase (se 8 (by rfl) ⟨15453, by rfl⟩ : syracuseStep 2637397 = 30907) (by norm_num)
theorem B7913045 : Blo 1851627 7913045 := bbase (se 8 (by rfl) ⟨46365, by rfl⟩ : syracuseStep 7913045 = 92731) (by norm_num)
theorem B4169357 : Blo 1851627 4169357 := bbase (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) (by norm_num)
theorem B31637141 : Blo 1851627 31637141 := bbase (se 6 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 31637141 = 1482991) (by norm_num)
theorem B2637517 : Blo 1851627 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B4284109 : Blo 1851627 4284109 := bbase (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) (by norm_num)
theorem B4169429 : Blo 1851627 4169429 := bbase (se 7 (by rfl) ⟨48860, by rfl⟩ : syracuseStep 4169429 = 97721) (by norm_num)
theorem B6250229 : Blo 1851627 6250229 := bbase (se 5 (by rfl) ⟨292979, by rfl⟩ : syracuseStep 6250229 = 585959) (by norm_num)
theorem B4169501 : Blo 1851627 4169501 := bbase (se 3 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 4169501 = 1563563) (by norm_num)
theorem B4226845 : Blo 1851627 4226845 := bbase (se 3 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 4226845 = 1585067) (by norm_num)
theorem B2637613 : Blo 1851627 2637613 := bbase (se 3 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 2637613 = 989105) (by norm_num)
theorem B9379637 : Blo 1851627 9379637 := bbase (se 5 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 9379637 = 879341) (by norm_num)
theorem B7913285 : Blo 1851627 7913285 := bbase (se 4 (by rfl) ⟨741870, by rfl⟩ : syracuseStep 7913285 = 1483741) (by norm_num)
theorem B4169573 : Blo 1851627 4169573 := bbase (se 4 (by rfl) ⟨390897, by rfl⟩ : syracuseStep 4169573 = 781795) (by norm_num)
theorem B4169645 : Blo 1851627 4169645 := bbase (se 3 (by rfl) ⟨781808, by rfl⟩ : syracuseStep 4169645 = 1563617) (by norm_num)
theorem B3956693 : Blo 1851627 3956693 := bbase (se 7 (by rfl) ⟨46367, by rfl⟩ : syracuseStep 3956693 = 92735) (by norm_num)
theorem B7036901 : Blo 1851627 7036901 := bbase (se 4 (by rfl) ⟨659709, by rfl⟩ : syracuseStep 7036901 = 1319419) (by norm_num)
theorem B5275637 : Blo 1851627 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B4169717 : Blo 1851627 4169717 := bbase (se 5 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 4169717 = 390911) (by norm_num)
theorem B6250499 : Blo 1851627 6250499 := bstep (se 1 (by rfl) ⟨4687874, by rfl⟩ : syracuseStep 6250499 = 9375749) B9375749
theorem B2637841 : Blo 1851627 2637841 := bstep (se 2 (by rfl) ⟨989190, by rfl⟩ : syracuseStep 2637841 = 1978381) B1978381
theorem B2637955 : Blo 1851627 2637955 := bstep (se 1 (by rfl) ⟨1978466, by rfl⟩ : syracuseStep 2637955 = 3956933) B3956933
theorem B4751587 : Blo 1851627 4751587 := bstep (se 1 (by rfl) ⟨3563690, by rfl⟩ : syracuseStep 4751587 = 7127381) B7127381
theorem B5144813 : Blo 1851627 5144813 := bstep (se 3 (by rfl) ⟨964652, by rfl⟩ : syracuseStep 5144813 = 1929305) B1929305
theorem B10019057 : Blo 1851627 10019057 := bstep (se 2 (by rfl) ⟨3757146, by rfl⟩ : syracuseStep 10019057 = 7514293) B7514293
theorem B4169969 : Blo 1851627 4169969 := bstep (se 2 (by rfl) ⟨1563738, by rfl⟩ : syracuseStep 4169969 = 3127477) B3127477
theorem B1851635 : Blo 1851627 1851635 := bstep (se 1 (by rfl) ⟨1388726, by rfl⟩ : syracuseStep 1851635 = 2777453) B2777453
theorem B1851651 : Blo 1851627 1851651 := bstep (se 1 (by rfl) ⟨1388738, by rfl⟩ : syracuseStep 1851651 = 2777477) B2777477
theorem B4169987 : Blo 1851627 4169987 := bstep (se 1 (by rfl) ⟨3127490, by rfl⟩ : syracuseStep 4169987 = 6254981) B6254981
theorem B6250769 : Blo 1851627 6250769 := bstep (se 2 (by rfl) ⟨2344038, by rfl⟩ : syracuseStep 6250769 = 4688077) B4688077
theorem B1851667 : Blo 1851627 1851667 := bstep (se 1 (by rfl) ⟨1388750, by rfl⟩ : syracuseStep 1851667 = 2777501) B2777501
theorem B1851683 : Blo 1851627 1851683 := bstep (se 1 (by rfl) ⟨1388762, by rfl⟩ : syracuseStep 1851683 = 2777525) B2777525
theorem B7037219 : Blo 1851627 7037219 := bstep (se 1 (by rfl) ⟨5277914, by rfl⟩ : syracuseStep 7037219 = 10555829) B10555829
theorem B1851699 : Blo 1851627 1851699 := bstep (se 1 (by rfl) ⟨1388774, by rfl⟩ : syracuseStep 1851699 = 2777549) B2777549
theorem B1851715 : Blo 1851627 1851715 := bstep (se 1 (by rfl) ⟨1388786, by rfl⟩ : syracuseStep 1851715 = 2777573) B2777573
theorem B17809733 : Blo 1851627 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B1851731 : Blo 1851627 1851731 := bstep (se 1 (by rfl) ⟨1388798, by rfl⟩ : syracuseStep 1851731 = 2777597) B2777597
theorem B2777441 : Blo 1851627 2777441 := bstep (se 2 (by rfl) ⟨1041540, by rfl⟩ : syracuseStep 2777441 = 2083081) B2083081
theorem B1851747 : Blo 1851627 1851747 := bstep (se 1 (by rfl) ⟨1388810, by rfl⟩ : syracuseStep 1851747 = 2777621) B2777621
theorem B4817251 : Blo 1851627 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B2777459 : Blo 1851627 2777459 := bstep (se 1 (by rfl) ⟨2083094, by rfl⟩ : syracuseStep 2777459 = 4166189) B4166189
theorem B1851763 : Blo 1851627 1851763 := bstep (se 1 (by rfl) ⟨1388822, by rfl⟩ : syracuseStep 1851763 = 2777645) B2777645
theorem B1851779 : Blo 1851627 1851779 := bstep (se 1 (by rfl) ⟨1388834, by rfl⟩ : syracuseStep 1851779 = 2777669) B2777669
theorem B2777489 : Blo 1851627 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B1851795 : Blo 1851627 1851795 := bstep (se 1 (by rfl) ⟨1388846, by rfl⟩ : syracuseStep 1851795 = 2777693) B2777693
theorem B2777507 : Blo 1851627 2777507 := bstep (se 1 (by rfl) ⟨2083130, by rfl⟩ : syracuseStep 2777507 = 4166261) B4166261
theorem B1851811 : Blo 1851627 1851811 := bstep (se 1 (by rfl) ⟨1388858, by rfl⟩ : syracuseStep 1851811 = 2777717) B2777717
theorem B1851827 : Blo 1851627 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B2777537 : Blo 1851627 2777537 := bstep (se 2 (by rfl) ⟨1041576, by rfl⟩ : syracuseStep 2777537 = 2083153) B2083153
theorem B1851843 : Blo 1851627 1851843 := bstep (se 1 (by rfl) ⟨1388882, by rfl⟩ : syracuseStep 1851843 = 2777765) B2777765
theorem B7913933 : Blo 1851627 7913933 := bstep (se 3 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 7913933 = 2967725) B2967725
theorem B2777555 : Blo 1851627 2777555 := bstep (se 1 (by rfl) ⟨2083166, by rfl⟩ : syracuseStep 2777555 = 4166333) B4166333
theorem B1851859 : Blo 1851627 1851859 := bstep (se 1 (by rfl) ⟨1388894, by rfl⟩ : syracuseStep 1851859 = 2777789) B2777789
theorem B1851875 : Blo 1851627 1851875 := bstep (se 1 (by rfl) ⟨1388906, by rfl⟩ : syracuseStep 1851875 = 2777813) B2777813
theorem B2777585 : Blo 1851627 2777585 := bstep (se 2 (by rfl) ⟨1041594, by rfl⟩ : syracuseStep 2777585 = 2083189) B2083189
theorem B7913969 : Blo 1851627 7913969 := bstep (se 2 (by rfl) ⟨2967738, by rfl⟩ : syracuseStep 7913969 = 5935477) B5935477
theorem B1851891 : Blo 1851627 1851891 := bstep (se 1 (by rfl) ⟨1388918, by rfl⟩ : syracuseStep 1851891 = 2777837) B2777837
theorem B2777603 : Blo 1851627 2777603 := bstep (se 1 (by rfl) ⟨2083202, by rfl⟩ : syracuseStep 2777603 = 4166405) B4166405
theorem B1851907 : Blo 1851627 1851907 := bstep (se 1 (by rfl) ⟨1388930, by rfl⟩ : syracuseStep 1851907 = 2777861) B2777861
theorem B4170257 : Blo 1851627 4170257 := bstep (se 2 (by rfl) ⟨1563846, by rfl⟩ : syracuseStep 4170257 = 3127693) B3127693
theorem B1851923 : Blo 1851627 1851923 := bstep (se 1 (by rfl) ⟨1388942, by rfl⟩ : syracuseStep 1851923 = 2777885) B2777885
theorem B2777633 : Blo 1851627 2777633 := bstep (se 2 (by rfl) ⟨1041612, by rfl⟩ : syracuseStep 2777633 = 2083225) B2083225
theorem B1851939 : Blo 1851627 1851939 := bstep (se 1 (by rfl) ⟨1388954, by rfl⟩ : syracuseStep 1851939 = 2777909) B2777909
theorem B4170275 : Blo 1851627 4170275 := bstep (se 1 (by rfl) ⟨3127706, by rfl⟩ : syracuseStep 4170275 = 6255413) B6255413
theorem B2777651 : Blo 1851627 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B1851955 : Blo 1851627 1851955 := bstep (se 1 (by rfl) ⟨1388966, by rfl⟩ : syracuseStep 1851955 = 2777933) B2777933
theorem B1851971 : Blo 1851627 1851971 := bstep (se 1 (by rfl) ⟨1388978, by rfl⟩ : syracuseStep 1851971 = 2777957) B2777957
theorem B2777681 : Blo 1851627 2777681 := bstep (se 2 (by rfl) ⟨1041630, by rfl⟩ : syracuseStep 2777681 = 2083261) B2083261
theorem B1851987 : Blo 1851627 1851987 := bstep (se 1 (by rfl) ⟨1388990, by rfl⟩ : syracuseStep 1851987 = 2777981) B2777981
theorem B2777699 : Blo 1851627 2777699 := bstep (se 1 (by rfl) ⟨2083274, by rfl⟩ : syracuseStep 2777699 = 4166549) B4166549
theorem B1852003 : Blo 1851627 1852003 := bstep (se 1 (by rfl) ⟨1389002, by rfl⟩ : syracuseStep 1852003 = 2778005) B2778005
theorem B1852019 : Blo 1851627 1852019 := bstep (se 1 (by rfl) ⟨1389014, by rfl⟩ : syracuseStep 1852019 = 2778029) B2778029
theorem B2777729 : Blo 1851627 2777729 := bstep (se 2 (by rfl) ⟨1041648, by rfl⟩ : syracuseStep 2777729 = 2083297) B2083297
theorem B1852035 : Blo 1851627 1852035 := bstep (se 1 (by rfl) ⟨1389026, by rfl⟩ : syracuseStep 1852035 = 2778053) B2778053
theorem B2777747 : Blo 1851627 2777747 := bstep (se 1 (by rfl) ⟨2083310, by rfl⟩ : syracuseStep 2777747 = 4166621) B4166621
theorem B1852051 : Blo 1851627 1852051 := bstep (se 1 (by rfl) ⟨1389038, by rfl⟩ : syracuseStep 1852051 = 2778077) B2778077
theorem B1852067 : Blo 1851627 1852067 := bstep (se 1 (by rfl) ⟨1389050, by rfl⟩ : syracuseStep 1852067 = 2778101) B2778101
theorem B2777777 : Blo 1851627 2777777 := bstep (se 2 (by rfl) ⟨1041666, by rfl⟩ : syracuseStep 2777777 = 2083333) B2083333
theorem B1852083 : Blo 1851627 1852083 := bstep (se 1 (by rfl) ⟨1389062, by rfl⟩ : syracuseStep 1852083 = 2778125) B2778125
theorem B2777795 : Blo 1851627 2777795 := bstep (se 1 (by rfl) ⟨2083346, by rfl⟩ : syracuseStep 2777795 = 4166693) B4166693
theorem B1852099 : Blo 1851627 1852099 := bstep (se 1 (by rfl) ⟨1389074, by rfl⟩ : syracuseStep 1852099 = 2778149) B2778149
theorem B24052421 : Blo 1851627 24052421 := bstep (se 4 (by rfl) ⟨2254914, by rfl⟩ : syracuseStep 24052421 = 4509829) B4509829
theorem B15819461 : Blo 1851627 15819461 := bstep (se 4 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 15819461 = 2966149) B2966149
theorem B1852115 : Blo 1851627 1852115 := bstep (se 1 (by rfl) ⟨1389086, by rfl⟩ : syracuseStep 1852115 = 2778173) B2778173
theorem B2777825 : Blo 1851627 2777825 := bstep (se 2 (by rfl) ⟨1041684, by rfl⟩ : syracuseStep 2777825 = 2083369) B2083369
theorem B1852131 : Blo 1851627 1852131 := bstep (se 1 (by rfl) ⟨1389098, by rfl⟩ : syracuseStep 1852131 = 2778197) B2778197
theorem B2777843 : Blo 1851627 2777843 := bstep (se 1 (by rfl) ⟨2083382, by rfl⟩ : syracuseStep 2777843 = 4166765) B4166765
theorem B1852147 : Blo 1851627 1852147 := bstep (se 1 (by rfl) ⟨1389110, by rfl⟩ : syracuseStep 1852147 = 2778221) B2778221
theorem B1852163 : Blo 1851627 1852163 := bstep (se 1 (by rfl) ⟨1389122, by rfl⟩ : syracuseStep 1852163 = 2778245) B2778245
theorem B2777873 : Blo 1851627 2777873 := bstep (se 2 (by rfl) ⟨1041702, by rfl⟩ : syracuseStep 2777873 = 2083405) B2083405
theorem B1852179 : Blo 1851627 1852179 := bstep (se 1 (by rfl) ⟨1389134, by rfl⟩ : syracuseStep 1852179 = 2778269) B2778269
theorem B2777891 : Blo 1851627 2777891 := bstep (se 1 (by rfl) ⟨2083418, by rfl⟩ : syracuseStep 2777891 = 4166837) B4166837
theorem B1852195 : Blo 1851627 1852195 := bstep (se 1 (by rfl) ⟨1389146, by rfl⟩ : syracuseStep 1852195 = 2778293) B2778293
theorem B6251309 : Blo 1851627 6251309 := bstep (se 3 (by rfl) ⟨1172120, by rfl⟩ : syracuseStep 6251309 = 2344241) B2344241
theorem B4170545 : Blo 1851627 4170545 := bstep (se 2 (by rfl) ⟨1563954, by rfl⟩ : syracuseStep 4170545 = 3127909) B3127909
theorem B1852211 : Blo 1851627 1852211 := bstep (se 1 (by rfl) ⟨1389158, by rfl⟩ : syracuseStep 1852211 = 2778317) B2778317
theorem B2777921 : Blo 1851627 2777921 := bstep (se 2 (by rfl) ⟨1041720, by rfl⟩ : syracuseStep 2777921 = 2083441) B2083441
theorem B1852227 : Blo 1851627 1852227 := bstep (se 1 (by rfl) ⟨1389170, by rfl⟩ : syracuseStep 1852227 = 2778341) B2778341
theorem B4170563 : Blo 1851627 4170563 := bstep (se 1 (by rfl) ⟨3127922, by rfl⟩ : syracuseStep 4170563 = 6255845) B6255845
theorem B2777939 : Blo 1851627 2777939 := bstep (se 1 (by rfl) ⟨2083454, by rfl⟩ : syracuseStep 2777939 = 4166909) B4166909
theorem B1852243 : Blo 1851627 1852243 := bstep (se 1 (by rfl) ⟨1389182, by rfl⟩ : syracuseStep 1852243 = 2778365) B2778365
theorem B6251363 : Blo 1851627 6251363 := bstep (se 1 (by rfl) ⟨4688522, by rfl⟩ : syracuseStep 6251363 = 9377045) B9377045
theorem B1852259 : Blo 1851627 1852259 := bstep (se 1 (by rfl) ⟨1389194, by rfl⟩ : syracuseStep 1852259 = 2778389) B2778389
theorem B2777969 : Blo 1851627 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B1852275 : Blo 1851627 1852275 := bstep (se 1 (by rfl) ⟨1389206, by rfl⟩ : syracuseStep 1852275 = 2778413) B2778413
theorem B2343811 : Blo 1851627 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B2777987 : Blo 1851627 2777987 := bstep (se 1 (by rfl) ⟨2083490, by rfl⟩ : syracuseStep 2777987 = 4166981) B4166981
theorem B1852291 : Blo 1851627 1852291 := bstep (se 1 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 1852291 = 2778437) B2778437
theorem B1852307 : Blo 1851627 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B2778017 : Blo 1851627 2778017 := bstep (se 2 (by rfl) ⟨1041756, by rfl⟩ : syracuseStep 2778017 = 2083513) B2083513
theorem B1852323 : Blo 1851627 1852323 := bstep (se 1 (by rfl) ⟨1389242, by rfl⟩ : syracuseStep 1852323 = 2778485) B2778485
theorem B9380771 : Blo 1851627 9380771 := bstep (se 1 (by rfl) ⟨7035578, by rfl⟩ : syracuseStep 9380771 = 14071157) B14071157
theorem B5276593 : Blo 1851627 5276593 := bstep (se 2 (by rfl) ⟨1978722, by rfl⟩ : syracuseStep 5276593 = 3957445) B3957445
theorem B7037873 : Blo 1851627 7037873 := bstep (se 2 (by rfl) ⟨2639202, by rfl⟩ : syracuseStep 7037873 = 5278405) B5278405
theorem B2778035 : Blo 1851627 2778035 := bstep (se 1 (by rfl) ⟨2083526, by rfl⟩ : syracuseStep 2778035 = 4167053) B4167053
theorem B1852339 : Blo 1851627 1852339 := bstep (se 1 (by rfl) ⟨1389254, by rfl⟩ : syracuseStep 1852339 = 2778509) B2778509
theorem B1852355 : Blo 1851627 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B2778065 : Blo 1851627 2778065 := bstep (se 2 (by rfl) ⟨1041774, by rfl⟩ : syracuseStep 2778065 = 2083549) B2083549
theorem B1852371 : Blo 1851627 1852371 := bstep (se 1 (by rfl) ⟨1389278, by rfl⟩ : syracuseStep 1852371 = 2778557) B2778557
theorem B2343907 : Blo 1851627 2343907 := bstep (se 1 (by rfl) ⟨1757930, by rfl⟩ : syracuseStep 2343907 = 3515861) B3515861
theorem B2778083 : Blo 1851627 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B1852387 : Blo 1851627 1852387 := bstep (se 1 (by rfl) ⟨1389290, by rfl⟩ : syracuseStep 1852387 = 2778581) B2778581
theorem B9511921 : Blo 1851627 9511921 := bstep (se 2 (by rfl) ⟨3566970, by rfl⟩ : syracuseStep 9511921 = 7133941) B7133941
theorem B1852403 : Blo 1851627 1852403 := bstep (se 1 (by rfl) ⟨1389302, by rfl⟩ : syracuseStep 1852403 = 2778605) B2778605
theorem B2778113 : Blo 1851627 2778113 := bstep (se 2 (by rfl) ⟨1041792, by rfl⟩ : syracuseStep 2778113 = 2083585) B2083585
theorem B1852419 : Blo 1851627 1852419 := bstep (se 1 (by rfl) ⟨1389314, by rfl⟩ : syracuseStep 1852419 = 2778629) B2778629
theorem B2778131 : Blo 1851627 2778131 := bstep (se 1 (by rfl) ⟨2083598, by rfl⟩ : syracuseStep 2778131 = 4167197) B4167197
theorem B1852435 : Blo 1851627 1852435 := bstep (se 1 (by rfl) ⟨1389326, by rfl⟩ : syracuseStep 1852435 = 2778653) B2778653
theorem B1852451 : Blo 1851627 1852451 := bstep (se 1 (by rfl) ⟨1389338, by rfl⟩ : syracuseStep 1852451 = 2778677) B2778677
theorem B2778161 : Blo 1851627 2778161 := bstep (se 2 (by rfl) ⟨1041810, by rfl⟩ : syracuseStep 2778161 = 2083621) B2083621
theorem B1852467 : Blo 1851627 1852467 := bstep (se 1 (by rfl) ⟨1389350, by rfl⟩ : syracuseStep 1852467 = 2778701) B2778701
theorem B2778179 : Blo 1851627 2778179 := bstep (se 1 (by rfl) ⟨2083634, by rfl⟩ : syracuseStep 2778179 = 4167269) B4167269
theorem B1852483 : Blo 1851627 1852483 := bstep (se 1 (by rfl) ⟨1389362, by rfl⟩ : syracuseStep 1852483 = 2778725) B2778725
theorem B22848581 : Blo 1851627 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B1852499 : Blo 1851627 1852499 := bstep (se 1 (by rfl) ⟨1389374, by rfl⟩ : syracuseStep 1852499 = 2778749) B2778749
theorem B2778209 : Blo 1851627 2778209 := bstep (se 2 (by rfl) ⟨1041828, by rfl⟩ : syracuseStep 2778209 = 2083657) B2083657
theorem B1852515 : Blo 1851627 1852515 := bstep (se 1 (by rfl) ⟨1389386, by rfl⟩ : syracuseStep 1852515 = 2778773) B2778773
theorem B6251633 : Blo 1851627 6251633 := bstep (se 2 (by rfl) ⟨2344362, by rfl⟩ : syracuseStep 6251633 = 4688725) B4688725
theorem B2778227 : Blo 1851627 2778227 := bstep (se 1 (by rfl) ⟨2083670, by rfl⟩ : syracuseStep 2778227 = 4167341) B4167341
theorem B1852531 : Blo 1851627 1852531 := bstep (se 1 (by rfl) ⟨1389398, by rfl⟩ : syracuseStep 1852531 = 2778797) B2778797
theorem B1852547 : Blo 1851627 1852547 := bstep (se 1 (by rfl) ⟨1389410, by rfl⟩ : syracuseStep 1852547 = 2778821) B2778821
theorem B2778257 : Blo 1851627 2778257 := bstep (se 2 (by rfl) ⟨1041846, by rfl⟩ : syracuseStep 2778257 = 2083693) B2083693
theorem B1852563 : Blo 1851627 1852563 := bstep (se 1 (by rfl) ⟨1389422, by rfl⟩ : syracuseStep 1852563 = 2778845) B2778845
theorem B2778275 : Blo 1851627 2778275 := bstep (se 1 (by rfl) ⟨2083706, by rfl⟩ : syracuseStep 2778275 = 4167413) B4167413
theorem B1852579 : Blo 1851627 1852579 := bstep (se 1 (by rfl) ⟨1389434, by rfl⟩ : syracuseStep 1852579 = 2778869) B2778869
theorem B1852595 : Blo 1851627 1852595 := bstep (se 1 (by rfl) ⟨1389446, by rfl⟩ : syracuseStep 1852595 = 2778893) B2778893
theorem B2778305 : Blo 1851627 2778305 := bstep (se 2 (by rfl) ⟨1041864, by rfl⟩ : syracuseStep 2778305 = 2083729) B2083729
theorem B1852611 : Blo 1851627 1852611 := bstep (se 1 (by rfl) ⟨1389458, by rfl⟩ : syracuseStep 1852611 = 2778917) B2778917
theorem B2778323 : Blo 1851627 2778323 := bstep (se 1 (by rfl) ⟨2083742, by rfl⟩ : syracuseStep 2778323 = 4167485) B4167485
theorem B1852627 : Blo 1851627 1852627 := bstep (se 1 (by rfl) ⟨1389470, by rfl⟩ : syracuseStep 1852627 = 2778941) B2778941
theorem B1852643 : Blo 1851627 1852643 := bstep (se 1 (by rfl) ⟨1389482, by rfl⟩ : syracuseStep 1852643 = 2778965) B2778965
theorem B3515633 : Blo 1851627 3515633 := bstep (se 2 (by rfl) ⟨1318362, by rfl⟩ : syracuseStep 3515633 = 2636725) B2636725
theorem B2778353 : Blo 1851627 2778353 := bstep (se 2 (by rfl) ⟨1041882, by rfl⟩ : syracuseStep 2778353 = 2083765) B2083765
theorem B1852659 : Blo 1851627 1852659 := bstep (se 1 (by rfl) ⟨1389494, by rfl⟩ : syracuseStep 1852659 = 2778989) B2778989
theorem B15828209 : Blo 1851627 15828209 := bstep (se 2 (by rfl) ⟨5935578, by rfl⟩ : syracuseStep 15828209 = 11871157) B11871157
theorem B2778371 : Blo 1851627 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B1852675 : Blo 1851627 1852675 := bstep (se 1 (by rfl) ⟨1389506, by rfl⟩ : syracuseStep 1852675 = 2779013) B2779013
theorem B1852691 : Blo 1851627 1852691 := bstep (se 1 (by rfl) ⟨1389518, by rfl⟩ : syracuseStep 1852691 = 2779037) B2779037
theorem B2778401 : Blo 1851627 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B1852707 : Blo 1851627 1852707 := bstep (se 1 (by rfl) ⟨1389530, by rfl⟩ : syracuseStep 1852707 = 2779061) B2779061
theorem B2778419 : Blo 1851627 2778419 := bstep (se 1 (by rfl) ⟨2083814, by rfl⟩ : syracuseStep 2778419 = 4167629) B4167629
theorem B1852723 : Blo 1851627 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B1852739 : Blo 1851627 1852739 := bstep (se 1 (by rfl) ⟨1389554, by rfl⟩ : syracuseStep 1852739 = 2779109) B2779109
theorem B2778449 : Blo 1851627 2778449 := bstep (se 2 (by rfl) ⟨1041918, by rfl⟩ : syracuseStep 2778449 = 2083837) B2083837
theorem B1852755 : Blo 1851627 1852755 := bstep (se 1 (by rfl) ⟨1389566, by rfl⟩ : syracuseStep 1852755 = 2779133) B2779133
theorem B2778467 : Blo 1851627 2778467 := bstep (se 1 (by rfl) ⟨2083850, by rfl⟩ : syracuseStep 2778467 = 4167701) B4167701
theorem B1852771 : Blo 1851627 1852771 := bstep (se 1 (by rfl) ⟨1389578, by rfl⟩ : syracuseStep 1852771 = 2779157) B2779157
theorem B4687217 : Blo 1851627 4687217 := bstep (se 2 (by rfl) ⟨1757706, by rfl⟩ : syracuseStep 4687217 = 3515413) B3515413
theorem B1852787 : Blo 1851627 1852787 := bstep (se 1 (by rfl) ⟨1389590, by rfl⟩ : syracuseStep 1852787 = 2779181) B2779181
theorem B2778497 : Blo 1851627 2778497 := bstep (se 2 (by rfl) ⟨1041936, by rfl⟩ : syracuseStep 2778497 = 2083873) B2083873
theorem B1852803 : Blo 1851627 1852803 := bstep (se 1 (by rfl) ⟨1389602, by rfl⟩ : syracuseStep 1852803 = 2779205) B2779205
theorem B6014353 : Blo 1851627 6014353 := bstep (se 2 (by rfl) ⟨2255382, by rfl⟩ : syracuseStep 6014353 = 4510765) B4510765
theorem B2778515 : Blo 1851627 2778515 := bstep (se 1 (by rfl) ⟨2083886, by rfl⟩ : syracuseStep 2778515 = 4167773) B4167773
theorem B1852819 : Blo 1851627 1852819 := bstep (se 1 (by rfl) ⟨1389614, by rfl⟩ : syracuseStep 1852819 = 2779229) B2779229
theorem B4687267 : Blo 1851627 4687267 := bstep (se 1 (by rfl) ⟨3515450, by rfl⟩ : syracuseStep 4687267 = 7030901) B7030901
theorem B1852835 : Blo 1851627 1852835 := bstep (se 1 (by rfl) ⟨1389626, by rfl⟩ : syracuseStep 1852835 = 2779253) B2779253
theorem B2778545 : Blo 1851627 2778545 := bstep (se 2 (by rfl) ⟨1041954, by rfl⟩ : syracuseStep 2778545 = 2083909) B2083909
theorem B1852851 : Blo 1851627 1852851 := bstep (se 1 (by rfl) ⟨1389638, by rfl⟩ : syracuseStep 1852851 = 2779277) B2779277
theorem B2778563 : Blo 1851627 2778563 := bstep (se 1 (by rfl) ⟨2083922, by rfl⟩ : syracuseStep 2778563 = 4167845) B4167845
theorem B1852867 : Blo 1851627 1852867 := bstep (se 1 (by rfl) ⟨1389650, by rfl⟩ : syracuseStep 1852867 = 2779301) B2779301
theorem B2344403 : Blo 1851627 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B1852883 : Blo 1851627 1852883 := bstep (se 1 (by rfl) ⟨1389662, by rfl⟩ : syracuseStep 1852883 = 2779325) B2779325
theorem B2778593 : Blo 1851627 2778593 := bstep (se 2 (by rfl) ⟨1041972, by rfl⟩ : syracuseStep 2778593 = 2083945) B2083945
theorem B1852899 : Blo 1851627 1852899 := bstep (se 1 (by rfl) ⟨1389674, by rfl⟩ : syracuseStep 1852899 = 2779349) B2779349
theorem B2778611 : Blo 1851627 2778611 := bstep (se 1 (by rfl) ⟨2083958, by rfl⟩ : syracuseStep 2778611 = 4167917) B4167917
theorem B1852915 : Blo 1851627 1852915 := bstep (se 1 (by rfl) ⟨1389686, by rfl⟩ : syracuseStep 1852915 = 2779373) B2779373
theorem B1852931 : Blo 1851627 1852931 := bstep (se 1 (by rfl) ⟨1389698, by rfl⟩ : syracuseStep 1852931 = 2779397) B2779397
theorem B2778641 : Blo 1851627 2778641 := bstep (se 2 (by rfl) ⟨1041990, by rfl⟩ : syracuseStep 2778641 = 2083981) B2083981
theorem B2967059 : Blo 1851627 2967059 := bstep (se 1 (by rfl) ⟨2225294, by rfl⟩ : syracuseStep 2967059 = 4450589) B4450589
theorem B1852947 : Blo 1851627 1852947 := bstep (se 1 (by rfl) ⟨1389710, by rfl⟩ : syracuseStep 1852947 = 2779421) B2779421
theorem B8898083 : Blo 1851627 8898083 := bstep (se 1 (by rfl) ⟨6673562, by rfl⟩ : syracuseStep 8898083 = 13347125) B13347125
theorem B2778659 : Blo 1851627 2778659 := bstep (se 1 (by rfl) ⟨2083994, by rfl⟩ : syracuseStep 2778659 = 4167989) B4167989
theorem B1852963 : Blo 1851627 1852963 := bstep (se 1 (by rfl) ⟨1389722, by rfl⟩ : syracuseStep 1852963 = 2779445) B2779445
theorem B4687409 : Blo 1851627 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B1852979 : Blo 1851627 1852979 := bstep (se 1 (by rfl) ⟨1389734, by rfl⟩ : syracuseStep 1852979 = 2779469) B2779469
theorem B2778689 : Blo 1851627 2778689 := bstep (se 2 (by rfl) ⟨1042008, by rfl⟩ : syracuseStep 2778689 = 2084017) B2084017
theorem B1852995 : Blo 1851627 1852995 := bstep (se 1 (by rfl) ⟨1389746, by rfl⟩ : syracuseStep 1852995 = 2779493) B2779493
theorem B14067269 : Blo 1851627 14067269 := bstep (se 4 (by rfl) ⟨1318806, by rfl⟩ : syracuseStep 14067269 = 2637613) B2637613
theorem B2778707 : Blo 1851627 2778707 := bstep (se 1 (by rfl) ⟨2084030, by rfl⟩ : syracuseStep 2778707 = 4168061) B4168061
theorem B1853011 : Blo 1851627 1853011 := bstep (se 1 (by rfl) ⟨1389758, by rfl⟩ : syracuseStep 1853011 = 2779517) B2779517
theorem B1853027 : Blo 1851627 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B2778737 : Blo 1851627 2778737 := bstep (se 2 (by rfl) ⟨1042026, by rfl⟩ : syracuseStep 2778737 = 2084053) B2084053
theorem B1853043 : Blo 1851627 1853043 := bstep (se 1 (by rfl) ⟨1389782, by rfl⟩ : syracuseStep 1853043 = 2779565) B2779565
theorem B2778755 : Blo 1851627 2778755 := bstep (se 1 (by rfl) ⟨2084066, by rfl⟩ : syracuseStep 2778755 = 4168133) B4168133
theorem B1853059 : Blo 1851627 1853059 := bstep (se 1 (by rfl) ⟨1389794, by rfl⟩ : syracuseStep 1853059 = 2779589) B2779589
theorem B10020485 : Blo 1851627 10020485 := bstep (se 4 (by rfl) ⟨939420, by rfl⟩ : syracuseStep 10020485 = 1878841) B1878841
theorem B6252173 : Blo 1851627 6252173 := bstep (se 3 (by rfl) ⟨1172282, by rfl⟩ : syracuseStep 6252173 = 2344565) B2344565
theorem B18548365 : Blo 1851627 18548365 := bstep (se 3 (by rfl) ⟨3477818, by rfl⟩ : syracuseStep 18548365 = 6955637) B6955637
theorem B2967187 : Blo 1851627 2967187 := bstep (se 1 (by rfl) ⟨2225390, by rfl⟩ : syracuseStep 2967187 = 4450781) B4450781
theorem B1853075 : Blo 1851627 1853075 := bstep (se 1 (by rfl) ⟨1389806, by rfl⟩ : syracuseStep 1853075 = 2779613) B2779613
theorem B2778785 : Blo 1851627 2778785 := bstep (se 2 (by rfl) ⟨1042044, by rfl⟩ : syracuseStep 2778785 = 2084089) B2084089
theorem B1853091 : Blo 1851627 1853091 := bstep (se 1 (by rfl) ⟨1389818, by rfl⟩ : syracuseStep 1853091 = 2779637) B2779637
theorem B2778803 : Blo 1851627 2778803 := bstep (se 1 (by rfl) ⟨2084102, by rfl⟩ : syracuseStep 2778803 = 4168205) B4168205
theorem B1853107 : Blo 1851627 1853107 := bstep (se 1 (by rfl) ⟨1389830, by rfl⟩ : syracuseStep 1853107 = 2779661) B2779661
theorem B6252227 : Blo 1851627 6252227 := bstep (se 1 (by rfl) ⟨4689170, by rfl⟩ : syracuseStep 6252227 = 9378341) B9378341
theorem B1853123 : Blo 1851627 1853123 := bstep (se 1 (by rfl) ⟨1389842, by rfl⟩ : syracuseStep 1853123 = 2779685) B2779685
theorem B22537925 : Blo 1851627 22537925 := bstep (se 4 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 22537925 = 4225861) B4225861
theorem B9381581 : Blo 1851627 9381581 := bstep (se 3 (by rfl) ⟨1759046, by rfl⟩ : syracuseStep 9381581 = 3518093) B3518093
theorem B2778833 : Blo 1851627 2778833 := bstep (se 2 (by rfl) ⟨1042062, by rfl⟩ : syracuseStep 2778833 = 2084125) B2084125
theorem B1853139 : Blo 1851627 1853139 := bstep (se 1 (by rfl) ⟨1389854, by rfl⟩ : syracuseStep 1853139 = 2779709) B2779709
theorem B2778851 : Blo 1851627 2778851 := bstep (se 1 (by rfl) ⟨2084138, by rfl⟩ : syracuseStep 2778851 = 4168277) B4168277
theorem B6768355 : Blo 1851627 6768355 := bstep (se 1 (by rfl) ⟨5076266, by rfl⟩ : syracuseStep 6768355 = 10152533) B10152533
theorem B1853155 : Blo 1851627 1853155 := bstep (se 1 (by rfl) ⟨1389866, by rfl⟩ : syracuseStep 1853155 = 2779733) B2779733
theorem B1853171 : Blo 1851627 1853171 := bstep (se 1 (by rfl) ⟨1389878, by rfl⟩ : syracuseStep 1853171 = 2779757) B2779757
theorem B2778881 : Blo 1851627 2778881 := bstep (se 2 (by rfl) ⟨1042080, by rfl⟩ : syracuseStep 2778881 = 2084161) B2084161
theorem B1853187 : Blo 1851627 1853187 := bstep (se 1 (by rfl) ⟨1389890, by rfl⟩ : syracuseStep 1853187 = 2779781) B2779781
theorem B2778899 : Blo 1851627 2778899 := bstep (se 1 (by rfl) ⟨2084174, by rfl⟩ : syracuseStep 2778899 = 4168349) B4168349
theorem B1853203 : Blo 1851627 1853203 := bstep (se 1 (by rfl) ⟨1389902, by rfl⟩ : syracuseStep 1853203 = 2779805) B2779805
theorem B2967329 : Blo 1851627 2967329 := bstep (se 2 (by rfl) ⟨1112748, by rfl⟩ : syracuseStep 2967329 = 2225497) B2225497
theorem B1853219 : Blo 1851627 1853219 := bstep (se 1 (by rfl) ⟨1389914, by rfl⟩ : syracuseStep 1853219 = 2779829) B2779829
theorem B2778929 : Blo 1851627 2778929 := bstep (se 2 (by rfl) ⟨1042098, by rfl⟩ : syracuseStep 2778929 = 2084197) B2084197
theorem B1853235 : Blo 1851627 1853235 := bstep (se 1 (by rfl) ⟨1389926, by rfl⟩ : syracuseStep 1853235 = 2779853) B2779853
theorem B2778947 : Blo 1851627 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B1853251 : Blo 1851627 1853251 := bstep (se 1 (by rfl) ⟨1389938, by rfl⟩ : syracuseStep 1853251 = 2779877) B2779877
theorem B10553165 : Blo 1851627 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B1853267 : Blo 1851627 1853267 := bstep (se 1 (by rfl) ⟨1389950, by rfl⟩ : syracuseStep 1853267 = 2779901) B2779901
theorem B2778977 : Blo 1851627 2778977 := bstep (se 2 (by rfl) ⟨1042116, by rfl⟩ : syracuseStep 2778977 = 2084233) B2084233
theorem B11863907 : Blo 1851627 11863907 := bstep (se 1 (by rfl) ⟨8897930, by rfl⟩ : syracuseStep 11863907 = 17795861) B17795861
theorem B1853283 : Blo 1851627 1853283 := bstep (se 1 (by rfl) ⟨1389962, by rfl⟩ : syracuseStep 1853283 = 2779925) B2779925
theorem B2778995 : Blo 1851627 2778995 := bstep (se 1 (by rfl) ⟨2084246, by rfl⟩ : syracuseStep 2778995 = 4168493) B4168493
theorem B1853299 : Blo 1851627 1853299 := bstep (se 1 (by rfl) ⟨1389974, by rfl⟩ : syracuseStep 1853299 = 2779949) B2779949
theorem B1853315 : Blo 1851627 1853315 := bstep (se 1 (by rfl) ⟨1389986, by rfl⟩ : syracuseStep 1853315 = 2779973) B2779973
theorem B2779025 : Blo 1851627 2779025 := bstep (se 2 (by rfl) ⟨1042134, by rfl⟩ : syracuseStep 2779025 = 2084269) B2084269
theorem B1853331 : Blo 1851627 1853331 := bstep (se 1 (by rfl) ⟨1389998, by rfl⟩ : syracuseStep 1853331 = 2779997) B2779997
theorem B2779043 : Blo 1851627 2779043 := bstep (se 1 (by rfl) ⟨2084282, by rfl⟩ : syracuseStep 2779043 = 4168565) B4168565
theorem B1853347 : Blo 1851627 1853347 := bstep (se 1 (by rfl) ⟨1390010, by rfl⟩ : syracuseStep 1853347 = 2780021) B2780021
theorem B1853363 : Blo 1851627 1853363 := bstep (se 1 (by rfl) ⟨1390022, by rfl⟩ : syracuseStep 1853363 = 2780045) B2780045
theorem B2779073 : Blo 1851627 2779073 := bstep (se 2 (by rfl) ⟨1042152, by rfl⟩ : syracuseStep 2779073 = 2084305) B2084305
theorem B1853379 : Blo 1851627 1853379 := bstep (se 1 (by rfl) ⟨1390034, by rfl⟩ : syracuseStep 1853379 = 2780069) B2780069
theorem B6252497 : Blo 1851627 6252497 := bstep (se 2 (by rfl) ⟨2344686, by rfl⟩ : syracuseStep 6252497 = 4689373) B4689373
theorem B2779091 : Blo 1851627 2779091 := bstep (se 1 (by rfl) ⟨2084318, by rfl⟩ : syracuseStep 2779091 = 4168637) B4168637
theorem B1853395 : Blo 1851627 1853395 := bstep (se 1 (by rfl) ⟨1390046, by rfl⟩ : syracuseStep 1853395 = 2780093) B2780093
theorem B1853411 : Blo 1851627 1853411 := bstep (se 1 (by rfl) ⟨1390058, by rfl⟩ : syracuseStep 1853411 = 2780117) B2780117
theorem B2779121 : Blo 1851627 2779121 := bstep (se 2 (by rfl) ⟨1042170, by rfl⟩ : syracuseStep 2779121 = 2084341) B2084341
theorem B1853427 : Blo 1851627 1853427 := bstep (se 1 (by rfl) ⟨1390070, by rfl⟩ : syracuseStep 1853427 = 2780141) B2780141
theorem B2779139 : Blo 1851627 2779139 := bstep (se 1 (by rfl) ⟨2084354, by rfl⟩ : syracuseStep 2779139 = 4168709) B4168709
theorem B1853443 : Blo 1851627 1853443 := bstep (se 1 (by rfl) ⟨1390082, by rfl⟩ : syracuseStep 1853443 = 2780165) B2780165
theorem B1853459 : Blo 1851627 1853459 := bstep (se 1 (by rfl) ⟨1390094, by rfl⟩ : syracuseStep 1853459 = 2780189) B2780189
theorem B2779169 : Blo 1851627 2779169 := bstep (se 2 (by rfl) ⟨1042188, by rfl⟩ : syracuseStep 2779169 = 2084377) B2084377
theorem B1853475 : Blo 1851627 1853475 := bstep (se 1 (by rfl) ⟨1390106, by rfl⟩ : syracuseStep 1853475 = 2780213) B2780213
theorem B2779187 : Blo 1851627 2779187 := bstep (se 1 (by rfl) ⟨2084390, by rfl⟩ : syracuseStep 2779187 = 4168781) B4168781
theorem B1853491 : Blo 1851627 1853491 := bstep (se 1 (by rfl) ⟨1390118, by rfl⟩ : syracuseStep 1853491 = 2780237) B2780237
theorem B2967617 : Blo 1851627 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B1853507 : Blo 1851627 1853507 := bstep (se 1 (by rfl) ⟨1390130, by rfl⟩ : syracuseStep 1853507 = 2780261) B2780261
theorem B2779217 : Blo 1851627 2779217 := bstep (se 2 (by rfl) ⟨1042206, by rfl⟩ : syracuseStep 2779217 = 2084413) B2084413
theorem B1853523 : Blo 1851627 1853523 := bstep (se 1 (by rfl) ⟨1390142, by rfl⟩ : syracuseStep 1853523 = 2780285) B2780285
theorem B2779235 : Blo 1851627 2779235 := bstep (se 1 (by rfl) ⟨2084426, by rfl⟩ : syracuseStep 2779235 = 4168853) B4168853
theorem B1853539 : Blo 1851627 1853539 := bstep (se 1 (by rfl) ⟨1390154, by rfl⟩ : syracuseStep 1853539 = 2780309) B2780309
theorem B3516529 : Blo 1851627 3516529 := bstep (se 2 (by rfl) ⟨1318698, by rfl⟩ : syracuseStep 3516529 = 2637397) B2637397
theorem B1853555 : Blo 1851627 1853555 := bstep (se 1 (by rfl) ⟨1390166, by rfl⟩ : syracuseStep 1853555 = 2780333) B2780333
theorem B2779265 : Blo 1851627 2779265 := bstep (se 2 (by rfl) ⟨1042224, by rfl⟩ : syracuseStep 2779265 = 2084449) B2084449
theorem B1853571 : Blo 1851627 1853571 := bstep (se 1 (by rfl) ⟨1390178, by rfl⟩ : syracuseStep 1853571 = 2780357) B2780357
theorem B2779283 : Blo 1851627 2779283 := bstep (se 1 (by rfl) ⟨2084462, by rfl⟩ : syracuseStep 2779283 = 4168925) B4168925
theorem B2345107 : Blo 1851627 2345107 := bstep (se 1 (by rfl) ⟨1758830, by rfl⟩ : syracuseStep 2345107 = 3517661) B3517661
theorem B1853587 : Blo 1851627 1853587 := bstep (se 1 (by rfl) ⟨1390190, by rfl⟩ : syracuseStep 1853587 = 2780381) B2780381
theorem B3754147 : Blo 1851627 3754147 := bstep (se 1 (by rfl) ⟨2815610, by rfl⟩ : syracuseStep 3754147 = 5631221) B5631221
theorem B1853603 : Blo 1851627 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B5277869 : Blo 1851627 5277869 := bstep (se 3 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 5277869 = 1979201) B1979201
theorem B2779313 : Blo 1851627 2779313 := bstep (se 2 (by rfl) ⟨1042242, by rfl⟩ : syracuseStep 2779313 = 2084485) B2084485
theorem B1853619 : Blo 1851627 1853619 := bstep (se 1 (by rfl) ⟨1390214, by rfl⟩ : syracuseStep 1853619 = 2780429) B2780429
theorem B2779331 : Blo 1851627 2779331 := bstep (se 1 (by rfl) ⟨2084498, by rfl⟩ : syracuseStep 2779331 = 4168997) B4168997
theorem B2779361 : Blo 1851627 2779361 := bstep (se 2 (by rfl) ⟨1042260, by rfl⟩ : syracuseStep 2779361 = 2084521) B2084521
theorem B5933297 : Blo 1851627 5933297 := bstep (se 2 (by rfl) ⟨2224986, by rfl⟩ : syracuseStep 5933297 = 4449973) B4449973
theorem B2779379 : Blo 1851627 2779379 := bstep (se 1 (by rfl) ⟨2084534, by rfl⟩ : syracuseStep 2779379 = 4169069) B4169069
theorem B2345203 : Blo 1851627 2345203 := bstep (se 1 (by rfl) ⟨1758902, by rfl⟩ : syracuseStep 2345203 = 3517805) B3517805
theorem B3516689 : Blo 1851627 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B2779409 : Blo 1851627 2779409 := bstep (se 2 (by rfl) ⟨1042278, by rfl⟩ : syracuseStep 2779409 = 2084557) B2084557
theorem B2779427 : Blo 1851627 2779427 := bstep (se 1 (by rfl) ⟨2084570, by rfl⟩ : syracuseStep 2779427 = 4169141) B4169141
theorem B2779457 : Blo 1851627 2779457 := bstep (se 2 (by rfl) ⟨1042296, by rfl⟩ : syracuseStep 2779457 = 2084593) B2084593
theorem B2779475 : Blo 1851627 2779475 := bstep (se 1 (by rfl) ⟨2084606, by rfl⟩ : syracuseStep 2779475 = 4169213) B4169213
theorem B2083171 : Blo 1851627 2083171 := bstep (se 1 (by rfl) ⟨1562378, by rfl⟩ : syracuseStep 2083171 = 3124757) B3124757
theorem B5278051 : Blo 1851627 5278051 := bstep (se 1 (by rfl) ⟨3958538, by rfl⟩ : syracuseStep 5278051 = 7917077) B7917077
theorem B2779505 : Blo 1851627 2779505 := bstep (se 2 (by rfl) ⟨1042314, by rfl⟩ : syracuseStep 2779505 = 2084629) B2084629
theorem B2779523 : Blo 1851627 2779523 := bstep (se 1 (by rfl) ⟨2084642, by rfl⟩ : syracuseStep 2779523 = 4169285) B4169285
theorem B3664273 : Blo 1851627 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B5278097 : Blo 1851627 5278097 := bstep (se 2 (by rfl) ⟨1979286, by rfl⟩ : syracuseStep 5278097 = 3958573) B3958573
theorem B2779553 : Blo 1851627 2779553 := bstep (se 2 (by rfl) ⟨1042332, by rfl⟩ : syracuseStep 2779553 = 2084665) B2084665
theorem B9374129 : Blo 1851627 9374129 := bstep (se 2 (by rfl) ⟨3515298, by rfl⟩ : syracuseStep 9374129 = 7030597) B7030597
theorem B2779571 : Blo 1851627 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B2779601 : Blo 1851627 2779601 := bstep (se 2 (by rfl) ⟨1042350, by rfl⟩ : syracuseStep 2779601 = 2084701) B2084701
theorem B2779619 : Blo 1851627 2779619 := bstep (se 1 (by rfl) ⟨2084714, by rfl⟩ : syracuseStep 2779619 = 4169429) B4169429
theorem B6253037 : Blo 1851627 6253037 := bstep (se 3 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 6253037 = 2344889) B2344889
theorem B2083315 : Blo 1851627 2083315 := bstep (se 1 (by rfl) ⟨1562486, by rfl⟩ : syracuseStep 2083315 = 3124973) B3124973
theorem B2779649 : Blo 1851627 2779649 := bstep (se 2 (by rfl) ⟨1042368, by rfl⟩ : syracuseStep 2779649 = 2084737) B2084737
theorem B4688401 : Blo 1851627 4688401 := bstep (se 2 (by rfl) ⟨1758150, by rfl⟩ : syracuseStep 4688401 = 3516301) B3516301
theorem B2779667 : Blo 1851627 2779667 := bstep (se 1 (by rfl) ⟨2084750, by rfl⟩ : syracuseStep 2779667 = 4169501) B4169501
theorem B6253091 : Blo 1851627 6253091 := bstep (se 1 (by rfl) ⟨4689818, by rfl⟩ : syracuseStep 6253091 = 9379637) B9379637
theorem B2779697 : Blo 1851627 2779697 := bstep (se 2 (by rfl) ⟨1042386, by rfl⟩ : syracuseStep 2779697 = 2084773) B2084773
theorem B2779715 : Blo 1851627 2779715 := bstep (se 1 (by rfl) ⟨2084786, by rfl⟩ : syracuseStep 2779715 = 4169573) B4169573
theorem B2779745 : Blo 1851627 2779745 := bstep (se 2 (by rfl) ⟨1042404, by rfl⟩ : syracuseStep 2779745 = 2084809) B2084809
theorem B2779763 : Blo 1851627 2779763 := bstep (se 1 (by rfl) ⟨2084822, by rfl⟩ : syracuseStep 2779763 = 4169645) B4169645
theorem B2083459 : Blo 1851627 2083459 := bstep (se 1 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 2083459 = 3125189) B3125189
theorem B2779793 : Blo 1851627 2779793 := bstep (se 2 (by rfl) ⟨1042422, by rfl⟩ : syracuseStep 2779793 = 2084845) B2084845
theorem B3517091 : Blo 1851627 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B2779811 : Blo 1851627 2779811 := bstep (se 1 (by rfl) ⟨2084858, by rfl⟩ : syracuseStep 2779811 = 4169717) B4169717
theorem B2779841 : Blo 1851627 2779841 := bstep (se 2 (by rfl) ⟨1042440, by rfl⟩ : syracuseStep 2779841 = 2084881) B2084881
theorem B2779859 : Blo 1851627 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B2345699 : Blo 1851627 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B10554097 : Blo 1851627 10554097 := bstep (se 2 (by rfl) ⟨3957786, by rfl⟩ : syracuseStep 10554097 = 7915573) B7915573
theorem B2779889 : Blo 1851627 2779889 := bstep (se 2 (by rfl) ⟨1042458, by rfl⟩ : syracuseStep 2779889 = 2084917) B2084917
theorem B2779907 : Blo 1851627 2779907 := bstep (se 1 (by rfl) ⟨2084930, by rfl⟩ : syracuseStep 2779907 = 4169861) B4169861
theorem B5933837 : Blo 1851627 5933837 := bstep (se 3 (by rfl) ⟨1112594, by rfl⟩ : syracuseStep 5933837 = 2225189) B2225189
theorem B2083603 : Blo 1851627 2083603 := bstep (se 1 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 2083603 = 3125405) B3125405
theorem B2779937 : Blo 1851627 2779937 := bstep (se 2 (by rfl) ⟨1042476, by rfl⟩ : syracuseStep 2779937 = 2084953) B2084953
theorem B4688675 : Blo 1851627 4688675 := bstep (se 1 (by rfl) ⟨3516506, by rfl⟩ : syracuseStep 4688675 = 7033013) B7033013
theorem B6679331 : Blo 1851627 6679331 := bstep (se 1 (by rfl) ⟨5009498, by rfl⟩ : syracuseStep 6679331 = 10018997) B10018997
theorem B6253361 : Blo 1851627 6253361 := bstep (se 2 (by rfl) ⟨2345010, by rfl⟩ : syracuseStep 6253361 = 4690021) B4690021
theorem B2779955 : Blo 1851627 2779955 := bstep (se 1 (by rfl) ⟨2084966, by rfl⟩ : syracuseStep 2779955 = 4169933) B4169933
theorem B2779985 : Blo 1851627 2779985 := bstep (se 2 (by rfl) ⟨1042494, by rfl⟩ : syracuseStep 2779985 = 2084989) B2084989
theorem B2968417 : Blo 1851627 2968417 := bstep (se 2 (by rfl) ⟨1113156, by rfl⟩ : syracuseStep 2968417 = 2226313) B2226313
theorem B2780003 : Blo 1851627 2780003 := bstep (se 1 (by rfl) ⟨2085002, by rfl⟩ : syracuseStep 2780003 = 4170005) B4170005
theorem B2780033 : Blo 1851627 2780033 := bstep (se 2 (by rfl) ⟨1042512, by rfl⟩ : syracuseStep 2780033 = 2085025) B2085025
theorem B4451203 : Blo 1851627 4451203 := bstep (se 1 (by rfl) ⟨3338402, by rfl⟩ : syracuseStep 4451203 = 6676805) B6676805
theorem B2780051 : Blo 1851627 2780051 := bstep (se 1 (by rfl) ⟨2085038, by rfl⟩ : syracuseStep 2780051 = 4170077) B4170077
theorem B2083747 : Blo 1851627 2083747 := bstep (se 1 (by rfl) ⟨1562810, by rfl⟩ : syracuseStep 2083747 = 3125621) B3125621
theorem B8022947 : Blo 1851627 8022947 := bstep (se 1 (by rfl) ⟨6017210, by rfl⟩ : syracuseStep 8022947 = 12034421) B12034421
theorem B2780081 : Blo 1851627 2780081 := bstep (se 2 (by rfl) ⟨1042530, by rfl⟩ : syracuseStep 2780081 = 2085061) B2085061
theorem B2780099 : Blo 1851627 2780099 := bstep (se 1 (by rfl) ⟨2085074, by rfl⟩ : syracuseStep 2780099 = 4170149) B4170149
theorem B2780129 : Blo 1851627 2780129 := bstep (se 2 (by rfl) ⟨1042548, by rfl⟩ : syracuseStep 2780129 = 2085097) B2085097
theorem B4688867 : Blo 1851627 4688867 := bstep (se 1 (by rfl) ⟨3516650, by rfl⟩ : syracuseStep 4688867 = 7033301) B7033301
theorem B2780147 : Blo 1851627 2780147 := bstep (se 1 (by rfl) ⟨2085110, by rfl⟩ : syracuseStep 2780147 = 4170221) B4170221
theorem B2780177 : Blo 1851627 2780177 := bstep (se 2 (by rfl) ⟨1042566, by rfl⟩ : syracuseStep 2780177 = 2085133) B2085133
theorem B7031843 : Blo 1851627 7031843 := bstep (se 1 (by rfl) ⟨5273882, by rfl⟩ : syracuseStep 7031843 = 10547765) B10547765
theorem B2780195 : Blo 1851627 2780195 := bstep (se 1 (by rfl) ⟨2085146, by rfl⟩ : syracuseStep 2780195 = 4170293) B4170293
theorem B4451377 : Blo 1851627 4451377 := bstep (se 2 (by rfl) ⟨1669266, by rfl⟩ : syracuseStep 4451377 = 3338533) B3338533
theorem B3566641 : Blo 1851627 3566641 := bstep (se 2 (by rfl) ⟨1337490, by rfl⟩ : syracuseStep 3566641 = 2674981) B2674981
theorem B2083891 : Blo 1851627 2083891 := bstep (se 1 (by rfl) ⟨1562918, by rfl⟩ : syracuseStep 2083891 = 3125837) B3125837
theorem B2780225 : Blo 1851627 2780225 := bstep (se 2 (by rfl) ⟨1042584, by rfl⟩ : syracuseStep 2780225 = 2085169) B2085169
theorem B2780243 : Blo 1851627 2780243 := bstep (se 1 (by rfl) ⟨2085182, by rfl⟩ : syracuseStep 2780243 = 4170365) B4170365
theorem B5008493 : Blo 1851627 5008493 := bstep (se 3 (by rfl) ⟨939092, by rfl⟩ : syracuseStep 5008493 = 1878185) B1878185
theorem B2780273 : Blo 1851627 2780273 := bstep (se 2 (by rfl) ⟨1042602, by rfl⟩ : syracuseStep 2780273 = 2085205) B2085205
theorem B2780291 : Blo 1851627 2780291 := bstep (se 1 (by rfl) ⟨2085218, by rfl⟩ : syracuseStep 2780291 = 4170437) B4170437
theorem B2780321 : Blo 1851627 2780321 := bstep (se 2 (by rfl) ⟨1042620, by rfl⟩ : syracuseStep 2780321 = 2085241) B2085241
theorem B7130275 : Blo 1851627 7130275 := bstep (se 1 (by rfl) ⟨5347706, by rfl⟩ : syracuseStep 7130275 = 10695413) B10695413
theorem B2780339 : Blo 1851627 2780339 := bstep (se 1 (by rfl) ⟨2085254, by rfl⟩ : syracuseStep 2780339 = 4170509) B4170509
theorem B2084035 : Blo 1851627 2084035 := bstep (se 1 (by rfl) ⟨1563026, by rfl⟩ : syracuseStep 2084035 = 3126053) B3126053
theorem B2780369 : Blo 1851627 2780369 := bstep (se 2 (by rfl) ⟨1042638, by rfl⟩ : syracuseStep 2780369 = 2085277) B2085277
theorem B7130339 : Blo 1851627 7130339 := bstep (se 1 (by rfl) ⟨5347754, by rfl⟩ : syracuseStep 7130339 = 10695509) B10695509
theorem B2780387 : Blo 1851627 2780387 := bstep (se 1 (by rfl) ⟨2085290, by rfl⟩ : syracuseStep 2780387 = 4170581) B4170581
theorem B3755249 : Blo 1851627 3755249 := bstep (se 2 (by rfl) ⟨1408218, by rfl⟩ : syracuseStep 3755249 = 2816437) B2816437
theorem B2780417 : Blo 1851627 2780417 := bstep (se 2 (by rfl) ⟨1042656, by rfl⟩ : syracuseStep 2780417 = 2085313) B2085313
theorem B2780435 : Blo 1851627 2780435 := bstep (se 1 (by rfl) ⟨2085326, by rfl⟩ : syracuseStep 2780435 = 4170653) B4170653
theorem B6253901 : Blo 1851627 6253901 := bstep (se 3 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 6253901 = 2345213) B2345213
theorem B2084179 : Blo 1851627 2084179 := bstep (se 1 (by rfl) ⟨1563134, by rfl⟩ : syracuseStep 2084179 = 3126269) B3126269
theorem B6253955 : Blo 1851627 6253955 := bstep (se 1 (by rfl) ⟨4690466, by rfl⟩ : syracuseStep 6253955 = 9380933) B9380933
theorem B2084323 : Blo 1851627 2084323 := bstep (se 1 (by rfl) ⟨1563242, by rfl⟩ : syracuseStep 2084323 = 3126485) B3126485
theorem B3124723 : Blo 1851627 3124723 := bstep (se 1 (by rfl) ⟨2343542, by rfl⟩ : syracuseStep 3124723 = 4687085) B4687085
theorem B3517987 : Blo 1851627 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B2674225 : Blo 1851627 2674225 := bstep (se 2 (by rfl) ⟨1002834, by rfl⟩ : syracuseStep 2674225 = 2005669) B2005669
theorem B357305909 : Blo 1851627 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B30469745 : Blo 1851627 30469745 := bstep (se 2 (by rfl) ⟨11426154, by rfl⟩ : syracuseStep 30469745 = 22852309) B22852309
theorem B2084467 : Blo 1851627 2084467 := bstep (se 1 (by rfl) ⟨1563350, by rfl⟩ : syracuseStep 2084467 = 3126701) B3126701
theorem B3124865 : Blo 1851627 3124865 := bstep (se 2 (by rfl) ⟨1171824, by rfl⟩ : syracuseStep 3124865 = 2343649) B2343649
theorem B6254225 : Blo 1851627 6254225 := bstep (se 2 (by rfl) ⟨2345334, by rfl⟩ : syracuseStep 6254225 = 4690669) B4690669
theorem B3518147 : Blo 1851627 3518147 := bstep (se 1 (by rfl) ⟨2638610, by rfl⟩ : syracuseStep 3518147 = 5277221) B5277221
theorem B3124993 : Blo 1851627 3124993 := bstep (se 2 (by rfl) ⟨1171872, by rfl⟩ : syracuseStep 3124993 = 2343745) B2343745
theorem B2084611 : Blo 1851627 2084611 := bstep (se 1 (by rfl) ⟨1563458, by rfl⟩ : syracuseStep 2084611 = 3126917) B3126917
theorem B3125027 : Blo 1851627 3125027 := bstep (se 1 (by rfl) ⟨2343770, by rfl⟩ : syracuseStep 3125027 = 4687541) B4687541
theorem B9506609 : Blo 1851627 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B2256707 : Blo 1851627 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B9375587 : Blo 1851627 9375587 := bstep (se 1 (by rfl) ⟨7031690, by rfl⟩ : syracuseStep 9375587 = 14063381) B14063381
theorem B13356899 : Blo 1851627 13356899 := bstep (se 1 (by rfl) ⟨10017674, by rfl⟩ : syracuseStep 13356899 = 20035349) B20035349
theorem B4689809 : Blo 1851627 4689809 := bstep (se 2 (by rfl) ⟨1758678, by rfl⟩ : syracuseStep 4689809 = 3517357) B3517357
theorem B2084755 : Blo 1851627 2084755 := bstep (se 1 (by rfl) ⟨1563566, by rfl⟩ : syracuseStep 2084755 = 3127133) B3127133
theorem B3125155 : Blo 1851627 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B4689859 : Blo 1851627 4689859 := bstep (se 1 (by rfl) ⟨3517394, by rfl⟩ : syracuseStep 4689859 = 7034789) B7034789
theorem B7032845 : Blo 1851627 7032845 := bstep (se 3 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 7032845 = 2637317) B2637317
theorem B2084899 : Blo 1851627 2084899 := bstep (se 1 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 2084899 = 3127349) B3127349
theorem B3125297 : Blo 1851627 3125297 := bstep (se 2 (by rfl) ⟨1171986, by rfl⟩ : syracuseStep 3125297 = 2343973) B2343973
theorem B4690001 : Blo 1851627 4690001 := bstep (se 2 (by rfl) ⟨1758750, by rfl⟩ : syracuseStep 4690001 = 3517501) B3517501
theorem B12669041 : Blo 1851627 12669041 := bstep (se 2 (by rfl) ⟨4750890, by rfl⟩ : syracuseStep 12669041 = 9501781) B9501781
theorem B10547333 : Blo 1851627 10547333 := bstep (se 4 (by rfl) ⟨988812, by rfl⟩ : syracuseStep 10547333 = 1977625) B1977625
theorem B8450189 : Blo 1851627 8450189 := bstep (se 3 (by rfl) ⟨1584410, by rfl⟩ : syracuseStep 8450189 = 3168821) B3168821
theorem B10555555 : Blo 1851627 10555555 := bstep (se 1 (by rfl) ⟨7916666, by rfl⟩ : syracuseStep 10555555 = 15833333) B15833333
theorem B6254765 : Blo 1851627 6254765 := bstep (se 3 (by rfl) ⟨1172768, by rfl⟩ : syracuseStep 6254765 = 2345537) B2345537
theorem B3125425 : Blo 1851627 3125425 := bstep (se 2 (by rfl) ⟨1172034, by rfl⟩ : syracuseStep 3125425 = 2344069) B2344069
theorem B2085043 : Blo 1851627 2085043 := bstep (se 1 (by rfl) ⟨1563782, by rfl⟩ : syracuseStep 2085043 = 3127565) B3127565
theorem B3125459 : Blo 1851627 3125459 := bstep (se 1 (by rfl) ⟨2344094, by rfl⟩ : syracuseStep 3125459 = 4688189) B4688189
theorem B6254819 : Blo 1851627 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B19263757 : Blo 1851627 19263757 := bstep (se 3 (by rfl) ⟨3611954, by rfl⟩ : syracuseStep 19263757 = 7223909) B7223909
theorem B5009681 : Blo 1851627 5009681 := bstep (se 2 (by rfl) ⟨1878630, by rfl⟩ : syracuseStep 5009681 = 3757261) B3757261
theorem B2085187 : Blo 1851627 2085187 := bstep (se 1 (by rfl) ⟨1563890, by rfl⟩ : syracuseStep 2085187 = 3127781) B3127781
theorem B3125587 : Blo 1851627 3125587 := bstep (se 1 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 3125587 = 4688381) B4688381
theorem B14061923 : Blo 1851627 14061923 := bstep (se 1 (by rfl) ⟨10546442, by rfl⟩ : syracuseStep 14061923 = 21092885) B21092885
theorem B1978787 : Blo 1851627 1978787 := bstep (se 1 (by rfl) ⟨1484090, by rfl⟩ : syracuseStep 1978787 = 2968181) B2968181
theorem B2503105 : Blo 1851627 2503105 := bstep (se 2 (by rfl) ⟨938664, by rfl⟩ : syracuseStep 2503105 = 1877329) B1877329
theorem B2085331 : Blo 1851627 2085331 := bstep (se 1 (by rfl) ⟨1563998, by rfl⟩ : syracuseStep 2085331 = 3127997) B3127997
theorem B3125729 : Blo 1851627 3125729 := bstep (se 2 (by rfl) ⟨1172148, by rfl⟩ : syracuseStep 3125729 = 2344297) B2344297
theorem B6255089 : Blo 1851627 6255089 := bstep (se 2 (by rfl) ⟨2345658, by rfl⟩ : syracuseStep 6255089 = 4691317) B4691317
theorem B2224675 : Blo 1851627 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B4166225 : Blo 1851627 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B3125857 : Blo 1851627 3125857 := bstep (se 2 (by rfl) ⟨1172196, by rfl⟩ : syracuseStep 3125857 = 2344393) B2344393
theorem B4166243 : Blo 1851627 4166243 := bstep (se 1 (by rfl) ⟨3124682, by rfl⟩ : syracuseStep 4166243 = 6249365) B6249365
theorem B5345905 : Blo 1851627 5345905 := bstep (se 2 (by rfl) ⟨2004714, by rfl⟩ : syracuseStep 5345905 = 4009429) B4009429
theorem B3125891 : Blo 1851627 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B9376397 : Blo 1851627 9376397 := bstep (se 3 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 9376397 = 3516149) B3516149
theorem B6337201 : Blo 1851627 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B10556081 : Blo 1851627 10556081 := bstep (se 2 (by rfl) ⟨3958530, by rfl⟩ : syracuseStep 10556081 = 7917061) B7917061
theorem B4510417 : Blo 1851627 4510417 := bstep (se 2 (by rfl) ⟨1691406, by rfl⟩ : syracuseStep 4510417 = 3382813) B3382813
theorem B3126019 : Blo 1851627 3126019 := bstep (se 1 (by rfl) ⟨2344514, by rfl⟩ : syracuseStep 3126019 = 4689029) B4689029
theorem B6017809 : Blo 1851627 6017809 := bstep (se 2 (by rfl) ⟨2256678, by rfl⟩ : syracuseStep 6017809 = 4513357) B4513357
theorem B5010221 : Blo 1851627 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B7910243 : Blo 1851627 7910243 := bstep (se 1 (by rfl) ⟨5932682, by rfl⟩ : syracuseStep 7910243 = 11865365) B11865365
theorem B4166513 : Blo 1851627 4166513 := bstep (se 2 (by rfl) ⟨1562442, by rfl⟩ : syracuseStep 4166513 = 3124885) B3124885
theorem B4166531 : Blo 1851627 4166531 := bstep (se 1 (by rfl) ⟨3124898, by rfl⟩ : syracuseStep 4166531 = 6249797) B6249797
theorem B3126161 : Blo 1851627 3126161 := bstep (se 2 (by rfl) ⟨1172310, by rfl⟩ : syracuseStep 3126161 = 2344621) B2344621
theorem B11867057 : Blo 1851627 11867057 := bstep (se 2 (by rfl) ⟨4450146, by rfl⟩ : syracuseStep 11867057 = 8900293) B8900293
theorem B3806147 : Blo 1851627 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B5632973 : Blo 1851627 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B11867107 : Blo 1851627 11867107 := bstep (se 1 (by rfl) ⟨8900330, by rfl⟩ : syracuseStep 11867107 = 17800661) B17800661
theorem B12030989 : Blo 1851627 12030989 := bstep (se 3 (by rfl) ⟨2255810, by rfl⟩ : syracuseStep 12030989 = 4511621) B4511621
theorem B6255629 : Blo 1851627 6255629 := bstep (se 3 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 6255629 = 2345861) B2345861
theorem B3126289 : Blo 1851627 3126289 := bstep (se 2 (by rfl) ⟨1172358, by rfl⟩ : syracuseStep 3126289 = 2344717) B2344717
theorem B4690993 : Blo 1851627 4690993 := bstep (se 2 (by rfl) ⟨1759122, by rfl⟩ : syracuseStep 4690993 = 3518245) B3518245
theorem B3126323 : Blo 1851627 3126323 := bstep (se 1 (by rfl) ⟨2344742, by rfl⟩ : syracuseStep 3126323 = 4689485) B4689485
theorem B6255683 : Blo 1851627 6255683 := bstep (se 1 (by rfl) ⟨4691762, by rfl⟩ : syracuseStep 6255683 = 9383525) B9383525
theorem B21091427 : Blo 1851627 21091427 := bstep (se 1 (by rfl) ⟨15818570, by rfl⟩ : syracuseStep 21091427 = 31637141) B31637141
theorem B40613005 : Blo 1851627 40613005 := bstep (se 3 (by rfl) ⟨7614938, by rfl⟩ : syracuseStep 40613005 = 15229877) B15229877
theorem B4166801 : Blo 1851627 4166801 := bstep (se 2 (by rfl) ⟨1562550, by rfl⟩ : syracuseStep 4166801 = 3125101) B3125101
theorem B3806353 : Blo 1851627 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B4166819 : Blo 1851627 4166819 := bstep (se 1 (by rfl) ⟨3125114, by rfl⟩ : syracuseStep 4166819 = 6250229) B6250229
theorem B3126451 : Blo 1851627 3126451 := bstep (se 1 (by rfl) ⟨2344838, by rfl⟩ : syracuseStep 3126451 = 4689677) B4689677
theorem B5346577 : Blo 1851627 5346577 := bstep (se 2 (by rfl) ⟨2004966, by rfl⟩ : syracuseStep 5346577 = 4009933) B4009933
theorem B3126593 : Blo 1851627 3126593 := bstep (se 2 (by rfl) ⟨1172472, by rfl⟩ : syracuseStep 3126593 = 2344945) B2344945
theorem B4691267 : Blo 1851627 4691267 := bstep (se 1 (by rfl) ⟨3518450, by rfl⟩ : syracuseStep 4691267 = 7036901) B7036901
theorem B6255953 : Blo 1851627 6255953 := bstep (se 2 (by rfl) ⟨2345982, by rfl⟩ : syracuseStep 6255953 = 4691965) B4691965
theorem B4167089 : Blo 1851627 4167089 := bstep (se 2 (by rfl) ⟨1562658, by rfl⟩ : syracuseStep 4167089 = 3125317) B3125317
theorem B5494193 : Blo 1851627 5494193 := bstep (se 2 (by rfl) ⟨2060322, by rfl⟩ : syracuseStep 5494193 = 4120645) B4120645
theorem B3126721 : Blo 1851627 3126721 := bstep (se 2 (by rfl) ⟨1172520, by rfl⟩ : syracuseStep 3126721 = 2345041) B2345041
theorem B4167107 : Blo 1851627 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B3126755 : Blo 1851627 3126755 := bstep (se 1 (by rfl) ⟨2345066, by rfl⟩ : syracuseStep 3126755 = 4690133) B4690133
theorem B4691459 : Blo 1851627 4691459 := bstep (se 1 (by rfl) ⟨3518594, by rfl⟩ : syracuseStep 4691459 = 7037189) B7037189
theorem B3757585 : Blo 1851627 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B3757603 : Blo 1851627 3757603 := bstep (se 1 (by rfl) ⟨2818202, by rfl⟩ : syracuseStep 3757603 = 5636405) B5636405
theorem B3126883 : Blo 1851627 3126883 := bstep (se 1 (by rfl) ⟨2345162, by rfl⟩ : syracuseStep 3126883 = 4690325) B4690325
theorem B10016419 : Blo 1851627 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B11876003 : Blo 1851627 11876003 := bstep (se 1 (by rfl) ⟨8907002, by rfl⟩ : syracuseStep 11876003 = 17814005) B17814005
theorem B4167377 : Blo 1851627 4167377 := bstep (se 2 (by rfl) ⟨1562766, by rfl⟩ : syracuseStep 4167377 = 3125533) B3125533
theorem B4167395 : Blo 1851627 4167395 := bstep (se 1 (by rfl) ⟨3125546, by rfl⟩ : syracuseStep 4167395 = 6251093) B6251093
theorem B3127025 : Blo 1851627 3127025 := bstep (se 2 (by rfl) ⟨1172634, by rfl⟩ : syracuseStep 3127025 = 2345269) B2345269
theorem B3127153 : Blo 1851627 3127153 := bstep (se 2 (by rfl) ⟨1172682, by rfl⟩ : syracuseStep 3127153 = 2345365) B2345365
theorem B3127187 : Blo 1851627 3127187 := bstep (se 1 (by rfl) ⟨2345390, by rfl⟩ : syracuseStep 3127187 = 4690781) B4690781
theorem B3168163 : Blo 1851627 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B4167665 : Blo 1851627 4167665 := bstep (se 2 (by rfl) ⟨1562874, by rfl⟩ : syracuseStep 4167665 = 3125749) B3125749
theorem B4167683 : Blo 1851627 4167683 := bstep (se 1 (by rfl) ⟨3125762, by rfl⟩ : syracuseStep 4167683 = 6251525) B6251525
theorem B3127315 : Blo 1851627 3127315 := bstep (se 1 (by rfl) ⟨2345486, by rfl⟩ : syracuseStep 3127315 = 4690973) B4690973
theorem B3168323 : Blo 1851627 3168323 := bstep (se 1 (by rfl) ⟨2376242, by rfl⟩ : syracuseStep 3168323 = 4752485) B4752485
theorem B5273677 : Blo 1851627 5273677 := bstep (se 3 (by rfl) ⟨988814, by rfl⟩ : syracuseStep 5273677 = 1977629) B1977629
theorem B7034957 : Blo 1851627 7034957 := bstep (se 3 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 7034957 = 2638109) B2638109
theorem B23730317 : Blo 1851627 23730317 := bstep (se 3 (by rfl) ⟨4449434, by rfl⟩ : syracuseStep 23730317 = 8898869) B8898869
theorem B3127457 : Blo 1851627 3127457 := bstep (se 2 (by rfl) ⟨1172796, by rfl⟩ : syracuseStep 3127457 = 2345593) B2345593
theorem B4167953 : Blo 1851627 4167953 := bstep (se 2 (by rfl) ⟨1562982, by rfl⟩ : syracuseStep 4167953 = 3125965) B3125965
theorem B5937425 : Blo 1851627 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B3127585 : Blo 1851627 3127585 := bstep (se 2 (by rfl) ⟨1172844, by rfl⟩ : syracuseStep 3127585 = 2345689) B2345689
theorem B4167971 : Blo 1851627 4167971 := bstep (se 1 (by rfl) ⟨3125978, by rfl⟩ : syracuseStep 4167971 = 6251957) B6251957
theorem B2226467 : Blo 1851627 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B5273905 : Blo 1851627 5273905 := bstep (se 2 (by rfl) ⟨1977714, by rfl⟩ : syracuseStep 5273905 = 3955429) B3955429
theorem B3127619 : Blo 1851627 3127619 := bstep (se 1 (by rfl) ⟨2345714, by rfl⟩ : syracuseStep 3127619 = 4691429) B4691429
theorem B2111923 : Blo 1851627 2111923 := bstep (se 1 (by rfl) ⟨1583942, by rfl⟩ : syracuseStep 2111923 = 3167885) B3167885
theorem B3955139 : Blo 1851627 3955139 := bstep (se 1 (by rfl) ⟨2966354, by rfl⟩ : syracuseStep 3955139 = 5932709) B5932709
theorem B3127747 : Blo 1851627 3127747 := bstep (se 1 (by rfl) ⟨2345810, by rfl⟩ : syracuseStep 3127747 = 4691621) B4691621
theorem B5274065 : Blo 1851627 5274065 := bstep (se 2 (by rfl) ⟨1977774, by rfl⟩ : syracuseStep 5274065 = 3955549) B3955549
theorem B4168241 : Blo 1851627 4168241 := bstep (se 2 (by rfl) ⟨1563090, by rfl⟩ : syracuseStep 4168241 = 3126181) B3126181
theorem B5274179 : Blo 1851627 5274179 := bstep (se 1 (by rfl) ⟨3955634, by rfl⟩ : syracuseStep 5274179 = 7911269) B7911269
theorem B4168259 : Blo 1851627 4168259 := bstep (se 1 (by rfl) ⟨3126194, by rfl⟩ : syracuseStep 4168259 = 6252389) B6252389
theorem B3127889 : Blo 1851627 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B2005651 : Blo 1851627 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B2636497 : Blo 1851627 2636497 := bstep (se 2 (by rfl) ⟨988686, by rfl⟩ : syracuseStep 2636497 = 1977373) B1977373
theorem B4168529 : Blo 1851627 4168529 := bstep (se 2 (by rfl) ⟨1563198, by rfl⟩ : syracuseStep 4168529 = 3126397) B3126397
theorem B4168547 : Blo 1851627 4168547 := bstep (se 1 (by rfl) ⟨3126410, by rfl⟩ : syracuseStep 4168547 = 6252821) B6252821
theorem B7035761 : Blo 1851627 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B6339491 : Blo 1851627 6339491 := bstep (se 1 (by rfl) ⟨4754618, by rfl⟩ : syracuseStep 6339491 = 9509237) B9509237
theorem B4225969 : Blo 1851627 4225969 := bstep (se 2 (by rfl) ⟨1584738, by rfl⟩ : syracuseStep 4225969 = 3169477) B3169477
theorem B5938115 : Blo 1851627 5938115 := bstep (se 1 (by rfl) ⟨4453586, by rfl⟩ : syracuseStep 5938115 = 8907173) B8907173
theorem B11262925 : Blo 1851627 11262925 := bstep (se 3 (by rfl) ⟨2111798, by rfl⟩ : syracuseStep 11262925 = 4223597) B4223597
theorem B3955729 : Blo 1851627 3955729 := bstep (se 2 (by rfl) ⟨1483398, by rfl⟩ : syracuseStep 3955729 = 2966797) B2966797
theorem B9403469 : Blo 1851627 9403469 := bstep (se 3 (by rfl) ⟨1763150, by rfl⟩ : syracuseStep 9403469 = 3526301) B3526301
theorem B6249581 : Blo 1851627 6249581 := bstep (se 3 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 6249581 = 2343593) B2343593
theorem B4168817 : Blo 1851627 4168817 := bstep (se 2 (by rfl) ⟨1563306, by rfl⟩ : syracuseStep 4168817 = 3126613) B3126613
theorem B4168835 : Blo 1851627 4168835 := bstep (se 1 (by rfl) ⟨3126626, by rfl⟩ : syracuseStep 4168835 = 6253253) B6253253
theorem B6249635 : Blo 1851627 6249635 := bstep (se 1 (by rfl) ⟨4687226, by rfl⟩ : syracuseStep 6249635 = 9374453) B9374453
theorem B14073101 : Blo 1851627 14073101 := bstep (se 3 (by rfl) ⟨2638706, by rfl⟩ : syracuseStep 14073101 = 5277413) B5277413
theorem B24067381 : Blo 1851627 24067381 := bstep (se 5 (by rfl) ⟨1128158, by rfl⟩ : syracuseStep 24067381 = 2256317) B2256317
theorem B11869517 : Blo 1851627 11869517 := bstep (se 3 (by rfl) ⟨2225534, by rfl⟩ : syracuseStep 11869517 = 4451069) B4451069
theorem B4169105 : Blo 1851627 4169105 := bstep (se 2 (by rfl) ⟨1563414, by rfl⟩ : syracuseStep 4169105 = 3126829) B3126829
theorem B2637203 : Blo 1851627 2637203 := bstep (se 1 (by rfl) ⟨1977902, by rfl⟩ : syracuseStep 2637203 = 3955805) B3955805
theorem B4169123 : Blo 1851627 4169123 := bstep (se 1 (by rfl) ⟨3126842, by rfl⟩ : syracuseStep 4169123 = 6253685) B6253685
theorem B6249905 : Blo 1851627 6249905 := bstep (se 2 (by rfl) ⟨2343714, by rfl⟩ : syracuseStep 6249905 = 4687429) B4687429
theorem B9379313 : Blo 1851627 9379313 := bstep (se 2 (by rfl) ⟨3517242, by rfl⟩ : syracuseStep 9379313 = 7034485) B7034485
theorem B7036429 : Blo 1851627 7036429 := bstep (se 3 (by rfl) ⟨1319330, by rfl⟩ : syracuseStep 7036429 = 2638661) B2638661
theorem B5275181 : Blo 1851627 5275181 := bstep (se 3 (by rfl) ⟨989096, by rfl⟩ : syracuseStep 5275181 = 1978193) B1978193
theorem B4169393 : Blo 1851627 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B4169411 : Blo 1851627 4169411 := bstep (se 1 (by rfl) ⟨3127058, by rfl⟩ : syracuseStep 4169411 = 6254117) B6254117
theorem B5635793 : Blo 1851627 5635793 := bstep (se 2 (by rfl) ⟨2113422, by rfl⟩ : syracuseStep 5635793 = 4226845) B4226845
theorem B5275363 : Blo 1851627 5275363 := bstep (se 1 (by rfl) ⟨3956522, by rfl⟩ : syracuseStep 5275363 = 7913045) B7913045
theorem B5275523 : Blo 1851627 5275523 := bstep (se 1 (by rfl) ⟨3956642, by rfl⟩ : syracuseStep 5275523 = 7913285) B7913285
theorem B10551181 : Blo 1851627 10551181 := bstep (se 3 (by rfl) ⟨1978346, by rfl⟩ : syracuseStep 10551181 = 3956693) B3956693
theorem B6250445 : Blo 1851627 6250445 := bstep (se 3 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 6250445 = 2343917) B2343917
theorem B4169681 : Blo 1851627 4169681 := bstep (se 2 (by rfl) ⟨1563630, by rfl⟩ : syracuseStep 4169681 = 3127261) B3127261
theorem B4169699 : Blo 1851627 4169699 := bstep (se 1 (by rfl) ⟨3127274, by rfl⟩ : syracuseStep 4169699 = 6254549) B6254549
theorem B4169753 : Blo 1851627 4169753 := bstep (se 2 (by rfl) ⟨1563657, by rfl⟩ : syracuseStep 4169753 = 3127315) B3127315
theorem B8446027 : Blo 1851627 8446027 := bstep (se 1 (by rfl) ⟨6334520, by rfl⟩ : syracuseStep 8446027 = 12669041) B12669041
theorem B4169843 : Blo 1851627 4169843 := bstep (se 1 (by rfl) ⟨3127382, by rfl⟩ : syracuseStep 4169843 = 6254765) B6254765
theorem B4169879 : Blo 1851627 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B7913645 : Blo 1851627 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B5005529 : Blo 1851627 5005529 := bstep (se 2 (by rfl) ⟨1877073, by rfl⟩ : syracuseStep 5005529 = 3754147) B3754147
theorem B14074073 : Blo 1851627 14074073 := bstep (se 2 (by rfl) ⟨5277777, by rfl⟩ : syracuseStep 14074073 = 10555555) B10555555
theorem B1851627 : Blo 1851627 1851627 := bstep (se 1 (by rfl) ⟨1388720, by rfl⟩ : syracuseStep 1851627 = 2777441) B2777441
theorem B1851639 : Blo 1851627 1851639 := bstep (se 1 (by rfl) ⟨1388729, by rfl⟩ : syracuseStep 1851639 = 2777459) B2777459
theorem B1851659 : Blo 1851627 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B1851671 : Blo 1851627 1851671 := bstep (se 1 (by rfl) ⟨1388753, by rfl⟩ : syracuseStep 1851671 = 2777507) B2777507
theorem B1851691 : Blo 1851627 1851691 := bstep (se 1 (by rfl) ⟨1388768, by rfl⟩ : syracuseStep 1851691 = 2777537) B2777537
theorem B5275955 : Blo 1851627 5275955 := bstep (se 1 (by rfl) ⟨3956966, by rfl⟩ : syracuseStep 5275955 = 7913933) B7913933
theorem B1851703 : Blo 1851627 1851703 := bstep (se 1 (by rfl) ⟨1388777, by rfl⟩ : syracuseStep 1851703 = 2777555) B2777555
theorem B1851723 : Blo 1851627 1851723 := bstep (se 1 (by rfl) ⟨1388792, by rfl⟩ : syracuseStep 1851723 = 2777585) B2777585
theorem B5275979 : Blo 1851627 5275979 := bstep (se 1 (by rfl) ⟨3956984, by rfl⟩ : syracuseStep 5275979 = 7913969) B7913969
theorem B4170059 : Blo 1851627 4170059 := bstep (se 1 (by rfl) ⟨3127544, by rfl⟩ : syracuseStep 4170059 = 6255089) B6255089
theorem B1851735 : Blo 1851627 1851735 := bstep (se 1 (by rfl) ⟨1388801, by rfl⟩ : syracuseStep 1851735 = 2777603) B2777603
theorem B1851755 : Blo 1851627 1851755 := bstep (se 1 (by rfl) ⟨1388816, by rfl⟩ : syracuseStep 1851755 = 2777633) B2777633
theorem B1851767 : Blo 1851627 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B4170113 : Blo 1851627 4170113 := bstep (se 2 (by rfl) ⟨1563792, by rfl⟩ : syracuseStep 4170113 = 3127585) B3127585
theorem B2777483 : Blo 1851627 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B1851787 : Blo 1851627 1851787 := bstep (se 1 (by rfl) ⟨1388840, by rfl⟩ : syracuseStep 1851787 = 2777681) B2777681
theorem B2777495 : Blo 1851627 2777495 := bstep (se 1 (by rfl) ⟨2083121, by rfl⟩ : syracuseStep 2777495 = 4166243) B4166243
theorem B1851799 : Blo 1851627 1851799 := bstep (se 1 (by rfl) ⟨1388849, by rfl⟩ : syracuseStep 1851799 = 2777699) B2777699
theorem B1851819 : Blo 1851627 1851819 := bstep (se 1 (by rfl) ⟨1388864, by rfl⟩ : syracuseStep 1851819 = 2777729) B2777729
theorem B6250931 : Blo 1851627 6250931 := bstep (se 1 (by rfl) ⟨4688198, by rfl⟩ : syracuseStep 6250931 = 9376397) B9376397
theorem B1851831 : Blo 1851627 1851831 := bstep (se 1 (by rfl) ⟨1388873, by rfl⟩ : syracuseStep 1851831 = 2777747) B2777747
theorem B1851851 : Blo 1851627 1851851 := bstep (se 1 (by rfl) ⟨1388888, by rfl⟩ : syracuseStep 1851851 = 2777777) B2777777
theorem B7037387 : Blo 1851627 7037387 := bstep (se 1 (by rfl) ⟨5278040, by rfl⟩ : syracuseStep 7037387 = 10556081) B10556081
theorem B1851863 : Blo 1851627 1851863 := bstep (se 1 (by rfl) ⟨1388897, by rfl⟩ : syracuseStep 1851863 = 2777795) B2777795
theorem B2777561 : Blo 1851627 2777561 := bstep (se 2 (by rfl) ⟨1041585, by rfl⟩ : syracuseStep 2777561 = 2083171) B2083171
theorem B7037401 : Blo 1851627 7037401 := bstep (se 2 (by rfl) ⟨2639025, by rfl⟩ : syracuseStep 7037401 = 5278051) B5278051
theorem B1851883 : Blo 1851627 1851883 := bstep (se 1 (by rfl) ⟨1388912, by rfl⟩ : syracuseStep 1851883 = 2777825) B2777825
theorem B1851895 : Blo 1851627 1851895 := bstep (se 1 (by rfl) ⟨1388921, by rfl⟩ : syracuseStep 1851895 = 2777843) B2777843
theorem B1851915 : Blo 1851627 1851915 := bstep (se 1 (by rfl) ⟨1388936, by rfl⟩ : syracuseStep 1851915 = 2777873) B2777873
theorem B1851927 : Blo 1851627 1851927 := bstep (se 1 (by rfl) ⟨1388945, by rfl⟩ : syracuseStep 1851927 = 2777891) B2777891
theorem B1851947 : Blo 1851627 1851947 := bstep (se 1 (by rfl) ⟨1388960, by rfl⟩ : syracuseStep 1851947 = 2777921) B2777921
theorem B3811263029 : Blo 1851627 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B1851959 : Blo 1851627 1851959 := bstep (se 1 (by rfl) ⟨1388969, by rfl⟩ : syracuseStep 1851959 = 2777939) B2777939
theorem B2777675 : Blo 1851627 2777675 := bstep (se 1 (by rfl) ⟨2083256, by rfl⟩ : syracuseStep 2777675 = 4166513) B4166513
theorem B1851979 : Blo 1851627 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B2777687 : Blo 1851627 2777687 := bstep (se 1 (by rfl) ⟨2083265, by rfl⟩ : syracuseStep 2777687 = 4166531) B4166531
theorem B1851991 : Blo 1851627 1851991 := bstep (se 1 (by rfl) ⟨1388993, by rfl⟩ : syracuseStep 1851991 = 2777987) B2777987
theorem B4170329 : Blo 1851627 4170329 := bstep (se 2 (by rfl) ⟨1563873, by rfl⟩ : syracuseStep 4170329 = 3127747) B3127747
theorem B1852011 : Blo 1851627 1852011 := bstep (se 1 (by rfl) ⟨1389008, by rfl⟩ : syracuseStep 1852011 = 2778017) B2778017
theorem B1852023 : Blo 1851627 1852023 := bstep (se 1 (by rfl) ⟨1389017, by rfl⟩ : syracuseStep 1852023 = 2778035) B2778035
theorem B1852043 : Blo 1851627 1852043 := bstep (se 1 (by rfl) ⟨1389032, by rfl⟩ : syracuseStep 1852043 = 2778065) B2778065
theorem B1852055 : Blo 1851627 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B2777753 : Blo 1851627 2777753 := bstep (se 2 (by rfl) ⟨1041657, by rfl⟩ : syracuseStep 2777753 = 2083315) B2083315
theorem B1852075 : Blo 1851627 1852075 := bstep (se 1 (by rfl) ⟨1389056, by rfl⟩ : syracuseStep 1852075 = 2778113) B2778113
theorem B4170419 : Blo 1851627 4170419 := bstep (se 1 (by rfl) ⟨3127814, by rfl⟩ : syracuseStep 4170419 = 6255629) B6255629
theorem B1852087 : Blo 1851627 1852087 := bstep (se 1 (by rfl) ⟨1389065, by rfl⟩ : syracuseStep 1852087 = 2778131) B2778131
theorem B6251201 : Blo 1851627 6251201 := bstep (se 2 (by rfl) ⟨2344200, by rfl⟩ : syracuseStep 6251201 = 4688401) B4688401
theorem B1852107 : Blo 1851627 1852107 := bstep (se 1 (by rfl) ⟨1389080, by rfl⟩ : syracuseStep 1852107 = 2778161) B2778161
theorem B1852119 : Blo 1851627 1852119 := bstep (se 1 (by rfl) ⟨1389089, by rfl⟩ : syracuseStep 1852119 = 2778179) B2778179
theorem B4170455 : Blo 1851627 4170455 := bstep (se 1 (by rfl) ⟨3127841, by rfl⟩ : syracuseStep 4170455 = 6255683) B6255683
theorem B2966233 : Blo 1851627 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B1852139 : Blo 1851627 1852139 := bstep (se 1 (by rfl) ⟨1389104, by rfl⟩ : syracuseStep 1852139 = 2778209) B2778209
theorem B1852151 : Blo 1851627 1852151 := bstep (se 1 (by rfl) ⟨1389113, by rfl⟩ : syracuseStep 1852151 = 2778227) B2778227
theorem B2777867 : Blo 1851627 2777867 := bstep (se 1 (by rfl) ⟨2083400, by rfl⟩ : syracuseStep 2777867 = 4166801) B4166801
theorem B1852171 : Blo 1851627 1852171 := bstep (se 1 (by rfl) ⟨1389128, by rfl⟩ : syracuseStep 1852171 = 2778257) B2778257
theorem B2777879 : Blo 1851627 2777879 := bstep (se 1 (by rfl) ⟨2083409, by rfl⟩ : syracuseStep 2777879 = 4166819) B4166819
theorem B1852183 : Blo 1851627 1852183 := bstep (se 1 (by rfl) ⟨1389137, by rfl⟩ : syracuseStep 1852183 = 2778275) B2778275
theorem B1852203 : Blo 1851627 1852203 := bstep (se 1 (by rfl) ⟨1389152, by rfl⟩ : syracuseStep 1852203 = 2778305) B2778305
theorem B1852215 : Blo 1851627 1852215 := bstep (se 1 (by rfl) ⟨1389161, by rfl⟩ : syracuseStep 1852215 = 2778323) B2778323
theorem B7127873 : Blo 1851627 7127873 := bstep (se 2 (by rfl) ⟨2672952, by rfl⟩ : syracuseStep 7127873 = 5345905) B5345905
theorem B2343755 : Blo 1851627 2343755 := bstep (se 1 (by rfl) ⟨1757816, by rfl⟩ : syracuseStep 2343755 = 3515633) B3515633
theorem B1852235 : Blo 1851627 1852235 := bstep (se 1 (by rfl) ⟨1389176, by rfl⟩ : syracuseStep 1852235 = 2778353) B2778353
theorem B10552139 : Blo 1851627 10552139 := bstep (se 1 (by rfl) ⟨7914104, by rfl⟩ : syracuseStep 10552139 = 15828209) B15828209
theorem B1852247 : Blo 1851627 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B2777945 : Blo 1851627 2777945 := bstep (se 2 (by rfl) ⟨1041729, by rfl⟩ : syracuseStep 2777945 = 2083459) B2083459
theorem B38028133 : Blo 1851627 38028133 := bstep (se 4 (by rfl) ⟨3565137, by rfl⟩ : syracuseStep 38028133 = 7130275) B7130275
theorem B1852267 : Blo 1851627 1852267 := bstep (se 1 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 1852267 = 2778401) B2778401
theorem B1852279 : Blo 1851627 1852279 := bstep (se 1 (by rfl) ⟨1389209, by rfl⟩ : syracuseStep 1852279 = 2778419) B2778419
theorem B1852299 : Blo 1851627 1852299 := bstep (se 1 (by rfl) ⟨1389224, by rfl⟩ : syracuseStep 1852299 = 2778449) B2778449
theorem B4170635 : Blo 1851627 4170635 := bstep (se 1 (by rfl) ⟨3127976, by rfl⟩ : syracuseStep 4170635 = 6255953) B6255953
theorem B1852311 : Blo 1851627 1852311 := bstep (se 1 (by rfl) ⟨1389233, by rfl⟩ : syracuseStep 1852311 = 2778467) B2778467
theorem B1852331 : Blo 1851627 1852331 := bstep (se 1 (by rfl) ⟨1389248, by rfl⟩ : syracuseStep 1852331 = 2778497) B2778497
theorem B1852343 : Blo 1851627 1852343 := bstep (se 1 (by rfl) ⟨1389257, by rfl⟩ : syracuseStep 1852343 = 2778515) B2778515
theorem B3515329 : Blo 1851627 3515329 := bstep (se 2 (by rfl) ⟨1318248, by rfl⟩ : syracuseStep 3515329 = 2636497) B2636497
theorem B6013889 : Blo 1851627 6013889 := bstep (se 2 (by rfl) ⟨2255208, by rfl⟩ : syracuseStep 6013889 = 4510417) B4510417
theorem B2778059 : Blo 1851627 2778059 := bstep (se 1 (by rfl) ⟨2083544, by rfl⟩ : syracuseStep 2778059 = 4167089) B4167089
theorem B1852363 : Blo 1851627 1852363 := bstep (se 1 (by rfl) ⟨1389272, by rfl⟩ : syracuseStep 1852363 = 2778545) B2778545
theorem B3662795 : Blo 1851627 3662795 := bstep (se 1 (by rfl) ⟨2747096, by rfl⟩ : syracuseStep 3662795 = 5494193) B5494193
theorem B2778071 : Blo 1851627 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B1852375 : Blo 1851627 1852375 := bstep (se 1 (by rfl) ⟨1389281, by rfl⟩ : syracuseStep 1852375 = 2778563) B2778563
theorem B1852395 : Blo 1851627 1852395 := bstep (se 1 (by rfl) ⟨1389296, by rfl⟩ : syracuseStep 1852395 = 2778593) B2778593
theorem B1852407 : Blo 1851627 1852407 := bstep (se 1 (by rfl) ⟨1389305, by rfl⟩ : syracuseStep 1852407 = 2778611) B2778611
theorem B1852427 : Blo 1851627 1852427 := bstep (se 1 (by rfl) ⟨1389320, by rfl⟩ : syracuseStep 1852427 = 2778641) B2778641
theorem B5932055 : Blo 1851627 5932055 := bstep (se 1 (by rfl) ⟨4449041, by rfl⟩ : syracuseStep 5932055 = 8898083) B8898083
theorem B1852439 : Blo 1851627 1852439 := bstep (se 1 (by rfl) ⟨1389329, by rfl⟩ : syracuseStep 1852439 = 2778659) B2778659
theorem B2778137 : Blo 1851627 2778137 := bstep (se 2 (by rfl) ⟨1041801, by rfl⟩ : syracuseStep 2778137 = 2083603) B2083603
theorem B1852459 : Blo 1851627 1852459 := bstep (se 1 (by rfl) ⟨1389344, by rfl⟩ : syracuseStep 1852459 = 2778689) B2778689
theorem B1852471 : Blo 1851627 1852471 := bstep (se 1 (by rfl) ⟨1389353, by rfl⟩ : syracuseStep 1852471 = 2778707) B2778707
theorem B1852491 : Blo 1851627 1852491 := bstep (se 1 (by rfl) ⟨1389368, by rfl⟩ : syracuseStep 1852491 = 2778737) B2778737
theorem B1852503 : Blo 1851627 1852503 := bstep (se 1 (by rfl) ⟨1389377, by rfl⟩ : syracuseStep 1852503 = 2778755) B2778755
theorem B5276765 : Blo 1851627 5276765 := bstep (se 3 (by rfl) ⟨989393, by rfl⟩ : syracuseStep 5276765 = 1978787) B1978787
theorem B1852523 : Blo 1851627 1852523 := bstep (se 1 (by rfl) ⟨1389392, by rfl⟩ : syracuseStep 1852523 = 2778785) B2778785
theorem B1852535 : Blo 1851627 1852535 := bstep (se 1 (by rfl) ⟨1389401, by rfl⟩ : syracuseStep 1852535 = 2778803) B2778803
theorem B15025283 : Blo 1851627 15025283 := bstep (se 1 (by rfl) ⟨11268962, by rfl⟩ : syracuseStep 15025283 = 22537925) B22537925
theorem B2778251 : Blo 1851627 2778251 := bstep (se 1 (by rfl) ⟨2083688, by rfl⟩ : syracuseStep 2778251 = 4167377) B4167377
theorem B1852555 : Blo 1851627 1852555 := bstep (se 1 (by rfl) ⟨1389416, by rfl⟩ : syracuseStep 1852555 = 2778833) B2778833
theorem B2778263 : Blo 1851627 2778263 := bstep (se 1 (by rfl) ⟨2083697, by rfl⟩ : syracuseStep 2778263 = 4167395) B4167395
theorem B1852567 : Blo 1851627 1852567 := bstep (se 1 (by rfl) ⟨1389425, by rfl⟩ : syracuseStep 1852567 = 2778851) B2778851
theorem B1852587 : Blo 1851627 1852587 := bstep (se 1 (by rfl) ⟨1389440, by rfl⟩ : syracuseStep 1852587 = 2778881) B2778881
theorem B1852599 : Blo 1851627 1852599 := bstep (se 1 (by rfl) ⟨1389449, by rfl⟩ : syracuseStep 1852599 = 2778899) B2778899
theorem B1852619 : Blo 1851627 1852619 := bstep (se 1 (by rfl) ⟨1389464, by rfl⟩ : syracuseStep 1852619 = 2778929) B2778929
theorem B1852631 : Blo 1851627 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B2778329 : Blo 1851627 2778329 := bstep (se 2 (by rfl) ⟨1041873, by rfl⟩ : syracuseStep 2778329 = 2083747) B2083747
theorem B6251741 : Blo 1851627 6251741 := bstep (se 3 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 6251741 = 2344403) B2344403
theorem B1852651 : Blo 1851627 1852651 := bstep (se 1 (by rfl) ⟨1389488, by rfl⟩ : syracuseStep 1852651 = 2778977) B2778977
theorem B1852663 : Blo 1851627 1852663 := bstep (se 1 (by rfl) ⟨1389497, by rfl⟩ : syracuseStep 1852663 = 2778995) B2778995
theorem B1852683 : Blo 1851627 1852683 := bstep (se 1 (by rfl) ⟨1389512, by rfl⟩ : syracuseStep 1852683 = 2779025) B2779025
theorem B15017233 : Blo 1851627 15017233 := bstep (se 2 (by rfl) ⟨5631462, by rfl⟩ : syracuseStep 15017233 = 11262925) B11262925
theorem B1852695 : Blo 1851627 1852695 := bstep (se 1 (by rfl) ⟨1389521, by rfl⟩ : syracuseStep 1852695 = 2779043) B2779043
theorem B1852715 : Blo 1851627 1852715 := bstep (se 1 (by rfl) ⟨1389536, by rfl⟩ : syracuseStep 1852715 = 2779073) B2779073
theorem B1852727 : Blo 1851627 1852727 := bstep (se 1 (by rfl) ⟨1389545, by rfl⟩ : syracuseStep 1852727 = 2779091) B2779091
theorem B2778443 : Blo 1851627 2778443 := bstep (se 1 (by rfl) ⟨2083832, by rfl⟩ : syracuseStep 2778443 = 4167665) B4167665
theorem B1852747 : Blo 1851627 1852747 := bstep (se 1 (by rfl) ⟨1389560, by rfl⟩ : syracuseStep 1852747 = 2779121) B2779121
theorem B2778455 : Blo 1851627 2778455 := bstep (se 1 (by rfl) ⟨2083841, by rfl⟩ : syracuseStep 2778455 = 4167683) B4167683
theorem B1852759 : Blo 1851627 1852759 := bstep (se 1 (by rfl) ⟨1389569, by rfl⟩ : syracuseStep 1852759 = 2779139) B2779139
theorem B1852779 : Blo 1851627 1852779 := bstep (se 1 (by rfl) ⟨1389584, by rfl⟩ : syracuseStep 1852779 = 2779169) B2779169
theorem B1852791 : Blo 1851627 1852791 := bstep (se 1 (by rfl) ⟨1389593, by rfl⟩ : syracuseStep 1852791 = 2779187) B2779187
theorem B1852811 : Blo 1851627 1852811 := bstep (se 1 (by rfl) ⟨1389608, by rfl⟩ : syracuseStep 1852811 = 2779217) B2779217
theorem B1852823 : Blo 1851627 1852823 := bstep (se 1 (by rfl) ⟨1389617, by rfl⟩ : syracuseStep 1852823 = 2779235) B2779235
theorem B2778521 : Blo 1851627 2778521 := bstep (se 2 (by rfl) ⟨1041945, by rfl⟩ : syracuseStep 2778521 = 2083891) B2083891
theorem B1852843 : Blo 1851627 1852843 := bstep (se 1 (by rfl) ⟨1389632, by rfl⟩ : syracuseStep 1852843 = 2779265) B2779265
theorem B15820211 : Blo 1851627 15820211 := bstep (se 1 (by rfl) ⟨11865158, by rfl⟩ : syracuseStep 15820211 = 23730317) B23730317
theorem B1852855 : Blo 1851627 1852855 := bstep (se 1 (by rfl) ⟨1389641, by rfl⟩ : syracuseStep 1852855 = 2779283) B2779283
theorem B1852875 : Blo 1851627 1852875 := bstep (se 1 (by rfl) ⟨1389656, by rfl⟩ : syracuseStep 1852875 = 2779313) B2779313
theorem B1852887 : Blo 1851627 1852887 := bstep (se 1 (by rfl) ⟨1389665, by rfl⟩ : syracuseStep 1852887 = 2779331) B2779331
theorem B1852907 : Blo 1851627 1852907 := bstep (se 1 (by rfl) ⟨1389680, by rfl⟩ : syracuseStep 1852907 = 2779361) B2779361
theorem B1852919 : Blo 1851627 1852919 := bstep (se 1 (by rfl) ⟨1389689, by rfl⟩ : syracuseStep 1852919 = 2779379) B2779379
theorem B2344459 : Blo 1851627 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B2778635 : Blo 1851627 2778635 := bstep (se 1 (by rfl) ⟨2083976, by rfl⟩ : syracuseStep 2778635 = 4167953) B4167953
theorem B1852939 : Blo 1851627 1852939 := bstep (se 1 (by rfl) ⟨1389704, by rfl⟩ : syracuseStep 1852939 = 2779409) B2779409
theorem B3958283 : Blo 1851627 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B54150673 : Blo 1851627 54150673 := bstep (se 2 (by rfl) ⟨20306502, by rfl⟩ : syracuseStep 54150673 = 40613005) B40613005
theorem B2778647 : Blo 1851627 2778647 := bstep (se 1 (by rfl) ⟨2083985, by rfl⟩ : syracuseStep 2778647 = 4167971) B4167971
theorem B1852951 : Blo 1851627 1852951 := bstep (se 1 (by rfl) ⟨1389713, by rfl⟩ : syracuseStep 1852951 = 2779427) B2779427
theorem B1852971 : Blo 1851627 1852971 := bstep (se 1 (by rfl) ⟨1389728, by rfl⟩ : syracuseStep 1852971 = 2779457) B2779457
theorem B1852983 : Blo 1851627 1852983 := bstep (se 1 (by rfl) ⟨1389737, by rfl⟩ : syracuseStep 1852983 = 2779475) B2779475
theorem B1853003 : Blo 1851627 1853003 := bstep (se 1 (by rfl) ⟨1389752, by rfl⟩ : syracuseStep 1853003 = 2779505) B2779505
theorem B1853015 : Blo 1851627 1853015 := bstep (se 1 (by rfl) ⟨1389761, by rfl⟩ : syracuseStep 1853015 = 2779523) B2779523
theorem B2778713 : Blo 1851627 2778713 := bstep (se 2 (by rfl) ⟨1042017, by rfl⟩ : syracuseStep 2778713 = 2084035) B2084035
theorem B1853035 : Blo 1851627 1853035 := bstep (se 1 (by rfl) ⟨1389776, by rfl⟩ : syracuseStep 1853035 = 2779553) B2779553
theorem B1853047 : Blo 1851627 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B3516043 : Blo 1851627 3516043 := bstep (se 1 (by rfl) ⟨2637032, by rfl⟩ : syracuseStep 3516043 = 5274065) B5274065
theorem B1853067 : Blo 1851627 1853067 := bstep (se 1 (by rfl) ⟨1389800, by rfl⟩ : syracuseStep 1853067 = 2779601) B2779601
theorem B1853079 : Blo 1851627 1853079 := bstep (se 1 (by rfl) ⟨1389809, by rfl⟩ : syracuseStep 1853079 = 2779619) B2779619
theorem B1853099 : Blo 1851627 1853099 := bstep (se 1 (by rfl) ⟨1389824, by rfl⟩ : syracuseStep 1853099 = 2779649) B2779649
theorem B1853111 : Blo 1851627 1853111 := bstep (se 1 (by rfl) ⟨1389833, by rfl⟩ : syracuseStep 1853111 = 2779667) B2779667
theorem B7128769 : Blo 1851627 7128769 := bstep (se 2 (by rfl) ⟨2673288, by rfl⟩ : syracuseStep 7128769 = 5346577) B5346577
theorem B2778827 : Blo 1851627 2778827 := bstep (se 1 (by rfl) ⟨2084120, by rfl⟩ : syracuseStep 2778827 = 4168241) B4168241
theorem B1853131 : Blo 1851627 1853131 := bstep (se 1 (by rfl) ⟨1389848, by rfl⟩ : syracuseStep 1853131 = 2779697) B2779697
theorem B3516119 : Blo 1851627 3516119 := bstep (se 1 (by rfl) ⟨2637089, by rfl⟩ : syracuseStep 3516119 = 5274179) B5274179
theorem B2778839 : Blo 1851627 2778839 := bstep (se 1 (by rfl) ⟨2084129, by rfl⟩ : syracuseStep 2778839 = 4168259) B4168259
theorem B1853143 : Blo 1851627 1853143 := bstep (se 1 (by rfl) ⟨1389857, by rfl⟩ : syracuseStep 1853143 = 2779715) B2779715
theorem B1853163 : Blo 1851627 1853163 := bstep (se 1 (by rfl) ⟨1389872, by rfl⟩ : syracuseStep 1853163 = 2779745) B2779745
theorem B32089841 : Blo 1851627 32089841 := bstep (se 2 (by rfl) ⟨12033690, by rfl⟩ : syracuseStep 32089841 = 24067381) B24067381
theorem B1853175 : Blo 1851627 1853175 := bstep (se 1 (by rfl) ⟨1389881, by rfl⟩ : syracuseStep 1853175 = 2779763) B2779763
theorem B1853195 : Blo 1851627 1853195 := bstep (se 1 (by rfl) ⟨1389896, by rfl⟩ : syracuseStep 1853195 = 2779793) B2779793
theorem B2344727 : Blo 1851627 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B1853207 : Blo 1851627 1853207 := bstep (se 1 (by rfl) ⟨1389905, by rfl⟩ : syracuseStep 1853207 = 2779811) B2779811
theorem B2778905 : Blo 1851627 2778905 := bstep (se 2 (by rfl) ⟨1042089, by rfl⟩ : syracuseStep 2778905 = 2084179) B2084179
theorem B1853227 : Blo 1851627 1853227 := bstep (se 1 (by rfl) ⟨1389920, by rfl⟩ : syracuseStep 1853227 = 2779841) B2779841
theorem B1853239 : Blo 1851627 1853239 := bstep (se 1 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 1853239 = 2779859) B2779859
theorem B1853259 : Blo 1851627 1853259 := bstep (se 1 (by rfl) ⟨1389944, by rfl⟩ : syracuseStep 1853259 = 2779889) B2779889
theorem B1853271 : Blo 1851627 1853271 := bstep (se 1 (by rfl) ⟨1389953, by rfl⟩ : syracuseStep 1853271 = 2779907) B2779907
theorem B25692005 : Blo 1851627 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B1853291 : Blo 1851627 1853291 := bstep (se 1 (by rfl) ⟨1389968, by rfl⟩ : syracuseStep 1853291 = 2779937) B2779937
theorem B1853303 : Blo 1851627 1853303 := bstep (se 1 (by rfl) ⟨1389977, by rfl⟩ : syracuseStep 1853303 = 2779955) B2779955
theorem B2779019 : Blo 1851627 2779019 := bstep (se 1 (by rfl) ⟨2084264, by rfl⟩ : syracuseStep 2779019 = 4168529) B4168529
theorem B1853323 : Blo 1851627 1853323 := bstep (se 1 (by rfl) ⟨1389992, by rfl⟩ : syracuseStep 1853323 = 2779985) B2779985
theorem B2779031 : Blo 1851627 2779031 := bstep (se 1 (by rfl) ⟨2084273, by rfl⟩ : syracuseStep 2779031 = 4168547) B4168547
theorem B1853335 : Blo 1851627 1853335 := bstep (se 1 (by rfl) ⟨1390001, by rfl⟩ : syracuseStep 1853335 = 2780003) B2780003
theorem B1853355 : Blo 1851627 1853355 := bstep (se 1 (by rfl) ⟨1390016, by rfl⟩ : syracuseStep 1853355 = 2780033) B2780033
theorem B1853367 : Blo 1851627 1853367 := bstep (se 1 (by rfl) ⟨1390025, by rfl⟩ : syracuseStep 1853367 = 2780051) B2780051
theorem B1853387 : Blo 1851627 1853387 := bstep (se 1 (by rfl) ⟨1390040, by rfl⟩ : syracuseStep 1853387 = 2780081) B2780081
theorem B1853399 : Blo 1851627 1853399 := bstep (se 1 (by rfl) ⟨1390049, by rfl⟩ : syracuseStep 1853399 = 2780099) B2780099
theorem B2779097 : Blo 1851627 2779097 := bstep (se 2 (by rfl) ⟨1042161, by rfl⟩ : syracuseStep 2779097 = 2084323) B2084323
theorem B1853419 : Blo 1851627 1853419 := bstep (se 1 (by rfl) ⟨1390064, by rfl⟩ : syracuseStep 1853419 = 2780129) B2780129
theorem B1853431 : Blo 1851627 1853431 := bstep (se 1 (by rfl) ⟨1390073, by rfl⟩ : syracuseStep 1853431 = 2780147) B2780147
theorem B1853451 : Blo 1851627 1853451 := bstep (se 1 (by rfl) ⟨1390088, by rfl⟩ : syracuseStep 1853451 = 2780177) B2780177
theorem B9381905 : Blo 1851627 9381905 := bstep (se 2 (by rfl) ⟨3518214, by rfl⟩ : syracuseStep 9381905 = 7036429) B7036429
theorem B4687895 : Blo 1851627 4687895 := bstep (se 1 (by rfl) ⟨3515921, by rfl⟩ : syracuseStep 4687895 = 7031843) B7031843
theorem B1853463 : Blo 1851627 1853463 := bstep (se 1 (by rfl) ⟨1390097, by rfl⟩ : syracuseStep 1853463 = 2780195) B2780195
theorem B1853483 : Blo 1851627 1853483 := bstep (se 1 (by rfl) ⟨1390112, by rfl⟩ : syracuseStep 1853483 = 2780225) B2780225
theorem B6268979 : Blo 1851627 6268979 := bstep (se 1 (by rfl) ⟨4701734, by rfl⟩ : syracuseStep 6268979 = 9403469) B9403469
theorem B1853495 : Blo 1851627 1853495 := bstep (se 1 (by rfl) ⟨1390121, by rfl⟩ : syracuseStep 1853495 = 2780243) B2780243
theorem B3565633 : Blo 1851627 3565633 := bstep (se 2 (by rfl) ⟨1337112, by rfl⟩ : syracuseStep 3565633 = 2674225) B2674225
theorem B2779211 : Blo 1851627 2779211 := bstep (se 1 (by rfl) ⟨2084408, by rfl⟩ : syracuseStep 2779211 = 4168817) B4168817
theorem B1853515 : Blo 1851627 1853515 := bstep (se 1 (by rfl) ⟨1390136, by rfl⟩ : syracuseStep 1853515 = 2780273) B2780273
theorem B2779223 : Blo 1851627 2779223 := bstep (se 1 (by rfl) ⟨2084417, by rfl⟩ : syracuseStep 2779223 = 4168835) B4168835
theorem B1853527 : Blo 1851627 1853527 := bstep (se 1 (by rfl) ⟨1390145, by rfl⟩ : syracuseStep 1853527 = 2780291) B2780291
theorem B1853547 : Blo 1851627 1853547 := bstep (se 1 (by rfl) ⟨1390160, by rfl⟩ : syracuseStep 1853547 = 2780321) B2780321
theorem B1853559 : Blo 1851627 1853559 := bstep (se 1 (by rfl) ⟨1390169, by rfl⟩ : syracuseStep 1853559 = 2780339) B2780339
theorem B1853579 : Blo 1851627 1853579 := bstep (se 1 (by rfl) ⟨1390184, by rfl⟩ : syracuseStep 1853579 = 2780369) B2780369
theorem B4753559 : Blo 1851627 4753559 := bstep (se 1 (by rfl) ⟨3565169, by rfl⟩ : syracuseStep 4753559 = 7130339) B7130339
theorem B1853591 : Blo 1851627 1853591 := bstep (se 1 (by rfl) ⟨1390193, by rfl⟩ : syracuseStep 1853591 = 2780387) B2780387
theorem B2779289 : Blo 1851627 2779289 := bstep (se 2 (by rfl) ⟨1042233, by rfl⟩ : syracuseStep 2779289 = 2084467) B2084467
theorem B1853611 : Blo 1851627 1853611 := bstep (se 1 (by rfl) ⟨1390208, by rfl⟩ : syracuseStep 1853611 = 2780417) B2780417
theorem B9382067 : Blo 1851627 9382067 := bstep (se 1 (by rfl) ⟨7036550, by rfl⟩ : syracuseStep 9382067 = 14073101) B14073101
theorem B1853623 : Blo 1851627 1853623 := bstep (se 1 (by rfl) ⟨1390217, by rfl⟩ : syracuseStep 1853623 = 2780435) B2780435
theorem B13355225 : Blo 1851627 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B2779403 : Blo 1851627 2779403 := bstep (se 1 (by rfl) ⟨2084552, by rfl⟩ : syracuseStep 2779403 = 4169105) B4169105
theorem B2779415 : Blo 1851627 2779415 := bstep (se 1 (by rfl) ⟨2084561, by rfl⟩ : syracuseStep 2779415 = 4169123) B4169123
theorem B6252875 : Blo 1851627 6252875 := bstep (se 1 (by rfl) ⟨4689656, by rfl⟩ : syracuseStep 6252875 = 9379313) B9379313
theorem B2779481 : Blo 1851627 2779481 := bstep (se 2 (by rfl) ⟨1042305, by rfl⟩ : syracuseStep 2779481 = 2084611) B2084611
theorem B3516787 : Blo 1851627 3516787 := bstep (se 1 (by rfl) ⟨2637590, by rfl⟩ : syracuseStep 3516787 = 5275181) B5275181
theorem B2083243 : Blo 1851627 2083243 := bstep (se 1 (by rfl) ⟨1562432, by rfl⟩ : syracuseStep 2083243 = 3124865) B3124865
theorem B2779595 : Blo 1851627 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B2779607 : Blo 1851627 2779607 := bstep (se 1 (by rfl) ⟨2084705, by rfl⟩ : syracuseStep 2779607 = 4169411) B4169411
theorem B2345431 : Blo 1851627 2345431 := bstep (se 1 (by rfl) ⟨1759073, by rfl⟩ : syracuseStep 2345431 = 3518147) B3518147
theorem B14068241 : Blo 1851627 14068241 := bstep (se 2 (by rfl) ⟨5275590, by rfl⟩ : syracuseStep 14068241 = 10551181) B10551181
theorem B2083351 : Blo 1851627 2083351 := bstep (se 1 (by rfl) ⟨1562513, by rfl⟩ : syracuseStep 2083351 = 3125027) B3125027
theorem B2779673 : Blo 1851627 2779673 := bstep (se 2 (by rfl) ⟨1042377, by rfl⟩ : syracuseStep 2779673 = 2084755) B2084755
theorem B3517015 : Blo 1851627 3517015 := bstep (se 1 (by rfl) ⟨2637761, by rfl⟩ : syracuseStep 3517015 = 5275523) B5275523
theorem B6253145 : Blo 1851627 6253145 := bstep (se 2 (by rfl) ⟨2344929, by rfl⟩ : syracuseStep 6253145 = 4689859) B4689859
theorem B2779787 : Blo 1851627 2779787 := bstep (se 1 (by rfl) ⟨2084840, by rfl⟩ : syracuseStep 2779787 = 4169681) B4169681
theorem B2779799 : Blo 1851627 2779799 := bstep (se 1 (by rfl) ⟨2084849, by rfl⟩ : syracuseStep 2779799 = 4169699) B4169699
theorem B4688563 : Blo 1851627 4688563 := bstep (se 1 (by rfl) ⟨3516422, by rfl⟩ : syracuseStep 4688563 = 7032845) B7032845
theorem B3517121 : Blo 1851627 3517121 := bstep (se 2 (by rfl) ⟨1318920, by rfl⟩ : syracuseStep 3517121 = 2637841) B2637841
theorem B2083531 : Blo 1851627 2083531 := bstep (se 1 (by rfl) ⟨1562648, by rfl⟩ : syracuseStep 2083531 = 3125297) B3125297
theorem B32082637 : Blo 1851627 32082637 := bstep (se 3 (by rfl) ⟨6015494, by rfl⟩ : syracuseStep 32082637 = 12030989) B12030989
theorem B2779865 : Blo 1851627 2779865 := bstep (se 2 (by rfl) ⟨1042449, by rfl⟩ : syracuseStep 2779865 = 2084899) B2084899
theorem B7031555 : Blo 1851627 7031555 := bstep (se 1 (by rfl) ⟨5273666, by rfl⟩ : syracuseStep 7031555 = 10547333) B10547333
theorem B7031569 : Blo 1851627 7031569 := bstep (se 2 (by rfl) ⟨2636838, by rfl⟩ : syracuseStep 7031569 = 5273677) B5273677
theorem B2083639 : Blo 1851627 2083639 := bstep (se 1 (by rfl) ⟨1562729, by rfl⟩ : syracuseStep 2083639 = 3125459) B3125459
theorem B4688705 : Blo 1851627 4688705 := bstep (se 2 (by rfl) ⟨1758264, by rfl⟩ : syracuseStep 4688705 = 3516529) B3516529
theorem B2779979 : Blo 1851627 2779979 := bstep (se 1 (by rfl) ⟨2084984, by rfl⟩ : syracuseStep 2779979 = 4169969) B4169969
theorem B2779991 : Blo 1851627 2779991 := bstep (se 1 (by rfl) ⟨2084993, by rfl⟩ : syracuseStep 2779991 = 4169987) B4169987
theorem B3517273 : Blo 1851627 3517273 := bstep (se 2 (by rfl) ⟨1318977, by rfl⟩ : syracuseStep 3517273 = 2637955) B2637955
theorem B11873155 : Blo 1851627 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B9374615 : Blo 1851627 9374615 := bstep (se 1 (by rfl) ⟨7030961, by rfl⟩ : syracuseStep 9374615 = 14061923) B14061923
theorem B2780057 : Blo 1851627 2780057 := bstep (se 2 (by rfl) ⟨1042521, by rfl⟩ : syracuseStep 2780057 = 2085043) B2085043
theorem B2083819 : Blo 1851627 2083819 := bstep (se 1 (by rfl) ⟨1562864, by rfl⟩ : syracuseStep 2083819 = 3125729) B3125729
theorem B2780171 : Blo 1851627 2780171 := bstep (se 1 (by rfl) ⟨2085128, by rfl⟩ : syracuseStep 2780171 = 4170257) B4170257
theorem B25685009 : Blo 1851627 25685009 := bstep (se 2 (by rfl) ⟨9631878, by rfl⟩ : syracuseStep 25685009 = 19263757) B19263757
theorem B2780183 : Blo 1851627 2780183 := bstep (se 1 (by rfl) ⟨2085137, by rfl⟩ : syracuseStep 2780183 = 4170275) B4170275
theorem B7031873 : Blo 1851627 7031873 := bstep (se 2 (by rfl) ⟨2636952, by rfl⟩ : syracuseStep 7031873 = 5273905) B5273905
theorem B2083927 : Blo 1851627 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B2780249 : Blo 1851627 2780249 := bstep (se 2 (by rfl) ⟨1042593, by rfl⟩ : syracuseStep 2780249 = 2085187) B2085187
theorem B10546307 : Blo 1851627 10546307 := bstep (se 1 (by rfl) ⟨7909730, by rfl⟩ : syracuseStep 10546307 = 15819461) B15819461
theorem B4885697 : Blo 1851627 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B2780363 : Blo 1851627 2780363 := bstep (se 1 (by rfl) ⟨2085272, by rfl⟩ : syracuseStep 2780363 = 4170545) B4170545
theorem B2780375 : Blo 1851627 2780375 := bstep (se 1 (by rfl) ⟨2085281, by rfl⟩ : syracuseStep 2780375 = 4170563) B4170563
theorem B2084107 : Blo 1851627 2084107 := bstep (se 1 (by rfl) ⟨1563080, by rfl⟩ : syracuseStep 2084107 = 3126161) B3126161
theorem B6253847 : Blo 1851627 6253847 := bstep (se 1 (by rfl) ⟨4690385, by rfl⟩ : syracuseStep 6253847 = 9380771) B9380771
theorem B2780441 : Blo 1851627 2780441 := bstep (se 2 (by rfl) ⟨1042665, by rfl⟩ : syracuseStep 2780441 = 2085331) B2085331
theorem B15822125 : Blo 1851627 15822125 := bstep (se 3 (by rfl) ⟨2966648, by rfl⟩ : syracuseStep 15822125 = 5933297) B5933297
theorem B26717485 : Blo 1851627 26717485 := bstep (se 3 (by rfl) ⟨5009528, by rfl⟩ : syracuseStep 26717485 = 10019057) B10019057
theorem B3755315 : Blo 1851627 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2084215 : Blo 1851627 2084215 := bstep (se 1 (by rfl) ⟨1563161, by rfl⟩ : syracuseStep 2084215 = 3126323) B3126323
theorem B15232387 : Blo 1851627 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B14060951 : Blo 1851627 14060951 := bstep (se 1 (by rfl) ⟨10545713, by rfl⟩ : syracuseStep 14060951 = 21091427) B21091427
theorem B2674201 : Blo 1851627 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B2084395 : Blo 1851627 2084395 := bstep (se 1 (by rfl) ⟨1563296, by rfl⟩ : syracuseStep 2084395 = 3126593) B3126593
theorem B8449601 : Blo 1851627 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B3124811 : Blo 1851627 3124811 := bstep (se 1 (by rfl) ⟨2343608, by rfl⟩ : syracuseStep 3124811 = 4687217) B4687217
theorem B2084503 : Blo 1851627 2084503 := bstep (se 1 (by rfl) ⟨1563377, by rfl⟩ : syracuseStep 2084503 = 3126755) B3126755
theorem B1978039 : Blo 1851627 1978039 := bstep (se 1 (by rfl) ⟨1483529, by rfl⟩ : syracuseStep 1978039 = 2967059) B2967059
theorem B8023745 : Blo 1851627 8023745 := bstep (se 2 (by rfl) ⟨3008904, by rfl⟩ : syracuseStep 8023745 = 6017809) B6017809
theorem B3124939 : Blo 1851627 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B7032541 : Blo 1851627 7032541 := bstep (se 3 (by rfl) ⟨1318601, by rfl⟩ : syracuseStep 7032541 = 2637203) B2637203
theorem B6680323 : Blo 1851627 6680323 := bstep (se 1 (by rfl) ⟨5010242, by rfl⟩ : syracuseStep 6680323 = 10020485) B10020485
theorem B7917335 : Blo 1851627 7917335 := bstep (se 1 (by rfl) ⟨5938001, by rfl⟩ : syracuseStep 7917335 = 11876003) B11876003
theorem B6254387 : Blo 1851627 6254387 := bstep (se 1 (by rfl) ⟨4690790, by rfl⟩ : syracuseStep 6254387 = 9381581) B9381581
theorem B2084683 : Blo 1851627 2084683 := bstep (se 1 (by rfl) ⟨1563512, by rfl⟩ : syracuseStep 2084683 = 3127025) B3127025
theorem B3125081 : Blo 1851627 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B25341797 : Blo 1851627 25341797 := bstep (se 4 (by rfl) ⟨2375793, by rfl⟩ : syracuseStep 25341797 = 4751587) B4751587
theorem B1978219 : Blo 1851627 1978219 := bstep (se 1 (by rfl) ⟨1483664, by rfl⟩ : syracuseStep 1978219 = 2967329) B2967329
theorem B7909271 : Blo 1851627 7909271 := bstep (se 1 (by rfl) ⟨5931953, by rfl⟩ : syracuseStep 7909271 = 11863907) B11863907
theorem B2084791 : Blo 1851627 2084791 := bstep (se 1 (by rfl) ⟨1563593, by rfl⟩ : syracuseStep 2084791 = 3127187) B3127187
theorem B3125209 : Blo 1851627 3125209 := bstep (se 2 (by rfl) ⟨1171953, by rfl⟩ : syracuseStep 3125209 = 2343907) B2343907
theorem B15822809 : Blo 1851627 15822809 := bstep (se 2 (by rfl) ⟨5933553, by rfl⟩ : syracuseStep 15822809 = 11867107) B11867107
theorem B4689971 : Blo 1851627 4689971 := bstep (se 1 (by rfl) ⟨3517478, by rfl⟩ : syracuseStep 4689971 = 7034957) B7034957
theorem B5935169 : Blo 1851627 5935169 := bstep (se 2 (by rfl) ⟨2225688, by rfl⟩ : syracuseStep 5935169 = 4451377) B4451377
theorem B6254657 : Blo 1851627 6254657 := bstep (se 2 (by rfl) ⟨2345496, by rfl⟩ : syracuseStep 6254657 = 4690993) B4690993
theorem B4755521 : Blo 1851627 4755521 := bstep (se 2 (by rfl) ⟨1783320, by rfl⟩ : syracuseStep 4755521 = 3566641) B3566641
theorem B2084971 : Blo 1851627 2084971 := bstep (se 1 (by rfl) ⟨1563728, by rfl⟩ : syracuseStep 2084971 = 3127457) B3127457
theorem B3518579 : Blo 1851627 3518579 := bstep (se 1 (by rfl) ⟨2638934, by rfl⟩ : syracuseStep 3518579 = 5277869) B5277869
theorem B5075137 : Blo 1851627 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B2085079 : Blo 1851627 2085079 := bstep (se 1 (by rfl) ⟨1563809, by rfl⟩ : syracuseStep 2085079 = 3127619) B3127619
theorem B3518731 : Blo 1851627 3518731 := bstep (se 1 (by rfl) ⟨2639048, by rfl⟩ : syracuseStep 3518731 = 5278097) B5278097
theorem B2085259 : Blo 1851627 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B15831557 : Blo 1851627 15831557 := bstep (se 4 (by rfl) ⟨1484208, by rfl⟩ : syracuseStep 15831557 = 2968417) B2968417
theorem B64139789 : Blo 1851627 64139789 := bstep (se 3 (by rfl) ⟨12026210, by rfl⟩ : syracuseStep 64139789 = 24052421) B24052421
theorem B3125783 : Blo 1851627 3125783 := bstep (se 1 (by rfl) ⟨2344337, by rfl⟩ : syracuseStep 3125783 = 4688675) B4688675
theorem B4452887 : Blo 1851627 4452887 := bstep (se 1 (by rfl) ⟨3339665, by rfl⟩ : syracuseStep 4452887 = 6679331) B6679331
theorem B4690507 : Blo 1851627 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B6255197 : Blo 1851627 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B3125911 : Blo 1851627 3125911 := bstep (se 1 (by rfl) ⟨2344433, by rfl⟩ : syracuseStep 3125911 = 4688867) B4688867
theorem B4166297 : Blo 1851627 4166297 := bstep (se 2 (by rfl) ⟨1562361, by rfl⟩ : syracuseStep 4166297 = 3124723) B3124723
theorem B5010113 : Blo 1851627 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B4690649 : Blo 1851627 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B5010137 : Blo 1851627 5010137 := bstep (se 2 (by rfl) ⟨1878801, by rfl⟩ : syracuseStep 5010137 = 3757603) B3757603
theorem B4166387 : Blo 1851627 4166387 := bstep (se 1 (by rfl) ⟨3124790, by rfl⟩ : syracuseStep 4166387 = 6249581) B6249581
theorem B3338995 : Blo 1851627 3338995 := bstep (se 1 (by rfl) ⟨2504246, by rfl⟩ : syracuseStep 3338995 = 5008493) B5008493
theorem B4166423 : Blo 1851627 4166423 := bstep (se 1 (by rfl) ⟨3124817, by rfl⟩ : syracuseStep 4166423 = 6249635) B6249635
theorem B2503499 : Blo 1851627 2503499 := bstep (se 1 (by rfl) ⟨1877624, by rfl⟩ : syracuseStep 2503499 = 3755249) B3755249
theorem B6017885 : Blo 1851627 6017885 := bstep (se 3 (by rfl) ⟨1128353, by rfl⟩ : syracuseStep 6017885 = 2256707) B2256707
theorem B16896869 : Blo 1851627 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B4166603 : Blo 1851627 4166603 := bstep (se 1 (by rfl) ⟨3124952, by rfl⟩ : syracuseStep 4166603 = 6249905) B6249905
theorem B7033817 : Blo 1851627 7033817 := bstep (se 2 (by rfl) ⟨2637681, by rfl⟩ : syracuseStep 7033817 = 5275363) B5275363
theorem B9024473 : Blo 1851627 9024473 := bstep (se 2 (by rfl) ⟨3384177, by rfl⟩ : syracuseStep 9024473 = 6768355) B6768355
theorem B4166657 : Blo 1851627 4166657 := bstep (se 2 (by rfl) ⟨1562496, by rfl⟩ : syracuseStep 4166657 = 3124993) B3124993
theorem B13349893 : Blo 1851627 13349893 := bstep (se 4 (by rfl) ⟨1251552, by rfl⟩ : syracuseStep 13349893 = 2503105) B2503105
theorem B20313163 : Blo 1851627 20313163 := bstep (se 1 (by rfl) ⟨15234872, by rfl⟩ : syracuseStep 20313163 = 30469745) B30469745
theorem B21394525 : Blo 1851627 21394525 := bstep (se 3 (by rfl) ⟨4011473, by rfl⟩ : syracuseStep 21394525 = 8022947) B8022947
theorem B3757195 : Blo 1851627 3757195 := bstep (se 1 (by rfl) ⟨2817896, by rfl⟩ : syracuseStep 3757195 = 5635793) B5635793
theorem B6337739 : Blo 1851627 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B4166873 : Blo 1851627 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B50730245 : Blo 1851627 50730245 := bstep (se 4 (by rfl) ⟨4755960, by rfl⟩ : syracuseStep 50730245 = 9511921) B9511921
theorem B3126539 : Blo 1851627 3126539 := bstep (se 1 (by rfl) ⟨2344904, by rfl⟩ : syracuseStep 3126539 = 4689809) B4689809
theorem B4166963 : Blo 1851627 4166963 := bstep (se 1 (by rfl) ⟨3125222, by rfl⟩ : syracuseStep 4166963 = 6250445) B6250445
theorem B4166999 : Blo 1851627 4166999 := bstep (se 1 (by rfl) ⟨3125249, by rfl⟩ : syracuseStep 4166999 = 6250499) B6250499
theorem B3126667 : Blo 1851627 3126667 := bstep (se 1 (by rfl) ⟨2345000, by rfl⟩ : syracuseStep 3126667 = 4690001) B4690001
theorem B5633459 : Blo 1851627 5633459 := bstep (se 1 (by rfl) ⟨4225094, by rfl⟩ : syracuseStep 5633459 = 8450189) B8450189
theorem B3429875 : Blo 1851627 3429875 := bstep (se 1 (by rfl) ⟨2572406, by rfl⟩ : syracuseStep 3429875 = 5144813) B5144813
theorem B4167179 : Blo 1851627 4167179 := bstep (se 1 (by rfl) ⟨3125384, by rfl⟩ : syracuseStep 4167179 = 6250769) B6250769
theorem B3339787 : Blo 1851627 3339787 := bstep (se 1 (by rfl) ⟨2504840, by rfl⟩ : syracuseStep 3339787 = 5009681) B5009681
theorem B4691479 : Blo 1851627 4691479 := bstep (se 1 (by rfl) ⟨3518609, by rfl⟩ : syracuseStep 4691479 = 7037219) B7037219
theorem B3126809 : Blo 1851627 3126809 := bstep (se 2 (by rfl) ⟨1172553, by rfl⟩ : syracuseStep 3126809 = 2345107) B2345107
theorem B4167233 : Blo 1851627 4167233 := bstep (se 2 (by rfl) ⟨1562712, by rfl⟩ : syracuseStep 4167233 = 3125425) B3125425
theorem B3126937 : Blo 1851627 3126937 := bstep (se 2 (by rfl) ⟨1172601, by rfl⟩ : syracuseStep 3126937 = 2345203) B2345203
theorem B4167449 : Blo 1851627 4167449 := bstep (se 2 (by rfl) ⟨1562793, by rfl⟩ : syracuseStep 4167449 = 3125587) B3125587
theorem B4167539 : Blo 1851627 4167539 := bstep (se 1 (by rfl) ⟨3125654, by rfl⟩ : syracuseStep 4167539 = 6251309) B6251309
theorem B5273495 : Blo 1851627 5273495 := bstep (se 1 (by rfl) ⟨3955121, by rfl⟩ : syracuseStep 5273495 = 7910243) B7910243
theorem B4167575 : Blo 1851627 4167575 := bstep (se 1 (by rfl) ⟨3125681, by rfl⟩ : syracuseStep 4167575 = 6251363) B6251363
theorem B2815897 : Blo 1851627 2815897 := bstep (se 2 (by rfl) ⟨1055961, by rfl⟩ : syracuseStep 2815897 = 2111923) B2111923
theorem B7911371 : Blo 1851627 7911371 := bstep (se 1 (by rfl) ⟨5933528, by rfl⟩ : syracuseStep 7911371 = 11867057) B11867057
theorem B4691915 : Blo 1851627 4691915 := bstep (se 1 (by rfl) ⟨3518936, by rfl⟩ : syracuseStep 4691915 = 7037873) B7037873
theorem B4167755 : Blo 1851627 4167755 := bstep (se 1 (by rfl) ⟨3125816, by rfl⟩ : syracuseStep 4167755 = 6251633) B6251633
theorem B5937245 : Blo 1851627 5937245 := bstep (se 3 (by rfl) ⟨1113233, by rfl⟩ : syracuseStep 5937245 = 2226467) B2226467
theorem B4167809 : Blo 1851627 4167809 := bstep (se 2 (by rfl) ⟨1562928, by rfl⟩ : syracuseStep 4167809 = 3125857) B3125857
theorem B3127511 : Blo 1851627 3127511 := bstep (se 1 (by rfl) ⟨2345633, by rfl⟩ : syracuseStep 3127511 = 4691267) B4691267
theorem B14072129 : Blo 1851627 14072129 := bstep (se 2 (by rfl) ⟨5277048, by rfl⟩ : syracuseStep 14072129 = 10554097) B10554097
theorem B3127639 : Blo 1851627 3127639 := bstep (se 1 (by rfl) ⟨2345729, by rfl⟩ : syracuseStep 3127639 = 4691459) B4691459
theorem B4168025 : Blo 1851627 4168025 := bstep (se 2 (by rfl) ⟨1563009, by rfl⟩ : syracuseStep 4168025 = 3126019) B3126019
theorem B9378179 : Blo 1851627 9378179 := bstep (se 1 (by rfl) ⟨7033634, by rfl⟩ : syracuseStep 9378179 = 14067269) B14067269
theorem B4168115 : Blo 1851627 4168115 := bstep (se 1 (by rfl) ⟨3126086, by rfl⟩ : syracuseStep 4168115 = 6252173) B6252173
theorem B4168151 : Blo 1851627 4168151 := bstep (se 1 (by rfl) ⟨3126113, by rfl⟩ : syracuseStep 4168151 = 6252227) B6252227
theorem B7035443 : Blo 1851627 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B5634625 : Blo 1851627 5634625 := bstep (se 2 (by rfl) ⟨2112984, by rfl⟩ : syracuseStep 5634625 = 4225969) B4225969
theorem B7035457 : Blo 1851627 7035457 := bstep (se 2 (by rfl) ⟨2638296, by rfl⟩ : syracuseStep 7035457 = 5276593) B5276593
theorem B4168331 : Blo 1851627 4168331 := bstep (se 1 (by rfl) ⟨3126248, by rfl⟩ : syracuseStep 4168331 = 6252497) B6252497
theorem B5274305 : Blo 1851627 5274305 := bstep (se 2 (by rfl) ⟨1977864, by rfl⟩ : syracuseStep 5274305 = 3955729) B3955729
theorem B4168385 : Blo 1851627 4168385 := bstep (se 2 (by rfl) ⟨1563144, by rfl⟩ : syracuseStep 4168385 = 3126289) B3126289
theorem B2112215 : Blo 1851627 2112215 := bstep (se 1 (by rfl) ⟨1584161, by rfl⟩ : syracuseStep 2112215 = 3168323) B3168323
theorem B4168601 : Blo 1851627 4168601 := bstep (se 2 (by rfl) ⟨1563225, by rfl⟩ : syracuseStep 4168601 = 3126451) B3126451
theorem B6249419 : Blo 1851627 6249419 := bstep (se 1 (by rfl) ⟨4687064, by rfl⟩ : syracuseStep 6249419 = 9374129) B9374129
theorem B2636759 : Blo 1851627 2636759 := bstep (se 1 (by rfl) ⟨1977569, by rfl⟩ : syracuseStep 2636759 = 3955139) B3955139
theorem B4168691 : Blo 1851627 4168691 := bstep (se 1 (by rfl) ⟨3126518, by rfl⟩ : syracuseStep 4168691 = 6253037) B6253037
theorem B4168727 : Blo 1851627 4168727 := bstep (se 1 (by rfl) ⟨3126545, by rfl⟩ : syracuseStep 4168727 = 6253091) B6253091
theorem B3955891 : Blo 1851627 3955891 := bstep (se 1 (by rfl) ⟨2966918, by rfl⟩ : syracuseStep 3955891 = 5933837) B5933837
theorem B8019137 : Blo 1851627 8019137 := bstep (se 2 (by rfl) ⟨3007176, by rfl⟩ : syracuseStep 8019137 = 6014353) B6014353
theorem B4168907 : Blo 1851627 4168907 := bstep (se 1 (by rfl) ⟨3126680, by rfl⟩ : syracuseStep 4168907 = 6253361) B6253361
theorem B6249689 : Blo 1851627 6249689 := bstep (se 2 (by rfl) ⟨2343633, by rfl⟩ : syracuseStep 6249689 = 4687267) B4687267
theorem B4168961 : Blo 1851627 4168961 := bstep (se 2 (by rfl) ⟨1563360, by rfl⟩ : syracuseStep 4168961 = 3126721) B3126721
theorem B4226327 : Blo 1851627 4226327 := bstep (se 1 (by rfl) ⟨3169745, by rfl⟩ : syracuseStep 4226327 = 6339491) B6339491
theorem B23739749 : Blo 1851627 23739749 := bstep (se 4 (by rfl) ⟨2225601, by rfl⟩ : syracuseStep 23739749 = 4451203) B4451203
theorem B13360589 : Blo 1851627 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B4169177 : Blo 1851627 4169177 := bstep (se 2 (by rfl) ⟨1563441, by rfl⟩ : syracuseStep 4169177 = 3126883) B3126883
theorem B24731153 : Blo 1851627 24731153 := bstep (se 2 (by rfl) ⟨9274182, by rfl⟩ : syracuseStep 24731153 = 18548365) B18548365
theorem B3956249 : Blo 1851627 3956249 := bstep (se 2 (by rfl) ⟨1483593, by rfl⟩ : syracuseStep 3956249 = 2967187) B2967187
theorem B7913011 : Blo 1851627 7913011 := bstep (se 1 (by rfl) ⟨5934758, by rfl⟩ : syracuseStep 7913011 = 11869517) B11869517
theorem B4169267 : Blo 1851627 4169267 := bstep (se 1 (by rfl) ⟨3126950, by rfl⟩ : syracuseStep 4169267 = 6253901) B6253901
theorem B4169303 : Blo 1851627 4169303 := bstep (se 1 (by rfl) ⟨3126977, by rfl⟩ : syracuseStep 4169303 = 6253955) B6253955
theorem B4169483 : Blo 1851627 4169483 := bstep (se 1 (by rfl) ⟨3127112, by rfl⟩ : syracuseStep 4169483 = 6254225) B6254225
theorem B4169537 : Blo 1851627 4169537 := bstep (se 2 (by rfl) ⟨1563576, by rfl⟩ : syracuseStep 4169537 = 3127153) B3127153
theorem B10149725 : Blo 1851627 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B15834973 : Blo 1851627 15834973 := bstep (se 3 (by rfl) ⟨2969057, by rfl⟩ : syracuseStep 15834973 = 5938115) B5938115
theorem B6250391 : Blo 1851627 6250391 := bstep (se 1 (by rfl) ⟨4687793, by rfl⟩ : syracuseStep 6250391 = 9375587) B9375587
theorem B8904599 : Blo 1851627 8904599 := bstep (se 1 (by rfl) ⟨6678449, by rfl⟩ : syracuseStep 8904599 = 13356899) B13356899
theorem B3956779 : Blo 1851627 3956779 := bstep (se 1 (by rfl) ⟨2967584, by rfl⟩ : syracuseStep 3956779 = 5935169) B5935169
theorem B4169771 : Blo 1851627 4169771 := bstep (se 1 (by rfl) ⟨3127328, by rfl⟩ : syracuseStep 4169771 = 6254657) B6254657
theorem B3170347 : Blo 1851627 3170347 := bstep (se 1 (by rfl) ⟨2377760, by rfl⟩ : syracuseStep 3170347 = 4755521) B4755521
theorem B15818813 : Blo 1851627 15818813 := bstep (se 3 (by rfl) ⟨2966027, by rfl⟩ : syracuseStep 15818813 = 5932055) B5932055
theorem B5275763 : Blo 1851627 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B6766849 : Blo 1851627 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B1851655 : Blo 1851627 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B1851663 : Blo 1851627 1851663 := bstep (se 1 (by rfl) ⟨1388747, by rfl⟩ : syracuseStep 1851663 = 2777495) B2777495
theorem B1851707 : Blo 1851627 1851707 := bstep (se 1 (by rfl) ⟨1388780, by rfl⟩ : syracuseStep 1851707 = 2777561) B2777561
theorem B1851783 : Blo 1851627 1851783 := bstep (se 1 (by rfl) ⟨1388837, by rfl⟩ : syracuseStep 1851783 = 2777675) B2777675
theorem B1851791 : Blo 1851627 1851791 := bstep (se 1 (by rfl) ⟨1388843, by rfl⟩ : syracuseStep 1851791 = 2777687) B2777687
theorem B4170131 : Blo 1851627 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B2777531 : Blo 1851627 2777531 := bstep (se 1 (by rfl) ⟨2083148, by rfl⟩ : syracuseStep 2777531 = 4166297) B4166297
theorem B1851835 : Blo 1851627 1851835 := bstep (se 1 (by rfl) ⟨1388876, by rfl⟩ : syracuseStep 1851835 = 2777753) B2777753
theorem B4170185 : Blo 1851627 4170185 := bstep (se 2 (by rfl) ⟨1563819, by rfl⟩ : syracuseStep 4170185 = 3127639) B3127639
theorem B2777591 : Blo 1851627 2777591 := bstep (se 1 (by rfl) ⟨2083193, by rfl⟩ : syracuseStep 2777591 = 4166387) B4166387
theorem B1851911 : Blo 1851627 1851911 := bstep (se 1 (by rfl) ⟨1388933, by rfl⟩ : syracuseStep 1851911 = 2777867) B2777867
theorem B2777615 : Blo 1851627 2777615 := bstep (se 1 (by rfl) ⟨2083211, by rfl⟩ : syracuseStep 2777615 = 4166423) B4166423
theorem B1851919 : Blo 1851627 1851919 := bstep (se 1 (by rfl) ⟨1388939, by rfl⟩ : syracuseStep 1851919 = 2777879) B2777879
theorem B2777657 : Blo 1851627 2777657 := bstep (se 2 (by rfl) ⟨1041621, by rfl⟩ : syracuseStep 2777657 = 2083243) B2083243
theorem B1851963 : Blo 1851627 1851963 := bstep (se 1 (by rfl) ⟨1388972, by rfl⟩ : syracuseStep 1851963 = 2777945) B2777945
theorem B11264579 : Blo 1851627 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B2777735 : Blo 1851627 2777735 := bstep (se 1 (by rfl) ⟨2083301, by rfl⟩ : syracuseStep 2777735 = 4166603) B4166603
theorem B1852039 : Blo 1851627 1852039 := bstep (se 1 (by rfl) ⟨1389029, by rfl⟩ : syracuseStep 1852039 = 2778059) B2778059
theorem B2441863 : Blo 1851627 2441863 := bstep (se 1 (by rfl) ⟨1831397, by rfl⟩ : syracuseStep 2441863 = 3662795) B3662795
theorem B1852047 : Blo 1851627 1852047 := bstep (se 1 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 1852047 = 2778071) B2778071
theorem B2777771 : Blo 1851627 2777771 := bstep (se 1 (by rfl) ⟨2083328, by rfl⟩ : syracuseStep 2777771 = 4166657) B4166657
theorem B76030645 : Blo 1851627 76030645 := bstep (se 5 (by rfl) ⟨3563936, by rfl⟩ : syracuseStep 76030645 = 7127873) B7127873
theorem B1852091 : Blo 1851627 1852091 := bstep (se 1 (by rfl) ⟨1389068, by rfl⟩ : syracuseStep 1852091 = 2778137) B2778137
theorem B2777801 : Blo 1851627 2777801 := bstep (se 2 (by rfl) ⟨1041675, by rfl⟩ : syracuseStep 2777801 = 2083351) B2083351
theorem B20038373 : Blo 1851627 20038373 := bstep (se 4 (by rfl) ⟨1878597, by rfl⟩ : syracuseStep 20038373 = 3757195) B3757195
theorem B7512833 : Blo 1851627 7512833 := bstep (se 2 (by rfl) ⟨2817312, by rfl⟩ : syracuseStep 7512833 = 5634625) B5634625
theorem B9380609 : Blo 1851627 9380609 := bstep (se 2 (by rfl) ⟨3517728, by rfl⟩ : syracuseStep 9380609 = 7035457) B7035457
theorem B1852167 : Blo 1851627 1852167 := bstep (se 1 (by rfl) ⟨1389125, by rfl⟩ : syracuseStep 1852167 = 2778251) B2778251
theorem B1852175 : Blo 1851627 1852175 := bstep (se 1 (by rfl) ⟨1389131, by rfl⟩ : syracuseStep 1852175 = 2778263) B2778263
theorem B2777915 : Blo 1851627 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B1852219 : Blo 1851627 1852219 := bstep (se 1 (by rfl) ⟨1389164, by rfl⟩ : syracuseStep 1852219 = 2778329) B2778329
theorem B2777975 : Blo 1851627 2777975 := bstep (se 1 (by rfl) ⟨2083481, by rfl⟩ : syracuseStep 2777975 = 4166963) B4166963
theorem B1852295 : Blo 1851627 1852295 := bstep (se 1 (by rfl) ⟨1389221, by rfl⟩ : syracuseStep 1852295 = 2778443) B2778443
theorem B2777999 : Blo 1851627 2777999 := bstep (se 1 (by rfl) ⟨2083499, by rfl⟩ : syracuseStep 2777999 = 4166999) B4166999
theorem B1852303 : Blo 1851627 1852303 := bstep (se 1 (by rfl) ⟨1389227, by rfl⟩ : syracuseStep 1852303 = 2778455) B2778455
theorem B6251417 : Blo 1851627 6251417 := bstep (se 2 (by rfl) ⟨2344281, by rfl⟩ : syracuseStep 6251417 = 4688563) B4688563
theorem B2778041 : Blo 1851627 2778041 := bstep (se 2 (by rfl) ⟨1041765, by rfl⟩ : syracuseStep 2778041 = 2083531) B2083531
theorem B1852347 : Blo 1851627 1852347 := bstep (se 1 (by rfl) ⟨1389260, by rfl⟩ : syracuseStep 1852347 = 2778521) B2778521
theorem B2778119 : Blo 1851627 2778119 := bstep (se 1 (by rfl) ⟨2083589, by rfl⟩ : syracuseStep 2778119 = 4167179) B4167179
theorem B1852423 : Blo 1851627 1852423 := bstep (se 1 (by rfl) ⟨1389317, by rfl⟩ : syracuseStep 1852423 = 2778635) B2778635
theorem B2638855 : Blo 1851627 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B1852431 : Blo 1851627 1852431 := bstep (se 1 (by rfl) ⟨1389323, by rfl⟩ : syracuseStep 1852431 = 2778647) B2778647
theorem B2778155 : Blo 1851627 2778155 := bstep (se 1 (by rfl) ⟨2083616, by rfl⟩ : syracuseStep 2778155 = 4167233) B4167233
theorem B1852475 : Blo 1851627 1852475 := bstep (se 1 (by rfl) ⟨1389356, by rfl⟩ : syracuseStep 1852475 = 2778713) B2778713
theorem B2778185 : Blo 1851627 2778185 := bstep (se 2 (by rfl) ⟨1041819, by rfl⟩ : syracuseStep 2778185 = 2083639) B2083639
theorem B1852551 : Blo 1851627 1852551 := bstep (se 1 (by rfl) ⟨1389413, by rfl⟩ : syracuseStep 1852551 = 2778827) B2778827
theorem B2344079 : Blo 1851627 2344079 := bstep (se 1 (by rfl) ⟨1758059, by rfl⟩ : syracuseStep 2344079 = 3516119) B3516119
theorem B1852559 : Blo 1851627 1852559 := bstep (se 1 (by rfl) ⟨1389419, by rfl⟩ : syracuseStep 1852559 = 2778839) B2778839
theorem B2778299 : Blo 1851627 2778299 := bstep (se 1 (by rfl) ⟨2083724, by rfl⟩ : syracuseStep 2778299 = 4167449) B4167449
theorem B1852603 : Blo 1851627 1852603 := bstep (se 1 (by rfl) ⟨1389452, by rfl⟩ : syracuseStep 1852603 = 2778905) B2778905
theorem B2778359 : Blo 1851627 2778359 := bstep (se 1 (by rfl) ⟨2083769, by rfl⟩ : syracuseStep 2778359 = 4167539) B4167539
theorem B4687105 : Blo 1851627 4687105 := bstep (se 2 (by rfl) ⟨1757664, by rfl⟩ : syracuseStep 4687105 = 3515329) B3515329
theorem B1852679 : Blo 1851627 1852679 := bstep (se 1 (by rfl) ⟨1389509, by rfl⟩ : syracuseStep 1852679 = 2779019) B2779019
theorem B3515663 : Blo 1851627 3515663 := bstep (se 1 (by rfl) ⟨2636747, by rfl⟩ : syracuseStep 3515663 = 5273495) B5273495
theorem B2778383 : Blo 1851627 2778383 := bstep (se 1 (by rfl) ⟨2083787, by rfl⟩ : syracuseStep 2778383 = 4167575) B4167575
theorem B1852687 : Blo 1851627 1852687 := bstep (se 1 (by rfl) ⟨1389515, by rfl⟩ : syracuseStep 1852687 = 2779031) B2779031
theorem B2778425 : Blo 1851627 2778425 := bstep (se 2 (by rfl) ⟨1041909, by rfl⟩ : syracuseStep 2778425 = 2083819) B2083819
theorem B1852731 : Blo 1851627 1852731 := bstep (se 1 (by rfl) ⟨1389548, by rfl⟩ : syracuseStep 1852731 = 2779097) B2779097
theorem B4179319 : Blo 1851627 4179319 := bstep (se 1 (by rfl) ⟨3134489, by rfl⟩ : syracuseStep 4179319 = 6268979) B6268979
theorem B2778503 : Blo 1851627 2778503 := bstep (se 1 (by rfl) ⟨2083877, by rfl⟩ : syracuseStep 2778503 = 4167755) B4167755
theorem B1852807 : Blo 1851627 1852807 := bstep (se 1 (by rfl) ⟨1389605, by rfl⟩ : syracuseStep 1852807 = 2779211) B2779211
theorem B1852815 : Blo 1851627 1852815 := bstep (se 1 (by rfl) ⟨1389611, by rfl⟩ : syracuseStep 1852815 = 2779223) B2779223
theorem B3958163 : Blo 1851627 3958163 := bstep (se 1 (by rfl) ⟨2968622, by rfl⟩ : syracuseStep 3958163 = 5937245) B5937245
theorem B2778539 : Blo 1851627 2778539 := bstep (se 1 (by rfl) ⟨2083904, by rfl⟩ : syracuseStep 2778539 = 4167809) B4167809
theorem B27084217 : Blo 1851627 27084217 := bstep (se 2 (by rfl) ⟨10156581, by rfl⟩ : syracuseStep 27084217 = 20313163) B20313163
theorem B1852859 : Blo 1851627 1852859 := bstep (se 1 (by rfl) ⟨1389644, by rfl⟩ : syracuseStep 1852859 = 2779289) B2779289
theorem B2778569 : Blo 1851627 2778569 := bstep (se 2 (by rfl) ⟨1041963, by rfl⟩ : syracuseStep 2778569 = 2083927) B2083927
theorem B28526033 : Blo 1851627 28526033 := bstep (se 2 (by rfl) ⟨10697262, by rfl⟩ : syracuseStep 28526033 = 21394525) B21394525
theorem B1852935 : Blo 1851627 1852935 := bstep (se 1 (by rfl) ⟨1389701, by rfl⟩ : syracuseStep 1852935 = 2779403) B2779403
theorem B1852943 : Blo 1851627 1852943 := bstep (se 1 (by rfl) ⟨1389707, by rfl⟩ : syracuseStep 1852943 = 2779415) B2779415
theorem B9381419 : Blo 1851627 9381419 := bstep (se 1 (by rfl) ⟨7036064, by rfl⟩ : syracuseStep 9381419 = 14072129) B14072129
theorem B2778683 : Blo 1851627 2778683 := bstep (se 1 (by rfl) ⟨2084012, by rfl⟩ : syracuseStep 2778683 = 4168025) B4168025
theorem B1852987 : Blo 1851627 1852987 := bstep (se 1 (by rfl) ⟨1389740, by rfl⟩ : syracuseStep 1852987 = 2779481) B2779481
theorem B6252119 : Blo 1851627 6252119 := bstep (se 1 (by rfl) ⟨4689089, by rfl⟩ : syracuseStep 6252119 = 9378179) B9378179
theorem B2778743 : Blo 1851627 2778743 := bstep (se 1 (by rfl) ⟨2084057, by rfl⟩ : syracuseStep 2778743 = 4168115) B4168115
theorem B1853063 : Blo 1851627 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B2778767 : Blo 1851627 2778767 := bstep (se 1 (by rfl) ⟨2084075, by rfl⟩ : syracuseStep 2778767 = 4168151) B4168151
theorem B1853071 : Blo 1851627 1853071 := bstep (se 1 (by rfl) ⟨1389803, by rfl⟩ : syracuseStep 1853071 = 2779607) B2779607
theorem B2778809 : Blo 1851627 2778809 := bstep (se 2 (by rfl) ⟨1042053, by rfl⟩ : syracuseStep 2778809 = 2084107) B2084107
theorem B1853115 : Blo 1851627 1853115 := bstep (se 1 (by rfl) ⟨1389836, by rfl⟩ : syracuseStep 1853115 = 2779673) B2779673
theorem B20022977 : Blo 1851627 20022977 := bstep (se 2 (by rfl) ⟨7508616, by rfl⟩ : syracuseStep 20022977 = 15017233) B15017233
theorem B2778887 : Blo 1851627 2778887 := bstep (se 1 (by rfl) ⟨2084165, by rfl⟩ : syracuseStep 2778887 = 4168331) B4168331
theorem B1853191 : Blo 1851627 1853191 := bstep (se 1 (by rfl) ⟨1389893, by rfl⟩ : syracuseStep 1853191 = 2779787) B2779787
theorem B1853199 : Blo 1851627 1853199 := bstep (se 1 (by rfl) ⟨1389899, by rfl⟩ : syracuseStep 1853199 = 2779799) B2779799
theorem B3516203 : Blo 1851627 3516203 := bstep (se 1 (by rfl) ⟨2637152, by rfl⟩ : syracuseStep 3516203 = 5274305) B5274305
theorem B2778923 : Blo 1851627 2778923 := bstep (se 1 (by rfl) ⟨2084192, by rfl⟩ : syracuseStep 2778923 = 4168385) B4168385
theorem B1853243 : Blo 1851627 1853243 := bstep (se 1 (by rfl) ⟨1389932, by rfl⟩ : syracuseStep 1853243 = 2779865) B2779865
theorem B2778953 : Blo 1851627 2778953 := bstep (se 2 (by rfl) ⟨1042107, by rfl⟩ : syracuseStep 2778953 = 2084215) B2084215
theorem B4687703 : Blo 1851627 4687703 := bstep (se 1 (by rfl) ⟨3515777, by rfl⟩ : syracuseStep 4687703 = 7031555) B7031555
theorem B20309849 : Blo 1851627 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B1853319 : Blo 1851627 1853319 := bstep (se 1 (by rfl) ⟨1389989, by rfl⟩ : syracuseStep 1853319 = 2779979) B2779979
theorem B1853327 : Blo 1851627 1853327 := bstep (se 1 (by rfl) ⟨1389995, by rfl⟩ : syracuseStep 1853327 = 2779991) B2779991
theorem B2779067 : Blo 1851627 2779067 := bstep (se 1 (by rfl) ⟨2084300, by rfl⟩ : syracuseStep 2779067 = 4168601) B4168601
theorem B1853371 : Blo 1851627 1853371 := bstep (se 1 (by rfl) ⟨1390028, by rfl⟩ : syracuseStep 1853371 = 2780057) B2780057
theorem B2779127 : Blo 1851627 2779127 := bstep (se 1 (by rfl) ⟨2084345, by rfl⟩ : syracuseStep 2779127 = 4168691) B4168691
theorem B1853447 : Blo 1851627 1853447 := bstep (se 1 (by rfl) ⟨1390085, by rfl⟩ : syracuseStep 1853447 = 2780171) B2780171
theorem B17123339 : Blo 1851627 17123339 := bstep (se 1 (by rfl) ⟨12842504, by rfl⟩ : syracuseStep 17123339 = 25685009) B25685009
theorem B2779151 : Blo 1851627 2779151 := bstep (se 1 (by rfl) ⟨2084363, by rfl⟩ : syracuseStep 2779151 = 4168727) B4168727
theorem B1853455 : Blo 1851627 1853455 := bstep (se 1 (by rfl) ⟨1390091, by rfl⟩ : syracuseStep 1853455 = 2780183) B2780183
theorem B3565601 : Blo 1851627 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B4687915 : Blo 1851627 4687915 := bstep (se 1 (by rfl) ⟨3515936, by rfl⟩ : syracuseStep 4687915 = 7031873) B7031873
theorem B2779193 : Blo 1851627 2779193 := bstep (se 2 (by rfl) ⟨1042197, by rfl⟩ : syracuseStep 2779193 = 2084395) B2084395
theorem B1853499 : Blo 1851627 1853499 := bstep (se 1 (by rfl) ⟨1390124, by rfl⟩ : syracuseStep 1853499 = 2780249) B2780249
theorem B6252605 : Blo 1851627 6252605 := bstep (se 3 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 6252605 = 2344727) B2344727
theorem B7030871 : Blo 1851627 7030871 := bstep (se 1 (by rfl) ⟨5273153, by rfl⟩ : syracuseStep 7030871 = 10546307) B10546307
theorem B2779271 : Blo 1851627 2779271 := bstep (se 1 (by rfl) ⟨2084453, by rfl⟩ : syracuseStep 2779271 = 4168907) B4168907
theorem B1853575 : Blo 1851627 1853575 := bstep (se 1 (by rfl) ⟨1390181, by rfl⟩ : syracuseStep 1853575 = 2780363) B2780363
theorem B1853583 : Blo 1851627 1853583 := bstep (se 1 (by rfl) ⟨1390187, by rfl⟩ : syracuseStep 1853583 = 2780375) B2780375
theorem B2779307 : Blo 1851627 2779307 := bstep (se 1 (by rfl) ⟨2084480, by rfl⟩ : syracuseStep 2779307 = 4168961) B4168961
theorem B4688057 : Blo 1851627 4688057 := bstep (se 2 (by rfl) ⟨1758021, by rfl⟩ : syracuseStep 4688057 = 3516043) B3516043
theorem B1853627 : Blo 1851627 1853627 := bstep (se 1 (by rfl) ⟨1390220, by rfl⟩ : syracuseStep 1853627 = 2780441) B2780441
theorem B2779337 : Blo 1851627 2779337 := bstep (se 2 (by rfl) ⟨1042251, by rfl⟩ : syracuseStep 2779337 = 2084503) B2084503
theorem B9505025 : Blo 1851627 9505025 := bstep (se 2 (by rfl) ⟨3564384, by rfl⟩ : syracuseStep 9505025 = 7128769) B7128769
theorem B68512013 : Blo 1851627 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B9373967 : Blo 1851627 9373967 := bstep (se 1 (by rfl) ⟨7030475, by rfl⟩ : syracuseStep 9373967 = 14060951) B14060951
theorem B8907059 : Blo 1851627 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B2779451 : Blo 1851627 2779451 := bstep (se 1 (by rfl) ⟨2084588, by rfl⟩ : syracuseStep 2779451 = 4169177) B4169177
theorem B8907097 : Blo 1851627 8907097 := bstep (se 2 (by rfl) ⟨3340161, by rfl⟩ : syracuseStep 8907097 = 6680323) B6680323
theorem B2779511 : Blo 1851627 2779511 := bstep (se 1 (by rfl) ⟨2084633, by rfl⟩ : syracuseStep 2779511 = 4169267) B4169267
theorem B2083207 : Blo 1851627 2083207 := bstep (se 1 (by rfl) ⟨1562405, by rfl⟩ : syracuseStep 2083207 = 3124811) B3124811
theorem B2779535 : Blo 1851627 2779535 := bstep (se 1 (by rfl) ⟨2084651, by rfl⟩ : syracuseStep 2779535 = 4169303) B4169303
theorem B2779577 : Blo 1851627 2779577 := bstep (se 2 (by rfl) ⟨1042341, by rfl⟩ : syracuseStep 2779577 = 2084683) B2084683
theorem B21113297 : Blo 1851627 21113297 := bstep (se 2 (by rfl) ⟨7917486, by rfl⟩ : syracuseStep 21113297 = 15834973) B15834973
theorem B2779655 : Blo 1851627 2779655 := bstep (se 1 (by rfl) ⟨2084741, by rfl⟩ : syracuseStep 2779655 = 4169483) B4169483
theorem B5278223 : Blo 1851627 5278223 := bstep (se 1 (by rfl) ⟨3958667, by rfl⟩ : syracuseStep 5278223 = 7917335) B7917335
theorem B3754529 : Blo 1851627 3754529 := bstep (se 2 (by rfl) ⟨1407948, by rfl⟩ : syracuseStep 3754529 = 2815897) B2815897
theorem B2779691 : Blo 1851627 2779691 := bstep (se 1 (by rfl) ⟨2084768, by rfl⟩ : syracuseStep 2779691 = 4169537) B4169537
theorem B2083387 : Blo 1851627 2083387 := bstep (se 1 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 2083387 = 3125081) B3125081
theorem B7031357 : Blo 1851627 7031357 := bstep (se 3 (by rfl) ⟨1318379, by rfl⟩ : syracuseStep 7031357 = 2636759) B2636759
theorem B16894531 : Blo 1851627 16894531 := bstep (se 1 (by rfl) ⟨12670898, by rfl⟩ : syracuseStep 16894531 = 25341797) B25341797
theorem B2779721 : Blo 1851627 2779721 := bstep (se 2 (by rfl) ⟨1042395, by rfl⟩ : syracuseStep 2779721 = 2084791) B2084791
theorem B2779835 : Blo 1851627 2779835 := bstep (se 1 (by rfl) ⟨2084876, by rfl⟩ : syracuseStep 2779835 = 4169753) B4169753
theorem B2779895 : Blo 1851627 2779895 := bstep (se 1 (by rfl) ⟨2084921, by rfl⟩ : syracuseStep 2779895 = 4169843) B4169843
theorem B4754177 : Blo 1851627 4754177 := bstep (se 2 (by rfl) ⟨1782816, by rfl⟩ : syracuseStep 4754177 = 3565633) B3565633
theorem B2779919 : Blo 1851627 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B2779961 : Blo 1851627 2779961 := bstep (se 2 (by rfl) ⟨1042485, by rfl⟩ : syracuseStep 2779961 = 2084971) B2084971
theorem B3337019 : Blo 1851627 3337019 := bstep (se 1 (by rfl) ⟨2502764, by rfl⟩ : syracuseStep 3337019 = 5005529) B5005529
theorem B9382715 : Blo 1851627 9382715 := bstep (se 1 (by rfl) ⟨7037036, by rfl⟩ : syracuseStep 9382715 = 14074073) B14074073
theorem B3517319 : Blo 1851627 3517319 := bstep (se 1 (by rfl) ⟨2637989, by rfl⟩ : syracuseStep 3517319 = 5275979) B5275979
theorem B2780039 : Blo 1851627 2780039 := bstep (se 1 (by rfl) ⟨2085029, by rfl⟩ : syracuseStep 2780039 = 4170059) B4170059
theorem B2780075 : Blo 1851627 2780075 := bstep (se 1 (by rfl) ⟨2085056, by rfl⟩ : syracuseStep 2780075 = 4170113) B4170113
theorem B2780105 : Blo 1851627 2780105 := bstep (se 2 (by rfl) ⟨1042539, by rfl⟩ : syracuseStep 2780105 = 2085079) B2085079
theorem B9382877 : Blo 1851627 9382877 := bstep (se 3 (by rfl) ⟨1759289, by rfl⟩ : syracuseStep 9382877 = 3518579) B3518579
theorem B10554371 : Blo 1851627 10554371 := bstep (se 1 (by rfl) ⟨7915778, by rfl⟩ : syracuseStep 10554371 = 15831557) B15831557
theorem B2083855 : Blo 1851627 2083855 := bstep (se 1 (by rfl) ⟨1562891, by rfl⟩ : syracuseStep 2083855 = 3125783) B3125783
theorem B2968591 : Blo 1851627 2968591 := bstep (se 1 (by rfl) ⟨2226443, by rfl⟩ : syracuseStep 2968591 = 4452887) B4452887
theorem B2540842019 : Blo 1851627 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B2780219 : Blo 1851627 2780219 := bstep (se 1 (by rfl) ⟨2085164, by rfl⟩ : syracuseStep 2780219 = 4170329) B4170329
theorem B2780279 : Blo 1851627 2780279 := bstep (se 1 (by rfl) ⟨2085209, by rfl⟩ : syracuseStep 2780279 = 4170419) B4170419
theorem B2780303 : Blo 1851627 2780303 := bstep (se 1 (by rfl) ⟨2085227, by rfl⟩ : syracuseStep 2780303 = 4170455) B4170455
theorem B4689049 : Blo 1851627 4689049 := bstep (se 2 (by rfl) ⟨1758393, by rfl⟩ : syracuseStep 4689049 = 3516787) B3516787
theorem B13028525 : Blo 1851627 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B2780345 : Blo 1851627 2780345 := bstep (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) B2085259
theorem B2780423 : Blo 1851627 2780423 := bstep (se 1 (by rfl) ⟨2085317, by rfl⟩ : syracuseStep 2780423 = 4170635) B4170635
theorem B9383201 : Blo 1851627 9383201 := bstep (se 2 (by rfl) ⟨3518700, by rfl⟩ : syracuseStep 9383201 = 7037401) B7037401
theorem B4009259 : Blo 1851627 4009259 := bstep (se 1 (by rfl) ⟨3006944, by rfl⟩ : syracuseStep 4009259 = 6013889) B6013889
theorem B4689211 : Blo 1851627 4689211 := bstep (se 1 (by rfl) ⟨3516908, by rfl⟩ : syracuseStep 4689211 = 7033817) B7033817
theorem B3517843 : Blo 1851627 3517843 := bstep (se 1 (by rfl) ⟨2638382, by rfl⟩ : syracuseStep 3517843 = 5276765) B5276765
theorem B6254009 : Blo 1851627 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B4689353 : Blo 1851627 4689353 := bstep (se 2 (by rfl) ⟨1758507, by rfl⟩ : syracuseStep 4689353 = 3517015) B3517015
theorem B14069213 : Blo 1851627 14069213 := bstep (se 3 (by rfl) ⟨2637977, by rfl⟩ : syracuseStep 14069213 = 5275955) B5275955
theorem B33820163 : Blo 1851627 33820163 := bstep (se 1 (by rfl) ⟨25365122, by rfl⟩ : syracuseStep 33820163 = 50730245) B50730245
theorem B2084359 : Blo 1851627 2084359 := bstep (se 1 (by rfl) ⟨1563269, by rfl⟩ : syracuseStep 2084359 = 3126539) B3126539
theorem B10546807 : Blo 1851627 10546807 := bstep (se 1 (by rfl) ⟨7910105, by rfl⟩ : syracuseStep 10546807 = 15820211) B15820211
theorem B3755639 : Blo 1851627 3755639 := bstep (se 1 (by rfl) ⟨2816729, by rfl⟩ : syracuseStep 3755639 = 5633459) B5633459
theorem B4451993 : Blo 1851627 4451993 := bstep (se 2 (by rfl) ⟨1669497, by rfl⟩ : syracuseStep 4451993 = 3338995) B3338995
theorem B2084539 : Blo 1851627 2084539 := bstep (se 1 (by rfl) ⟨1563404, by rfl⟩ : syracuseStep 2084539 = 3126809) B3126809
theorem B9375425 : Blo 1851627 9375425 := bstep (se 2 (by rfl) ⟨3515784, by rfl⟩ : syracuseStep 9375425 = 7031569) B7031569
theorem B4689697 : Blo 1851627 4689697 := bstep (se 2 (by rfl) ⟨1758636, by rfl⟩ : syracuseStep 4689697 = 3517273) B3517273
theorem B21393227 : Blo 1851627 21393227 := bstep (se 1 (by rfl) ⟨16044920, by rfl⟩ : syracuseStep 21393227 = 32089841) B32089841
theorem B15830873 : Blo 1851627 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B9146333 : Blo 1851627 9146333 := bstep (se 3 (by rfl) ⟨1714937, by rfl⟩ : syracuseStep 9146333 = 3429875) B3429875
theorem B6254603 : Blo 1851627 6254603 := bstep (se 1 (by rfl) ⟨4690952, by rfl⟩ : syracuseStep 6254603 = 9381905) B9381905
theorem B3125263 : Blo 1851627 3125263 := bstep (se 1 (by rfl) ⟨2343947, by rfl⟩ : syracuseStep 3125263 = 4687895) B4687895
theorem B6254711 : Blo 1851627 6254711 := bstep (se 1 (by rfl) ⟨4691033, by rfl⟩ : syracuseStep 6254711 = 9382067) B9382067
theorem B2085007 : Blo 1851627 2085007 := bstep (se 1 (by rfl) ⟨1563755, by rfl⟩ : syracuseStep 2085007 = 3127511) B3127511
theorem B22532269 : Blo 1851627 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B4690295 : Blo 1851627 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B35623313 : Blo 1851627 35623313 := bstep (se 2 (by rfl) ⟨13358742, by rfl⟩ : syracuseStep 35623313 = 26717485) B26717485
theorem B3125803 : Blo 1851627 3125803 := bstep (se 1 (by rfl) ⟨2344352, by rfl⟩ : syracuseStep 3125803 = 4688705) B4688705
theorem B5632573 : Blo 1851627 5632573 := bstep (se 3 (by rfl) ⟨1056107, by rfl⟩ : syracuseStep 5632573 = 2112215) B2112215
theorem B4166279 : Blo 1851627 4166279 := bstep (se 1 (by rfl) ⟨3124709, by rfl⟩ : syracuseStep 4166279 = 6249419) B6249419
theorem B3125945 : Blo 1851627 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B4453049 : Blo 1851627 4453049 := bstep (se 2 (by rfl) ⟨1669893, by rfl⟩ : syracuseStep 4453049 = 3339787) B3339787
theorem B72200897 : Blo 1851627 72200897 := bstep (se 2 (by rfl) ⟨27075336, by rfl⟩ : syracuseStep 72200897 = 54150673) B54150673
theorem B6255305 : Blo 1851627 6255305 := bstep (se 2 (by rfl) ⟨2345739, by rfl⟩ : syracuseStep 6255305 = 4691479) B4691479
theorem B5346091 : Blo 1851627 5346091 := bstep (se 1 (by rfl) ⟨4009568, by rfl⟩ : syracuseStep 5346091 = 8019137) B8019137
theorem B4166459 : Blo 1851627 4166459 := bstep (se 1 (by rfl) ⟨3124844, by rfl⟩ : syracuseStep 4166459 = 6249689) B6249689
theorem B10548083 : Blo 1851627 10548083 := bstep (se 1 (by rfl) ⟨7911062, by rfl⟩ : syracuseStep 10548083 = 15822125) B15822125
theorem B2503543 : Blo 1851627 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B4166585 : Blo 1851627 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B9376721 : Blo 1851627 9376721 := bstep (se 2 (by rfl) ⟨3516270, by rfl⟩ : syracuseStep 9376721 = 7032541) B7032541
theorem B16487435 : Blo 1851627 16487435 := bstep (se 1 (by rfl) ⟨12365576, by rfl⟩ : syracuseStep 16487435 = 24731153) B24731153
theorem B24065261 : Blo 1851627 24065261 := bstep (se 3 (by rfl) ⟨4512236, by rfl⟩ : syracuseStep 24065261 = 9024473) B9024473
theorem B5272847 : Blo 1851627 5272847 := bstep (se 1 (by rfl) ⟨3954635, by rfl⟩ : syracuseStep 5272847 = 7909271) B7909271
theorem B4166927 : Blo 1851627 4166927 := bstep (se 1 (by rfl) ⟨3125195, by rfl⟩ : syracuseStep 4166927 = 6250391) B6250391
theorem B5936399 : Blo 1851627 5936399 := bstep (se 1 (by rfl) ⟨4452299, by rfl⟩ : syracuseStep 5936399 = 8904599) B8904599
theorem B4166945 : Blo 1851627 4166945 := bstep (se 2 (by rfl) ⟨1562604, by rfl⟩ : syracuseStep 4166945 = 3125209) B3125209
theorem B10548539 : Blo 1851627 10548539 := bstep (se 1 (by rfl) ⟨7911404, by rfl⟩ : syracuseStep 10548539 = 15822809) B15822809
theorem B3126647 : Blo 1851627 3126647 := bstep (se 1 (by rfl) ⟨2344985, by rfl⟩ : syracuseStep 3126647 = 4689971) B4689971
theorem B11261369 : Blo 1851627 11261369 := bstep (se 2 (by rfl) ⟨4223013, by rfl⟩ : syracuseStep 11261369 = 8446027) B8446027
theorem B4167287 : Blo 1851627 4167287 := bstep (se 1 (by rfl) ⟨3125465, by rfl⟩ : syracuseStep 4167287 = 6250931) B6250931
theorem B4691591 : Blo 1851627 4691591 := bstep (se 1 (by rfl) ⟨3518693, by rfl⟩ : syracuseStep 4691591 = 7037387) B7037387
theorem B42759859 : Blo 1851627 42759859 := bstep (se 1 (by rfl) ⟨32069894, by rfl⟩ : syracuseStep 42759859 = 64139789) B64139789
theorem B4691641 : Blo 1851627 4691641 := bstep (se 2 (by rfl) ⟨1759365, by rfl⟩ : syracuseStep 4691641 = 3518731) B3518731
theorem B4167467 : Blo 1851627 4167467 := bstep (se 1 (by rfl) ⟨3125600, by rfl⟩ : syracuseStep 4167467 = 6251201) B6251201
theorem B3127099 : Blo 1851627 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B3340091 : Blo 1851627 3340091 := bstep (se 1 (by rfl) ⟨2505068, by rfl⟩ : syracuseStep 3340091 = 5010137) B5010137
theorem B7034759 : Blo 1851627 7034759 := bstep (se 1 (by rfl) ⟨5276069, by rfl⟩ : syracuseStep 7034759 = 10552139) B10552139
theorem B4011923 : Blo 1851627 4011923 := bstep (se 1 (by rfl) ⟨3008942, by rfl⟩ : syracuseStep 4011923 = 6017885) B6017885
theorem B3127241 : Blo 1851627 3127241 := bstep (se 2 (by rfl) ⟨1172715, by rfl⟩ : syracuseStep 3127241 = 2345431) B2345431
theorem B10016855 : Blo 1851627 10016855 := bstep (se 1 (by rfl) ⟨7512641, by rfl⟩ : syracuseStep 10016855 = 15025283) B15025283
theorem B26703989 : Blo 1851627 26703989 := bstep (se 5 (by rfl) ⟨1251749, by rfl⟩ : syracuseStep 26703989 = 2503499) B2503499
theorem B4225159 : Blo 1851627 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B4167827 : Blo 1851627 4167827 := bstep (se 1 (by rfl) ⟨3125870, by rfl⟩ : syracuseStep 4167827 = 6251741) B6251741
theorem B4167881 : Blo 1851627 4167881 := bstep (se 2 (by rfl) ⟨1562955, by rfl⟩ : syracuseStep 4167881 = 3125911) B3125911
theorem B42776849 : Blo 1851627 42776849 := bstep (se 2 (by rfl) ⟨16041318, by rfl⟩ : syracuseStep 42776849 = 32082637) B32082637
theorem B3954977 : Blo 1851627 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B10549541 : Blo 1851627 10549541 := bstep (se 4 (by rfl) ⟨989019, by rfl⟩ : syracuseStep 10549541 = 1978039) B1978039
theorem B5274247 : Blo 1851627 5274247 := bstep (se 1 (by rfl) ⟨3955685, by rfl⟩ : syracuseStep 5274247 = 7911371) B7911371
theorem B3127943 : Blo 1851627 3127943 := bstep (se 1 (by rfl) ⟨2345957, by rfl⟩ : syracuseStep 3127943 = 4691915) B4691915
theorem B17799857 : Blo 1851627 17799857 := bstep (se 2 (by rfl) ⟨6674946, by rfl⟩ : syracuseStep 17799857 = 13349893) B13349893
theorem B10549997 : Blo 1851627 10549997 := bstep (se 3 (by rfl) ⟨1978124, by rfl⟩ : syracuseStep 10549997 = 3956249) B3956249
theorem B3169039 : Blo 1851627 3169039 := bstep (se 1 (by rfl) ⟨2376779, by rfl⟩ : syracuseStep 3169039 = 4753559) B4753559
theorem B8903483 : Blo 1851627 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B4168583 : Blo 1851627 4168583 := bstep (se 1 (by rfl) ⟨3126437, by rfl⟩ : syracuseStep 4168583 = 6252875) B6252875
theorem B5274521 : Blo 1851627 5274521 := bstep (se 2 (by rfl) ⟨1977945, by rfl⟩ : syracuseStep 5274521 = 3955891) B3955891
theorem B9378827 : Blo 1851627 9378827 := bstep (se 1 (by rfl) ⟨7034120, by rfl⟩ : syracuseStep 9378827 = 14068241) B14068241
theorem B4168763 : Blo 1851627 4168763 := bstep (se 1 (by rfl) ⟨3126572, by rfl⟩ : syracuseStep 4168763 = 6253145) B6253145
theorem B9378989 : Blo 1851627 9378989 := bstep (se 3 (by rfl) ⟨1758560, by rfl⟩ : syracuseStep 9378989 = 3517121) B3517121
theorem B13360301 : Blo 1851627 13360301 := bstep (se 3 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 13360301 = 5010113) B5010113
theorem B4168889 : Blo 1851627 4168889 := bstep (se 2 (by rfl) ⟨1563333, by rfl⟩ : syracuseStep 4168889 = 3126667) B3126667
theorem B202816709 : Blo 1851627 202816709 := bstep (se 4 (by rfl) ⟨19014066, by rfl⟩ : syracuseStep 202816709 = 38028133) B38028133
theorem B6249743 : Blo 1851627 6249743 := bstep (se 1 (by rfl) ⟨4687307, by rfl⟩ : syracuseStep 6249743 = 9374615) B9374615
theorem B10550681 : Blo 1851627 10550681 := bstep (se 2 (by rfl) ⟨3956505, by rfl⟩ : syracuseStep 10550681 = 7913011) B7913011
theorem B4169231 : Blo 1851627 4169231 := bstep (se 1 (by rfl) ⟨3126923, by rfl⟩ : syracuseStep 4169231 = 6253847) B6253847
theorem B2817551 : Blo 1851627 2817551 := bstep (se 1 (by rfl) ⟨2113163, by rfl⟩ : syracuseStep 2817551 = 4226327) B4226327
theorem B6250013 : Blo 1851627 6250013 := bstep (se 3 (by rfl) ⟨1171877, by rfl⟩ : syracuseStep 6250013 = 2343755) B2343755
theorem B4169249 : Blo 1851627 4169249 := bstep (se 2 (by rfl) ⟨1563468, by rfl⟩ : syracuseStep 4169249 = 3126937) B3126937
theorem B15826499 : Blo 1851627 15826499 := bstep (se 1 (by rfl) ⟨11869874, by rfl⟩ : syracuseStep 15826499 = 23739749) B23739749
theorem B27065933 : Blo 1851627 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B5349163 : Blo 1851627 5349163 := bstep (se 1 (by rfl) ⟨4011872, by rfl⟩ : syracuseStep 5349163 = 8023745) B8023745
theorem B2637625 : Blo 1851627 2637625 := bstep (se 2 (by rfl) ⟨989109, by rfl⟩ : syracuseStep 2637625 = 1978219) B1978219
theorem B4169591 : Blo 1851627 4169591 := bstep (se 1 (by rfl) ⟨3127193, by rfl⟩ : syracuseStep 4169591 = 6254387) B6254387
theorem B4169735 : Blo 1851627 4169735 := bstep (se 1 (by rfl) ⟨3127301, by rfl⟩ : syracuseStep 4169735 = 6254603) B6254603
theorem B45662237 : Blo 1851627 45662237 := bstep (se 3 (by rfl) ⟨8561669, by rfl⟩ : syracuseStep 45662237 = 17123339) B17123339
theorem B6250553 : Blo 1851627 6250553 := bstep (se 2 (by rfl) ⟨2343957, by rfl⟩ : syracuseStep 6250553 = 4687915) B4687915
theorem B5275705 : Blo 1851627 5275705 := bstep (se 2 (by rfl) ⟨1978389, by rfl⟩ : syracuseStep 5275705 = 3956779) B3956779
theorem B4169807 : Blo 1851627 4169807 := bstep (se 1 (by rfl) ⟨3127355, by rfl⟩ : syracuseStep 4169807 = 6254711) B6254711
theorem B16908517 : Blo 1851627 16908517 := bstep (se 4 (by rfl) ⟨1585173, by rfl⟩ : syracuseStep 16908517 = 3170347) B3170347
theorem B23748875 : Blo 1851627 23748875 := bstep (se 1 (by rfl) ⟨17811656, by rfl⟩ : syracuseStep 23748875 = 35623313) B35623313
theorem B1851687 : Blo 1851627 1851687 := bstep (se 1 (by rfl) ⟨1388765, by rfl⟩ : syracuseStep 1851687 = 2777531) B2777531
theorem B1851727 : Blo 1851627 1851727 := bstep (se 1 (by rfl) ⟨1388795, by rfl⟩ : syracuseStep 1851727 = 2777591) B2777591
theorem B1851743 : Blo 1851627 1851743 := bstep (se 1 (by rfl) ⟨1388807, by rfl⟩ : syracuseStep 1851743 = 2777615) B2777615
theorem B1851771 : Blo 1851627 1851771 := bstep (se 1 (by rfl) ⟨1388828, by rfl⟩ : syracuseStep 1851771 = 2777657) B2777657
theorem B6250877 : Blo 1851627 6250877 := bstep (se 3 (by rfl) ⟨1172039, by rfl⟩ : syracuseStep 6250877 = 2344079) B2344079
theorem B2777519 : Blo 1851627 2777519 := bstep (se 1 (by rfl) ⟨2083139, by rfl⟩ : syracuseStep 2777519 = 4166279) B4166279
theorem B1851823 : Blo 1851627 1851823 := bstep (se 1 (by rfl) ⟨1388867, by rfl⟩ : syracuseStep 1851823 = 2777735) B2777735
theorem B1851847 : Blo 1851627 1851847 := bstep (se 1 (by rfl) ⟨1388885, by rfl⟩ : syracuseStep 1851847 = 2777771) B2777771
theorem B1851867 : Blo 1851627 1851867 := bstep (se 1 (by rfl) ⟨1388900, by rfl⟩ : syracuseStep 1851867 = 2777801) B2777801
theorem B4170203 : Blo 1851627 4170203 := bstep (se 1 (by rfl) ⟨3127652, by rfl⟩ : syracuseStep 4170203 = 6255305) B6255305
theorem B2777609 : Blo 1851627 2777609 := bstep (se 2 (by rfl) ⟨1041603, by rfl⟩ : syracuseStep 2777609 = 2083207) B2083207
theorem B2777639 : Blo 1851627 2777639 := bstep (se 1 (by rfl) ⟨2083229, by rfl⟩ : syracuseStep 2777639 = 4166459) B4166459
theorem B1851943 : Blo 1851627 1851943 := bstep (se 1 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 1851943 = 2777915) B2777915
theorem B1851983 : Blo 1851627 1851983 := bstep (se 1 (by rfl) ⟨1388987, by rfl⟩ : syracuseStep 1851983 = 2777975) B2777975
theorem B1851999 : Blo 1851627 1851999 := bstep (se 1 (by rfl) ⟨1388999, by rfl⟩ : syracuseStep 1851999 = 2777999) B2777999
theorem B2777723 : Blo 1851627 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1852027 : Blo 1851627 1852027 := bstep (se 1 (by rfl) ⟨1389020, by rfl⟩ : syracuseStep 1852027 = 2778041) B2778041
theorem B6251147 : Blo 1851627 6251147 := bstep (se 1 (by rfl) ⟨4688360, by rfl⟩ : syracuseStep 6251147 = 9376721) B9376721
theorem B1852079 : Blo 1851627 1852079 := bstep (se 1 (by rfl) ⟨1389059, by rfl⟩ : syracuseStep 1852079 = 2778119) B2778119
theorem B1852103 : Blo 1851627 1852103 := bstep (se 1 (by rfl) ⟨1389077, by rfl⟩ : syracuseStep 1852103 = 2778155) B2778155
theorem B1852123 : Blo 1851627 1852123 := bstep (se 1 (by rfl) ⟨1389092, by rfl⟩ : syracuseStep 1852123 = 2778185) B2778185
theorem B2777849 : Blo 1851627 2777849 := bstep (se 2 (by rfl) ⟨1041693, by rfl⟩ : syracuseStep 2777849 = 2083387) B2083387
theorem B1852199 : Blo 1851627 1852199 := bstep (se 1 (by rfl) ⟨1389149, by rfl⟩ : syracuseStep 1852199 = 2778299) B2778299
theorem B1852239 : Blo 1851627 1852239 := bstep (se 1 (by rfl) ⟨1389179, by rfl⟩ : syracuseStep 1852239 = 2778359) B2778359
theorem B3515231 : Blo 1851627 3515231 := bstep (se 1 (by rfl) ⟨2636423, by rfl⟩ : syracuseStep 3515231 = 5272847) B5272847
theorem B2777951 : Blo 1851627 2777951 := bstep (se 1 (by rfl) ⟨2083463, by rfl⟩ : syracuseStep 2777951 = 4166927) B4166927
theorem B1852255 : Blo 1851627 1852255 := bstep (se 1 (by rfl) ⟨1389191, by rfl⟩ : syracuseStep 1852255 = 2778383) B2778383
theorem B3957599 : Blo 1851627 3957599 := bstep (se 1 (by rfl) ⟨2968199, by rfl⟩ : syracuseStep 3957599 = 5936399) B5936399
theorem B2777963 : Blo 1851627 2777963 := bstep (se 1 (by rfl) ⟨2083472, by rfl⟩ : syracuseStep 2777963 = 4166945) B4166945
theorem B1852283 : Blo 1851627 1852283 := bstep (se 1 (by rfl) ⟨1389212, by rfl⟩ : syracuseStep 1852283 = 2778425) B2778425
theorem B1852335 : Blo 1851627 1852335 := bstep (se 1 (by rfl) ⟨1389251, by rfl⟩ : syracuseStep 1852335 = 2778503) B2778503
theorem B2638775 : Blo 1851627 2638775 := bstep (se 1 (by rfl) ⟨1979081, by rfl⟩ : syracuseStep 2638775 = 3958163) B3958163
theorem B1852359 : Blo 1851627 1852359 := bstep (se 1 (by rfl) ⟨1389269, by rfl⟩ : syracuseStep 1852359 = 2778539) B2778539
theorem B1852379 : Blo 1851627 1852379 := bstep (se 1 (by rfl) ⟨1389284, by rfl⟩ : syracuseStep 1852379 = 2778569) B2778569
theorem B1852455 : Blo 1851627 1852455 := bstep (se 1 (by rfl) ⟨1389341, by rfl⟩ : syracuseStep 1852455 = 2778683) B2778683
theorem B7128121 : Blo 1851627 7128121 := bstep (se 2 (by rfl) ⟨2673045, by rfl⟩ : syracuseStep 7128121 = 5346091) B5346091
theorem B2778191 : Blo 1851627 2778191 := bstep (se 1 (by rfl) ⟨2083643, by rfl⟩ : syracuseStep 2778191 = 4167287) B4167287
theorem B1852495 : Blo 1851627 1852495 := bstep (se 1 (by rfl) ⟨1389371, by rfl⟩ : syracuseStep 1852495 = 2778743) B2778743
theorem B1852511 : Blo 1851627 1852511 := bstep (se 1 (by rfl) ⟨1389383, by rfl⟩ : syracuseStep 1852511 = 2778767) B2778767
theorem B1852539 : Blo 1851627 1852539 := bstep (se 1 (by rfl) ⟨1389404, by rfl⟩ : syracuseStep 1852539 = 2778809) B2778809
theorem B1852591 : Blo 1851627 1852591 := bstep (se 1 (by rfl) ⟨1389443, by rfl⟩ : syracuseStep 1852591 = 2778887) B2778887
theorem B2344135 : Blo 1851627 2344135 := bstep (se 1 (by rfl) ⟨1758101, by rfl⟩ : syracuseStep 2344135 = 3516203) B3516203
theorem B2778311 : Blo 1851627 2778311 := bstep (se 1 (by rfl) ⟨2083733, by rfl⟩ : syracuseStep 2778311 = 4167467) B4167467
theorem B1852615 : Blo 1851627 1852615 := bstep (se 1 (by rfl) ⟨1389461, by rfl⟩ : syracuseStep 1852615 = 2778923) B2778923
theorem B1852635 : Blo 1851627 1852635 := bstep (se 1 (by rfl) ⟨1389476, by rfl⟩ : syracuseStep 1852635 = 2778953) B2778953
theorem B1852711 : Blo 1851627 1852711 := bstep (se 1 (by rfl) ⟨1389533, by rfl⟩ : syracuseStep 1852711 = 2779067) B2779067
theorem B1852751 : Blo 1851627 1852751 := bstep (se 1 (by rfl) ⟨1389563, by rfl⟩ : syracuseStep 1852751 = 2779127) B2779127
theorem B1852767 : Blo 1851627 1852767 := bstep (se 1 (by rfl) ⟨1389575, by rfl⟩ : syracuseStep 1852767 = 2779151) B2779151
theorem B2778473 : Blo 1851627 2778473 := bstep (se 2 (by rfl) ⟨1041927, by rfl⟩ : syracuseStep 2778473 = 2083855) B2083855
theorem B2377067 : Blo 1851627 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B3958121 : Blo 1851627 3958121 := bstep (se 2 (by rfl) ⟨1484295, by rfl⟩ : syracuseStep 3958121 = 2968591) B2968591
theorem B1852795 : Blo 1851627 1852795 := bstep (se 1 (by rfl) ⟨1389596, by rfl⟩ : syracuseStep 1852795 = 2779193) B2779193
theorem B7513469 : Blo 1851627 7513469 := bstep (se 3 (by rfl) ⟨1408775, by rfl⟩ : syracuseStep 7513469 = 2817551) B2817551
theorem B4687247 : Blo 1851627 4687247 := bstep (se 1 (by rfl) ⟨3515435, by rfl⟩ : syracuseStep 4687247 = 7030871) B7030871
theorem B6677903 : Blo 1851627 6677903 := bstep (se 1 (by rfl) ⟨5008427, by rfl⟩ : syracuseStep 6677903 = 10016855) B10016855
theorem B17802659 : Blo 1851627 17802659 := bstep (se 1 (by rfl) ⟨13351994, by rfl⟩ : syracuseStep 17802659 = 26703989) B26703989
theorem B1852847 : Blo 1851627 1852847 := bstep (se 1 (by rfl) ⟨1389635, by rfl⟩ : syracuseStep 1852847 = 2779271) B2779271
theorem B2778551 : Blo 1851627 2778551 := bstep (se 1 (by rfl) ⟨2083913, by rfl⟩ : syracuseStep 2778551 = 4167827) B4167827
theorem B1852871 : Blo 1851627 1852871 := bstep (se 1 (by rfl) ⟨1389653, by rfl⟩ : syracuseStep 1852871 = 2779307) B2779307
theorem B2778587 : Blo 1851627 2778587 := bstep (se 1 (by rfl) ⟨2083940, by rfl⟩ : syracuseStep 2778587 = 4167881) B4167881
theorem B1852891 : Blo 1851627 1852891 := bstep (se 1 (by rfl) ⟨1389668, by rfl⟩ : syracuseStep 1852891 = 2779337) B2779337
theorem B6252065 : Blo 1851627 6252065 := bstep (se 2 (by rfl) ⟨2344524, by rfl⟩ : syracuseStep 6252065 = 4689049) B4689049
theorem B1852967 : Blo 1851627 1852967 := bstep (se 1 (by rfl) ⟨1389725, by rfl⟩ : syracuseStep 1852967 = 2779451) B2779451
theorem B1853007 : Blo 1851627 1853007 := bstep (se 1 (by rfl) ⟨1389755, by rfl⟩ : syracuseStep 1853007 = 2779511) B2779511
theorem B1853023 : Blo 1851627 1853023 := bstep (se 1 (by rfl) ⟨1389767, by rfl⟩ : syracuseStep 1853023 = 2779535) B2779535
theorem B1853051 : Blo 1851627 1853051 := bstep (se 1 (by rfl) ⟨1389788, by rfl⟩ : syracuseStep 1853051 = 2779577) B2779577
theorem B14075531 : Blo 1851627 14075531 := bstep (se 1 (by rfl) ⟨10556648, by rfl⟩ : syracuseStep 14075531 = 21113297) B21113297
theorem B1853103 : Blo 1851627 1853103 := bstep (se 1 (by rfl) ⟨1389827, by rfl⟩ : syracuseStep 1853103 = 2779655) B2779655
theorem B1853127 : Blo 1851627 1853127 := bstep (se 1 (by rfl) ⟨1389845, by rfl⟩ : syracuseStep 1853127 = 2779691) B2779691
theorem B4687571 : Blo 1851627 4687571 := bstep (se 1 (by rfl) ⟨3515678, by rfl⟩ : syracuseStep 4687571 = 7031357) B7031357
theorem B1853147 : Blo 1851627 1853147 := bstep (se 1 (by rfl) ⟨1389860, by rfl⟩ : syracuseStep 1853147 = 2779721) B2779721
theorem B6252281 : Blo 1851627 6252281 := bstep (se 2 (by rfl) ⟨2344605, by rfl⟩ : syracuseStep 6252281 = 4689211) B4689211
theorem B1853223 : Blo 1851627 1853223 := bstep (se 1 (by rfl) ⟨1389917, by rfl⟩ : syracuseStep 1853223 = 2779835) B2779835
theorem B1853263 : Blo 1851627 1853263 := bstep (se 1 (by rfl) ⟨1389947, by rfl⟩ : syracuseStep 1853263 = 2779895) B2779895
theorem B1853279 : Blo 1851627 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B1853307 : Blo 1851627 1853307 := bstep (se 1 (by rfl) ⟨1389980, by rfl⟩ : syracuseStep 1853307 = 2779961) B2779961
theorem B36112289 : Blo 1851627 36112289 := bstep (se 2 (by rfl) ⟨13542108, by rfl⟩ : syracuseStep 36112289 = 27084217) B27084217
theorem B2779055 : Blo 1851627 2779055 := bstep (se 1 (by rfl) ⟨2084291, by rfl⟩ : syracuseStep 2779055 = 4168583) B4168583
theorem B2344879 : Blo 1851627 2344879 := bstep (se 1 (by rfl) ⟨1758659, by rfl⟩ : syracuseStep 2344879 = 3517319) B3517319
theorem B1853359 : Blo 1851627 1853359 := bstep (se 1 (by rfl) ⟨1390019, by rfl⟩ : syracuseStep 1853359 = 2780039) B2780039
theorem B3516347 : Blo 1851627 3516347 := bstep (se 1 (by rfl) ⟨2637260, by rfl⟩ : syracuseStep 3516347 = 5274521) B5274521
theorem B1853383 : Blo 1851627 1853383 := bstep (se 1 (by rfl) ⟨1390037, by rfl⟩ : syracuseStep 1853383 = 2780075) B2780075
theorem B1853403 : Blo 1851627 1853403 := bstep (se 1 (by rfl) ⟨1390052, by rfl⟩ : syracuseStep 1853403 = 2780105) B2780105
theorem B6252551 : Blo 1851627 6252551 := bstep (se 1 (by rfl) ⟨4689413, by rfl⟩ : syracuseStep 6252551 = 9378827) B9378827
theorem B2779145 : Blo 1851627 2779145 := bstep (se 2 (by rfl) ⟨1042179, by rfl⟩ : syracuseStep 2779145 = 2084359) B2084359
theorem B1693894679 : Blo 1851627 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B2779175 : Blo 1851627 2779175 := bstep (se 1 (by rfl) ⟨2084381, by rfl⟩ : syracuseStep 2779175 = 4168763) B4168763
theorem B1853479 : Blo 1851627 1853479 := bstep (se 1 (by rfl) ⟨1390109, by rfl⟩ : syracuseStep 1853479 = 2780219) B2780219
theorem B1853519 : Blo 1851627 1853519 := bstep (se 1 (by rfl) ⟨1390139, by rfl⟩ : syracuseStep 1853519 = 2780279) B2780279
theorem B1853535 : Blo 1851627 1853535 := bstep (se 1 (by rfl) ⟨1390151, by rfl⟩ : syracuseStep 1853535 = 2780303) B2780303
theorem B6252659 : Blo 1851627 6252659 := bstep (se 1 (by rfl) ⟨4689494, by rfl⟩ : syracuseStep 6252659 = 9378989) B9378989
theorem B8685683 : Blo 1851627 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B8906867 : Blo 1851627 8906867 := bstep (se 1 (by rfl) ⟨6680150, by rfl⟩ : syracuseStep 8906867 = 13360301) B13360301
theorem B2779259 : Blo 1851627 2779259 := bstep (se 1 (by rfl) ⟨2084444, by rfl⟩ : syracuseStep 2779259 = 4168889) B4168889
theorem B1853563 : Blo 1851627 1853563 := bstep (se 1 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 1853563 = 2780345) B2780345
theorem B135211139 : Blo 1851627 135211139 := bstep (se 1 (by rfl) ⟨101408354, by rfl⟩ : syracuseStep 135211139 = 202816709) B202816709
theorem B1853615 : Blo 1851627 1853615 := bstep (se 1 (by rfl) ⟨1390211, by rfl⟩ : syracuseStep 1853615 = 2780423) B2780423
theorem B2672839 : Blo 1851627 2672839 := bstep (se 1 (by rfl) ⟨2004629, by rfl⟩ : syracuseStep 2672839 = 4009259) B4009259
theorem B2779385 : Blo 1851627 2779385 := bstep (se 2 (by rfl) ⟨1042269, by rfl⟩ : syracuseStep 2779385 = 2084539) B2084539
theorem B22546775 : Blo 1851627 22546775 := bstep (se 1 (by rfl) ⟨16910081, by rfl⟩ : syracuseStep 22546775 = 33820163) B33820163
theorem B2779487 : Blo 1851627 2779487 := bstep (se 1 (by rfl) ⟨2084615, by rfl⟩ : syracuseStep 2779487 = 4169231) B4169231
theorem B2779499 : Blo 1851627 2779499 := bstep (se 1 (by rfl) ⟨2084624, by rfl⟩ : syracuseStep 2779499 = 4169249) B4169249
theorem B6252929 : Blo 1851627 6252929 := bstep (se 2 (by rfl) ⟨2344848, by rfl⟩ : syracuseStep 6252929 = 4689697) B4689697
theorem B3516833 : Blo 1851627 3516833 := bstep (se 2 (by rfl) ⟨1318812, by rfl⟩ : syracuseStep 3516833 = 2637625) B2637625
theorem B2967995 : Blo 1851627 2967995 := bstep (se 1 (by rfl) ⟨2225996, by rfl⟩ : syracuseStep 2967995 = 4451993) B4451993
theorem B10553915 : Blo 1851627 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B2779727 : Blo 1851627 2779727 := bstep (se 1 (by rfl) ⟨2084795, by rfl⟩ : syracuseStep 2779727 = 4169591) B4169591
theorem B6097555 : Blo 1851627 6097555 := bstep (se 1 (by rfl) ⟨4573166, by rfl⟩ : syracuseStep 6097555 = 9146333) B9146333
theorem B2779847 : Blo 1851627 2779847 := bstep (se 1 (by rfl) ⟨2084885, by rfl⟩ : syracuseStep 2779847 = 4169771) B4169771
theorem B10545875 : Blo 1851627 10545875 := bstep (se 1 (by rfl) ⟨7909406, by rfl⟩ : syracuseStep 10545875 = 15818813) B15818813
theorem B3517175 : Blo 1851627 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B2780009 : Blo 1851627 2780009 := bstep (se 2 (by rfl) ⟨1042503, by rfl⟩ : syracuseStep 2780009 = 2085007) B2085007
theorem B30043025 : Blo 1851627 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B2780087 : Blo 1851627 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B2780123 : Blo 1851627 2780123 := bstep (se 1 (by rfl) ⟨2085092, by rfl⟩ : syracuseStep 2780123 = 4170185) B4170185
theorem B9022465 : Blo 1851627 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B2083963 : Blo 1851627 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B2968699 : Blo 1851627 2968699 := bstep (se 1 (by rfl) ⟨2226524, by rfl⟩ : syracuseStep 2968699 = 4453049) B4453049
theorem B5008555 : Blo 1851627 5008555 := bstep (se 1 (by rfl) ⟨3756416, by rfl⟩ : syracuseStep 5008555 = 7512833) B7512833
theorem B6253739 : Blo 1851627 6253739 := bstep (se 1 (by rfl) ⟨4690304, by rfl⟩ : syracuseStep 6253739 = 9380609) B9380609
theorem B7032055 : Blo 1851627 7032055 := bstep (se 1 (by rfl) ⟨5274041, by rfl⟩ : syracuseStep 7032055 = 10548083) B10548083
theorem B9375101 : Blo 1851627 9375101 := bstep (se 3 (by rfl) ⟨1757831, by rfl⟩ : syracuseStep 9375101 = 3515663) B3515663
theorem B16043507 : Blo 1851627 16043507 := bstep (se 1 (by rfl) ⟨12032630, by rfl⟩ : syracuseStep 16043507 = 24065261) B24065261
theorem B7032329 : Blo 1851627 7032329 := bstep (se 2 (by rfl) ⟨2637123, by rfl⟩ : syracuseStep 7032329 = 5274247) B5274247
theorem B3255817 : Blo 1851627 3255817 := bstep (se 2 (by rfl) ⟨1220931, by rfl⟩ : syracuseStep 3255817 = 2441863) B2441863
theorem B7032359 : Blo 1851627 7032359 := bstep (se 1 (by rfl) ⟨5274269, by rfl⟩ : syracuseStep 7032359 = 10548539) B10548539
theorem B2084431 : Blo 1851627 2084431 := bstep (se 1 (by rfl) ⟨1563323, by rfl⟩ : syracuseStep 2084431 = 3126647) B3126647
theorem B7507579 : Blo 1851627 7507579 := bstep (se 1 (by rfl) ⟨5630684, by rfl⟩ : syracuseStep 7507579 = 11261369) B11261369
theorem B19017355 : Blo 1851627 19017355 := bstep (se 1 (by rfl) ⟨14263016, by rfl⟩ : syracuseStep 19017355 = 28526033) B28526033
theorem B6254279 : Blo 1851627 6254279 := bstep (se 1 (by rfl) ⟨4690709, by rfl⟩ : syracuseStep 6254279 = 9381419) B9381419
theorem B13348651 : Blo 1851627 13348651 := bstep (se 1 (by rfl) ⟨10011488, by rfl⟩ : syracuseStep 13348651 = 20022977) B20022977
theorem B3338057 : Blo 1851627 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B3125135 : Blo 1851627 3125135 := bstep (se 1 (by rfl) ⟨2343851, by rfl⟩ : syracuseStep 3125135 = 4687703) B4687703
theorem B4689839 : Blo 1851627 4689839 := bstep (se 1 (by rfl) ⟨3517379, by rfl⟩ : syracuseStep 4689839 = 7034759) B7034759
theorem B2084827 : Blo 1851627 2084827 := bstep (se 1 (by rfl) ⟨1563620, by rfl⟩ : syracuseStep 2084827 = 3127241) B3127241
theorem B3518473 : Blo 1851627 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B3125371 : Blo 1851627 3125371 := bstep (se 1 (by rfl) ⟨2344028, by rfl⟩ : syracuseStep 3125371 = 4688057) B4688057
theorem B6336683 : Blo 1851627 6336683 := bstep (se 1 (by rfl) ⟨4752512, by rfl⟩ : syracuseStep 6336683 = 9505025) B9505025
theorem B45674675 : Blo 1851627 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B7033027 : Blo 1851627 7033027 := bstep (se 1 (by rfl) ⟨5274770, by rfl⟩ : syracuseStep 7033027 = 10549541) B10549541
theorem B3518815 : Blo 1851627 3518815 := bstep (se 1 (by rfl) ⟨2639111, by rfl⟩ : syracuseStep 3518815 = 5278223) B5278223
theorem B2503019 : Blo 1851627 2503019 := bstep (se 1 (by rfl) ⟨1877264, by rfl⟩ : syracuseStep 2503019 = 3754529) B3754529
theorem B2085295 : Blo 1851627 2085295 := bstep (se 1 (by rfl) ⟨1563971, by rfl⟩ : syracuseStep 2085295 = 3127943) B3127943
theorem B11866571 : Blo 1851627 11866571 := bstep (se 1 (by rfl) ⟨8899928, by rfl⟩ : syracuseStep 11866571 = 17799857) B17799857
theorem B7033331 : Blo 1851627 7033331 := bstep (se 1 (by rfl) ⟨5274998, by rfl⟩ : syracuseStep 7033331 = 10549997) B10549997
theorem B4690457 : Blo 1851627 4690457 := bstep (se 2 (by rfl) ⟨1758921, by rfl⟩ : syracuseStep 4690457 = 3517843) B3517843
theorem B2224679 : Blo 1851627 2224679 := bstep (se 1 (by rfl) ⟨1668509, by rfl⟩ : syracuseStep 2224679 = 3337019) B3337019
theorem B5935655 : Blo 1851627 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B6255143 : Blo 1851627 6255143 := bstep (se 1 (by rfl) ⟨4691357, by rfl⟩ : syracuseStep 6255143 = 9382715) B9382715
theorem B6255251 : Blo 1851627 6255251 := bstep (se 1 (by rfl) ⟨4691438, by rfl⟩ : syracuseStep 6255251 = 9382877) B9382877
theorem B14062409 : Blo 1851627 14062409 := bstep (se 2 (by rfl) ⟨5273403, by rfl⟩ : syracuseStep 14062409 = 10546807) B10546807
theorem B4166495 : Blo 1851627 4166495 := bstep (se 1 (by rfl) ⟨3124871, by rfl⟩ : syracuseStep 4166495 = 6249743) B6249743
theorem B6255467 : Blo 1851627 6255467 := bstep (se 1 (by rfl) ⟨4691600, by rfl⟩ : syracuseStep 6255467 = 9383201) B9383201
theorem B57013145 : Blo 1851627 57013145 := bstep (se 2 (by rfl) ⟨21379929, by rfl⟩ : syracuseStep 57013145 = 42759859) B42759859
theorem B6255521 : Blo 1851627 6255521 := bstep (se 2 (by rfl) ⟨2345820, by rfl⟩ : syracuseStep 6255521 = 4691641) B4691641
theorem B7033787 : Blo 1851627 7033787 := bstep (se 1 (by rfl) ⟨5275340, by rfl⟩ : syracuseStep 7033787 = 10550681) B10550681
theorem B3126235 : Blo 1851627 3126235 := bstep (se 1 (by rfl) ⟨2344676, by rfl⟩ : syracuseStep 3126235 = 4689353) B4689353
theorem B4166675 : Blo 1851627 4166675 := bstep (se 1 (by rfl) ⟨3125006, by rfl⟩ : syracuseStep 4166675 = 6250013) B6250013
theorem B18043955 : Blo 1851627 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B7132217 : Blo 1851627 7132217 := bstep (se 2 (by rfl) ⟨2674581, by rfl⟩ : syracuseStep 7132217 = 5349163) B5349163
theorem B2503759 : Blo 1851627 2503759 := bstep (se 1 (by rfl) ⟨1877819, by rfl⟩ : syracuseStep 2503759 = 3755639) B3755639
theorem B89158805 : Blo 1851627 89158805 := bstep (se 6 (by rfl) ⟨2089659, by rfl⟩ : syracuseStep 89158805 = 4179319) B4179319
theorem B4167017 : Blo 1851627 4167017 := bstep (se 2 (by rfl) ⟨1562631, by rfl⟩ : syracuseStep 4167017 = 3125263) B3125263
theorem B5633545 : Blo 1851627 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B3126863 : Blo 1851627 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B7509719 : Blo 1851627 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B11876129 : Blo 1851627 11876129 := bstep (se 2 (by rfl) ⟨4453548, by rfl⟩ : syracuseStep 11876129 = 8907097) B8907097
theorem B48133931 : Blo 1851627 48133931 := bstep (se 1 (by rfl) ⟨36100448, by rfl⟩ : syracuseStep 48133931 = 72200897) B72200897
theorem B13358915 : Blo 1851627 13358915 := bstep (se 1 (by rfl) ⟨10019186, by rfl⟩ : syracuseStep 13358915 = 20038373) B20038373
theorem B4167611 : Blo 1851627 4167611 := bstep (se 1 (by rfl) ⟨3125708, by rfl⟩ : syracuseStep 4167611 = 6251417) B6251417
theorem B10991623 : Blo 1851627 10991623 := bstep (se 1 (by rfl) ⟨8243717, by rfl⟩ : syracuseStep 10991623 = 16487435) B16487435
theorem B114071597 : Blo 1851627 114071597 := bstep (se 3 (by rfl) ⟨21388424, by rfl⟩ : syracuseStep 114071597 = 42776849) B42776849
theorem B4167737 : Blo 1851627 4167737 := bstep (se 2 (by rfl) ⟨1562901, by rfl⟩ : syracuseStep 4167737 = 3125803) B3125803
theorem B7510097 : Blo 1851627 7510097 := bstep (se 2 (by rfl) ⟨2816286, by rfl⟩ : syracuseStep 7510097 = 5632573) B5632573
theorem B22526041 : Blo 1851627 22526041 := bstep (se 2 (by rfl) ⟨8447265, by rfl⟩ : syracuseStep 22526041 = 16894531) B16894531
theorem B101374193 : Blo 1851627 101374193 := bstep (se 2 (by rfl) ⟨38015322, by rfl⟩ : syracuseStep 101374193 = 76030645) B76030645
theorem B4225385 : Blo 1851627 4225385 := bstep (se 2 (by rfl) ⟨1584519, by rfl⟩ : syracuseStep 4225385 = 3169039) B3169039
theorem B4168079 : Blo 1851627 4168079 := bstep (se 1 (by rfl) ⟨3126059, by rfl⟩ : syracuseStep 4168079 = 6252119) B6252119
theorem B3127727 : Blo 1851627 3127727 := bstep (se 1 (by rfl) ⟨2345795, by rfl⟩ : syracuseStep 3127727 = 4691591) B4691591
theorem B2226727 : Blo 1851627 2226727 := bstep (se 1 (by rfl) ⟨1670045, by rfl⟩ : syracuseStep 2226727 = 3340091) B3340091
theorem B13539899 : Blo 1851627 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B4168403 : Blo 1851627 4168403 := bstep (se 1 (by rfl) ⟨3126302, by rfl⟩ : syracuseStep 4168403 = 6252605) B6252605
theorem B6249311 : Blo 1851627 6249311 := bstep (se 1 (by rfl) ⟨4686983, by rfl⟩ : syracuseStep 6249311 = 9373967) B9373967
theorem B2636651 : Blo 1851627 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B5938039 : Blo 1851627 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B6249473 : Blo 1851627 6249473 := bstep (se 2 (by rfl) ⟨2343552, by rfl⟩ : syracuseStep 6249473 = 4687105) B4687105
theorem B3169451 : Blo 1851627 3169451 := bstep (se 1 (by rfl) ⟨2377088, by rfl⟩ : syracuseStep 3169451 = 4754177) B4754177
theorem B7036247 : Blo 1851627 7036247 := bstep (se 1 (by rfl) ⟨5277185, by rfl⟩ : syracuseStep 7036247 = 10554371) B10554371
theorem B4169339 : Blo 1851627 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B9379475 : Blo 1851627 9379475 := bstep (se 1 (by rfl) ⟨7034606, by rfl⟩ : syracuseStep 9379475 = 14069213) B14069213
theorem B10550999 : Blo 1851627 10550999 := bstep (se 1 (by rfl) ⟨7913249, by rfl⟩ : syracuseStep 10550999 = 15826499) B15826499
theorem B10698461 : Blo 1851627 10698461 := bstep (se 3 (by rfl) ⟨2005961, by rfl⟩ : syracuseStep 10698461 = 4011923) B4011923
theorem B4169465 : Blo 1851627 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B6250283 : Blo 1851627 6250283 := bstep (se 1 (by rfl) ⟨4687712, by rfl⟩ : syracuseStep 6250283 = 9375425) B9375425
theorem B14262151 : Blo 1851627 14262151 := bstep (se 1 (by rfl) ⟨10696613, by rfl⟩ : syracuseStep 14262151 = 21393227) B21393227
theorem B14655497 : Blo 1851627 14655497 := bstep (se 2 (by rfl) ⟨5495811, by rfl⟩ : syracuseStep 14655497 = 10991623) B10991623
theorem B30441491 : Blo 1851627 30441491 := bstep (se 1 (by rfl) ⟨22831118, by rfl⟩ : syracuseStep 30441491 = 45662237) B45662237
theorem B30449783 : Blo 1851627 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B3563785 : Blo 1851627 3563785 := bstep (se 2 (by rfl) ⟨1336419, by rfl⟩ : syracuseStep 3563785 = 2672839) B2672839
theorem B1851679 : Blo 1851627 1851679 := bstep (se 1 (by rfl) ⟨1388759, by rfl⟩ : syracuseStep 1851679 = 2777519) B2777519
theorem B22544689 : Blo 1851627 22544689 := bstep (se 2 (by rfl) ⟨8454258, by rfl⟩ : syracuseStep 22544689 = 16908517) B16908517
theorem B1851739 : Blo 1851627 1851739 := bstep (se 1 (by rfl) ⟨1388804, by rfl⟩ : syracuseStep 1851739 = 2777609) B2777609
theorem B1851759 : Blo 1851627 1851759 := bstep (se 1 (by rfl) ⟨1388819, by rfl⟩ : syracuseStep 1851759 = 2777639) B2777639
theorem B3957103 : Blo 1851627 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B4170095 : Blo 1851627 4170095 := bstep (se 1 (by rfl) ⟨3127571, by rfl⟩ : syracuseStep 4170095 = 6255143) B6255143
theorem B1851815 : Blo 1851627 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B4170167 : Blo 1851627 4170167 := bstep (se 1 (by rfl) ⟨3127625, by rfl⟩ : syracuseStep 4170167 = 6255251) B6255251
theorem B1851899 : Blo 1851627 1851899 := bstep (se 1 (by rfl) ⟨1388924, by rfl⟩ : syracuseStep 1851899 = 2777849) B2777849
theorem B2343487 : Blo 1851627 2343487 := bstep (se 1 (by rfl) ⟨1757615, by rfl⟩ : syracuseStep 2343487 = 3515231) B3515231
theorem B2777663 : Blo 1851627 2777663 := bstep (se 1 (by rfl) ⟨2083247, by rfl⟩ : syracuseStep 2777663 = 4166495) B4166495
theorem B1851967 : Blo 1851627 1851967 := bstep (se 1 (by rfl) ⟨1388975, by rfl⟩ : syracuseStep 1851967 = 2777951) B2777951
theorem B1851975 : Blo 1851627 1851975 := bstep (se 1 (by rfl) ⟨1388981, by rfl⟩ : syracuseStep 1851975 = 2777963) B2777963
theorem B4170311 : Blo 1851627 4170311 := bstep (se 1 (by rfl) ⟨3127733, by rfl⟩ : syracuseStep 4170311 = 6255467) B6255467
theorem B4170347 : Blo 1851627 4170347 := bstep (se 1 (by rfl) ⟨3127760, by rfl⟩ : syracuseStep 4170347 = 6255521) B6255521
theorem B2777783 : Blo 1851627 2777783 := bstep (se 1 (by rfl) ⟨2083337, by rfl⟩ : syracuseStep 2777783 = 4166675) B4166675
theorem B1852127 : Blo 1851627 1852127 := bstep (se 1 (by rfl) ⟨1389095, by rfl⟩ : syracuseStep 1852127 = 2778191) B2778191
theorem B1852207 : Blo 1851627 1852207 := bstep (se 1 (by rfl) ⟨1389155, by rfl⟩ : syracuseStep 1852207 = 2778311) B2778311
theorem B2778011 : Blo 1851627 2778011 := bstep (se 1 (by rfl) ⟨2083508, by rfl⟩ : syracuseStep 2778011 = 4167017) B4167017
theorem B1852315 : Blo 1851627 1852315 := bstep (se 1 (by rfl) ⟨1389236, by rfl⟩ : syracuseStep 1852315 = 2778473) B2778473
theorem B2638747 : Blo 1851627 2638747 := bstep (se 1 (by rfl) ⟨1979060, by rfl⟩ : syracuseStep 2638747 = 3958121) B3958121
theorem B1852367 : Blo 1851627 1852367 := bstep (se 1 (by rfl) ⟨1389275, by rfl⟩ : syracuseStep 1852367 = 2778551) B2778551
theorem B1852391 : Blo 1851627 1852391 := bstep (se 1 (by rfl) ⟨1389293, by rfl⟩ : syracuseStep 1852391 = 2778587) B2778587
theorem B5006479 : Blo 1851627 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B8905943 : Blo 1851627 8905943 := bstep (se 1 (by rfl) ⟨6679457, by rfl⟩ : syracuseStep 8905943 = 13358915) B13358915
theorem B1852703 : Blo 1851627 1852703 := bstep (se 1 (by rfl) ⟨1389527, by rfl⟩ : syracuseStep 1852703 = 2779055) B2779055
theorem B2344231 : Blo 1851627 2344231 := bstep (se 1 (by rfl) ⟨1758173, by rfl⟩ : syracuseStep 2344231 = 3516347) B3516347
theorem B2778407 : Blo 1851627 2778407 := bstep (se 1 (by rfl) ⟨2083805, by rfl⟩ : syracuseStep 2778407 = 4167611) B4167611
theorem B1852763 : Blo 1851627 1852763 := bstep (se 1 (by rfl) ⟨1389572, by rfl⟩ : syracuseStep 1852763 = 2779145) B2779145
theorem B1852783 : Blo 1851627 1852783 := bstep (se 1 (by rfl) ⟨1389587, by rfl⟩ : syracuseStep 1852783 = 2779175) B2779175
theorem B76047731 : Blo 1851627 76047731 := bstep (se 1 (by rfl) ⟨57035798, by rfl⟩ : syracuseStep 76047731 = 114071597) B114071597
theorem B2778491 : Blo 1851627 2778491 := bstep (se 1 (by rfl) ⟨2083868, by rfl⟩ : syracuseStep 2778491 = 4167737) B4167737
theorem B5006731 : Blo 1851627 5006731 := bstep (se 1 (by rfl) ⟨3755048, by rfl⟩ : syracuseStep 5006731 = 7510097) B7510097
theorem B9504161 : Blo 1851627 9504161 := bstep (se 2 (by rfl) ⟨3564060, by rfl⟩ : syracuseStep 9504161 = 7128121) B7128121
theorem B1852839 : Blo 1851627 1852839 := bstep (se 1 (by rfl) ⟨1389629, by rfl⟩ : syracuseStep 1852839 = 2779259) B2779259
theorem B5932477 : Blo 1851627 5932477 := bstep (se 3 (by rfl) ⟨1112339, by rfl⟩ : syracuseStep 5932477 = 2224679) B2224679
theorem B2778617 : Blo 1851627 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B3958265 : Blo 1851627 3958265 := bstep (se 2 (by rfl) ⟨1484349, by rfl⟩ : syracuseStep 3958265 = 2968699) B2968699
theorem B1852923 : Blo 1851627 1852923 := bstep (se 1 (by rfl) ⟨1389692, by rfl⟩ : syracuseStep 1852923 = 2779385) B2779385
theorem B6678073 : Blo 1851627 6678073 := bstep (se 2 (by rfl) ⟨2504277, by rfl⟩ : syracuseStep 6678073 = 5008555) B5008555
theorem B1852991 : Blo 1851627 1852991 := bstep (se 1 (by rfl) ⟨1389743, by rfl⟩ : syracuseStep 1852991 = 2779487) B2779487
theorem B1852999 : Blo 1851627 1852999 := bstep (se 1 (by rfl) ⟨1389749, by rfl⟩ : syracuseStep 1852999 = 2779499) B2779499
theorem B2778719 : Blo 1851627 2778719 := bstep (se 1 (by rfl) ⟨2084039, by rfl⟩ : syracuseStep 2778719 = 4168079) B4168079
theorem B2344555 : Blo 1851627 2344555 := bstep (se 1 (by rfl) ⟨1758416, by rfl⟩ : syracuseStep 2344555 = 3516833) B3516833
theorem B1853151 : Blo 1851627 1853151 := bstep (se 1 (by rfl) ⟨1389863, by rfl⟩ : syracuseStep 1853151 = 2779727) B2779727
theorem B1853231 : Blo 1851627 1853231 := bstep (se 1 (by rfl) ⟨1389923, by rfl⟩ : syracuseStep 1853231 = 2779847) B2779847
theorem B7030583 : Blo 1851627 7030583 := bstep (se 1 (by rfl) ⟨5272937, by rfl⟩ : syracuseStep 7030583 = 10545875) B10545875
theorem B2778935 : Blo 1851627 2778935 := bstep (se 1 (by rfl) ⟨2084201, by rfl⟩ : syracuseStep 2778935 = 4168403) B4168403
theorem B2344783 : Blo 1851627 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B1853339 : Blo 1851627 1853339 := bstep (se 1 (by rfl) ⟨1390004, by rfl⟩ : syracuseStep 1853339 = 2780009) B2780009
theorem B1853391 : Blo 1851627 1853391 := bstep (se 1 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 1853391 = 2780087) B2780087
theorem B1853415 : Blo 1851627 1853415 := bstep (se 1 (by rfl) ⟨1390061, by rfl⟩ : syracuseStep 1853415 = 2780123) B2780123
theorem B2779241 : Blo 1851627 2779241 := bstep (se 2 (by rfl) ⟨1042215, by rfl⟩ : syracuseStep 2779241 = 2084431) B2084431
theorem B25356473 : Blo 1851627 25356473 := bstep (se 2 (by rfl) ⟨9508677, by rfl⟩ : syracuseStep 25356473 = 19017355) B19017355
theorem B10553597 : Blo 1851627 10553597 := bstep (se 3 (by rfl) ⟨1978799, by rfl⟩ : syracuseStep 10553597 = 3957599) B3957599
theorem B7031069 : Blo 1851627 7031069 := bstep (se 3 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 7031069 = 2636651) B2636651
theorem B4688219 : Blo 1851627 4688219 := bstep (se 1 (by rfl) ⟨3516164, by rfl⟩ : syracuseStep 4688219 = 7032329) B7032329
theorem B4688239 : Blo 1851627 4688239 := bstep (se 1 (by rfl) ⟨3516179, by rfl⟩ : syracuseStep 4688239 = 7032359) B7032359
theorem B2779559 : Blo 1851627 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B96299437 : Blo 1851627 96299437 := bstep (se 3 (by rfl) ⟨18056144, by rfl⟩ : syracuseStep 96299437 = 36112289) B36112289
theorem B6252983 : Blo 1851627 6252983 := bstep (se 1 (by rfl) ⟨4689737, by rfl⟩ : syracuseStep 6252983 = 9379475) B9379475
theorem B2779643 : Blo 1851627 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B19016201 : Blo 1851627 19016201 := bstep (se 2 (by rfl) ⟨7131075, by rfl⟩ : syracuseStep 19016201 = 14262151) B14262151
theorem B2083423 : Blo 1851627 2083423 := bstep (se 1 (by rfl) ⟨1562567, by rfl⟩ : syracuseStep 2083423 = 3125135) B3125135
theorem B2779769 : Blo 1851627 2779769 := bstep (se 2 (by rfl) ⟨1042413, by rfl⟩ : syracuseStep 2779769 = 2084827) B2084827
theorem B2779823 : Blo 1851627 2779823 := bstep (se 1 (by rfl) ⟨2084867, by rfl⟩ : syracuseStep 2779823 = 4169735) B4169735
theorem B2779871 : Blo 1851627 2779871 := bstep (se 1 (by rfl) ⟨2084903, by rfl⟩ : syracuseStep 2779871 = 4169807) B4169807
theorem B30034721 : Blo 1851627 30034721 := bstep (se 2 (by rfl) ⟨11263020, by rfl⟩ : syracuseStep 30034721 = 22526041) B22526041
theorem B2780135 : Blo 1851627 2780135 := bstep (se 1 (by rfl) ⟨2085101, by rfl⟩ : syracuseStep 2780135 = 4170203) B4170203
theorem B4688887 : Blo 1851627 4688887 := bstep (se 1 (by rfl) ⟨3516665, by rfl⟩ : syracuseStep 4688887 = 7033331) B7033331
theorem B9374939 : Blo 1851627 9374939 := bstep (se 1 (by rfl) ⟨7031204, by rfl⟩ : syracuseStep 9374939 = 14062409) B14062409
theorem B2780393 : Blo 1851627 2780393 := bstep (se 2 (by rfl) ⟨1042647, by rfl⟩ : syracuseStep 2780393 = 2085295) B2085295
theorem B4689191 : Blo 1851627 4689191 := bstep (se 1 (by rfl) ⟨3516893, by rfl⟩ : syracuseStep 4689191 = 7033787) B7033787
theorem B12029303 : Blo 1851627 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B2968969 : Blo 1851627 2968969 := bstep (se 2 (by rfl) ⟨1113363, by rfl⟩ : syracuseStep 2968969 = 2226727) B2226727
theorem B8130073 : Blo 1851627 8130073 := bstep (se 2 (by rfl) ⟨3048777, by rfl⟩ : syracuseStep 8130073 = 6097555) B6097555
theorem B5008979 : Blo 1851627 5008979 := bstep (se 1 (by rfl) ⟨3756734, by rfl⟩ : syracuseStep 5008979 = 7513469) B7513469
theorem B3124831 : Blo 1851627 3124831 := bstep (se 1 (by rfl) ⟨2343623, by rfl⟩ : syracuseStep 3124831 = 4687247) B4687247
theorem B4451935 : Blo 1851627 4451935 := bstep (se 1 (by rfl) ⟨3338951, by rfl⟩ : syracuseStep 4451935 = 6677903) B6677903
theorem B11267693 : Blo 1851627 11267693 := bstep (se 3 (by rfl) ⟨2112692, by rfl⟩ : syracuseStep 11267693 = 4225385) B4225385
theorem B2084575 : Blo 1851627 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B9383687 : Blo 1851627 9383687 := bstep (se 1 (by rfl) ⟨7037765, by rfl⟩ : syracuseStep 9383687 = 14075531) B14075531
theorem B3125047 : Blo 1851627 3125047 := bstep (se 1 (by rfl) ⟨2343785, by rfl⟩ : syracuseStep 3125047 = 4687571) B4687571
theorem B7917385 : Blo 1851627 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B7917419 : Blo 1851627 7917419 := bstep (se 1 (by rfl) ⟨5938064, by rfl⟩ : syracuseStep 7917419 = 11876129) B11876129
theorem B12029953 : Blo 1851627 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B1129263119 : Blo 1851627 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B90140759 : Blo 1851627 90140759 := bstep (se 1 (by rfl) ⟨67605569, by rfl⟩ : syracuseStep 90140759 = 135211139) B135211139
theorem B3338345 : Blo 1851627 3338345 := bstep (se 2 (by rfl) ⟨1251879, by rfl⟩ : syracuseStep 3338345 = 2503759) B2503759
theorem B3125513 : Blo 1851627 3125513 := bstep (se 2 (by rfl) ⟨1172067, by rfl⟩ : syracuseStep 3125513 = 2344135) B2344135
theorem B2085151 : Blo 1851627 2085151 := bstep (se 1 (by rfl) ⟨1563863, by rfl⟩ : syracuseStep 2085151 = 3127727) B3127727
theorem B1978663 : Blo 1851627 1978663 := bstep (se 1 (by rfl) ⟨1483997, by rfl⟩ : syracuseStep 1978663 = 2967995) B2967995
theorem B9376073 : Blo 1851627 9376073 := bstep (se 2 (by rfl) ⟨3516027, by rfl⟩ : syracuseStep 9376073 = 7032055) B7032055
theorem B4166207 : Blo 1851627 4166207 := bstep (se 1 (by rfl) ⟨3124655, by rfl⟩ : syracuseStep 4166207 = 6249311) B6249311
theorem B4166315 : Blo 1851627 4166315 := bstep (se 1 (by rfl) ⟨3124736, by rfl⟩ : syracuseStep 4166315 = 6249473) B6249473
theorem B128357149 : Blo 1851627 128357149 := bstep (se 3 (by rfl) ⟨24066965, by rfl⟩ : syracuseStep 128357149 = 48133931) B48133931
theorem B8901485 : Blo 1851627 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B4690831 : Blo 1851627 4690831 := bstep (se 1 (by rfl) ⟨3518123, by rfl⟩ : syracuseStep 4690831 = 7036247) B7036247
theorem B10695671 : Blo 1851627 10695671 := bstep (se 1 (by rfl) ⟨8021753, by rfl⟩ : syracuseStep 10695671 = 16043507) B16043507
theorem B17798201 : Blo 1851627 17798201 := bstep (se 2 (by rfl) ⟨6674325, by rfl⟩ : syracuseStep 17798201 = 13348651) B13348651
theorem B7033999 : Blo 1851627 7033999 := bstep (se 1 (by rfl) ⟨5275499, by rfl⟩ : syracuseStep 7033999 = 10550999) B10550999
theorem B7132307 : Blo 1851627 7132307 := bstep (se 1 (by rfl) ⟨5349230, by rfl⟩ : syracuseStep 7132307 = 10698461) B10698461
theorem B4166855 : Blo 1851627 4166855 := bstep (se 1 (by rfl) ⟨3125141, by rfl⟩ : syracuseStep 4166855 = 6250283) B6250283
theorem B3126505 : Blo 1851627 3126505 := bstep (se 2 (by rfl) ⟨1172439, by rfl⟩ : syracuseStep 3126505 = 2344879) B2344879
theorem B3126559 : Blo 1851627 3126559 := bstep (se 1 (by rfl) ⟨2344919, by rfl⟩ : syracuseStep 3126559 = 4689839) B4689839
theorem B4691297 : Blo 1851627 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B4167035 : Blo 1851627 4167035 := bstep (se 1 (by rfl) ⟨3125276, by rfl⟩ : syracuseStep 4167035 = 6250553) B6250553
theorem B7034273 : Blo 1851627 7034273 := bstep (se 2 (by rfl) ⟨2637852, by rfl⟩ : syracuseStep 7034273 = 5275705) B5275705
theorem B4224455 : Blo 1851627 4224455 := bstep (se 1 (by rfl) ⟨3168341, by rfl⟩ : syracuseStep 4224455 = 6336683) B6336683
theorem B4167161 : Blo 1851627 4167161 := bstep (se 2 (by rfl) ⟨1562685, by rfl⟩ : syracuseStep 4167161 = 3125371) B3125371
theorem B15832583 : Blo 1851627 15832583 := bstep (se 1 (by rfl) ⟨11874437, by rfl⟩ : syracuseStep 15832583 = 23748875) B23748875
theorem B4167251 : Blo 1851627 4167251 := bstep (se 1 (by rfl) ⟨3125438, by rfl⟩ : syracuseStep 4167251 = 6250877) B6250877
theorem B9377369 : Blo 1851627 9377369 := bstep (se 2 (by rfl) ⟨3516513, by rfl⟩ : syracuseStep 9377369 = 7033027) B7033027
theorem B7911047 : Blo 1851627 7911047 := bstep (se 1 (by rfl) ⟨5933285, by rfl⟩ : syracuseStep 7911047 = 11866571) B11866571
theorem B3126971 : Blo 1851627 3126971 := bstep (se 1 (by rfl) ⟨2345228, by rfl⟩ : syracuseStep 3126971 = 4690457) B4690457
theorem B4167431 : Blo 1851627 4167431 := bstep (se 1 (by rfl) ⟨3125573, by rfl⟩ : syracuseStep 4167431 = 6251147) B6251147
theorem B4691753 : Blo 1851627 4691753 := bstep (se 2 (by rfl) ⟨1759407, by rfl⟩ : syracuseStep 4691753 = 3518815) B3518815
theorem B76076981 : Blo 1851627 76076981 := bstep (se 5 (by rfl) ⟨3566108, by rfl⟩ : syracuseStep 76076981 = 7132217) B7132217
theorem B38008763 : Blo 1851627 38008763 := bstep (se 1 (by rfl) ⟨28506572, by rfl⟩ : syracuseStep 38008763 = 57013145) B57013145
theorem B59439203 : Blo 1851627 59439203 := bstep (se 1 (by rfl) ⟨44579402, by rfl⟩ : syracuseStep 59439203 = 89158805) B89158805
theorem B11868439 : Blo 1851627 11868439 := bstep (se 1 (by rfl) ⟨8901329, by rfl⟩ : syracuseStep 11868439 = 17802659) B17802659
theorem B6674717 : Blo 1851627 6674717 := bstep (se 3 (by rfl) ⟨1251509, by rfl⟩ : syracuseStep 6674717 = 2503019) B2503019
theorem B6338845 : Blo 1851627 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B4168043 : Blo 1851627 4168043 := bstep (se 1 (by rfl) ⟨3126032, by rfl⟩ : syracuseStep 4168043 = 6252065) B6252065
theorem B4168187 : Blo 1851627 4168187 := bstep (se 1 (by rfl) ⟨3126140, by rfl⟩ : syracuseStep 4168187 = 6252281) B6252281
theorem B4168313 : Blo 1851627 4168313 := bstep (se 2 (by rfl) ⟨1563117, by rfl⟩ : syracuseStep 4168313 = 3126235) B3126235
theorem B4168367 : Blo 1851627 4168367 := bstep (se 1 (by rfl) ⟨3126275, by rfl⟩ : syracuseStep 4168367 = 6252551) B6252551
theorem B4168439 : Blo 1851627 4168439 := bstep (se 1 (by rfl) ⟨3126329, by rfl⟩ : syracuseStep 4168439 = 6252659) B6252659
theorem B5790455 : Blo 1851627 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B5937911 : Blo 1851627 5937911 := bstep (se 1 (by rfl) ⟨4453433, by rfl⟩ : syracuseStep 5937911 = 8906867) B8906867
theorem B67582795 : Blo 1851627 67582795 := bstep (se 1 (by rfl) ⟨50687096, by rfl⟩ : syracuseStep 67582795 = 101374193) B101374193
theorem B15031183 : Blo 1851627 15031183 := bstep (se 1 (by rfl) ⟨11273387, by rfl⟩ : syracuseStep 15031183 = 22546775) B22546775
theorem B4168619 : Blo 1851627 4168619 := bstep (se 1 (by rfl) ⟨3126464, by rfl⟩ : syracuseStep 4168619 = 6252929) B6252929
theorem B7035943 : Blo 1851627 7035943 := bstep (se 1 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 7035943 = 10553915) B10553915
theorem B9026599 : Blo 1851627 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B20028683 : Blo 1851627 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B4341089 : Blo 1851627 4341089 := bstep (se 2 (by rfl) ⟨1627908, by rfl⟩ : syracuseStep 4341089 = 3255817) B3255817
theorem B7511393 : Blo 1851627 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B2112967 : Blo 1851627 2112967 := bstep (se 1 (by rfl) ⟨1584725, by rfl⟩ : syracuseStep 2112967 = 3169451) B3169451
theorem B4169159 : Blo 1851627 4169159 := bstep (se 1 (by rfl) ⟨3126869, by rfl⟩ : syracuseStep 4169159 = 6253739) B6253739
theorem B10010105 : Blo 1851627 10010105 := bstep (se 2 (by rfl) ⟨3753789, by rfl⟩ : syracuseStep 10010105 = 7507579) B7507579
theorem B6250067 : Blo 1851627 6250067 := bstep (se 1 (by rfl) ⟨4687550, by rfl⟩ : syracuseStep 6250067 = 9375101) B9375101
theorem B4169519 : Blo 1851627 4169519 := bstep (se 1 (by rfl) ⟨3127139, by rfl⟩ : syracuseStep 4169519 = 6254279) B6254279
theorem B7036733 : Blo 1851627 7036733 := bstep (se 3 (by rfl) ⟨1319387, by rfl⟩ : syracuseStep 7036733 = 2638775) B2638775
theorem B16039937 : Blo 1851627 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B20299855 : Blo 1851627 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B6250715 : Blo 1851627 6250715 := bstep (se 1 (by rfl) ⟨4688036, by rfl⟩ : syracuseStep 6250715 = 9376073) B9376073
theorem B4751713 : Blo 1851627 4751713 := bstep (se 2 (by rfl) ⟨1781892, by rfl⟩ : syracuseStep 4751713 = 3563785) B3563785
theorem B2777471 : Blo 1851627 2777471 := bstep (se 1 (by rfl) ⟨2083103, by rfl⟩ : syracuseStep 2777471 = 4166207) B4166207
theorem B1851775 : Blo 1851627 1851775 := bstep (se 1 (by rfl) ⟨1388831, by rfl⟩ : syracuseStep 1851775 = 2777663) B2777663
theorem B2638217 : Blo 1851627 2638217 := bstep (se 2 (by rfl) ⟨989331, by rfl⟩ : syracuseStep 2638217 = 1978663) B1978663
theorem B2777543 : Blo 1851627 2777543 := bstep (se 1 (by rfl) ⟨2083157, by rfl⟩ : syracuseStep 2777543 = 4166315) B4166315
theorem B1851855 : Blo 1851627 1851855 := bstep (se 1 (by rfl) ⟨1388891, by rfl⟩ : syracuseStep 1851855 = 2777783) B2777783
theorem B6250985 : Blo 1851627 6250985 := bstep (se 2 (by rfl) ⟨2344119, by rfl⟩ : syracuseStep 6250985 = 4688239) B4688239
theorem B1852007 : Blo 1851627 1852007 := bstep (se 1 (by rfl) ⟨1389005, by rfl⟩ : syracuseStep 1852007 = 2778011) B2778011
theorem B2777897 : Blo 1851627 2777897 := bstep (se 2 (by rfl) ⟨1041711, by rfl⟩ : syracuseStep 2777897 = 2083423) B2083423
theorem B2777903 : Blo 1851627 2777903 := bstep (se 1 (by rfl) ⟨2083427, by rfl⟩ : syracuseStep 2777903 = 4166855) B4166855
theorem B1852271 : Blo 1851627 1852271 := bstep (se 1 (by rfl) ⟨1389203, by rfl⟩ : syracuseStep 1852271 = 2778407) B2778407
theorem B2778023 : Blo 1851627 2778023 := bstep (se 1 (by rfl) ⟨2083517, by rfl⟩ : syracuseStep 2778023 = 4167035) B4167035
theorem B1852327 : Blo 1851627 1852327 := bstep (se 1 (by rfl) ⟨1389245, by rfl⟩ : syracuseStep 1852327 = 2778491) B2778491
theorem B2778107 : Blo 1851627 2778107 := bstep (se 1 (by rfl) ⟨2083580, by rfl⟩ : syracuseStep 2778107 = 4167161) B4167161
theorem B1852411 : Blo 1851627 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B2778167 : Blo 1851627 2778167 := bstep (se 1 (by rfl) ⟨2083625, by rfl⟩ : syracuseStep 2778167 = 4167251) B4167251
theorem B6251579 : Blo 1851627 6251579 := bstep (se 1 (by rfl) ⟨4688684, by rfl⟩ : syracuseStep 6251579 = 9377369) B9377369
theorem B1852479 : Blo 1851627 1852479 := bstep (se 1 (by rfl) ⟨1389359, by rfl⟩ : syracuseStep 1852479 = 2778719) B2778719
theorem B2778287 : Blo 1851627 2778287 := bstep (se 1 (by rfl) ⟨2083715, by rfl⟩ : syracuseStep 2778287 = 4167431) B4167431
theorem B4687055 : Blo 1851627 4687055 := bstep (se 1 (by rfl) ⟨3515291, by rfl⟩ : syracuseStep 4687055 = 7030583) B7030583
theorem B1852623 : Blo 1851627 1852623 := bstep (se 1 (by rfl) ⟨1389467, by rfl⟩ : syracuseStep 1852623 = 2778935) B2778935
theorem B50717987 : Blo 1851627 50717987 := bstep (se 1 (by rfl) ⟨38038490, by rfl⟩ : syracuseStep 50717987 = 76076981) B76076981
theorem B25339175 : Blo 1851627 25339175 := bstep (se 1 (by rfl) ⟨19004381, by rfl⟩ : syracuseStep 25339175 = 38008763) B38008763
theorem B6251849 : Blo 1851627 6251849 := bstep (se 2 (by rfl) ⟨2344443, by rfl⟩ : syracuseStep 6251849 = 4688887) B4688887
theorem B9381257 : Blo 1851627 9381257 := bstep (se 2 (by rfl) ⟨3517971, by rfl⟩ : syracuseStep 9381257 = 7035943) B7035943
theorem B12035465 : Blo 1851627 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B39626135 : Blo 1851627 39626135 := bstep (se 1 (by rfl) ⟨29719601, by rfl⟩ : syracuseStep 39626135 = 59439203) B59439203
theorem B1852827 : Blo 1851627 1852827 := bstep (se 1 (by rfl) ⟨1389620, by rfl⟩ : syracuseStep 1852827 = 2779241) B2779241
theorem B4687379 : Blo 1851627 4687379 := bstep (se 1 (by rfl) ⟨3515534, by rfl⟩ : syracuseStep 4687379 = 7031069) B7031069
theorem B4449811 : Blo 1851627 4449811 := bstep (se 1 (by rfl) ⟨3337358, by rfl⟩ : syracuseStep 4449811 = 6674717) B6674717
theorem B2778695 : Blo 1851627 2778695 := bstep (se 1 (by rfl) ⟨2084021, by rfl⟩ : syracuseStep 2778695 = 4168043) B4168043
theorem B1853039 : Blo 1851627 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B2778791 : Blo 1851627 2778791 := bstep (se 1 (by rfl) ⟨2084093, by rfl⟩ : syracuseStep 2778791 = 4168187) B4168187
theorem B1853095 : Blo 1851627 1853095 := bstep (se 1 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 1853095 = 2779643) B2779643
theorem B2778875 : Blo 1851627 2778875 := bstep (se 1 (by rfl) ⟨2084156, by rfl⟩ : syracuseStep 2778875 = 4168313) B4168313
theorem B1853179 : Blo 1851627 1853179 := bstep (se 1 (by rfl) ⟨1389884, by rfl⟩ : syracuseStep 1853179 = 2779769) B2779769
theorem B2778911 : Blo 1851627 2778911 := bstep (se 1 (by rfl) ⟨2084183, by rfl⟩ : syracuseStep 2778911 = 4168367) B4168367
theorem B1853215 : Blo 1851627 1853215 := bstep (se 1 (by rfl) ⟨1389911, by rfl⟩ : syracuseStep 1853215 = 2779823) B2779823
theorem B1853247 : Blo 1851627 1853247 := bstep (se 1 (by rfl) ⟨1389935, by rfl⟩ : syracuseStep 1853247 = 2779871) B2779871
theorem B2778959 : Blo 1851627 2778959 := bstep (se 1 (by rfl) ⟨2084219, by rfl⟩ : syracuseStep 2778959 = 4168439) B4168439
theorem B3860303 : Blo 1851627 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B3958607 : Blo 1851627 3958607 := bstep (se 1 (by rfl) ⟨2968955, by rfl⟩ : syracuseStep 3958607 = 5937911) B5937911
theorem B3958625 : Blo 1851627 3958625 := bstep (se 2 (by rfl) ⟨1484484, by rfl⟩ : syracuseStep 3958625 = 2968969) B2968969
theorem B20023147 : Blo 1851627 20023147 := bstep (se 1 (by rfl) ⟨15017360, by rfl⟩ : syracuseStep 20023147 = 30034721) B30034721
theorem B21104549 : Blo 1851627 21104549 := bstep (se 4 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 21104549 = 3957103) B3957103
theorem B2779079 : Blo 1851627 2779079 := bstep (se 1 (by rfl) ⟨2084309, by rfl⟩ : syracuseStep 2779079 = 4168619) B4168619
theorem B1853423 : Blo 1851627 1853423 := bstep (se 1 (by rfl) ⟨1390067, by rfl⟩ : syracuseStep 1853423 = 2780135) B2780135
theorem B10840097 : Blo 1851627 10840097 := bstep (se 2 (by rfl) ⟨4065036, by rfl⟩ : syracuseStep 10840097 = 8130073) B8130073
theorem B1853595 : Blo 1851627 1853595 := bstep (se 1 (by rfl) ⟨1390196, by rfl⟩ : syracuseStep 1853595 = 2780393) B2780393
theorem B2894059 : Blo 1851627 2894059 := bstep (se 1 (by rfl) ⟨2170544, by rfl⟩ : syracuseStep 2894059 = 4341089) B4341089
theorem B5007595 : Blo 1851627 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B2779433 : Blo 1851627 2779433 := bstep (se 2 (by rfl) ⟨1042287, by rfl⟩ : syracuseStep 2779433 = 2084575) B2084575
theorem B2779439 : Blo 1851627 2779439 := bstep (se 1 (by rfl) ⟨2084579, by rfl⟩ : syracuseStep 2779439 = 4169159) B4169159
theorem B2779679 : Blo 1851627 2779679 := bstep (se 1 (by rfl) ⟨2084759, by rfl⟩ : syracuseStep 2779679 = 4169519) B4169519
theorem B5278279 : Blo 1851627 5278279 := bstep (se 1 (by rfl) ⟨3958709, by rfl⟩ : syracuseStep 5278279 = 7917419) B7917419
theorem B20294327 : Blo 1851627 20294327 := bstep (se 1 (by rfl) ⟨15220745, by rfl⟩ : syracuseStep 20294327 = 30441491) B30441491
theorem B2083675 : Blo 1851627 2083675 := bstep (se 1 (by rfl) ⟨1562756, by rfl⟩ : syracuseStep 2083675 = 3125513) B3125513
theorem B2780063 : Blo 1851627 2780063 := bstep (se 1 (by rfl) ⟨2085047, by rfl⟩ : syracuseStep 2780063 = 4170095) B4170095
theorem B2780111 : Blo 1851627 2780111 := bstep (se 1 (by rfl) ⟨2085083, by rfl⟩ : syracuseStep 2780111 = 4170167) B4170167
theorem B2780201 : Blo 1851627 2780201 := bstep (se 2 (by rfl) ⟨1042575, by rfl⟩ : syracuseStep 2780201 = 2085151) B2085151
theorem B2780207 : Blo 1851627 2780207 := bstep (se 1 (by rfl) ⟨2085155, by rfl⟩ : syracuseStep 2780207 = 4170311) B4170311
theorem B30059585 : Blo 1851627 30059585 := bstep (se 2 (by rfl) ⟨11272344, by rfl⟩ : syracuseStep 30059585 = 22544689) B22544689
theorem B2780231 : Blo 1851627 2780231 := bstep (se 1 (by rfl) ⟨2085173, by rfl⟩ : syracuseStep 2780231 = 4170347) B4170347
theorem B5934323 : Blo 1851627 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B7130447 : Blo 1851627 7130447 := bstep (se 1 (by rfl) ⟨5347835, by rfl⟩ : syracuseStep 7130447 = 10695671) B10695671
theorem B11865467 : Blo 1851627 11865467 := bstep (se 1 (by rfl) ⟨8899100, by rfl⟩ : syracuseStep 11865467 = 17798201) B17798201
theorem B3124649 : Blo 1851627 3124649 := bstep (se 2 (by rfl) ⟨1171743, by rfl⟩ : syracuseStep 3124649 = 2343487) B2343487
theorem B6336107 : Blo 1851627 6336107 := bstep (se 1 (by rfl) ⟨4752080, by rfl⟩ : syracuseStep 6336107 = 9504161) B9504161
theorem B4689515 : Blo 1851627 4689515 := bstep (se 1 (by rfl) ⟨3517136, by rfl⟩ : syracuseStep 4689515 = 7034273) B7034273
theorem B10555055 : Blo 1851627 10555055 := bstep (se 1 (by rfl) ⟨7916291, by rfl⟩ : syracuseStep 10555055 = 15832583) B15832583
theorem B171142865 : Blo 1851627 171142865 := bstep (se 2 (by rfl) ⟨64178574, by rfl⟩ : syracuseStep 171142865 = 128357149) B128357149
theorem B2084647 : Blo 1851627 2084647 := bstep (se 1 (by rfl) ⟨1563485, by rfl⟩ : syracuseStep 2084647 = 3126971) B3126971
theorem B6254441 : Blo 1851627 6254441 := bstep (se 2 (by rfl) ⟨2345415, by rfl⟩ : syracuseStep 6254441 = 4690831) B4690831
theorem B20041577 : Blo 1851627 20041577 := bstep (se 2 (by rfl) ⟨7515591, by rfl⟩ : syracuseStep 20041577 = 15031183) B15031183
theorem B3518329 : Blo 1851627 3518329 := bstep (se 2 (by rfl) ⟨1319373, by rfl⟩ : syracuseStep 3518329 = 2638747) B2638747
theorem B10555373 : Blo 1851627 10555373 := bstep (se 3 (by rfl) ⟨1979132, by rfl⟩ : syracuseStep 10555373 = 3958265) B3958265
theorem B16904315 : Blo 1851627 16904315 := bstep (se 1 (by rfl) ⟨12678236, by rfl⟩ : syracuseStep 16904315 = 25356473) B25356473
theorem B3125479 : Blo 1851627 3125479 := bstep (se 1 (by rfl) ⟨2344109, by rfl⟩ : syracuseStep 3125479 = 4688219) B4688219
theorem B12677467 : Blo 1851627 12677467 := bstep (se 1 (by rfl) ⟨9508100, by rfl⟩ : syracuseStep 12677467 = 19016201) B19016201
theorem B3125641 : Blo 1851627 3125641 := bstep (se 2 (by rfl) ⟨1172115, by rfl⟩ : syracuseStep 3125641 = 2344231) B2344231
theorem B7909969 : Blo 1851627 7909969 := bstep (se 2 (by rfl) ⟨2966238, by rfl⟩ : syracuseStep 7909969 = 5932477) B5932477
theorem B4166441 : Blo 1851627 4166441 := bstep (se 2 (by rfl) ⟨1562415, by rfl⟩ : syracuseStep 4166441 = 3124831) B3124831
theorem B5935913 : Blo 1851627 5935913 := bstep (se 2 (by rfl) ⟨2225967, by rfl⟩ : syracuseStep 5935913 = 4451935) B4451935
theorem B3126073 : Blo 1851627 3126073 := bstep (se 2 (by rfl) ⟨1172277, by rfl⟩ : syracuseStep 3126073 = 2344555) B2344555
theorem B3126127 : Blo 1851627 3126127 := bstep (se 1 (by rfl) ⟨2344595, by rfl⟩ : syracuseStep 3126127 = 4689191) B4689191
theorem B6673403 : Blo 1851627 6673403 := bstep (se 1 (by rfl) ⟨5005052, by rfl⟩ : syracuseStep 6673403 = 10010105) B10010105
theorem B4166711 : Blo 1851627 4166711 := bstep (se 1 (by rfl) ⟨3125033, by rfl⟩ : syracuseStep 4166711 = 6250067) B6250067
theorem B3339319 : Blo 1851627 3339319 := bstep (se 1 (by rfl) ⟨2504489, by rfl⟩ : syracuseStep 3339319 = 5008979) B5008979
theorem B4166729 : Blo 1851627 4166729 := bstep (se 2 (by rfl) ⟨1562523, by rfl⟩ : syracuseStep 4166729 = 3125047) B3125047
theorem B10556513 : Blo 1851627 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3126377 : Blo 1851627 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B6255791 : Blo 1851627 6255791 := bstep (se 1 (by rfl) ⟨4691843, by rfl⟩ : syracuseStep 6255791 = 9383687) B9383687
theorem B4691155 : Blo 1851627 4691155 := bstep (se 1 (by rfl) ⟨3518366, by rfl⟩ : syracuseStep 4691155 = 7036733) B7036733
theorem B752842079 : Blo 1851627 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B39081325 : Blo 1851627 39081325 := bstep (se 3 (by rfl) ⟨7327748, by rfl⟩ : syracuseStep 39081325 = 14655497) B14655497
theorem B60093839 : Blo 1851627 60093839 := bstep (se 1 (by rfl) ⟨45070379, by rfl⟩ : syracuseStep 60093839 = 90140759) B90140759
theorem B2225563 : Blo 1851627 2225563 := bstep (se 1 (by rfl) ⟨1669172, by rfl⟩ : syracuseStep 2225563 = 3338345) B3338345
theorem B15824585 : Blo 1851627 15824585 := bstep (se 2 (by rfl) ⟨5934219, by rfl⟩ : syracuseStep 15824585 = 11868439) B11868439
theorem B8451793 : Blo 1851627 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B19019485 : Blo 1851627 19019485 := bstep (se 3 (by rfl) ⟨3566153, by rfl⟩ : syracuseStep 19019485 = 7132307) B7132307
theorem B128399249 : Blo 1851627 128399249 := bstep (se 2 (by rfl) ⟨48149718, by rfl⟩ : syracuseStep 128399249 = 96299437) B96299437
theorem B5937295 : Blo 1851627 5937295 := bstep (se 1 (by rfl) ⟨4452971, by rfl⟩ : syracuseStep 5937295 = 8905943) B8905943
theorem B3127531 : Blo 1851627 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B50698487 : Blo 1851627 50698487 := bstep (se 1 (by rfl) ⟨38023865, by rfl⟩ : syracuseStep 50698487 = 76047731) B76047731
theorem B2816303 : Blo 1851627 2816303 := bstep (se 1 (by rfl) ⟨2112227, by rfl⟩ : syracuseStep 2816303 = 4224455) B4224455
theorem B5274031 : Blo 1851627 5274031 := bstep (se 1 (by rfl) ⟨3955523, by rfl⟩ : syracuseStep 5274031 = 7911047) B7911047
theorem B90110393 : Blo 1851627 90110393 := bstep (se 2 (by rfl) ⟨33791397, by rfl⟩ : syracuseStep 90110393 = 67582795) B67582795
theorem B3127835 : Blo 1851627 3127835 := bstep (se 1 (by rfl) ⟨2345876, by rfl⟩ : syracuseStep 3127835 = 4691753) B4691753
theorem B7035731 : Blo 1851627 7035731 := bstep (se 1 (by rfl) ⟨5276798, by rfl⟩ : syracuseStep 7035731 = 10553597) B10553597
theorem B6675305 : Blo 1851627 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B9378665 : Blo 1851627 9378665 := bstep (se 2 (by rfl) ⟨3516999, by rfl⟩ : syracuseStep 9378665 = 7033999) B7033999
theorem B4168655 : Blo 1851627 4168655 := bstep (se 1 (by rfl) ⟨3126491, by rfl⟩ : syracuseStep 4168655 = 6252983) B6252983
theorem B4168673 : Blo 1851627 4168673 := bstep (se 2 (by rfl) ⟨1563252, by rfl⟩ : syracuseStep 4168673 = 3126505) B3126505
theorem B4168745 : Blo 1851627 4168745 := bstep (se 2 (by rfl) ⟨1563279, by rfl⟩ : syracuseStep 4168745 = 3126559) B3126559
theorem B6675641 : Blo 1851627 6675641 := bstep (se 2 (by rfl) ⟨2503365, by rfl⟩ : syracuseStep 6675641 = 5006731) B5006731
theorem B2817289 : Blo 1851627 2817289 := bstep (se 2 (by rfl) ⟨1056483, by rfl⟩ : syracuseStep 2817289 = 2112967) B2112967
theorem B8904097 : Blo 1851627 8904097 := bstep (se 2 (by rfl) ⟨3339036, by rfl⟩ : syracuseStep 8904097 = 6678073) B6678073
theorem B6249959 : Blo 1851627 6249959 := bstep (se 1 (by rfl) ⟨4687469, by rfl⟩ : syracuseStep 6249959 = 9374939) B9374939
theorem B13352455 : Blo 1851627 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B8019535 : Blo 1851627 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B7511795 : Blo 1851627 7511795 := bstep (se 1 (by rfl) ⟨5633846, by rfl⟩ : syracuseStep 7511795 = 11267693) B11267693
theorem B71213093 : Blo 1851627 71213093 := bstep (se 4 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 71213093 = 13352455) B13352455
theorem B27066473 : Blo 1851627 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B1851647 : Blo 1851627 1851647 := bstep (se 1 (by rfl) ⟨1388735, by rfl⟩ : syracuseStep 1851647 = 2777471) B2777471
theorem B1851695 : Blo 1851627 1851695 := bstep (se 1 (by rfl) ⟨1388771, by rfl⟩ : syracuseStep 1851695 = 2777543) B2777543
theorem B6676793 : Blo 1851627 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B4170041 : Blo 1851627 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B2777627 : Blo 1851627 2777627 := bstep (se 1 (by rfl) ⟨2083220, by rfl⟩ : syracuseStep 2777627 = 4166441) B4166441
theorem B1851931 : Blo 1851627 1851931 := bstep (se 1 (by rfl) ⟨1388948, by rfl⟩ : syracuseStep 1851931 = 2777897) B2777897
theorem B3957275 : Blo 1851627 3957275 := bstep (se 1 (by rfl) ⟨2967956, by rfl⟩ : syracuseStep 3957275 = 5935913) B5935913
theorem B1851935 : Blo 1851627 1851935 := bstep (se 1 (by rfl) ⟨1388951, by rfl⟩ : syracuseStep 1851935 = 2777903) B2777903
theorem B1852015 : Blo 1851627 1852015 := bstep (se 1 (by rfl) ⟨1389011, by rfl⟩ : syracuseStep 1852015 = 2778023) B2778023
theorem B4448935 : Blo 1851627 4448935 := bstep (se 1 (by rfl) ⟨3336701, by rfl⟩ : syracuseStep 4448935 = 6673403) B6673403
theorem B1852071 : Blo 1851627 1852071 := bstep (se 1 (by rfl) ⟨1389053, by rfl⟩ : syracuseStep 1852071 = 2778107) B2778107
theorem B2777807 : Blo 1851627 2777807 := bstep (se 1 (by rfl) ⟨2083355, by rfl⟩ : syracuseStep 2777807 = 4166711) B4166711
theorem B1852111 : Blo 1851627 1852111 := bstep (se 1 (by rfl) ⟨1389083, by rfl⟩ : syracuseStep 1852111 = 2778167) B2778167
theorem B2777819 : Blo 1851627 2777819 := bstep (se 1 (by rfl) ⟨2083364, by rfl⟩ : syracuseStep 2777819 = 4166729) B4166729
theorem B7037675 : Blo 1851627 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B7037705 : Blo 1851627 7037705 := bstep (se 2 (by rfl) ⟨2639139, by rfl⟩ : syracuseStep 7037705 = 5278279) B5278279
theorem B1852191 : Blo 1851627 1852191 := bstep (se 1 (by rfl) ⟨1389143, by rfl⟩ : syracuseStep 1852191 = 2778287) B2778287
theorem B4170527 : Blo 1851627 4170527 := bstep (se 1 (by rfl) ⟨3127895, by rfl⟩ : syracuseStep 4170527 = 6255791) B6255791
theorem B16892783 : Blo 1851627 16892783 := bstep (se 1 (by rfl) ⟨12669587, by rfl⟩ : syracuseStep 16892783 = 25339175) B25339175
theorem B1852463 : Blo 1851627 1852463 := bstep (se 1 (by rfl) ⟨1389347, by rfl⟩ : syracuseStep 1852463 = 2778695) B2778695
theorem B1852527 : Blo 1851627 1852527 := bstep (se 1 (by rfl) ⟨1389395, by rfl⟩ : syracuseStep 1852527 = 2778791) B2778791
theorem B2778233 : Blo 1851627 2778233 := bstep (se 2 (by rfl) ⟨1041837, by rfl⟩ : syracuseStep 2778233 = 2083675) B2083675
theorem B1852583 : Blo 1851627 1852583 := bstep (se 1 (by rfl) ⟨1389437, by rfl⟩ : syracuseStep 1852583 = 2778875) B2778875
theorem B1852607 : Blo 1851627 1852607 := bstep (se 1 (by rfl) ⟨1389455, by rfl⟩ : syracuseStep 1852607 = 2778911) B2778911
theorem B1852639 : Blo 1851627 1852639 := bstep (se 1 (by rfl) ⟨1389479, by rfl⟩ : syracuseStep 1852639 = 2778959) B2778959
theorem B2639071 : Blo 1851627 2639071 := bstep (se 1 (by rfl) ⟨1979303, by rfl⟩ : syracuseStep 2639071 = 3958607) B3958607
theorem B15434981 : Blo 1851627 15434981 := bstep (se 4 (by rfl) ⟨1447029, by rfl⟩ : syracuseStep 15434981 = 2894059) B2894059
theorem B2639083 : Blo 1851627 2639083 := bstep (se 1 (by rfl) ⟨1979312, by rfl⟩ : syracuseStep 2639083 = 3958625) B3958625
theorem B85599499 : Blo 1851627 85599499 := bstep (se 1 (by rfl) ⟨64199624, by rfl⟩ : syracuseStep 85599499 = 128399249) B128399249
theorem B1852719 : Blo 1851627 1852719 := bstep (se 1 (by rfl) ⟨1389539, by rfl⟩ : syracuseStep 1852719 = 2779079) B2779079
theorem B7226731 : Blo 1851627 7226731 := bstep (se 1 (by rfl) ⟨5420048, by rfl⟩ : syracuseStep 7226731 = 10840097) B10840097
theorem B1852955 : Blo 1851627 1852955 := bstep (se 1 (by rfl) ⟨1389716, by rfl⟩ : syracuseStep 1852955 = 2779433) B2779433
theorem B1852959 : Blo 1851627 1852959 := bstep (se 1 (by rfl) ⟨1389719, by rfl⟩ : syracuseStep 1852959 = 2779439) B2779439
theorem B60073595 : Blo 1851627 60073595 := bstep (se 1 (by rfl) ⟨45055196, by rfl⟩ : syracuseStep 60073595 = 90110393) B90110393
theorem B1853119 : Blo 1851627 1853119 := bstep (se 1 (by rfl) ⟨1389839, by rfl⟩ : syracuseStep 1853119 = 2779679) B2779679
theorem B54118205 : Blo 1851627 54118205 := bstep (se 3 (by rfl) ⟨10147163, by rfl⟩ : syracuseStep 54118205 = 20294327) B20294327
theorem B6252443 : Blo 1851627 6252443 := bstep (se 1 (by rfl) ⟨4689332, by rfl⟩ : syracuseStep 6252443 = 9378665) B9378665
theorem B1853375 : Blo 1851627 1853375 := bstep (se 1 (by rfl) ⟨1390031, by rfl⟩ : syracuseStep 1853375 = 2780063) B2780063
theorem B2779103 : Blo 1851627 2779103 := bstep (se 1 (by rfl) ⟨2084327, by rfl⟩ : syracuseStep 2779103 = 4168655) B4168655
theorem B1853407 : Blo 1851627 1853407 := bstep (se 1 (by rfl) ⟨1390055, by rfl⟩ : syracuseStep 1853407 = 2780111) B2780111
theorem B2779115 : Blo 1851627 2779115 := bstep (se 1 (by rfl) ⟨2084336, by rfl⟩ : syracuseStep 2779115 = 4168673) B4168673
theorem B5933081 : Blo 1851627 5933081 := bstep (se 2 (by rfl) ⟨2224905, by rfl⟩ : syracuseStep 5933081 = 4449811) B4449811
theorem B2779163 : Blo 1851627 2779163 := bstep (se 1 (by rfl) ⟨2084372, by rfl⟩ : syracuseStep 2779163 = 4168745) B4168745
theorem B1853467 : Blo 1851627 1853467 := bstep (se 1 (by rfl) ⟨1390100, by rfl⟩ : syracuseStep 1853467 = 2780201) B2780201
theorem B1853471 : Blo 1851627 1853471 := bstep (se 1 (by rfl) ⟨1390103, by rfl⟩ : syracuseStep 1853471 = 2780207) B2780207
theorem B20039723 : Blo 1851627 20039723 := bstep (se 1 (by rfl) ⟨15029792, by rfl⟩ : syracuseStep 20039723 = 30059585) B30059585
theorem B1853487 : Blo 1851627 1853487 := bstep (se 1 (by rfl) ⟨1390115, by rfl⟩ : syracuseStep 1853487 = 2780231) B2780231
theorem B10692713 : Blo 1851627 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B4450427 : Blo 1851627 4450427 := bstep (se 1 (by rfl) ⟨3337820, by rfl⟩ : syracuseStep 4450427 = 6675641) B6675641
theorem B4753631 : Blo 1851627 4753631 := bstep (se 1 (by rfl) ⟨3565223, by rfl⟩ : syracuseStep 4753631 = 7130447) B7130447
theorem B2083099 : Blo 1851627 2083099 := bstep (se 1 (by rfl) ⟨1562324, by rfl⟩ : syracuseStep 2083099 = 3124649) B3124649
theorem B2779529 : Blo 1851627 2779529 := bstep (se 2 (by rfl) ⟨1042323, by rfl⟩ : syracuseStep 2779529 = 2084647) B2084647
theorem B5007863 : Blo 1851627 5007863 := bstep (se 1 (by rfl) ⟨3755897, by rfl⟩ : syracuseStep 5007863 = 7511795) B7511795
theorem B10693291 : Blo 1851627 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B7916393 : Blo 1851627 7916393 := bstep (se 2 (by rfl) ⟨2968647, by rfl⟩ : syracuseStep 7916393 = 5937295) B5937295
theorem B16903289 : Blo 1851627 16903289 := bstep (se 2 (by rfl) ⟨6338733, by rfl⟩ : syracuseStep 16903289 = 12677467) B12677467
theorem B6335617 : Blo 1851627 6335617 := bstep (se 2 (by rfl) ⟨2375856, by rfl⟩ : syracuseStep 6335617 = 4751713) B4751713
theorem B7032041 : Blo 1851627 7032041 := bstep (se 2 (by rfl) ⟨2637015, by rfl⟩ : syracuseStep 7032041 = 5274031) B5274031
theorem B135195965 : Blo 1851627 135195965 := bstep (se 3 (by rfl) ⟨25349243, by rfl⟩ : syracuseStep 135195965 = 50698487) B50698487
theorem B2084251 : Blo 1851627 2084251 := bstep (se 1 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 2084251 = 3126377) B3126377
theorem B10546625 : Blo 1851627 10546625 := bstep (se 2 (by rfl) ⟨3954984, by rfl⟩ : syracuseStep 10546625 = 7909969) B7909969
theorem B3124703 : Blo 1851627 3124703 := bstep (se 1 (by rfl) ⟨2343527, by rfl⟩ : syracuseStep 3124703 = 4687055) B4687055
theorem B33811991 : Blo 1851627 33811991 := bstep (se 1 (by rfl) ⟨25358993, by rfl⟩ : syracuseStep 33811991 = 50717987) B50717987
theorem B501894719 : Blo 1851627 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B6254171 : Blo 1851627 6254171 := bstep (se 1 (by rfl) ⟨4690628, by rfl⟩ : syracuseStep 6254171 = 9381257) B9381257
theorem B8023643 : Blo 1851627 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B40062559 : Blo 1851627 40062559 := bstep (se 1 (by rfl) ⟨30046919, by rfl⟩ : syracuseStep 40062559 = 60093839) B60093839
theorem B3124919 : Blo 1851627 3124919 := bstep (se 1 (by rfl) ⟨2343689, by rfl⟩ : syracuseStep 3124919 = 4687379) B4687379
theorem B14069699 : Blo 1851627 14069699 := bstep (se 1 (by rfl) ⟨10552274, by rfl⟩ : syracuseStep 14069699 = 21104549) B21104549
theorem B4452425 : Blo 1851627 4452425 := bstep (se 2 (by rfl) ⟨1669659, by rfl⟩ : syracuseStep 4452425 = 3339319) B3339319
theorem B6254873 : Blo 1851627 6254873 := bstep (se 2 (by rfl) ⟨2345577, by rfl⟩ : syracuseStep 6254873 = 4691155) B4691155
theorem B3756385 : Blo 1851627 3756385 := bstep (se 2 (by rfl) ⟨1408644, by rfl⟩ : syracuseStep 3756385 = 2817289) B2817289
theorem B2085223 : Blo 1851627 2085223 := bstep (se 1 (by rfl) ⟨1563917, by rfl⟩ : syracuseStep 2085223 = 3127835) B3127835
theorem B4690487 : Blo 1851627 4690487 := bstep (se 1 (by rfl) ⟨3517865, by rfl⟩ : syracuseStep 4690487 = 7035731) B7035731
theorem B10294141 : Blo 1851627 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B7910311 : Blo 1851627 7910311 := bstep (se 1 (by rfl) ⟨5932733, by rfl⟩ : syracuseStep 7910311 = 11865467) B11865467
theorem B11269057 : Blo 1851627 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B25359313 : Blo 1851627 25359313 := bstep (se 2 (by rfl) ⟨9509742, by rfl⟩ : syracuseStep 25359313 = 19019485) B19019485
theorem B4166639 : Blo 1851627 4166639 := bstep (se 1 (by rfl) ⟨3124979, by rfl⟩ : syracuseStep 4166639 = 6249959) B6249959
theorem B4224071 : Blo 1851627 4224071 := bstep (se 1 (by rfl) ⟨3168053, by rfl⟩ : syracuseStep 4224071 = 6336107) B6336107
theorem B3126343 : Blo 1851627 3126343 := bstep (se 1 (by rfl) ⟨2344757, by rfl⟩ : syracuseStep 3126343 = 4689515) B4689515
theorem B114095243 : Blo 1851627 114095243 := bstep (se 1 (by rfl) ⟨85571432, by rfl⟩ : syracuseStep 114095243 = 171142865) B171142865
theorem B4691105 : Blo 1851627 4691105 := bstep (se 2 (by rfl) ⟨1759164, by rfl⟩ : syracuseStep 4691105 = 3518329) B3518329
theorem B11269543 : Blo 1851627 11269543 := bstep (se 1 (by rfl) ⟨8452157, by rfl⟩ : syracuseStep 11269543 = 16904315) B16904315
theorem B4167143 : Blo 1851627 4167143 := bstep (se 1 (by rfl) ⟨3125357, by rfl⟩ : syracuseStep 4167143 = 6250715) B6250715
theorem B4167305 : Blo 1851627 4167305 := bstep (se 2 (by rfl) ⟨1562739, by rfl⟩ : syracuseStep 4167305 = 3125479) B3125479
theorem B4167323 : Blo 1851627 4167323 := bstep (se 1 (by rfl) ⟨3125492, by rfl⟩ : syracuseStep 4167323 = 6250985) B6250985
theorem B4167521 : Blo 1851627 4167521 := bstep (se 2 (by rfl) ⟨1562820, by rfl⟩ : syracuseStep 4167521 = 3125641) B3125641
theorem B4167719 : Blo 1851627 4167719 := bstep (se 1 (by rfl) ⟨3125789, by rfl⟩ : syracuseStep 4167719 = 6251579) B6251579
theorem B7510141 : Blo 1851627 7510141 := bstep (se 3 (by rfl) ⟨1408151, by rfl⟩ : syracuseStep 7510141 = 2816303) B2816303
theorem B4167899 : Blo 1851627 4167899 := bstep (se 1 (by rfl) ⟨3125924, by rfl⟩ : syracuseStep 4167899 = 6251849) B6251849
theorem B26417423 : Blo 1851627 26417423 := bstep (se 1 (by rfl) ⟨19813067, by rfl⟩ : syracuseStep 26417423 = 39626135) B39626135
theorem B7035245 : Blo 1851627 7035245 := bstep (se 3 (by rfl) ⟨1319108, by rfl⟩ : syracuseStep 7035245 = 2638217) B2638217
theorem B4168097 : Blo 1851627 4168097 := bstep (se 2 (by rfl) ⟨1563036, by rfl⟩ : syracuseStep 4168097 = 3126073) B3126073
theorem B10549723 : Blo 1851627 10549723 := bstep (se 1 (by rfl) ⟨7912292, by rfl⟩ : syracuseStep 10549723 = 15824585) B15824585
theorem B4168169 : Blo 1851627 4168169 := bstep (se 2 (by rfl) ⟨1563063, by rfl⟩ : syracuseStep 4168169 = 3126127) B3126127
theorem B52108433 : Blo 1851627 52108433 := bstep (se 2 (by rfl) ⟨19540662, by rfl⟩ : syracuseStep 52108433 = 39081325) B39081325
theorem B11869669 : Blo 1851627 11869669 := bstep (se 4 (by rfl) ⟨1112781, by rfl⟩ : syracuseStep 11869669 = 2225563) B2225563
theorem B3956215 : Blo 1851627 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B47488517 : Blo 1851627 47488517 := bstep (se 4 (by rfl) ⟨4452048, by rfl⟩ : syracuseStep 47488517 = 8904097) B8904097
theorem B17800813 : Blo 1851627 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B7036703 : Blo 1851627 7036703 := bstep (se 1 (by rfl) ⟨5277527, by rfl⟩ : syracuseStep 7036703 = 10555055) B10555055
theorem B26697529 : Blo 1851627 26697529 := bstep (se 2 (by rfl) ⟨10011573, by rfl⟩ : syracuseStep 26697529 = 20023147) B20023147
theorem B4169627 : Blo 1851627 4169627 := bstep (se 1 (by rfl) ⟨3127220, by rfl⟩ : syracuseStep 4169627 = 6254441) B6254441
theorem B13361051 : Blo 1851627 13361051 := bstep (se 1 (by rfl) ⟨10020788, by rfl⟩ : syracuseStep 13361051 = 20041577) B20041577
theorem B7036915 : Blo 1851627 7036915 := bstep (se 1 (by rfl) ⟨5277686, by rfl⟩ : syracuseStep 7036915 = 10555373) B10555373
theorem B4169915 : Blo 1851627 4169915 := bstep (se 1 (by rfl) ⟨3127436, by rfl⟩ : syracuseStep 4169915 = 6254873) B6254873
theorem B11264189 : Blo 1851627 11264189 := bstep (se 3 (by rfl) ⟨2112035, by rfl⟩ : syracuseStep 11264189 = 4224071) B4224071
theorem B1851751 : Blo 1851627 1851751 := bstep (se 1 (by rfl) ⟨1388813, by rfl⟩ : syracuseStep 1851751 = 2777627) B2777627
theorem B2638183 : Blo 1851627 2638183 := bstep (se 1 (by rfl) ⟨1978637, by rfl⟩ : syracuseStep 2638183 = 3957275) B3957275
theorem B2777465 : Blo 1851627 2777465 := bstep (se 2 (by rfl) ⟨1041549, by rfl⟩ : syracuseStep 2777465 = 2083099) B2083099
theorem B1851871 : Blo 1851627 1851871 := bstep (se 1 (by rfl) ⟨1388903, by rfl⟩ : syracuseStep 1851871 = 2777807) B2777807
theorem B1851879 : Blo 1851627 1851879 := bstep (se 1 (by rfl) ⟨1388909, by rfl⟩ : syracuseStep 1851879 = 2777819) B2777819
theorem B14066297 : Blo 1851627 14066297 := bstep (se 2 (by rfl) ⟨5274861, by rfl⟩ : syracuseStep 14066297 = 10549723) B10549723
theorem B2777759 : Blo 1851627 2777759 := bstep (se 1 (by rfl) ⟨2083319, by rfl⟩ : syracuseStep 2777759 = 4166639) B4166639
theorem B1852155 : Blo 1851627 1852155 := bstep (se 1 (by rfl) ⟨1389116, by rfl⟩ : syracuseStep 1852155 = 2778233) B2778233
theorem B76063495 : Blo 1851627 76063495 := bstep (se 1 (by rfl) ⟨57047621, by rfl⟩ : syracuseStep 76063495 = 114095243) B114095243
theorem B10289987 : Blo 1851627 10289987 := bstep (se 1 (by rfl) ⟨7717490, by rfl⟩ : syracuseStep 10289987 = 15434981) B15434981
theorem B2778095 : Blo 1851627 2778095 := bstep (se 1 (by rfl) ⟨2083571, by rfl⟩ : syracuseStep 2778095 = 4167143) B4167143
theorem B2778203 : Blo 1851627 2778203 := bstep (se 1 (by rfl) ⟨2083652, by rfl⟩ : syracuseStep 2778203 = 4167305) B4167305
theorem B2778215 : Blo 1851627 2778215 := bstep (se 1 (by rfl) ⟨2083661, by rfl⟩ : syracuseStep 2778215 = 4167323) B4167323
theorem B14075045 : Blo 1851627 14075045 := bstep (se 4 (by rfl) ⟨1319535, by rfl⟩ : syracuseStep 14075045 = 2639071) B2639071
theorem B36078803 : Blo 1851627 36078803 := bstep (se 1 (by rfl) ⟨27059102, by rfl⟩ : syracuseStep 36078803 = 54118205) B54118205
theorem B2778347 : Blo 1851627 2778347 := bstep (se 1 (by rfl) ⟨2083760, by rfl⟩ : syracuseStep 2778347 = 4167521) B4167521
theorem B15025409 : Blo 1851627 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B13354301 : Blo 1851627 13354301 := bstep (se 3 (by rfl) ⟨2503931, by rfl⟩ : syracuseStep 13354301 = 5007863) B5007863
theorem B1852735 : Blo 1851627 1852735 := bstep (se 1 (by rfl) ⟨1389551, by rfl⟩ : syracuseStep 1852735 = 2779103) B2779103
theorem B1852743 : Blo 1851627 1852743 := bstep (se 1 (by rfl) ⟨1389557, by rfl⟩ : syracuseStep 1852743 = 2779115) B2779115
theorem B1852775 : Blo 1851627 1852775 := bstep (se 1 (by rfl) ⟨1389581, by rfl⟩ : syracuseStep 1852775 = 2779163) B2779163
theorem B2778479 : Blo 1851627 2778479 := bstep (se 1 (by rfl) ⟨2083859, by rfl⟩ : syracuseStep 2778479 = 4167719) B4167719
theorem B2966951 : Blo 1851627 2966951 := bstep (se 1 (by rfl) ⟨2225213, by rfl⟩ : syracuseStep 2966951 = 4450427) B4450427
theorem B2778599 : Blo 1851627 2778599 := bstep (se 1 (by rfl) ⟨2083949, by rfl⟩ : syracuseStep 2778599 = 4167899) B4167899
theorem B8447489 : Blo 1851627 8447489 := bstep (se 2 (by rfl) ⟨3167808, by rfl⟩ : syracuseStep 8447489 = 6335617) B6335617
theorem B1853019 : Blo 1851627 1853019 := bstep (se 1 (by rfl) ⟨1389764, by rfl⟩ : syracuseStep 1853019 = 2779529) B2779529
theorem B2778731 : Blo 1851627 2778731 := bstep (se 1 (by rfl) ⟨2084048, by rfl⟩ : syracuseStep 2778731 = 4168097) B4168097
theorem B2778779 : Blo 1851627 2778779 := bstep (se 1 (by rfl) ⟨2084084, by rfl⟩ : syracuseStep 2778779 = 4168169) B4168169
theorem B114132665 : Blo 1851627 114132665 := bstep (se 2 (by rfl) ⟨42799749, by rfl⟩ : syracuseStep 114132665 = 85599499) B85599499
theorem B9635641 : Blo 1851627 9635641 := bstep (se 2 (by rfl) ⟨3613365, by rfl⟩ : syracuseStep 9635641 = 7226731) B7226731
theorem B2779001 : Blo 1851627 2779001 := bstep (se 2 (by rfl) ⟨1042125, by rfl⟩ : syracuseStep 2779001 = 2084251) B2084251
theorem B15026057 : Blo 1851627 15026057 := bstep (se 2 (by rfl) ⟨5634771, by rfl⟩ : syracuseStep 15026057 = 11269543) B11269543
theorem B23734417 : Blo 1851627 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B4688027 : Blo 1851627 4688027 := bstep (se 1 (by rfl) ⟨3516020, by rfl⟩ : syracuseStep 4688027 = 7032041) B7032041
theorem B90130643 : Blo 1851627 90130643 := bstep (se 1 (by rfl) ⟨67597982, by rfl⟩ : syracuseStep 90130643 = 135195965) B135195965
theorem B7031083 : Blo 1851627 7031083 := bstep (se 1 (by rfl) ⟨5273312, by rfl⟩ : syracuseStep 7031083 = 10546625) B10546625
theorem B2083135 : Blo 1851627 2083135 := bstep (se 1 (by rfl) ⟨1562351, by rfl⟩ : syracuseStep 2083135 = 3124703) B3124703
theorem B334596479 : Blo 1851627 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B35596705 : Blo 1851627 35596705 := bstep (se 2 (by rfl) ⟨13348764, by rfl⟩ : syracuseStep 35596705 = 26697529) B26697529
theorem B2083279 : Blo 1851627 2083279 := bstep (se 1 (by rfl) ⟨1562459, by rfl⟩ : syracuseStep 2083279 = 3124919) B3124919
theorem B2779751 : Blo 1851627 2779751 := bstep (se 1 (by rfl) ⟨2084813, by rfl⟩ : syracuseStep 2779751 = 4169627) B4169627
theorem B8907367 : Blo 1851627 8907367 := bstep (se 1 (by rfl) ⟨6680525, by rfl⟩ : syracuseStep 8907367 = 13361051) B13361051
theorem B9382553 : Blo 1851627 9382553 := bstep (se 2 (by rfl) ⟨3518457, by rfl⟩ : syracuseStep 9382553 = 7036915) B7036915
theorem B47475395 : Blo 1851627 47475395 := bstep (se 1 (by rfl) ⟨35606546, by rfl⟩ : syracuseStep 47475395 = 71213093) B71213093
theorem B2968283 : Blo 1851627 2968283 := bstep (se 1 (by rfl) ⟨2226212, by rfl⟩ : syracuseStep 2968283 = 4452425) B4452425
theorem B4451195 : Blo 1851627 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B2780027 : Blo 1851627 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B45075437 : Blo 1851627 45075437 := bstep (se 3 (by rfl) ⟨8451644, by rfl⟩ : syracuseStep 45075437 = 16903289) B16903289
theorem B5008513 : Blo 1851627 5008513 := bstep (se 2 (by rfl) ⟨1878192, by rfl⟩ : syracuseStep 5008513 = 3756385) B3756385
theorem B2780297 : Blo 1851627 2780297 := bstep (se 2 (by rfl) ⟨1042611, by rfl⟩ : syracuseStep 2780297 = 2085223) B2085223
theorem B2780351 : Blo 1851627 2780351 := bstep (se 1 (by rfl) ⟨2085263, by rfl⟩ : syracuseStep 2780351 = 4170527) B4170527
theorem B40054085 : Blo 1851627 40054085 := bstep (se 4 (by rfl) ⟨3755070, by rfl⟩ : syracuseStep 40054085 = 7510141) B7510141
theorem B23727653 : Blo 1851627 23727653 := bstep (se 4 (by rfl) ⟨2224467, by rfl⟩ : syracuseStep 23727653 = 4448935) B4448935
theorem B14257721 : Blo 1851627 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B13725521 : Blo 1851627 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B10547081 : Blo 1851627 10547081 := bstep (se 2 (by rfl) ⟨3955155, by rfl⟩ : syracuseStep 10547081 = 7910311) B7910311
theorem B33812417 : Blo 1851627 33812417 := bstep (se 2 (by rfl) ⟨12679656, by rfl⟩ : syracuseStep 33812417 = 25359313) B25359313
theorem B4690163 : Blo 1851627 4690163 := bstep (se 1 (by rfl) ⟨3517622, by rfl⟩ : syracuseStep 4690163 = 7035245) B7035245
theorem B3518777 : Blo 1851627 3518777 := bstep (se 2 (by rfl) ⟨1319541, by rfl⟩ : syracuseStep 3518777 = 2639083) B2639083
theorem B34738955 : Blo 1851627 34738955 := bstep (se 1 (by rfl) ⟨26054216, by rfl⟩ : syracuseStep 34738955 = 52108433) B52108433
theorem B53416745 : Blo 1851627 53416745 := bstep (se 2 (by rfl) ⟨20031279, by rfl⟩ : syracuseStep 53416745 = 40062559) B40062559
theorem B31659011 : Blo 1851627 31659011 := bstep (se 1 (by rfl) ⟨23744258, by rfl⟩ : syracuseStep 31659011 = 47488517) B47488517
theorem B22541327 : Blo 1851627 22541327 := bstep (se 1 (by rfl) ⟨16905995, by rfl⟩ : syracuseStep 22541327 = 33811991) B33811991
theorem B4691135 : Blo 1851627 4691135 := bstep (se 1 (by rfl) ⟨3518351, by rfl⟩ : syracuseStep 4691135 = 7036703) B7036703
theorem B18044315 : Blo 1851627 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B28513901 : Blo 1851627 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B3126991 : Blo 1851627 3126991 := bstep (se 1 (by rfl) ⟨2345243, by rfl⟩ : syracuseStep 3126991 = 4690487) B4690487
theorem B4691783 : Blo 1851627 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B4691803 : Blo 1851627 4691803 := bstep (se 1 (by rfl) ⟨3518852, by rfl⟩ : syracuseStep 4691803 = 7037705) B7037705
theorem B11261855 : Blo 1851627 11261855 := bstep (se 1 (by rfl) ⟨8446391, by rfl⟩ : syracuseStep 11261855 = 16892783) B16892783
theorem B3127403 : Blo 1851627 3127403 := bstep (se 1 (by rfl) ⟨2345552, by rfl⟩ : syracuseStep 3127403 = 4691105) B4691105
theorem B40049063 : Blo 1851627 40049063 := bstep (se 1 (by rfl) ⟨30036797, by rfl⟩ : syracuseStep 40049063 = 60073595) B60073595
theorem B4168295 : Blo 1851627 4168295 := bstep (se 1 (by rfl) ⟨3126221, by rfl⟩ : syracuseStep 4168295 = 6252443) B6252443
theorem B3955387 : Blo 1851627 3955387 := bstep (se 1 (by rfl) ⟨2966540, by rfl⟩ : syracuseStep 3955387 = 5933081) B5933081
theorem B13359815 : Blo 1851627 13359815 := bstep (se 1 (by rfl) ⟨10019861, by rfl⟩ : syracuseStep 13359815 = 20039723) B20039723
theorem B4168457 : Blo 1851627 4168457 := bstep (se 2 (by rfl) ⟨1563171, by rfl⟩ : syracuseStep 4168457 = 3126343) B3126343
theorem B3169087 : Blo 1851627 3169087 := bstep (se 1 (by rfl) ⟨2376815, by rfl⟩ : syracuseStep 3169087 = 4753631) B4753631
theorem B17611615 : Blo 1851627 17611615 := bstep (se 1 (by rfl) ⟨13208711, by rfl⟩ : syracuseStep 17611615 = 26417423) B26417423
theorem B15826225 : Blo 1851627 15826225 := bstep (se 2 (by rfl) ⟨5934834, by rfl⟩ : syracuseStep 15826225 = 11869669) B11869669
theorem B5274953 : Blo 1851627 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B21110381 : Blo 1851627 21110381 := bstep (se 3 (by rfl) ⟨3958196, by rfl⟩ : syracuseStep 21110381 = 7916393) B7916393
theorem B4169447 : Blo 1851627 4169447 := bstep (se 1 (by rfl) ⟨3127085, by rfl⟩ : syracuseStep 4169447 = 6254171) B6254171
theorem B5349095 : Blo 1851627 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B9379799 : Blo 1851627 9379799 := bstep (se 1 (by rfl) ⟨7034849, by rfl⟩ : syracuseStep 9379799 = 14069699) B14069699
theorem B31645889 : Blo 1851627 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B1851643 : Blo 1851627 1851643 := bstep (se 1 (by rfl) ⟨1388732, by rfl⟩ : syracuseStep 1851643 = 2777465) B2777465
theorem B2777513 : Blo 1851627 2777513 := bstep (se 2 (by rfl) ⟨1041567, by rfl⟩ : syracuseStep 2777513 = 2083135) B2083135
theorem B1851839 : Blo 1851627 1851839 := bstep (se 1 (by rfl) ⟨1388879, by rfl⟩ : syracuseStep 1851839 = 2777759) B2777759
theorem B23159303 : Blo 1851627 23159303 := bstep (se 1 (by rfl) ⟨17369477, by rfl⟩ : syracuseStep 23159303 = 34738955) B34738955
theorem B35611163 : Blo 1851627 35611163 := bstep (se 1 (by rfl) ⟨26708372, by rfl⟩ : syracuseStep 35611163 = 53416745) B53416745
theorem B2777705 : Blo 1851627 2777705 := bstep (se 2 (by rfl) ⟨1041639, by rfl⟩ : syracuseStep 2777705 = 2083279) B2083279
theorem B1852063 : Blo 1851627 1852063 := bstep (se 1 (by rfl) ⟨1389047, by rfl⟩ : syracuseStep 1852063 = 2778095) B2778095
theorem B1852135 : Blo 1851627 1852135 := bstep (se 1 (by rfl) ⟨1389101, by rfl⟩ : syracuseStep 1852135 = 2778203) B2778203
theorem B1852143 : Blo 1851627 1852143 := bstep (se 1 (by rfl) ⟨1389107, by rfl⟩ : syracuseStep 1852143 = 2778215) B2778215
theorem B24052535 : Blo 1851627 24052535 := bstep (se 1 (by rfl) ⟨18039401, by rfl⟩ : syracuseStep 24052535 = 36078803) B36078803
theorem B1852231 : Blo 1851627 1852231 := bstep (se 1 (by rfl) ⟨1389173, by rfl⟩ : syracuseStep 1852231 = 2778347) B2778347
theorem B1852319 : Blo 1851627 1852319 := bstep (se 1 (by rfl) ⟨1389239, by rfl⟩ : syracuseStep 1852319 = 2778479) B2778479
theorem B1852399 : Blo 1851627 1852399 := bstep (se 1 (by rfl) ⟨1389299, by rfl⟩ : syracuseStep 1852399 = 2778599) B2778599
theorem B892257277 : Blo 1851627 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B101417993 : Blo 1851627 101417993 := bstep (se 2 (by rfl) ⟨38031747, by rfl⟩ : syracuseStep 101417993 = 76063495) B76063495
theorem B1852487 : Blo 1851627 1852487 := bstep (se 1 (by rfl) ⟨1389365, by rfl⟩ : syracuseStep 1852487 = 2778731) B2778731
theorem B1852519 : Blo 1851627 1852519 := bstep (se 1 (by rfl) ⟨1389389, by rfl⟩ : syracuseStep 1852519 = 2778779) B2778779
theorem B1852667 : Blo 1851627 1852667 := bstep (se 1 (by rfl) ⟨1389500, by rfl⟩ : syracuseStep 1852667 = 2779001) B2779001
theorem B6678017 : Blo 1851627 6678017 := bstep (se 2 (by rfl) ⟨2504256, by rfl⟩ : syracuseStep 6678017 = 5008513) B5008513
theorem B26699375 : Blo 1851627 26699375 := bstep (se 1 (by rfl) ⟨20024531, by rfl⟩ : syracuseStep 26699375 = 40049063) B40049063
theorem B51390085 : Blo 1851627 51390085 := bstep (se 4 (by rfl) ⟨4817820, by rfl⟩ : syracuseStep 51390085 = 9635641) B9635641
theorem B16901797 : Blo 1851627 16901797 := bstep (se 4 (by rfl) ⟨1584543, by rfl⟩ : syracuseStep 16901797 = 3169087) B3169087
theorem B2778863 : Blo 1851627 2778863 := bstep (se 1 (by rfl) ⟨2084147, by rfl⟩ : syracuseStep 2778863 = 4168295) B4168295
theorem B1853167 : Blo 1851627 1853167 := bstep (se 1 (by rfl) ⟨1389875, by rfl⟩ : syracuseStep 1853167 = 2779751) B2779751
theorem B8906543 : Blo 1851627 8906543 := bstep (se 1 (by rfl) ⟨6679907, by rfl⟩ : syracuseStep 8906543 = 13359815) B13359815
theorem B2778971 : Blo 1851627 2778971 := bstep (se 1 (by rfl) ⟨2084228, by rfl⟩ : syracuseStep 2778971 = 4168457) B4168457
theorem B7915421 : Blo 1851627 7915421 := bstep (se 3 (by rfl) ⟨1484141, by rfl⟩ : syracuseStep 7915421 = 2968283) B2968283
theorem B2967463 : Blo 1851627 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B1853351 : Blo 1851627 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B30050291 : Blo 1851627 30050291 := bstep (se 1 (by rfl) ⟨22537718, by rfl⟩ : syracuseStep 30050291 = 45075437) B45075437
theorem B1853531 : Blo 1851627 1853531 := bstep (se 1 (by rfl) ⟨1390148, by rfl⟩ : syracuseStep 1853531 = 2780297) B2780297
theorem B1853567 : Blo 1851627 1853567 := bstep (se 1 (by rfl) ⟨1390175, by rfl⟩ : syracuseStep 1853567 = 2780351) B2780351
theorem B3516635 : Blo 1851627 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B9505147 : Blo 1851627 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B2779631 : Blo 1851627 2779631 := bstep (se 1 (by rfl) ⟨2084723, by rfl⟩ : syracuseStep 2779631 = 4169447) B4169447
theorem B3566063 : Blo 1851627 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B7031387 : Blo 1851627 7031387 := bstep (se 1 (by rfl) ⟨5273540, by rfl⟩ : syracuseStep 7031387 = 10547081) B10547081
theorem B6253199 : Blo 1851627 6253199 := bstep (se 1 (by rfl) ⟨4689899, by rfl⟩ : syracuseStep 6253199 = 9379799) B9379799
theorem B2779943 : Blo 1851627 2779943 := bstep (se 1 (by rfl) ⟨2084957, by rfl⟩ : syracuseStep 2779943 = 4169915) B4169915
theorem B2345851 : Blo 1851627 2345851 := bstep (se 1 (by rfl) ⟨1759388, by rfl⟩ : syracuseStep 2345851 = 3518777) B3518777
theorem B9374777 : Blo 1851627 9374777 := bstep (se 2 (by rfl) ⟨3515541, by rfl⟩ : syracuseStep 9374777 = 7031083) B7031083
theorem B3517577 : Blo 1851627 3517577 := bstep (se 2 (by rfl) ⟨1319091, by rfl⟩ : syracuseStep 3517577 = 2638183) B2638183
theorem B6859991 : Blo 1851627 6859991 := bstep (se 1 (by rfl) ⟨5144993, by rfl⟩ : syracuseStep 6859991 = 10289987) B10289987
theorem B21106007 : Blo 1851627 21106007 := bstep (se 1 (by rfl) ⟨15829505, by rfl⟩ : syracuseStep 21106007 = 31659011) B31659011
theorem B15027551 : Blo 1851627 15027551 := bstep (se 1 (by rfl) ⟨11270663, by rfl⟩ : syracuseStep 15027551 = 22541327) B22541327
theorem B9383363 : Blo 1851627 9383363 := bstep (se 1 (by rfl) ⟨7037522, by rfl⟩ : syracuseStep 9383363 = 14075045) B14075045
theorem B12029543 : Blo 1851627 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B1977967 : Blo 1851627 1977967 := bstep (se 1 (by rfl) ⟨1483475, by rfl⟩ : syracuseStep 1977967 = 2966951) B2966951
theorem B5631659 : Blo 1851627 5631659 := bstep (se 1 (by rfl) ⟨4223744, by rfl⟩ : syracuseStep 5631659 = 8447489) B8447489
theorem B23482153 : Blo 1851627 23482153 := bstep (se 2 (by rfl) ⟨8805807, by rfl⟩ : syracuseStep 23482153 = 17611615) B17611615
theorem B7507903 : Blo 1851627 7507903 := bstep (se 1 (by rfl) ⟨5630927, by rfl⟩ : syracuseStep 7507903 = 11261855) B11261855
theorem B2084935 : Blo 1851627 2084935 := bstep (se 1 (by rfl) ⟨1563701, by rfl⟩ : syracuseStep 2084935 = 3127403) B3127403
theorem B3125351 : Blo 1851627 3125351 := bstep (se 1 (by rfl) ⟨2344013, by rfl⟩ : syracuseStep 3125351 = 4688027) B4688027
theorem B6255035 : Blo 1851627 6255035 := bstep (se 1 (by rfl) ⟨4691276, by rfl⟩ : syracuseStep 6255035 = 9382553) B9382553
theorem B31650263 : Blo 1851627 31650263 := bstep (se 1 (by rfl) ⟨23737697, by rfl⟩ : syracuseStep 31650263 = 47475395) B47475395
theorem B304353773 : Blo 1851627 304353773 := bstep (se 3 (by rfl) ⟨57066332, by rfl⟩ : syracuseStep 304353773 = 114132665) B114132665
theorem B26702723 : Blo 1851627 26702723 := bstep (se 1 (by rfl) ⟨20027042, by rfl⟩ : syracuseStep 26702723 = 40054085) B40054085
theorem B6255737 : Blo 1851627 6255737 := bstep (se 2 (by rfl) ⟨2345901, by rfl⟩ : syracuseStep 6255737 = 4691803) B4691803
theorem B22541611 : Blo 1851627 22541611 := bstep (se 1 (by rfl) ⟨16906208, by rfl⟩ : syracuseStep 22541611 = 33812417) B33812417
theorem B3126775 : Blo 1851627 3126775 := bstep (se 1 (by rfl) ⟨2345081, by rfl⟩ : syracuseStep 3126775 = 4690163) B4690163
theorem B9377531 : Blo 1851627 9377531 := bstep (se 1 (by rfl) ⟨7033148, by rfl⟩ : syracuseStep 9377531 = 14066297) B14066297
theorem B30037837 : Blo 1851627 30037837 := bstep (se 3 (by rfl) ⟨5632094, by rfl⟩ : syracuseStep 30037837 = 11264189) B11264189
theorem B47462273 : Blo 1851627 47462273 := bstep (se 2 (by rfl) ⟨17798352, by rfl⟩ : syracuseStep 47462273 = 35596705) B35596705
theorem B3127423 : Blo 1851627 3127423 := bstep (se 1 (by rfl) ⟨2345567, by rfl⟩ : syracuseStep 3127423 = 4691135) B4691135
theorem B11876489 : Blo 1851627 11876489 := bstep (se 2 (by rfl) ⟨4453683, by rfl⟩ : syracuseStep 11876489 = 8907367) B8907367
theorem B10016939 : Blo 1851627 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B8902867 : Blo 1851627 8902867 := bstep (se 1 (by rfl) ⟨6677150, by rfl⟩ : syracuseStep 8902867 = 13354301) B13354301
theorem B5273849 : Blo 1851627 5273849 := bstep (se 2 (by rfl) ⟨1977693, by rfl⟩ : syracuseStep 5273849 = 3955387) B3955387
theorem B3127855 : Blo 1851627 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B10017371 : Blo 1851627 10017371 := bstep (se 1 (by rfl) ⟨7513028, by rfl⟩ : syracuseStep 10017371 = 15026057) B15026057
theorem B60087095 : Blo 1851627 60087095 := bstep (se 1 (by rfl) ⟨45065321, by rfl⟩ : syracuseStep 60087095 = 90130643) B90130643
theorem B76037069 : Blo 1851627 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B21101633 : Blo 1851627 21101633 := bstep (se 2 (by rfl) ⟨7913112, by rfl⟩ : syracuseStep 21101633 = 15826225) B15826225
theorem B4169321 : Blo 1851627 4169321 := bstep (se 2 (by rfl) ⟨1563495, by rfl⟩ : syracuseStep 4169321 = 3126991) B3126991
theorem B15818435 : Blo 1851627 15818435 := bstep (se 1 (by rfl) ⟨11863826, by rfl⟩ : syracuseStep 15818435 = 23727653) B23727653
theorem B14073587 : Blo 1851627 14073587 := bstep (se 1 (by rfl) ⟨10555190, by rfl⟩ : syracuseStep 14073587 = 21110381) B21110381
theorem B9150347 : Blo 1851627 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B4169897 : Blo 1851627 4169897 := bstep (se 2 (by rfl) ⟨1563711, by rfl⟩ : syracuseStep 4169897 = 3127423) B3127423
theorem B11870489 : Blo 1851627 11870489 := bstep (se 2 (by rfl) ⟨4451433, by rfl⟩ : syracuseStep 11870489 = 8902867) B8902867
theorem B1851675 : Blo 1851627 1851675 := bstep (se 1 (by rfl) ⟨1388756, by rfl⟩ : syracuseStep 1851675 = 2777513) B2777513
theorem B4170023 : Blo 1851627 4170023 := bstep (se 1 (by rfl) ⟨3127517, by rfl⟩ : syracuseStep 4170023 = 6255035) B6255035
theorem B23740775 : Blo 1851627 23740775 := bstep (se 1 (by rfl) ⟨17805581, by rfl⟩ : syracuseStep 23740775 = 35611163) B35611163
theorem B1851803 : Blo 1851627 1851803 := bstep (se 1 (by rfl) ⟨1388852, by rfl⟩ : syracuseStep 1851803 = 2777705) B2777705
theorem B12673529 : Blo 1851627 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B18293309 : Blo 1851627 18293309 := bstep (se 3 (by rfl) ⟨3429995, by rfl⟩ : syracuseStep 18293309 = 6859991) B6859991
theorem B17801815 : Blo 1851627 17801815 := bstep (se 1 (by rfl) ⟨13351361, by rfl⟩ : syracuseStep 17801815 = 26702723) B26702723
theorem B4170473 : Blo 1851627 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B4170491 : Blo 1851627 4170491 := bstep (se 1 (by rfl) ⟨3127868, by rfl⟩ : syracuseStep 4170491 = 6255737) B6255737
theorem B1852575 : Blo 1851627 1852575 := bstep (se 1 (by rfl) ⟨1389431, by rfl⟩ : syracuseStep 1852575 = 2778863) B2778863
theorem B6251687 : Blo 1851627 6251687 := bstep (se 1 (by rfl) ⟨4688765, by rfl⟩ : syracuseStep 6251687 = 9377531) B9377531
theorem B1852647 : Blo 1851627 1852647 := bstep (se 1 (by rfl) ⟨1389485, by rfl⟩ : syracuseStep 1852647 = 2778971) B2778971
theorem B5276947 : Blo 1851627 5276947 := bstep (se 1 (by rfl) ⟨3957710, by rfl⟩ : syracuseStep 5276947 = 7915421) B7915421
theorem B1189676369 : Blo 1851627 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B6677959 : Blo 1851627 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B3515899 : Blo 1851627 3515899 := bstep (se 1 (by rfl) ⟨2636924, by rfl⟩ : syracuseStep 3515899 = 5273849) B5273849
theorem B1853087 : Blo 1851627 1853087 := bstep (se 1 (by rfl) ⟨1389815, by rfl⟩ : syracuseStep 1853087 = 2779631) B2779631
theorem B4687591 : Blo 1851627 4687591 := bstep (se 1 (by rfl) ⟨3515693, by rfl⟩ : syracuseStep 4687591 = 7031387) B7031387
theorem B1853295 : Blo 1851627 1853295 := bstep (se 1 (by rfl) ⟨1389971, by rfl⟩ : syracuseStep 1853295 = 2779943) B2779943
theorem B14067755 : Blo 1851627 14067755 := bstep (se 1 (by rfl) ⟨10550816, by rfl⟩ : syracuseStep 14067755 = 21101633) B21101633
theorem B2345051 : Blo 1851627 2345051 := bstep (se 1 (by rfl) ⟨1758788, by rfl⟩ : syracuseStep 2345051 = 3517577) B3517577
theorem B68520113 : Blo 1851627 68520113 := bstep (se 2 (by rfl) ⟨25695042, by rfl⟩ : syracuseStep 68520113 = 51390085) B51390085
theorem B2779547 : Blo 1851627 2779547 := bstep (se 1 (by rfl) ⟨2084660, by rfl⟩ : syracuseStep 2779547 = 4169321) B4169321
theorem B3754439 : Blo 1851627 3754439 := bstep (se 1 (by rfl) ⟨2815829, by rfl⟩ : syracuseStep 3754439 = 5631659) B5631659
theorem B10545623 : Blo 1851627 10545623 := bstep (se 1 (by rfl) ⟨7909217, by rfl⟩ : syracuseStep 10545623 = 15818435) B15818435
theorem B9382391 : Blo 1851627 9382391 := bstep (se 1 (by rfl) ⟨7036793, by rfl⟩ : syracuseStep 9382391 = 14073587) B14073587
theorem B2083567 : Blo 1851627 2083567 := bstep (se 1 (by rfl) ⟨1562675, by rfl⟩ : syracuseStep 2083567 = 3125351) B3125351
theorem B2779913 : Blo 1851627 2779913 := bstep (se 2 (by rfl) ⟨1042467, by rfl⟩ : syracuseStep 2779913 = 2084935) B2084935
theorem B21097259 : Blo 1851627 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B202902515 : Blo 1851627 202902515 := bstep (se 1 (by rfl) ⟨152176886, by rfl⟩ : syracuseStep 202902515 = 304353773) B304353773
theorem B16035023 : Blo 1851627 16035023 := bstep (se 1 (by rfl) ⟨12026267, by rfl⟩ : syracuseStep 16035023 = 24052535) B24052535
theorem B67611995 : Blo 1851627 67611995 := bstep (se 1 (by rfl) ⟨50708996, by rfl⟩ : syracuseStep 67611995 = 101417993) B101417993
theorem B4452011 : Blo 1851627 4452011 := bstep (se 1 (by rfl) ⟨3339008, by rfl⟩ : syracuseStep 4452011 = 6678017) B6678017
theorem B31641515 : Blo 1851627 31641515 := bstep (se 1 (by rfl) ⟨23731136, by rfl⟩ : syracuseStep 31641515 = 47462273) B47462273
theorem B7917659 : Blo 1851627 7917659 := bstep (se 1 (by rfl) ⟨5938244, by rfl⟩ : syracuseStep 7917659 = 11876489) B11876489
theorem B14070671 : Blo 1851627 14070671 := bstep (se 1 (by rfl) ⟨10553003, by rfl⟩ : syracuseStep 14070671 = 21106007) B21106007
theorem B6255575 : Blo 1851627 6255575 := bstep (se 1 (by rfl) ⟨4691681, by rfl⟩ : syracuseStep 6255575 = 9383363) B9383363
theorem B24400925 : Blo 1851627 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B21100175 : Blo 1851627 21100175 := bstep (se 1 (by rfl) ⟨15825131, by rfl⟩ : syracuseStep 21100175 = 31650263) B31650263
theorem B15439535 : Blo 1851627 15439535 := bstep (se 1 (by rfl) ⟨11579651, by rfl⟩ : syracuseStep 15439535 = 23159303) B23159303
theorem B9377693 : Blo 1851627 9377693 := bstep (se 3 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 9377693 = 3516635) B3516635
theorem B17799583 : Blo 1851627 17799583 := bstep (se 1 (by rfl) ⟨13349687, by rfl⟩ : syracuseStep 17799583 = 26699375) B26699375
theorem B3127801 : Blo 1851627 3127801 := bstep (se 2 (by rfl) ⟨1172925, by rfl⟩ : syracuseStep 3127801 = 2345851) B2345851
theorem B5937695 : Blo 1851627 5937695 := bstep (se 1 (by rfl) ⟨4453271, by rfl⟩ : syracuseStep 5937695 = 8906543) B8906543
theorem B9509501 : Blo 1851627 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B26712989 : Blo 1851627 26712989 := bstep (se 3 (by rfl) ⟨5008685, by rfl⟩ : syracuseStep 26712989 = 10017371) B10017371
theorem B30055481 : Blo 1851627 30055481 := bstep (se 2 (by rfl) ⟨11270805, by rfl⟩ : syracuseStep 30055481 = 22541611) B22541611
theorem B4168799 : Blo 1851627 4168799 := bstep (se 1 (by rfl) ⟨3126599, by rfl⟩ : syracuseStep 4168799 = 6253199) B6253199
theorem B40058063 : Blo 1851627 40058063 := bstep (se 1 (by rfl) ⟨30043547, by rfl⟩ : syracuseStep 40058063 = 60087095) B60087095
theorem B50691379 : Blo 1851627 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B4169033 : Blo 1851627 4169033 := bstep (se 2 (by rfl) ⟨1563387, by rfl⟩ : syracuseStep 4169033 = 3126775) B3126775
theorem B6249851 : Blo 1851627 6249851 := bstep (se 1 (by rfl) ⟨4687388, by rfl⟩ : syracuseStep 6249851 = 9374777) B9374777
theorem B2637289 : Blo 1851627 2637289 := bstep (se 2 (by rfl) ⟨988983, by rfl⟩ : syracuseStep 2637289 = 1977967) B1977967
theorem B22535729 : Blo 1851627 22535729 := bstep (se 2 (by rfl) ⟨8450898, by rfl⟩ : syracuseStep 22535729 = 16901797) B16901797
theorem B10018367 : Blo 1851627 10018367 := bstep (se 1 (by rfl) ⟨7513775, by rfl⟩ : syracuseStep 10018367 = 15027551) B15027551
theorem B31309537 : Blo 1851627 31309537 := bstep (se 2 (by rfl) ⟨11741076, by rfl⟩ : syracuseStep 31309537 = 23482153) B23482153
theorem B8019695 : Blo 1851627 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B40050449 : Blo 1851627 40050449 := bstep (se 2 (by rfl) ⟨15018918, by rfl⟩ : syracuseStep 40050449 = 30037837) B30037837
theorem B3956617 : Blo 1851627 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B10010537 : Blo 1851627 10010537 := bstep (se 2 (by rfl) ⟨3753951, by rfl⟩ : syracuseStep 10010537 = 7507903) B7507903
theorem B80134109 : Blo 1851627 80134109 := bstep (se 3 (by rfl) ⟨15025145, by rfl⟩ : syracuseStep 80134109 = 30050291) B30050291
theorem B15827183 : Blo 1851627 15827183 := bstep (se 1 (by rfl) ⟨11870387, by rfl⟩ : syracuseStep 15827183 = 23740775) B23740775
theorem B23732777 : Blo 1851627 23732777 := bstep (se 2 (by rfl) ⟨8899791, by rfl⟩ : syracuseStep 23732777 = 17799583) B17799583
theorem B9380447 : Blo 1851627 9380447 := bstep (se 1 (by rfl) ⟨7035335, by rfl⟩ : syracuseStep 9380447 = 14070671) B14070671
theorem B4170383 : Blo 1851627 4170383 := bstep (se 1 (by rfl) ⟨3127787, by rfl⟩ : syracuseStep 4170383 = 6255575) B6255575
theorem B4170401 : Blo 1851627 4170401 := bstep (se 2 (by rfl) ⟨1563900, by rfl⟩ : syracuseStep 4170401 = 3127801) B3127801
theorem B31654637 : Blo 1851627 31654637 := bstep (se 3 (by rfl) ⟨5935244, by rfl⟩ : syracuseStep 31654637 = 11870489) B11870489
theorem B2778089 : Blo 1851627 2778089 := bstep (se 2 (by rfl) ⟨1041783, by rfl⟩ : syracuseStep 2778089 = 2083567) B2083567
theorem B14066783 : Blo 1851627 14066783 := bstep (se 1 (by rfl) ⟨10550087, by rfl⟩ : syracuseStep 14066783 = 21100175) B21100175
theorem B6251795 : Blo 1851627 6251795 := bstep (se 1 (by rfl) ⟨4688846, by rfl⟩ : syracuseStep 6251795 = 9377693) B9377693
theorem B45680075 : Blo 1851627 45680075 := bstep (se 1 (by rfl) ⟨34260056, by rfl⟩ : syracuseStep 45680075 = 68520113) B68520113
theorem B1853031 : Blo 1851627 1853031 := bstep (se 1 (by rfl) ⟨1389773, by rfl⟩ : syracuseStep 1853031 = 2779547) B2779547
theorem B7030415 : Blo 1851627 7030415 := bstep (se 1 (by rfl) ⟨5272811, by rfl⟩ : syracuseStep 7030415 = 10545623) B10545623
theorem B3958463 : Blo 1851627 3958463 := bstep (se 1 (by rfl) ⟨2968847, by rfl⟩ : syracuseStep 3958463 = 5937695) B5937695
theorem B1853275 : Blo 1851627 1853275 := bstep (se 1 (by rfl) ⟨1389956, by rfl⟩ : syracuseStep 1853275 = 2779913) B2779913
theorem B3516385 : Blo 1851627 3516385 := bstep (se 2 (by rfl) ⟨1318644, by rfl⟩ : syracuseStep 3516385 = 2637289) B2637289
theorem B4687865 : Blo 1851627 4687865 := bstep (se 2 (by rfl) ⟨1757949, by rfl⟩ : syracuseStep 4687865 = 3515899) B3515899
theorem B135268343 : Blo 1851627 135268343 := bstep (se 1 (by rfl) ⟨101451257, by rfl⟩ : syracuseStep 135268343 = 202902515) B202902515
theorem B2779199 : Blo 1851627 2779199 := bstep (se 1 (by rfl) ⟨2084399, by rfl⟩ : syracuseStep 2779199 = 4168799) B4168799
theorem B2779355 : Blo 1851627 2779355 := bstep (se 1 (by rfl) ⟨2084516, by rfl⟩ : syracuseStep 2779355 = 4169033) B4169033
theorem B45074663 : Blo 1851627 45074663 := bstep (se 1 (by rfl) ⟨33805997, by rfl⟩ : syracuseStep 45074663 = 67611995) B67611995
theorem B6678911 : Blo 1851627 6678911 := bstep (se 1 (by rfl) ⟨5009183, by rfl⟩ : syracuseStep 6678911 = 10018367) B10018367
theorem B2968007 : Blo 1851627 2968007 := bstep (se 1 (by rfl) ⟨2226005, by rfl⟩ : syracuseStep 2968007 = 4452011) B4452011
theorem B26700299 : Blo 1851627 26700299 := bstep (se 1 (by rfl) ⟨20025224, by rfl⟩ : syracuseStep 26700299 = 40050449) B40050449
theorem B53422739 : Blo 1851627 53422739 := bstep (se 1 (by rfl) ⟨40067054, by rfl⟩ : syracuseStep 53422739 = 80134109) B80134109
theorem B5278439 : Blo 1851627 5278439 := bstep (se 1 (by rfl) ⟨3958829, by rfl⟩ : syracuseStep 5278439 = 7917659) B7917659
theorem B2779931 : Blo 1851627 2779931 := bstep (se 1 (by rfl) ⟨2084948, by rfl⟩ : syracuseStep 2779931 = 4169897) B4169897
theorem B2780015 : Blo 1851627 2780015 := bstep (se 1 (by rfl) ⟨2085011, by rfl⟩ : syracuseStep 2780015 = 4170023) B4170023
theorem B6253469 : Blo 1851627 6253469 := bstep (se 3 (by rfl) ⟨1172525, by rfl⟩ : syracuseStep 6253469 = 2345051) B2345051
theorem B8449019 : Blo 1851627 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B2780315 : Blo 1851627 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B2780327 : Blo 1851627 2780327 := bstep (se 1 (by rfl) ⟨2085245, by rfl⟩ : syracuseStep 2780327 = 4170491) B4170491
theorem B23735753 : Blo 1851627 23735753 := bstep (se 2 (by rfl) ⟨8900907, by rfl⟩ : syracuseStep 23735753 = 17801815) B17801815
theorem B3172470317 : Blo 1851627 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B10293023 : Blo 1851627 10293023 := bstep (se 1 (by rfl) ⟨7719767, by rfl⟩ : syracuseStep 10293023 = 15439535) B15439535
theorem B2502959 : Blo 1851627 2502959 := bstep (se 1 (by rfl) ⟨1877219, by rfl⟩ : syracuseStep 2502959 = 3754439) B3754439
theorem B6254927 : Blo 1851627 6254927 := bstep (se 1 (by rfl) ⟨4691195, by rfl⟩ : syracuseStep 6254927 = 9382391) B9382391
theorem B67588505 : Blo 1851627 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B21385853 : Blo 1851627 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B4166567 : Blo 1851627 4166567 := bstep (se 1 (by rfl) ⟨3124925, by rfl⟩ : syracuseStep 4166567 = 6249851) B6249851
theorem B6673691 : Blo 1851627 6673691 := bstep (se 1 (by rfl) ⟨5005268, by rfl⟩ : syracuseStep 6673691 = 10010537) B10010537
theorem B12195539 : Blo 1851627 12195539 := bstep (se 1 (by rfl) ⟨9146654, by rfl⟩ : syracuseStep 12195539 = 18293309) B18293309
theorem B16267283 : Blo 1851627 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B4167791 : Blo 1851627 4167791 := bstep (se 1 (by rfl) ⟨3125843, by rfl⟩ : syracuseStep 4167791 = 6251687) B6251687
theorem B9378503 : Blo 1851627 9378503 := bstep (se 1 (by rfl) ⟨7033877, by rfl⟩ : syracuseStep 9378503 = 14067755) B14067755
theorem B7035929 : Blo 1851627 7035929 := bstep (se 2 (by rfl) ⟨2638473, by rfl⟩ : syracuseStep 7035929 = 5276947) B5276947
theorem B6339667 : Blo 1851627 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B14064839 : Blo 1851627 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B8903945 : Blo 1851627 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B17808659 : Blo 1851627 17808659 := bstep (se 1 (by rfl) ⟨13356494, by rfl⟩ : syracuseStep 17808659 = 26712989) B26712989
theorem B20036987 : Blo 1851627 20036987 := bstep (se 1 (by rfl) ⟨15027740, by rfl⟩ : syracuseStep 20036987 = 30055481) B30055481
theorem B10690015 : Blo 1851627 10690015 := bstep (se 1 (by rfl) ⟨8017511, by rfl⟩ : syracuseStep 10690015 = 16035023) B16035023
theorem B26705375 : Blo 1851627 26705375 := bstep (se 1 (by rfl) ⟨20029031, by rfl⟩ : syracuseStep 26705375 = 40058063) B40058063
theorem B41746049 : Blo 1851627 41746049 := bstep (se 2 (by rfl) ⟨15654768, by rfl⟩ : syracuseStep 41746049 = 31309537) B31309537
theorem B6250121 : Blo 1851627 6250121 := bstep (se 2 (by rfl) ⟨2343795, by rfl⟩ : syracuseStep 6250121 = 4687591) B4687591
theorem B15023819 : Blo 1851627 15023819 := bstep (se 1 (by rfl) ⟨11267864, by rfl⟩ : syracuseStep 15023819 = 22535729) B22535729
theorem B5275489 : Blo 1851627 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B21094343 : Blo 1851627 21094343 := bstep (se 1 (by rfl) ⟨15820757, by rfl⟩ : syracuseStep 21094343 = 31641515) B31641515
theorem B10551455 : Blo 1851627 10551455 := bstep (se 1 (by rfl) ⟨7913591, by rfl⟩ : syracuseStep 10551455 = 15827183) B15827183
theorem B4169951 : Blo 1851627 4169951 := bstep (se 1 (by rfl) ⟨3127463, by rfl⟩ : syracuseStep 4169951 = 6254927) B6254927
theorem B21103091 : Blo 1851627 21103091 := bstep (se 1 (by rfl) ⟨15827318, by rfl⟩ : syracuseStep 21103091 = 31654637) B31654637
theorem B2777711 : Blo 1851627 2777711 := bstep (se 1 (by rfl) ⟨2083283, by rfl⟩ : syracuseStep 2777711 = 4166567) B4166567
theorem B1852059 : Blo 1851627 1852059 := bstep (se 1 (by rfl) ⟨1389044, by rfl⟩ : syracuseStep 1852059 = 2778089) B2778089
theorem B4686943 : Blo 1851627 4686943 := bstep (se 1 (by rfl) ⟨3515207, by rfl⟩ : syracuseStep 4686943 = 7030415) B7030415
theorem B2638975 : Blo 1851627 2638975 := bstep (se 1 (by rfl) ⟨1979231, by rfl⟩ : syracuseStep 2638975 = 3958463) B3958463
theorem B7914685 : Blo 1851627 7914685 := bstep (se 3 (by rfl) ⟨1484003, by rfl⟩ : syracuseStep 7914685 = 2968007) B2968007
theorem B90178895 : Blo 1851627 90178895 := bstep (se 1 (by rfl) ⟨67634171, by rfl⟩ : syracuseStep 90178895 = 135268343) B135268343
theorem B1852799 : Blo 1851627 1852799 := bstep (se 1 (by rfl) ⟨1389599, by rfl⟩ : syracuseStep 1852799 = 2779199) B2779199
theorem B2778527 : Blo 1851627 2778527 := bstep (se 1 (by rfl) ⟨2083895, by rfl⟩ : syracuseStep 2778527 = 4167791) B4167791
theorem B1852903 : Blo 1851627 1852903 := bstep (se 1 (by rfl) ⟨1389677, by rfl⟩ : syracuseStep 1852903 = 2779355) B2779355
theorem B30049775 : Blo 1851627 30049775 := bstep (se 1 (by rfl) ⟨22537331, by rfl⟩ : syracuseStep 30049775 = 45074663) B45074663
theorem B6252335 : Blo 1851627 6252335 := bstep (se 1 (by rfl) ⟨4689251, by rfl⟩ : syracuseStep 6252335 = 9378503) B9378503
theorem B1853287 : Blo 1851627 1853287 := bstep (se 1 (by rfl) ⟨1389965, by rfl⟩ : syracuseStep 1853287 = 2779931) B2779931
theorem B1853343 : Blo 1851627 1853343 := bstep (se 1 (by rfl) ⟨1390007, by rfl⟩ : syracuseStep 1853343 = 2780015) B2780015
theorem B1853543 : Blo 1851627 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B1853551 : Blo 1851627 1853551 := bstep (se 1 (by rfl) ⟨1390163, by rfl⟩ : syracuseStep 1853551 = 2780327) B2780327
theorem B11872439 : Blo 1851627 11872439 := bstep (se 1 (by rfl) ⟨8904329, by rfl⟩ : syracuseStep 11872439 = 17808659) B17808659
theorem B17803583 : Blo 1851627 17803583 := bstep (se 1 (by rfl) ⟨13352687, by rfl⟩ : syracuseStep 17803583 = 26705375) B26705375
theorem B2114980211 : Blo 1851627 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B27830699 : Blo 1851627 27830699 := bstep (se 1 (by rfl) ⟨20873024, by rfl⟩ : syracuseStep 27830699 = 41746049) B41746049
theorem B4688513 : Blo 1851627 4688513 := bstep (se 2 (by rfl) ⟨1758192, by rfl⟩ : syracuseStep 4688513 = 3516385) B3516385
theorem B45059003 : Blo 1851627 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B15821851 : Blo 1851627 15821851 := bstep (se 1 (by rfl) ⟨11866388, by rfl⟩ : syracuseStep 15821851 = 23732777) B23732777
theorem B6253631 : Blo 1851627 6253631 := bstep (se 1 (by rfl) ⟨4690223, by rfl⟩ : syracuseStep 6253631 = 9380447) B9380447
theorem B14257235 : Blo 1851627 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B2780255 : Blo 1851627 2780255 := bstep (se 1 (by rfl) ⟨2085191, by rfl⟩ : syracuseStep 2780255 = 4170383) B4170383
theorem B2780267 : Blo 1851627 2780267 := bstep (se 1 (by rfl) ⟨2085200, by rfl⟩ : syracuseStep 2780267 = 4170401) B4170401
theorem B17796509 : Blo 1851627 17796509 := bstep (se 3 (by rfl) ⟨3336845, by rfl⟩ : syracuseStep 17796509 = 6673691) B6673691
theorem B30453383 : Blo 1851627 30453383 := bstep (se 1 (by rfl) ⟨22840037, by rfl⟩ : syracuseStep 30453383 = 45680075) B45680075
theorem B8130359 : Blo 1851627 8130359 := bstep (se 1 (by rfl) ⟨6097769, by rfl⟩ : syracuseStep 8130359 = 12195539) B12195539
theorem B3125243 : Blo 1851627 3125243 := bstep (se 1 (by rfl) ⟨2343932, by rfl⟩ : syracuseStep 3125243 = 4687865) B4687865
theorem B4452607 : Blo 1851627 4452607 := bstep (se 1 (by rfl) ⟨3339455, by rfl⟩ : syracuseStep 4452607 = 6678911) B6678911
theorem B35615159 : Blo 1851627 35615159 := bstep (se 1 (by rfl) ⟨26711369, by rfl⟩ : syracuseStep 35615159 = 53422739) B53422739
theorem B3518959 : Blo 1851627 3518959 := bstep (se 1 (by rfl) ⟨2639219, by rfl⟩ : syracuseStep 3518959 = 5278439) B5278439
theorem B40063517 : Blo 1851627 40063517 := bstep (se 3 (by rfl) ⟨7511909, by rfl⟩ : syracuseStep 40063517 = 15023819) B15023819
theorem B5632679 : Blo 1851627 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B4690619 : Blo 1851627 4690619 := bstep (se 1 (by rfl) ⟨3517964, by rfl⟩ : syracuseStep 4690619 = 7035929) B7035929
theorem B9376559 : Blo 1851627 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B5935963 : Blo 1851627 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B13357991 : Blo 1851627 13357991 := bstep (se 1 (by rfl) ⟨10018493, by rfl⟩ : syracuseStep 13357991 = 20036987) B20036987
theorem B15823835 : Blo 1851627 15823835 := bstep (se 1 (by rfl) ⟨11867876, by rfl⟩ : syracuseStep 15823835 = 23735753) B23735753
theorem B4166747 : Blo 1851627 4166747 := bstep (se 1 (by rfl) ⟨3125060, by rfl⟩ : syracuseStep 4166747 = 6250121) B6250121
theorem B7033985 : Blo 1851627 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B6862015 : Blo 1851627 6862015 := bstep (se 1 (by rfl) ⟨5146511, by rfl⟩ : syracuseStep 6862015 = 10293023) B10293023
theorem B14062895 : Blo 1851627 14062895 := bstep (se 1 (by rfl) ⟨10547171, by rfl⟩ : syracuseStep 14062895 = 21094343) B21094343
theorem B9377855 : Blo 1851627 9377855 := bstep (se 1 (by rfl) ⟨7033391, by rfl⟩ : syracuseStep 9377855 = 14066783) B14066783
theorem B6674557 : Blo 1851627 6674557 := bstep (se 3 (by rfl) ⟨1251479, by rfl⟩ : syracuseStep 6674557 = 2502959) B2502959
theorem B4167863 : Blo 1851627 4167863 := bstep (se 1 (by rfl) ⟨3125897, by rfl⟩ : syracuseStep 4167863 = 6251795) B6251795
theorem B10844855 : Blo 1851627 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B8452889 : Blo 1851627 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B17800199 : Blo 1851627 17800199 := bstep (se 1 (by rfl) ⟨13350149, by rfl⟩ : syracuseStep 17800199 = 26700299) B26700299
theorem B4168979 : Blo 1851627 4168979 := bstep (se 1 (by rfl) ⟨3126734, by rfl⟩ : syracuseStep 4168979 = 6253469) B6253469
theorem B14253353 : Blo 1851627 14253353 := bstep (se 2 (by rfl) ⟨5345007, by rfl⟩ : syracuseStep 14253353 = 10690015) B10690015
theorem B1851807 : Blo 1851627 1851807 := bstep (se 1 (by rfl) ⟨1388855, by rfl⟩ : syracuseStep 1851807 = 2777711) B2777711
theorem B6251039 : Blo 1851627 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B2777831 : Blo 1851627 2777831 := bstep (se 1 (by rfl) ⟨2083373, by rfl⟩ : syracuseStep 2777831 = 4166747) B4166747
theorem B1852351 : Blo 1851627 1852351 := bstep (se 1 (by rfl) ⟨1389263, by rfl⟩ : syracuseStep 1852351 = 2778527) B2778527
theorem B7914617 : Blo 1851627 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B21095801 : Blo 1851627 21095801 := bstep (se 2 (by rfl) ⟨7910925, by rfl⟩ : syracuseStep 21095801 = 15821851) B15821851
theorem B6251903 : Blo 1851627 6251903 := bstep (se 1 (by rfl) ⟨4688927, by rfl⟩ : syracuseStep 6251903 = 9377855) B9377855
theorem B2778575 : Blo 1851627 2778575 := bstep (se 1 (by rfl) ⟨2083931, by rfl⟩ : syracuseStep 2778575 = 4167863) B4167863
theorem B7914959 : Blo 1851627 7914959 := bstep (se 1 (by rfl) ⟨5936219, by rfl⟩ : syracuseStep 7914959 = 11872439) B11872439
theorem B10552913 : Blo 1851627 10552913 := bstep (se 2 (by rfl) ⟨3957342, by rfl⟩ : syracuseStep 10552913 = 7914685) B7914685
theorem B9504823 : Blo 1851627 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B1853503 : Blo 1851627 1853503 := bstep (se 1 (by rfl) ⟨1390127, by rfl⟩ : syracuseStep 1853503 = 2780255) B2780255
theorem B1853511 : Blo 1851627 1853511 := bstep (se 1 (by rfl) ⟨1390133, by rfl⟩ : syracuseStep 1853511 = 2780267) B2780267
theorem B2779319 : Blo 1851627 2779319 := bstep (se 1 (by rfl) ⟨2084489, by rfl⟩ : syracuseStep 2779319 = 4168979) B4168979
theorem B11864339 : Blo 1851627 11864339 := bstep (se 1 (by rfl) ⟨8898254, by rfl⟩ : syracuseStep 11864339 = 17796509) B17796509
theorem B20302255 : Blo 1851627 20302255 := bstep (se 1 (by rfl) ⟨15226691, by rfl⟩ : syracuseStep 20302255 = 30453383) B30453383
theorem B35621309 : Blo 1851627 35621309 := bstep (se 3 (by rfl) ⟨6678995, by rfl⟩ : syracuseStep 35621309 = 13357991) B13357991
theorem B2083495 : Blo 1851627 2083495 := bstep (se 1 (by rfl) ⟨1562621, by rfl⟩ : syracuseStep 2083495 = 3125243) B3125243
theorem B2779967 : Blo 1851627 2779967 := bstep (se 1 (by rfl) ⟨2084975, by rfl⟩ : syracuseStep 2779967 = 4169951) B4169951
theorem B8899409 : Blo 1851627 8899409 := bstep (se 2 (by rfl) ⟨3337278, by rfl⟩ : syracuseStep 8899409 = 6674557) B6674557
theorem B23743439 : Blo 1851627 23743439 := bstep (se 1 (by rfl) ⟨17807579, by rfl⟩ : syracuseStep 23743439 = 35615159) B35615159
theorem B14068727 : Blo 1851627 14068727 := bstep (se 1 (by rfl) ⟨10551545, by rfl⟩ : syracuseStep 14068727 = 21103091) B21103091
theorem B26709011 : Blo 1851627 26709011 := bstep (se 1 (by rfl) ⟨20031758, by rfl⟩ : syracuseStep 26709011 = 40063517) B40063517
theorem B4689323 : Blo 1851627 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B9375263 : Blo 1851627 9375263 := bstep (se 1 (by rfl) ⟨7031447, by rfl⟩ : syracuseStep 9375263 = 14062895) B14062895
theorem B20033183 : Blo 1851627 20033183 := bstep (se 1 (by rfl) ⟨15024887, by rfl⟩ : syracuseStep 20033183 = 30049775) B30049775
theorem B36597413 : Blo 1851627 36597413 := bstep (se 4 (by rfl) ⟨3431007, by rfl⟩ : syracuseStep 36597413 = 6862015) B6862015
theorem B3518633 : Blo 1851627 3518633 := bstep (se 2 (by rfl) ⟨1319487, by rfl⟩ : syracuseStep 3518633 = 2638975) B2638975
theorem B1409986807 : Blo 1851627 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B3125675 : Blo 1851627 3125675 := bstep (se 1 (by rfl) ⟨2344256, by rfl⟩ : syracuseStep 3125675 = 4688513) B4688513
theorem B15020477 : Blo 1851627 15020477 := bstep (se 3 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 15020477 = 5632679) B5632679
theorem B7229903 : Blo 1851627 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B11866799 : Blo 1851627 11866799 := bstep (se 1 (by rfl) ⟨8900099, by rfl⟩ : syracuseStep 11866799 = 17800199) B17800199
theorem B5420239 : Blo 1851627 5420239 := bstep (se 1 (by rfl) ⟨4065179, by rfl⟩ : syracuseStep 5420239 = 8130359) B8130359
theorem B7034303 : Blo 1851627 7034303 := bstep (se 1 (by rfl) ⟨5275727, by rfl⟩ : syracuseStep 7034303 = 10551455) B10551455
theorem B5936809 : Blo 1851627 5936809 := bstep (se 2 (by rfl) ⟨2226303, by rfl⟩ : syracuseStep 5936809 = 4452607) B4452607
theorem B3127079 : Blo 1851627 3127079 := bstep (se 1 (by rfl) ⟨2345309, by rfl⟩ : syracuseStep 3127079 = 4690619) B4690619
theorem B10549223 : Blo 1851627 10549223 := bstep (se 1 (by rfl) ⟨7911917, by rfl⟩ : syracuseStep 10549223 = 15823835) B15823835
theorem B4691945 : Blo 1851627 4691945 := bstep (se 2 (by rfl) ⟨1759479, by rfl⟩ : syracuseStep 4691945 = 3518959) B3518959
theorem B60119263 : Blo 1851627 60119263 := bstep (se 1 (by rfl) ⟨45089447, by rfl⟩ : syracuseStep 60119263 = 90178895) B90178895
theorem B4168223 : Blo 1851627 4168223 := bstep (se 1 (by rfl) ⟨3126167, by rfl⟩ : syracuseStep 4168223 = 6252335) B6252335
theorem B6249257 : Blo 1851627 6249257 := bstep (se 2 (by rfl) ⟨2343471, by rfl⟩ : syracuseStep 6249257 = 4686943) B4686943
theorem B11869055 : Blo 1851627 11869055 := bstep (se 1 (by rfl) ⟨8901791, by rfl⟩ : syracuseStep 11869055 = 17803583) B17803583
theorem B18553799 : Blo 1851627 18553799 := bstep (se 1 (by rfl) ⟨13915349, by rfl⟩ : syracuseStep 18553799 = 27830699) B27830699
theorem B5635259 : Blo 1851627 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B30039335 : Blo 1851627 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B4169087 : Blo 1851627 4169087 := bstep (se 1 (by rfl) ⟨3126815, by rfl⟩ : syracuseStep 4169087 = 6253631) B6253631
theorem B9502235 : Blo 1851627 9502235 := bstep (se 1 (by rfl) ⟨7126676, by rfl⟩ : syracuseStep 9502235 = 14253353) B14253353
theorem B12673097 : Blo 1851627 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B80159017 : Blo 1851627 80159017 := bstep (se 2 (by rfl) ⟨30059631, by rfl⟩ : syracuseStep 80159017 = 60119263) B60119263
theorem B1851887 : Blo 1851627 1851887 := bstep (se 1 (by rfl) ⟨1388915, by rfl⟩ : syracuseStep 1851887 = 2777831) B2777831
theorem B5276411 : Blo 1851627 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2777993 : Blo 1851627 2777993 := bstep (se 2 (by rfl) ⟨1041747, by rfl⟩ : syracuseStep 2777993 = 2083495) B2083495
theorem B1852383 : Blo 1851627 1852383 := bstep (se 1 (by rfl) ⟨1389287, by rfl⟩ : syracuseStep 1852383 = 2778575) B2778575
theorem B5276639 : Blo 1851627 5276639 := bstep (se 1 (by rfl) ⟨3957479, by rfl⟩ : syracuseStep 5276639 = 7914959) B7914959
theorem B1852879 : Blo 1851627 1852879 := bstep (se 1 (by rfl) ⟨1389659, by rfl⟩ : syracuseStep 1852879 = 2779319) B2779319
theorem B2778815 : Blo 1851627 2778815 := bstep (se 1 (by rfl) ⟨2084111, by rfl⟩ : syracuseStep 2778815 = 4168223) B4168223
theorem B1853311 : Blo 1851627 1853311 := bstep (se 1 (by rfl) ⟨1389983, by rfl⟩ : syracuseStep 1853311 = 2779967) B2779967
theorem B5932939 : Blo 1851627 5932939 := bstep (se 1 (by rfl) ⟨4449704, by rfl⟩ : syracuseStep 5932939 = 8899409) B8899409
theorem B15828959 : Blo 1851627 15828959 := bstep (se 1 (by rfl) ⟨11871719, by rfl⟩ : syracuseStep 15828959 = 23743439) B23743439
theorem B7915745 : Blo 1851627 7915745 := bstep (se 2 (by rfl) ⟨2968404, by rfl⟩ : syracuseStep 7915745 = 5936809) B5936809
theorem B2779391 : Blo 1851627 2779391 := bstep (se 1 (by rfl) ⟨2084543, by rfl⟩ : syracuseStep 2779391 = 4169087) B4169087
theorem B6334823 : Blo 1851627 6334823 := bstep (se 1 (by rfl) ⟨4751117, by rfl⟩ : syracuseStep 6334823 = 9502235) B9502235
theorem B13355455 : Blo 1851627 13355455 := bstep (se 1 (by rfl) ⟨10016591, by rfl⟩ : syracuseStep 13355455 = 20033183) B20033183
theorem B24398275 : Blo 1851627 24398275 := bstep (se 1 (by rfl) ⟨18298706, by rfl⟩ : syracuseStep 24398275 = 36597413) B36597413
theorem B2345755 : Blo 1851627 2345755 := bstep (se 1 (by rfl) ⟨1759316, by rfl⟩ : syracuseStep 2345755 = 3518633) B3518633
theorem B2083783 : Blo 1851627 2083783 := bstep (se 1 (by rfl) ⟨1562837, by rfl⟩ : syracuseStep 2083783 = 3125675) B3125675
theorem B10013651 : Blo 1851627 10013651 := bstep (se 1 (by rfl) ⟨7510238, by rfl⟩ : syracuseStep 10013651 = 15020477) B15020477
theorem B27069673 : Blo 1851627 27069673 := bstep (se 2 (by rfl) ⟨10151127, by rfl⟩ : syracuseStep 27069673 = 20302255) B20302255
theorem B4689535 : Blo 1851627 4689535 := bstep (se 1 (by rfl) ⟨3517151, by rfl⟩ : syracuseStep 4689535 = 7034303) B7034303
theorem B2084719 : Blo 1851627 2084719 := bstep (se 1 (by rfl) ⟨1563539, by rfl⟩ : syracuseStep 2084719 = 3127079) B3127079
theorem B19279741 : Blo 1851627 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B7032815 : Blo 1851627 7032815 := bstep (se 1 (by rfl) ⟨5274611, by rfl⟩ : syracuseStep 7032815 = 10549223) B10549223
theorem B7909559 : Blo 1851627 7909559 := bstep (se 1 (by rfl) ⟨5932169, by rfl⟩ : syracuseStep 7909559 = 11864339) B11864339
theorem B4166171 : Blo 1851627 4166171 := bstep (se 1 (by rfl) ⟨3124628, by rfl⟩ : syracuseStep 4166171 = 6249257) B6249257
theorem B17806007 : Blo 1851627 17806007 := bstep (se 1 (by rfl) ⟨13354505, by rfl⟩ : syracuseStep 17806007 = 26709011) B26709011
theorem B3756839 : Blo 1851627 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B20026223 : Blo 1851627 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B3126215 : Blo 1851627 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B30079718549 : Blo 1851627 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B4167359 : Blo 1851627 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B7911199 : Blo 1851627 7911199 := bstep (se 1 (by rfl) ⟨5933399, by rfl⟩ : syracuseStep 7911199 = 11866799) B11866799
theorem B14063867 : Blo 1851627 14063867 := bstep (se 1 (by rfl) ⟨10547900, by rfl⟩ : syracuseStep 14063867 = 21095801) B21095801
theorem B4167935 : Blo 1851627 4167935 := bstep (se 1 (by rfl) ⟨3125951, by rfl⟩ : syracuseStep 4167935 = 6251903) B6251903
theorem B7035275 : Blo 1851627 7035275 := bstep (se 1 (by rfl) ⟨5276456, by rfl⟩ : syracuseStep 7035275 = 10552913) B10552913
theorem B28907941 : Blo 1851627 28907941 := bstep (se 4 (by rfl) ⟨2710119, by rfl⟩ : syracuseStep 28907941 = 5420239) B5420239
theorem B3127963 : Blo 1851627 3127963 := bstep (se 1 (by rfl) ⟨2345972, by rfl⟩ : syracuseStep 3127963 = 4691945) B4691945
theorem B23747539 : Blo 1851627 23747539 := bstep (se 1 (by rfl) ⟨17810654, by rfl⟩ : syracuseStep 23747539 = 35621309) B35621309
theorem B7912703 : Blo 1851627 7912703 := bstep (se 1 (by rfl) ⟨5934527, by rfl⟩ : syracuseStep 7912703 = 11869055) B11869055
theorem B12369199 : Blo 1851627 12369199 := bstep (se 1 (by rfl) ⟨9276899, by rfl⟩ : syracuseStep 12369199 = 18553799) B18553799
theorem B9379151 : Blo 1851627 9379151 := bstep (se 1 (by rfl) ⟨7034363, by rfl⟩ : syracuseStep 9379151 = 14068727) B14068727
theorem B6250175 : Blo 1851627 6250175 := bstep (se 1 (by rfl) ⟨4687631, by rfl⟩ : syracuseStep 6250175 = 9375263) B9375263
theorem B2777447 : Blo 1851627 2777447 := bstep (se 1 (by rfl) ⟨2083085, by rfl⟩ : syracuseStep 2777447 = 4166171) B4166171
theorem B11870671 : Blo 1851627 11870671 := bstep (se 1 (by rfl) ⟨8903003, by rfl⟩ : syracuseStep 11870671 = 17806007) B17806007
theorem B38543921 : Blo 1851627 38543921 := bstep (se 2 (by rfl) ⟨14453970, by rfl⟩ : syracuseStep 38543921 = 28907941) B28907941
theorem B32531033 : Blo 1851627 32531033 := bstep (se 2 (by rfl) ⟨12199137, by rfl⟩ : syracuseStep 32531033 = 24398275) B24398275
theorem B1851995 : Blo 1851627 1851995 := bstep (se 1 (by rfl) ⟨1388996, by rfl⟩ : syracuseStep 1851995 = 2777993) B2777993
theorem B4170617 : Blo 1851627 4170617 := bstep (se 2 (by rfl) ⟨1563981, by rfl⟩ : syracuseStep 4170617 = 3127963) B3127963
theorem B2778239 : Blo 1851627 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B1852543 : Blo 1851627 1852543 := bstep (se 1 (by rfl) ⟨1389407, by rfl⟩ : syracuseStep 1852543 = 2778815) B2778815
theorem B2778377 : Blo 1851627 2778377 := bstep (se 2 (by rfl) ⟨1041891, by rfl⟩ : syracuseStep 2778377 = 2083783) B2083783
theorem B31663385 : Blo 1851627 31663385 := bstep (se 2 (by rfl) ⟨11873769, by rfl⟩ : syracuseStep 31663385 = 23747539) B23747539
theorem B10552639 : Blo 1851627 10552639 := bstep (se 1 (by rfl) ⟨7914479, by rfl⟩ : syracuseStep 10552639 = 15828959) B15828959
theorem B5277163 : Blo 1851627 5277163 := bstep (se 1 (by rfl) ⟨3957872, by rfl⟩ : syracuseStep 5277163 = 7915745) B7915745
theorem B2778623 : Blo 1851627 2778623 := bstep (se 1 (by rfl) ⟨2083967, by rfl⟩ : syracuseStep 2778623 = 4167935) B4167935
theorem B1852927 : Blo 1851627 1852927 := bstep (se 1 (by rfl) ⟨1389695, by rfl⟩ : syracuseStep 1852927 = 2779391) B2779391
theorem B16492265 : Blo 1851627 16492265 := bstep (se 2 (by rfl) ⟨6184599, by rfl⟩ : syracuseStep 16492265 = 12369199) B12369199
theorem B6252713 : Blo 1851627 6252713 := bstep (se 2 (by rfl) ⟨2344767, by rfl⟩ : syracuseStep 6252713 = 4689535) B4689535
theorem B6252767 : Blo 1851627 6252767 := bstep (se 1 (by rfl) ⟨4689575, by rfl⟩ : syracuseStep 6252767 = 9379151) B9379151
theorem B2779625 : Blo 1851627 2779625 := bstep (se 2 (by rfl) ⟨1042359, by rfl⟩ : syracuseStep 2779625 = 2084719) B2084719
theorem B4688543 : Blo 1851627 4688543 := bstep (se 1 (by rfl) ⟨3516407, by rfl⟩ : syracuseStep 4688543 = 7032815) B7032815
theorem B8448731 : Blo 1851627 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B3517607 : Blo 1851627 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B2084143 : Blo 1851627 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B3517759 : Blo 1851627 3517759 := bstep (se 1 (by rfl) ⟨2638319, by rfl⟩ : syracuseStep 3517759 = 5276639) B5276639
theorem B9375911 : Blo 1851627 9375911 := bstep (se 1 (by rfl) ⟨7031933, by rfl⟩ : syracuseStep 9375911 = 14063867) B14063867
theorem B4223215 : Blo 1851627 4223215 := bstep (se 1 (by rfl) ⟨3167411, by rfl⟩ : syracuseStep 4223215 = 6334823) B6334823
theorem B4690183 : Blo 1851627 4690183 := bstep (se 1 (by rfl) ⟨3517637, by rfl⟩ : syracuseStep 4690183 = 7035275) B7035275
theorem B10548265 : Blo 1851627 10548265 := bstep (se 2 (by rfl) ⟨3955599, by rfl⟩ : syracuseStep 10548265 = 7911199) B7911199
theorem B4166783 : Blo 1851627 4166783 := bstep (se 1 (by rfl) ⟨3125087, by rfl⟩ : syracuseStep 4166783 = 6250175) B6250175
theorem B7910585 : Blo 1851627 7910585 := bstep (se 2 (by rfl) ⟨2966469, by rfl⟩ : syracuseStep 7910585 = 5932939) B5932939
theorem B5273039 : Blo 1851627 5273039 := bstep (se 1 (by rfl) ⟨3954779, by rfl⟩ : syracuseStep 5273039 = 7909559) B7909559
theorem B106878689 : Blo 1851627 106878689 := bstep (se 2 (by rfl) ⟨40079508, by rfl⟩ : syracuseStep 106878689 = 80159017) B80159017
theorem B13350815 : Blo 1851627 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B17807273 : Blo 1851627 17807273 := bstep (se 2 (by rfl) ⟨6677727, by rfl⟩ : syracuseStep 17807273 = 13355455) B13355455
theorem B20053145699 : Blo 1851627 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B3127673 : Blo 1851627 3127673 := bstep (se 2 (by rfl) ⟨1172877, by rfl⟩ : syracuseStep 3127673 = 2345755) B2345755
theorem B36092897 : Blo 1851627 36092897 := bstep (se 2 (by rfl) ⟨13534836, by rfl⟩ : syracuseStep 36092897 = 27069673) B27069673
theorem B6675767 : Blo 1851627 6675767 := bstep (se 1 (by rfl) ⟨5006825, by rfl⟩ : syracuseStep 6675767 = 10013651) B10013651
theorem B10018237 : Blo 1851627 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B5275135 : Blo 1851627 5275135 := bstep (se 1 (by rfl) ⟨3956351, by rfl⟩ : syracuseStep 5275135 = 7912703) B7912703
theorem B25706321 : Blo 1851627 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B6250607 : Blo 1851627 6250607 := bstep (se 1 (by rfl) ⟨4687955, by rfl⟩ : syracuseStep 6250607 = 9375911) B9375911
theorem B1851631 : Blo 1851627 1851631 := bstep (se 1 (by rfl) ⟨1388723, by rfl⟩ : syracuseStep 1851631 = 2777447) B2777447
theorem B9380285 : Blo 1851627 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B15827561 : Blo 1851627 15827561 := bstep (se 2 (by rfl) ⟨5935335, by rfl⟩ : syracuseStep 15827561 = 11870671) B11870671
theorem B2777855 : Blo 1851627 2777855 := bstep (se 1 (by rfl) ⟨2083391, by rfl⟩ : syracuseStep 2777855 = 4166783) B4166783
theorem B1852159 : Blo 1851627 1852159 := bstep (se 1 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 1852159 = 2778239) B2778239
theorem B1852251 : Blo 1851627 1852251 := bstep (se 1 (by rfl) ⟨1389188, by rfl⟩ : syracuseStep 1852251 = 2778377) B2778377
theorem B1852415 : Blo 1851627 1852415 := bstep (se 1 (by rfl) ⟨1389311, by rfl⟩ : syracuseStep 1852415 = 2778623) B2778623
theorem B11871515 : Blo 1851627 11871515 := bstep (se 1 (by rfl) ⟨8903636, by rfl⟩ : syracuseStep 11871515 = 17807273) B17807273
theorem B13368763799 : Blo 1851627 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B1853083 : Blo 1851627 1853083 := bstep (se 1 (by rfl) ⟨1389812, by rfl⟩ : syracuseStep 1853083 = 2779625) B2779625
theorem B2778857 : Blo 1851627 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B24061931 : Blo 1851627 24061931 := bstep (se 1 (by rfl) ⟨18046448, by rfl⟩ : syracuseStep 24061931 = 36092897) B36092897
theorem B4450511 : Blo 1851627 4450511 := bstep (se 1 (by rfl) ⟨3337883, by rfl⟩ : syracuseStep 4450511 = 6675767) B6675767
theorem B175917493 : Blo 1851627 175917493 := bstep (se 5 (by rfl) ⟨8246132, by rfl⟩ : syracuseStep 175917493 = 16492265) B16492265
theorem B5630953 : Blo 1851627 5630953 := bstep (se 2 (by rfl) ⟨2111607, by rfl⟩ : syracuseStep 5630953 = 4223215) B4223215
theorem B6253577 : Blo 1851627 6253577 := bstep (se 2 (by rfl) ⟨2345091, by rfl⟩ : syracuseStep 6253577 = 4690183) B4690183
theorem B21687355 : Blo 1851627 21687355 := bstep (se 1 (by rfl) ⟨16265516, by rfl⟩ : syracuseStep 21687355 = 32531033) B32531033
theorem B2780411 : Blo 1851627 2780411 := bstep (se 1 (by rfl) ⟨2085308, by rfl⟩ : syracuseStep 2780411 = 4170617) B4170617
theorem B14061437 : Blo 1851627 14061437 := bstep (se 3 (by rfl) ⟨2636519, by rfl⟩ : syracuseStep 14061437 = 5273039) B5273039
theorem B8900543 : Blo 1851627 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B2085115 : Blo 1851627 2085115 := bstep (se 1 (by rfl) ⟨1563836, by rfl⟩ : syracuseStep 2085115 = 3127673) B3127673
theorem B14070185 : Blo 1851627 14070185 := bstep (se 2 (by rfl) ⟨5276319, by rfl⟩ : syracuseStep 14070185 = 10552639) B10552639
theorem B4690345 : Blo 1851627 4690345 := bstep (se 2 (by rfl) ⟨1758879, by rfl⟩ : syracuseStep 4690345 = 3517759) B3517759
theorem B3125695 : Blo 1851627 3125695 := bstep (se 1 (by rfl) ⟨2344271, by rfl⟩ : syracuseStep 3125695 = 4688543) B4688543
theorem B5632487 : Blo 1851627 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B13357649 : Blo 1851627 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B7033513 : Blo 1851627 7033513 := bstep (se 2 (by rfl) ⟨2637567, by rfl⟩ : syracuseStep 7033513 = 5275135) B5275135
theorem B25695947 : Blo 1851627 25695947 := bstep (se 1 (by rfl) ⟨19271960, by rfl⟩ : syracuseStep 25695947 = 38543921) B38543921
theorem B5273723 : Blo 1851627 5273723 := bstep (se 1 (by rfl) ⟨3955292, by rfl⟩ : syracuseStep 5273723 = 7910585) B7910585
theorem B21108923 : Blo 1851627 21108923 := bstep (se 1 (by rfl) ⟨15831692, by rfl⟩ : syracuseStep 21108923 = 31663385) B31663385
theorem B71252459 : Blo 1851627 71252459 := bstep (se 1 (by rfl) ⟨53439344, by rfl⟩ : syracuseStep 71252459 = 106878689) B106878689
theorem B14064353 : Blo 1851627 14064353 := bstep (se 2 (by rfl) ⟨5274132, by rfl⟩ : syracuseStep 14064353 = 10548265) B10548265
theorem B4168475 : Blo 1851627 4168475 := bstep (se 1 (by rfl) ⟨3126356, by rfl⟩ : syracuseStep 4168475 = 6252713) B6252713
theorem B4168511 : Blo 1851627 4168511 := bstep (se 1 (by rfl) ⟨3126383, by rfl⟩ : syracuseStep 4168511 = 6252767) B6252767
theorem B7036217 : Blo 1851627 7036217 := bstep (se 2 (by rfl) ⟨2638581, by rfl⟩ : syracuseStep 7036217 = 5277163) B5277163
theorem B17137547 : Blo 1851627 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B9380123 : Blo 1851627 9380123 := bstep (se 1 (by rfl) ⟨7035092, by rfl⟩ : syracuseStep 9380123 = 14070185) B14070185
theorem B8905099 : Blo 1851627 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B10551707 : Blo 1851627 10551707 := bstep (se 1 (by rfl) ⟨7913780, by rfl⟩ : syracuseStep 10551707 = 15827561) B15827561
theorem B1851903 : Blo 1851627 1851903 := bstep (se 1 (by rfl) ⟨1388927, by rfl⟩ : syracuseStep 1851903 = 2777855) B2777855
theorem B7914343 : Blo 1851627 7914343 := bstep (se 1 (by rfl) ⟨5935757, by rfl⟩ : syracuseStep 7914343 = 11871515) B11871515
theorem B17130631 : Blo 1851627 17130631 := bstep (se 1 (by rfl) ⟨12847973, by rfl⟩ : syracuseStep 17130631 = 25695947) B25695947
theorem B1852571 : Blo 1851627 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B16041287 : Blo 1851627 16041287 := bstep (se 1 (by rfl) ⟨12030965, by rfl⟩ : syracuseStep 16041287 = 24061931) B24061931
theorem B3515815 : Blo 1851627 3515815 := bstep (se 1 (by rfl) ⟨2636861, by rfl⟩ : syracuseStep 3515815 = 5273723) B5273723
theorem B2778983 : Blo 1851627 2778983 := bstep (se 1 (by rfl) ⟨2084237, by rfl⟩ : syracuseStep 2778983 = 4168475) B4168475
theorem B2779007 : Blo 1851627 2779007 := bstep (se 1 (by rfl) ⟨2084255, by rfl⟩ : syracuseStep 2779007 = 4168511) B4168511
theorem B1853607 : Blo 1851627 1853607 := bstep (se 1 (by rfl) ⟨1390205, by rfl⟩ : syracuseStep 1853607 = 2780411) B2780411
theorem B23734781 : Blo 1851627 23734781 := bstep (se 3 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 23734781 = 8900543) B8900543
theorem B9374291 : Blo 1851627 9374291 := bstep (se 1 (by rfl) ⟨7030718, by rfl⟩ : syracuseStep 9374291 = 14061437) B14061437
theorem B6253523 : Blo 1851627 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B3754991 : Blo 1851627 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B2780153 : Blo 1851627 2780153 := bstep (se 2 (by rfl) ⟨1042557, by rfl⟩ : syracuseStep 2780153 = 2085115) B2085115
theorem B6253793 : Blo 1851627 6253793 := bstep (se 2 (by rfl) ⟨2345172, by rfl⟩ : syracuseStep 6253793 = 4690345) B4690345
theorem B234556657 : Blo 1851627 234556657 := bstep (se 2 (by rfl) ⟨87958746, by rfl⟩ : syracuseStep 234556657 = 175917493) B175917493
theorem B7507937 : Blo 1851627 7507937 := bstep (se 2 (by rfl) ⟨2815476, by rfl⟩ : syracuseStep 7507937 = 5630953) B5630953
theorem B47501639 : Blo 1851627 47501639 := bstep (se 1 (by rfl) ⟨35626229, by rfl⟩ : syracuseStep 47501639 = 71252459) B71252459
theorem B9376235 : Blo 1851627 9376235 := bstep (se 1 (by rfl) ⟨7032176, by rfl⟩ : syracuseStep 9376235 = 14064353) B14064353
theorem B4690811 : Blo 1851627 4690811 := bstep (se 1 (by rfl) ⟨3518108, by rfl⟩ : syracuseStep 4690811 = 7036217) B7036217
theorem B11425031 : Blo 1851627 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B4167071 : Blo 1851627 4167071 := bstep (se 1 (by rfl) ⟨3125303, by rfl⟩ : syracuseStep 4167071 = 6250607) B6250607
theorem B11868029 : Blo 1851627 11868029 := bstep (se 3 (by rfl) ⟨2225255, by rfl⟩ : syracuseStep 11868029 = 4450511) B4450511
theorem B4167593 : Blo 1851627 4167593 := bstep (se 2 (by rfl) ⟨1562847, by rfl⟩ : syracuseStep 4167593 = 3125695) B3125695
theorem B9378017 : Blo 1851627 9378017 := bstep (se 2 (by rfl) ⟨3516756, by rfl⟩ : syracuseStep 9378017 = 7033513) B7033513
theorem B8912509199 : Blo 1851627 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B28916473 : Blo 1851627 28916473 := bstep (se 2 (by rfl) ⟨10843677, by rfl⟩ : syracuseStep 28916473 = 21687355) B21687355
theorem B14072615 : Blo 1851627 14072615 := bstep (se 1 (by rfl) ⟨10554461, by rfl⟩ : syracuseStep 14072615 = 21108923) B21108923
theorem B4169051 : Blo 1851627 4169051 := bstep (se 1 (by rfl) ⟨3126788, by rfl⟩ : syracuseStep 4169051 = 6253577) B6253577
theorem B6250823 : Blo 1851627 6250823 := bstep (se 1 (by rfl) ⟨4688117, by rfl⟩ : syracuseStep 6250823 = 9376235) B9376235
theorem B2778047 : Blo 1851627 2778047 := bstep (se 1 (by rfl) ⟨2083535, by rfl⟩ : syracuseStep 2778047 = 4167071) B4167071
theorem B10552457 : Blo 1851627 10552457 := bstep (se 2 (by rfl) ⟨3957171, by rfl⟩ : syracuseStep 10552457 = 7914343) B7914343
theorem B1852655 : Blo 1851627 1852655 := bstep (se 1 (by rfl) ⟨1389491, by rfl⟩ : syracuseStep 1852655 = 2778983) B2778983
theorem B1852671 : Blo 1851627 1852671 := bstep (se 1 (by rfl) ⟨1389503, by rfl⟩ : syracuseStep 1852671 = 2779007) B2779007
theorem B2778395 : Blo 1851627 2778395 := bstep (se 1 (by rfl) ⟨2083796, by rfl⟩ : syracuseStep 2778395 = 4167593) B4167593
theorem B6252011 : Blo 1851627 6252011 := bstep (se 1 (by rfl) ⟨4689008, by rfl⟩ : syracuseStep 6252011 = 9378017) B9378017
theorem B22840841 : Blo 1851627 22840841 := bstep (se 2 (by rfl) ⟨8565315, by rfl⟩ : syracuseStep 22840841 = 17130631) B17130631
theorem B9381743 : Blo 1851627 9381743 := bstep (se 1 (by rfl) ⟨7036307, by rfl⟩ : syracuseStep 9381743 = 14072615) B14072615
theorem B4687753 : Blo 1851627 4687753 := bstep (se 2 (by rfl) ⟨1757907, by rfl⟩ : syracuseStep 4687753 = 3515815) B3515815
theorem B1853435 : Blo 1851627 1853435 := bstep (se 1 (by rfl) ⟨1390076, by rfl⟩ : syracuseStep 1853435 = 2780153) B2780153
theorem B2779367 : Blo 1851627 2779367 := bstep (se 1 (by rfl) ⟨2084525, by rfl⟩ : syracuseStep 2779367 = 4169051) B4169051
theorem B6253415 : Blo 1851627 6253415 := bstep (se 1 (by rfl) ⟨4690061, by rfl⟩ : syracuseStep 6253415 = 9380123) B9380123
theorem B11873465 : Blo 1851627 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B10694191 : Blo 1851627 10694191 := bstep (se 1 (by rfl) ⟨8020643, by rfl⟩ : syracuseStep 10694191 = 16041287) B16041287
theorem B38555297 : Blo 1851627 38555297 := bstep (se 2 (by rfl) ⟨14458236, by rfl⟩ : syracuseStep 38555297 = 28916473) B28916473
theorem B15823187 : Blo 1851627 15823187 := bstep (se 1 (by rfl) ⟨11867390, by rfl⟩ : syracuseStep 15823187 = 23734781) B23734781
theorem B2503327 : Blo 1851627 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B5003875349 : Blo 1851627 5003875349 := bstep (se 6 (by rfl) ⟨117278328, by rfl⟩ : syracuseStep 5003875349 = 234556657) B234556657
theorem B31667759 : Blo 1851627 31667759 := bstep (se 1 (by rfl) ⟨23750819, by rfl⟩ : syracuseStep 31667759 = 47501639) B47501639
theorem B7034471 : Blo 1851627 7034471 := bstep (se 1 (by rfl) ⟨5275853, by rfl⟩ : syracuseStep 7034471 = 10551707) B10551707
theorem B3127207 : Blo 1851627 3127207 := bstep (se 1 (by rfl) ⟨2345405, by rfl⟩ : syracuseStep 3127207 = 4690811) B4690811
theorem B7616687 : Blo 1851627 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B7912019 : Blo 1851627 7912019 := bstep (se 1 (by rfl) ⟨5934014, by rfl⟩ : syracuseStep 7912019 = 11868029) B11868029
theorem B5941672799 : Blo 1851627 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B6249527 : Blo 1851627 6249527 := bstep (se 1 (by rfl) ⟨4687145, by rfl⟩ : syracuseStep 6249527 = 9374291) B9374291
theorem B4169015 : Blo 1851627 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B4169195 : Blo 1851627 4169195 := bstep (se 1 (by rfl) ⟨3126896, by rfl⟩ : syracuseStep 4169195 = 6253793) B6253793
theorem B20021165 : Blo 1851627 20021165 := bstep (se 3 (by rfl) ⟨3753968, by rfl⟩ : syracuseStep 20021165 = 7507937) B7507937
theorem B1852031 : Blo 1851627 1852031 := bstep (se 1 (by rfl) ⟨1389023, by rfl⟩ : syracuseStep 1852031 = 2778047) B2778047
theorem B1852263 : Blo 1851627 1852263 := bstep (se 1 (by rfl) ⟨1389197, by rfl⟩ : syracuseStep 1852263 = 2778395) B2778395
theorem B21111839 : Blo 1851627 21111839 := bstep (se 1 (by rfl) ⟨15833879, by rfl⟩ : syracuseStep 21111839 = 31667759) B31667759
theorem B1852911 : Blo 1851627 1852911 := bstep (se 1 (by rfl) ⟨1389683, by rfl⟩ : syracuseStep 1852911 = 2779367) B2779367
theorem B7915643 : Blo 1851627 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B2779343 : Blo 1851627 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B15844460797 : Blo 1851627 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B2779463 : Blo 1851627 2779463 := bstep (se 1 (by rfl) ⟨2084597, by rfl⟩ : syracuseStep 2779463 = 4169195) B4169195
theorem B13347443 : Blo 1851627 13347443 := bstep (se 1 (by rfl) ⟨10010582, by rfl⟩ : syracuseStep 13347443 = 20021165) B20021165
theorem B20311165 : Blo 1851627 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B3335916899 : Blo 1851627 3335916899 := bstep (se 1 (by rfl) ⟨2501937674, by rfl⟩ : syracuseStep 3335916899 = 5003875349) B5003875349
theorem B3337769 : Blo 1851627 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B4689647 : Blo 1851627 4689647 := bstep (se 1 (by rfl) ⟨3517235, by rfl⟩ : syracuseStep 4689647 = 7034471) B7034471
theorem B6254495 : Blo 1851627 6254495 := bstep (se 1 (by rfl) ⟨4690871, by rfl⟩ : syracuseStep 6254495 = 9381743) B9381743
theorem B21098717 : Blo 1851627 21098717 := bstep (se 3 (by rfl) ⟨3956009, by rfl⟩ : syracuseStep 21098717 = 7912019) B7912019
theorem B4166351 : Blo 1851627 4166351 := bstep (se 1 (by rfl) ⟨3124763, by rfl⟩ : syracuseStep 4166351 = 6249527) B6249527
theorem B14258921 : Blo 1851627 14258921 := bstep (se 2 (by rfl) ⟨5347095, by rfl⟩ : syracuseStep 14258921 = 10694191) B10694191
theorem B25703531 : Blo 1851627 25703531 := bstep (se 1 (by rfl) ⟨19277648, by rfl⟩ : syracuseStep 25703531 = 38555297) B38555297
theorem B4167215 : Blo 1851627 4167215 := bstep (se 1 (by rfl) ⟨3125411, by rfl⟩ : syracuseStep 4167215 = 6250823) B6250823
theorem B10548791 : Blo 1851627 10548791 := bstep (se 1 (by rfl) ⟨7911593, by rfl⟩ : syracuseStep 10548791 = 15823187) B15823187
theorem B7034971 : Blo 1851627 7034971 := bstep (se 1 (by rfl) ⟨5276228, by rfl⟩ : syracuseStep 7034971 = 10552457) B10552457
theorem B4168007 : Blo 1851627 4168007 := bstep (se 1 (by rfl) ⟨3126005, by rfl⟩ : syracuseStep 4168007 = 6252011) B6252011
theorem B15227227 : Blo 1851627 15227227 := bstep (se 1 (by rfl) ⟨11420420, by rfl⟩ : syracuseStep 15227227 = 22840841) B22840841
theorem B4168943 : Blo 1851627 4168943 := bstep (se 1 (by rfl) ⟨3126707, by rfl⟩ : syracuseStep 4168943 = 6253415) B6253415
theorem B6250337 : Blo 1851627 6250337 := bstep (se 2 (by rfl) ⟨2343876, by rfl⟩ : syracuseStep 6250337 = 4687753) B4687753
theorem B4169609 : Blo 1851627 4169609 := bstep (se 2 (by rfl) ⟨1563603, by rfl⟩ : syracuseStep 4169609 = 3127207) B3127207
theorem B9379961 : Blo 1851627 9379961 := bstep (se 2 (by rfl) ⟨3517485, by rfl⟩ : syracuseStep 9379961 = 7034971) B7034971
theorem B14065811 : Blo 1851627 14065811 := bstep (se 1 (by rfl) ⟨10549358, by rfl⟩ : syracuseStep 14065811 = 21098717) B21098717
theorem B21125947729 : Blo 1851627 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B2777567 : Blo 1851627 2777567 := bstep (se 1 (by rfl) ⟨2083175, by rfl⟩ : syracuseStep 2777567 = 4166351) B4166351
theorem B14074559 : Blo 1851627 14074559 := bstep (se 1 (by rfl) ⟨10555919, by rfl⟩ : syracuseStep 14074559 = 21111839) B21111839
theorem B2778143 : Blo 1851627 2778143 := bstep (se 1 (by rfl) ⟨2083607, by rfl⟩ : syracuseStep 2778143 = 4167215) B4167215
theorem B5277095 : Blo 1851627 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B1852895 : Blo 1851627 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B2778671 : Blo 1851627 2778671 := bstep (se 1 (by rfl) ⟨2084003, by rfl⟩ : syracuseStep 2778671 = 4168007) B4168007
theorem B1852975 : Blo 1851627 1852975 := bstep (se 1 (by rfl) ⟨1389731, by rfl⟩ : syracuseStep 1852975 = 2779463) B2779463
theorem B8898295 : Blo 1851627 8898295 := bstep (se 1 (by rfl) ⟨6673721, by rfl⟩ : syracuseStep 8898295 = 13347443) B13347443
theorem B2779295 : Blo 1851627 2779295 := bstep (se 1 (by rfl) ⟨2084471, by rfl⟩ : syracuseStep 2779295 = 4168943) B4168943
theorem B152095157 : Blo 1851627 152095157 := bstep (se 5 (by rfl) ⟨7129460, by rfl⟩ : syracuseStep 152095157 = 14258921) B14258921
theorem B2779739 : Blo 1851627 2779739 := bstep (se 1 (by rfl) ⟨2084804, by rfl⟩ : syracuseStep 2779739 = 4169609) B4169609
theorem B20302969 : Blo 1851627 20302969 := bstep (se 2 (by rfl) ⟨7613613, by rfl⟩ : syracuseStep 20302969 = 15227227) B15227227
theorem B7032527 : Blo 1851627 7032527 := bstep (se 1 (by rfl) ⟨5274395, by rfl⟩ : syracuseStep 7032527 = 10548791) B10548791
theorem B2223944599 : Blo 1851627 2223944599 := bstep (se 1 (by rfl) ⟨1667958449, by rfl⟩ : syracuseStep 2223944599 = 3335916899) B3335916899
theorem B2225179 : Blo 1851627 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B3126431 : Blo 1851627 3126431 := bstep (se 1 (by rfl) ⟨2344823, by rfl⟩ : syracuseStep 3126431 = 4689647) B4689647
theorem B4166891 : Blo 1851627 4166891 := bstep (se 1 (by rfl) ⟨3125168, by rfl⟩ : syracuseStep 4166891 = 6250337) B6250337
theorem B17135687 : Blo 1851627 17135687 := bstep (se 1 (by rfl) ⟨12851765, by rfl⟩ : syracuseStep 17135687 = 25703531) B25703531
theorem B27081553 : Blo 1851627 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B4169663 : Blo 1851627 4169663 := bstep (se 1 (by rfl) ⟨3127247, by rfl⟩ : syracuseStep 4169663 = 6254495) B6254495
theorem B1851711 : Blo 1851627 1851711 := bstep (se 1 (by rfl) ⟨1388783, by rfl⟩ : syracuseStep 1851711 = 2777567) B2777567
theorem B28167930305 : Blo 1851627 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B1852095 : Blo 1851627 1852095 := bstep (se 1 (by rfl) ⟨1389071, by rfl⟩ : syracuseStep 1852095 = 2778143) B2778143
theorem B2777927 : Blo 1851627 2777927 := bstep (se 1 (by rfl) ⟨2083445, by rfl⟩ : syracuseStep 2777927 = 4166891) B4166891
theorem B1852447 : Blo 1851627 1852447 := bstep (se 1 (by rfl) ⟨1389335, by rfl⟩ : syracuseStep 1852447 = 2778671) B2778671
theorem B2965259465 : Blo 1851627 2965259465 := bstep (se 2 (by rfl) ⟨1111972299, by rfl⟩ : syracuseStep 2965259465 = 2223944599) B2223944599
theorem B2966905 : Blo 1851627 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B1852863 : Blo 1851627 1852863 := bstep (se 1 (by rfl) ⟨1389647, by rfl⟩ : syracuseStep 1852863 = 2779295) B2779295
theorem B1853159 : Blo 1851627 1853159 := bstep (se 1 (by rfl) ⟨1389869, by rfl⟩ : syracuseStep 1853159 = 2779739) B2779739
theorem B11864393 : Blo 1851627 11864393 := bstep (se 2 (by rfl) ⟨4449147, by rfl⟩ : syracuseStep 11864393 = 8898295) B8898295
theorem B4688351 : Blo 1851627 4688351 := bstep (se 1 (by rfl) ⟨3516263, by rfl⟩ : syracuseStep 4688351 = 7032527) B7032527
theorem B2779775 : Blo 1851627 2779775 := bstep (se 1 (by rfl) ⟨2084831, by rfl⟩ : syracuseStep 2779775 = 4169663) B4169663
theorem B6253307 : Blo 1851627 6253307 := bstep (se 1 (by rfl) ⟨4689980, by rfl⟩ : syracuseStep 6253307 = 9379961) B9379961
theorem B9383039 : Blo 1851627 9383039 := bstep (se 1 (by rfl) ⟨7037279, by rfl⟩ : syracuseStep 9383039 = 14074559) B14074559
theorem B2084287 : Blo 1851627 2084287 := bstep (se 1 (by rfl) ⟨1563215, by rfl⟩ : syracuseStep 2084287 = 3126431) B3126431
theorem B3518063 : Blo 1851627 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B11423791 : Blo 1851627 11423791 := bstep (se 1 (by rfl) ⟨8567843, by rfl⟩ : syracuseStep 11423791 = 17135687) B17135687
theorem B27070625 : Blo 1851627 27070625 := bstep (se 2 (by rfl) ⟨10151484, by rfl⟩ : syracuseStep 27070625 = 20302969) B20302969
theorem B101396771 : Blo 1851627 101396771 := bstep (se 1 (by rfl) ⟨76047578, by rfl⟩ : syracuseStep 101396771 = 152095157) B152095157
theorem B9377207 : Blo 1851627 9377207 := bstep (se 1 (by rfl) ⟨7032905, by rfl⟩ : syracuseStep 9377207 = 14065811) B14065811
theorem B36108737 : Blo 1851627 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B18047083 : Blo 1851627 18047083 := bstep (se 1 (by rfl) ⟨13535312, by rfl⟩ : syracuseStep 18047083 = 27070625) B27070625
theorem B18778620203 : Blo 1851627 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B1851951 : Blo 1851627 1851951 := bstep (se 1 (by rfl) ⟨1388963, by rfl⟩ : syracuseStep 1851951 = 2777927) B2777927
theorem B6251471 : Blo 1851627 6251471 := bstep (se 1 (by rfl) ⟨4688603, by rfl⟩ : syracuseStep 6251471 = 9377207) B9377207
theorem B1853183 : Blo 1851627 1853183 := bstep (se 1 (by rfl) ⟨1389887, by rfl⟩ : syracuseStep 1853183 = 2779775) B2779775
theorem B2779049 : Blo 1851627 2779049 := bstep (se 2 (by rfl) ⟨1042143, by rfl⟩ : syracuseStep 2779049 = 2084287) B2084287
theorem B2345375 : Blo 1851627 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B15231721 : Blo 1851627 15231721 := bstep (se 2 (by rfl) ⟨5711895, by rfl⟩ : syracuseStep 15231721 = 11423791) B11423791
theorem B1976839643 : Blo 1851627 1976839643 := bstep (se 1 (by rfl) ⟨1482629732, by rfl⟩ : syracuseStep 1976839643 = 2965259465) B2965259465
theorem B7909595 : Blo 1851627 7909595 := bstep (se 1 (by rfl) ⟨5932196, by rfl⟩ : syracuseStep 7909595 = 11864393) B11864393
theorem B24072491 : Blo 1851627 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B3125567 : Blo 1851627 3125567 := bstep (se 1 (by rfl) ⟨2344175, by rfl⟩ : syracuseStep 3125567 = 4688351) B4688351
theorem B6255359 : Blo 1851627 6255359 := bstep (se 1 (by rfl) ⟨4691519, by rfl⟩ : syracuseStep 6255359 = 9383039) B9383039
theorem B67597847 : Blo 1851627 67597847 := bstep (se 1 (by rfl) ⟨50698385, by rfl⟩ : syracuseStep 67597847 = 101396771) B101396771
theorem B3955873 : Blo 1851627 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B4168871 : Blo 1851627 4168871 := bstep (se 1 (by rfl) ⟨3126653, by rfl⟩ : syracuseStep 4168871 = 6253307) B6253307
theorem B12519080135 : Blo 1851627 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B16048327 : Blo 1851627 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B4170239 : Blo 1851627 4170239 := bstep (se 1 (by rfl) ⟨3127679, by rfl⟩ : syracuseStep 4170239 = 6255359) B6255359
theorem B20308961 : Blo 1851627 20308961 := bstep (se 2 (by rfl) ⟨7615860, by rfl⟩ : syracuseStep 20308961 = 15231721) B15231721
theorem B45065231 : Blo 1851627 45065231 := bstep (se 1 (by rfl) ⟨33798923, by rfl⟩ : syracuseStep 45065231 = 67597847) B67597847
theorem B1852699 : Blo 1851627 1852699 := bstep (se 1 (by rfl) ⟨1389524, by rfl⟩ : syracuseStep 1852699 = 2779049) B2779049
theorem B2779247 : Blo 1851627 2779247 := bstep (se 1 (by rfl) ⟨2084435, by rfl⟩ : syracuseStep 2779247 = 4168871) B4168871
theorem B24062777 : Blo 1851627 24062777 := bstep (se 2 (by rfl) ⟨9023541, by rfl⟩ : syracuseStep 24062777 = 18047083) B18047083
theorem B2083711 : Blo 1851627 2083711 := bstep (se 1 (by rfl) ⟨1562783, by rfl⟩ : syracuseStep 2083711 = 3125567) B3125567
theorem B6254333 : Blo 1851627 6254333 := bstep (se 3 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 6254333 = 2345375) B2345375
theorem B1317893095 : Blo 1851627 1317893095 := bstep (se 1 (by rfl) ⟨988419821, by rfl⟩ : syracuseStep 1317893095 = 1976839643) B1976839643
theorem B5273063 : Blo 1851627 5273063 := bstep (se 1 (by rfl) ⟨3954797, by rfl⟩ : syracuseStep 5273063 = 7909595) B7909595
theorem B4167647 : Blo 1851627 4167647 := bstep (se 1 (by rfl) ⟨3125735, by rfl⟩ : syracuseStep 4167647 = 6251471) B6251471
theorem B5274497 : Blo 1851627 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B21397769 : Blo 1851627 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B3515375 : Blo 1851627 3515375 := bstep (se 1 (by rfl) ⟨2636531, by rfl⟩ : syracuseStep 3515375 = 5273063) B5273063
theorem B2778281 : Blo 1851627 2778281 := bstep (se 2 (by rfl) ⟨1041855, by rfl⟩ : syracuseStep 2778281 = 2083711) B2083711
theorem B2778431 : Blo 1851627 2778431 := bstep (se 1 (by rfl) ⟨2083823, by rfl⟩ : syracuseStep 2778431 = 4167647) B4167647
theorem B1852831 : Blo 1851627 1852831 := bstep (se 1 (by rfl) ⟨1389623, by rfl⟩ : syracuseStep 1852831 = 2779247) B2779247
theorem B16041851 : Blo 1851627 16041851 := bstep (se 1 (by rfl) ⟨12031388, by rfl⟩ : syracuseStep 16041851 = 24062777) B24062777
theorem B8346053423 : Blo 1851627 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B2780159 : Blo 1851627 2780159 := bstep (se 1 (by rfl) ⟨2085119, by rfl⟩ : syracuseStep 2780159 = 4170239) B4170239
theorem B30043487 : Blo 1851627 30043487 := bstep (se 1 (by rfl) ⟨22532615, by rfl⟩ : syracuseStep 30043487 = 45065231) B45065231
theorem B13539307 : Blo 1851627 13539307 := bstep (se 1 (by rfl) ⟨10154480, by rfl⟩ : syracuseStep 13539307 = 20308961) B20308961
theorem B1757190793 : Blo 1851627 1757190793 := bstep (se 2 (by rfl) ⟨658946547, by rfl⟩ : syracuseStep 1757190793 = 1317893095) B1317893095
theorem B14065325 : Blo 1851627 14065325 := bstep (se 3 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 14065325 = 5274497) B5274497
theorem B4169555 : Blo 1851627 4169555 := bstep (se 1 (by rfl) ⟨3127166, by rfl⟩ : syracuseStep 4169555 = 6254333) B6254333
theorem B2342921057 : Blo 1851627 2342921057 := bstep (se 2 (by rfl) ⟨878595396, by rfl⟩ : syracuseStep 2342921057 = 1757190793) B1757190793
theorem B2343583 : Blo 1851627 2343583 := bstep (se 1 (by rfl) ⟨1757687, by rfl⟩ : syracuseStep 2343583 = 3515375) B3515375
theorem B1852187 : Blo 1851627 1852187 := bstep (se 1 (by rfl) ⟨1389140, by rfl⟩ : syracuseStep 1852187 = 2778281) B2778281
theorem B1852287 : Blo 1851627 1852287 := bstep (se 1 (by rfl) ⟨1389215, by rfl⟩ : syracuseStep 1852287 = 2778431) B2778431
theorem B1853439 : Blo 1851627 1853439 := bstep (se 1 (by rfl) ⟨1390079, by rfl⟩ : syracuseStep 1853439 = 2780159) B2780159
theorem B22256142461 : Blo 1851627 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B2779703 : Blo 1851627 2779703 := bstep (se 1 (by rfl) ⟨2084777, by rfl⟩ : syracuseStep 2779703 = 4169555) B4169555
theorem B14265179 : Blo 1851627 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B10694567 : Blo 1851627 10694567 := bstep (se 1 (by rfl) ⟨8020925, by rfl⟩ : syracuseStep 10694567 = 16041851) B16041851
theorem B9376883 : Blo 1851627 9376883 := bstep (se 1 (by rfl) ⟨7032662, by rfl⟩ : syracuseStep 9376883 = 14065325) B14065325
theorem B18052409 : Blo 1851627 18052409 := bstep (se 2 (by rfl) ⟨6769653, by rfl⟩ : syracuseStep 18052409 = 13539307) B13539307
theorem B20028991 : Blo 1851627 20028991 := bstep (se 1 (by rfl) ⟨15021743, by rfl⟩ : syracuseStep 20028991 = 30043487) B30043487
theorem B6251255 : Blo 1851627 6251255 := bstep (se 1 (by rfl) ⟨4688441, by rfl⟩ : syracuseStep 6251255 = 9376883) B9376883
theorem B12034939 : Blo 1851627 12034939 := bstep (se 1 (by rfl) ⟨9026204, by rfl⟩ : syracuseStep 12034939 = 18052409) B18052409
theorem B1853135 : Blo 1851627 1853135 := bstep (se 1 (by rfl) ⟨1389851, by rfl⟩ : syracuseStep 1853135 = 2779703) B2779703
theorem B7129711 : Blo 1851627 7129711 := bstep (se 1 (by rfl) ⟨5347283, by rfl⟩ : syracuseStep 7129711 = 10694567) B10694567
theorem B1561947371 : Blo 1851627 1561947371 := bstep (se 1 (by rfl) ⟨1171460528, by rfl⟩ : syracuseStep 1561947371 = 2342921057) B2342921057
theorem B3124777 : Blo 1851627 3124777 := bstep (se 2 (by rfl) ⟨1171791, by rfl⟩ : syracuseStep 3124777 = 2343583) B2343583
theorem B14837428307 : Blo 1851627 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B9510119 : Blo 1851627 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B26705321 : Blo 1851627 26705321 := bstep (se 2 (by rfl) ⟨10014495, by rfl⟩ : syracuseStep 26705321 = 20028991) B20028991
theorem B9891618871 : Blo 1851627 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B17803547 : Blo 1851627 17803547 := bstep (se 1 (by rfl) ⟨13352660, by rfl⟩ : syracuseStep 17803547 = 26705321) B26705321
theorem B9506281 : Blo 1851627 9506281 := bstep (se 2 (by rfl) ⟨3564855, by rfl⟩ : syracuseStep 9506281 = 7129711) B7129711
theorem B4166369 : Blo 1851627 4166369 := bstep (se 2 (by rfl) ⟨1562388, by rfl⟩ : syracuseStep 4166369 = 3124777) B3124777
theorem B1041298247 : Blo 1851627 1041298247 := bstep (se 1 (by rfl) ⟨780973685, by rfl⟩ : syracuseStep 1041298247 = 1561947371) B1561947371
theorem B4167503 : Blo 1851627 4167503 := bstep (se 1 (by rfl) ⟨3125627, by rfl⟩ : syracuseStep 4167503 = 6251255) B6251255
theorem B16046585 : Blo 1851627 16046585 := bstep (se 2 (by rfl) ⟨6017469, by rfl⟩ : syracuseStep 16046585 = 12034939) B12034939
theorem B6340079 : Blo 1851627 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B13188825161 : Blo 1851627 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B2777579 : Blo 1851627 2777579 := bstep (se 1 (by rfl) ⟨2083184, by rfl⟩ : syracuseStep 2777579 = 4166369) B4166369
theorem B694198831 : Blo 1851627 694198831 := bstep (se 1 (by rfl) ⟨520649123, by rfl⟩ : syracuseStep 694198831 = 1041298247) B1041298247
theorem B2778335 : Blo 1851627 2778335 := bstep (se 1 (by rfl) ⟨2083751, by rfl⟩ : syracuseStep 2778335 = 4167503) B4167503
theorem B12675041 : Blo 1851627 12675041 := bstep (se 2 (by rfl) ⟨4753140, by rfl⟩ : syracuseStep 12675041 = 9506281) B9506281
theorem B16906877 : Blo 1851627 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B11869031 : Blo 1851627 11869031 := bstep (se 1 (by rfl) ⟨8901773, by rfl⟩ : syracuseStep 11869031 = 17803547) B17803547
theorem B10697723 : Blo 1851627 10697723 := bstep (se 1 (by rfl) ⟨8023292, by rfl⟩ : syracuseStep 10697723 = 16046585) B16046585
theorem B1851719 : Blo 1851627 1851719 := bstep (se 1 (by rfl) ⟨1388789, by rfl⟩ : syracuseStep 1851719 = 2777579) B2777579
theorem B925598441 : Blo 1851627 925598441 := bstep (se 2 (by rfl) ⟨347099415, by rfl⟩ : syracuseStep 925598441 = 694198831) B694198831
theorem B1852223 : Blo 1851627 1852223 := bstep (se 1 (by rfl) ⟨1389167, by rfl⟩ : syracuseStep 1852223 = 2778335) B2778335
theorem B8792550107 : Blo 1851627 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B8450027 : Blo 1851627 8450027 := bstep (se 1 (by rfl) ⟨6337520, by rfl⟩ : syracuseStep 8450027 = 12675041) B12675041
theorem B7131815 : Blo 1851627 7131815 := bstep (se 1 (by rfl) ⟨5348861, by rfl⟩ : syracuseStep 7131815 = 10697723) B10697723
theorem B11271251 : Blo 1851627 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B7912687 : Blo 1851627 7912687 := bstep (se 1 (by rfl) ⟨5934515, by rfl⟩ : syracuseStep 7912687 = 11869031) B11869031
theorem B7514167 : Blo 1851627 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B4754543 : Blo 1851627 4754543 := bstep (se 1 (by rfl) ⟨3565907, by rfl⟩ : syracuseStep 4754543 = 7131815) B7131815
theorem B617065627 : Blo 1851627 617065627 := bstep (se 1 (by rfl) ⟨462799220, by rfl⟩ : syracuseStep 617065627 = 925598441) B925598441
theorem B5861700071 : Blo 1851627 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B5633351 : Blo 1851627 5633351 := bstep (se 1 (by rfl) ⟨4225013, by rfl⟩ : syracuseStep 5633351 = 8450027) B8450027
theorem B10550249 : Blo 1851627 10550249 := bstep (se 2 (by rfl) ⟨3956343, by rfl⟩ : syracuseStep 10550249 = 7912687) B7912687
theorem B10018889 : Blo 1851627 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B3907800047 : Blo 1851627 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B3755567 : Blo 1851627 3755567 := bstep (se 1 (by rfl) ⟨2816675, by rfl⟩ : syracuseStep 3755567 = 5633351) B5633351
theorem B7033499 : Blo 1851627 7033499 := bstep (se 1 (by rfl) ⟨5275124, by rfl⟩ : syracuseStep 7033499 = 10550249) B10550249
theorem B12678781 : Blo 1851627 12678781 := bstep (se 3 (by rfl) ⟨2377271, by rfl⟩ : syracuseStep 12678781 = 4754543) B4754543
theorem B822754169 : Blo 1851627 822754169 := bstep (se 2 (by rfl) ⟨308532813, by rfl⟩ : syracuseStep 822754169 = 617065627) B617065627
theorem B6679259 : Blo 1851627 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B4688999 : Blo 1851627 4688999 := bstep (se 1 (by rfl) ⟨3516749, by rfl⟩ : syracuseStep 4688999 = 7033499) B7033499
theorem B2605200031 : Blo 1851627 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B16905041 : Blo 1851627 16905041 := bstep (se 2 (by rfl) ⟨6339390, by rfl⟩ : syracuseStep 16905041 = 12678781) B12678781
theorem B2503711 : Blo 1851627 2503711 := bstep (se 1 (by rfl) ⟨1877783, by rfl⟩ : syracuseStep 2503711 = 3755567) B3755567
theorem B548502779 : Blo 1851627 548502779 := bstep (se 1 (by rfl) ⟨411377084, by rfl⟩ : syracuseStep 548502779 = 822754169) B822754169
theorem B365668519 : Blo 1851627 365668519 := bstep (se 1 (by rfl) ⟨274251389, by rfl⟩ : syracuseStep 365668519 = 548502779) B548502779
theorem B3473600041 : Blo 1851627 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B3338281 : Blo 1851627 3338281 := bstep (se 2 (by rfl) ⟨1251855, by rfl⟩ : syracuseStep 3338281 = 2503711) B2503711
theorem B4452839 : Blo 1851627 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B3125999 : Blo 1851627 3125999 := bstep (se 1 (by rfl) ⟨2344499, by rfl⟩ : syracuseStep 3125999 = 4688999) B4688999
theorem B11270027 : Blo 1851627 11270027 := bstep (se 1 (by rfl) ⟨8452520, by rfl⟩ : syracuseStep 11270027 = 16905041) B16905041
theorem B4451041 : Blo 1851627 4451041 := bstep (se 2 (by rfl) ⟨1669140, by rfl⟩ : syracuseStep 4451041 = 3338281) B3338281
theorem B487558025 : Blo 1851627 487558025 := bstep (se 2 (by rfl) ⟨182834259, by rfl⟩ : syracuseStep 487558025 = 365668519) B365668519
theorem B2968559 : Blo 1851627 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B2083999 : Blo 1851627 2083999 := bstep (se 1 (by rfl) ⟨1562999, by rfl⟩ : syracuseStep 2083999 = 3125999) B3125999
theorem B4631466721 : Blo 1851627 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B30053405 : Blo 1851627 30053405 := bstep (se 3 (by rfl) ⟨5635013, by rfl⟩ : syracuseStep 30053405 = 11270027) B11270027
theorem B2778665 : Blo 1851627 2778665 := bstep (se 2 (by rfl) ⟨1041999, by rfl⟩ : syracuseStep 2778665 = 2083999) B2083999
theorem B5934721 : Blo 1851627 5934721 := bstep (se 2 (by rfl) ⟨2225520, by rfl⟩ : syracuseStep 5934721 = 4451041) B4451041
theorem B6175288961 : Blo 1851627 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B325038683 : Blo 1851627 325038683 := bstep (se 1 (by rfl) ⟨243779012, by rfl⟩ : syracuseStep 325038683 = 487558025) B487558025
theorem B1979039 : Blo 1851627 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B20035603 : Blo 1851627 20035603 := bstep (se 1 (by rfl) ⟨15026702, by rfl⟩ : syracuseStep 20035603 = 30053405) B30053405
theorem B26714137 : Blo 1851627 26714137 := bstep (se 2 (by rfl) ⟨10017801, by rfl⟩ : syracuseStep 26714137 = 20035603) B20035603
theorem B1852443 : Blo 1851627 1852443 := bstep (se 1 (by rfl) ⟨1389332, by rfl⟩ : syracuseStep 1852443 = 2778665) B2778665
theorem B5277437 : Blo 1851627 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B4116859307 : Blo 1851627 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B216692455 : Blo 1851627 216692455 := bstep (se 1 (by rfl) ⟨162519341, by rfl⟩ : syracuseStep 216692455 = 325038683) B325038683
theorem B7912961 : Blo 1851627 7912961 := bstep (se 2 (by rfl) ⟨2967360, by rfl⟩ : syracuseStep 7912961 = 5934721) B5934721
theorem B35618849 : Blo 1851627 35618849 := bstep (se 2 (by rfl) ⟨13357068, by rfl⟩ : syracuseStep 35618849 = 26714137) B26714137
theorem B3518291 : Blo 1851627 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B2744572871 : Blo 1851627 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B288923273 : Blo 1851627 288923273 := bstep (se 2 (by rfl) ⟨108346227, by rfl⟩ : syracuseStep 288923273 = 216692455) B216692455
theorem B5275307 : Blo 1851627 5275307 := bstep (se 1 (by rfl) ⟨3956480, by rfl⟩ : syracuseStep 5275307 = 7912961) B7912961
theorem B3516871 : Blo 1851627 3516871 := bstep (se 1 (by rfl) ⟨2637653, by rfl⟩ : syracuseStep 3516871 = 5275307) B5275307
theorem B2345527 : Blo 1851627 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B192615515 : Blo 1851627 192615515 := bstep (se 1 (by rfl) ⟨144461636, by rfl⟩ : syracuseStep 192615515 = 288923273) B288923273
theorem B23745899 : Blo 1851627 23745899 := bstep (se 1 (by rfl) ⟨17809424, by rfl⟩ : syracuseStep 23745899 = 35618849) B35618849
theorem B1829715247 : Blo 1851627 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B128410343 : Blo 1851627 128410343 := bstep (se 1 (by rfl) ⟨96307757, by rfl⟩ : syracuseStep 128410343 = 192615515) B192615515
theorem B2439620329 : Blo 1851627 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B4689161 : Blo 1851627 4689161 := bstep (se 2 (by rfl) ⟨1758435, by rfl⟩ : syracuseStep 4689161 = 3516871) B3516871
theorem B15830599 : Blo 1851627 15830599 := bstep (se 1 (by rfl) ⟨11872949, by rfl⟩ : syracuseStep 15830599 = 23745899) B23745899
theorem B3127369 : Blo 1851627 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B4169825 : Blo 1851627 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B85606895 : Blo 1851627 85606895 := bstep (se 1 (by rfl) ⟨64205171, by rfl⟩ : syracuseStep 85606895 = 128410343) B128410343
theorem B21107465 : Blo 1851627 21107465 := bstep (se 2 (by rfl) ⟨7915299, by rfl⟩ : syracuseStep 21107465 = 15830599) B15830599
theorem B3126107 : Blo 1851627 3126107 := bstep (se 1 (by rfl) ⟨2344580, by rfl⟩ : syracuseStep 3126107 = 4689161) B4689161
theorem B3252827105 : Blo 1851627 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B2779883 : Blo 1851627 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B2084071 : Blo 1851627 2084071 := bstep (se 1 (by rfl) ⟨1563053, by rfl⟩ : syracuseStep 2084071 = 3126107) B3126107
theorem B14071643 : Blo 1851627 14071643 := bstep (se 1 (by rfl) ⟨10553732, by rfl⟩ : syracuseStep 14071643 = 21107465) B21107465
theorem B2168551403 : Blo 1851627 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B228285053 : Blo 1851627 228285053 := bstep (se 3 (by rfl) ⟨42803447, by rfl⟩ : syracuseStep 228285053 = 85606895) B85606895
theorem B9381095 : Blo 1851627 9381095 := bstep (se 1 (by rfl) ⟨7035821, by rfl⟩ : syracuseStep 9381095 = 14071643) B14071643
theorem B1445700935 : Blo 1851627 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B2778761 : Blo 1851627 2778761 := bstep (se 2 (by rfl) ⟨1042035, by rfl⟩ : syracuseStep 2778761 = 2084071) B2084071
theorem B1853255 : Blo 1851627 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B152190035 : Blo 1851627 152190035 := bstep (se 1 (by rfl) ⟨114142526, by rfl⟩ : syracuseStep 152190035 = 228285053) B228285053
theorem B1852507 : Blo 1851627 1852507 := bstep (se 1 (by rfl) ⟨1389380, by rfl⟩ : syracuseStep 1852507 = 2778761) B2778761
theorem B101460023 : Blo 1851627 101460023 := bstep (se 1 (by rfl) ⟨76095017, by rfl⟩ : syracuseStep 101460023 = 152190035) B152190035
theorem B6254063 : Blo 1851627 6254063 := bstep (se 1 (by rfl) ⟨4690547, by rfl⟩ : syracuseStep 6254063 = 9381095) B9381095
theorem B963800623 : Blo 1851627 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B5140269989 : Blo 1851627 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B67640015 : Blo 1851627 67640015 := bstep (se 1 (by rfl) ⟨50730011, by rfl⟩ : syracuseStep 67640015 = 101460023) B101460023
theorem B4169375 : Blo 1851627 4169375 := bstep (se 1 (by rfl) ⟨3127031, by rfl⟩ : syracuseStep 4169375 = 6254063) B6254063
theorem B3426846659 : Blo 1851627 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B2779583 : Blo 1851627 2779583 := bstep (se 1 (by rfl) ⟨2084687, by rfl⟩ : syracuseStep 2779583 = 4169375) B4169375
theorem B45093343 : Blo 1851627 45093343 := bstep (se 1 (by rfl) ⟨33820007, by rfl⟩ : syracuseStep 45093343 = 67640015) B67640015
theorem B1853055 : Blo 1851627 1853055 := bstep (se 1 (by rfl) ⟨1389791, by rfl⟩ : syracuseStep 1853055 = 2779583) B2779583
theorem B60124457 : Blo 1851627 60124457 := bstep (se 2 (by rfl) ⟨22546671, by rfl⟩ : syracuseStep 60124457 = 45093343) B45093343
theorem B2284564439 : Blo 1851627 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B1523042959 : Blo 1851627 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B40082971 : Blo 1851627 40082971 := bstep (se 1 (by rfl) ⟨30062228, by rfl⟩ : syracuseStep 40082971 = 60124457) B60124457
theorem B2030723945 : Blo 1851627 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B53443961 : Blo 1851627 53443961 := bstep (se 2 (by rfl) ⟨20041485, by rfl⟩ : syracuseStep 53443961 = 40082971) B40082971
theorem B35629307 : Blo 1851627 35629307 := bstep (se 1 (by rfl) ⟨26721980, by rfl⟩ : syracuseStep 35629307 = 53443961) B53443961
theorem B1353815963 : Blo 1851627 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B23752871 : Blo 1851627 23752871 := bstep (se 1 (by rfl) ⟨17814653, by rfl⟩ : syracuseStep 23752871 = 35629307) B35629307
theorem B902543975 : Blo 1851627 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B15835247 : Blo 1851627 15835247 := bstep (se 1 (by rfl) ⟨11876435, by rfl⟩ : syracuseStep 15835247 = 23752871) B23752871
theorem B601695983 : Blo 1851627 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B1604522621 : Blo 1851627 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B10556831 : Blo 1851627 10556831 := bstep (se 1 (by rfl) ⟨7917623, by rfl⟩ : syracuseStep 10556831 = 15835247) B15835247
theorem B7037887 : Blo 1851627 7037887 := bstep (se 1 (by rfl) ⟨5278415, by rfl⟩ : syracuseStep 7037887 = 10556831) B10556831
theorem B4278726989 : Blo 1851627 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B9383849 : Blo 1851627 9383849 := bstep (se 2 (by rfl) ⟨3518943, by rfl⟩ : syracuseStep 9383849 = 7037887) B7037887
theorem B2852484659 : Blo 1851627 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B6255899 : Blo 1851627 6255899 := bstep (se 1 (by rfl) ⟨4691924, by rfl⟩ : syracuseStep 6255899 = 9383849) B9383849
theorem B1901656439 : Blo 1851627 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B4170599 : Blo 1851627 4170599 := bstep (se 1 (by rfl) ⟨3127949, by rfl⟩ : syracuseStep 4170599 = 6255899) B6255899
theorem B1267770959 : Blo 1851627 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B2780399 : Blo 1851627 2780399 := bstep (se 1 (by rfl) ⟨2085299, by rfl⟩ : syracuseStep 2780399 = 4170599) B4170599
theorem B845180639 : Blo 1851627 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B1853599 : Blo 1851627 1853599 := bstep (se 1 (by rfl) ⟨1390199, by rfl⟩ : syracuseStep 1853599 = 2780399) B2780399
theorem B563453759 : Blo 1851627 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B1502543357 : Blo 1851627 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 1851627 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B667797047 : Blo 1851627 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B445198031 : Blo 1851627 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B296798687 : Blo 1851627 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B197865791 : Blo 1851627 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B131910527 : Blo 1851627 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B87940351 : Blo 1851627 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B117253801 : Blo 1851627 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B625353605 : Blo 1851627 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B416902403 : Blo 1851627 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 1851627 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B741159827 : Blo 1851627 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B494106551 : Blo 1851627 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 1851627 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B219602911 : Blo 1851627 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 1851627 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 1851627 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 1851627 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B694053643 : Blo 1851627 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 1851627 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B616936571 : Blo 1851627 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 1851627 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B1096776125 : Blo 1851627 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B731184083 : Blo 1851627 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B487456055 : Blo 1851627 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 1851627 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B216647135 : Blo 1851627 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B144431423 : Blo 1851627 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 1851627 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 1851627 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B42794495 : Blo 1851627 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 1851627 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B76079101 : Blo 1851627 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B101438801 : Blo 1851627 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B67625867 : Blo 1851627 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B180335645 : Blo 1851627 180335645 := bstep (se 3 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 180335645 = 67625867) B67625867
theorem B120223763 : Blo 1851627 120223763 := bstep (se 1 (by rfl) ⟨90167822, by rfl⟩ : syracuseStep 120223763 = 180335645) B180335645
theorem B80149175 : Blo 1851627 80149175 := bstep (se 1 (by rfl) ⟨60111881, by rfl⟩ : syracuseStep 80149175 = 120223763) B120223763
theorem B53432783 : Blo 1851627 53432783 := bstep (se 1 (by rfl) ⟨40074587, by rfl⟩ : syracuseStep 53432783 = 80149175) B80149175
theorem B35621855 : Blo 1851627 35621855 := bstep (se 1 (by rfl) ⟨26716391, by rfl⟩ : syracuseStep 35621855 = 53432783) B53432783
theorem B23747903 : Blo 1851627 23747903 := bstep (se 1 (by rfl) ⟨17810927, by rfl⟩ : syracuseStep 23747903 = 35621855) B35621855
theorem B15831935 : Blo 1851627 15831935 := bstep (se 1 (by rfl) ⟨11873951, by rfl⟩ : syracuseStep 15831935 = 23747903) B23747903
theorem B10554623 : Blo 1851627 10554623 := bstep (se 1 (by rfl) ⟨7915967, by rfl⟩ : syracuseStep 10554623 = 15831935) B15831935
theorem B7036415 : Blo 1851627 7036415 := bstep (se 1 (by rfl) ⟨5277311, by rfl⟩ : syracuseStep 7036415 = 10554623) B10554623
theorem B4690943 : Blo 1851627 4690943 := bstep (se 1 (by rfl) ⟨3518207, by rfl⟩ : syracuseStep 4690943 = 7036415) B7036415
theorem B3127295 : Blo 1851627 3127295 := bstep (se 1 (by rfl) ⟨2345471, by rfl⟩ : syracuseStep 3127295 = 4690943) B4690943
theorem B2084863 : Blo 1851627 2084863 := bstep (se 1 (by rfl) ⟨1563647, by rfl⟩ : syracuseStep 2084863 = 3127295) B3127295
theorem B2779817 : Blo 1851627 2779817 := bstep (se 2 (by rfl) ⟨1042431, by rfl⟩ : syracuseStep 2779817 = 2084863) B2084863
theorem B1853211 : Blo 1851627 1853211 := bstep (se 1 (by rfl) ⟨1389908, by rfl⟩ : syracuseStep 1853211 = 2779817) B2779817

theorem C0 (j : ℕ) (h1 : 462906 ≤ j) (h2 : j ≤ 463406) : Blo 1851627 (4 * j + 3) := by
  interval_cases j
  · exact B1851627
  · exact B1851631
  · exact B1851635
  · exact B1851639
  · exact B1851643
  · exact B1851647
  · exact B1851651
  · exact B1851655
  · exact B1851659
  · exact B1851663
  · exact B1851667
  · exact B1851671
  · exact B1851675
  · exact B1851679
  · exact B1851683
  · exact B1851687
  · exact B1851691
  · exact B1851695
  · exact B1851699
  · exact B1851703
  · exact B1851707
  · exact B1851711
  · exact B1851715
  · exact B1851719
  · exact B1851723
  · exact B1851727
  · exact B1851731
  · exact B1851735
  · exact B1851739
  · exact B1851743
  · exact B1851747
  · exact B1851751
  · exact B1851755
  · exact B1851759
  · exact B1851763
  · exact B1851767
  · exact B1851771
  · exact B1851775
  · exact B1851779
  · exact B1851783
  · exact B1851787
  · exact B1851791
  · exact B1851795
  · exact B1851799
  · exact B1851803
  · exact B1851807
  · exact B1851811
  · exact B1851815
  · exact B1851819
  · exact B1851823
  · exact B1851827
  · exact B1851831
  · exact B1851835
  · exact B1851839
  · exact B1851843
  · exact B1851847
  · exact B1851851
  · exact B1851855
  · exact B1851859
  · exact B1851863
  · exact B1851867
  · exact B1851871
  · exact B1851875
  · exact B1851879
  · exact B1851883
  · exact B1851887
  · exact B1851891
  · exact B1851895
  · exact B1851899
  · exact B1851903
  · exact B1851907
  · exact B1851911
  · exact B1851915
  · exact B1851919
  · exact B1851923
  · exact B1851927
  · exact B1851931
  · exact B1851935
  · exact B1851939
  · exact B1851943
  · exact B1851947
  · exact B1851951
  · exact B1851955
  · exact B1851959
  · exact B1851963
  · exact B1851967
  · exact B1851971
  · exact B1851975
  · exact B1851979
  · exact B1851983
  · exact B1851987
  · exact B1851991
  · exact B1851995
  · exact B1851999
  · exact B1852003
  · exact B1852007
  · exact B1852011
  · exact B1852015
  · exact B1852019
  · exact B1852023
  · exact B1852027
  · exact B1852031
  · exact B1852035
  · exact B1852039
  · exact B1852043
  · exact B1852047
  · exact B1852051
  · exact B1852055
  · exact B1852059
  · exact B1852063
  · exact B1852067
  · exact B1852071
  · exact B1852075
  · exact B1852079
  · exact B1852083
  · exact B1852087
  · exact B1852091
  · exact B1852095
  · exact B1852099
  · exact B1852103
  · exact B1852107
  · exact B1852111
  · exact B1852115
  · exact B1852119
  · exact B1852123
  · exact B1852127
  · exact B1852131
  · exact B1852135
  · exact B1852139
  · exact B1852143
  · exact B1852147
  · exact B1852151
  · exact B1852155
  · exact B1852159
  · exact B1852163
  · exact B1852167
  · exact B1852171
  · exact B1852175
  · exact B1852179
  · exact B1852183
  · exact B1852187
  · exact B1852191
  · exact B1852195
  · exact B1852199
  · exact B1852203
  · exact B1852207
  · exact B1852211
  · exact B1852215
  · exact B1852219
  · exact B1852223
  · exact B1852227
  · exact B1852231
  · exact B1852235
  · exact B1852239
  · exact B1852243
  · exact B1852247
  · exact B1852251
  · exact B1852255
  · exact B1852259
  · exact B1852263
  · exact B1852267
  · exact B1852271
  · exact B1852275
  · exact B1852279
  · exact B1852283
  · exact B1852287
  · exact B1852291
  · exact B1852295
  · exact B1852299
  · exact B1852303
  · exact B1852307
  · exact B1852311
  · exact B1852315
  · exact B1852319
  · exact B1852323
  · exact B1852327
  · exact B1852331
  · exact B1852335
  · exact B1852339
  · exact B1852343
  · exact B1852347
  · exact B1852351
  · exact B1852355
  · exact B1852359
  · exact B1852363
  · exact B1852367
  · exact B1852371
  · exact B1852375
  · exact B1852379
  · exact B1852383
  · exact B1852387
  · exact B1852391
  · exact B1852395
  · exact B1852399
  · exact B1852403
  · exact B1852407
  · exact B1852411
  · exact B1852415
  · exact B1852419
  · exact B1852423
  · exact B1852427
  · exact B1852431
  · exact B1852435
  · exact B1852439
  · exact B1852443
  · exact B1852447
  · exact B1852451
  · exact B1852455
  · exact B1852459
  · exact B1852463
  · exact B1852467
  · exact B1852471
  · exact B1852475
  · exact B1852479
  · exact B1852483
  · exact B1852487
  · exact B1852491
  · exact B1852495
  · exact B1852499
  · exact B1852503
  · exact B1852507
  · exact B1852511
  · exact B1852515
  · exact B1852519
  · exact B1852523
  · exact B1852527
  · exact B1852531
  · exact B1852535
  · exact B1852539
  · exact B1852543
  · exact B1852547
  · exact B1852551
  · exact B1852555
  · exact B1852559
  · exact B1852563
  · exact B1852567
  · exact B1852571
  · exact B1852575
  · exact B1852579
  · exact B1852583
  · exact B1852587
  · exact B1852591
  · exact B1852595
  · exact B1852599
  · exact B1852603
  · exact B1852607
  · exact B1852611
  · exact B1852615
  · exact B1852619
  · exact B1852623
  · exact B1852627
  · exact B1852631
  · exact B1852635
  · exact B1852639
  · exact B1852643
  · exact B1852647
  · exact B1852651
  · exact B1852655
  · exact B1852659
  · exact B1852663
  · exact B1852667
  · exact B1852671
  · exact B1852675
  · exact B1852679
  · exact B1852683
  · exact B1852687
  · exact B1852691
  · exact B1852695
  · exact B1852699
  · exact B1852703
  · exact B1852707
  · exact B1852711
  · exact B1852715
  · exact B1852719
  · exact B1852723
  · exact B1852727
  · exact B1852731
  · exact B1852735
  · exact B1852739
  · exact B1852743
  · exact B1852747
  · exact B1852751
  · exact B1852755
  · exact B1852759
  · exact B1852763
  · exact B1852767
  · exact B1852771
  · exact B1852775
  · exact B1852779
  · exact B1852783
  · exact B1852787
  · exact B1852791
  · exact B1852795
  · exact B1852799
  · exact B1852803
  · exact B1852807
  · exact B1852811
  · exact B1852815
  · exact B1852819
  · exact B1852823
  · exact B1852827
  · exact B1852831
  · exact B1852835
  · exact B1852839
  · exact B1852843
  · exact B1852847
  · exact B1852851
  · exact B1852855
  · exact B1852859
  · exact B1852863
  · exact B1852867
  · exact B1852871
  · exact B1852875
  · exact B1852879
  · exact B1852883
  · exact B1852887
  · exact B1852891
  · exact B1852895
  · exact B1852899
  · exact B1852903
  · exact B1852907
  · exact B1852911
  · exact B1852915
  · exact B1852919
  · exact B1852923
  · exact B1852927
  · exact B1852931
  · exact B1852935
  · exact B1852939
  · exact B1852943
  · exact B1852947
  · exact B1852951
  · exact B1852955
  · exact B1852959
  · exact B1852963
  · exact B1852967
  · exact B1852971
  · exact B1852975
  · exact B1852979
  · exact B1852983
  · exact B1852987
  · exact B1852991
  · exact B1852995
  · exact B1852999
  · exact B1853003
  · exact B1853007
  · exact B1853011
  · exact B1853015
  · exact B1853019
  · exact B1853023
  · exact B1853027
  · exact B1853031
  · exact B1853035
  · exact B1853039
  · exact B1853043
  · exact B1853047
  · exact B1853051
  · exact B1853055
  · exact B1853059
  · exact B1853063
  · exact B1853067
  · exact B1853071
  · exact B1853075
  · exact B1853079
  · exact B1853083
  · exact B1853087
  · exact B1853091
  · exact B1853095
  · exact B1853099
  · exact B1853103
  · exact B1853107
  · exact B1853111
  · exact B1853115
  · exact B1853119
  · exact B1853123
  · exact B1853127
  · exact B1853131
  · exact B1853135
  · exact B1853139
  · exact B1853143
  · exact B1853147
  · exact B1853151
  · exact B1853155
  · exact B1853159
  · exact B1853163
  · exact B1853167
  · exact B1853171
  · exact B1853175
  · exact B1853179
  · exact B1853183
  · exact B1853187
  · exact B1853191
  · exact B1853195
  · exact B1853199
  · exact B1853203
  · exact B1853207
  · exact B1853211
  · exact B1853215
  · exact B1853219
  · exact B1853223
  · exact B1853227
  · exact B1853231
  · exact B1853235
  · exact B1853239
  · exact B1853243
  · exact B1853247
  · exact B1853251
  · exact B1853255
  · exact B1853259
  · exact B1853263
  · exact B1853267
  · exact B1853271
  · exact B1853275
  · exact B1853279
  · exact B1853283
  · exact B1853287
  · exact B1853291
  · exact B1853295
  · exact B1853299
  · exact B1853303
  · exact B1853307
  · exact B1853311
  · exact B1853315
  · exact B1853319
  · exact B1853323
  · exact B1853327
  · exact B1853331
  · exact B1853335
  · exact B1853339
  · exact B1853343
  · exact B1853347
  · exact B1853351
  · exact B1853355
  · exact B1853359
  · exact B1853363
  · exact B1853367
  · exact B1853371
  · exact B1853375
  · exact B1853379
  · exact B1853383
  · exact B1853387
  · exact B1853391
  · exact B1853395
  · exact B1853399
  · exact B1853403
  · exact B1853407
  · exact B1853411
  · exact B1853415
  · exact B1853419
  · exact B1853423
  · exact B1853427
  · exact B1853431
  · exact B1853435
  · exact B1853439
  · exact B1853443
  · exact B1853447
  · exact B1853451
  · exact B1853455
  · exact B1853459
  · exact B1853463
  · exact B1853467
  · exact B1853471
  · exact B1853475
  · exact B1853479
  · exact B1853483
  · exact B1853487
  · exact B1853491
  · exact B1853495
  · exact B1853499
  · exact B1853503
  · exact B1853507
  · exact B1853511
  · exact B1853515
  · exact B1853519
  · exact B1853523
  · exact B1853527
  · exact B1853531
  · exact B1853535
  · exact B1853539
  · exact B1853543
  · exact B1853547
  · exact B1853551
  · exact B1853555
  · exact B1853559
  · exact B1853563
  · exact B1853567
  · exact B1853571
  · exact B1853575
  · exact B1853579
  · exact B1853583
  · exact B1853587
  · exact B1853591
  · exact B1853595
  · exact B1853599
  · exact B1853603
  · exact B1853607
  · exact B1853611
  · exact B1853615
  · exact B1853619
  · exact B1853623
  · exact B1853627

theorem solution (m : ℕ) (hlo : 1851627 ≤ m) (hhi : m ≤ 1853627) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 462906 ≤ j := by omega
    have hj2 : j ≤ 463406 := by omega
    have hb : Blo 1851627 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
