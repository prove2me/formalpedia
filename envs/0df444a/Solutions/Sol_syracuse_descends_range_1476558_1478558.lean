-- Prove2me | solution 1 for syracuse_descends_range_1476558_1478558
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:45:16.467864+00:00
-- url     : https://prove2.me/submissions/f1708831-7415-4ab7-9b57-f90b0272a2cf

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


theorem B1662997 : Blo 1476558 1662997 := bbase (se 6 (by rfl) ⟨38976, by rfl⟩ : syracuseStep 1662997 = 77953) (by norm_num)
theorem B1663033 : Blo 1476558 1663033 := bbase (se 2 (by rfl) ⟨623637, by rfl⟩ : syracuseStep 1663033 = 1247275) (by norm_num)
theorem B3326021 : Blo 1476558 3326021 := bbase (se 4 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 3326021 = 623629) (by norm_num)
theorem B1663069 : Blo 1476558 1663069 := bbase (se 3 (by rfl) ⟨311825, by rfl⟩ : syracuseStep 1663069 = 623651) (by norm_num)
theorem B1663105 : Blo 1476558 1663105 := bbase (se 2 (by rfl) ⟨623664, by rfl⟩ : syracuseStep 1663105 = 1247329) (by norm_num)
theorem B3326093 : Blo 1476558 3326093 := bbase (se 3 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 3326093 = 1247285) (by norm_num)
theorem B2842781 : Blo 1476558 2842781 := bbase (se 3 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 2842781 = 1066043) (by norm_num)
theorem B1663141 : Blo 1476558 1663141 := bbase (se 4 (by rfl) ⟨155919, by rfl⟩ : syracuseStep 1663141 = 311839) (by norm_num)
theorem B2400421 : Blo 1476558 2400421 := bbase (se 4 (by rfl) ⟨225039, by rfl⟩ : syracuseStep 2400421 = 450079) (by norm_num)
theorem B1663177 : Blo 1476558 1663177 := bbase (se 2 (by rfl) ⟨623691, by rfl⟩ : syracuseStep 1663177 = 1247383) (by norm_num)
theorem B3154133 : Blo 1476558 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B3326165 : Blo 1476558 3326165 := bbase (se 7 (by rfl) ⟨38978, by rfl⟩ : syracuseStep 3326165 = 77957) (by norm_num)
theorem B1663213 : Blo 1476558 1663213 := bbase (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) (by norm_num)
theorem B5611781 : Blo 1476558 5611781 := bbase (se 4 (by rfl) ⟨526104, by rfl⟩ : syracuseStep 5611781 = 1052209) (by norm_num)
theorem B1663249 : Blo 1476558 1663249 := bbase (se 2 (by rfl) ⟨623718, by rfl⟩ : syracuseStep 1663249 = 1247437) (by norm_num)
theorem B3326237 : Blo 1476558 3326237 := bbase (se 3 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 3326237 = 1247339) (by norm_num)
theorem B4989221 : Blo 1476558 4989221 := bbase (se 4 (by rfl) ⟨467739, by rfl⟩ : syracuseStep 4989221 = 935479) (by norm_num)
theorem B1663285 : Blo 1476558 1663285 := bbase (se 5 (by rfl) ⟨77966, by rfl⟩ : syracuseStep 1663285 = 155933) (by norm_num)
theorem B1663321 : Blo 1476558 1663321 := bbase (se 2 (by rfl) ⟨623745, by rfl⟩ : syracuseStep 1663321 = 1247491) (by norm_num)
theorem B3326309 : Blo 1476558 3326309 := bbase (se 4 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 3326309 = 623683) (by norm_num)
theorem B1663357 : Blo 1476558 1663357 := bbase (se 3 (by rfl) ⟨311879, by rfl⟩ : syracuseStep 1663357 = 623759) (by norm_num)
theorem B7479701 : Blo 1476558 7479701 := bbase (se 6 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 7479701 = 350611) (by norm_num)
theorem B3326381 : Blo 1476558 3326381 := bbase (se 3 (by rfl) ⟨623696, by rfl⟩ : syracuseStep 3326381 = 1247393) (by norm_num)
theorem B3326453 : Blo 1476558 3326453 := bbase (se 5 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 3326453 = 311855) (by norm_num)
theorem B4735493 : Blo 1476558 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B3326525 : Blo 1476558 3326525 := bbase (se 3 (by rfl) ⟨623723, by rfl⟩ : syracuseStep 3326525 = 1247447) (by norm_num)
theorem B2663045 : Blo 1476558 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B3326597 : Blo 1476558 3326597 := bbase (se 4 (by rfl) ⟨311868, by rfl⟩ : syracuseStep 3326597 = 623737) (by norm_num)
theorem B3326669 : Blo 1476558 3326669 := bbase (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) (by norm_num)
theorem B4989653 : Blo 1476558 4989653 := bbase (se 7 (by rfl) ⟨58472, by rfl⟩ : syracuseStep 4989653 = 116945) (by norm_num)
theorem B3326741 : Blo 1476558 3326741 := bbase (se 6 (by rfl) ⟨77970, by rfl⟩ : syracuseStep 3326741 = 155941) (by norm_num)
theorem B9462581 : Blo 1476558 9462581 := bbase (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) (by norm_num)
theorem B1868933 : Blo 1476558 1868933 := bbase (se 4 (by rfl) ⟨175212, by rfl⟩ : syracuseStep 1868933 = 350425) (by norm_num)
theorem B4990085 : Blo 1476558 4990085 := bbase (se 4 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 4990085 = 935641) (by norm_num)
theorem B1868989 : Blo 1476558 1868989 := bbase (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) (by norm_num)
theorem B1869085 : Blo 1476558 1869085 := bbase (se 3 (by rfl) ⟨350453, by rfl⟩ : syracuseStep 1869085 = 700907) (by norm_num)
theorem B12617045 : Blo 1476558 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B2844013 : Blo 1476558 2844013 := bbase (se 3 (by rfl) ⟨533252, by rfl⟩ : syracuseStep 2844013 = 1066505) (by norm_num)
theorem B2491789 : Blo 1476558 2491789 := bbase (se 3 (by rfl) ⟨467210, by rfl⟩ : syracuseStep 2491789 = 934421) (by norm_num)
theorem B1869257 : Blo 1476558 1869257 := bbase (se 2 (by rfl) ⟨700971, by rfl⟩ : syracuseStep 1869257 = 1401943) (by norm_num)
theorem B2803157 : Blo 1476558 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B2491877 : Blo 1476558 2491877 := bbase (se 4 (by rfl) ⟨233613, by rfl⟩ : syracuseStep 2491877 = 467227) (by norm_num)
theorem B3368429 : Blo 1476558 3368429 := bbase (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) (by norm_num)
theorem B1869313 : Blo 1476558 1869313 := bbase (se 2 (by rfl) ⟨700992, by rfl⟩ : syracuseStep 1869313 = 1401985) (by norm_num)
theorem B1869409 : Blo 1476558 1869409 := bbase (se 2 (by rfl) ⟨701028, by rfl⟩ : syracuseStep 1869409 = 1402057) (by norm_num)
theorem B2492005 : Blo 1476558 2492005 := bbase (se 4 (by rfl) ⟨233625, by rfl⟩ : syracuseStep 2492005 = 467251) (by norm_num)
theorem B7480997 : Blo 1476558 7480997 := bbase (se 4 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 7480997 = 1402687) (by norm_num)
theorem B2492093 : Blo 1476558 2492093 := bbase (se 3 (by rfl) ⟨467267, by rfl⟩ : syracuseStep 2492093 = 934535) (by norm_num)
theorem B3548861 : Blo 1476558 3548861 := bbase (se 3 (by rfl) ⟨665411, by rfl⟩ : syracuseStep 3548861 = 1330823) (by norm_num)
theorem B1869581 : Blo 1476558 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B8415029 : Blo 1476558 8415029 := bbase (se 5 (by rfl) ⟨394454, by rfl⟩ : syracuseStep 8415029 = 788909) (by norm_num)
theorem B2492221 : Blo 1476558 2492221 := bbase (se 3 (by rfl) ⟨467291, by rfl⟩ : syracuseStep 2492221 = 934583) (by norm_num)
theorem B3155773 : Blo 1476558 3155773 := bbase (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) (by norm_num)
theorem B6309701 : Blo 1476558 6309701 := bbase (se 4 (by rfl) ⟨591534, by rfl⟩ : syracuseStep 6309701 = 1183069) (by norm_num)
theorem B1869637 : Blo 1476558 1869637 := bbase (se 4 (by rfl) ⟨175278, by rfl⟩ : syracuseStep 1869637 = 350557) (by norm_num)
theorem B15976277 : Blo 1476558 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B9471829 : Blo 1476558 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B3549053 : Blo 1476558 3549053 := bbase (se 3 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 3549053 = 1330895) (by norm_num)
theorem B2492309 : Blo 1476558 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B1869733 : Blo 1476558 1869733 := bbase (se 4 (by rfl) ⟨175287, by rfl⟩ : syracuseStep 1869733 = 350575) (by norm_num)
theorem B7096261 : Blo 1476558 7096261 := bbase (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) (by norm_num)
theorem B3737573 : Blo 1476558 3737573 := bbase (se 4 (by rfl) ⟨350397, by rfl⟩ : syracuseStep 3737573 = 700795) (by norm_num)
theorem B2492437 : Blo 1476558 2492437 := bbase (se 6 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 2492437 = 116833) (by norm_num)
theorem B11225141 : Blo 1476558 11225141 := bbase (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) (by norm_num)
theorem B1869905 : Blo 1476558 1869905 := bbase (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) (by norm_num)
theorem B2492525 : Blo 1476558 2492525 := bbase (se 3 (by rfl) ⟨467348, by rfl⟩ : syracuseStep 2492525 = 934697) (by norm_num)
theorem B1869961 : Blo 1476558 1869961 := bbase (se 2 (by rfl) ⟨701235, by rfl⟩ : syracuseStep 1869961 = 1402471) (by norm_num)
theorem B4049045 : Blo 1476558 4049045 := bbase (se 6 (by rfl) ⟨94899, by rfl⟩ : syracuseStep 4049045 = 189799) (by norm_num)
theorem B10389653 : Blo 1476558 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B3737765 : Blo 1476558 3737765 := bbase (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) (by norm_num)
theorem B2803909 : Blo 1476558 2803909 := bbase (se 4 (by rfl) ⟨262866, by rfl⟩ : syracuseStep 2803909 = 525733) (by norm_num)
theorem B1870057 : Blo 1476558 1870057 := bbase (se 2 (by rfl) ⟨701271, by rfl⟩ : syracuseStep 1870057 = 1402543) (by norm_num)
theorem B2492653 : Blo 1476558 2492653 := bbase (se 3 (by rfl) ⟨467372, by rfl⟩ : syracuseStep 2492653 = 934745) (by norm_num)
theorem B2492741 : Blo 1476558 2492741 := bbase (se 4 (by rfl) ⟨233694, by rfl⟩ : syracuseStep 2492741 = 467389) (by norm_num)
theorem B5613893 : Blo 1476558 5613893 := bbase (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) (by norm_num)
theorem B2804053 : Blo 1476558 2804053 := bbase (se 10 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 2804053 = 8215) (by norm_num)
theorem B2247053 : Blo 1476558 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B1870229 : Blo 1476558 1870229 := bbase (se 6 (by rfl) ⟨43833, by rfl⟩ : syracuseStep 1870229 = 87667) (by norm_num)
theorem B2492869 : Blo 1476558 2492869 := bbase (se 4 (by rfl) ⟨233706, by rfl⟩ : syracuseStep 2492869 = 467413) (by norm_num)
theorem B1870285 : Blo 1476558 1870285 := bbase (se 3 (by rfl) ⟨350678, by rfl⟩ : syracuseStep 1870285 = 701357) (by norm_num)
theorem B1599953 : Blo 1476558 1599953 := bbase (se 2 (by rfl) ⟨599982, by rfl⟩ : syracuseStep 1599953 = 1199965) (by norm_num)
theorem B11217365 : Blo 1476558 11217365 := bbase (se 7 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 11217365 = 262907) (by norm_num)
theorem B4491749 : Blo 1476558 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B2804213 : Blo 1476558 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B3738109 : Blo 1476558 3738109 := bbase (se 3 (by rfl) ⟨700895, by rfl⟩ : syracuseStep 3738109 = 1401791) (by norm_num)
theorem B2492957 : Blo 1476558 2492957 := bbase (se 3 (by rfl) ⟨467429, by rfl⟩ : syracuseStep 2492957 = 934859) (by norm_num)
theorem B1870381 : Blo 1476558 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B12143189 : Blo 1476558 12143189 := bbase (se 8 (by rfl) ⟨71151, by rfl⟩ : syracuseStep 12143189 = 142303) (by norm_num)
theorem B3738221 : Blo 1476558 3738221 := bbase (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) (by norm_num)
theorem B4795013 : Blo 1476558 4795013 := bbase (se 4 (by rfl) ⟨449532, by rfl⟩ : syracuseStep 4795013 = 899065) (by norm_num)
theorem B2804357 : Blo 1476558 2804357 := bbase (se 4 (by rfl) ⟨262908, by rfl⟩ : syracuseStep 2804357 = 525817) (by norm_num)
theorem B2493085 : Blo 1476558 2493085 := bbase (se 3 (by rfl) ⟨467453, by rfl⟩ : syracuseStep 2493085 = 934907) (by norm_num)
theorem B3156661 : Blo 1476558 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B1870553 : Blo 1476558 1870553 := bbase (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) (by norm_num)
theorem B2493173 : Blo 1476558 2493173 := bbase (se 5 (by rfl) ⟨116867, by rfl⟩ : syracuseStep 2493173 = 233735) (by norm_num)
theorem B4205317 : Blo 1476558 4205317 := bbase (se 4 (by rfl) ⟨394248, by rfl⟩ : syracuseStep 4205317 = 788497) (by norm_num)
theorem B2132749 : Blo 1476558 2132749 := bbase (se 3 (by rfl) ⟨399890, by rfl⟩ : syracuseStep 2132749 = 799781) (by norm_num)
theorem B1870609 : Blo 1476558 1870609 := bbase (se 2 (by rfl) ⟨701478, by rfl⟩ : syracuseStep 1870609 = 1402957) (by norm_num)
theorem B3738413 : Blo 1476558 3738413 := bbase (se 3 (by rfl) ⟨700952, by rfl⟩ : syracuseStep 3738413 = 1401905) (by norm_num)
theorem B4983605 : Blo 1476558 4983605 := bbase (se 5 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 4983605 = 467213) (by norm_num)
theorem B2526061 : Blo 1476558 2526061 := bbase (se 3 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 2526061 = 947273) (by norm_num)
theorem B1870705 : Blo 1476558 1870705 := bbase (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) (by norm_num)
theorem B2493301 : Blo 1476558 2493301 := bbase (se 5 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 2493301 = 233747) (by norm_num)
theorem B2804645 : Blo 1476558 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B7482293 : Blo 1476558 7482293 := bbase (se 5 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 7482293 = 701465) (by norm_num)
theorem B2214845 : Blo 1476558 2214845 := bbase (se 3 (by rfl) ⟨415283, by rfl⟩ : syracuseStep 2214845 = 830567) (by norm_num)
theorem B2493389 : Blo 1476558 2493389 := bbase (se 3 (by rfl) ⟨467510, by rfl⟩ : syracuseStep 2493389 = 935021) (by norm_num)
theorem B2214869 : Blo 1476558 2214869 := bbase (se 7 (by rfl) ⟨25955, by rfl⟩ : syracuseStep 2214869 = 51911) (by norm_num)
theorem B2214893 : Blo 1476558 2214893 := bbase (se 3 (by rfl) ⟨415292, by rfl⟩ : syracuseStep 2214893 = 830585) (by norm_num)
theorem B2247661 : Blo 1476558 2247661 := bbase (se 3 (by rfl) ⟨421436, by rfl⟩ : syracuseStep 2247661 = 842873) (by norm_num)
theorem B5606405 : Blo 1476558 5606405 := bbase (se 4 (by rfl) ⟨525600, by rfl⟩ : syracuseStep 5606405 = 1051201) (by norm_num)
theorem B2214917 : Blo 1476558 2214917 := bbase (se 4 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 2214917 = 415297) (by norm_num)
theorem B1895449 : Blo 1476558 1895449 := bbase (se 2 (by rfl) ⟨710793, by rfl⟩ : syracuseStep 1895449 = 1421587) (by norm_num)
theorem B2214941 : Blo 1476558 2214941 := bbase (se 3 (by rfl) ⟨415301, by rfl⟩ : syracuseStep 2214941 = 830603) (by norm_num)
theorem B1870877 : Blo 1476558 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B2214965 : Blo 1476558 2214965 := bbase (se 5 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 2214965 = 207653) (by norm_num)
theorem B2804797 : Blo 1476558 2804797 := bbase (se 3 (by rfl) ⟨525899, by rfl⟩ : syracuseStep 2804797 = 1051799) (by norm_num)
theorem B2214989 : Blo 1476558 2214989 := bbase (se 3 (by rfl) ⟨415310, by rfl⟩ : syracuseStep 2214989 = 830621) (by norm_num)
theorem B2493517 : Blo 1476558 2493517 := bbase (se 3 (by rfl) ⟨467534, by rfl⟩ : syracuseStep 2493517 = 935069) (by norm_num)
theorem B1870933 : Blo 1476558 1870933 := bbase (se 8 (by rfl) ⟨10962, by rfl⟩ : syracuseStep 1870933 = 21925) (by norm_num)
theorem B2215013 : Blo 1476558 2215013 := bbase (se 4 (by rfl) ⟨207657, by rfl⟩ : syracuseStep 2215013 = 415315) (by norm_num)
theorem B2215037 : Blo 1476558 2215037 := bbase (se 3 (by rfl) ⟨415319, by rfl⟩ : syracuseStep 2215037 = 830639) (by norm_num)
theorem B3738757 : Blo 1476558 3738757 := bbase (se 4 (by rfl) ⟨350508, by rfl⟩ : syracuseStep 3738757 = 701017) (by norm_num)
theorem B2247821 : Blo 1476558 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B2215061 : Blo 1476558 2215061 := bbase (se 6 (by rfl) ⟨51915, by rfl⟩ : syracuseStep 2215061 = 103831) (by norm_num)
theorem B2493605 : Blo 1476558 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B3157157 : Blo 1476558 3157157 := bbase (se 4 (by rfl) ⟨295983, by rfl⟩ : syracuseStep 3157157 = 591967) (by norm_num)
theorem B2215085 : Blo 1476558 2215085 := bbase (se 3 (by rfl) ⟨415328, by rfl⟩ : syracuseStep 2215085 = 830657) (by norm_num)
theorem B1871029 : Blo 1476558 1871029 := bbase (se 5 (by rfl) ⟨87704, by rfl⟩ : syracuseStep 1871029 = 175409) (by norm_num)
theorem B2215109 : Blo 1476558 2215109 := bbase (se 4 (by rfl) ⟨207666, by rfl⟩ : syracuseStep 2215109 = 415333) (by norm_num)
theorem B2215133 : Blo 1476558 2215133 := bbase (se 3 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 2215133 = 830675) (by norm_num)
theorem B4984037 : Blo 1476558 4984037 := bbase (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) (by norm_num)
theorem B2215157 : Blo 1476558 2215157 := bbase (se 5 (by rfl) ⟨103835, by rfl⟩ : syracuseStep 2215157 = 207671) (by norm_num)
theorem B3738869 : Blo 1476558 3738869 := bbase (se 5 (by rfl) ⟨175259, by rfl⟩ : syracuseStep 3738869 = 350519) (by norm_num)
theorem B2215181 : Blo 1476558 2215181 := bbase (se 3 (by rfl) ⟨415346, by rfl⟩ : syracuseStep 2215181 = 830693) (by norm_num)
theorem B2215205 : Blo 1476558 2215205 := bbase (se 4 (by rfl) ⟨207675, by rfl⟩ : syracuseStep 2215205 = 415351) (by norm_num)
theorem B2493733 : Blo 1476558 2493733 := bbase (se 4 (by rfl) ⟨233787, by rfl⟩ : syracuseStep 2493733 = 467575) (by norm_num)
theorem B2215229 : Blo 1476558 2215229 := bbase (se 3 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 2215229 = 830711) (by norm_num)
theorem B2247997 : Blo 1476558 2247997 := bbase (se 3 (by rfl) ⟨421499, by rfl⟩ : syracuseStep 2247997 = 842999) (by norm_num)
theorem B2215253 : Blo 1476558 2215253 := bbase (se 11 (by rfl) ⟨1622, by rfl⟩ : syracuseStep 2215253 = 3245) (by norm_num)
theorem B1871201 : Blo 1476558 1871201 := bbase (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) (by norm_num)
theorem B2215277 : Blo 1476558 2215277 := bbase (se 3 (by rfl) ⟨415364, by rfl⟩ : syracuseStep 2215277 = 830729) (by norm_num)
theorem B2805101 : Blo 1476558 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B7990645 : Blo 1476558 7990645 := bbase (se 5 (by rfl) ⟨374561, by rfl⟩ : syracuseStep 7990645 = 749123) (by norm_num)
theorem B2493821 : Blo 1476558 2493821 := bbase (se 3 (by rfl) ⟨467591, by rfl⟩ : syracuseStep 2493821 = 935183) (by norm_num)
theorem B2215301 : Blo 1476558 2215301 := bbase (se 4 (by rfl) ⟨207684, by rfl⟩ : syracuseStep 2215301 = 415369) (by norm_num)
theorem B1871257 : Blo 1476558 1871257 := bbase (se 2 (by rfl) ⟨701721, by rfl⟩ : syracuseStep 1871257 = 1403443) (by norm_num)
theorem B2215325 : Blo 1476558 2215325 := bbase (se 3 (by rfl) ⟨415373, by rfl⟩ : syracuseStep 2215325 = 830747) (by norm_num)
theorem B2215349 : Blo 1476558 2215349 := bbase (se 5 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 2215349 = 207689) (by norm_num)
theorem B3739061 : Blo 1476558 3739061 := bbase (se 5 (by rfl) ⟨175268, by rfl⟩ : syracuseStep 3739061 = 350537) (by norm_num)
theorem B2215373 : Blo 1476558 2215373 := bbase (se 3 (by rfl) ⟨415382, by rfl⟩ : syracuseStep 2215373 = 830765) (by norm_num)
theorem B2215397 : Blo 1476558 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B2215421 : Blo 1476558 2215421 := bbase (se 3 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 2215421 = 830783) (by norm_num)
theorem B2493949 : Blo 1476558 2493949 := bbase (se 3 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 2493949 = 935231) (by norm_num)
theorem B2215445 : Blo 1476558 2215445 := bbase (se 6 (by rfl) ⟨51924, by rfl⟩ : syracuseStep 2215445 = 103849) (by norm_num)
theorem B2215469 : Blo 1476558 2215469 := bbase (se 3 (by rfl) ⟨415400, by rfl⟩ : syracuseStep 2215469 = 830801) (by norm_num)
theorem B2215493 : Blo 1476558 2215493 := bbase (se 4 (by rfl) ⟨207702, by rfl⟩ : syracuseStep 2215493 = 415405) (by norm_num)
theorem B2494037 : Blo 1476558 2494037 := bbase (se 8 (by rfl) ⟨14613, by rfl⟩ : syracuseStep 2494037 = 29227) (by norm_num)
theorem B2215517 : Blo 1476558 2215517 := bbase (se 3 (by rfl) ⟨415409, by rfl⟩ : syracuseStep 2215517 = 830819) (by norm_num)
theorem B2215541 : Blo 1476558 2215541 := bbase (se 5 (by rfl) ⟨103853, by rfl⟩ : syracuseStep 2215541 = 207707) (by norm_num)
theorem B2215565 : Blo 1476558 2215565 := bbase (se 3 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 2215565 = 830837) (by norm_num)
theorem B4984469 : Blo 1476558 4984469 := bbase (se 6 (by rfl) ⟨116823, by rfl⟩ : syracuseStep 4984469 = 233647) (by norm_num)
theorem B2526869 : Blo 1476558 2526869 := bbase (se 6 (by rfl) ⟨59223, by rfl⟩ : syracuseStep 2526869 = 118447) (by norm_num)
theorem B2215589 : Blo 1476558 2215589 := bbase (se 4 (by rfl) ⟨207711, by rfl⟩ : syracuseStep 2215589 = 415423) (by norm_num)
theorem B2215613 : Blo 1476558 2215613 := bbase (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) (by norm_num)
theorem B2215637 : Blo 1476558 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B2494165 : Blo 1476558 2494165 := bbase (se 7 (by rfl) ⟨29228, by rfl⟩ : syracuseStep 2494165 = 58457) (by norm_num)
theorem B2215661 : Blo 1476558 2215661 := bbase (se 3 (by rfl) ⟨415436, by rfl⟩ : syracuseStep 2215661 = 830873) (by norm_num)
theorem B3600125 : Blo 1476558 3600125 := bbase (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) (by norm_num)
theorem B2215685 : Blo 1476558 2215685 := bbase (se 4 (by rfl) ⟨207720, by rfl⟩ : syracuseStep 2215685 = 415441) (by norm_num)
theorem B3739405 : Blo 1476558 3739405 := bbase (se 3 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 3739405 = 1402277) (by norm_num)
theorem B2215709 : Blo 1476558 2215709 := bbase (se 3 (by rfl) ⟨415445, by rfl⟩ : syracuseStep 2215709 = 830891) (by norm_num)
theorem B2494253 : Blo 1476558 2494253 := bbase (se 3 (by rfl) ⟨467672, by rfl⟩ : syracuseStep 2494253 = 935345) (by norm_num)
theorem B2215733 : Blo 1476558 2215733 := bbase (se 5 (by rfl) ⟨103862, by rfl⟩ : syracuseStep 2215733 = 207725) (by norm_num)
theorem B2215757 : Blo 1476558 2215757 := bbase (se 3 (by rfl) ⟨415454, by rfl⟩ : syracuseStep 2215757 = 830909) (by norm_num)
theorem B3551053 : Blo 1476558 3551053 := bbase (se 3 (by rfl) ⟨665822, by rfl⟩ : syracuseStep 3551053 = 1331645) (by norm_num)
theorem B4206421 : Blo 1476558 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B1576793 : Blo 1476558 1576793 := bbase (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) (by norm_num)
theorem B2215781 : Blo 1476558 2215781 := bbase (se 4 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 2215781 = 415459) (by norm_num)
theorem B2215805 : Blo 1476558 2215805 := bbase (se 3 (by rfl) ⟨415463, by rfl⟩ : syracuseStep 2215805 = 830927) (by norm_num)
theorem B3739517 : Blo 1476558 3739517 := bbase (se 3 (by rfl) ⟨701159, by rfl⟩ : syracuseStep 3739517 = 1402319) (by norm_num)
theorem B2215829 : Blo 1476558 2215829 := bbase (se 6 (by rfl) ⟨51933, by rfl⟩ : syracuseStep 2215829 = 103867) (by norm_num)
theorem B2215853 : Blo 1476558 2215853 := bbase (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) (by norm_num)
theorem B2494381 : Blo 1476558 2494381 := bbase (se 3 (by rfl) ⟨467696, by rfl⟩ : syracuseStep 2494381 = 935393) (by norm_num)
theorem B9465781 : Blo 1476558 9465781 := bbase (se 5 (by rfl) ⟨443708, by rfl⟩ : syracuseStep 9465781 = 887417) (by norm_num)
theorem B2215877 : Blo 1476558 2215877 := bbase (se 4 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 2215877 = 415477) (by norm_num)
theorem B2215901 : Blo 1476558 2215901 := bbase (se 3 (by rfl) ⟨415481, by rfl⟩ : syracuseStep 2215901 = 830963) (by norm_num)
theorem B2215925 : Blo 1476558 2215925 := bbase (se 5 (by rfl) ⟨103871, by rfl⟩ : syracuseStep 2215925 = 207743) (by norm_num)
theorem B2494469 : Blo 1476558 2494469 := bbase (se 4 (by rfl) ⟨233856, by rfl⟩ : syracuseStep 2494469 = 467713) (by norm_num)
theorem B3600389 : Blo 1476558 3600389 := bbase (se 4 (by rfl) ⟨337536, by rfl⟩ : syracuseStep 3600389 = 675073) (by norm_num)
theorem B2215949 : Blo 1476558 2215949 := bbase (se 3 (by rfl) ⟨415490, by rfl⟩ : syracuseStep 2215949 = 830981) (by norm_num)
theorem B2215973 : Blo 1476558 2215973 := bbase (se 4 (by rfl) ⟨207747, by rfl⟩ : syracuseStep 2215973 = 415495) (by norm_num)
theorem B5992501 : Blo 1476558 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B2215997 : Blo 1476558 2215997 := bbase (se 3 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 2215997 = 830999) (by norm_num)
theorem B3739709 : Blo 1476558 3739709 := bbase (se 3 (by rfl) ⟨701195, by rfl⟩ : syracuseStep 3739709 = 1402391) (by norm_num)
theorem B4984901 : Blo 1476558 4984901 := bbase (se 4 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 4984901 = 934669) (by norm_num)
theorem B2216021 : Blo 1476558 2216021 := bbase (se 8 (by rfl) ⟨12984, by rfl⟩ : syracuseStep 2216021 = 25969) (by norm_num)
theorem B2805853 : Blo 1476558 2805853 := bbase (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) (by norm_num)
theorem B2216045 : Blo 1476558 2216045 := bbase (se 3 (by rfl) ⟨415508, by rfl⟩ : syracuseStep 2216045 = 831017) (by norm_num)
theorem B2216069 : Blo 1476558 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B2494597 : Blo 1476558 2494597 := bbase (se 4 (by rfl) ⟨233868, by rfl⟩ : syracuseStep 2494597 = 467737) (by norm_num)
theorem B2216093 : Blo 1476558 2216093 := bbase (se 3 (by rfl) ⟨415517, by rfl⟩ : syracuseStep 2216093 = 831035) (by norm_num)
theorem B3371165 : Blo 1476558 3371165 := bbase (se 3 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 3371165 = 1264187) (by norm_num)
theorem B5607589 : Blo 1476558 5607589 := bbase (se 4 (by rfl) ⟨525711, by rfl⟩ : syracuseStep 5607589 = 1051423) (by norm_num)
theorem B4796581 : Blo 1476558 4796581 := bbase (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) (by norm_num)
theorem B2216117 : Blo 1476558 2216117 := bbase (se 5 (by rfl) ⟨103880, by rfl⟩ : syracuseStep 2216117 = 207761) (by norm_num)
theorem B2699453 : Blo 1476558 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B7483589 : Blo 1476558 7483589 := bbase (se 4 (by rfl) ⟨701586, by rfl⟩ : syracuseStep 7483589 = 1403173) (by norm_num)
theorem B2216141 : Blo 1476558 2216141 := bbase (se 3 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 2216141 = 831053) (by norm_num)
theorem B2494685 : Blo 1476558 2494685 := bbase (se 3 (by rfl) ⟨467753, by rfl⟩ : syracuseStep 2494685 = 935507) (by norm_num)
theorem B2216165 : Blo 1476558 2216165 := bbase (se 4 (by rfl) ⟨207765, by rfl⟩ : syracuseStep 2216165 = 415531) (by norm_num)
theorem B2805997 : Blo 1476558 2805997 := bbase (se 3 (by rfl) ⟨526124, by rfl⟩ : syracuseStep 2805997 = 1052249) (by norm_num)
theorem B2216189 : Blo 1476558 2216189 := bbase (se 3 (by rfl) ⟨415535, by rfl⟩ : syracuseStep 2216189 = 831071) (by norm_num)
theorem B1577237 : Blo 1476558 1577237 := bbase (se 6 (by rfl) ⟨36966, by rfl⟩ : syracuseStep 1577237 = 73933) (by norm_num)
theorem B2216213 : Blo 1476558 2216213 := bbase (se 6 (by rfl) ⟨51942, by rfl⟩ : syracuseStep 2216213 = 103885) (by norm_num)
theorem B2216237 : Blo 1476558 2216237 := bbase (se 3 (by rfl) ⟨415544, by rfl⟩ : syracuseStep 2216237 = 831089) (by norm_num)
theorem B2216261 : Blo 1476558 2216261 := bbase (se 4 (by rfl) ⟨207774, by rfl⟩ : syracuseStep 2216261 = 415549) (by norm_num)
theorem B2527573 : Blo 1476558 2527573 := bbase (se 10 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 2527573 = 7405) (by norm_num)
theorem B2216285 : Blo 1476558 2216285 := bbase (se 3 (by rfl) ⟨415553, by rfl⟩ : syracuseStep 2216285 = 831107) (by norm_num)
theorem B2494813 : Blo 1476558 2494813 := bbase (se 3 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 2494813 = 935555) (by norm_num)
theorem B2216309 : Blo 1476558 2216309 := bbase (se 5 (by rfl) ⟨103889, by rfl⟩ : syracuseStep 2216309 = 207779) (by norm_num)
theorem B2216333 : Blo 1476558 2216333 := bbase (se 3 (by rfl) ⟨415562, by rfl⟩ : syracuseStep 2216333 = 831125) (by norm_num)
theorem B2806157 : Blo 1476558 2806157 := bbase (se 3 (by rfl) ⟨526154, by rfl⟩ : syracuseStep 2806157 = 1052309) (by norm_num)
theorem B3551629 : Blo 1476558 3551629 := bbase (se 3 (by rfl) ⟨665930, by rfl⟩ : syracuseStep 3551629 = 1331861) (by norm_num)
theorem B3740053 : Blo 1476558 3740053 := bbase (se 6 (by rfl) ⟨87657, by rfl⟩ : syracuseStep 3740053 = 175315) (by norm_num)
theorem B3322277 : Blo 1476558 3322277 := bbase (se 4 (by rfl) ⟨311463, by rfl⟩ : syracuseStep 3322277 = 622927) (by norm_num)
theorem B4731301 : Blo 1476558 4731301 := bbase (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) (by norm_num)
theorem B2216357 : Blo 1476558 2216357 := bbase (se 4 (by rfl) ⟨207783, by rfl⟩ : syracuseStep 2216357 = 415567) (by norm_num)
theorem B1798573 : Blo 1476558 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B2494901 : Blo 1476558 2494901 := bbase (se 5 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 2494901 = 233897) (by norm_num)
theorem B2216381 : Blo 1476558 2216381 := bbase (se 3 (by rfl) ⟨415571, by rfl⟩ : syracuseStep 2216381 = 831143) (by norm_num)
theorem B4493765 : Blo 1476558 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B5607893 : Blo 1476558 5607893 := bbase (se 7 (by rfl) ⟨65717, by rfl⟩ : syracuseStep 5607893 = 131435) (by norm_num)
theorem B2216405 : Blo 1476558 2216405 := bbase (se 7 (by rfl) ⟨25973, by rfl⟩ : syracuseStep 2216405 = 51947) (by norm_num)
theorem B3322349 : Blo 1476558 3322349 := bbase (se 3 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 3322349 = 1245881) (by norm_num)
theorem B2216429 : Blo 1476558 2216429 := bbase (se 3 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 2216429 = 831161) (by norm_num)
theorem B13472245 : Blo 1476558 13472245 := bbase (se 5 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 13472245 = 1263023) (by norm_num)
theorem B4985333 : Blo 1476558 4985333 := bbase (se 5 (by rfl) ⟨233687, by rfl⟩ : syracuseStep 4985333 = 467375) (by norm_num)
theorem B3740165 : Blo 1476558 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B2216453 : Blo 1476558 2216453 := bbase (se 4 (by rfl) ⟨207792, by rfl⟩ : syracuseStep 2216453 = 415585) (by norm_num)
theorem B1577485 : Blo 1476558 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B2216477 : Blo 1476558 2216477 := bbase (se 3 (by rfl) ⟨415589, by rfl⟩ : syracuseStep 2216477 = 831179) (by norm_num)
theorem B2806301 : Blo 1476558 2806301 := bbase (se 3 (by rfl) ⟨526181, by rfl⟩ : syracuseStep 2806301 = 1052363) (by norm_num)
theorem B8409653 : Blo 1476558 8409653 := bbase (se 5 (by rfl) ⟨394202, by rfl⟩ : syracuseStep 8409653 = 788405) (by norm_num)
theorem B3322421 : Blo 1476558 3322421 := bbase (se 5 (by rfl) ⟨155738, by rfl⟩ : syracuseStep 3322421 = 311477) (by norm_num)
theorem B2216501 : Blo 1476558 2216501 := bbase (se 5 (by rfl) ⟨103898, by rfl⟩ : syracuseStep 2216501 = 207797) (by norm_num)
theorem B2495029 : Blo 1476558 2495029 := bbase (se 5 (by rfl) ⟨116954, by rfl⟩ : syracuseStep 2495029 = 233909) (by norm_num)
theorem B2216525 : Blo 1476558 2216525 := bbase (se 3 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 2216525 = 831197) (by norm_num)
theorem B7475813 : Blo 1476558 7475813 := bbase (se 4 (by rfl) ⟨700857, by rfl⟩ : syracuseStep 7475813 = 1401715) (by norm_num)
theorem B1774181 : Blo 1476558 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B2216549 : Blo 1476558 2216549 := bbase (se 4 (by rfl) ⟨207801, by rfl⟩ : syracuseStep 2216549 = 415603) (by norm_num)
theorem B2527853 : Blo 1476558 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B3322493 : Blo 1476558 3322493 := bbase (se 3 (by rfl) ⟨622967, by rfl⟩ : syracuseStep 3322493 = 1245935) (by norm_num)
theorem B2216573 : Blo 1476558 2216573 := bbase (se 3 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 2216573 = 831215) (by norm_num)
theorem B6075013 : Blo 1476558 6075013 := bbase (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) (by norm_num)
theorem B12145301 : Blo 1476558 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B2216597 : Blo 1476558 2216597 := bbase (se 6 (by rfl) ⟨51951, by rfl⟩ : syracuseStep 2216597 = 103903) (by norm_num)
theorem B2216621 : Blo 1476558 2216621 := bbase (se 3 (by rfl) ⟨415616, by rfl⟩ : syracuseStep 2216621 = 831233) (by norm_num)
theorem B3322565 : Blo 1476558 3322565 := bbase (se 4 (by rfl) ⟨311490, by rfl⟩ : syracuseStep 3322565 = 622981) (by norm_num)
theorem B4264645 : Blo 1476558 4264645 := bbase (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) (by norm_num)
theorem B3740357 : Blo 1476558 3740357 := bbase (se 4 (by rfl) ⟨350658, by rfl⟩ : syracuseStep 3740357 = 701317) (by norm_num)
theorem B2216645 : Blo 1476558 2216645 := bbase (se 4 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 2216645 = 415621) (by norm_num)
theorem B2527957 : Blo 1476558 2527957 := bbase (se 7 (by rfl) ⟨29624, by rfl⟩ : syracuseStep 2527957 = 59249) (by norm_num)
theorem B3551957 : Blo 1476558 3551957 := bbase (se 7 (by rfl) ⟨41624, by rfl⟩ : syracuseStep 3551957 = 83249) (by norm_num)
theorem B2216669 : Blo 1476558 2216669 := bbase (se 3 (by rfl) ⟨415625, by rfl⟩ : syracuseStep 2216669 = 831251) (by norm_num)
theorem B2216693 : Blo 1476558 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B3322637 : Blo 1476558 3322637 := bbase (se 3 (by rfl) ⟨622994, by rfl⟩ : syracuseStep 3322637 = 1245989) (by norm_num)
theorem B2216717 : Blo 1476558 2216717 := bbase (se 3 (by rfl) ⟨415634, by rfl⟩ : syracuseStep 2216717 = 831269) (by norm_num)
theorem B3552013 : Blo 1476558 3552013 := bbase (se 3 (by rfl) ⟨666002, by rfl⟩ : syracuseStep 3552013 = 1332005) (by norm_num)
theorem B2216741 : Blo 1476558 2216741 := bbase (se 4 (by rfl) ⟨207819, by rfl⟩ : syracuseStep 2216741 = 415639) (by norm_num)
theorem B2216765 : Blo 1476558 2216765 := bbase (se 3 (by rfl) ⟨415643, by rfl⟩ : syracuseStep 2216765 = 831287) (by norm_num)
theorem B2806589 : Blo 1476558 2806589 := bbase (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) (by norm_num)
theorem B3322709 : Blo 1476558 3322709 := bbase (se 9 (by rfl) ⟨9734, by rfl⟩ : syracuseStep 3322709 = 19469) (by norm_num)
theorem B2216789 : Blo 1476558 2216789 := bbase (se 9 (by rfl) ⟨6494, by rfl⟩ : syracuseStep 2216789 = 12989) (by norm_num)
theorem B2216813 : Blo 1476558 2216813 := bbase (se 3 (by rfl) ⟨415652, by rfl⟩ : syracuseStep 2216813 = 831305) (by norm_num)
theorem B2216837 : Blo 1476558 2216837 := bbase (se 4 (by rfl) ⟨207828, by rfl⟩ : syracuseStep 2216837 = 415657) (by norm_num)
theorem B1774489 : Blo 1476558 1774489 := bbase (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) (by norm_num)
theorem B3322781 : Blo 1476558 3322781 := bbase (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) (by norm_num)
theorem B2216861 : Blo 1476558 2216861 := bbase (se 3 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 2216861 = 831323) (by norm_num)
theorem B4985765 : Blo 1476558 4985765 := bbase (se 4 (by rfl) ⟨467415, by rfl⟩ : syracuseStep 4985765 = 934831) (by norm_num)
theorem B2216885 : Blo 1476558 2216885 := bbase (se 5 (by rfl) ⟨103916, by rfl⟩ : syracuseStep 2216885 = 207833) (by norm_num)
theorem B1577917 : Blo 1476558 1577917 := bbase (se 3 (by rfl) ⟨295859, by rfl⟩ : syracuseStep 1577917 = 591719) (by norm_num)
theorem B2216909 : Blo 1476558 2216909 := bbase (se 3 (by rfl) ⟨415670, by rfl⟩ : syracuseStep 2216909 = 831341) (by norm_num)
theorem B2806741 : Blo 1476558 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B3322853 : Blo 1476558 3322853 := bbase (se 4 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 3322853 = 623035) (by norm_num)
theorem B2216933 : Blo 1476558 2216933 := bbase (se 4 (by rfl) ⟨207837, by rfl⟩ : syracuseStep 2216933 = 415675) (by norm_num)
theorem B3552245 : Blo 1476558 3552245 := bbase (se 5 (by rfl) ⟨166511, by rfl⟩ : syracuseStep 3552245 = 333023) (by norm_num)
theorem B2216957 : Blo 1476558 2216957 := bbase (se 3 (by rfl) ⟨415679, by rfl⟩ : syracuseStep 2216957 = 831359) (by norm_num)
theorem B7099397 : Blo 1476558 7099397 := bbase (se 4 (by rfl) ⟨665568, by rfl⟩ : syracuseStep 7099397 = 1331137) (by norm_num)
theorem B1577989 : Blo 1476558 1577989 := bbase (se 4 (by rfl) ⟨147936, by rfl⟩ : syracuseStep 1577989 = 295873) (by norm_num)
theorem B2995213 : Blo 1476558 2995213 := bbase (se 3 (by rfl) ⟨561602, by rfl⟩ : syracuseStep 2995213 = 1123205) (by norm_num)
theorem B1995797 : Blo 1476558 1995797 := bbase (se 6 (by rfl) ⟨46776, by rfl⟩ : syracuseStep 1995797 = 93553) (by norm_num)
theorem B2216981 : Blo 1476558 2216981 := bbase (se 6 (by rfl) ⟨51960, by rfl⟩ : syracuseStep 2216981 = 103921) (by norm_num)
theorem B3740701 : Blo 1476558 3740701 := bbase (se 3 (by rfl) ⟨701381, by rfl⟩ : syracuseStep 3740701 = 1402763) (by norm_num)
theorem B3322925 : Blo 1476558 3322925 := bbase (se 3 (by rfl) ⟨623048, by rfl⟩ : syracuseStep 3322925 = 1246097) (by norm_num)
theorem B2217005 : Blo 1476558 2217005 := bbase (se 3 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 2217005 = 831377) (by norm_num)
theorem B1774657 : Blo 1476558 1774657 := bbase (se 2 (by rfl) ⟨665496, by rfl⟩ : syracuseStep 1774657 = 1330993) (by norm_num)
theorem B1995845 : Blo 1476558 1995845 := bbase (se 4 (by rfl) ⟨187110, by rfl⟩ : syracuseStep 1995845 = 374221) (by norm_num)
theorem B2217029 : Blo 1476558 2217029 := bbase (se 4 (by rfl) ⟨207846, by rfl⟩ : syracuseStep 2217029 = 415693) (by norm_num)
theorem B8983637 : Blo 1476558 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B2217053 : Blo 1476558 2217053 := bbase (se 3 (by rfl) ⟨415697, by rfl⟩ : syracuseStep 2217053 = 831395) (by norm_num)
theorem B3322997 : Blo 1476558 3322997 := bbase (se 5 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 3322997 = 311531) (by norm_num)
theorem B2217077 : Blo 1476558 2217077 := bbase (se 5 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 2217077 = 207851) (by norm_num)
theorem B3740813 : Blo 1476558 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2217101 : Blo 1476558 2217101 := bbase (se 3 (by rfl) ⟨415706, by rfl⟩ : syracuseStep 2217101 = 831413) (by norm_num)
theorem B2217125 : Blo 1476558 2217125 := bbase (se 4 (by rfl) ⟨207855, by rfl⟩ : syracuseStep 2217125 = 415711) (by norm_num)
theorem B3552437 : Blo 1476558 3552437 := bbase (se 5 (by rfl) ⟨166520, by rfl⟩ : syracuseStep 3552437 = 333041) (by norm_num)
theorem B3323069 : Blo 1476558 3323069 := bbase (se 3 (by rfl) ⟨623075, by rfl⟩ : syracuseStep 3323069 = 1246151) (by norm_num)
theorem B2217149 : Blo 1476558 2217149 := bbase (se 3 (by rfl) ⟨415715, by rfl⟩ : syracuseStep 2217149 = 831431) (by norm_num)
theorem B2217173 : Blo 1476558 2217173 := bbase (se 7 (by rfl) ⟨25982, by rfl⟩ : syracuseStep 2217173 = 51965) (by norm_num)
theorem B2217197 : Blo 1476558 2217197 := bbase (se 3 (by rfl) ⟨415724, by rfl⟩ : syracuseStep 2217197 = 831449) (by norm_num)
theorem B9860341 : Blo 1476558 9860341 := bbase (se 5 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 9860341 = 924407) (by norm_num)
theorem B3323141 : Blo 1476558 3323141 := bbase (se 4 (by rfl) ⟨311544, by rfl⟩ : syracuseStep 3323141 = 623089) (by norm_num)
theorem B1774853 : Blo 1476558 1774853 := bbase (se 4 (by rfl) ⟨166392, by rfl⟩ : syracuseStep 1774853 = 332785) (by norm_num)
theorem B2217221 : Blo 1476558 2217221 := bbase (se 4 (by rfl) ⟨207864, by rfl⟩ : syracuseStep 2217221 = 415729) (by norm_num)
theorem B2217245 : Blo 1476558 2217245 := bbase (se 3 (by rfl) ⟨415733, by rfl⟩ : syracuseStep 2217245 = 831467) (by norm_num)
theorem B4207925 : Blo 1476558 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B2217269 : Blo 1476558 2217269 := bbase (se 5 (by rfl) ⟨103934, by rfl⟩ : syracuseStep 2217269 = 207869) (by norm_num)
theorem B3323213 : Blo 1476558 3323213 := bbase (se 3 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 3323213 = 1246205) (by norm_num)
theorem B3741005 : Blo 1476558 3741005 := bbase (se 3 (by rfl) ⟨701438, by rfl⟩ : syracuseStep 3741005 = 1402877) (by norm_num)
theorem B2217293 : Blo 1476558 2217293 := bbase (se 3 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 2217293 = 831485) (by norm_num)
theorem B4986197 : Blo 1476558 4986197 := bbase (se 14 (by rfl) ⟨456, by rfl⟩ : syracuseStep 4986197 = 913) (by norm_num)
theorem B2217317 : Blo 1476558 2217317 := bbase (se 4 (by rfl) ⟨207873, by rfl⟩ : syracuseStep 2217317 = 415747) (by norm_num)
theorem B5051765 : Blo 1476558 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1578361 : Blo 1476558 1578361 := bbase (se 2 (by rfl) ⟨591885, by rfl⟩ : syracuseStep 1578361 = 1183771) (by norm_num)
theorem B2217341 : Blo 1476558 2217341 := bbase (se 3 (by rfl) ⟨415751, by rfl⟩ : syracuseStep 2217341 = 831503) (by norm_num)
theorem B3323285 : Blo 1476558 3323285 := bbase (se 6 (by rfl) ⟨77889, by rfl⟩ : syracuseStep 3323285 = 155779) (by norm_num)
theorem B2217365 : Blo 1476558 2217365 := bbase (se 6 (by rfl) ⟨51969, by rfl⟩ : syracuseStep 2217365 = 103939) (by norm_num)
theorem B2217389 : Blo 1476558 2217389 := bbase (se 3 (by rfl) ⟨415760, by rfl⟩ : syracuseStep 2217389 = 831521) (by norm_num)
theorem B2217413 : Blo 1476558 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B7484885 : Blo 1476558 7484885 := bbase (se 7 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 7484885 = 175427) (by norm_num)
theorem B3323357 : Blo 1476558 3323357 := bbase (se 3 (by rfl) ⟨623129, by rfl⟩ : syracuseStep 3323357 = 1246259) (by norm_num)
theorem B2217437 : Blo 1476558 2217437 := bbase (se 3 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 2217437 = 831539) (by norm_num)
theorem B2217461 : Blo 1476558 2217461 := bbase (se 5 (by rfl) ⟨103943, by rfl⟩ : syracuseStep 2217461 = 207887) (by norm_num)
theorem B2217485 : Blo 1476558 2217485 := bbase (se 3 (by rfl) ⟨415778, by rfl⟩ : syracuseStep 2217485 = 831557) (by norm_num)
theorem B3323429 : Blo 1476558 3323429 := bbase (se 4 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 3323429 = 623143) (by norm_num)
theorem B2217509 : Blo 1476558 2217509 := bbase (se 4 (by rfl) ⟨207891, by rfl⟩ : syracuseStep 2217509 = 415783) (by norm_num)
theorem B1685053 : Blo 1476558 1685053 := bbase (se 3 (by rfl) ⟨315947, by rfl⟩ : syracuseStep 1685053 = 631895) (by norm_num)
theorem B2217533 : Blo 1476558 2217533 := bbase (se 3 (by rfl) ⟨415787, by rfl⟩ : syracuseStep 2217533 = 831575) (by norm_num)
theorem B2102869 : Blo 1476558 2102869 := bbase (se 8 (by rfl) ⟨12321, by rfl⟩ : syracuseStep 2102869 = 24643) (by norm_num)
theorem B2217557 : Blo 1476558 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B3995237 : Blo 1476558 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B3323501 : Blo 1476558 3323501 := bbase (se 3 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 3323501 = 1246313) (by norm_num)
theorem B2217581 : Blo 1476558 2217581 := bbase (se 3 (by rfl) ⟨415796, by rfl⟩ : syracuseStep 2217581 = 831593) (by norm_num)
theorem B2217605 : Blo 1476558 2217605 := bbase (se 4 (by rfl) ⟨207900, by rfl⟩ : syracuseStep 2217605 = 415801) (by norm_num)
theorem B2217629 : Blo 1476558 2217629 := bbase (se 3 (by rfl) ⟨415805, by rfl⟩ : syracuseStep 2217629 = 831611) (by norm_num)
theorem B3741349 : Blo 1476558 3741349 := bbase (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) (by norm_num)
theorem B3323573 : Blo 1476558 3323573 := bbase (se 5 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 3323573 = 311585) (by norm_num)
theorem B2217653 : Blo 1476558 2217653 := bbase (se 5 (by rfl) ⟨103952, by rfl⟩ : syracuseStep 2217653 = 207905) (by norm_num)
theorem B2217677 : Blo 1476558 2217677 := bbase (se 3 (by rfl) ⟨415814, by rfl⟩ : syracuseStep 2217677 = 831629) (by norm_num)
theorem B8410837 : Blo 1476558 8410837 := bbase (se 7 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 8410837 = 197129) (by norm_num)
theorem B2217701 : Blo 1476558 2217701 := bbase (se 4 (by rfl) ⟨207909, by rfl⟩ : syracuseStep 2217701 = 415819) (by norm_num)
theorem B1578737 : Blo 1476558 1578737 := bbase (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) (by norm_num)
theorem B4732661 : Blo 1476558 4732661 := bbase (se 5 (by rfl) ⟨221843, by rfl⟩ : syracuseStep 4732661 = 443687) (by norm_num)
theorem B3323645 : Blo 1476558 3323645 := bbase (se 3 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 3323645 = 1246367) (by norm_num)
theorem B2217725 : Blo 1476558 2217725 := bbase (se 3 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 2217725 = 831647) (by norm_num)
theorem B4986629 : Blo 1476558 4986629 := bbase (se 4 (by rfl) ⟨467496, by rfl⟩ : syracuseStep 4986629 = 934993) (by norm_num)
theorem B6313733 : Blo 1476558 6313733 := bbase (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) (by norm_num)
theorem B3741461 : Blo 1476558 3741461 := bbase (se 6 (by rfl) ⟨87690, by rfl⟩ : syracuseStep 3741461 = 175381) (by norm_num)
theorem B2217749 : Blo 1476558 2217749 := bbase (se 6 (by rfl) ⟨51978, by rfl⟩ : syracuseStep 2217749 = 103957) (by norm_num)
theorem B2217773 : Blo 1476558 2217773 := bbase (se 3 (by rfl) ⟨415832, by rfl⟩ : syracuseStep 2217773 = 831665) (by norm_num)
theorem B1578809 : Blo 1476558 1578809 := bbase (se 2 (by rfl) ⟨592053, by rfl⟩ : syracuseStep 1578809 = 1184107) (by norm_num)
theorem B3323717 : Blo 1476558 3323717 := bbase (se 4 (by rfl) ⟨311598, by rfl⟩ : syracuseStep 3323717 = 623197) (by norm_num)
theorem B2217797 : Blo 1476558 2217797 := bbase (se 4 (by rfl) ⟨207918, by rfl⟩ : syracuseStep 2217797 = 415837) (by norm_num)
theorem B2217821 : Blo 1476558 2217821 := bbase (se 3 (by rfl) ⟨415841, by rfl⟩ : syracuseStep 2217821 = 831683) (by norm_num)
theorem B7477109 : Blo 1476558 7477109 := bbase (se 5 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 7477109 = 700979) (by norm_num)
theorem B4732789 : Blo 1476558 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B3413885 : Blo 1476558 3413885 := bbase (se 3 (by rfl) ⟨640103, by rfl⟩ : syracuseStep 3413885 = 1280207) (by norm_num)
theorem B3323789 : Blo 1476558 3323789 := bbase (se 3 (by rfl) ⟨623210, by rfl⟩ : syracuseStep 3323789 = 1246421) (by norm_num)
theorem B2365357 : Blo 1476558 2365357 := bbase (se 3 (by rfl) ⟨443504, by rfl⟩ : syracuseStep 2365357 = 887009) (by norm_num)
theorem B3323861 : Blo 1476558 3323861 := bbase (se 7 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 3323861 = 77903) (by norm_num)
theorem B3741653 : Blo 1476558 3741653 := bbase (se 7 (by rfl) ⟨43847, by rfl⟩ : syracuseStep 3741653 = 87695) (by norm_num)
theorem B3323933 : Blo 1476558 3323933 := bbase (se 3 (by rfl) ⟨623237, by rfl⟩ : syracuseStep 3323933 = 1246475) (by norm_num)
theorem B3324005 : Blo 1476558 3324005 := bbase (se 4 (by rfl) ⟨311625, by rfl⟩ : syracuseStep 3324005 = 623251) (by norm_num)
theorem B4733045 : Blo 1476558 4733045 := bbase (se 5 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 4733045 = 443723) (by norm_num)
theorem B2365613 : Blo 1476558 2365613 := bbase (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) (by norm_num)
theorem B3324077 : Blo 1476558 3324077 := bbase (se 3 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 3324077 = 1246529) (by norm_num)
theorem B2463925 : Blo 1476558 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B4987061 : Blo 1476558 4987061 := bbase (se 5 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 4987061 = 467537) (by norm_num)
theorem B1685729 : Blo 1476558 1685729 := bbase (se 2 (by rfl) ⟨632148, by rfl⟩ : syracuseStep 1685729 = 1264297) (by norm_num)
theorem B1661161 : Blo 1476558 1661161 := bbase (se 2 (by rfl) ⟨622935, by rfl⟩ : syracuseStep 1661161 = 1245871) (by norm_num)
theorem B3324149 : Blo 1476558 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B1661197 : Blo 1476558 1661197 := bbase (se 3 (by rfl) ⟨311474, by rfl⟩ : syracuseStep 1661197 = 622949) (by norm_num)
theorem B3741997 : Blo 1476558 3741997 := bbase (se 3 (by rfl) ⟨701624, by rfl⟩ : syracuseStep 3741997 = 1403249) (by norm_num)
theorem B1661233 : Blo 1476558 1661233 := bbase (se 2 (by rfl) ⟨622962, by rfl⟩ : syracuseStep 1661233 = 1245925) (by norm_num)
theorem B3324221 : Blo 1476558 3324221 := bbase (se 3 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 3324221 = 1246583) (by norm_num)
theorem B1661269 : Blo 1476558 1661269 := bbase (se 10 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 1661269 = 4867) (by norm_num)
theorem B2103661 : Blo 1476558 2103661 := bbase (se 3 (by rfl) ⟨394436, by rfl⟩ : syracuseStep 2103661 = 788873) (by norm_num)
theorem B1849717 : Blo 1476558 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B1661305 : Blo 1476558 1661305 := bbase (se 2 (by rfl) ⟨622989, by rfl⟩ : syracuseStep 1661305 = 1245979) (by norm_num)
theorem B3324293 : Blo 1476558 3324293 := bbase (se 4 (by rfl) ⟨311652, by rfl⟩ : syracuseStep 3324293 = 623305) (by norm_num)
theorem B1661341 : Blo 1476558 1661341 := bbase (se 3 (by rfl) ⟨311501, by rfl⟩ : syracuseStep 1661341 = 623003) (by norm_num)
theorem B3742109 : Blo 1476558 3742109 := bbase (se 3 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 3742109 = 1403291) (by norm_num)
theorem B1661377 : Blo 1476558 1661377 := bbase (se 2 (by rfl) ⟨623016, by rfl⟩ : syracuseStep 1661377 = 1246033) (by norm_num)
theorem B3324365 : Blo 1476558 3324365 := bbase (se 3 (by rfl) ⟨623318, by rfl⟩ : syracuseStep 3324365 = 1246637) (by norm_num)
theorem B1661413 : Blo 1476558 1661413 := bbase (se 4 (by rfl) ⟨155757, by rfl⟩ : syracuseStep 1661413 = 311515) (by norm_num)
theorem B1661449 : Blo 1476558 1661449 := bbase (se 2 (by rfl) ⟨623043, by rfl⟩ : syracuseStep 1661449 = 1246087) (by norm_num)
theorem B3324437 : Blo 1476558 3324437 := bbase (se 6 (by rfl) ⟨77916, by rfl⟩ : syracuseStep 3324437 = 155833) (by norm_num)
theorem B5610005 : Blo 1476558 5610005 := bbase (se 6 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 5610005 = 262969) (by norm_num)
theorem B1661485 : Blo 1476558 1661485 := bbase (se 3 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 1661485 = 623057) (by norm_num)
theorem B1661521 : Blo 1476558 1661521 := bbase (se 2 (by rfl) ⟨623070, by rfl⟩ : syracuseStep 1661521 = 1246141) (by norm_num)
theorem B2398805 : Blo 1476558 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B3324509 : Blo 1476558 3324509 := bbase (se 3 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 3324509 = 1246691) (by norm_num)
theorem B3742301 : Blo 1476558 3742301 := bbase (se 3 (by rfl) ⟨701681, by rfl⟩ : syracuseStep 3742301 = 1403363) (by norm_num)
theorem B4987493 : Blo 1476558 4987493 := bbase (se 4 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 4987493 = 935155) (by norm_num)
theorem B1661557 : Blo 1476558 1661557 := bbase (se 5 (by rfl) ⟨77885, by rfl⟩ : syracuseStep 1661557 = 155771) (by norm_num)
theorem B1661593 : Blo 1476558 1661593 := bbase (se 2 (by rfl) ⟨623097, by rfl⟩ : syracuseStep 1661593 = 1246195) (by norm_num)
theorem B3324581 : Blo 1476558 3324581 := bbase (se 4 (by rfl) ⟨311679, by rfl⟩ : syracuseStep 3324581 = 623359) (by norm_num)
theorem B1661629 : Blo 1476558 1661629 := bbase (se 3 (by rfl) ⟨311555, by rfl⟩ : syracuseStep 1661629 = 623111) (by norm_num)
theorem B2103997 : Blo 1476558 2103997 := bbase (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) (by norm_num)
theorem B1661665 : Blo 1476558 1661665 := bbase (se 2 (by rfl) ⟨623124, by rfl⟩ : syracuseStep 1661665 = 1246249) (by norm_num)
theorem B3324653 : Blo 1476558 3324653 := bbase (se 3 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 3324653 = 1246745) (by norm_num)
theorem B1661701 : Blo 1476558 1661701 := bbase (se 4 (by rfl) ⟨155784, by rfl⟩ : syracuseStep 1661701 = 311569) (by norm_num)
theorem B1661737 : Blo 1476558 1661737 := bbase (se 2 (by rfl) ⟨623151, by rfl⟩ : syracuseStep 1661737 = 1246303) (by norm_num)
theorem B5610293 : Blo 1476558 5610293 := bbase (se 5 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 5610293 = 525965) (by norm_num)
theorem B3324725 : Blo 1476558 3324725 := bbase (se 5 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 3324725 = 311693) (by norm_num)
theorem B1661773 : Blo 1476558 1661773 := bbase (se 3 (by rfl) ⟨311582, by rfl⟩ : syracuseStep 1661773 = 623165) (by norm_num)
theorem B4209509 : Blo 1476558 4209509 := bbase (se 4 (by rfl) ⟨394641, by rfl⟩ : syracuseStep 4209509 = 789283) (by norm_num)
theorem B2366317 : Blo 1476558 2366317 := bbase (se 3 (by rfl) ⟨443684, by rfl⟩ : syracuseStep 2366317 = 887369) (by norm_num)
theorem B1661809 : Blo 1476558 1661809 := bbase (se 2 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 1661809 = 1246357) (by norm_num)
theorem B2997109 : Blo 1476558 2997109 := bbase (se 5 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 2997109 = 280979) (by norm_num)
theorem B3324797 : Blo 1476558 3324797 := bbase (se 3 (by rfl) ⟨623399, by rfl⟩ : syracuseStep 3324797 = 1246799) (by norm_num)
theorem B1661845 : Blo 1476558 1661845 := bbase (se 6 (by rfl) ⟨38949, by rfl⟩ : syracuseStep 1661845 = 77899) (by norm_num)
theorem B2104213 : Blo 1476558 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B1661881 : Blo 1476558 1661881 := bbase (se 2 (by rfl) ⟨623205, by rfl⟩ : syracuseStep 1661881 = 1246411) (by norm_num)
theorem B3324869 : Blo 1476558 3324869 := bbase (se 4 (by rfl) ⟨311706, by rfl⟩ : syracuseStep 3324869 = 623413) (by norm_num)
theorem B11369429 : Blo 1476558 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B1661917 : Blo 1476558 1661917 := bbase (se 3 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 1661917 = 623219) (by norm_num)
theorem B1661953 : Blo 1476558 1661953 := bbase (se 2 (by rfl) ⟨623232, by rfl⟩ : syracuseStep 1661953 = 1246465) (by norm_num)
theorem B3324941 : Blo 1476558 3324941 := bbase (se 3 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 3324941 = 1246853) (by norm_num)
theorem B8526869 : Blo 1476558 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B4987925 : Blo 1476558 4987925 := bbase (se 6 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 4987925 = 233809) (by norm_num)
theorem B1661989 : Blo 1476558 1661989 := bbase (se 4 (by rfl) ⟨155811, by rfl⟩ : syracuseStep 1661989 = 311623) (by norm_num)
theorem B1498157 : Blo 1476558 1498157 := bbase (se 3 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 1498157 = 561809) (by norm_num)
theorem B1662025 : Blo 1476558 1662025 := bbase (se 2 (by rfl) ⟨623259, by rfl⟩ : syracuseStep 1662025 = 1246519) (by norm_num)
theorem B3325013 : Blo 1476558 3325013 := bbase (se 8 (by rfl) ⟨19482, by rfl⟩ : syracuseStep 3325013 = 38965) (by norm_num)
theorem B1662061 : Blo 1476558 1662061 := bbase (se 3 (by rfl) ⟨311636, by rfl⟩ : syracuseStep 1662061 = 623273) (by norm_num)
theorem B2399357 : Blo 1476558 2399357 := bbase (se 3 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 2399357 = 899759) (by norm_num)
theorem B7478405 : Blo 1476558 7478405 := bbase (se 4 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 7478405 = 1402201) (by norm_num)
theorem B1662097 : Blo 1476558 1662097 := bbase (se 2 (by rfl) ⟨623286, by rfl⟩ : syracuseStep 1662097 = 1246573) (by norm_num)
theorem B3325085 : Blo 1476558 3325085 := bbase (se 3 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 3325085 = 1246907) (by norm_num)
theorem B1662133 : Blo 1476558 1662133 := bbase (se 5 (by rfl) ⟨77912, by rfl⟩ : syracuseStep 1662133 = 155825) (by norm_num)
theorem B2399429 : Blo 1476558 2399429 := bbase (se 4 (by rfl) ⟨224946, by rfl⟩ : syracuseStep 2399429 = 449893) (by norm_num)
theorem B1662169 : Blo 1476558 1662169 := bbase (se 2 (by rfl) ⟨623313, by rfl⟩ : syracuseStep 1662169 = 1246627) (by norm_num)
theorem B3325157 : Blo 1476558 3325157 := bbase (se 4 (by rfl) ⟨311733, by rfl⟩ : syracuseStep 3325157 = 623467) (by norm_num)
theorem B1662205 : Blo 1476558 1662205 := bbase (se 3 (by rfl) ⟨311663, by rfl⟩ : syracuseStep 1662205 = 623327) (by norm_num)
theorem B2104589 : Blo 1476558 2104589 := bbase (se 3 (by rfl) ⟨394610, by rfl⟩ : syracuseStep 2104589 = 789221) (by norm_num)
theorem B2366741 : Blo 1476558 2366741 := bbase (se 6 (by rfl) ⟨55470, by rfl⟩ : syracuseStep 2366741 = 110941) (by norm_num)
theorem B1662241 : Blo 1476558 1662241 := bbase (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) (by norm_num)
theorem B3325229 : Blo 1476558 3325229 := bbase (se 3 (by rfl) ⟨623480, by rfl⟩ : syracuseStep 3325229 = 1246961) (by norm_num)
theorem B1662277 : Blo 1476558 1662277 := bbase (se 4 (by rfl) ⟨155838, by rfl⟩ : syracuseStep 1662277 = 311677) (by norm_num)
theorem B27344213 : Blo 1476558 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B1662313 : Blo 1476558 1662313 := bbase (se 2 (by rfl) ⟨623367, by rfl⟩ : syracuseStep 1662313 = 1246735) (by norm_num)
theorem B8985973 : Blo 1476558 8985973 := bbase (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) (by norm_num)
theorem B3325301 : Blo 1476558 3325301 := bbase (se 5 (by rfl) ⟨155873, by rfl⟩ : syracuseStep 3325301 = 311747) (by norm_num)
theorem B1662349 : Blo 1476558 1662349 := bbase (se 3 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 1662349 = 623381) (by norm_num)
theorem B1662385 : Blo 1476558 1662385 := bbase (se 2 (by rfl) ⟨623394, by rfl⟩ : syracuseStep 1662385 = 1246789) (by norm_num)
theorem B3325373 : Blo 1476558 3325373 := bbase (se 3 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 3325373 = 1247015) (by norm_num)
theorem B4988357 : Blo 1476558 4988357 := bbase (se 4 (by rfl) ⟨467658, by rfl⟩ : syracuseStep 4988357 = 935317) (by norm_num)
theorem B1662421 : Blo 1476558 1662421 := bbase (se 7 (by rfl) ⟨19481, by rfl⟩ : syracuseStep 1662421 = 38963) (by norm_num)
theorem B6315509 : Blo 1476558 6315509 := bbase (se 5 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 6315509 = 592079) (by norm_num)
theorem B1662457 : Blo 1476558 1662457 := bbase (se 2 (by rfl) ⟨623421, by rfl⟩ : syracuseStep 1662457 = 1246843) (by norm_num)
theorem B4554245 : Blo 1476558 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B3325445 : Blo 1476558 3325445 := bbase (se 4 (by rfl) ⟨311760, by rfl⟩ : syracuseStep 3325445 = 623521) (by norm_num)
theorem B4210181 : Blo 1476558 4210181 := bbase (se 4 (by rfl) ⟨394704, by rfl⟩ : syracuseStep 4210181 = 789409) (by norm_num)
theorem B1662493 : Blo 1476558 1662493 := bbase (se 3 (by rfl) ⟨311717, by rfl⟩ : syracuseStep 1662493 = 623435) (by norm_num)
theorem B2367029 : Blo 1476558 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1662529 : Blo 1476558 1662529 := bbase (se 2 (by rfl) ⟨623448, by rfl⟩ : syracuseStep 1662529 = 1246897) (by norm_num)
theorem B3325517 : Blo 1476558 3325517 := bbase (se 3 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 3325517 = 1247069) (by norm_num)
theorem B6307429 : Blo 1476558 6307429 := bbase (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) (by norm_num)
theorem B1662565 : Blo 1476558 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B6307445 : Blo 1476558 6307445 := bbase (se 5 (by rfl) ⟨295661, by rfl⟩ : syracuseStep 6307445 = 591323) (by norm_num)
theorem B2662021 : Blo 1476558 2662021 := bbase (se 4 (by rfl) ⟨249564, by rfl⟩ : syracuseStep 2662021 = 499129) (by norm_num)
theorem B1662601 : Blo 1476558 1662601 := bbase (se 2 (by rfl) ⟨623475, by rfl⟩ : syracuseStep 1662601 = 1246951) (by norm_num)
theorem B5987989 : Blo 1476558 5987989 := bbase (se 6 (by rfl) ⟨140343, by rfl⟩ : syracuseStep 5987989 = 280687) (by norm_num)
theorem B8412821 : Blo 1476558 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B3325589 : Blo 1476558 3325589 := bbase (se 6 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 3325589 = 155887) (by norm_num)
theorem B1662637 : Blo 1476558 1662637 := bbase (se 3 (by rfl) ⟨311744, by rfl⟩ : syracuseStep 1662637 = 623489) (by norm_num)
theorem B1662673 : Blo 1476558 1662673 := bbase (se 2 (by rfl) ⟨623502, by rfl⟩ : syracuseStep 1662673 = 1247005) (by norm_num)
theorem B3325661 : Blo 1476558 3325661 := bbase (se 3 (by rfl) ⟨623561, by rfl⟩ : syracuseStep 3325661 = 1247123) (by norm_num)
theorem B7577317 : Blo 1476558 7577317 := bbase (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) (by norm_num)
theorem B7102181 : Blo 1476558 7102181 := bbase (se 4 (by rfl) ⟨665829, by rfl⟩ : syracuseStep 7102181 = 1331659) (by norm_num)
theorem B1662709 : Blo 1476558 1662709 := bbase (se 5 (by rfl) ⟨77939, by rfl⟩ : syracuseStep 1662709 = 155879) (by norm_num)
theorem B2367253 : Blo 1476558 2367253 := bbase (se 6 (by rfl) ⟨55482, by rfl⟩ : syracuseStep 2367253 = 110965) (by norm_num)
theorem B1662745 : Blo 1476558 1662745 := bbase (se 2 (by rfl) ⟨623529, by rfl⟩ : syracuseStep 1662745 = 1247059) (by norm_num)
theorem B3325733 : Blo 1476558 3325733 := bbase (se 4 (by rfl) ⟨311787, by rfl⟩ : syracuseStep 3325733 = 623575) (by norm_num)
theorem B1662781 : Blo 1476558 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B28417877 : Blo 1476558 28417877 := bbase (se 9 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 28417877 = 166511) (by norm_num)
theorem B3153757 : Blo 1476558 3153757 := bbase (se 3 (by rfl) ⟨591329, by rfl⟩ : syracuseStep 3153757 = 1182659) (by norm_num)
theorem B2662237 : Blo 1476558 2662237 := bbase (se 3 (by rfl) ⟨499169, by rfl⟩ : syracuseStep 2662237 = 998339) (by norm_num)
theorem B1662817 : Blo 1476558 1662817 := bbase (se 2 (by rfl) ⟨623556, by rfl⟩ : syracuseStep 1662817 = 1247113) (by norm_num)
theorem B3325805 : Blo 1476558 3325805 := bbase (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) (by norm_num)
theorem B4988789 : Blo 1476558 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B1662853 : Blo 1476558 1662853 := bbase (se 4 (by rfl) ⟨155892, by rfl⟩ : syracuseStep 1662853 = 311785) (by norm_num)
theorem B1662889 : Blo 1476558 1662889 := bbase (se 2 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 1662889 = 1247167) (by norm_num)
theorem B3325877 : Blo 1476558 3325877 := bbase (se 5 (by rfl) ⟨155900, by rfl⟩ : syracuseStep 3325877 = 311801) (by norm_num)
theorem B1662925 : Blo 1476558 1662925 := bbase (se 3 (by rfl) ⟨311798, by rfl⟩ : syracuseStep 1662925 = 623597) (by norm_num)
theorem B5611477 : Blo 1476558 5611477 := bbase (se 7 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 5611477 = 131519) (by norm_num)
theorem B1662961 : Blo 1476558 1662961 := bbase (se 2 (by rfl) ⟨623610, by rfl⟩ : syracuseStep 1662961 = 1247221) (by norm_num)
theorem B3325949 : Blo 1476558 3325949 := bbase (se 3 (by rfl) ⟨623615, by rfl⟩ : syracuseStep 3325949 = 1247231) (by norm_num)
theorem B1662979 : Blo 1476558 1662979 := bstep (se 1 (by rfl) ⟨1247234, by rfl⟩ : syracuseStep 1662979 = 2494469) B2494469
theorem B9601037 : Blo 1476558 9601037 := bstep (se 3 (by rfl) ⟨1800194, by rfl⟩ : syracuseStep 9601037 = 3600389) B3600389
theorem B18931765 : Blo 1476558 18931765 := bstep (se 5 (by rfl) ⟨887426, by rfl⟩ : syracuseStep 18931765 = 1774853) B1774853
theorem B8413253 : Blo 1476558 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B4989005 : Blo 1476558 4989005 := bstep (se 3 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 4989005 = 1870877) B1870877
theorem B4989059 : Blo 1476558 4989059 := bstep (se 1 (by rfl) ⟨3741794, by rfl⟩ : syracuseStep 4989059 = 7483589) B7483589
theorem B1663123 : Blo 1476558 1663123 := bstep (se 1 (by rfl) ⟨1247342, by rfl⟩ : syracuseStep 1663123 = 2494685) B2494685
theorem B3326129 : Blo 1476558 3326129 := bstep (se 2 (by rfl) ⟨1247298, by rfl⟩ : syracuseStep 3326129 = 2494597) B2494597
theorem B3326147 : Blo 1476558 3326147 := bstep (se 1 (by rfl) ⟨2494610, by rfl⟩ : syracuseStep 3326147 = 4989221) B4989221
theorem B3285233 : Blo 1476558 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B1663267 : Blo 1476558 1663267 := bstep (se 1 (by rfl) ⟨1247450, by rfl⟩ : syracuseStep 1663267 = 2494901) B2494901
theorem B8986949 : Blo 1476558 8986949 := bstep (se 4 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 8986949 = 1685053) B1685053
theorem B4989329 : Blo 1476558 4989329 := bstep (se 2 (by rfl) ⟨1870998, by rfl⟩ : syracuseStep 4989329 = 3741997) B3741997
theorem B3326417 : Blo 1476558 3326417 := bstep (se 2 (by rfl) ⟨1247406, by rfl⟩ : syracuseStep 3326417 = 2494813) B2494813
theorem B2367971 : Blo 1476558 2367971 := bstep (se 1 (by rfl) ⟨1775978, by rfl⟩ : syracuseStep 2367971 = 3551957) B3551957
theorem B3326435 : Blo 1476558 3326435 := bstep (se 1 (by rfl) ⟨2494826, by rfl⟩ : syracuseStep 3326435 = 4989653) B4989653
theorem B2466289 : Blo 1476558 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B4735505 : Blo 1476558 4735505 := bstep (se 2 (by rfl) ⟨1775814, by rfl⟩ : syracuseStep 4735505 = 3551629) B3551629
theorem B6308387 : Blo 1476558 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B2368163 : Blo 1476558 2368163 := bstep (se 1 (by rfl) ⟨1776122, by rfl⟩ : syracuseStep 2368163 = 3552245) B3552245
theorem B5612237 : Blo 1476558 5612237 := bstep (se 3 (by rfl) ⟨1052294, by rfl⟩ : syracuseStep 5612237 = 2104589) B2104589
theorem B5989091 : Blo 1476558 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B3326705 : Blo 1476558 3326705 := bstep (se 2 (by rfl) ⟨1247514, by rfl⟩ : syracuseStep 3326705 = 2495029) B2495029
theorem B3326723 : Blo 1476558 3326723 := bstep (se 1 (by rfl) ⟨2495042, by rfl⟩ : syracuseStep 3326723 = 4990085) B4990085
theorem B2368291 : Blo 1476558 2368291 := bstep (se 1 (by rfl) ⟨1776218, by rfl⟩ : syracuseStep 2368291 = 3552437) B3552437
theorem B4989869 : Blo 1476558 4989869 := bstep (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) B1871201
theorem B5686193 : Blo 1476558 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B16835525 : Blo 1476558 16835525 := bstep (se 4 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 16835525 = 3156661) B3156661
theorem B1868771 : Blo 1476558 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B4989923 : Blo 1476558 4989923 := bstep (se 1 (by rfl) ⟨3742442, by rfl⟩ : syracuseStep 4989923 = 7484885) B7484885
theorem B2245619 : Blo 1476558 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B4736017 : Blo 1476558 4736017 := bstep (se 2 (by rfl) ⟨1776006, by rfl⟩ : syracuseStep 4736017 = 3552013) B3552013
theorem B2663491 : Blo 1476558 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B3368081 : Blo 1476558 3368081 := bstep (se 2 (by rfl) ⟨1263030, by rfl⟩ : syracuseStep 3368081 = 2526061) B2526061
theorem B3155107 : Blo 1476558 3155107 := bstep (se 1 (by rfl) ⟨2366330, by rfl⟩ : syracuseStep 3155107 = 4732661) B4732661
theorem B10650851 : Blo 1476558 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B2491715 : Blo 1476558 2491715 := bstep (se 1 (by rfl) ⟨1868786, by rfl⟩ : syracuseStep 2491715 = 3737573) B3737573
theorem B3155363 : Blo 1476558 3155363 := bstep (se 1 (by rfl) ⟨2366522, by rfl⟩ : syracuseStep 3155363 = 4733045) B4733045
theorem B2491843 : Blo 1476558 2491843 := bstep (se 1 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 2491843 = 3737765) B3737765
theorem B2491985 : Blo 1476558 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B1869475 : Blo 1476558 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B2492113 : Blo 1476558 2492113 := bstep (se 2 (by rfl) ⟨934542, by rfl⟩ : syracuseStep 2492113 = 1869085) B1869085
theorem B8095459 : Blo 1476558 8095459 := bstep (se 1 (by rfl) ⟨6071594, by rfl⟩ : syracuseStep 8095459 = 12143189) B12143189
theorem B1599203 : Blo 1476558 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B2492147 : Blo 1476558 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B3196675 : Blo 1476558 3196675 := bstep (se 1 (by rfl) ⟨2397506, by rfl⟩ : syracuseStep 3196675 = 4795013) B4795013
theorem B1869571 : Blo 1476558 1869571 := bstep (se 1 (by rfl) ⟨1402178, by rfl⟩ : syracuseStep 1869571 = 2804357) B2804357
theorem B14198597 : Blo 1476558 14198597 := bstep (se 4 (by rfl) ⟨1331118, by rfl⟩ : syracuseStep 14198597 = 2662237) B2662237
theorem B2492275 : Blo 1476558 2492275 := bstep (se 1 (by rfl) ⟨1869206, by rfl⟩ : syracuseStep 2492275 = 3738413) B3738413
theorem B1476563 : Blo 1476558 1476563 := bstep (se 1 (by rfl) ⟨1107422, by rfl⟩ : syracuseStep 1476563 = 2214845) B2214845
theorem B1476579 : Blo 1476558 1476579 := bstep (se 1 (by rfl) ⟨1107434, by rfl⟩ : syracuseStep 1476579 = 2214869) B2214869
theorem B7579619 : Blo 1476558 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B1476595 : Blo 1476558 1476595 := bstep (se 1 (by rfl) ⟨1107446, by rfl⟩ : syracuseStep 1476595 = 2214893) B2214893
theorem B2492417 : Blo 1476558 2492417 := bstep (se 2 (by rfl) ⟨934656, by rfl⟩ : syracuseStep 2492417 = 1869313) B1869313
theorem B3737603 : Blo 1476558 3737603 := bstep (se 1 (by rfl) ⟨2803202, by rfl⟩ : syracuseStep 3737603 = 5606405) B5606405
theorem B1476611 : Blo 1476558 1476611 := bstep (se 1 (by rfl) ⟨1107458, by rfl⟩ : syracuseStep 1476611 = 2214917) B2214917
theorem B1476627 : Blo 1476558 1476627 := bstep (se 1 (by rfl) ⟨1107470, by rfl⟩ : syracuseStep 1476627 = 2214941) B2214941
theorem B1476643 : Blo 1476558 1476643 := bstep (se 1 (by rfl) ⟨1107482, by rfl⟩ : syracuseStep 1476643 = 2214965) B2214965
theorem B1476659 : Blo 1476558 1476659 := bstep (se 1 (by rfl) ⟨1107494, by rfl⟩ : syracuseStep 1476659 = 2214989) B2214989
theorem B1476675 : Blo 1476558 1476675 := bstep (se 1 (by rfl) ⟨1107506, by rfl⟩ : syracuseStep 1476675 = 2215013) B2215013
theorem B1476691 : Blo 1476558 1476691 := bstep (se 1 (by rfl) ⟨1107518, by rfl⟩ : syracuseStep 1476691 = 2215037) B2215037
theorem B1599571 : Blo 1476558 1599571 := bstep (se 1 (by rfl) ⟨1199678, by rfl⟩ : syracuseStep 1599571 = 2399357) B2399357
theorem B1476707 : Blo 1476558 1476707 := bstep (se 1 (by rfl) ⟨1107530, by rfl⟩ : syracuseStep 1476707 = 2215061) B2215061
theorem B2803825 : Blo 1476558 2803825 := bstep (se 2 (by rfl) ⟨1051434, by rfl⟩ : syracuseStep 2803825 = 2102869) B2102869
theorem B1476723 : Blo 1476558 1476723 := bstep (se 1 (by rfl) ⟨1107542, by rfl⟩ : syracuseStep 1476723 = 2215085) B2215085
theorem B2492545 : Blo 1476558 2492545 := bstep (se 2 (by rfl) ⟨934704, by rfl⟩ : syracuseStep 2492545 = 1869409) B1869409
theorem B1476739 : Blo 1476558 1476739 := bstep (se 1 (by rfl) ⟨1107554, by rfl⟩ : syracuseStep 1476739 = 2215109) B2215109
theorem B1599619 : Blo 1476558 1599619 := bstep (se 1 (by rfl) ⟨1199714, by rfl⟩ : syracuseStep 1599619 = 2399429) B2399429
theorem B1476755 : Blo 1476558 1476755 := bstep (se 1 (by rfl) ⟨1107566, by rfl⟩ : syracuseStep 1476755 = 2215133) B2215133
theorem B1476771 : Blo 1476558 1476771 := bstep (se 1 (by rfl) ⟨1107578, by rfl⟩ : syracuseStep 1476771 = 2215157) B2215157
theorem B2492579 : Blo 1476558 2492579 := bstep (se 1 (by rfl) ⟨1869434, by rfl⟩ : syracuseStep 2492579 = 3738869) B3738869
theorem B3549361 : Blo 1476558 3549361 := bstep (se 2 (by rfl) ⟨1331010, by rfl⟩ : syracuseStep 3549361 = 2662021) B2662021
theorem B1476787 : Blo 1476558 1476787 := bstep (se 1 (by rfl) ⟨1107590, by rfl⟩ : syracuseStep 1476787 = 2215181) B2215181
theorem B1476803 : Blo 1476558 1476803 := bstep (se 1 (by rfl) ⟨1107602, by rfl⟩ : syracuseStep 1476803 = 2215205) B2215205
theorem B25233605 : Blo 1476558 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B1476819 : Blo 1476558 1476819 := bstep (se 1 (by rfl) ⟨1107614, by rfl⟩ : syracuseStep 1476819 = 2215229) B2215229
theorem B1476835 : Blo 1476558 1476835 := bstep (se 1 (by rfl) ⟨1107626, by rfl⟩ : syracuseStep 1476835 = 2215253) B2215253
theorem B18229475 : Blo 1476558 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B4204781 : Blo 1476558 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B1476851 : Blo 1476558 1476851 := bstep (se 1 (by rfl) ⟨1107638, by rfl⟩ : syracuseStep 1476851 = 2215277) B2215277
theorem B1870067 : Blo 1476558 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1476867 : Blo 1476558 1476867 := bstep (se 1 (by rfl) ⟨1107650, by rfl⟩ : syracuseStep 1476867 = 2215301) B2215301
theorem B1476883 : Blo 1476558 1476883 := bstep (se 1 (by rfl) ⟨1107662, by rfl⟩ : syracuseStep 1476883 = 2215325) B2215325
theorem B1476899 : Blo 1476558 1476899 := bstep (se 1 (by rfl) ⟨1107674, by rfl⟩ : syracuseStep 1476899 = 2215349) B2215349
theorem B2492707 : Blo 1476558 2492707 := bstep (se 1 (by rfl) ⟨1869530, by rfl⟩ : syracuseStep 2492707 = 3739061) B3739061
theorem B10103089 : Blo 1476558 10103089 := bstep (se 2 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 10103089 = 7577317) B7577317
theorem B1476915 : Blo 1476558 1476915 := bstep (se 1 (by rfl) ⟨1107686, by rfl⟩ : syracuseStep 1476915 = 2215373) B2215373
theorem B1476931 : Blo 1476558 1476931 := bstep (se 1 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 1476931 = 2215397) B2215397
theorem B9103693 : Blo 1476558 9103693 := bstep (se 3 (by rfl) ⟨1706942, by rfl⟩ : syracuseStep 9103693 = 3413885) B3413885
theorem B9464141 : Blo 1476558 9464141 := bstep (se 3 (by rfl) ⟨1774526, by rfl⟩ : syracuseStep 9464141 = 3549053) B3549053
theorem B1476947 : Blo 1476558 1476947 := bstep (se 1 (by rfl) ⟨1107710, by rfl⟩ : syracuseStep 1476947 = 2215421) B2215421
theorem B1476963 : Blo 1476558 1476963 := bstep (se 1 (by rfl) ⟨1107722, by rfl⟩ : syracuseStep 1476963 = 2215445) B2215445
theorem B3156337 : Blo 1476558 3156337 := bstep (se 2 (by rfl) ⟨1183626, by rfl⟩ : syracuseStep 3156337 = 2367253) B2367253
theorem B1476979 : Blo 1476558 1476979 := bstep (se 1 (by rfl) ⟨1107734, by rfl⟩ : syracuseStep 1476979 = 2215469) B2215469
theorem B1476995 : Blo 1476558 1476995 := bstep (se 1 (by rfl) ⟨1107746, by rfl⟩ : syracuseStep 1476995 = 2215493) B2215493
theorem B1477011 : Blo 1476558 1477011 := bstep (se 1 (by rfl) ⟨1107758, by rfl⟩ : syracuseStep 1477011 = 2215517) B2215517
theorem B4204963 : Blo 1476558 4204963 := bstep (se 1 (by rfl) ⟨3153722, by rfl⟩ : syracuseStep 4204963 = 6307445) B6307445
theorem B1477027 : Blo 1476558 1477027 := bstep (se 1 (by rfl) ⟨1107770, by rfl⟩ : syracuseStep 1477027 = 2215541) B2215541
theorem B2492849 : Blo 1476558 2492849 := bstep (se 2 (by rfl) ⟨934818, by rfl⟩ : syracuseStep 2492849 = 1869637) B1869637
theorem B1477043 : Blo 1476558 1477043 := bstep (se 1 (by rfl) ⟨1107782, by rfl⟩ : syracuseStep 1477043 = 2215565) B2215565
theorem B1477059 : Blo 1476558 1477059 := bstep (se 1 (by rfl) ⟨1107794, by rfl⟩ : syracuseStep 1477059 = 2215589) B2215589
theorem B4205009 : Blo 1476558 4205009 := bstep (se 2 (by rfl) ⟨1576878, by rfl⟩ : syracuseStep 4205009 = 3153757) B3153757
theorem B1477075 : Blo 1476558 1477075 := bstep (se 1 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 1477075 = 2215613) B2215613
theorem B1477091 : Blo 1476558 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B6310385 : Blo 1476558 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B1477107 : Blo 1476558 1477107 := bstep (se 1 (by rfl) ⟨1107830, by rfl⟩ : syracuseStep 1477107 = 2215661) B2215661
theorem B1477123 : Blo 1476558 1477123 := bstep (se 1 (by rfl) ⟨1107842, by rfl⟩ : syracuseStep 1477123 = 2215685) B2215685
theorem B1477139 : Blo 1476558 1477139 := bstep (se 1 (by rfl) ⟨1107854, by rfl⟩ : syracuseStep 1477139 = 2215709) B2215709
theorem B1477155 : Blo 1476558 1477155 := bstep (se 1 (by rfl) ⟨1107866, by rfl⟩ : syracuseStep 1477155 = 2215733) B2215733
theorem B2492977 : Blo 1476558 2492977 := bstep (se 2 (by rfl) ⟨934866, by rfl⟩ : syracuseStep 2492977 = 1869733) B1869733
theorem B1477171 : Blo 1476558 1477171 := bstep (se 1 (by rfl) ⟨1107878, by rfl⟩ : syracuseStep 1477171 = 2215757) B2215757
theorem B1477187 : Blo 1476558 1477187 := bstep (se 1 (by rfl) ⟨1107890, by rfl⟩ : syracuseStep 1477187 = 2215781) B2215781
theorem B1477203 : Blo 1476558 1477203 := bstep (se 1 (by rfl) ⟨1107902, by rfl⟩ : syracuseStep 1477203 = 2215805) B2215805
theorem B2493011 : Blo 1476558 2493011 := bstep (se 1 (by rfl) ⟨1869758, by rfl⟩ : syracuseStep 2493011 = 3739517) B3739517
theorem B1477219 : Blo 1476558 1477219 := bstep (se 1 (by rfl) ⟨1107914, by rfl⟩ : syracuseStep 1477219 = 2215829) B2215829
theorem B7481969 : Blo 1476558 7481969 := bstep (se 2 (by rfl) ⟨2805738, by rfl⟩ : syracuseStep 7481969 = 5611477) B5611477
theorem B1477235 : Blo 1476558 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B1477251 : Blo 1476558 1477251 := bstep (se 1 (by rfl) ⟨1107938, by rfl⟩ : syracuseStep 1477251 = 2215877) B2215877
theorem B1477267 : Blo 1476558 1477267 := bstep (se 1 (by rfl) ⟨1107950, by rfl⟩ : syracuseStep 1477267 = 2215901) B2215901
theorem B1477283 : Blo 1476558 1477283 := bstep (se 1 (by rfl) ⟨1107962, by rfl⟩ : syracuseStep 1477283 = 2215925) B2215925
theorem B1477299 : Blo 1476558 1477299 := bstep (se 1 (by rfl) ⟨1107974, by rfl⟩ : syracuseStep 1477299 = 2215949) B2215949
theorem B1477315 : Blo 1476558 1477315 := bstep (se 1 (by rfl) ⟨1107986, by rfl⟩ : syracuseStep 1477315 = 2215973) B2215973
theorem B1477331 : Blo 1476558 1477331 := bstep (se 1 (by rfl) ⟨1107998, by rfl⟩ : syracuseStep 1477331 = 2215997) B2215997
theorem B2493139 : Blo 1476558 2493139 := bstep (se 1 (by rfl) ⟨1869854, by rfl⟩ : syracuseStep 2493139 = 3739709) B3739709
theorem B1477347 : Blo 1476558 1477347 := bstep (se 1 (by rfl) ⟨1108010, by rfl⟩ : syracuseStep 1477347 = 2216021) B2216021
theorem B7990001 : Blo 1476558 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B1477363 : Blo 1476558 1477363 := bstep (se 1 (by rfl) ⟨1108022, by rfl⟩ : syracuseStep 1477363 = 2216045) B2216045
theorem B1477379 : Blo 1476558 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B1477395 : Blo 1476558 1477395 := bstep (se 1 (by rfl) ⟨1108046, by rfl⟩ : syracuseStep 1477395 = 2216093) B2216093
theorem B2247443 : Blo 1476558 2247443 := bstep (se 1 (by rfl) ⟨1685582, by rfl⟩ : syracuseStep 2247443 = 3371165) B3371165
theorem B1477411 : Blo 1476558 1477411 := bstep (se 1 (by rfl) ⟨1108058, by rfl⟩ : syracuseStep 1477411 = 2216117) B2216117
theorem B1477427 : Blo 1476558 1477427 := bstep (se 1 (by rfl) ⟨1108070, by rfl⟩ : syracuseStep 1477427 = 2216141) B2216141
theorem B1477443 : Blo 1476558 1477443 := bstep (se 1 (by rfl) ⟨1108082, by rfl⟩ : syracuseStep 1477443 = 2216165) B2216165
theorem B1477459 : Blo 1476558 1477459 := bstep (se 1 (by rfl) ⟨1108094, by rfl⟩ : syracuseStep 1477459 = 2216189) B2216189
theorem B2493281 : Blo 1476558 2493281 := bstep (se 2 (by rfl) ⟨934980, by rfl⟩ : syracuseStep 2493281 = 1869961) B1869961
theorem B1477475 : Blo 1476558 1477475 := bstep (se 1 (by rfl) ⟨1108106, by rfl⟩ : syracuseStep 1477475 = 2216213) B2216213
theorem B1477491 : Blo 1476558 1477491 := bstep (se 1 (by rfl) ⟨1108118, by rfl⟩ : syracuseStep 1477491 = 2216237) B2216237
theorem B1477507 : Blo 1476558 1477507 := bstep (se 1 (by rfl) ⟨1108130, by rfl⟩ : syracuseStep 1477507 = 2216261) B2216261
theorem B1477523 : Blo 1476558 1477523 := bstep (se 1 (by rfl) ⟨1108142, by rfl⟩ : syracuseStep 1477523 = 2216285) B2216285
theorem B1477539 : Blo 1476558 1477539 := bstep (se 1 (by rfl) ⟨1108154, by rfl⟩ : syracuseStep 1477539 = 2216309) B2216309
theorem B3738545 : Blo 1476558 3738545 := bstep (se 2 (by rfl) ⟨1401954, by rfl⟩ : syracuseStep 3738545 = 2803909) B2803909
theorem B1477555 : Blo 1476558 1477555 := bstep (se 1 (by rfl) ⟨1108166, by rfl⟩ : syracuseStep 1477555 = 2216333) B2216333
theorem B1870771 : Blo 1476558 1870771 := bstep (se 1 (by rfl) ⟨1403078, by rfl⟩ : syracuseStep 1870771 = 2806157) B2806157
theorem B2214851 : Blo 1476558 2214851 := bstep (se 1 (by rfl) ⟨1661138, by rfl⟩ : syracuseStep 2214851 = 3322277) B3322277
theorem B1477571 : Blo 1476558 1477571 := bstep (se 1 (by rfl) ⟨1108178, by rfl⟩ : syracuseStep 1477571 = 2216357) B2216357
theorem B1477587 : Blo 1476558 1477587 := bstep (se 1 (by rfl) ⟨1108190, by rfl⟩ : syracuseStep 1477587 = 2216381) B2216381
theorem B2214881 : Blo 1476558 2214881 := bstep (se 2 (by rfl) ⟨830580, by rfl⟩ : syracuseStep 2214881 = 1661161) B1661161
theorem B2493409 : Blo 1476558 2493409 := bstep (se 2 (by rfl) ⟨935028, by rfl⟩ : syracuseStep 2493409 = 1870057) B1870057
theorem B3738595 : Blo 1476558 3738595 := bstep (se 1 (by rfl) ⟨2803946, by rfl⟩ : syracuseStep 3738595 = 5607893) B5607893
theorem B1477603 : Blo 1476558 1477603 := bstep (se 1 (by rfl) ⟨1108202, by rfl⟩ : syracuseStep 1477603 = 2216405) B2216405
theorem B2214899 : Blo 1476558 2214899 := bstep (se 1 (by rfl) ⟨1661174, by rfl⟩ : syracuseStep 2214899 = 3322349) B3322349
theorem B1477619 : Blo 1476558 1477619 := bstep (se 1 (by rfl) ⟨1108214, by rfl⟩ : syracuseStep 1477619 = 2216429) B2216429
theorem B2493443 : Blo 1476558 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B1477635 : Blo 1476558 1477635 := bstep (se 1 (by rfl) ⟨1108226, by rfl⟩ : syracuseStep 1477635 = 2216453) B2216453
theorem B3156995 : Blo 1476558 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B4983821 : Blo 1476558 4983821 := bstep (se 3 (by rfl) ⟨934466, by rfl⟩ : syracuseStep 4983821 = 1868933) B1868933
theorem B2214929 : Blo 1476558 2214929 := bstep (se 2 (by rfl) ⟨830598, by rfl⟩ : syracuseStep 2214929 = 1661197) B1661197
theorem B1477651 : Blo 1476558 1477651 := bstep (se 1 (by rfl) ⟨1108238, by rfl⟩ : syracuseStep 1477651 = 2216477) B2216477
theorem B1870867 : Blo 1476558 1870867 := bstep (se 1 (by rfl) ⟨1403150, by rfl⟩ : syracuseStep 1870867 = 2806301) B2806301
theorem B5606435 : Blo 1476558 5606435 := bstep (se 1 (by rfl) ⟨4204826, by rfl⟩ : syracuseStep 5606435 = 8409653) B8409653
theorem B2214947 : Blo 1476558 2214947 := bstep (se 1 (by rfl) ⟨1661210, by rfl⟩ : syracuseStep 2214947 = 3322421) B3322421
theorem B1477667 : Blo 1476558 1477667 := bstep (se 1 (by rfl) ⟨1108250, by rfl⟩ : syracuseStep 1477667 = 2216501) B2216501
theorem B1477683 : Blo 1476558 1477683 := bstep (se 1 (by rfl) ⟨1108262, by rfl⟩ : syracuseStep 1477683 = 2216525) B2216525
theorem B2214977 : Blo 1476558 2214977 := bstep (se 2 (by rfl) ⟨830616, by rfl⟩ : syracuseStep 2214977 = 1661233) B1661233
theorem B4983875 : Blo 1476558 4983875 := bstep (se 1 (by rfl) ⟨3737906, by rfl⟩ : syracuseStep 4983875 = 7475813) B7475813
theorem B1477699 : Blo 1476558 1477699 := bstep (se 1 (by rfl) ⟨1108274, by rfl⟩ : syracuseStep 1477699 = 2216549) B2216549
theorem B2214995 : Blo 1476558 2214995 := bstep (se 1 (by rfl) ⟨1661246, by rfl⟩ : syracuseStep 2214995 = 3322493) B3322493
theorem B1477715 : Blo 1476558 1477715 := bstep (se 1 (by rfl) ⟨1108286, by rfl⟩ : syracuseStep 1477715 = 2216573) B2216573
theorem B8096867 : Blo 1476558 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B1477731 : Blo 1476558 1477731 := bstep (se 1 (by rfl) ⟨1108298, by rfl⟩ : syracuseStep 1477731 = 2216597) B2216597
theorem B2215025 : Blo 1476558 2215025 := bstep (se 2 (by rfl) ⟨830634, by rfl⟩ : syracuseStep 2215025 = 1661269) B1661269
theorem B3738737 : Blo 1476558 3738737 := bstep (se 2 (by rfl) ⟨1402026, by rfl⟩ : syracuseStep 3738737 = 2804053) B2804053
theorem B3370097 : Blo 1476558 3370097 := bstep (se 2 (by rfl) ⟨1263786, by rfl⟩ : syracuseStep 3370097 = 2527573) B2527573
theorem B1477747 : Blo 1476558 1477747 := bstep (se 1 (by rfl) ⟨1108310, by rfl⟩ : syracuseStep 1477747 = 2216621) B2216621
theorem B2215043 : Blo 1476558 2215043 := bstep (se 1 (by rfl) ⟨1661282, by rfl⟩ : syracuseStep 2215043 = 3322565) B3322565
theorem B2493571 : Blo 1476558 2493571 := bstep (se 1 (by rfl) ⟨1870178, by rfl⟩ : syracuseStep 2493571 = 3740357) B3740357
theorem B1477763 : Blo 1476558 1477763 := bstep (se 1 (by rfl) ⟨1108322, by rfl⟩ : syracuseStep 1477763 = 2216645) B2216645
theorem B2804881 : Blo 1476558 2804881 := bstep (se 2 (by rfl) ⟨1051830, by rfl⟩ : syracuseStep 2804881 = 2103661) B2103661
theorem B1477779 : Blo 1476558 1477779 := bstep (se 1 (by rfl) ⟨1108334, by rfl⟩ : syracuseStep 1477779 = 2216669) B2216669
theorem B2215073 : Blo 1476558 2215073 := bstep (se 2 (by rfl) ⟨830652, by rfl⟩ : syracuseStep 2215073 = 1661305) B1661305
theorem B1477795 : Blo 1476558 1477795 := bstep (se 1 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 1477795 = 2216693) B2216693
theorem B2215091 : Blo 1476558 2215091 := bstep (se 1 (by rfl) ⟨1661318, by rfl⟩ : syracuseStep 2215091 = 3322637) B3322637
theorem B1477811 : Blo 1476558 1477811 := bstep (se 1 (by rfl) ⟨1108358, by rfl⟩ : syracuseStep 1477811 = 2216717) B2216717
theorem B1477827 : Blo 1476558 1477827 := bstep (se 1 (by rfl) ⟨1108370, by rfl⟩ : syracuseStep 1477827 = 2216741) B2216741
theorem B2215121 : Blo 1476558 2215121 := bstep (se 2 (by rfl) ⟨830670, by rfl⟩ : syracuseStep 2215121 = 1661341) B1661341
theorem B1477843 : Blo 1476558 1477843 := bstep (se 1 (by rfl) ⟨1108382, by rfl⟩ : syracuseStep 1477843 = 2216765) B2216765
theorem B2215139 : Blo 1476558 2215139 := bstep (se 1 (by rfl) ⟨1661354, by rfl⟩ : syracuseStep 2215139 = 3322709) B3322709
theorem B1477859 : Blo 1476558 1477859 := bstep (se 1 (by rfl) ⟨1108394, by rfl⟩ : syracuseStep 1477859 = 2216789) B2216789
theorem B1477875 : Blo 1476558 1477875 := bstep (se 1 (by rfl) ⟨1108406, by rfl⟩ : syracuseStep 1477875 = 2216813) B2216813
theorem B2215169 : Blo 1476558 2215169 := bstep (se 2 (by rfl) ⟨830688, by rfl⟩ : syracuseStep 2215169 = 1661377) B1661377
theorem B1477891 : Blo 1476558 1477891 := bstep (se 1 (by rfl) ⟨1108418, by rfl⟩ : syracuseStep 1477891 = 2216837) B2216837
theorem B2493713 : Blo 1476558 2493713 := bstep (se 2 (by rfl) ⟨935142, by rfl⟩ : syracuseStep 2493713 = 1870285) B1870285
theorem B2215187 : Blo 1476558 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B1477907 : Blo 1476558 1477907 := bstep (se 1 (by rfl) ⟨1108430, by rfl⟩ : syracuseStep 1477907 = 2216861) B2216861
theorem B1477923 : Blo 1476558 1477923 := bstep (se 1 (by rfl) ⟨1108442, by rfl⟩ : syracuseStep 1477923 = 2216885) B2216885
theorem B2215217 : Blo 1476558 2215217 := bstep (se 2 (by rfl) ⟨830706, by rfl⟩ : syracuseStep 2215217 = 1661413) B1661413
theorem B1477939 : Blo 1476558 1477939 := bstep (se 1 (by rfl) ⟨1108454, by rfl⟩ : syracuseStep 1477939 = 2216909) B2216909
theorem B2215235 : Blo 1476558 2215235 := bstep (se 1 (by rfl) ⟨1661426, by rfl⟩ : syracuseStep 2215235 = 3322853) B3322853
theorem B1477955 : Blo 1476558 1477955 := bstep (se 1 (by rfl) ⟨1108466, by rfl⟩ : syracuseStep 1477955 = 2216933) B2216933
theorem B4984145 : Blo 1476558 4984145 := bstep (se 2 (by rfl) ⟨1869054, by rfl⟩ : syracuseStep 4984145 = 3738109) B3738109
theorem B1477971 : Blo 1476558 1477971 := bstep (se 1 (by rfl) ⟨1108478, by rfl⟩ : syracuseStep 1477971 = 2216957) B2216957
theorem B2215265 : Blo 1476558 2215265 := bstep (se 2 (by rfl) ⟨830724, by rfl⟩ : syracuseStep 2215265 = 1661449) B1661449
theorem B1477987 : Blo 1476558 1477987 := bstep (se 1 (by rfl) ⟨1108490, by rfl⟩ : syracuseStep 1477987 = 2216981) B2216981
theorem B2215283 : Blo 1476558 2215283 := bstep (se 1 (by rfl) ⟨1661462, by rfl⟩ : syracuseStep 2215283 = 3322925) B3322925
theorem B1478003 : Blo 1476558 1478003 := bstep (se 1 (by rfl) ⟨1108502, by rfl⟩ : syracuseStep 1478003 = 2217005) B2217005
theorem B1478019 : Blo 1476558 1478019 := bstep (se 1 (by rfl) ⟨1108514, by rfl⟩ : syracuseStep 1478019 = 2217029) B2217029
theorem B2215313 : Blo 1476558 2215313 := bstep (se 2 (by rfl) ⟨830742, by rfl⟩ : syracuseStep 2215313 = 1661485) B1661485
theorem B2493841 : Blo 1476558 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B1478035 : Blo 1476558 1478035 := bstep (se 1 (by rfl) ⟨1108526, by rfl⟩ : syracuseStep 1478035 = 2217053) B2217053
theorem B2215331 : Blo 1476558 2215331 := bstep (se 1 (by rfl) ⟨1661498, by rfl⟩ : syracuseStep 2215331 = 3322997) B3322997
theorem B1478051 : Blo 1476558 1478051 := bstep (se 1 (by rfl) ⟨1108538, by rfl⟩ : syracuseStep 1478051 = 2217077) B2217077
theorem B2493875 : Blo 1476558 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B1478067 : Blo 1476558 1478067 := bstep (se 1 (by rfl) ⟨1108550, by rfl⟩ : syracuseStep 1478067 = 2217101) B2217101
theorem B2215361 : Blo 1476558 2215361 := bstep (se 2 (by rfl) ⟨830760, by rfl⟩ : syracuseStep 2215361 = 1661521) B1661521
theorem B1478083 : Blo 1476558 1478083 := bstep (se 1 (by rfl) ⟨1108562, by rfl⟩ : syracuseStep 1478083 = 2217125) B2217125
theorem B31935941 : Blo 1476558 31935941 := bstep (se 4 (by rfl) ⟨2993994, by rfl⟩ : syracuseStep 31935941 = 5987989) B5987989
theorem B2215379 : Blo 1476558 2215379 := bstep (se 1 (by rfl) ⟨1661534, by rfl⟩ : syracuseStep 2215379 = 3323069) B3323069
theorem B1478099 : Blo 1476558 1478099 := bstep (se 1 (by rfl) ⟨1108574, by rfl⟩ : syracuseStep 1478099 = 2217149) B2217149
theorem B1478115 : Blo 1476558 1478115 := bstep (se 1 (by rfl) ⟨1108586, by rfl⟩ : syracuseStep 1478115 = 2217173) B2217173
theorem B2215409 : Blo 1476558 2215409 := bstep (se 2 (by rfl) ⟨830778, by rfl⟩ : syracuseStep 2215409 = 1661557) B1661557
theorem B1478131 : Blo 1476558 1478131 := bstep (se 1 (by rfl) ⟨1108598, by rfl⟩ : syracuseStep 1478131 = 2217197) B2217197
theorem B2215427 : Blo 1476558 2215427 := bstep (se 1 (by rfl) ⟨1661570, by rfl⟩ : syracuseStep 2215427 = 3323141) B3323141
theorem B1478147 : Blo 1476558 1478147 := bstep (se 1 (by rfl) ⟨1108610, by rfl⟩ : syracuseStep 1478147 = 2217221) B2217221
theorem B1478163 : Blo 1476558 1478163 := bstep (se 1 (by rfl) ⟨1108622, by rfl⟩ : syracuseStep 1478163 = 2217245) B2217245
theorem B2215457 : Blo 1476558 2215457 := bstep (se 2 (by rfl) ⟨830796, by rfl⟩ : syracuseStep 2215457 = 1661593) B1661593
theorem B2805283 : Blo 1476558 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B1478179 : Blo 1476558 1478179 := bstep (se 1 (by rfl) ⟨1108634, by rfl⟩ : syracuseStep 1478179 = 2217269) B2217269
theorem B2215475 : Blo 1476558 2215475 := bstep (se 1 (by rfl) ⟨1661606, by rfl⟩ : syracuseStep 2215475 = 3323213) B3323213
theorem B2494003 : Blo 1476558 2494003 := bstep (se 1 (by rfl) ⟨1870502, by rfl⟩ : syracuseStep 2494003 = 3741005) B3741005
theorem B1478195 : Blo 1476558 1478195 := bstep (se 1 (by rfl) ⟨1108646, by rfl⟩ : syracuseStep 1478195 = 2217293) B2217293
theorem B1478211 : Blo 1476558 1478211 := bstep (se 1 (by rfl) ⟨1108658, by rfl⟩ : syracuseStep 1478211 = 2217317) B2217317
theorem B2215505 : Blo 1476558 2215505 := bstep (se 2 (by rfl) ⟨830814, by rfl⟩ : syracuseStep 2215505 = 1661629) B1661629
theorem B2805329 : Blo 1476558 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B1478227 : Blo 1476558 1478227 := bstep (se 1 (by rfl) ⟨1108670, by rfl⟩ : syracuseStep 1478227 = 2217341) B2217341
theorem B2215523 : Blo 1476558 2215523 := bstep (se 1 (by rfl) ⟨1661642, by rfl⟩ : syracuseStep 2215523 = 3323285) B3323285
theorem B1478243 : Blo 1476558 1478243 := bstep (se 1 (by rfl) ⟨1108682, by rfl⟩ : syracuseStep 1478243 = 2217365) B2217365
theorem B3370609 : Blo 1476558 3370609 := bstep (se 2 (by rfl) ⟨1263978, by rfl⟩ : syracuseStep 3370609 = 2527957) B2527957
theorem B1478259 : Blo 1476558 1478259 := bstep (se 1 (by rfl) ⟨1108694, by rfl⟩ : syracuseStep 1478259 = 2217389) B2217389
theorem B2215553 : Blo 1476558 2215553 := bstep (se 2 (by rfl) ⟨830832, by rfl⟩ : syracuseStep 2215553 = 1661665) B1661665
theorem B1478275 : Blo 1476558 1478275 := bstep (se 1 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 1478275 = 2217413) B2217413
theorem B13471373 : Blo 1476558 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2215571 : Blo 1476558 2215571 := bstep (se 1 (by rfl) ⟨1661678, by rfl⟩ : syracuseStep 2215571 = 3323357) B3323357
theorem B1478291 : Blo 1476558 1478291 := bstep (se 1 (by rfl) ⟨1108718, by rfl⟩ : syracuseStep 1478291 = 2217437) B2217437
theorem B1478307 : Blo 1476558 1478307 := bstep (se 1 (by rfl) ⟨1108730, by rfl⟩ : syracuseStep 1478307 = 2217461) B2217461
theorem B5607089 : Blo 1476558 5607089 := bstep (se 2 (by rfl) ⟨2102658, by rfl⟩ : syracuseStep 5607089 = 4205317) B4205317
theorem B2215601 : Blo 1476558 2215601 := bstep (se 2 (by rfl) ⟨830850, by rfl⟩ : syracuseStep 2215601 = 1661701) B1661701
theorem B1478323 : Blo 1476558 1478323 := bstep (se 1 (by rfl) ⟨1108742, by rfl⟩ : syracuseStep 1478323 = 2217485) B2217485
theorem B2494145 : Blo 1476558 2494145 := bstep (se 2 (by rfl) ⟨935304, by rfl⟩ : syracuseStep 2494145 = 1870609) B1870609
theorem B2215619 : Blo 1476558 2215619 := bstep (se 1 (by rfl) ⟨1661714, by rfl⟩ : syracuseStep 2215619 = 3323429) B3323429
theorem B1478339 : Blo 1476558 1478339 := bstep (se 1 (by rfl) ⟨1108754, by rfl⟩ : syracuseStep 1478339 = 2217509) B2217509
theorem B5992141 : Blo 1476558 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B1478355 : Blo 1476558 1478355 := bstep (se 1 (by rfl) ⟨1108766, by rfl⟩ : syracuseStep 1478355 = 2217533) B2217533
theorem B2215649 : Blo 1476558 2215649 := bstep (se 2 (by rfl) ⟨830868, by rfl⟩ : syracuseStep 2215649 = 1661737) B1661737
theorem B1478371 : Blo 1476558 1478371 := bstep (se 1 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 1478371 = 2217557) B2217557
theorem B2215667 : Blo 1476558 2215667 := bstep (se 1 (by rfl) ⟨1661750, by rfl⟩ : syracuseStep 2215667 = 3323501) B3323501
theorem B1478387 : Blo 1476558 1478387 := bstep (se 1 (by rfl) ⟨1108790, by rfl⟩ : syracuseStep 1478387 = 2217581) B2217581
theorem B1478403 : Blo 1476558 1478403 := bstep (se 1 (by rfl) ⟨1108802, by rfl⟩ : syracuseStep 1478403 = 2217605) B2217605
theorem B2215697 : Blo 1476558 2215697 := bstep (se 2 (by rfl) ⟨830886, by rfl⟩ : syracuseStep 2215697 = 1661773) B1661773
theorem B1478419 : Blo 1476558 1478419 := bstep (se 1 (by rfl) ⟨1108814, by rfl⟩ : syracuseStep 1478419 = 2217629) B2217629
theorem B2215715 : Blo 1476558 2215715 := bstep (se 1 (by rfl) ⟨1661786, by rfl⟩ : syracuseStep 2215715 = 3323573) B3323573
theorem B1478435 : Blo 1476558 1478435 := bstep (se 1 (by rfl) ⟨1108826, by rfl⟩ : syracuseStep 1478435 = 2217653) B2217653
theorem B1478451 : Blo 1476558 1478451 := bstep (se 1 (by rfl) ⟨1108838, by rfl⟩ : syracuseStep 1478451 = 2217677) B2217677
theorem B26963765 : Blo 1476558 26963765 := bstep (se 5 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 26963765 = 2527853) B2527853
theorem B2215745 : Blo 1476558 2215745 := bstep (se 2 (by rfl) ⟨830904, by rfl⟩ : syracuseStep 2215745 = 1661809) B1661809
theorem B2494273 : Blo 1476558 2494273 := bstep (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) B1870705
theorem B1478467 : Blo 1476558 1478467 := bstep (se 1 (by rfl) ⟨1108850, by rfl⟩ : syracuseStep 1478467 = 2217701) B2217701
theorem B2215763 : Blo 1476558 2215763 := bstep (se 1 (by rfl) ⟨1661822, by rfl⟩ : syracuseStep 2215763 = 3323645) B3323645
theorem B1478483 : Blo 1476558 1478483 := bstep (se 1 (by rfl) ⟨1108862, by rfl⟩ : syracuseStep 1478483 = 2217725) B2217725
theorem B2494307 : Blo 1476558 2494307 := bstep (se 1 (by rfl) ⟨1870730, by rfl⟩ : syracuseStep 2494307 = 3741461) B3741461
theorem B1478499 : Blo 1476558 1478499 := bstep (se 1 (by rfl) ⟨1108874, by rfl⟩ : syracuseStep 1478499 = 2217749) B2217749
theorem B4984685 : Blo 1476558 4984685 := bstep (se 3 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 4984685 = 1869257) B1869257
theorem B2215793 : Blo 1476558 2215793 := bstep (se 2 (by rfl) ⟨830922, by rfl⟩ : syracuseStep 2215793 = 1661845) B1661845
theorem B2805617 : Blo 1476558 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B1478515 : Blo 1476558 1478515 := bstep (se 1 (by rfl) ⟨1108886, by rfl⟩ : syracuseStep 1478515 = 2217773) B2217773
theorem B4206467 : Blo 1476558 4206467 := bstep (se 1 (by rfl) ⟨3154850, by rfl⟩ : syracuseStep 4206467 = 6309701) B6309701
theorem B2215811 : Blo 1476558 2215811 := bstep (se 1 (by rfl) ⟨1661858, by rfl⟩ : syracuseStep 2215811 = 3323717) B3323717
theorem B1478531 : Blo 1476558 1478531 := bstep (se 1 (by rfl) ⟨1108898, by rfl⟩ : syracuseStep 1478531 = 2217797) B2217797
theorem B1478547 : Blo 1476558 1478547 := bstep (se 1 (by rfl) ⟨1108910, by rfl⟩ : syracuseStep 1478547 = 2217821) B2217821
theorem B2215841 : Blo 1476558 2215841 := bstep (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) B1661881
theorem B4984739 : Blo 1476558 4984739 := bstep (se 1 (by rfl) ⟨3738554, by rfl⟩ : syracuseStep 4984739 = 7477109) B7477109
theorem B2215859 : Blo 1476558 2215859 := bstep (se 1 (by rfl) ⟨1661894, by rfl⟩ : syracuseStep 2215859 = 3323789) B3323789
theorem B2215889 : Blo 1476558 2215889 := bstep (se 2 (by rfl) ⟨830958, by rfl⟩ : syracuseStep 2215889 = 1661917) B1661917
theorem B2215907 : Blo 1476558 2215907 := bstep (se 1 (by rfl) ⟨1661930, by rfl⟩ : syracuseStep 2215907 = 3323861) B3323861
theorem B2494435 : Blo 1476558 2494435 := bstep (se 1 (by rfl) ⟨1870826, by rfl⟩ : syracuseStep 2494435 = 3741653) B3741653
theorem B2215937 : Blo 1476558 2215937 := bstep (se 2 (by rfl) ⟨830976, by rfl⟩ : syracuseStep 2215937 = 1661953) B1661953
theorem B12144653 : Blo 1476558 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B3993617 : Blo 1476558 3993617 := bstep (se 2 (by rfl) ⟨1497606, by rfl⟩ : syracuseStep 3993617 = 2995213) B2995213
theorem B2215955 : Blo 1476558 2215955 := bstep (se 1 (by rfl) ⟨1661966, by rfl⟩ : syracuseStep 2215955 = 3323933) B3323933
theorem B2527265 : Blo 1476558 2527265 := bstep (se 2 (by rfl) ⟨947724, by rfl⟩ : syracuseStep 2527265 = 1895449) B1895449
theorem B7483427 : Blo 1476558 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B2215985 : Blo 1476558 2215985 := bstep (se 2 (by rfl) ⟨830994, by rfl⟩ : syracuseStep 2215985 = 1661989) B1661989
theorem B2216003 : Blo 1476558 2216003 := bstep (se 1 (by rfl) ⟨1662002, by rfl⟩ : syracuseStep 2216003 = 3324005) B3324005
theorem B11374661 : Blo 1476558 11374661 := bstep (se 4 (by rfl) ⟨1066374, by rfl⟩ : syracuseStep 11374661 = 2132749) B2132749
theorem B3739729 : Blo 1476558 3739729 := bstep (se 2 (by rfl) ⟨1402398, by rfl⟩ : syracuseStep 3739729 = 2804797) B2804797
theorem B2216033 : Blo 1476558 2216033 := bstep (se 2 (by rfl) ⟨831012, by rfl⟩ : syracuseStep 2216033 = 1662025) B1662025
theorem B2699363 : Blo 1476558 2699363 := bstep (se 1 (by rfl) ⟨2024522, by rfl⟩ : syracuseStep 2699363 = 4049045) B4049045
theorem B6926435 : Blo 1476558 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B2494577 : Blo 1476558 2494577 := bstep (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) B1870933
theorem B1577075 : Blo 1476558 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B2216051 : Blo 1476558 2216051 := bstep (se 1 (by rfl) ⟨1662038, by rfl⟩ : syracuseStep 2216051 = 3324077) B3324077
theorem B6312077 : Blo 1476558 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B2216081 : Blo 1476558 2216081 := bstep (se 2 (by rfl) ⟨831030, by rfl⟩ : syracuseStep 2216081 = 1662061) B1662061
theorem B2216099 : Blo 1476558 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B4985009 : Blo 1476558 4985009 := bstep (se 2 (by rfl) ⟨1869378, by rfl⟩ : syracuseStep 4985009 = 3738757) B3738757
theorem B2216129 : Blo 1476558 2216129 := bstep (se 2 (by rfl) ⟨831048, by rfl⟩ : syracuseStep 2216129 = 1662097) B1662097
theorem B2216147 : Blo 1476558 2216147 := bstep (se 1 (by rfl) ⟨1662110, by rfl⟩ : syracuseStep 2216147 = 3324221) B3324221
theorem B2216177 : Blo 1476558 2216177 := bstep (se 2 (by rfl) ⟨831066, by rfl⟩ : syracuseStep 2216177 = 1662133) B1662133
theorem B2494705 : Blo 1476558 2494705 := bstep (se 2 (by rfl) ⟨935514, by rfl⟩ : syracuseStep 2494705 = 1871029) B1871029
theorem B2216195 : Blo 1476558 2216195 := bstep (se 1 (by rfl) ⟨1662146, by rfl⟩ : syracuseStep 2216195 = 3324293) B3324293
theorem B4731149 : Blo 1476558 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B2494739 : Blo 1476558 2494739 := bstep (se 1 (by rfl) ⟨1871054, by rfl⟩ : syracuseStep 2494739 = 3742109) B3742109
theorem B2216225 : Blo 1476558 2216225 := bstep (se 2 (by rfl) ⟨831084, by rfl⟩ : syracuseStep 2216225 = 1662169) B1662169
theorem B2216243 : Blo 1476558 2216243 := bstep (se 1 (by rfl) ⟨1662182, by rfl⟩ : syracuseStep 2216243 = 3324365) B3324365
theorem B30322997 : Blo 1476558 30322997 := bstep (se 5 (by rfl) ⟨1421390, by rfl⟩ : syracuseStep 30322997 = 2842781) B2842781
theorem B2994499 : Blo 1476558 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B2216273 : Blo 1476558 2216273 := bstep (se 2 (by rfl) ⟨831102, by rfl⟩ : syracuseStep 2216273 = 1662205) B1662205
theorem B2216291 : Blo 1476558 2216291 := bstep (se 1 (by rfl) ⟨1662218, by rfl⟩ : syracuseStep 2216291 = 3324437) B3324437
theorem B3740003 : Blo 1476558 3740003 := bstep (se 1 (by rfl) ⟨2805002, by rfl⟩ : syracuseStep 3740003 = 5610005) B5610005
theorem B2216321 : Blo 1476558 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B2216339 : Blo 1476558 2216339 := bstep (se 1 (by rfl) ⟨1662254, by rfl⟩ : syracuseStep 2216339 = 3324509) B3324509
theorem B2494867 : Blo 1476558 2494867 := bstep (se 1 (by rfl) ⟨1871150, by rfl⟩ : syracuseStep 2494867 = 3742301) B3742301
theorem B2216369 : Blo 1476558 2216369 := bstep (se 2 (by rfl) ⟨831138, by rfl⟩ : syracuseStep 2216369 = 1662277) B1662277
theorem B2216387 : Blo 1476558 2216387 := bstep (se 1 (by rfl) ⟨1662290, by rfl⟩ : syracuseStep 2216387 = 3324581) B3324581
theorem B2216417 : Blo 1476558 2216417 := bstep (se 2 (by rfl) ⟨831156, by rfl⟩ : syracuseStep 2216417 = 1662313) B1662313
theorem B11981297 : Blo 1476558 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B10654193 : Blo 1476558 10654193 := bstep (se 2 (by rfl) ⟨3995322, by rfl⟩ : syracuseStep 10654193 = 7990645) B7990645
theorem B2216435 : Blo 1476558 2216435 := bstep (se 1 (by rfl) ⟨1662326, by rfl⟩ : syracuseStep 2216435 = 3324653) B3324653
theorem B3322385 : Blo 1476558 3322385 := bstep (se 2 (by rfl) ⟨1245894, by rfl⟩ : syracuseStep 3322385 = 2491789) B2491789
theorem B2216465 : Blo 1476558 2216465 := bstep (se 2 (by rfl) ⟨831174, by rfl⟩ : syracuseStep 2216465 = 1662349) B1662349
theorem B2495009 : Blo 1476558 2495009 := bstep (se 2 (by rfl) ⟨935628, by rfl⟩ : syracuseStep 2495009 = 1871257) B1871257
theorem B3322403 : Blo 1476558 3322403 := bstep (se 1 (by rfl) ⟨2491802, by rfl⟩ : syracuseStep 3322403 = 4983605) B4983605
theorem B3740195 : Blo 1476558 3740195 := bstep (se 1 (by rfl) ⟨2805146, by rfl⟩ : syracuseStep 3740195 = 5610293) B5610293
theorem B2216483 : Blo 1476558 2216483 := bstep (se 1 (by rfl) ⟨1662362, by rfl⟩ : syracuseStep 2216483 = 3324725) B3324725
theorem B2216513 : Blo 1476558 2216513 := bstep (se 2 (by rfl) ⟨831192, by rfl⟩ : syracuseStep 2216513 = 1662385) B1662385
theorem B2806339 : Blo 1476558 2806339 := bstep (se 1 (by rfl) ⟨2104754, by rfl⟩ : syracuseStep 2806339 = 4209509) B4209509
theorem B12620357 : Blo 1476558 12620357 := bstep (se 4 (by rfl) ⟨1183158, by rfl⟩ : syracuseStep 12620357 = 2366317) B2366317
theorem B2216531 : Blo 1476558 2216531 := bstep (se 1 (by rfl) ⟨1662398, by rfl⟩ : syracuseStep 2216531 = 3324797) B3324797
theorem B2216561 : Blo 1476558 2216561 := bstep (se 2 (by rfl) ⟨831210, by rfl⟩ : syracuseStep 2216561 = 1662421) B1662421
theorem B2216579 : Blo 1476558 2216579 := bstep (se 1 (by rfl) ⟨1662434, by rfl⟩ : syracuseStep 2216579 = 3324869) B3324869
theorem B2216609 : Blo 1476558 2216609 := bstep (se 2 (by rfl) ⟨831228, by rfl⟩ : syracuseStep 2216609 = 1662457) B1662457
theorem B2216627 : Blo 1476558 2216627 := bstep (se 1 (by rfl) ⟨1662470, by rfl⟩ : syracuseStep 2216627 = 3324941) B3324941
theorem B4985549 : Blo 1476558 4985549 := bstep (se 3 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 4985549 = 1869581) B1869581
theorem B2216657 : Blo 1476558 2216657 := bstep (se 2 (by rfl) ⟨831246, by rfl⟩ : syracuseStep 2216657 = 1662493) B1662493
theorem B2216675 : Blo 1476558 2216675 := bstep (se 1 (by rfl) ⟨1662506, by rfl⟩ : syracuseStep 2216675 = 3325013) B3325013
theorem B2216705 : Blo 1476558 2216705 := bstep (se 2 (by rfl) ⟨831264, by rfl⟩ : syracuseStep 2216705 = 1662529) B1662529
theorem B4985603 : Blo 1476558 4985603 := bstep (se 1 (by rfl) ⟨3739202, by rfl⟩ : syracuseStep 4985603 = 7478405) B7478405
theorem B2216723 : Blo 1476558 2216723 := bstep (se 1 (by rfl) ⟨1662542, by rfl⟩ : syracuseStep 2216723 = 3325085) B3325085
theorem B8409905 : Blo 1476558 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B3322673 : Blo 1476558 3322673 := bstep (se 2 (by rfl) ⟨1246002, by rfl⟩ : syracuseStep 3322673 = 2492005) B2492005
theorem B2216753 : Blo 1476558 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B3322691 : Blo 1476558 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B2216771 : Blo 1476558 2216771 := bstep (se 1 (by rfl) ⟨1662578, by rfl⟩ : syracuseStep 2216771 = 3325157) B3325157
theorem B7484237 : Blo 1476558 7484237 := bstep (se 3 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 7484237 = 2806589) B2806589
theorem B2216801 : Blo 1476558 2216801 := bstep (se 2 (by rfl) ⟨831300, by rfl⟩ : syracuseStep 2216801 = 1662601) B1662601
theorem B1577827 : Blo 1476558 1577827 := bstep (se 1 (by rfl) ⟨1183370, by rfl⟩ : syracuseStep 1577827 = 2366741) B2366741
theorem B2216819 : Blo 1476558 2216819 := bstep (se 1 (by rfl) ⟨1662614, by rfl⟩ : syracuseStep 2216819 = 3325229) B3325229
theorem B2216849 : Blo 1476558 2216849 := bstep (se 2 (by rfl) ⟨831318, by rfl⟩ : syracuseStep 2216849 = 1662637) B1662637
theorem B2216867 : Blo 1476558 2216867 := bstep (se 1 (by rfl) ⟨1662650, by rfl⟩ : syracuseStep 2216867 = 3325301) B3325301
theorem B2216897 : Blo 1476558 2216897 := bstep (se 2 (by rfl) ⟨831336, by rfl⟩ : syracuseStep 2216897 = 1662673) B1662673
theorem B2216915 : Blo 1476558 2216915 := bstep (se 1 (by rfl) ⟨1662686, by rfl⟩ : syracuseStep 2216915 = 3325373) B3325373
theorem B2216945 : Blo 1476558 2216945 := bstep (se 2 (by rfl) ⟨831354, by rfl⟩ : syracuseStep 2216945 = 1662709) B1662709
theorem B2216963 : Blo 1476558 2216963 := bstep (se 1 (by rfl) ⟨1662722, by rfl⟩ : syracuseStep 2216963 = 3325445) B3325445
theorem B2806787 : Blo 1476558 2806787 := bstep (se 1 (by rfl) ⟨2105090, by rfl⟩ : syracuseStep 2806787 = 4210181) B4210181
theorem B4985873 : Blo 1476558 4985873 := bstep (se 2 (by rfl) ⟨1869702, by rfl⟩ : syracuseStep 4985873 = 3739405) B3739405
theorem B2216993 : Blo 1476558 2216993 := bstep (se 2 (by rfl) ⟨831372, by rfl⟩ : syracuseStep 2216993 = 1662745) B1662745
theorem B2217011 : Blo 1476558 2217011 := bstep (se 1 (by rfl) ⟨1662758, by rfl⟩ : syracuseStep 2217011 = 3325517) B3325517
theorem B3322961 : Blo 1476558 3322961 := bstep (se 2 (by rfl) ⟨1246110, by rfl⟩ : syracuseStep 3322961 = 2492221) B2492221
theorem B4207697 : Blo 1476558 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B2217041 : Blo 1476558 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B3322979 : Blo 1476558 3322979 := bstep (se 1 (by rfl) ⟨2492234, by rfl⟩ : syracuseStep 3322979 = 4984469) B4984469
theorem B5608547 : Blo 1476558 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B1684579 : Blo 1476558 1684579 := bstep (se 1 (by rfl) ⟨1263434, by rfl⟩ : syracuseStep 1684579 = 2526869) B2526869
theorem B2217059 : Blo 1476558 2217059 := bstep (se 1 (by rfl) ⟨1662794, by rfl⟩ : syracuseStep 2217059 = 3325589) B3325589
theorem B5608561 : Blo 1476558 5608561 := bstep (se 2 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 5608561 = 4206421) B4206421
theorem B12629105 : Blo 1476558 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B2217089 : Blo 1476558 2217089 := bstep (se 2 (by rfl) ⟨831408, by rfl⟩ : syracuseStep 2217089 = 1662817) B1662817
theorem B2217107 : Blo 1476558 2217107 := bstep (se 1 (by rfl) ⟨1662830, by rfl⟩ : syracuseStep 2217107 = 3325661) B3325661
theorem B2217137 : Blo 1476558 2217137 := bstep (se 2 (by rfl) ⟨831426, by rfl⟩ : syracuseStep 2217137 = 1662853) B1662853
theorem B2217155 : Blo 1476558 2217155 := bstep (se 1 (by rfl) ⟨1662866, by rfl⟩ : syracuseStep 2217155 = 3325733) B3325733
theorem B2217185 : Blo 1476558 2217185 := bstep (se 2 (by rfl) ⟨831444, by rfl⟩ : syracuseStep 2217185 = 1662889) B1662889
theorem B18945251 : Blo 1476558 18945251 := bstep (se 1 (by rfl) ⟨14208938, by rfl⟩ : syracuseStep 18945251 = 28417877) B28417877
theorem B12621041 : Blo 1476558 12621041 := bstep (se 2 (by rfl) ⟨4732890, by rfl⟩ : syracuseStep 12621041 = 9465781) B9465781
theorem B2217203 : Blo 1476558 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B2217233 : Blo 1476558 2217233 := bstep (se 2 (by rfl) ⟨831462, by rfl⟩ : syracuseStep 2217233 = 1662925) B1662925
theorem B2217251 : Blo 1476558 2217251 := bstep (se 1 (by rfl) ⟨1662938, by rfl⟩ : syracuseStep 2217251 = 3325877) B3325877
theorem B2217281 : Blo 1476558 2217281 := bstep (se 2 (by rfl) ⟨831480, by rfl⟩ : syracuseStep 2217281 = 1662961) B1662961
theorem B2217299 : Blo 1476558 2217299 := bstep (se 1 (by rfl) ⟨1662974, by rfl⟩ : syracuseStep 2217299 = 3325949) B3325949
theorem B3323249 : Blo 1476558 3323249 := bstep (se 2 (by rfl) ⟨1246218, by rfl⟩ : syracuseStep 3323249 = 2492437) B2492437
theorem B2217329 : Blo 1476558 2217329 := bstep (se 2 (by rfl) ⟨831498, by rfl⟩ : syracuseStep 2217329 = 1662997) B1662997
theorem B3323267 : Blo 1476558 3323267 := bstep (se 1 (by rfl) ⟨2492450, by rfl⟩ : syracuseStep 3323267 = 4984901) B4984901
theorem B2217347 : Blo 1476558 2217347 := bstep (se 1 (by rfl) ⟨1663010, by rfl⟩ : syracuseStep 2217347 = 3326021) B3326021
theorem B5322125 : Blo 1476558 5322125 := bstep (se 3 (by rfl) ⟨997898, by rfl⟩ : syracuseStep 5322125 = 1995797) B1995797
theorem B2217377 : Blo 1476558 2217377 := bstep (se 2 (by rfl) ⟨831516, by rfl⟩ : syracuseStep 2217377 = 1663033) B1663033
theorem B2217395 : Blo 1476558 2217395 := bstep (se 1 (by rfl) ⟨1663046, by rfl⟩ : syracuseStep 2217395 = 3326093) B3326093
theorem B3741137 : Blo 1476558 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B2217425 : Blo 1476558 2217425 := bstep (se 2 (by rfl) ⟨831534, by rfl⟩ : syracuseStep 2217425 = 1663069) B1663069
theorem B2102755 : Blo 1476558 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B2217443 : Blo 1476558 2217443 := bstep (se 1 (by rfl) ⟨1663082, by rfl⟩ : syracuseStep 2217443 = 3326165) B3326165
theorem B2217473 : Blo 1476558 2217473 := bstep (se 2 (by rfl) ⟨831552, by rfl⟩ : syracuseStep 2217473 = 1663105) B1663105
theorem B3741187 : Blo 1476558 3741187 := bstep (se 1 (by rfl) ⟨2805890, by rfl⟩ : syracuseStep 3741187 = 5611781) B5611781
theorem B5322253 : Blo 1476558 5322253 := bstep (se 3 (by rfl) ⟨997922, by rfl⟩ : syracuseStep 5322253 = 1995845) B1995845
theorem B2217491 : Blo 1476558 2217491 := bstep (se 1 (by rfl) ⟨1663118, by rfl⟩ : syracuseStep 2217491 = 3326237) B3326237
theorem B4986413 : Blo 1476558 4986413 := bstep (se 3 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 4986413 = 1869905) B1869905
theorem B7476785 : Blo 1476558 7476785 := bstep (se 2 (by rfl) ⟨2803794, by rfl⟩ : syracuseStep 7476785 = 5607589) B5607589
theorem B6395441 : Blo 1476558 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B2217521 : Blo 1476558 2217521 := bstep (se 2 (by rfl) ⟨831570, by rfl⟩ : syracuseStep 2217521 = 1663141) B1663141
theorem B16823861 : Blo 1476558 16823861 := bstep (se 5 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 16823861 = 1577237) B1577237
theorem B3200561 : Blo 1476558 3200561 := bstep (se 2 (by rfl) ⟨1200210, by rfl⟩ : syracuseStep 3200561 = 2400421) B2400421
theorem B2217539 : Blo 1476558 2217539 := bstep (se 1 (by rfl) ⟨1663154, by rfl⟩ : syracuseStep 2217539 = 3326309) B3326309
theorem B2217569 : Blo 1476558 2217569 := bstep (se 2 (by rfl) ⟨831588, by rfl⟩ : syracuseStep 2217569 = 1663177) B1663177
theorem B4986467 : Blo 1476558 4986467 := bstep (se 1 (by rfl) ⟨3739850, by rfl⟩ : syracuseStep 4986467 = 7479701) B7479701
theorem B2217587 : Blo 1476558 2217587 := bstep (se 1 (by rfl) ⟨1663190, by rfl⟩ : syracuseStep 2217587 = 3326381) B3326381
theorem B3323537 : Blo 1476558 3323537 := bstep (se 2 (by rfl) ⟨1246326, by rfl⟩ : syracuseStep 3323537 = 2492653) B2492653
theorem B3741329 : Blo 1476558 3741329 := bstep (se 2 (by rfl) ⟨1402998, by rfl⟩ : syracuseStep 3741329 = 2805997) B2805997
theorem B2217617 : Blo 1476558 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B3323555 : Blo 1476558 3323555 := bstep (se 1 (by rfl) ⟨2492666, by rfl⟩ : syracuseStep 3323555 = 4985333) B4985333
theorem B2217635 : Blo 1476558 2217635 := bstep (se 1 (by rfl) ⟨1663226, by rfl⟩ : syracuseStep 2217635 = 3326453) B3326453
theorem B2217665 : Blo 1476558 2217665 := bstep (se 2 (by rfl) ⟨831624, by rfl⟩ : syracuseStep 2217665 = 1663249) B1663249
theorem B2217683 : Blo 1476558 2217683 := bstep (se 1 (by rfl) ⟨1663262, by rfl⟩ : syracuseStep 2217683 = 3326525) B3326525
theorem B2217713 : Blo 1476558 2217713 := bstep (se 2 (by rfl) ⟨831642, by rfl⟩ : syracuseStep 2217713 = 1663285) B1663285
theorem B1775363 : Blo 1476558 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B2217731 : Blo 1476558 2217731 := bstep (se 1 (by rfl) ⟨1663298, by rfl⟩ : syracuseStep 2217731 = 3326597) B3326597
theorem B8419085 : Blo 1476558 8419085 := bstep (se 3 (by rfl) ⟨1578578, by rfl⟩ : syracuseStep 8419085 = 3157157) B3157157
theorem B2217761 : Blo 1476558 2217761 := bstep (se 2 (by rfl) ⟨831660, by rfl⟩ : syracuseStep 2217761 = 1663321) B1663321
theorem B15980341 : Blo 1476558 15980341 := bstep (se 5 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 15980341 = 1498157) B1498157
theorem B2217779 : Blo 1476558 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B7198541 : Blo 1476558 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B2217809 : Blo 1476558 2217809 := bstep (se 2 (by rfl) ⟨831678, by rfl⟩ : syracuseStep 2217809 = 1663357) B1663357
theorem B2217827 : Blo 1476558 2217827 := bstep (se 1 (by rfl) ⟨1663370, by rfl⟩ : syracuseStep 2217827 = 3326741) B3326741
theorem B4986737 : Blo 1476558 4986737 := bstep (se 2 (by rfl) ⟨1870026, by rfl⟩ : syracuseStep 4986737 = 3740053) B3740053
theorem B2398097 : Blo 1476558 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B4495277 : Blo 1476558 4495277 := bstep (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) B1685729
theorem B3323825 : Blo 1476558 3323825 := bstep (se 2 (by rfl) ⟨1246434, by rfl⟩ : syracuseStep 3323825 = 2492869) B2492869
theorem B3323843 : Blo 1476558 3323843 := bstep (se 1 (by rfl) ⟨2492882, by rfl⟩ : syracuseStep 3323843 = 4985765) B4985765
theorem B17962993 : Blo 1476558 17962993 := bstep (se 2 (by rfl) ⟨6736122, by rfl⟩ : syracuseStep 17962993 = 13472245) B13472245
theorem B4732931 : Blo 1476558 4732931 := bstep (se 1 (by rfl) ⟨3549698, by rfl⟩ : syracuseStep 4732931 = 7099397) B7099397
theorem B8100017 : Blo 1476558 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B3324113 : Blo 1476558 3324113 := bstep (se 2 (by rfl) ⟨1246542, by rfl⟩ : syracuseStep 3324113 = 2493085) B2493085
theorem B8411363 : Blo 1476558 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B3324131 : Blo 1476558 3324131 := bstep (se 1 (by rfl) ⟨2493098, by rfl⟩ : syracuseStep 3324131 = 4986197) B4986197
theorem B1661251 : Blo 1476558 1661251 := bstep (se 1 (by rfl) ⟨1245938, by rfl⟩ : syracuseStep 1661251 = 2491877) B2491877
theorem B4987277 : Blo 1476558 4987277 := bstep (se 3 (by rfl) ⟨935114, by rfl⟩ : syracuseStep 4987277 = 1870229) B1870229
theorem B4987331 : Blo 1476558 4987331 := bstep (se 1 (by rfl) ⟨3740498, by rfl⟩ : syracuseStep 4987331 = 7480997) B7480997
theorem B1661395 : Blo 1476558 1661395 := bstep (se 1 (by rfl) ⟨1246046, by rfl⟩ : syracuseStep 1661395 = 2492093) B2492093
theorem B2365907 : Blo 1476558 2365907 := bstep (se 1 (by rfl) ⟨1774430, by rfl⟩ : syracuseStep 2365907 = 3548861) B3548861
theorem B3324401 : Blo 1476558 3324401 := bstep (se 2 (by rfl) ⟨1246650, by rfl⟩ : syracuseStep 3324401 = 2493301) B2493301
theorem B3996145 : Blo 1476558 3996145 := bstep (se 2 (by rfl) ⟨1498554, by rfl⟩ : syracuseStep 3996145 = 2997109) B2997109
theorem B3324419 : Blo 1476558 3324419 := bstep (se 1 (by rfl) ⟨2493314, by rfl⟩ : syracuseStep 3324419 = 4986629) B4986629
theorem B4209155 : Blo 1476558 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B11983373 : Blo 1476558 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B2365985 : Blo 1476558 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B5610019 : Blo 1476558 5610019 := bstep (se 1 (by rfl) ⟨4207514, by rfl⟩ : syracuseStep 5610019 = 8415029) B8415029
theorem B4266541 : Blo 1476558 4266541 := bstep (se 3 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 4266541 = 1599953) B1599953
theorem B2103889 : Blo 1476558 2103889 := bstep (se 2 (by rfl) ⟨788958, by rfl⟩ : syracuseStep 2103889 = 1577917) B1577917
theorem B1661539 : Blo 1476558 1661539 := bstep (se 1 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 1661539 = 2492309) B2492309
theorem B3742321 : Blo 1476558 3742321 := bstep (se 2 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 3742321 = 2806741) B2806741
theorem B16841357 : Blo 1476558 16841357 := bstep (se 3 (by rfl) ⟨3157754, by rfl⟩ : syracuseStep 16841357 = 6315509) B6315509
theorem B2996881 : Blo 1476558 2996881 := bstep (se 2 (by rfl) ⟨1123830, by rfl⟩ : syracuseStep 2996881 = 2247661) B2247661
theorem B2103985 : Blo 1476558 2103985 := bstep (se 2 (by rfl) ⟨788994, by rfl⟩ : syracuseStep 2103985 = 1577989) B1577989
theorem B4987601 : Blo 1476558 4987601 := bstep (se 2 (by rfl) ⟨1870350, by rfl⟩ : syracuseStep 4987601 = 3740701) B3740701
theorem B1661683 : Blo 1476558 1661683 := bstep (se 1 (by rfl) ⟨1246262, by rfl⟩ : syracuseStep 1661683 = 2492525) B2492525
theorem B2366209 : Blo 1476558 2366209 := bstep (se 2 (by rfl) ⟨887328, by rfl⟩ : syracuseStep 2366209 = 1774657) B1774657
theorem B3324689 : Blo 1476558 3324689 := bstep (se 2 (by rfl) ⟨1246758, by rfl⟩ : syracuseStep 3324689 = 2493517) B2493517
theorem B3324707 : Blo 1476558 3324707 := bstep (se 1 (by rfl) ⟨2493530, by rfl⟩ : syracuseStep 3324707 = 4987061) B4987061
theorem B1661827 : Blo 1476558 1661827 := bstep (se 1 (by rfl) ⟨1246370, by rfl⟩ : syracuseStep 1661827 = 2492741) B2492741
theorem B3742595 : Blo 1476558 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B7478243 : Blo 1476558 7478243 := bstep (se 1 (by rfl) ⟨5608682, by rfl⟩ : syracuseStep 7478243 = 11217365) B11217365
theorem B13147121 : Blo 1476558 13147121 := bstep (se 2 (by rfl) ⟨4930170, by rfl⟩ : syracuseStep 13147121 = 9860341) B9860341
theorem B1661971 : Blo 1476558 1661971 := bstep (se 1 (by rfl) ⟨1246478, by rfl⟩ : syracuseStep 1661971 = 2492957) B2492957
theorem B3324977 : Blo 1476558 3324977 := bstep (se 2 (by rfl) ⟨1246866, by rfl⟩ : syracuseStep 3324977 = 2493733) B2493733
theorem B3324995 : Blo 1476558 3324995 := bstep (se 1 (by rfl) ⟨2493746, by rfl⟩ : syracuseStep 3324995 = 4987493) B4987493
theorem B2997329 : Blo 1476558 2997329 := bstep (se 2 (by rfl) ⟨1123998, by rfl⟩ : syracuseStep 2997329 = 2247997) B2247997
theorem B3792017 : Blo 1476558 3792017 := bstep (se 2 (by rfl) ⟨1422006, by rfl⟩ : syracuseStep 3792017 = 2844013) B2844013
theorem B2104481 : Blo 1476558 2104481 := bstep (se 2 (by rfl) ⟨789180, by rfl⟩ : syracuseStep 2104481 = 1578361) B1578361
theorem B1662115 : Blo 1476558 1662115 := bstep (se 1 (by rfl) ⟨1246586, by rfl⟩ : syracuseStep 1662115 = 2493173) B2493173
theorem B4988141 : Blo 1476558 4988141 := bstep (se 3 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 4988141 = 1870553) B1870553
theorem B4988195 : Blo 1476558 4988195 := bstep (se 1 (by rfl) ⟨3741146, by rfl⟩ : syracuseStep 4988195 = 7482293) B7482293
theorem B4209965 : Blo 1476558 4209965 := bstep (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) B1578737
theorem B1662259 : Blo 1476558 1662259 := bstep (se 1 (by rfl) ⟨1246694, by rfl⟩ : syracuseStep 1662259 = 2493389) B2493389
theorem B3325265 : Blo 1476558 3325265 := bstep (se 2 (by rfl) ⟨1246974, by rfl⟩ : syracuseStep 3325265 = 2493949) B2493949
theorem B5684579 : Blo 1476558 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B3325283 : Blo 1476558 3325283 := bstep (se 1 (by rfl) ⟨2493962, by rfl⟩ : syracuseStep 3325283 = 4987925) B4987925
theorem B1498547 : Blo 1476558 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B1662403 : Blo 1476558 1662403 := bstep (se 1 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 1662403 = 2493605) B2493605
theorem B4210157 : Blo 1476558 4210157 := bstep (se 3 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 4210157 = 1578809) B1578809
theorem B4988465 : Blo 1476558 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B1662547 : Blo 1476558 1662547 := bstep (se 1 (by rfl) ⟨1246910, by rfl⟩ : syracuseStep 1662547 = 2493821) B2493821
theorem B11214449 : Blo 1476558 11214449 := bstep (se 2 (by rfl) ⟨4205418, by rfl⟩ : syracuseStep 11214449 = 8410837) B8410837
theorem B3325553 : Blo 1476558 3325553 := bstep (se 2 (by rfl) ⟨1247082, by rfl⟩ : syracuseStep 3325553 = 2494165) B2494165
theorem B3325571 : Blo 1476558 3325571 := bstep (se 1 (by rfl) ⟨2494178, by rfl⟩ : syracuseStep 3325571 = 4988357) B4988357
theorem B1662691 : Blo 1476558 1662691 := bstep (se 1 (by rfl) ⟨1247018, by rfl⟩ : syracuseStep 1662691 = 2494037) B2494037
theorem B7479053 : Blo 1476558 7479053 := bstep (se 3 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 7479053 = 2804645) B2804645
theorem B4734737 : Blo 1476558 4734737 := bstep (se 2 (by rfl) ⟨1775526, by rfl⟩ : syracuseStep 4734737 = 3551053) B3551053
theorem B4734787 : Blo 1476558 4734787 := bstep (se 1 (by rfl) ⟨3551090, by rfl⟩ : syracuseStep 4734787 = 7102181) B7102181
theorem B2400083 : Blo 1476558 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B1662835 : Blo 1476558 1662835 := bstep (se 1 (by rfl) ⟨1247126, by rfl⟩ : syracuseStep 1662835 = 2494253) B2494253
theorem B3153809 : Blo 1476558 3153809 := bstep (se 2 (by rfl) ⟨1182678, by rfl⟩ : syracuseStep 3153809 = 2365357) B2365357
theorem B3325841 : Blo 1476558 3325841 := bstep (se 2 (by rfl) ⟨1247190, by rfl⟩ : syracuseStep 3325841 = 2494381) B2494381
theorem B3325859 : Blo 1476558 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B9461681 : Blo 1476558 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B2662411 : Blo 1476558 2662411 := bstep (se 1 (by rfl) ⟨1996808, by rfl⟩ : syracuseStep 2662411 = 3993617) B3993617
theorem B4988951 : Blo 1476558 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B3326003 : Blo 1476558 3326003 := bstep (se 1 (by rfl) ⟨2494502, by rfl⟩ : syracuseStep 3326003 = 4989005) B4989005
theorem B1663051 : Blo 1476558 1663051 := bstep (se 1 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 1663051 = 2494577) B2494577
theorem B3326039 : Blo 1476558 3326039 := bstep (se 1 (by rfl) ⟨2494529, by rfl⟩ : syracuseStep 3326039 = 4989059) B4989059
theorem B3154099 : Blo 1476558 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B1663159 : Blo 1476558 1663159 := bstep (se 1 (by rfl) ⟨1247369, by rfl⟩ : syracuseStep 1663159 = 2494739) B2494739
theorem B3326219 : Blo 1476558 3326219 := bstep (se 1 (by rfl) ⟨2494664, by rfl⟩ : syracuseStep 3326219 = 4989329) B4989329
theorem B8986925 : Blo 1476558 8986925 := bstep (se 3 (by rfl) ⟨1685048, by rfl⟩ : syracuseStep 8986925 = 3370097) B3370097
theorem B3326273 : Blo 1476558 3326273 := bstep (se 2 (by rfl) ⟨1247352, by rfl⟩ : syracuseStep 3326273 = 2494705) B2494705
theorem B1663339 : Blo 1476558 1663339 := bstep (se 1 (by rfl) ⟨1247504, by rfl⟩ : syracuseStep 1663339 = 2495009) B2495009
theorem B8413571 : Blo 1476558 8413571 := bstep (se 1 (by rfl) ⟨6310178, by rfl⟩ : syracuseStep 8413571 = 12620357) B12620357
theorem B5611949 : Blo 1476558 5611949 := bstep (se 3 (by rfl) ⟨1052240, by rfl⟩ : syracuseStep 5611949 = 2104481) B2104481
theorem B3326489 : Blo 1476558 3326489 := bstep (se 2 (by rfl) ⟨1247433, by rfl⟩ : syracuseStep 3326489 = 2494867) B2494867
theorem B4989491 : Blo 1476558 4989491 := bstep (se 1 (by rfl) ⟨3742118, by rfl⟩ : syracuseStep 4989491 = 7484237) B7484237
theorem B48611933 : Blo 1476558 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B3326579 : Blo 1476558 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B11223683 : Blo 1476558 11223683 := bstep (se 1 (by rfl) ⟨8417762, by rfl⟩ : syracuseStep 11223683 = 16835525) B16835525
theorem B3326615 : Blo 1476558 3326615 := bstep (se 1 (by rfl) ⟨2494961, by rfl⟩ : syracuseStep 3326615 = 4989923) B4989923
theorem B7480025 : Blo 1476558 7480025 := bstep (se 2 (by rfl) ⟨2805009, by rfl⟩ : syracuseStep 7480025 = 5610019) B5610019
theorem B4989761 : Blo 1476558 4989761 := bstep (se 2 (by rfl) ⟨1871160, by rfl⟩ : syracuseStep 4989761 = 3742321) B3742321
theorem B8414027 : Blo 1476558 8414027 := bstep (se 1 (by rfl) ⟨6310520, by rfl⟩ : syracuseStep 8414027 = 12621041) B12621041
theorem B3154945 : Blo 1476558 3154945 := bstep (se 2 (by rfl) ⟨1183104, by rfl⟩ : syracuseStep 3154945 = 2366209) B2366209
theorem B11215907 : Blo 1476558 11215907 := bstep (se 1 (by rfl) ⟨8411930, by rfl⟩ : syracuseStep 11215907 = 16823861) B16823861
theorem B5612723 : Blo 1476558 5612723 := bstep (se 1 (by rfl) ⟨4209542, by rfl⟩ : syracuseStep 5612723 = 8419085) B8419085
theorem B6309085 : Blo 1476558 6309085 := bstep (se 3 (by rfl) ⟨1182953, by rfl⟩ : syracuseStep 6309085 = 2365907) B2365907
theorem B31950125 : Blo 1476558 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B28411181 : Blo 1476558 28411181 := bstep (se 3 (by rfl) ⟨5327096, by rfl⟩ : syracuseStep 28411181 = 10654193) B10654193
theorem B2491735 : Blo 1476558 2491735 := bstep (se 1 (by rfl) ⟨1868801, by rfl⟩ : syracuseStep 2491735 = 3737603) B3737603
theorem B3155287 : Blo 1476558 3155287 := bstep (se 1 (by rfl) ⟨2366465, by rfl⟩ : syracuseStep 3155287 = 4732931) B4732931
theorem B5400011 : Blo 1476558 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B2246105 : Blo 1476558 2246105 := bstep (se 2 (by rfl) ⟨842289, by rfl⟩ : syracuseStep 2246105 = 1684579) B1684579
theorem B2803187 : Blo 1476558 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B6309427 : Blo 1476558 6309427 := bstep (se 1 (by rfl) ⟨4732070, by rfl⟩ : syracuseStep 6309427 = 9464141) B9464141
theorem B2803339 : Blo 1476558 2803339 := bstep (se 1 (by rfl) ⟨2102504, by rfl⟩ : syracuseStep 2803339 = 4205009) B4205009
theorem B7988915 : Blo 1476558 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B35923661 : Blo 1476558 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B5326667 : Blo 1476558 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B2492363 : Blo 1476558 2492363 := bstep (se 1 (by rfl) ⟨1869272, by rfl⟩ : syracuseStep 2492363 = 3738545) B3738545
theorem B1476567 : Blo 1476558 1476567 := bstep (se 1 (by rfl) ⟨1107425, by rfl⟩ : syracuseStep 1476567 = 2214851) B2214851
theorem B2803673 : Blo 1476558 2803673 := bstep (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) B2102755
theorem B1476587 : Blo 1476558 1476587 := bstep (se 1 (by rfl) ⟨1107440, by rfl⟩ : syracuseStep 1476587 = 2214881) B2214881
theorem B1476599 : Blo 1476558 1476599 := bstep (se 1 (by rfl) ⟨1107449, by rfl⟩ : syracuseStep 1476599 = 2214899) B2214899
theorem B1476619 : Blo 1476558 1476619 := bstep (se 1 (by rfl) ⟨1107464, by rfl⟩ : syracuseStep 1476619 = 2214929) B2214929
theorem B7096337 : Blo 1476558 7096337 := bstep (se 2 (by rfl) ⟨2661126, by rfl⟩ : syracuseStep 7096337 = 5322253) B5322253
theorem B3737623 : Blo 1476558 3737623 := bstep (se 1 (by rfl) ⟨2803217, by rfl⟩ : syracuseStep 3737623 = 5606435) B5606435
theorem B1476631 : Blo 1476558 1476631 := bstep (se 1 (by rfl) ⟨1107473, by rfl⟩ : syracuseStep 1476631 = 2214947) B2214947
theorem B1476651 : Blo 1476558 1476651 := bstep (se 1 (by rfl) ⟨1107488, by rfl⟩ : syracuseStep 1476651 = 2214977) B2214977
theorem B1476663 : Blo 1476558 1476663 := bstep (se 1 (by rfl) ⟨1107497, by rfl⟩ : syracuseStep 1476663 = 2214995) B2214995
theorem B1476683 : Blo 1476558 1476683 := bstep (se 1 (by rfl) ⟨1107512, by rfl⟩ : syracuseStep 1476683 = 2215025) B2215025
theorem B2492491 : Blo 1476558 2492491 := bstep (se 1 (by rfl) ⟨1869368, by rfl⟩ : syracuseStep 2492491 = 3738737) B3738737
theorem B1476695 : Blo 1476558 1476695 := bstep (se 1 (by rfl) ⟨1107521, by rfl⟩ : syracuseStep 1476695 = 2215043) B2215043
theorem B1476715 : Blo 1476558 1476715 := bstep (se 1 (by rfl) ⟨1107536, by rfl⟩ : syracuseStep 1476715 = 2215073) B2215073
theorem B1476727 : Blo 1476558 1476727 := bstep (se 1 (by rfl) ⟨1107545, by rfl⟩ : syracuseStep 1476727 = 2215091) B2215091
theorem B1476747 : Blo 1476558 1476747 := bstep (se 1 (by rfl) ⟨1107560, by rfl⟩ : syracuseStep 1476747 = 2215121) B2215121
theorem B1476759 : Blo 1476558 1476759 := bstep (se 1 (by rfl) ⟨1107569, by rfl⟩ : syracuseStep 1476759 = 2215139) B2215139
theorem B1476779 : Blo 1476558 1476779 := bstep (se 1 (by rfl) ⟨1107584, by rfl⟩ : syracuseStep 1476779 = 2215169) B2215169
theorem B1476791 : Blo 1476558 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B1476811 : Blo 1476558 1476811 := bstep (se 1 (by rfl) ⟨1107608, by rfl⟩ : syracuseStep 1476811 = 2215217) B2215217
theorem B1476823 : Blo 1476558 1476823 := bstep (se 1 (by rfl) ⟨1107617, by rfl⟩ : syracuseStep 1476823 = 2215235) B2215235
theorem B2492633 : Blo 1476558 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B1476843 : Blo 1476558 1476843 := bstep (se 1 (by rfl) ⟨1107632, by rfl⟩ : syracuseStep 1476843 = 2215265) B2215265
theorem B1476855 : Blo 1476558 1476855 := bstep (se 1 (by rfl) ⟨1107641, by rfl⟩ : syracuseStep 1476855 = 2215283) B2215283
theorem B1476875 : Blo 1476558 1476875 := bstep (se 1 (by rfl) ⟨1107656, by rfl⟩ : syracuseStep 1476875 = 2215313) B2215313
theorem B7989521 : Blo 1476558 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B1476887 : Blo 1476558 1476887 := bstep (se 1 (by rfl) ⟨1107665, by rfl⟩ : syracuseStep 1476887 = 2215331) B2215331
theorem B1476907 : Blo 1476558 1476907 := bstep (se 1 (by rfl) ⟨1107680, by rfl⟩ : syracuseStep 1476907 = 2215361) B2215361
theorem B7481645 : Blo 1476558 7481645 := bstep (se 3 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 7481645 = 2805617) B2805617
theorem B1476919 : Blo 1476558 1476919 := bstep (se 1 (by rfl) ⟨1107689, by rfl⟩ : syracuseStep 1476919 = 2215379) B2215379
theorem B1476939 : Blo 1476558 1476939 := bstep (se 1 (by rfl) ⟨1107704, by rfl⟩ : syracuseStep 1476939 = 2215409) B2215409
theorem B1476951 : Blo 1476558 1476951 := bstep (se 1 (by rfl) ⟨1107713, by rfl⟩ : syracuseStep 1476951 = 2215427) B2215427
theorem B4262233 : Blo 1476558 4262233 := bstep (se 2 (by rfl) ⟨1598337, by rfl⟩ : syracuseStep 4262233 = 3196675) B3196675
theorem B2492761 : Blo 1476558 2492761 := bstep (se 2 (by rfl) ⟨934785, by rfl⟩ : syracuseStep 2492761 = 1869571) B1869571
theorem B1476971 : Blo 1476558 1476971 := bstep (se 1 (by rfl) ⟨1107728, by rfl⟩ : syracuseStep 1476971 = 2215457) B2215457
theorem B63883637 : Blo 1476558 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B1476983 : Blo 1476558 1476983 := bstep (se 1 (by rfl) ⟨1107737, by rfl⟩ : syracuseStep 1476983 = 2215475) B2215475
theorem B1477003 : Blo 1476558 1477003 := bstep (se 1 (by rfl) ⟨1107752, by rfl⟩ : syracuseStep 1477003 = 2215505) B2215505
theorem B1870219 : Blo 1476558 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B1477015 : Blo 1476558 1477015 := bstep (se 1 (by rfl) ⟨1107761, by rfl⟩ : syracuseStep 1477015 = 2215523) B2215523
theorem B1477035 : Blo 1476558 1477035 := bstep (se 1 (by rfl) ⟨1107776, by rfl⟩ : syracuseStep 1477035 = 2215553) B2215553
theorem B1477047 : Blo 1476558 1477047 := bstep (se 1 (by rfl) ⟨1107785, by rfl⟩ : syracuseStep 1477047 = 2215571) B2215571
theorem B3738059 : Blo 1476558 3738059 := bstep (se 1 (by rfl) ⟨2803544, by rfl⟩ : syracuseStep 3738059 = 5607089) B5607089
theorem B1477067 : Blo 1476558 1477067 := bstep (se 1 (by rfl) ⟨1107800, by rfl⟩ : syracuseStep 1477067 = 2215601) B2215601
theorem B1477079 : Blo 1476558 1477079 := bstep (se 1 (by rfl) ⟨1107809, by rfl⟩ : syracuseStep 1477079 = 2215619) B2215619
theorem B1477099 : Blo 1476558 1477099 := bstep (se 1 (by rfl) ⟨1107824, by rfl⟩ : syracuseStep 1477099 = 2215649) B2215649
theorem B1477111 : Blo 1476558 1477111 := bstep (se 1 (by rfl) ⟨1107833, by rfl⟩ : syracuseStep 1477111 = 2215667) B2215667
theorem B1477131 : Blo 1476558 1477131 := bstep (se 1 (by rfl) ⟨1107848, by rfl⟩ : syracuseStep 1477131 = 2215697) B2215697
theorem B3156491 : Blo 1476558 3156491 := bstep (se 1 (by rfl) ⟨2367368, by rfl⟩ : syracuseStep 3156491 = 4734737) B4734737
theorem B1477143 : Blo 1476558 1477143 := bstep (se 1 (by rfl) ⟨1107857, by rfl⟩ : syracuseStep 1477143 = 2215715) B2215715
theorem B17975843 : Blo 1476558 17975843 := bstep (se 1 (by rfl) ⟨13481882, by rfl⟩ : syracuseStep 17975843 = 26963765) B26963765
theorem B1477163 : Blo 1476558 1477163 := bstep (se 1 (by rfl) ⟨1107872, by rfl⟩ : syracuseStep 1477163 = 2215745) B2215745
theorem B1477175 : Blo 1476558 1477175 := bstep (se 1 (by rfl) ⟨1107881, by rfl⟩ : syracuseStep 1477175 = 2215763) B2215763
theorem B1477195 : Blo 1476558 1477195 := bstep (se 1 (by rfl) ⟨1107896, by rfl⟩ : syracuseStep 1477195 = 2215793) B2215793
theorem B2804311 : Blo 1476558 2804311 := bstep (se 1 (by rfl) ⟨2103233, by rfl⟩ : syracuseStep 2804311 = 4206467) B4206467
theorem B1477207 : Blo 1476558 1477207 := bstep (se 1 (by rfl) ⟨1107905, by rfl⟩ : syracuseStep 1477207 = 2215811) B2215811
theorem B4983389 : Blo 1476558 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B1477227 : Blo 1476558 1477227 := bstep (se 1 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 1477227 = 2215841) B2215841
theorem B1477239 : Blo 1476558 1477239 := bstep (se 1 (by rfl) ⟨1107929, by rfl⟩ : syracuseStep 1477239 = 2215859) B2215859
theorem B1477259 : Blo 1476558 1477259 := bstep (se 1 (by rfl) ⟨1107944, by rfl⟩ : syracuseStep 1477259 = 2215889) B2215889
theorem B1477271 : Blo 1476558 1477271 := bstep (se 1 (by rfl) ⟨1107953, by rfl⟩ : syracuseStep 1477271 = 2215907) B2215907
theorem B1477291 : Blo 1476558 1477291 := bstep (se 1 (by rfl) ⟨1107968, by rfl⟩ : syracuseStep 1477291 = 2215937) B2215937
theorem B8096435 : Blo 1476558 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B6400691 : Blo 1476558 6400691 := bstep (se 1 (by rfl) ⟨4800518, by rfl⟩ : syracuseStep 6400691 = 9601037) B9601037
theorem B1477303 : Blo 1476558 1477303 := bstep (se 1 (by rfl) ⟨1107977, by rfl⟩ : syracuseStep 1477303 = 2215955) B2215955
theorem B1477323 : Blo 1476558 1477323 := bstep (se 1 (by rfl) ⟨1107992, by rfl⟩ : syracuseStep 1477323 = 2215985) B2215985
theorem B1477335 : Blo 1476558 1477335 := bstep (se 1 (by rfl) ⟨1108001, by rfl⟩ : syracuseStep 1477335 = 2216003) B2216003
theorem B1477355 : Blo 1476558 1477355 := bstep (se 1 (by rfl) ⟨1108016, by rfl⟩ : syracuseStep 1477355 = 2216033) B2216033
theorem B25242353 : Blo 1476558 25242353 := bstep (se 2 (by rfl) ⟨9465882, by rfl⟩ : syracuseStep 25242353 = 18931765) B18931765
theorem B1477367 : Blo 1476558 1477367 := bstep (se 1 (by rfl) ⟨1108025, by rfl⟩ : syracuseStep 1477367 = 2216051) B2216051
theorem B1477387 : Blo 1476558 1477387 := bstep (se 1 (by rfl) ⟨1108040, by rfl⟩ : syracuseStep 1477387 = 2216081) B2216081
theorem B1477399 : Blo 1476558 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B2132761 : Blo 1476558 2132761 := bstep (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) B1599571
theorem B1477419 : Blo 1476558 1477419 := bstep (se 1 (by rfl) ⟨1108064, by rfl⟩ : syracuseStep 1477419 = 2216129) B2216129
theorem B1477431 : Blo 1476558 1477431 := bstep (se 1 (by rfl) ⟨1108073, by rfl⟩ : syracuseStep 1477431 = 2216147) B2216147
theorem B3738433 : Blo 1476558 3738433 := bstep (se 2 (by rfl) ⟨1401912, by rfl⟩ : syracuseStep 3738433 = 2803825) B2803825
theorem B1477451 : Blo 1476558 1477451 := bstep (se 1 (by rfl) ⟨1108088, by rfl⟩ : syracuseStep 1477451 = 2216177) B2216177
theorem B1477463 : Blo 1476558 1477463 := bstep (se 1 (by rfl) ⟨1108097, by rfl⟩ : syracuseStep 1477463 = 2216195) B2216195
theorem B2132825 : Blo 1476558 2132825 := bstep (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) B1599619
theorem B1477483 : Blo 1476558 1477483 := bstep (se 1 (by rfl) ⟨1108112, by rfl⟩ : syracuseStep 1477483 = 2216225) B2216225
theorem B1477495 : Blo 1476558 1477495 := bstep (se 1 (by rfl) ⟨1108121, by rfl⟩ : syracuseStep 1477495 = 2216243) B2216243
theorem B5991299 : Blo 1476558 5991299 := bstep (se 1 (by rfl) ⟨4493474, by rfl⟩ : syracuseStep 5991299 = 8986949) B8986949
theorem B1477515 : Blo 1476558 1477515 := bstep (se 1 (by rfl) ⟨1108136, by rfl⟩ : syracuseStep 1477515 = 2216273) B2216273
theorem B1477527 : Blo 1476558 1477527 := bstep (se 1 (by rfl) ⟨1108145, by rfl⟩ : syracuseStep 1477527 = 2216291) B2216291
theorem B2493335 : Blo 1476558 2493335 := bstep (se 1 (by rfl) ⟨1870001, by rfl⟩ : syracuseStep 2493335 = 3740003) B3740003
theorem B1477547 : Blo 1476558 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B1477559 : Blo 1476558 1477559 := bstep (se 1 (by rfl) ⟨1108169, by rfl⟩ : syracuseStep 1477559 = 2216339) B2216339
theorem B1477579 : Blo 1476558 1477579 := bstep (se 1 (by rfl) ⟨1108184, by rfl⟩ : syracuseStep 1477579 = 2216369) B2216369
theorem B1477591 : Blo 1476558 1477591 := bstep (se 1 (by rfl) ⟨1108193, by rfl⟩ : syracuseStep 1477591 = 2216387) B2216387
theorem B4205533 : Blo 1476558 4205533 := bstep (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) B1577075
theorem B1477611 : Blo 1476558 1477611 := bstep (se 1 (by rfl) ⟨1108208, by rfl⟩ : syracuseStep 1477611 = 2216417) B2216417
theorem B1477623 : Blo 1476558 1477623 := bstep (se 1 (by rfl) ⟨1108217, by rfl⟩ : syracuseStep 1477623 = 2216435) B2216435
theorem B2214923 : Blo 1476558 2214923 := bstep (se 1 (by rfl) ⟨1661192, by rfl⟩ : syracuseStep 2214923 = 3322385) B3322385
theorem B1477643 : Blo 1476558 1477643 := bstep (se 1 (by rfl) ⟨1108232, by rfl⟩ : syracuseStep 1477643 = 2216465) B2216465
theorem B3157003 : Blo 1476558 3157003 := bstep (se 1 (by rfl) ⟨2367752, by rfl⟩ : syracuseStep 3157003 = 4735505) B4735505
theorem B63933461 : Blo 1476558 63933461 := bstep (se 6 (by rfl) ⟨1498440, by rfl⟩ : syracuseStep 63933461 = 2996881) B2996881
theorem B2214935 : Blo 1476558 2214935 := bstep (se 1 (by rfl) ⟨1661201, by rfl⟩ : syracuseStep 2214935 = 3322403) B3322403
theorem B4205591 : Blo 1476558 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B2493463 : Blo 1476558 2493463 := bstep (se 1 (by rfl) ⟨1870097, by rfl⟩ : syracuseStep 2493463 = 3740195) B3740195
theorem B1477655 : Blo 1476558 1477655 := bstep (se 1 (by rfl) ⟨1108241, by rfl⟩ : syracuseStep 1477655 = 2216483) B2216483
theorem B1477675 : Blo 1476558 1477675 := bstep (se 1 (by rfl) ⟨1108256, by rfl⟩ : syracuseStep 1477675 = 2216513) B2216513
theorem B8981549 : Blo 1476558 8981549 := bstep (se 3 (by rfl) ⟨1684040, by rfl⟩ : syracuseStep 8981549 = 3368081) B3368081
theorem B1477687 : Blo 1476558 1477687 := bstep (se 1 (by rfl) ⟨1108265, by rfl⟩ : syracuseStep 1477687 = 2216531) B2216531
theorem B13470785 : Blo 1476558 13470785 := bstep (se 2 (by rfl) ⟨5051544, by rfl⟩ : syracuseStep 13470785 = 10103089) B10103089
theorem B1477707 : Blo 1476558 1477707 := bstep (se 1 (by rfl) ⟨1108280, by rfl⟩ : syracuseStep 1477707 = 2216561) B2216561
theorem B1477719 : Blo 1476558 1477719 := bstep (se 1 (by rfl) ⟨1108289, by rfl⟩ : syracuseStep 1477719 = 2216579) B2216579
theorem B2215001 : Blo 1476558 2215001 := bstep (se 2 (by rfl) ⟨830625, by rfl⟩ : syracuseStep 2215001 = 1661251) B1661251
theorem B3992665 : Blo 1476558 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B1477739 : Blo 1476558 1477739 := bstep (se 1 (by rfl) ⟨1108304, by rfl⟩ : syracuseStep 1477739 = 2216609) B2216609
theorem B1477751 : Blo 1476558 1477751 := bstep (se 1 (by rfl) ⟨1108313, by rfl⟩ : syracuseStep 1477751 = 2216627) B2216627
theorem B1477771 : Blo 1476558 1477771 := bstep (se 1 (by rfl) ⟨1108328, by rfl⟩ : syracuseStep 1477771 = 2216657) B2216657
theorem B1477783 : Blo 1476558 1477783 := bstep (se 1 (by rfl) ⟨1108337, by rfl⟩ : syracuseStep 1477783 = 2216675) B2216675
theorem B1477803 : Blo 1476558 1477803 := bstep (se 1 (by rfl) ⟨1108352, by rfl⟩ : syracuseStep 1477803 = 2216705) B2216705
theorem B1477815 : Blo 1476558 1477815 := bstep (se 1 (by rfl) ⟨1108361, by rfl⟩ : syracuseStep 1477815 = 2216723) B2216723
theorem B5606603 : Blo 1476558 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B2215115 : Blo 1476558 2215115 := bstep (se 1 (by rfl) ⟨1661336, by rfl⟩ : syracuseStep 2215115 = 3322673) B3322673
theorem B1477835 : Blo 1476558 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B2215127 : Blo 1476558 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B5606617 : Blo 1476558 5606617 := bstep (se 2 (by rfl) ⟨2102481, by rfl⟩ : syracuseStep 5606617 = 4204963) B4204963
theorem B1477847 : Blo 1476558 1477847 := bstep (se 1 (by rfl) ⟨1108385, by rfl⟩ : syracuseStep 1477847 = 2216771) B2216771
theorem B1477867 : Blo 1476558 1477867 := bstep (se 1 (by rfl) ⟨1108400, by rfl⟩ : syracuseStep 1477867 = 2216801) B2216801
theorem B1477879 : Blo 1476558 1477879 := bstep (se 1 (by rfl) ⟨1108409, by rfl⟩ : syracuseStep 1477879 = 2216819) B2216819
theorem B1477899 : Blo 1476558 1477899 := bstep (se 1 (by rfl) ⟨1108424, by rfl⟩ : syracuseStep 1477899 = 2216849) B2216849
theorem B1477911 : Blo 1476558 1477911 := bstep (se 1 (by rfl) ⟨1108433, by rfl⟩ : syracuseStep 1477911 = 2216867) B2216867
theorem B2215193 : Blo 1476558 2215193 := bstep (se 2 (by rfl) ⟨830697, by rfl⟩ : syracuseStep 2215193 = 1661395) B1661395
theorem B1477931 : Blo 1476558 1477931 := bstep (se 1 (by rfl) ⟨1108448, by rfl⟩ : syracuseStep 1477931 = 2216897) B2216897
theorem B1477943 : Blo 1476558 1477943 := bstep (se 1 (by rfl) ⟨1108457, by rfl⟩ : syracuseStep 1477943 = 2216915) B2216915
theorem B3288385 : Blo 1476558 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B5328193 : Blo 1476558 5328193 := bstep (se 2 (by rfl) ⟨1998072, by rfl⟩ : syracuseStep 5328193 = 3996145) B3996145
theorem B1477963 : Blo 1476558 1477963 := bstep (se 1 (by rfl) ⟨1108472, by rfl⟩ : syracuseStep 1477963 = 2216945) B2216945
theorem B1477975 : Blo 1476558 1477975 := bstep (se 1 (by rfl) ⟨1108481, by rfl⟩ : syracuseStep 1477975 = 2216963) B2216963
theorem B1871191 : Blo 1476558 1871191 := bstep (se 1 (by rfl) ⟨1403393, by rfl⟩ : syracuseStep 1871191 = 2806787) B2806787
theorem B1477995 : Blo 1476558 1477995 := bstep (se 1 (by rfl) ⟨1108496, by rfl⟩ : syracuseStep 1477995 = 2216993) B2216993
theorem B1478007 : Blo 1476558 1478007 := bstep (se 1 (by rfl) ⟨1108505, by rfl⟩ : syracuseStep 1478007 = 2217011) B2217011
theorem B2215307 : Blo 1476558 2215307 := bstep (se 1 (by rfl) ⟨1661480, by rfl⟩ : syracuseStep 2215307 = 3322961) B3322961
theorem B2805131 : Blo 1476558 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B1478027 : Blo 1476558 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B5688721 : Blo 1476558 5688721 := bstep (se 2 (by rfl) ⟨2133270, by rfl⟩ : syracuseStep 5688721 = 4266541) B4266541
theorem B2215319 : Blo 1476558 2215319 := bstep (se 1 (by rfl) ⟨1661489, by rfl⟩ : syracuseStep 2215319 = 3322979) B3322979
theorem B3739031 : Blo 1476558 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B1478039 : Blo 1476558 1478039 := bstep (se 1 (by rfl) ⟨1108529, by rfl⟩ : syracuseStep 1478039 = 2217059) B2217059
theorem B1478059 : Blo 1476558 1478059 := bstep (se 1 (by rfl) ⟨1108544, by rfl⟩ : syracuseStep 1478059 = 2217089) B2217089
theorem B1478071 : Blo 1476558 1478071 := bstep (se 1 (by rfl) ⟨1108553, by rfl⟩ : syracuseStep 1478071 = 2217107) B2217107
theorem B2805185 : Blo 1476558 2805185 := bstep (se 2 (by rfl) ⟨1051944, by rfl⟩ : syracuseStep 2805185 = 2103889) B2103889
theorem B1478091 : Blo 1476558 1478091 := bstep (se 1 (by rfl) ⟨1108568, by rfl⟩ : syracuseStep 1478091 = 2217137) B2217137
theorem B102403541 : Blo 1476558 102403541 := bstep (se 7 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 102403541 = 2400083) B2400083
theorem B1478103 : Blo 1476558 1478103 := bstep (se 1 (by rfl) ⟨1108577, by rfl⟩ : syracuseStep 1478103 = 2217155) B2217155
theorem B2215385 : Blo 1476558 2215385 := bstep (se 2 (by rfl) ⟨830769, by rfl⟩ : syracuseStep 2215385 = 1661539) B1661539
theorem B1478123 : Blo 1476558 1478123 := bstep (se 1 (by rfl) ⟨1108592, by rfl⟩ : syracuseStep 1478123 = 2217185) B2217185
theorem B1478135 : Blo 1476558 1478135 := bstep (se 1 (by rfl) ⟨1108601, by rfl⟩ : syracuseStep 1478135 = 2217203) B2217203
theorem B1478155 : Blo 1476558 1478155 := bstep (se 1 (by rfl) ⟨1108616, by rfl⟩ : syracuseStep 1478155 = 2217233) B2217233
theorem B1478167 : Blo 1476558 1478167 := bstep (se 1 (by rfl) ⟨1108625, by rfl⟩ : syracuseStep 1478167 = 2217251) B2217251
theorem B1478187 : Blo 1476558 1478187 := bstep (se 1 (by rfl) ⟨1108640, by rfl⟩ : syracuseStep 1478187 = 2217281) B2217281
theorem B1478199 : Blo 1476558 1478199 := bstep (se 1 (by rfl) ⟨1108649, by rfl⟩ : syracuseStep 1478199 = 2217299) B2217299
theorem B2215499 : Blo 1476558 2215499 := bstep (se 1 (by rfl) ⟨1661624, by rfl⟩ : syracuseStep 2215499 = 3323249) B3323249
theorem B1478219 : Blo 1476558 1478219 := bstep (se 1 (by rfl) ⟨1108664, by rfl⟩ : syracuseStep 1478219 = 2217329) B2217329
theorem B2215511 : Blo 1476558 2215511 := bstep (se 1 (by rfl) ⟨1661633, by rfl⟩ : syracuseStep 2215511 = 3323267) B3323267
theorem B1478231 : Blo 1476558 1478231 := bstep (se 1 (by rfl) ⟨1108673, by rfl⟩ : syracuseStep 1478231 = 2217347) B2217347
theorem B1478251 : Blo 1476558 1478251 := bstep (se 1 (by rfl) ⟨1108688, by rfl⟩ : syracuseStep 1478251 = 2217377) B2217377
theorem B1478263 : Blo 1476558 1478263 := bstep (se 1 (by rfl) ⟨1108697, by rfl⟩ : syracuseStep 1478263 = 2217395) B2217395
theorem B2494091 : Blo 1476558 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1478283 : Blo 1476558 1478283 := bstep (se 1 (by rfl) ⟨1108712, by rfl⟩ : syracuseStep 1478283 = 2217425) B2217425
theorem B1478295 : Blo 1476558 1478295 := bstep (se 1 (by rfl) ⟨1108721, by rfl⟩ : syracuseStep 1478295 = 2217443) B2217443
theorem B2215577 : Blo 1476558 2215577 := bstep (se 2 (by rfl) ⟨830841, by rfl⟩ : syracuseStep 2215577 = 1661683) B1661683
theorem B1478315 : Blo 1476558 1478315 := bstep (se 1 (by rfl) ⟨1108736, by rfl⟩ : syracuseStep 1478315 = 2217473) B2217473
theorem B1478327 : Blo 1476558 1478327 := bstep (se 1 (by rfl) ⟨1108745, by rfl⟩ : syracuseStep 1478327 = 2217491) B2217491
theorem B4984523 : Blo 1476558 4984523 := bstep (se 1 (by rfl) ⟨3738392, by rfl⟩ : syracuseStep 4984523 = 7476785) B7476785
theorem B14192333 : Blo 1476558 14192333 := bstep (se 3 (by rfl) ⟨2661062, by rfl⟩ : syracuseStep 14192333 = 5322125) B5322125
theorem B1478347 : Blo 1476558 1478347 := bstep (se 1 (by rfl) ⟨1108760, by rfl⟩ : syracuseStep 1478347 = 2217521) B2217521
theorem B2133707 : Blo 1476558 2133707 := bstep (se 1 (by rfl) ⟨1600280, by rfl⟩ : syracuseStep 2133707 = 3200561) B3200561
theorem B1478359 : Blo 1476558 1478359 := bstep (se 1 (by rfl) ⟨1108769, by rfl⟩ : syracuseStep 1478359 = 2217539) B2217539
theorem B3157721 : Blo 1476558 3157721 := bstep (se 2 (by rfl) ⟨1184145, by rfl⟩ : syracuseStep 3157721 = 2368291) B2368291
theorem B1478379 : Blo 1476558 1478379 := bstep (se 1 (by rfl) ⟨1108784, by rfl⟩ : syracuseStep 1478379 = 2217569) B2217569
theorem B1478391 : Blo 1476558 1478391 := bstep (se 1 (by rfl) ⟨1108793, by rfl⟩ : syracuseStep 1478391 = 2217587) B2217587
theorem B2215691 : Blo 1476558 2215691 := bstep (se 1 (by rfl) ⟨1661768, by rfl⟩ : syracuseStep 2215691 = 3323537) B3323537
theorem B2494219 : Blo 1476558 2494219 := bstep (se 1 (by rfl) ⟨1870664, by rfl⟩ : syracuseStep 2494219 = 3741329) B3741329
theorem B1478411 : Blo 1476558 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B2215703 : Blo 1476558 2215703 := bstep (se 1 (by rfl) ⟨1661777, by rfl⟩ : syracuseStep 2215703 = 3323555) B3323555
theorem B1478423 : Blo 1476558 1478423 := bstep (se 1 (by rfl) ⟨1108817, by rfl⟩ : syracuseStep 1478423 = 2217635) B2217635
theorem B1478443 : Blo 1476558 1478443 := bstep (se 1 (by rfl) ⟨1108832, by rfl⟩ : syracuseStep 1478443 = 2217665) B2217665
theorem B1478455 : Blo 1476558 1478455 := bstep (se 1 (by rfl) ⟨1108841, by rfl⟩ : syracuseStep 1478455 = 2217683) B2217683
theorem B1478475 : Blo 1476558 1478475 := bstep (se 1 (by rfl) ⟨1108856, by rfl⟩ : syracuseStep 1478475 = 2217713) B2217713
theorem B1478487 : Blo 1476558 1478487 := bstep (se 1 (by rfl) ⟨1108865, by rfl⟩ : syracuseStep 1478487 = 2217731) B2217731
theorem B2215769 : Blo 1476558 2215769 := bstep (se 2 (by rfl) ⟨830913, by rfl⟩ : syracuseStep 2215769 = 1661827) B1661827
theorem B1478507 : Blo 1476558 1478507 := bstep (se 1 (by rfl) ⟨1108880, by rfl⟩ : syracuseStep 1478507 = 2217761) B2217761
theorem B1478519 : Blo 1476558 1478519 := bstep (se 1 (by rfl) ⟨1108889, by rfl⟩ : syracuseStep 1478519 = 2217779) B2217779
theorem B9465731 : Blo 1476558 9465731 := bstep (se 1 (by rfl) ⟨7099298, by rfl⟩ : syracuseStep 9465731 = 14198597) B14198597
theorem B1478539 : Blo 1476558 1478539 := bstep (se 1 (by rfl) ⟨1108904, by rfl⟩ : syracuseStep 1478539 = 2217809) B2217809
theorem B1478551 : Blo 1476558 1478551 := bstep (se 1 (by rfl) ⟨1108913, by rfl⟩ : syracuseStep 1478551 = 2217827) B2217827
theorem B2494361 : Blo 1476558 2494361 := bstep (se 2 (by rfl) ⟨935385, by rfl⟩ : syracuseStep 2494361 = 1870771) B1870771
theorem B2215883 : Blo 1476558 2215883 := bstep (se 1 (by rfl) ⟨1661912, by rfl⟩ : syracuseStep 2215883 = 3323825) B3323825
theorem B11227085 : Blo 1476558 11227085 := bstep (se 3 (by rfl) ⟨2105078, by rfl⟩ : syracuseStep 11227085 = 4210157) B4210157
theorem B2215895 : Blo 1476558 2215895 := bstep (se 1 (by rfl) ⟨1661921, by rfl⟩ : syracuseStep 2215895 = 3323843) B3323843
theorem B4984793 : Blo 1476558 4984793 := bstep (se 2 (by rfl) ⟨1869297, by rfl⟩ : syracuseStep 4984793 = 3738595) B3738595
theorem B2215961 : Blo 1476558 2215961 := bstep (se 2 (by rfl) ⟨830985, by rfl⟩ : syracuseStep 2215961 = 1661971) B1661971
theorem B2494489 : Blo 1476558 2494489 := bstep (se 2 (by rfl) ⟨935433, by rfl⟩ : syracuseStep 2494489 = 1870867) B1870867
theorem B3551321 : Blo 1476558 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B16822403 : Blo 1476558 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B2216075 : Blo 1476558 2216075 := bstep (se 1 (by rfl) ⟨1662056, by rfl⟩ : syracuseStep 2216075 = 3324113) B3324113
theorem B5607575 : Blo 1476558 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B2216087 : Blo 1476558 2216087 := bstep (se 1 (by rfl) ⟨1662065, by rfl⟩ : syracuseStep 2216087 = 3324131) B3324131
theorem B3739841 : Blo 1476558 3739841 := bstep (se 2 (by rfl) ⟨1402440, by rfl⟩ : syracuseStep 3739841 = 2804881) B2804881
theorem B4206809 : Blo 1476558 4206809 := bstep (se 2 (by rfl) ⟨1577553, by rfl⟩ : syracuseStep 4206809 = 3155107) B3155107
theorem B2216153 : Blo 1476558 2216153 := bstep (se 2 (by rfl) ⟨831057, by rfl⟩ : syracuseStep 2216153 = 1662115) B1662115
theorem B4206923 : Blo 1476558 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B2216267 : Blo 1476558 2216267 := bstep (se 1 (by rfl) ⟨1662200, by rfl⟩ : syracuseStep 2216267 = 3324401) B3324401
theorem B2216279 : Blo 1476558 2216279 := bstep (se 1 (by rfl) ⟨1662209, by rfl⟩ : syracuseStep 2216279 = 3324419) B3324419
theorem B2806103 : Blo 1476558 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B1577323 : Blo 1476558 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B2216345 : Blo 1476558 2216345 := bstep (se 2 (by rfl) ⟨831129, by rfl⟩ : syracuseStep 2216345 = 1662259) B1662259
theorem B11227571 : Blo 1476558 11227571 := bstep (se 1 (by rfl) ⟨8420678, by rfl⟩ : syracuseStep 11227571 = 16841357) B16841357
theorem B2216459 : Blo 1476558 2216459 := bstep (se 1 (by rfl) ⟨1662344, by rfl⟩ : syracuseStep 2216459 = 3324689) B3324689
theorem B2216471 : Blo 1476558 2216471 := bstep (se 1 (by rfl) ⟨1662353, by rfl⟩ : syracuseStep 2216471 = 3324707) B3324707
theorem B2495063 : Blo 1476558 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B3322457 : Blo 1476558 3322457 := bstep (se 2 (by rfl) ⟨1245921, by rfl⟩ : syracuseStep 3322457 = 2491843) B2491843
theorem B2216537 : Blo 1476558 2216537 := bstep (se 2 (by rfl) ⟨831201, by rfl⟩ : syracuseStep 2216537 = 1662403) B1662403
theorem B4264541 : Blo 1476558 4264541 := bstep (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) B1599203
theorem B4985495 : Blo 1476558 4985495 := bstep (se 1 (by rfl) ⟨3739121, by rfl⟩ : syracuseStep 4985495 = 7478243) B7478243
theorem B3322547 : Blo 1476558 3322547 := bstep (se 1 (by rfl) ⟨2491910, by rfl⟩ : syracuseStep 3322547 = 4983821) B4983821
theorem B2216651 : Blo 1476558 2216651 := bstep (se 1 (by rfl) ⟨1662488, by rfl⟩ : syracuseStep 2216651 = 3324977) B3324977
theorem B3322583 : Blo 1476558 3322583 := bstep (se 1 (by rfl) ⟨2491937, by rfl⟩ : syracuseStep 3322583 = 4983875) B4983875
theorem B3740377 : Blo 1476558 3740377 := bstep (se 2 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 3740377 = 2805283) B2805283
theorem B2216663 : Blo 1476558 2216663 := bstep (se 1 (by rfl) ⟨1662497, by rfl⟩ : syracuseStep 2216663 = 3324995) B3324995
theorem B2528011 : Blo 1476558 2528011 := bstep (se 1 (by rfl) ⟨1896008, by rfl⟩ : syracuseStep 2528011 = 3792017) B3792017
theorem B2216729 : Blo 1476558 2216729 := bstep (se 2 (by rfl) ⟨831273, by rfl⟩ : syracuseStep 2216729 = 1662547) B1662547
theorem B4494145 : Blo 1476558 4494145 := bstep (se 2 (by rfl) ⟨1685304, by rfl⟩ : syracuseStep 4494145 = 3370609) B3370609
theorem B2806643 : Blo 1476558 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B3322763 : Blo 1476558 3322763 := bstep (se 1 (by rfl) ⟨2492072, by rfl⟩ : syracuseStep 3322763 = 4984145) B4984145
theorem B2216843 : Blo 1476558 2216843 := bstep (se 1 (by rfl) ⟨1662632, by rfl⟩ : syracuseStep 2216843 = 3325265) B3325265
theorem B3789719 : Blo 1476558 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B2216855 : Blo 1476558 2216855 := bstep (se 1 (by rfl) ⟨1662641, by rfl⟩ : syracuseStep 2216855 = 3325283) B3325283
theorem B3322817 : Blo 1476558 3322817 := bstep (se 2 (by rfl) ⟨1246056, by rfl⟩ : syracuseStep 3322817 = 2492113) B2492113
theorem B10793945 : Blo 1476558 10793945 := bstep (se 2 (by rfl) ⟨4047729, by rfl⟩ : syracuseStep 10793945 = 8095459) B8095459
theorem B2216921 : Blo 1476558 2216921 := bstep (se 2 (by rfl) ⟨831345, by rfl⟩ : syracuseStep 2216921 = 1662691) B1662691
theorem B6394925 : Blo 1476558 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B7476299 : Blo 1476558 7476299 := bstep (se 1 (by rfl) ⟨5607224, by rfl⟩ : syracuseStep 7476299 = 11214449) B11214449
theorem B2217035 : Blo 1476558 2217035 := bstep (se 1 (by rfl) ⟨1662776, by rfl⟩ : syracuseStep 2217035 = 3325553) B3325553
theorem B2217047 : Blo 1476558 2217047 := bstep (se 1 (by rfl) ⟨1662785, by rfl⟩ : syracuseStep 2217047 = 3325571) B3325571
theorem B6313049 : Blo 1476558 6313049 := bstep (se 2 (by rfl) ⟨2367393, by rfl⟩ : syracuseStep 6313049 = 4734787) B4734787
theorem B3323033 : Blo 1476558 3323033 := bstep (se 2 (by rfl) ⟨1246137, by rfl⟩ : syracuseStep 3323033 = 2492275) B2492275
theorem B2217113 : Blo 1476558 2217113 := bstep (se 2 (by rfl) ⟨831417, by rfl⟩ : syracuseStep 2217113 = 1662835) B1662835
theorem B4986035 : Blo 1476558 4986035 := bstep (se 1 (by rfl) ⟨3739526, by rfl⟩ : syracuseStep 4986035 = 7479053) B7479053
theorem B35042485 : Blo 1476558 35042485 := bstep (se 5 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 35042485 = 3285233) B3285233
theorem B3323123 : Blo 1476558 3323123 := bstep (se 1 (by rfl) ⟨2492342, by rfl⟩ : syracuseStep 3323123 = 4984685) B4984685
theorem B2102539 : Blo 1476558 2102539 := bstep (se 1 (by rfl) ⟨1576904, by rfl⟩ : syracuseStep 2102539 = 3153809) B3153809
theorem B2217227 : Blo 1476558 2217227 := bstep (se 1 (by rfl) ⟨1662920, by rfl⟩ : syracuseStep 2217227 = 3325841) B3325841
theorem B3323159 : Blo 1476558 3323159 := bstep (se 1 (by rfl) ⟨2492369, by rfl⟩ : syracuseStep 3323159 = 4984739) B4984739
theorem B2217239 : Blo 1476558 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B35058989 : Blo 1476558 35058989 := bstep (se 3 (by rfl) ⟨6573560, by rfl⟩ : syracuseStep 35058989 = 13147121) B13147121
theorem B23950657 : Blo 1476558 23950657 := bstep (se 2 (by rfl) ⟨8981496, by rfl⟩ : syracuseStep 23950657 = 17962993) B17962993
theorem B2217305 : Blo 1476558 2217305 := bstep (se 2 (by rfl) ⟨831489, by rfl⟩ : syracuseStep 2217305 = 1662979) B1662979
theorem B8418653 : Blo 1476558 8418653 := bstep (se 3 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 8418653 = 3156995) B3156995
theorem B1684843 : Blo 1476558 1684843 := bstep (se 1 (by rfl) ⟨1263632, by rfl⟩ : syracuseStep 1684843 = 2527265) B2527265
theorem B5608835 : Blo 1476558 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B7583107 : Blo 1476558 7583107 := bstep (se 1 (by rfl) ⟨5687330, by rfl⟩ : syracuseStep 7583107 = 11374661) B11374661
theorem B4617623 : Blo 1476558 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B4208051 : Blo 1476558 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B4986305 : Blo 1476558 4986305 := bstep (se 2 (by rfl) ⟨1869864, by rfl⟩ : syracuseStep 4986305 = 3739729) B3739729
theorem B3323339 : Blo 1476558 3323339 := bstep (se 1 (by rfl) ⟨2492504, by rfl⟩ : syracuseStep 3323339 = 4985009) B4985009
theorem B2217419 : Blo 1476558 2217419 := bstep (se 1 (by rfl) ⟨1663064, by rfl⟩ : syracuseStep 2217419 = 3326129) B3326129
theorem B2217431 : Blo 1476558 2217431 := bstep (se 1 (by rfl) ⟨1663073, by rfl⟩ : syracuseStep 2217431 = 3326147) B3326147
theorem B3323393 : Blo 1476558 3323393 := bstep (se 2 (by rfl) ⟨1246272, by rfl⟩ : syracuseStep 3323393 = 2492545) B2492545
theorem B2217497 : Blo 1476558 2217497 := bstep (se 2 (by rfl) ⟨831561, by rfl⟩ : syracuseStep 2217497 = 1663123) B1663123
theorem B20215331 : Blo 1476558 20215331 := bstep (se 1 (by rfl) ⟨15161498, by rfl⟩ : syracuseStep 20215331 = 30322997) B30322997
theorem B7992877 : Blo 1476558 7992877 := bstep (se 3 (by rfl) ⟨1498664, by rfl⟩ : syracuseStep 7992877 = 2997329) B2997329
theorem B4732481 : Blo 1476558 4732481 := bstep (se 2 (by rfl) ⟨1774680, by rfl⟩ : syracuseStep 4732481 = 3549361) B3549361
theorem B7198301 : Blo 1476558 7198301 := bstep (se 3 (by rfl) ⟨1349681, by rfl⟩ : syracuseStep 7198301 = 2699363) B2699363
theorem B2217611 : Blo 1476558 2217611 := bstep (se 1 (by rfl) ⟨1663208, by rfl⟩ : syracuseStep 2217611 = 3326417) B3326417
theorem B1578647 : Blo 1476558 1578647 := bstep (se 1 (by rfl) ⟨1183985, by rfl⟩ : syracuseStep 1578647 = 2367971) B2367971
theorem B2217623 : Blo 1476558 2217623 := bstep (se 1 (by rfl) ⟨1663217, by rfl⟩ : syracuseStep 2217623 = 3326435) B3326435
theorem B3323609 : Blo 1476558 3323609 := bstep (se 2 (by rfl) ⟨1246353, by rfl⟩ : syracuseStep 3323609 = 2492707) B2492707
theorem B2217689 : Blo 1476558 2217689 := bstep (se 2 (by rfl) ⟨831633, by rfl⟩ : syracuseStep 2217689 = 1663267) B1663267
theorem B12138257 : Blo 1476558 12138257 := bstep (se 2 (by rfl) ⟨4551846, by rfl⟩ : syracuseStep 12138257 = 9103693) B9103693
theorem B1578775 : Blo 1476558 1578775 := bstep (se 1 (by rfl) ⟨1184081, by rfl⟩ : syracuseStep 1578775 = 2368163) B2368163
theorem B3323699 : Blo 1476558 3323699 := bstep (se 1 (by rfl) ⟨2492774, by rfl⟩ : syracuseStep 3323699 = 4985549) B4985549
theorem B3741491 : Blo 1476558 3741491 := bstep (se 1 (by rfl) ⟨2806118, by rfl⟩ : syracuseStep 3741491 = 5612237) B5612237
theorem B4208449 : Blo 1476558 4208449 := bstep (se 2 (by rfl) ⟨1578168, by rfl⟩ : syracuseStep 4208449 = 3156337) B3156337
theorem B2217803 : Blo 1476558 2217803 := bstep (se 1 (by rfl) ⟨1663352, by rfl⟩ : syracuseStep 2217803 = 3326705) B3326705
theorem B3323735 : Blo 1476558 3323735 := bstep (se 1 (by rfl) ⟨2492801, by rfl⟩ : syracuseStep 3323735 = 4985603) B4985603
theorem B2217815 : Blo 1476558 2217815 := bstep (se 1 (by rfl) ⟨1663361, by rfl⟩ : syracuseStep 2217815 = 3326723) B3326723
theorem B3790795 : Blo 1476558 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B4986845 : Blo 1476558 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B1497079 : Blo 1476558 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B3323915 : Blo 1476558 3323915 := bstep (se 1 (by rfl) ⟨2492936, by rfl⟩ : syracuseStep 3323915 = 4985873) B4985873
theorem B3323969 : Blo 1476558 3323969 := bstep (se 2 (by rfl) ⟨1246488, by rfl⟩ : syracuseStep 3323969 = 2492977) B2492977
theorem B8419403 : Blo 1476558 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B3741785 : Blo 1476558 3741785 := bstep (se 2 (by rfl) ⟨1403169, by rfl⟩ : syracuseStep 3741785 = 2806339) B2806339
theorem B7100567 : Blo 1476558 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B12630167 : Blo 1476558 12630167 := bstep (se 1 (by rfl) ⟨9472625, by rfl⟩ : syracuseStep 12630167 = 18945251) B18945251
theorem B1661143 : Blo 1476558 1661143 := bstep (se 1 (by rfl) ⟨1245857, by rfl⟩ : syracuseStep 1661143 = 2491715) B2491715
theorem B11221253 : Blo 1476558 11221253 := bstep (se 4 (by rfl) ⟨1051992, by rfl⟩ : syracuseStep 11221253 = 2103985) B2103985
theorem B2103575 : Blo 1476558 2103575 := bstep (se 1 (by rfl) ⟨1577681, by rfl⟩ : syracuseStep 2103575 = 3155363) B3155363
theorem B3324185 : Blo 1476558 3324185 := bstep (se 2 (by rfl) ⟨1246569, by rfl⟩ : syracuseStep 3324185 = 2493139) B2493139
theorem B3324275 : Blo 1476558 3324275 := bstep (se 1 (by rfl) ⟨2493206, by rfl⟩ : syracuseStep 3324275 = 4986413) B4986413
theorem B1661323 : Blo 1476558 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B3324311 : Blo 1476558 3324311 := bstep (se 1 (by rfl) ⟨2493233, by rfl⟩ : syracuseStep 3324311 = 4986467) B4986467
theorem B2103769 : Blo 1476558 2103769 := bstep (se 2 (by rfl) ⟨788913, by rfl⟩ : syracuseStep 2103769 = 1577827) B1577827
theorem B3996125 : Blo 1476558 3996125 := bstep (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) B1498547
theorem B1661431 : Blo 1476558 1661431 := bstep (se 1 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 1661431 = 2492147) B2492147
theorem B4799027 : Blo 1476558 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B3324491 : Blo 1476558 3324491 := bstep (se 1 (by rfl) ⟨2493368, by rfl⟩ : syracuseStep 3324491 = 4986737) B4986737
theorem B2996851 : Blo 1476558 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B3324545 : Blo 1476558 3324545 := bstep (se 2 (by rfl) ⟨1246704, by rfl⟩ : syracuseStep 3324545 = 2493409) B2493409
theorem B5053079 : Blo 1476558 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B1661611 : Blo 1476558 1661611 := bstep (se 1 (by rfl) ⟨1246208, by rfl⟩ : syracuseStep 1661611 = 2492417) B2492417
theorem B6314689 : Blo 1476558 6314689 := bstep (se 2 (by rfl) ⟨2368008, by rfl⟩ : syracuseStep 6314689 = 4736017) B4736017
theorem B1661719 : Blo 1476558 1661719 := bstep (se 1 (by rfl) ⟨1246289, by rfl⟩ : syracuseStep 1661719 = 2492579) B2492579
theorem B17054509 : Blo 1476558 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B7478081 : Blo 1476558 7478081 := bstep (se 2 (by rfl) ⟨2804280, by rfl⟩ : syracuseStep 7478081 = 5608561) B5608561
theorem B3324761 : Blo 1476558 3324761 := bstep (se 2 (by rfl) ⟨1246785, by rfl⟩ : syracuseStep 3324761 = 2493571) B2493571
theorem B3324851 : Blo 1476558 3324851 := bstep (se 1 (by rfl) ⟨2493638, by rfl⟩ : syracuseStep 3324851 = 4987277) B4987277
theorem B1661899 : Blo 1476558 1661899 := bstep (se 1 (by rfl) ⟨1246424, by rfl⟩ : syracuseStep 1661899 = 2492849) B2492849
theorem B3324887 : Blo 1476558 3324887 := bstep (se 1 (by rfl) ⟨2493665, by rfl⟩ : syracuseStep 3324887 = 4987331) B4987331
theorem B1662007 : Blo 1476558 1662007 := bstep (se 1 (by rfl) ⟨1246505, by rfl⟩ : syracuseStep 1662007 = 2493011) B2493011
theorem B4987979 : Blo 1476558 4987979 := bstep (se 1 (by rfl) ⟨3740984, by rfl⟩ : syracuseStep 4987979 = 7481969) B7481969
theorem B3325067 : Blo 1476558 3325067 := bstep (se 1 (by rfl) ⟨2493800, by rfl⟩ : syracuseStep 3325067 = 4987601) B4987601
theorem B1498295 : Blo 1476558 1498295 := bstep (se 1 (by rfl) ⟨1123721, by rfl⟩ : syracuseStep 1498295 = 2247443) B2247443
theorem B3325121 : Blo 1476558 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B1662187 : Blo 1476558 1662187 := bstep (se 1 (by rfl) ⟨1246640, by rfl⟩ : syracuseStep 1662187 = 2493281) B2493281
theorem B1662295 : Blo 1476558 1662295 := bstep (se 1 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 1662295 = 2493443) B2493443
theorem B4988249 : Blo 1476558 4988249 := bstep (se 2 (by rfl) ⟨1870593, by rfl⟩ : syracuseStep 4988249 = 3741187) B3741187
theorem B4734301 : Blo 1476558 4734301 := bstep (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) B1775363
theorem B5397911 : Blo 1476558 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B3325337 : Blo 1476558 3325337 := bstep (se 2 (by rfl) ⟨1247001, by rfl⟩ : syracuseStep 3325337 = 2494003) B2494003
theorem B3325427 : Blo 1476558 3325427 := bstep (se 1 (by rfl) ⟨2494070, by rfl⟩ : syracuseStep 3325427 = 4988141) B4988141
theorem B1662475 : Blo 1476558 1662475 := bstep (se 1 (by rfl) ⟨1246856, by rfl⟩ : syracuseStep 1662475 = 2493713) B2493713
theorem B3325463 : Blo 1476558 3325463 := bstep (se 1 (by rfl) ⟨2494097, by rfl⟩ : syracuseStep 3325463 = 4988195) B4988195
theorem B1662583 : Blo 1476558 1662583 := bstep (se 1 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 1662583 = 2493875) B2493875
theorem B21290627 : Blo 1476558 21290627 := bstep (se 1 (by rfl) ⟨15967970, by rfl⟩ : syracuseStep 21290627 = 31935941) B31935941
theorem B3325643 : Blo 1476558 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B21307121 : Blo 1476558 21307121 := bstep (se 2 (by rfl) ⟨7990170, by rfl⟩ : syracuseStep 21307121 = 15980341) B15980341
theorem B3325697 : Blo 1476558 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B1662763 : Blo 1476558 1662763 := bstep (se 1 (by rfl) ⟨1247072, by rfl⟩ : syracuseStep 1662763 = 2494145) B2494145
theorem B1662871 : Blo 1476558 1662871 := bstep (se 1 (by rfl) ⟨1247153, by rfl⟩ : syracuseStep 1662871 = 2494307) B2494307
theorem B6307787 : Blo 1476558 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B3325913 : Blo 1476558 3325913 := bstep (se 2 (by rfl) ⟨1247217, by rfl⟩ : syracuseStep 3325913 = 2494435) B2494435
theorem B3325967 : Blo 1476558 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B3325985 : Blo 1476558 3325985 := bstep (se 2 (by rfl) ⟨1247244, by rfl⟩ : syracuseStep 3325985 = 2494489) B2494489
theorem B11214935 : Blo 1476558 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B9470189 : Blo 1476558 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B3326327 : Blo 1476558 3326327 := bstep (se 1 (by rfl) ⟨2494745, by rfl⟩ : syracuseStep 3326327 = 4989491) B4989491
theorem B1663375 : Blo 1476558 1663375 := bstep (se 1 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 1663375 = 2495063) B2495063
theorem B2843027 : Blo 1476558 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B32407955 : Blo 1476558 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B3326507 : Blo 1476558 3326507 := bstep (se 1 (by rfl) ⟨2494880, by rfl⟩ : syracuseStep 3326507 = 4989761) B4989761
theorem B21300083 : Blo 1476558 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B23372659 : Blo 1476558 23372659 := bstep (se 1 (by rfl) ⟨17529494, by rfl⟩ : syracuseStep 23372659 = 35058989) B35058989
theorem B18940787 : Blo 1476558 18940787 := bstep (se 1 (by rfl) ⟨14205590, by rfl⟩ : syracuseStep 18940787 = 28411181) B28411181
theorem B5612435 : Blo 1476558 5612435 := bstep (se 1 (by rfl) ⟨4209326, by rfl⟩ : syracuseStep 5612435 = 8418653) B8418653
theorem B13476887 : Blo 1476558 13476887 := bstep (se 1 (by rfl) ⟨10107665, by rfl⟩ : syracuseStep 13476887 = 20215331) B20215331
theorem B7480349 : Blo 1476558 7480349 := bstep (se 3 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 7480349 = 2805131) B2805131
theorem B2843681 : Blo 1476558 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B3154987 : Blo 1476558 3154987 := bstep (se 1 (by rfl) ⟨2366240, by rfl⟩ : syracuseStep 3154987 = 4732481) B4732481
theorem B5612935 : Blo 1476558 5612935 := bstep (se 1 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 5612935 = 8419403) B8419403
theorem B7480835 : Blo 1476558 7480835 := bstep (se 1 (by rfl) ⟨5610626, by rfl⟩ : syracuseStep 7480835 = 11221253) B11221253
theorem B2492039 : Blo 1476558 2492039 := bstep (se 1 (by rfl) ⟨1869029, by rfl⟩ : syracuseStep 2492039 = 3738059) B3738059
theorem B2664083 : Blo 1476558 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B2803385 : Blo 1476558 2803385 := bstep (se 2 (by rfl) ⟨1051269, by rfl⟩ : syracuseStep 2803385 = 2102539) B2102539
theorem B31934209 : Blo 1476558 31934209 := bstep (se 2 (by rfl) ⟨11975328, by rfl⟩ : syracuseStep 31934209 = 23950657) B23950657
theorem B7104257 : Blo 1476558 7104257 := bstep (se 2 (by rfl) ⟨2664096, by rfl⟩ : syracuseStep 7104257 = 5328193) B5328193
theorem B3368719 : Blo 1476558 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B16828235 : Blo 1476558 16828235 := bstep (se 1 (by rfl) ⟨12621176, by rfl⟩ : syracuseStep 16828235 = 25242353) B25242353
theorem B10110809 : Blo 1476558 10110809 := bstep (se 2 (by rfl) ⟨3791553, by rfl⟩ : syracuseStep 10110809 = 7583107) B7583107
theorem B1476615 : Blo 1476558 1476615 := bstep (se 1 (by rfl) ⟨1107461, by rfl⟩ : syracuseStep 1476615 = 2214923) B2214923
theorem B1476623 : Blo 1476558 1476623 := bstep (se 1 (by rfl) ⟨1107467, by rfl⟩ : syracuseStep 1476623 = 2214935) B2214935
theorem B2803727 : Blo 1476558 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B8980523 : Blo 1476558 8980523 := bstep (se 1 (by rfl) ⟨6735392, by rfl⟩ : syracuseStep 8980523 = 13470785) B13470785
theorem B1476667 : Blo 1476558 1476667 := bstep (se 1 (by rfl) ⟨1107500, by rfl⟩ : syracuseStep 1476667 = 2215001) B2215001
theorem B22759541 : Blo 1476558 22759541 := bstep (se 5 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 22759541 = 2133707) B2133707
theorem B3737735 : Blo 1476558 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B1476743 : Blo 1476558 1476743 := bstep (se 1 (by rfl) ⟨1107557, by rfl⟩ : syracuseStep 1476743 = 2215115) B2215115
theorem B1476751 : Blo 1476558 1476751 := bstep (se 1 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 1476751 = 2215127) B2215127
theorem B3737785 : Blo 1476558 3737785 := bstep (se 2 (by rfl) ⟨1401669, by rfl⟩ : syracuseStep 3737785 = 2803339) B2803339
theorem B1476795 : Blo 1476558 1476795 := bstep (se 1 (by rfl) ⟨1107596, by rfl⟩ : syracuseStep 1476795 = 2215193) B2215193
theorem B5687533 : Blo 1476558 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B1476871 : Blo 1476558 1476871 := bstep (se 1 (by rfl) ⟨1107653, by rfl⟩ : syracuseStep 1476871 = 2215307) B2215307
theorem B1476879 : Blo 1476558 1476879 := bstep (se 1 (by rfl) ⟨1107659, by rfl⟩ : syracuseStep 1476879 = 2215319) B2215319
theorem B2492687 : Blo 1476558 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B3598607 : Blo 1476558 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B1870123 : Blo 1476558 1870123 := bstep (se 1 (by rfl) ⟨1402592, by rfl⟩ : syracuseStep 1870123 = 2805185) B2805185
theorem B1476923 : Blo 1476558 1476923 := bstep (se 1 (by rfl) ⟨1107692, by rfl⟩ : syracuseStep 1476923 = 2215385) B2215385
theorem B1476999 : Blo 1476558 1476999 := bstep (se 1 (by rfl) ⟨1107749, by rfl⟩ : syracuseStep 1476999 = 2215499) B2215499
theorem B1477007 : Blo 1476558 1477007 := bstep (se 1 (by rfl) ⟨1107755, by rfl⟩ : syracuseStep 1477007 = 2215511) B2215511
theorem B1477051 : Blo 1476558 1477051 := bstep (se 1 (by rfl) ⟨1107788, by rfl⟩ : syracuseStep 1477051 = 2215577) B2215577
theorem B1477127 : Blo 1476558 1477127 := bstep (se 1 (by rfl) ⟨1107845, by rfl⟩ : syracuseStep 1477127 = 2215691) B2215691
theorem B1477135 : Blo 1476558 1477135 := bstep (se 1 (by rfl) ⟨1107851, by rfl⟩ : syracuseStep 1477135 = 2215703) B2215703
theorem B1477179 : Blo 1476558 1477179 := bstep (se 1 (by rfl) ⟨1107884, by rfl⟩ : syracuseStep 1477179 = 2215769) B2215769
theorem B6310487 : Blo 1476558 6310487 := bstep (se 1 (by rfl) ⟨4732865, by rfl⟩ : syracuseStep 6310487 = 9465731) B9465731
theorem B4205191 : Blo 1476558 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B1477255 : Blo 1476558 1477255 := bstep (se 1 (by rfl) ⟨1107941, by rfl⟩ : syracuseStep 1477255 = 2215883) B2215883
theorem B1477263 : Blo 1476558 1477263 := bstep (se 1 (by rfl) ⟨1107947, by rfl⟩ : syracuseStep 1477263 = 2215895) B2215895
theorem B3549881 : Blo 1476558 3549881 := bstep (se 2 (by rfl) ⟨1331205, by rfl⟩ : syracuseStep 3549881 = 2662411) B2662411
theorem B1477307 : Blo 1476558 1477307 := bstep (se 1 (by rfl) ⟨1107980, by rfl⟩ : syracuseStep 1477307 = 2215961) B2215961
theorem B4983497 : Blo 1476558 4983497 := bstep (se 2 (by rfl) ⟨1868811, by rfl⟩ : syracuseStep 4983497 = 3737623) B3737623
theorem B1477383 : Blo 1476558 1477383 := bstep (se 1 (by rfl) ⟨1108037, by rfl⟩ : syracuseStep 1477383 = 2216075) B2216075
theorem B3738383 : Blo 1476558 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B1477391 : Blo 1476558 1477391 := bstep (se 1 (by rfl) ⟨1108043, by rfl⟩ : syracuseStep 1477391 = 2216087) B2216087
theorem B2493227 : Blo 1476558 2493227 := bstep (se 1 (by rfl) ⟨1869920, by rfl⟩ : syracuseStep 2493227 = 3739841) B3739841
theorem B2804539 : Blo 1476558 2804539 := bstep (se 1 (by rfl) ⟨2103404, by rfl⟩ : syracuseStep 2804539 = 4206809) B4206809
theorem B1477435 : Blo 1476558 1477435 := bstep (se 1 (by rfl) ⟨1108076, by rfl⟩ : syracuseStep 1477435 = 2216153) B2216153
theorem B5991283 : Blo 1476558 5991283 := bstep (se 1 (by rfl) ⟨4493462, by rfl⟩ : syracuseStep 5991283 = 8986925) B8986925
theorem B2804615 : Blo 1476558 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B1477511 : Blo 1476558 1477511 := bstep (se 1 (by rfl) ⟨1108133, by rfl⟩ : syracuseStep 1477511 = 2216267) B2216267
theorem B1477519 : Blo 1476558 1477519 := bstep (se 1 (by rfl) ⟨1108139, by rfl⟩ : syracuseStep 1477519 = 2216279) B2216279
theorem B4205465 : Blo 1476558 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B1477563 : Blo 1476558 1477563 := bstep (se 1 (by rfl) ⟨1108172, by rfl⟩ : syracuseStep 1477563 = 2216345) B2216345
theorem B2214857 : Blo 1476558 2214857 := bstep (se 2 (by rfl) ⟨830571, by rfl⟩ : syracuseStep 2214857 = 1661143) B1661143
theorem B1477639 : Blo 1476558 1477639 := bstep (se 1 (by rfl) ⟨1108229, by rfl⟩ : syracuseStep 1477639 = 2216459) B2216459
theorem B1477647 : Blo 1476558 1477647 := bstep (se 1 (by rfl) ⟨1108235, by rfl⟩ : syracuseStep 1477647 = 2216471) B2216471
theorem B2214971 : Blo 1476558 2214971 := bstep (se 1 (by rfl) ⟨1661228, by rfl⟩ : syracuseStep 2214971 = 3322457) B3322457
theorem B1477691 : Blo 1476558 1477691 := bstep (se 1 (by rfl) ⟨1108268, by rfl⟩ : syracuseStep 1477691 = 2216537) B2216537
theorem B7482455 : Blo 1476558 7482455 := bstep (se 1 (by rfl) ⟨5611841, by rfl⟩ : syracuseStep 7482455 = 11223683) B11223683
theorem B2215031 : Blo 1476558 2215031 := bstep (se 1 (by rfl) ⟨1661273, by rfl⟩ : syracuseStep 2215031 = 3322547) B3322547
theorem B1477767 : Blo 1476558 1477767 := bstep (se 1 (by rfl) ⟨1108325, by rfl⟩ : syracuseStep 1477767 = 2216651) B2216651
theorem B2215055 : Blo 1476558 2215055 := bstep (se 1 (by rfl) ⟨1661291, by rfl⟩ : syracuseStep 2215055 = 3322583) B3322583
theorem B1477775 : Blo 1476558 1477775 := bstep (se 1 (by rfl) ⟨1108331, by rfl⟩ : syracuseStep 1477775 = 2216663) B2216663
theorem B2215097 : Blo 1476558 2215097 := bstep (se 2 (by rfl) ⟨830661, by rfl⟩ : syracuseStep 2215097 = 1661323) B1661323
theorem B2493625 : Blo 1476558 2493625 := bstep (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) B1870219
theorem B1477819 : Blo 1476558 1477819 := bstep (se 1 (by rfl) ⟨1108364, by rfl⟩ : syracuseStep 1477819 = 2216729) B2216729
theorem B1871095 : Blo 1476558 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B2215175 : Blo 1476558 2215175 := bstep (se 1 (by rfl) ⟨1661381, by rfl⟩ : syracuseStep 2215175 = 3322763) B3322763
theorem B1477895 : Blo 1476558 1477895 := bstep (se 1 (by rfl) ⟨1108421, by rfl⟩ : syracuseStep 1477895 = 2216843) B2216843
theorem B2526479 : Blo 1476558 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B1477903 : Blo 1476558 1477903 := bstep (se 1 (by rfl) ⟨1108427, by rfl⟩ : syracuseStep 1477903 = 2216855) B2216855
theorem B2805025 : Blo 1476558 2805025 := bstep (se 2 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 2805025 = 2103769) B2103769
theorem B2215211 : Blo 1476558 2215211 := bstep (se 1 (by rfl) ⟨1661408, by rfl⟩ : syracuseStep 2215211 = 3322817) B3322817
theorem B7195963 : Blo 1476558 7195963 := bstep (se 1 (by rfl) ⟨5396972, by rfl⟩ : syracuseStep 7195963 = 10793945) B10793945
theorem B1477947 : Blo 1476558 1477947 := bstep (se 1 (by rfl) ⟨1108460, by rfl⟩ : syracuseStep 1477947 = 2216921) B2216921
theorem B2215241 : Blo 1476558 2215241 := bstep (se 2 (by rfl) ⟨830715, by rfl⟩ : syracuseStep 2215241 = 1661431) B1661431
theorem B4263283 : Blo 1476558 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B4984199 : Blo 1476558 4984199 := bstep (se 1 (by rfl) ⟨3738149, by rfl⟩ : syracuseStep 4984199 = 7476299) B7476299
theorem B1478023 : Blo 1476558 1478023 := bstep (se 1 (by rfl) ⟨1108517, by rfl⟩ : syracuseStep 1478023 = 2217035) B2217035
theorem B1478031 : Blo 1476558 1478031 := bstep (se 1 (by rfl) ⟨1108523, by rfl⟩ : syracuseStep 1478031 = 2217047) B2217047
theorem B2215355 : Blo 1476558 2215355 := bstep (se 1 (by rfl) ⟨1661516, by rfl⟩ : syracuseStep 2215355 = 3323033) B3323033
theorem B1478075 : Blo 1476558 1478075 := bstep (se 1 (by rfl) ⟨1108556, by rfl⟩ : syracuseStep 1478075 = 2217113) B2217113
theorem B3739081 : Blo 1476558 3739081 := bstep (se 2 (by rfl) ⟨1402155, by rfl⟩ : syracuseStep 3739081 = 2804311) B2804311
theorem B2215415 : Blo 1476558 2215415 := bstep (se 1 (by rfl) ⟨1661561, by rfl⟩ : syracuseStep 2215415 = 3323123) B3323123
theorem B1478151 : Blo 1476558 1478151 := bstep (se 1 (by rfl) ⟨1108613, by rfl⟩ : syracuseStep 1478151 = 2217227) B2217227
theorem B2215439 : Blo 1476558 2215439 := bstep (se 1 (by rfl) ⟨1661579, by rfl⟩ : syracuseStep 2215439 = 3323159) B3323159
theorem B1478159 : Blo 1476558 1478159 := bstep (se 1 (by rfl) ⟨1108619, by rfl⟩ : syracuseStep 1478159 = 2217239) B2217239
theorem B2215481 : Blo 1476558 2215481 := bstep (se 2 (by rfl) ⟨830805, by rfl⟩ : syracuseStep 2215481 = 1661611) B1661611
theorem B1478203 : Blo 1476558 1478203 := bstep (se 1 (by rfl) ⟨1108652, by rfl⟩ : syracuseStep 1478203 = 2217305) B2217305
theorem B7482941 : Blo 1476558 7482941 := bstep (se 3 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 7482941 = 2806103) B2806103
theorem B3739223 : Blo 1476558 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B2805367 : Blo 1476558 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B2215559 : Blo 1476558 2215559 := bstep (se 1 (by rfl) ⟨1661669, by rfl⟩ : syracuseStep 2215559 = 3323339) B3323339
theorem B3600007 : Blo 1476558 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B1478279 : Blo 1476558 1478279 := bstep (se 1 (by rfl) ⟨1108709, by rfl⟩ : syracuseStep 1478279 = 2217419) B2217419
theorem B1478287 : Blo 1476558 1478287 := bstep (se 1 (by rfl) ⟨1108715, by rfl⟩ : syracuseStep 1478287 = 2217431) B2217431
theorem B2215595 : Blo 1476558 2215595 := bstep (se 1 (by rfl) ⟨1661696, by rfl⟩ : syracuseStep 2215595 = 3323393) B3323393
theorem B3370681 : Blo 1476558 3370681 := bstep (se 2 (by rfl) ⟨1264005, by rfl⟩ : syracuseStep 3370681 = 2528011) B2528011
theorem B1478331 : Blo 1476558 1478331 := bstep (se 1 (by rfl) ⟨1108748, by rfl⟩ : syracuseStep 1478331 = 2217497) B2217497
theorem B2215625 : Blo 1476558 2215625 := bstep (se 2 (by rfl) ⟨830859, by rfl⟩ : syracuseStep 2215625 = 1661719) B1661719
theorem B4984577 : Blo 1476558 4984577 := bstep (se 2 (by rfl) ⟨1869216, by rfl⟩ : syracuseStep 4984577 = 3738433) B3738433
theorem B5992193 : Blo 1476558 5992193 := bstep (se 2 (by rfl) ⟨2247072, by rfl⟩ : syracuseStep 5992193 = 4494145) B4494145
theorem B1478407 : Blo 1476558 1478407 := bstep (se 1 (by rfl) ⟨1108805, by rfl⟩ : syracuseStep 1478407 = 2217611) B2217611
theorem B1478415 : Blo 1476558 1478415 := bstep (se 1 (by rfl) ⟨1108811, by rfl⟩ : syracuseStep 1478415 = 2217623) B2217623
theorem B23949107 : Blo 1476558 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B2215739 : Blo 1476558 2215739 := bstep (se 1 (by rfl) ⟨1661804, by rfl⟩ : syracuseStep 2215739 = 3323609) B3323609
theorem B1478459 : Blo 1476558 1478459 := bstep (se 1 (by rfl) ⟨1108844, by rfl⟩ : syracuseStep 1478459 = 2217689) B2217689
theorem B2215799 : Blo 1476558 2215799 := bstep (se 1 (by rfl) ⟨1661849, by rfl⟩ : syracuseStep 2215799 = 3323699) B3323699
theorem B2494327 : Blo 1476558 2494327 := bstep (se 1 (by rfl) ⟨1870745, by rfl⟩ : syracuseStep 2494327 = 3741491) B3741491
theorem B3551111 : Blo 1476558 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B1478535 : Blo 1476558 1478535 := bstep (se 1 (by rfl) ⟨1108901, by rfl⟩ : syracuseStep 1478535 = 2217803) B2217803
theorem B2215823 : Blo 1476558 2215823 := bstep (se 1 (by rfl) ⟨1661867, by rfl⟩ : syracuseStep 2215823 = 3323735) B3323735
theorem B1478543 : Blo 1476558 1478543 := bstep (se 1 (by rfl) ⟨1108907, by rfl⟩ : syracuseStep 1478543 = 2217815) B2217815
theorem B2215865 : Blo 1476558 2215865 := bstep (se 2 (by rfl) ⟨830949, by rfl⟩ : syracuseStep 2215865 = 1661899) B1661899
theorem B5607377 : Blo 1476558 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B7475165 : Blo 1476558 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B4206593 : Blo 1476558 4206593 := bstep (se 2 (by rfl) ⟨1577472, by rfl⟩ : syracuseStep 4206593 = 3154945) B3154945
theorem B2215943 : Blo 1476558 2215943 := bstep (se 1 (by rfl) ⟨1661957, by rfl⟩ : syracuseStep 2215943 = 3323915) B3323915
theorem B4730891 : Blo 1476558 4730891 := bstep (se 1 (by rfl) ⟨3548168, by rfl⟩ : syracuseStep 4730891 = 7096337) B7096337
theorem B2215979 : Blo 1476558 2215979 := bstep (se 1 (by rfl) ⟨1661984, by rfl⟩ : syracuseStep 2215979 = 3323969) B3323969
theorem B2494523 : Blo 1476558 2494523 := bstep (se 1 (by rfl) ⟨1870892, by rfl⟩ : syracuseStep 2494523 = 3741785) B3741785
theorem B2216009 : Blo 1476558 2216009 := bstep (se 2 (by rfl) ⟨831003, by rfl⟩ : syracuseStep 2216009 = 1662007) B1662007
theorem B2216123 : Blo 1476558 2216123 := bstep (se 1 (by rfl) ⟨1662092, by rfl⟩ : syracuseStep 2216123 = 3324185) B3324185
theorem B46723313 : Blo 1476558 46723313 := bstep (se 2 (by rfl) ⟨17521242, by rfl⟩ : syracuseStep 46723313 = 35042485) B35042485
theorem B2216183 : Blo 1476558 2216183 := bstep (se 1 (by rfl) ⟨1662137, by rfl⟩ : syracuseStep 2216183 = 3324275) B3324275
theorem B2216207 : Blo 1476558 2216207 := bstep (se 1 (by rfl) ⟨1662155, by rfl⟩ : syracuseStep 2216207 = 3324311) B3324311
theorem B7475489 : Blo 1476558 7475489 := bstep (se 2 (by rfl) ⟨2803308, by rfl⟩ : syracuseStep 7475489 = 5606617) B5606617
theorem B2216249 : Blo 1476558 2216249 := bstep (se 2 (by rfl) ⟨831093, by rfl⟩ : syracuseStep 2216249 = 1662187) B1662187
theorem B3199351 : Blo 1476558 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B2216327 : Blo 1476558 2216327 := bstep (se 1 (by rfl) ⟨1662245, by rfl⟩ : syracuseStep 2216327 = 3324491) B3324491
theorem B3322259 : Blo 1476558 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B2216363 : Blo 1476558 2216363 := bstep (se 1 (by rfl) ⟨1662272, by rfl⟩ : syracuseStep 2216363 = 3324545) B3324545
theorem B3322313 : Blo 1476558 3322313 := bstep (se 2 (by rfl) ⟨1245867, by rfl⟩ : syracuseStep 3322313 = 2491735) B2491735
theorem B4207049 : Blo 1476558 4207049 := bstep (se 2 (by rfl) ⟨1577643, by rfl⟩ : syracuseStep 4207049 = 3155287) B3155287
theorem B2216393 : Blo 1476558 2216393 := bstep (se 2 (by rfl) ⟨831147, by rfl⟩ : syracuseStep 2216393 = 1662295) B1662295
theorem B2494921 : Blo 1476558 2494921 := bstep (se 2 (by rfl) ⟨935595, by rfl⟩ : syracuseStep 2494921 = 1871191) B1871191
theorem B6312401 : Blo 1476558 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B21303773 : Blo 1476558 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B4985387 : Blo 1476558 4985387 := bstep (se 1 (by rfl) ⟨3739040, by rfl⟩ : syracuseStep 4985387 = 7478081) B7478081
theorem B2216507 : Blo 1476558 2216507 := bstep (se 1 (by rfl) ⟨1662380, by rfl⟩ : syracuseStep 2216507 = 3324761) B3324761
theorem B3994199 : Blo 1476558 3994199 := bstep (se 1 (by rfl) ⟨2995649, by rfl⟩ : syracuseStep 3994199 = 5991299) B5991299
theorem B2216567 : Blo 1476558 2216567 := bstep (se 1 (by rfl) ⟨1662425, by rfl⟩ : syracuseStep 2216567 = 3324851) B3324851
theorem B2216591 : Blo 1476558 2216591 := bstep (se 1 (by rfl) ⟨1662443, by rfl⟩ : syracuseStep 2216591 = 3324887) B3324887
theorem B2216633 : Blo 1476558 2216633 := bstep (se 2 (by rfl) ⟨831237, by rfl⟩ : syracuseStep 2216633 = 1662475) B1662475
theorem B2216711 : Blo 1476558 2216711 := bstep (se 1 (by rfl) ⟨1662533, by rfl⟩ : syracuseStep 2216711 = 3325067) B3325067
theorem B2216747 : Blo 1476558 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B2216777 : Blo 1476558 2216777 := bstep (se 2 (by rfl) ⟨831291, by rfl⟩ : syracuseStep 2216777 = 1662583) B1662583
theorem B2216891 : Blo 1476558 2216891 := bstep (se 1 (by rfl) ⟨1662668, by rfl⟩ : syracuseStep 2216891 = 3325337) B3325337
theorem B68269027 : Blo 1476558 68269027 := bstep (se 1 (by rfl) ⟨51201770, by rfl⟩ : syracuseStep 68269027 = 102403541) B102403541
theorem B2216951 : Blo 1476558 2216951 := bstep (se 1 (by rfl) ⟨1662713, by rfl⟩ : syracuseStep 2216951 = 3325427) B3325427
theorem B2216975 : Blo 1476558 2216975 := bstep (se 1 (by rfl) ⟨1662731, by rfl⟩ : syracuseStep 2216975 = 3325463) B3325463
theorem B2217017 : Blo 1476558 2217017 := bstep (se 2 (by rfl) ⟨831381, by rfl⟩ : syracuseStep 2217017 = 1662763) B1662763
theorem B14193751 : Blo 1476558 14193751 := bstep (se 1 (by rfl) ⟨10645313, by rfl⟩ : syracuseStep 14193751 = 21290627) B21290627
theorem B3323015 : Blo 1476558 3323015 := bstep (se 1 (by rfl) ⟨2492261, by rfl⟩ : syracuseStep 3323015 = 4984523) B4984523
theorem B2217095 : Blo 1476558 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B2217131 : Blo 1476558 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B2217161 : Blo 1476558 2217161 := bstep (se 2 (by rfl) ⟨831435, by rfl⟩ : syracuseStep 2217161 = 1662871) B1662871
theorem B7476461 : Blo 1476558 7476461 := bstep (se 3 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 7476461 = 2803673) B2803673
theorem B7484723 : Blo 1476558 7484723 := bstep (se 1 (by rfl) ⟨5613542, by rfl⟩ : syracuseStep 7484723 = 11227085) B11227085
theorem B3323195 : Blo 1476558 3323195 := bstep (se 1 (by rfl) ⟨2492396, by rfl⟩ : syracuseStep 3323195 = 4984793) B4984793
theorem B2217275 : Blo 1476558 2217275 := bstep (se 1 (by rfl) ⟨1662956, by rfl⟩ : syracuseStep 2217275 = 3325913) B3325913
theorem B1996105 : Blo 1476558 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B2217335 : Blo 1476558 2217335 := bstep (se 1 (by rfl) ⟨1663001, by rfl⟩ : syracuseStep 2217335 = 3326003) B3326003
theorem B2217359 : Blo 1476558 2217359 := bstep (se 1 (by rfl) ⟨1663019, by rfl⟩ : syracuseStep 2217359 = 3326039) B3326039
theorem B3323321 : Blo 1476558 3323321 := bstep (se 2 (by rfl) ⟨1246245, by rfl⟩ : syracuseStep 3323321 = 2492491) B2492491
theorem B2217401 : Blo 1476558 2217401 := bstep (se 2 (by rfl) ⟨831525, by rfl⟩ : syracuseStep 2217401 = 1663051) B1663051
theorem B2217479 : Blo 1476558 2217479 := bstep (se 1 (by rfl) ⟨1663109, by rfl⟩ : syracuseStep 2217479 = 3326219) B3326219
theorem B2217515 : Blo 1476558 2217515 := bstep (se 1 (by rfl) ⟨1663136, by rfl⟩ : syracuseStep 2217515 = 3326273) B3326273
theorem B2217545 : Blo 1476558 2217545 := bstep (se 2 (by rfl) ⟨831579, by rfl⟩ : syracuseStep 2217545 = 1663159) B1663159
theorem B5609047 : Blo 1476558 5609047 := bstep (se 1 (by rfl) ⟨4206785, by rfl⟩ : syracuseStep 5609047 = 8413571) B8413571
theorem B3741299 : Blo 1476558 3741299 := bstep (se 1 (by rfl) ⟨2805974, by rfl⟩ : syracuseStep 3741299 = 5611949) B5611949
theorem B7485047 : Blo 1476558 7485047 := bstep (se 1 (by rfl) ⟨5613785, by rfl⟩ : syracuseStep 7485047 = 11227571) B11227571
theorem B2217659 : Blo 1476558 2217659 := bstep (se 1 (by rfl) ⟨1663244, by rfl⟩ : syracuseStep 2217659 = 3326489) B3326489
theorem B2217719 : Blo 1476558 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B3323663 : Blo 1476558 3323663 := bstep (se 1 (by rfl) ⟨2492747, by rfl⟩ : syracuseStep 3323663 = 4985495) B4985495
theorem B2217743 : Blo 1476558 2217743 := bstep (se 1 (by rfl) ⟨1663307, by rfl⟩ : syracuseStep 2217743 = 3326615) B3326615
theorem B5682977 : Blo 1476558 5682977 := bstep (se 2 (by rfl) ⟨2131116, by rfl⟩ : syracuseStep 5682977 = 4262233) B4262233
theorem B3323681 : Blo 1476558 3323681 := bstep (se 2 (by rfl) ⟨1246380, by rfl⟩ : syracuseStep 3323681 = 2492761) B2492761
theorem B2103097 : Blo 1476558 2103097 := bstep (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) B1577323
theorem B4986683 : Blo 1476558 4986683 := bstep (se 1 (by rfl) ⟨3740012, by rfl⟩ : syracuseStep 4986683 = 7480025) B7480025
theorem B3995453 : Blo 1476558 3995453 := bstep (se 3 (by rfl) ⟨749147, by rfl⟩ : syracuseStep 3995453 = 1498295) B1498295
theorem B2217785 : Blo 1476558 2217785 := bstep (se 2 (by rfl) ⟨831669, by rfl⟩ : syracuseStep 2217785 = 1663339) B1663339
theorem B5609351 : Blo 1476558 5609351 := bstep (se 1 (by rfl) ⟨4207013, by rfl⟩ : syracuseStep 5609351 = 8414027) B8414027
theorem B7477271 : Blo 1476558 7477271 := bstep (se 1 (by rfl) ⟨5607953, by rfl⟩ : syracuseStep 7477271 = 11215907) B11215907
theorem B21305389 : Blo 1476558 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B4208699 : Blo 1476558 4208699 := bstep (se 1 (by rfl) ⟨3156524, by rfl⟩ : syracuseStep 4208699 = 6313049) B6313049
theorem B5609533 : Blo 1476558 5609533 := bstep (se 3 (by rfl) ⟨1051787, by rfl⟩ : syracuseStep 5609533 = 2103575) B2103575
theorem B3324023 : Blo 1476558 3324023 := bstep (se 1 (by rfl) ⟨2493017, by rfl⟩ : syracuseStep 3324023 = 4986035) B4986035
theorem B3741815 : Blo 1476558 3741815 := bstep (se 1 (by rfl) ⟨2806361, by rfl⟩ : syracuseStep 3741815 = 5612723) B5612723
theorem B3995801 : Blo 1476558 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B8419585 : Blo 1476558 8419585 := bstep (se 2 (by rfl) ⟨3157344, by rfl⟩ : syracuseStep 8419585 = 6314689) B6314689
theorem B3078415 : Blo 1476558 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B4987169 : Blo 1476558 4987169 := bstep (se 2 (by rfl) ⟨1870188, by rfl⟩ : syracuseStep 4987169 = 3740377) B3740377
theorem B3324203 : Blo 1476558 3324203 := bstep (se 1 (by rfl) ⟨2493152, by rfl⟩ : syracuseStep 3324203 = 4986305) B4986305
theorem B1497403 : Blo 1476558 1497403 := bstep (se 1 (by rfl) ⟨1123052, by rfl⟩ : syracuseStep 1497403 = 2246105) B2246105
theorem B22739345 : Blo 1476558 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B4798867 : Blo 1476558 4798867 := bstep (se 1 (by rfl) ⟨3599150, by rfl⟩ : syracuseStep 4798867 = 7198301) B7198301
theorem B8092171 : Blo 1476558 8092171 := bstep (se 1 (by rfl) ⟨6069128, by rfl⟩ : syracuseStep 8092171 = 12138257) B12138257
theorem B1661575 : Blo 1476558 1661575 := bstep (se 1 (by rfl) ⟨1246181, by rfl⟩ : syracuseStep 1661575 = 2492363) B2492363
theorem B3324563 : Blo 1476558 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B4209337 : Blo 1476558 4209337 := bstep (se 2 (by rfl) ⟨1578501, by rfl⟩ : syracuseStep 4209337 = 3157003) B3157003
theorem B3324617 : Blo 1476558 3324617 := bstep (se 2 (by rfl) ⟨1246731, by rfl⟩ : syracuseStep 3324617 = 2493463) B2493463
theorem B4733711 : Blo 1476558 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B8420111 : Blo 1476558 8420111 := bstep (se 1 (by rfl) ⟨6315083, by rfl⟩ : syracuseStep 8420111 = 12630167) B12630167
theorem B5323553 : Blo 1476558 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B1661755 : Blo 1476558 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B4987763 : Blo 1476558 4987763 := bstep (se 1 (by rfl) ⟨3740822, by rfl⟩ : syracuseStep 4987763 = 7481645) B7481645
theorem B42589091 : Blo 1476558 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B8412113 : Blo 1476558 8412113 := bstep (se 2 (by rfl) ⟨3154542, by rfl⟩ : syracuseStep 8412113 = 6309085) B6309085
theorem B17538053 : Blo 1476558 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B2104327 : Blo 1476558 2104327 := bstep (se 1 (by rfl) ⟨1578245, by rfl⟩ : syracuseStep 2104327 = 3156491) B3156491
theorem B11983895 : Blo 1476558 11983895 := bstep (se 1 (by rfl) ⟨8987921, by rfl⟩ : syracuseStep 11983895 = 17975843) B17975843
theorem B4209725 : Blo 1476558 4209725 := bstep (se 3 (by rfl) ⟨789323, by rfl⟩ : syracuseStep 4209725 = 1578647) B1578647
theorem B5397623 : Blo 1476558 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B4267127 : Blo 1476558 4267127 := bstep (se 1 (by rfl) ⟨3200345, by rfl⟩ : syracuseStep 4267127 = 6400691) B6400691
theorem B7584961 : Blo 1476558 7584961 := bstep (se 2 (by rfl) ⟨2844360, by rfl⟩ : syracuseStep 7584961 = 5688721) B5688721
theorem B8985829 : Blo 1476558 8985829 := bstep (se 4 (by rfl) ⟨842421, by rfl⟩ : syracuseStep 8985829 = 1684843) B1684843
theorem B1662223 : Blo 1476558 1662223 := bstep (se 1 (by rfl) ⟨1246667, by rfl⟩ : syracuseStep 1662223 = 2493335) B2493335
theorem B42622307 : Blo 1476558 42622307 := bstep (se 1 (by rfl) ⟨31966730, by rfl⟩ : syracuseStep 42622307 = 63933461) B63933461
theorem B5987699 : Blo 1476558 5987699 := bstep (se 1 (by rfl) ⟨4490774, by rfl⟩ : syracuseStep 5987699 = 8981549) B8981549
theorem B3325319 : Blo 1476558 3325319 := bstep (se 1 (by rfl) ⟨2493989, by rfl⟩ : syracuseStep 3325319 = 4987979) B4987979
theorem B10657169 : Blo 1476558 10657169 := bstep (se 2 (by rfl) ⟨3996438, by rfl⟩ : syracuseStep 10657169 = 7992877) B7992877
theorem B8412569 : Blo 1476558 8412569 := bstep (se 2 (by rfl) ⟨3154713, by rfl⟩ : syracuseStep 8412569 = 6309427) B6309427
theorem B3325499 : Blo 1476558 3325499 := bstep (se 1 (by rfl) ⟨2494124, by rfl⟩ : syracuseStep 3325499 = 4988249) B4988249
theorem B3325625 : Blo 1476558 3325625 := bstep (se 2 (by rfl) ⟨1247109, by rfl⟩ : syracuseStep 3325625 = 2494219) B2494219
theorem B2105033 : Blo 1476558 2105033 := bstep (se 2 (by rfl) ⟨789387, by rfl⟩ : syracuseStep 2105033 = 1578775) B1578775
theorem B5611265 : Blo 1476558 5611265 := bstep (se 2 (by rfl) ⟨2104224, by rfl⟩ : syracuseStep 5611265 = 4208449) B4208449
theorem B1662727 : Blo 1476558 1662727 := bstep (se 1 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 1662727 = 2494091) B2494091
theorem B9461555 : Blo 1476558 9461555 := bstep (se 1 (by rfl) ⟨7096166, by rfl⟩ : syracuseStep 9461555 = 14192333) B14192333
theorem B2105147 : Blo 1476558 2105147 := bstep (se 1 (by rfl) ⟨1578860, by rfl⟩ : syracuseStep 2105147 = 3157721) B3157721
theorem B14204747 : Blo 1476558 14204747 := bstep (se 1 (by rfl) ⟨10653560, by rfl⟩ : syracuseStep 14204747 = 21307121) B21307121
theorem B5054393 : Blo 1476558 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1662907 : Blo 1476558 1662907 := bstep (se 1 (by rfl) ⟨1247180, by rfl⟩ : syracuseStep 1662907 = 2494361) B2494361
theorem B46768141 : Blo 1476558 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B12615709 : Blo 1476558 12615709 := bstep (se 3 (by rfl) ⟨2365445, by rfl⟩ : syracuseStep 12615709 = 4730891) B4730891
theorem B1663015 : Blo 1476558 1663015 := bstep (se 1 (by rfl) ⟨1247261, by rfl⟩ : syracuseStep 1663015 = 2494523) B2494523
theorem B7479377 : Blo 1476558 7479377 := bstep (se 2 (by rfl) ⟨2804766, by rfl⟩ : syracuseStep 7479377 = 5609533) B5609533
theorem B76800149 : Blo 1476558 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B11223197 : Blo 1476558 11223197 := bstep (se 3 (by rfl) ⟨2104349, by rfl⟩ : syracuseStep 11223197 = 4208699) B4208699
theorem B11379005 : Blo 1476558 11379005 := bstep (se 3 (by rfl) ⟨2133563, by rfl⟩ : syracuseStep 11379005 = 4267127) B4267127
theorem B2662799 : Blo 1476558 2662799 := bstep (se 1 (by rfl) ⟨1997099, by rfl⟩ : syracuseStep 2662799 = 3994199) B3994199
theorem B6398489 : Blo 1476558 6398489 := bstep (se 2 (by rfl) ⟨2399433, by rfl⟩ : syracuseStep 6398489 = 4798867) B4798867
theorem B3326561 : Blo 1476558 3326561 := bstep (se 2 (by rfl) ⟨1247460, by rfl⟩ : syracuseStep 3326561 = 2494921) B2494921
theorem B10789561 : Blo 1476558 10789561 := bstep (se 2 (by rfl) ⟨4046085, by rfl⟩ : syracuseStep 10789561 = 8092171) B8092171
theorem B4989815 : Blo 1476558 4989815 := bstep (se 1 (by rfl) ⟨3742361, by rfl⟩ : syracuseStep 4989815 = 7484723) B7484723
theorem B5612449 : Blo 1476558 5612449 := bstep (se 2 (by rfl) ⟨2104668, by rfl⟩ : syracuseStep 5612449 = 4209337) B4209337
theorem B4990031 : Blo 1476558 4990031 := bstep (se 1 (by rfl) ⟨3742523, by rfl⟩ : syracuseStep 4990031 = 7485047) B7485047
theorem B1868923 : Blo 1476558 1868923 := bstep (se 1 (by rfl) ⟨1401692, by rfl⟩ : syracuseStep 1868923 = 2803385) B2803385
theorem B31163545 : Blo 1476558 31163545 := bstep (se 2 (by rfl) ⟨11686329, by rfl⟩ : syracuseStep 31163545 = 23372659) B23372659
theorem B7988377 : Blo 1476558 7988377 := bstep (se 2 (by rfl) ⟨2995641, by rfl⟩ : syracuseStep 7988377 = 5991283) B5991283
theorem B4736171 : Blo 1476558 4736171 := bstep (se 1 (by rfl) ⟨3552128, by rfl⟩ : syracuseStep 4736171 = 7104257) B7104257
theorem B1869151 : Blo 1476558 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B15173027 : Blo 1476558 15173027 := bstep (se 1 (by rfl) ⟨11379770, by rfl⟩ : syracuseStep 15173027 = 22759541) B22759541
theorem B16418213 : Blo 1476558 16418213 := bstep (se 4 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 16418213 = 3078415) B3078415
theorem B2491823 : Blo 1476558 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B2663867 : Blo 1476558 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B18925001 : Blo 1476558 18925001 := bstep (se 2 (by rfl) ⟨7096875, by rfl⟩ : syracuseStep 18925001 = 14193751) B14193751
theorem B9594617 : Blo 1476558 9594617 := bstep (se 2 (by rfl) ⟨3597981, by rfl⟩ : syracuseStep 9594617 = 7195963) B7195963
theorem B2492255 : Blo 1476558 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B3155807 : Blo 1476558 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B5613407 : Blo 1476558 5613407 := bstep (se 1 (by rfl) ⟨4210055, by rfl⟩ : syracuseStep 5613407 = 8420111) B8420111
theorem B3549035 : Blo 1476558 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B5613421 : Blo 1476558 5613421 := bstep (se 3 (by rfl) ⟨1052516, by rfl⟩ : syracuseStep 5613421 = 2105033) B2105033
theorem B1869743 : Blo 1476558 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B2803643 : Blo 1476558 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B1476571 : Blo 1476558 1476571 := bstep (se 1 (by rfl) ⟨1107428, by rfl⟩ : syracuseStep 1476571 = 2214857) B2214857
theorem B7989263 : Blo 1476558 7989263 := bstep (se 1 (by rfl) ⟨5991947, by rfl⟩ : syracuseStep 7989263 = 11983895) B11983895
theorem B1476647 : Blo 1476558 1476647 := bstep (se 1 (by rfl) ⟨1107485, by rfl⟩ : syracuseStep 1476647 = 2214971) B2214971
theorem B1476687 : Blo 1476558 1476687 := bstep (se 1 (by rfl) ⟨1107515, by rfl⟩ : syracuseStep 1476687 = 2215031) B2215031
theorem B3598415 : Blo 1476558 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B1476703 : Blo 1476558 1476703 := bstep (se 1 (by rfl) ⟨1107527, by rfl⟩ : syracuseStep 1476703 = 2215055) B2215055
theorem B1476731 : Blo 1476558 1476731 := bstep (se 1 (by rfl) ⟨1107548, by rfl⟩ : syracuseStep 1476731 = 2215097) B2215097
theorem B5613725 : Blo 1476558 5613725 := bstep (se 3 (by rfl) ⟨1052573, by rfl⟩ : syracuseStep 5613725 = 2105147) B2105147
theorem B1476783 : Blo 1476558 1476783 := bstep (se 1 (by rfl) ⟨1107587, by rfl⟩ : syracuseStep 1476783 = 2215175) B2215175
theorem B1476807 : Blo 1476558 1476807 := bstep (se 1 (by rfl) ⟨1107605, by rfl⟩ : syracuseStep 1476807 = 2215211) B2215211
theorem B1476827 : Blo 1476558 1476827 := bstep (se 1 (by rfl) ⟨1107620, by rfl⟩ : syracuseStep 1476827 = 2215241) B2215241
theorem B3991799 : Blo 1476558 3991799 := bstep (se 1 (by rfl) ⟨2993849, by rfl⟩ : syracuseStep 3991799 = 5987699) B5987699
theorem B7104779 : Blo 1476558 7104779 := bstep (se 1 (by rfl) ⟨5328584, by rfl⟩ : syracuseStep 7104779 = 10657169) B10657169
theorem B1476903 : Blo 1476558 1476903 := bstep (se 1 (by rfl) ⟨1107677, by rfl⟩ : syracuseStep 1476903 = 2215355) B2215355
theorem B1476943 : Blo 1476558 1476943 := bstep (se 1 (by rfl) ⟨1107707, by rfl⟩ : syracuseStep 1476943 = 2215415) B2215415
theorem B1476959 : Blo 1476558 1476959 := bstep (se 1 (by rfl) ⟨1107719, by rfl⟩ : syracuseStep 1476959 = 2215439) B2215439
theorem B4491625 : Blo 1476558 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B1476987 : Blo 1476558 1476987 := bstep (se 1 (by rfl) ⟨1107740, by rfl⟩ : syracuseStep 1476987 = 2215481) B2215481
theorem B2492815 : Blo 1476558 2492815 := bstep (se 1 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 2492815 = 3739223) B3739223
theorem B2804129 : Blo 1476558 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B1477039 : Blo 1476558 1477039 := bstep (se 1 (by rfl) ⟨1107779, by rfl⟩ : syracuseStep 1477039 = 2215559) B2215559
theorem B1477063 : Blo 1476558 1477063 := bstep (se 1 (by rfl) ⟨1107797, by rfl⟩ : syracuseStep 1477063 = 2215595) B2215595
theorem B1477083 : Blo 1476558 1477083 := bstep (se 1 (by rfl) ⟨1107812, by rfl⟩ : syracuseStep 1477083 = 2215625) B2215625
theorem B1477159 : Blo 1476558 1477159 := bstep (se 1 (by rfl) ⟨1107869, by rfl⟩ : syracuseStep 1477159 = 2215739) B2215739
theorem B1477199 : Blo 1476558 1477199 := bstep (se 1 (by rfl) ⟨1107899, by rfl⟩ : syracuseStep 1477199 = 2215799) B2215799
theorem B1477215 : Blo 1476558 1477215 := bstep (se 1 (by rfl) ⟨1107911, by rfl⟩ : syracuseStep 1477215 = 2215823) B2215823
theorem B1477243 : Blo 1476558 1477243 := bstep (se 1 (by rfl) ⟨1107932, by rfl⟩ : syracuseStep 1477243 = 2215865) B2215865
theorem B3369595 : Blo 1476558 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B3738251 : Blo 1476558 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B4983443 : Blo 1476558 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B2804395 : Blo 1476558 2804395 := bstep (se 1 (by rfl) ⟨2103296, by rfl⟩ : syracuseStep 2804395 = 4206593) B4206593
theorem B1477295 : Blo 1476558 1477295 := bstep (se 1 (by rfl) ⟨1107971, by rfl⟩ : syracuseStep 1477295 = 2215943) B2215943
theorem B1477319 : Blo 1476558 1477319 := bstep (se 1 (by rfl) ⟨1107989, by rfl⟩ : syracuseStep 1477319 = 2215979) B2215979
theorem B1477339 : Blo 1476558 1477339 := bstep (se 1 (by rfl) ⟨1108004, by rfl⟩ : syracuseStep 1477339 = 2216009) B2216009
theorem B1477415 : Blo 1476558 1477415 := bstep (se 1 (by rfl) ⟨1108061, by rfl⟩ : syracuseStep 1477415 = 2216123) B2216123
theorem B31148875 : Blo 1476558 31148875 := bstep (se 1 (by rfl) ⟨23361656, by rfl⟩ : syracuseStep 31148875 = 46723313) B46723313
theorem B1477455 : Blo 1476558 1477455 := bstep (se 1 (by rfl) ⟨1108091, by rfl⟩ : syracuseStep 1477455 = 2216183) B2216183
theorem B1477471 : Blo 1476558 1477471 := bstep (se 1 (by rfl) ⟨1108103, by rfl⟩ : syracuseStep 1477471 = 2216207) B2216207
theorem B4983659 : Blo 1476558 4983659 := bstep (se 1 (by rfl) ⟨3737744, by rfl⟩ : syracuseStep 4983659 = 7475489) B7475489
theorem B1477499 : Blo 1476558 1477499 := bstep (se 1 (by rfl) ⟨1108124, by rfl⟩ : syracuseStep 1477499 = 2216249) B2216249
theorem B4983713 : Blo 1476558 4983713 := bstep (se 2 (by rfl) ⟨1868892, by rfl⟩ : syracuseStep 4983713 = 3737785) B3737785
theorem B1477551 : Blo 1476558 1477551 := bstep (se 1 (by rfl) ⟨1108163, by rfl⟩ : syracuseStep 1477551 = 2216327) B2216327
theorem B2214839 : Blo 1476558 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B1895351 : Blo 1476558 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B21605303 : Blo 1476558 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B1477575 : Blo 1476558 1477575 := bstep (se 1 (by rfl) ⟨1108181, by rfl⟩ : syracuseStep 1477575 = 2216363) B2216363
theorem B2214875 : Blo 1476558 2214875 := bstep (se 1 (by rfl) ⟨1661156, by rfl⟩ : syracuseStep 2214875 = 3322313) B3322313
theorem B2804699 : Blo 1476558 2804699 := bstep (se 1 (by rfl) ⟨2103524, by rfl⟩ : syracuseStep 2804699 = 4207049) B4207049
theorem B1477595 : Blo 1476558 1477595 := bstep (se 1 (by rfl) ⟨1108196, by rfl⟩ : syracuseStep 1477595 = 2216393) B2216393
theorem B11226113 : Blo 1476558 11226113 := bstep (se 2 (by rfl) ⟨4209792, by rfl⟩ : syracuseStep 11226113 = 8419585) B8419585
theorem B1477671 : Blo 1476558 1477671 := bstep (se 1 (by rfl) ⟨1108253, by rfl⟩ : syracuseStep 1477671 = 2216507) B2216507
theorem B2493497 : Blo 1476558 2493497 := bstep (se 2 (by rfl) ⟨935061, by rfl⟩ : syracuseStep 2493497 = 1870123) B1870123
theorem B1477711 : Blo 1476558 1477711 := bstep (se 1 (by rfl) ⟨1108283, by rfl⟩ : syracuseStep 1477711 = 2216567) B2216567
theorem B1477727 : Blo 1476558 1477727 := bstep (se 1 (by rfl) ⟨1108295, by rfl⟩ : syracuseStep 1477727 = 2216591) B2216591
theorem B1477755 : Blo 1476558 1477755 := bstep (se 1 (by rfl) ⟨1108316, by rfl⟩ : syracuseStep 1477755 = 2216633) B2216633
theorem B1477807 : Blo 1476558 1477807 := bstep (se 1 (by rfl) ⟨1108355, by rfl⟩ : syracuseStep 1477807 = 2216711) B2216711
theorem B1477831 : Blo 1476558 1477831 := bstep (se 1 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 1477831 = 2216747) B2216747
theorem B1477851 : Blo 1476558 1477851 := bstep (se 1 (by rfl) ⟨1108388, by rfl⟩ : syracuseStep 1477851 = 2216777) B2216777
theorem B14200055 : Blo 1476558 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B12627191 : Blo 1476558 12627191 := bstep (se 1 (by rfl) ⟨9470393, by rfl⟩ : syracuseStep 12627191 = 18940787) B18940787
theorem B1477927 : Blo 1476558 1477927 := bstep (se 1 (by rfl) ⟨1108445, by rfl⟩ : syracuseStep 1477927 = 2216891) B2216891
theorem B1477967 : Blo 1476558 1477967 := bstep (se 1 (by rfl) ⟨1108475, by rfl⟩ : syracuseStep 1477967 = 2216951) B2216951
theorem B1477983 : Blo 1476558 1477983 := bstep (se 1 (by rfl) ⟨1108487, by rfl⟩ : syracuseStep 1477983 = 2216975) B2216975
theorem B1478011 : Blo 1476558 1478011 := bstep (se 1 (by rfl) ⟨1108508, by rfl⟩ : syracuseStep 1478011 = 2217017) B2217017
theorem B2215343 : Blo 1476558 2215343 := bstep (se 1 (by rfl) ⟨1661507, by rfl⟩ : syracuseStep 2215343 = 3323015) B3323015
theorem B1478063 : Blo 1476558 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B1478087 : Blo 1476558 1478087 := bstep (se 1 (by rfl) ⟨1108565, by rfl⟩ : syracuseStep 1478087 = 2217131) B2217131
theorem B1478107 : Blo 1476558 1478107 := bstep (se 1 (by rfl) ⟨1108580, by rfl⟩ : syracuseStep 1478107 = 2217161) B2217161
theorem B4984307 : Blo 1476558 4984307 := bstep (se 1 (by rfl) ⟨3738230, by rfl⟩ : syracuseStep 4984307 = 7476461) B7476461
theorem B5606921 : Blo 1476558 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B2215433 : Blo 1476558 2215433 := bstep (se 2 (by rfl) ⟨830787, by rfl⟩ : syracuseStep 2215433 = 1661575) B1661575
theorem B2215463 : Blo 1476558 2215463 := bstep (se 1 (by rfl) ⟨1661597, by rfl⟩ : syracuseStep 2215463 = 3323195) B3323195
theorem B1478183 : Blo 1476558 1478183 := bstep (se 1 (by rfl) ⟨1108637, by rfl⟩ : syracuseStep 1478183 = 2217275) B2217275
theorem B1478223 : Blo 1476558 1478223 := bstep (se 1 (by rfl) ⟨1108667, by rfl⟩ : syracuseStep 1478223 = 2217335) B2217335
theorem B1478239 : Blo 1476558 1478239 := bstep (se 1 (by rfl) ⟨1108679, by rfl⟩ : syracuseStep 1478239 = 2217359) B2217359
theorem B2215547 : Blo 1476558 2215547 := bstep (se 1 (by rfl) ⟨1661660, by rfl⟩ : syracuseStep 2215547 = 3323321) B3323321
theorem B1478267 : Blo 1476558 1478267 := bstep (se 1 (by rfl) ⟨1108700, by rfl⟩ : syracuseStep 1478267 = 2217401) B2217401
theorem B1478319 : Blo 1476558 1478319 := bstep (se 1 (by rfl) ⟨1108739, by rfl⟩ : syracuseStep 1478319 = 2217479) B2217479
theorem B1478343 : Blo 1476558 1478343 := bstep (se 1 (by rfl) ⟨1108757, by rfl⟩ : syracuseStep 1478343 = 2217515) B2217515
theorem B1478363 : Blo 1476558 1478363 := bstep (se 1 (by rfl) ⟨1108772, by rfl⟩ : syracuseStep 1478363 = 2217545) B2217545
theorem B2494199 : Blo 1476558 2494199 := bstep (se 1 (by rfl) ⟨1870649, by rfl⟩ : syracuseStep 2494199 = 3741299) B3741299
theorem B2215673 : Blo 1476558 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B3739385 : Blo 1476558 3739385 := bstep (se 2 (by rfl) ⟨1402269, by rfl⟩ : syracuseStep 3739385 = 2804539) B2804539
theorem B1478439 : Blo 1476558 1478439 := bstep (se 1 (by rfl) ⟨1108829, by rfl⟩ : syracuseStep 1478439 = 2217659) B2217659
theorem B1478479 : Blo 1476558 1478479 := bstep (se 1 (by rfl) ⟨1108859, by rfl⟩ : syracuseStep 1478479 = 2217719) B2217719
theorem B2215775 : Blo 1476558 2215775 := bstep (se 1 (by rfl) ⟨1661831, by rfl⟩ : syracuseStep 2215775 = 3323663) B3323663
theorem B1478495 : Blo 1476558 1478495 := bstep (se 1 (by rfl) ⟨1108871, by rfl⟩ : syracuseStep 1478495 = 2217743) B2217743
theorem B3788651 : Blo 1476558 3788651 := bstep (se 1 (by rfl) ⟨2841488, by rfl⟩ : syracuseStep 3788651 = 5682977) B5682977
theorem B2215787 : Blo 1476558 2215787 := bstep (se 1 (by rfl) ⟨1661840, by rfl⟩ : syracuseStep 2215787 = 3323681) B3323681
theorem B1478523 : Blo 1476558 1478523 := bstep (se 1 (by rfl) ⟨1108892, by rfl⟩ : syracuseStep 1478523 = 2217785) B2217785
theorem B11218823 : Blo 1476558 11218823 := bstep (se 1 (by rfl) ⟨8414117, by rfl⟩ : syracuseStep 11218823 = 16828235) B16828235
theorem B3739567 : Blo 1476558 3739567 := bstep (se 1 (by rfl) ⟨2804675, by rfl⟩ : syracuseStep 3739567 = 5609351) B5609351
theorem B91025369 : Blo 1476558 91025369 := bstep (se 2 (by rfl) ⟨34134513, by rfl⟩ : syracuseStep 91025369 = 68269027) B68269027
theorem B2805769 : Blo 1476558 2805769 := bstep (se 2 (by rfl) ⟨1052163, by rfl⟩ : syracuseStep 2805769 = 2104327) B2104327
theorem B4984847 : Blo 1476558 4984847 := bstep (se 1 (by rfl) ⟨3738635, by rfl⟩ : syracuseStep 4984847 = 7477271) B7477271
theorem B4206649 : Blo 1476558 4206649 := bstep (se 2 (by rfl) ⟨1577493, by rfl⟩ : syracuseStep 4206649 = 3154987) B3154987
theorem B2216015 : Blo 1476558 2216015 := bstep (se 1 (by rfl) ⟨1662011, by rfl⟩ : syracuseStep 2216015 = 3324023) B3324023
theorem B2494543 : Blo 1476558 2494543 := bstep (se 1 (by rfl) ⟨1870907, by rfl⟩ : syracuseStep 2494543 = 3741815) B3741815
theorem B2216135 : Blo 1476558 2216135 := bstep (se 1 (by rfl) ⟨1662101, by rfl⟩ : syracuseStep 2216135 = 3324203) B3324203
theorem B10113281 : Blo 1476558 10113281 := bstep (se 2 (by rfl) ⟨3792480, by rfl⟩ : syracuseStep 10113281 = 7584961) B7584961
theorem B15159563 : Blo 1476558 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B11981105 : Blo 1476558 11981105 := bstep (se 2 (by rfl) ⟨4492914, by rfl⟩ : syracuseStep 11981105 = 8985829) B8985829
theorem B2494793 : Blo 1476558 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B2216297 : Blo 1476558 2216297 := bstep (se 2 (by rfl) ⟨831111, by rfl⟩ : syracuseStep 2216297 = 1662223) B1662223
theorem B3740033 : Blo 1476558 3740033 := bstep (se 2 (by rfl) ⟨1402512, by rfl⟩ : syracuseStep 3740033 = 2805025) B2805025
theorem B4206991 : Blo 1476558 4206991 := bstep (se 1 (by rfl) ⟨3155243, by rfl⟩ : syracuseStep 4206991 = 6310487) B6310487
theorem B2216375 : Blo 1476558 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B3322331 : Blo 1476558 3322331 := bstep (se 1 (by rfl) ⟨2491748, by rfl⟩ : syracuseStep 3322331 = 4983497) B4983497
theorem B2216411 : Blo 1476558 2216411 := bstep (se 1 (by rfl) ⟨1662308, by rfl⟩ : syracuseStep 2216411 = 3324617) B3324617
theorem B7483913 : Blo 1476558 7483913 := bstep (se 2 (by rfl) ⟨2806467, by rfl⟩ : syracuseStep 7483913 = 5612935) B5612935
theorem B4985441 : Blo 1476558 4985441 := bstep (se 2 (by rfl) ⟨1869540, by rfl⟩ : syracuseStep 4985441 = 3739081) B3739081
theorem B22737509 : Blo 1476558 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B5608075 : Blo 1476558 5608075 := bstep (se 1 (by rfl) ⟨4206056, by rfl⟩ : syracuseStep 5608075 = 8412113) B8412113
theorem B2806483 : Blo 1476558 2806483 := bstep (se 1 (by rfl) ⟨2104862, by rfl⟩ : syracuseStep 2806483 = 4209725) B4209725
theorem B3740489 : Blo 1476558 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B10654541 : Blo 1476558 10654541 := bstep (se 3 (by rfl) ⟨1997726, by rfl⟩ : syracuseStep 10654541 = 3995453) B3995453
theorem B1684319 : Blo 1476558 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B28414871 : Blo 1476558 28414871 := bstep (se 1 (by rfl) ⟨21311153, by rfl⟩ : syracuseStep 28414871 = 42622307) B42622307
theorem B4494241 : Blo 1476558 4494241 := bstep (se 2 (by rfl) ⟨1685340, by rfl⟩ : syracuseStep 4494241 = 3370681) B3370681
theorem B3322799 : Blo 1476558 3322799 := bstep (se 1 (by rfl) ⟨2492099, by rfl⟩ : syracuseStep 3322799 = 4984199) B4984199
theorem B2216879 : Blo 1476558 2216879 := bstep (se 1 (by rfl) ⟨1662659, by rfl⟩ : syracuseStep 2216879 = 3325319) B3325319
theorem B5608379 : Blo 1476558 5608379 := bstep (se 1 (by rfl) ⟨4206284, by rfl⟩ : syracuseStep 5608379 = 8412569) B8412569
theorem B42578945 : Blo 1476558 42578945 := bstep (se 2 (by rfl) ⟨15967104, by rfl⟩ : syracuseStep 42578945 = 31934209) B31934209
theorem B2216969 : Blo 1476558 2216969 := bstep (se 2 (by rfl) ⟨831363, by rfl⟩ : syracuseStep 2216969 = 1662727) B1662727
theorem B2216999 : Blo 1476558 2216999 := bstep (se 1 (by rfl) ⟨1662749, by rfl⟩ : syracuseStep 2216999 = 3325499) B3325499
theorem B2217083 : Blo 1476558 2217083 := bstep (se 1 (by rfl) ⟨1662812, by rfl⟩ : syracuseStep 2217083 = 3325625) B3325625
theorem B3323051 : Blo 1476558 3323051 := bstep (se 1 (by rfl) ⟨2492288, by rfl⟩ : syracuseStep 3323051 = 4984577) B4984577
theorem B3740843 : Blo 1476558 3740843 := bstep (se 1 (by rfl) ⟨2805632, by rfl⟩ : syracuseStep 3740843 = 5611265) B5611265
theorem B3994795 : Blo 1476558 3994795 := bstep (se 1 (by rfl) ⟨2996096, by rfl⟩ : syracuseStep 3994795 = 5992193) B5992193
theorem B2217209 : Blo 1476558 2217209 := bstep (se 2 (by rfl) ⟨831453, by rfl⟩ : syracuseStep 2217209 = 1662907) B1662907
theorem B2217311 : Blo 1476558 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B2217323 : Blo 1476558 2217323 := bstep (se 1 (by rfl) ⟨1662992, by rfl⟩ : syracuseStep 2217323 = 3325985) B3325985
theorem B7476623 : Blo 1476558 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B28407185 : Blo 1476558 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B7583149 : Blo 1476558 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B6313459 : Blo 1476558 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B2217551 : Blo 1476558 2217551 := bstep (se 1 (by rfl) ⟨1663163, by rfl⟩ : syracuseStep 2217551 = 3326327) B3326327
theorem B4208267 : Blo 1476558 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B7583377 : Blo 1476558 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B14202515 : Blo 1476558 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B3323591 : Blo 1476558 3323591 := bstep (se 1 (by rfl) ⟨2492693, by rfl⟩ : syracuseStep 3323591 = 4985387) B4985387
theorem B2217671 : Blo 1476558 2217671 := bstep (se 1 (by rfl) ⟨1663253, by rfl⟩ : syracuseStep 2217671 = 3326507) B3326507
theorem B1996537 : Blo 1476558 1996537 := bstep (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) B1497403
theorem B4265801 : Blo 1476558 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B2217833 : Blo 1476558 2217833 := bstep (se 2 (by rfl) ⟨831687, by rfl⟩ : syracuseStep 2217833 = 1663375) B1663375
theorem B3741623 : Blo 1476558 3741623 := bstep (se 1 (by rfl) ⟨2806217, by rfl⟩ : syracuseStep 3741623 = 5612435) B5612435
theorem B8984591 : Blo 1476558 8984591 := bstep (se 1 (by rfl) ⟨6738443, by rfl⟩ : syracuseStep 8984591 = 13476887) B13476887
theorem B4986899 : Blo 1476558 4986899 := bstep (se 1 (by rfl) ⟨3740174, by rfl⟩ : syracuseStep 4986899 = 7480349) B7480349
theorem B4987223 : Blo 1476558 4987223 := bstep (se 1 (by rfl) ⟨3740417, by rfl⟩ : syracuseStep 4987223 = 7480835) B7480835
theorem B1661359 : Blo 1476558 1661359 := bstep (se 1 (by rfl) ⟨1246019, by rfl⟩ : syracuseStep 1661359 = 2492039) B2492039
theorem B1776055 : Blo 1476558 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B3324455 : Blo 1476558 3324455 := bstep (se 1 (by rfl) ⟨2493341, by rfl⟩ : syracuseStep 3324455 = 4986683) B4986683
theorem B6740539 : Blo 1476558 6740539 := bstep (se 1 (by rfl) ⟨5055404, by rfl⟩ : syracuseStep 6740539 = 10110809) B10110809
theorem B5987015 : Blo 1476558 5987015 := bstep (se 1 (by rfl) ⟨4490261, by rfl⟩ : syracuseStep 5987015 = 8980523) B8980523
theorem B1661791 : Blo 1476558 1661791 := bstep (se 1 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 1661791 = 2492687) B2492687
theorem B2399071 : Blo 1476558 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B3324779 : Blo 1476558 3324779 := bstep (se 1 (by rfl) ⟨2493584, by rfl⟩ : syracuseStep 3324779 = 4987169) B4987169
theorem B3324833 : Blo 1476558 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B2661473 : Blo 1476558 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B2366587 : Blo 1476558 2366587 := bstep (se 1 (by rfl) ⟨1774940, by rfl⟩ : syracuseStep 2366587 = 3549881) B3549881
theorem B1662151 : Blo 1476558 1662151 := bstep (se 1 (by rfl) ⟨1246613, by rfl⟩ : syracuseStep 1662151 = 2493227) B2493227
theorem B3325175 : Blo 1476558 3325175 := bstep (se 1 (by rfl) ⟨2493881, by rfl⟩ : syracuseStep 3325175 = 4987763) B4987763
theorem B28392727 : Blo 1476558 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B4988303 : Blo 1476558 4988303 := bstep (se 1 (by rfl) ⟨3741227, by rfl⟩ : syracuseStep 4988303 = 7482455) B7482455
theorem B7478729 : Blo 1476558 7478729 := bstep (se 2 (by rfl) ⟨2804523, by rfl⟩ : syracuseStep 7478729 = 5609047) B5609047
theorem B4988627 : Blo 1476558 4988627 := bstep (se 1 (by rfl) ⟨3741470, by rfl⟩ : syracuseStep 4988627 = 7482941) B7482941
theorem B3325769 : Blo 1476558 3325769 := bstep (se 2 (by rfl) ⟨1247163, by rfl⟩ : syracuseStep 3325769 = 2494327) B2494327
theorem B15966071 : Blo 1476558 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B6307703 : Blo 1476558 6307703 := bstep (se 1 (by rfl) ⟨4730777, by rfl⟩ : syracuseStep 6307703 = 9461555) B9461555
theorem B9469831 : Blo 1476558 9469831 := bstep (se 1 (by rfl) ⟨7102373, by rfl⟩ : syracuseStep 9469831 = 14204747) B14204747
theorem B2367407 : Blo 1476558 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B62357521 : Blo 1476558 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B51200099 : Blo 1476558 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B3326057 : Blo 1476558 3326057 := bstep (se 2 (by rfl) ⟨1247271, by rfl⟩ : syracuseStep 3326057 = 2494543) B2494543
theorem B6742187 : Blo 1476558 6742187 := bstep (se 1 (by rfl) ⟨5056640, by rfl⟩ : syracuseStep 6742187 = 10113281) B10113281
theorem B7987403 : Blo 1476558 7987403 := bstep (se 1 (by rfl) ⟨5990552, by rfl⟩ : syracuseStep 7987403 = 11981105) B11981105
theorem B7586003 : Blo 1476558 7586003 := bstep (se 1 (by rfl) ⟨5689502, by rfl⟩ : syracuseStep 7586003 = 11379005) B11379005
theorem B1663195 : Blo 1476558 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B4989275 : Blo 1476558 4989275 := bstep (se 1 (by rfl) ⟨3741956, by rfl⟩ : syracuseStep 4989275 = 7483913) B7483913
theorem B5988833 : Blo 1476558 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B7103027 : Blo 1476558 7103027 := bstep (se 1 (by rfl) ⟨5327270, by rfl⟩ : syracuseStep 7103027 = 10654541) B10654541
theorem B2368073 : Blo 1476558 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B3326543 : Blo 1476558 3326543 := bstep (se 1 (by rfl) ⟨2494907, by rfl⟩ : syracuseStep 3326543 = 4989815) B4989815
theorem B28385963 : Blo 1476558 28385963 := bstep (se 1 (by rfl) ⟨21289472, by rfl⟩ : syracuseStep 28385963 = 42578945) B42578945
theorem B3326687 : Blo 1476558 3326687 := bstep (se 1 (by rfl) ⟨2495015, by rfl⟩ : syracuseStep 3326687 = 4990031) B4990031
theorem B14386081 : Blo 1476558 14386081 := bstep (se 2 (by rfl) ⟨5394780, by rfl⟩ : syracuseStep 14386081 = 10789561) B10789561
theorem B10945475 : Blo 1476558 10945475 := bstep (se 1 (by rfl) ⟨8209106, by rfl⟩ : syracuseStep 10945475 = 16418213) B16418213
theorem B12616667 : Blo 1476558 12616667 := bstep (se 1 (by rfl) ⟨9462500, by rfl⟩ : syracuseStep 12616667 = 18925001) B18925001
theorem B17966069 : Blo 1476558 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B2843867 : Blo 1476558 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B1869095 : Blo 1476558 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B5989727 : Blo 1476558 5989727 := bstep (se 1 (by rfl) ⟨4492295, by rfl⟩ : syracuseStep 5989727 = 8984591) B8984591
theorem B5326175 : Blo 1476558 5326175 := bstep (se 1 (by rfl) ⟨3994631, by rfl⟩ : syracuseStep 5326175 = 7989263) B7989263
theorem B2491897 : Blo 1476558 2491897 := bstep (se 2 (by rfl) ⟨934461, by rfl⟩ : syracuseStep 2491897 = 1868923) B1868923
theorem B3155449 : Blo 1476558 3155449 := bstep (se 2 (by rfl) ⟨1183293, by rfl⟩ : syracuseStep 3155449 = 2366587) B2366587
theorem B4736519 : Blo 1476558 4736519 := bstep (se 1 (by rfl) ⟨3552389, by rfl⟩ : syracuseStep 4736519 = 7104779) B7104779
theorem B10651169 : Blo 1476558 10651169 := bstep (se 2 (by rfl) ⟨3994188, by rfl⟩ : syracuseStep 10651169 = 7988377) B7988377
theorem B5326393 : Blo 1476558 5326393 := bstep (se 2 (by rfl) ⟨1997397, by rfl⟩ : syracuseStep 5326393 = 3994795) B3994795
theorem B1869419 : Blo 1476558 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B37856969 : Blo 1476558 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B166127333 : Blo 1476558 166127333 := bstep (se 4 (by rfl) ⟨15574437, by rfl⟩ : syracuseStep 166127333 = 31148875) B31148875
theorem B2492167 : Blo 1476558 2492167 := bstep (se 1 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 2492167 = 3738251) B3738251
theorem B2492201 : Blo 1476558 2492201 := bstep (se 2 (by rfl) ⟨934575, by rfl⟩ : syracuseStep 2492201 = 1869151) B1869151
theorem B1476559 : Blo 1476558 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B1869799 : Blo 1476558 1869799 := bstep (se 1 (by rfl) ⟨1402349, by rfl⟩ : syracuseStep 1869799 = 2804699) B2804699
theorem B1476583 : Blo 1476558 1476583 := bstep (se 1 (by rfl) ⟨1107437, by rfl⟩ : syracuseStep 1476583 = 2214875) B2214875
theorem B25585645 : Blo 1476558 25585645 := bstep (se 3 (by rfl) ⟨4797308, by rfl⟩ : syracuseStep 25585645 = 9594617) B9594617
theorem B10111169 : Blo 1476558 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B8415485 : Blo 1476558 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B10103069 : Blo 1476558 10103069 := bstep (se 3 (by rfl) ⟨1894325, by rfl⟩ : syracuseStep 10103069 = 3788651) B3788651
theorem B1476895 : Blo 1476558 1476895 := bstep (se 1 (by rfl) ⟨1107671, by rfl⟩ : syracuseStep 1476895 = 2215343) B2215343
theorem B3737947 : Blo 1476558 3737947 := bstep (se 1 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 3737947 = 5606921) B5606921
theorem B1476955 : Blo 1476558 1476955 := bstep (se 1 (by rfl) ⟨1107716, by rfl⟩ : syracuseStep 1476955 = 2215433) B2215433
theorem B1476975 : Blo 1476558 1476975 := bstep (se 1 (by rfl) ⟨1107731, by rfl⟩ : syracuseStep 1476975 = 2215463) B2215463
theorem B1477031 : Blo 1476558 1477031 := bstep (se 1 (by rfl) ⟨1107773, by rfl⟩ : syracuseStep 1477031 = 2215547) B2215547
theorem B1477115 : Blo 1476558 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B2492923 : Blo 1476558 2492923 := bstep (se 1 (by rfl) ⟨1869692, by rfl⟩ : syracuseStep 2492923 = 3739385) B3739385
theorem B12626441 : Blo 1476558 12626441 := bstep (se 2 (by rfl) ⟨4734915, by rfl⟩ : syracuseStep 12626441 = 9469831) B9469831
theorem B1477183 : Blo 1476558 1477183 := bstep (se 1 (by rfl) ⟨1107887, by rfl⟩ : syracuseStep 1477183 = 2215775) B2215775
theorem B1477191 : Blo 1476558 1477191 := bstep (se 1 (by rfl) ⟨1107893, by rfl⟩ : syracuseStep 1477191 = 2215787) B2215787
theorem B10644047 : Blo 1476558 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B4205135 : Blo 1476558 4205135 := bstep (se 1 (by rfl) ⟨3153851, by rfl⟩ : syracuseStep 4205135 = 6307703) B6307703
theorem B16820945 : Blo 1476558 16820945 := bstep (se 2 (by rfl) ⟨6307854, by rfl⟩ : syracuseStep 16820945 = 12615709) B12615709
theorem B1477343 : Blo 1476558 1477343 := bstep (se 1 (by rfl) ⟨1108007, by rfl⟩ : syracuseStep 1477343 = 2216015) B2216015
theorem B7482131 : Blo 1476558 7482131 := bstep (se 1 (by rfl) ⟨5611598, by rfl⟩ : syracuseStep 7482131 = 11223197) B11223197
theorem B1477423 : Blo 1476558 1477423 := bstep (se 1 (by rfl) ⟨1108067, by rfl⟩ : syracuseStep 1477423 = 2216135) B2216135
theorem B1477531 : Blo 1476558 1477531 := bstep (se 1 (by rfl) ⟨1108148, by rfl⟩ : syracuseStep 1477531 = 2216297) B2216297
theorem B2493355 : Blo 1476558 2493355 := bstep (se 1 (by rfl) ⟨1870016, by rfl⟩ : syracuseStep 2493355 = 3740033) B3740033
theorem B1477583 : Blo 1476558 1477583 := bstep (se 1 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 1477583 = 2216375) B2216375
theorem B35949541 : Blo 1476558 35949541 := bstep (se 4 (by rfl) ⟨3370269, by rfl⟩ : syracuseStep 35949541 = 6740539) B6740539
theorem B2214887 : Blo 1476558 2214887 := bstep (se 1 (by rfl) ⟨1661165, by rfl⟩ : syracuseStep 2214887 = 3322331) B3322331
theorem B1477607 : Blo 1476558 1477607 := bstep (se 1 (by rfl) ⟨1108205, by rfl⟩ : syracuseStep 1477607 = 2216411) B2216411
theorem B15158339 : Blo 1476558 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B2493659 : Blo 1476558 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B2215145 : Blo 1476558 2215145 := bstep (se 2 (by rfl) ⟨830679, by rfl⟩ : syracuseStep 2215145 = 1661359) B1661359
theorem B18943247 : Blo 1476558 18943247 := bstep (se 1 (by rfl) ⟨14207435, by rfl⟩ : syracuseStep 18943247 = 28414871) B28414871
theorem B2215199 : Blo 1476558 2215199 := bstep (se 1 (by rfl) ⟨1661399, by rfl⟩ : syracuseStep 2215199 = 3322799) B3322799
theorem B1477919 : Blo 1476558 1477919 := bstep (se 1 (by rfl) ⟨1108439, by rfl⟩ : syracuseStep 1477919 = 2216879) B2216879
theorem B3738919 : Blo 1476558 3738919 := bstep (se 1 (by rfl) ⟨2804189, by rfl⟩ : syracuseStep 3738919 = 5608379) B5608379
theorem B10644797 : Blo 1476558 10644797 := bstep (se 3 (by rfl) ⟨1995899, by rfl⟩ : syracuseStep 10644797 = 3991799) B3991799
theorem B1477979 : Blo 1476558 1477979 := bstep (se 1 (by rfl) ⟨1108484, by rfl⟩ : syracuseStep 1477979 = 2216969) B2216969
theorem B1477999 : Blo 1476558 1477999 := bstep (se 1 (by rfl) ⟨1108499, by rfl⟩ : syracuseStep 1477999 = 2216999) B2216999
theorem B1478055 : Blo 1476558 1478055 := bstep (se 1 (by rfl) ⟨1108541, by rfl⟩ : syracuseStep 1478055 = 2217083) B2217083
theorem B2215367 : Blo 1476558 2215367 := bstep (se 1 (by rfl) ⟨1661525, by rfl⟩ : syracuseStep 2215367 = 3323051) B3323051
theorem B2493895 : Blo 1476558 2493895 := bstep (se 1 (by rfl) ⟨1870421, by rfl⟩ : syracuseStep 2493895 = 3740843) B3740843
theorem B4492793 : Blo 1476558 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B1478139 : Blo 1476558 1478139 := bstep (se 1 (by rfl) ⟨1108604, by rfl⟩ : syracuseStep 1478139 = 2217209) B2217209
theorem B3739193 : Blo 1476558 3739193 := bstep (se 2 (by rfl) ⟨1402197, by rfl⟩ : syracuseStep 3739193 = 2804395) B2804395
theorem B1478207 : Blo 1476558 1478207 := bstep (se 1 (by rfl) ⟨1108655, by rfl⟩ : syracuseStep 1478207 = 2217311) B2217311
theorem B1478215 : Blo 1476558 1478215 := bstep (se 1 (by rfl) ⟨1108661, by rfl⟩ : syracuseStep 1478215 = 2217323) B2217323
theorem B4984415 : Blo 1476558 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B1478367 : Blo 1476558 1478367 := bstep (se 1 (by rfl) ⟨1108775, by rfl⟩ : syracuseStep 1478367 = 2217551) B2217551
theorem B2805511 : Blo 1476558 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B2215721 : Blo 1476558 2215721 := bstep (se 2 (by rfl) ⟨830895, by rfl⟩ : syracuseStep 2215721 = 1661791) B1661791
theorem B3198761 : Blo 1476558 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2215727 : Blo 1476558 2215727 := bstep (se 1 (by rfl) ⟨1661795, by rfl⟩ : syracuseStep 2215727 = 3323591) B3323591
theorem B1478447 : Blo 1476558 1478447 := bstep (se 1 (by rfl) ⟨1108835, by rfl⟩ : syracuseStep 1478447 = 2217671) B2217671
theorem B5992321 : Blo 1476558 5992321 := bstep (se 2 (by rfl) ⟨2247120, by rfl⟩ : syracuseStep 5992321 = 4494241) B4494241
theorem B7483265 : Blo 1476558 7483265 := bstep (se 2 (by rfl) ⟨2806224, by rfl⟩ : syracuseStep 7483265 = 5612449) B5612449
theorem B1478555 : Blo 1476558 1478555 := bstep (se 1 (by rfl) ⟨1108916, by rfl⟩ : syracuseStep 1478555 = 2217833) B2217833
theorem B2494415 : Blo 1476558 2494415 := bstep (se 1 (by rfl) ⟨1870811, by rfl⟩ : syracuseStep 2494415 = 3741623) B3741623
theorem B2216201 : Blo 1476558 2216201 := bstep (se 2 (by rfl) ⟨831075, by rfl⟩ : syracuseStep 2216201 = 1662151) B1662151
theorem B2216303 : Blo 1476558 2216303 := bstep (se 1 (by rfl) ⟨1662227, by rfl⟩ : syracuseStep 2216303 = 3324455) B3324455
theorem B3322295 : Blo 1476558 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B3322439 : Blo 1476558 3322439 := bstep (se 1 (by rfl) ⟨2491829, by rfl⟩ : syracuseStep 3322439 = 4983659) B4983659
theorem B2216519 : Blo 1476558 2216519 := bstep (se 1 (by rfl) ⟨1662389, by rfl⟩ : syracuseStep 2216519 = 3324779) B3324779
theorem B3322475 : Blo 1476558 3322475 := bstep (se 1 (by rfl) ⟨2491856, by rfl⟩ : syracuseStep 3322475 = 4983713) B4983713
theorem B2216555 : Blo 1476558 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B8417945 : Blo 1476558 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B7484075 : Blo 1476558 7484075 := bstep (se 1 (by rfl) ⟨5613056, by rfl⟩ : syracuseStep 7484075 = 11226113) B11226113
theorem B1774315 : Blo 1476558 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B63861493 : Blo 1476558 63861493 := bstep (se 5 (by rfl) ⟨2993507, by rfl⟩ : syracuseStep 63861493 = 5987015) B5987015
theorem B9466703 : Blo 1476558 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B2216783 : Blo 1476558 2216783 := bstep (se 1 (by rfl) ⟨1662587, by rfl⟩ : syracuseStep 2216783 = 3325175) B3325175
theorem B8418127 : Blo 1476558 8418127 := bstep (se 1 (by rfl) ⟨6313595, by rfl⟩ : syracuseStep 8418127 = 12627191) B12627191
theorem B4985819 : Blo 1476558 4985819 := bstep (se 1 (by rfl) ⟨3739364, by rfl⟩ : syracuseStep 4985819 = 7478729) B7478729
theorem B3322871 : Blo 1476558 3322871 := bstep (se 1 (by rfl) ⟨2492153, by rfl⟩ : syracuseStep 3322871 = 4984307) B4984307
theorem B4985981 : Blo 1476558 4985981 := bstep (se 3 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 4985981 = 1869743) B1869743
theorem B6313085 : Blo 1476558 6313085 := bstep (se 3 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 6313085 = 2367407) B2367407
theorem B7484561 : Blo 1476558 7484561 := bstep (se 2 (by rfl) ⟨2806710, by rfl⟩ : syracuseStep 7484561 = 5613421) B5613421
theorem B2217179 : Blo 1476558 2217179 := bstep (se 1 (by rfl) ⟨1662884, by rfl⟩ : syracuseStep 2217179 = 3325769) B3325769
theorem B4986089 : Blo 1476558 4986089 := bstep (se 2 (by rfl) ⟨1869783, by rfl⟩ : syracuseStep 4986089 = 3739567) B3739567
theorem B60683579 : Blo 1476558 60683579 := bstep (se 1 (by rfl) ⟨45512684, by rfl⟩ : syracuseStep 60683579 = 91025369) B91025369
theorem B3323231 : Blo 1476558 3323231 := bstep (se 1 (by rfl) ⟨2492423, by rfl⟩ : syracuseStep 3323231 = 4984847) B4984847
theorem B3741025 : Blo 1476558 3741025 := bstep (se 2 (by rfl) ⟨1402884, by rfl⟩ : syracuseStep 3741025 = 2805769) B2805769
theorem B2217353 : Blo 1476558 2217353 := bstep (se 2 (by rfl) ⟨831507, by rfl⟩ : syracuseStep 2217353 = 1663015) B1663015
theorem B4986251 : Blo 1476558 4986251 := bstep (se 1 (by rfl) ⟨3739688, by rfl⟩ : syracuseStep 4986251 = 7479377) B7479377
theorem B5608865 : Blo 1476558 5608865 := bstep (se 2 (by rfl) ⟨2103324, by rfl⟩ : syracuseStep 5608865 = 4206649) B4206649
theorem B10106375 : Blo 1476558 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B4265659 : Blo 1476558 4265659 := bstep (se 1 (by rfl) ⟨3199244, by rfl⟩ : syracuseStep 4265659 = 6398489) B6398489
theorem B3323627 : Blo 1476558 3323627 := bstep (se 1 (by rfl) ⟨2492720, by rfl⟩ : syracuseStep 3323627 = 4985441) B4985441
theorem B2217707 : Blo 1476558 2217707 := bstep (se 1 (by rfl) ⟨1663280, by rfl⟩ : syracuseStep 2217707 = 3326561) B3326561
theorem B12629789 : Blo 1476558 12629789 := bstep (se 3 (by rfl) ⟨2368085, by rfl⟩ : syracuseStep 12629789 = 4736171) B4736171
theorem B3323753 : Blo 1476558 3323753 := bstep (se 2 (by rfl) ⟨1246407, by rfl⟩ : syracuseStep 3323753 = 2492815) B2492815
theorem B5609321 : Blo 1476558 5609321 := bstep (se 2 (by rfl) ⟨2103495, by rfl⟩ : syracuseStep 5609321 = 4206991) B4206991
theorem B166205573 : Blo 1476558 166205573 := bstep (se 4 (by rfl) ⟨15581772, by rfl⟩ : syracuseStep 166205573 = 31163545) B31163545
theorem B7477433 : Blo 1476558 7477433 := bstep (se 2 (by rfl) ⟨2804037, by rfl⟩ : syracuseStep 7477433 = 5608075) B5608075
theorem B18938123 : Blo 1476558 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B10115351 : Blo 1476558 10115351 := bstep (se 1 (by rfl) ⟨7586513, by rfl⟩ : syracuseStep 10115351 = 15173027) B15173027
theorem B3741977 : Blo 1476558 3741977 := bstep (se 2 (by rfl) ⟨1403241, by rfl⟩ : syracuseStep 3741977 = 2806483) B2806483
theorem B1661215 : Blo 1476558 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1775911 : Blo 1476558 1775911 := bstep (se 1 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 1775911 = 2663867) B2663867
theorem B7100797 : Blo 1476558 7100797 := bstep (se 3 (by rfl) ⟨1331399, by rfl⟩ : syracuseStep 7100797 = 2662799) B2662799
theorem B9468343 : Blo 1476558 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B1661503 : Blo 1476558 1661503 := bstep (se 1 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 1661503 = 2492255) B2492255
theorem B3742271 : Blo 1476558 3742271 := bstep (se 1 (by rfl) ⟨2806703, by rfl⟩ : syracuseStep 3742271 = 5613407) B5613407
theorem B2366023 : Blo 1476558 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B3324599 : Blo 1476558 3324599 := bstep (se 1 (by rfl) ⟨2493449, by rfl⟩ : syracuseStep 3324599 = 4986899) B4986899
theorem B2398943 : Blo 1476558 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B3742483 : Blo 1476558 3742483 := bstep (se 1 (by rfl) ⟨2806862, by rfl⟩ : syracuseStep 3742483 = 5613725) B5613725
theorem B3324815 : Blo 1476558 3324815 := bstep (se 1 (by rfl) ⟨2493611, by rfl⟩ : syracuseStep 3324815 = 4987223) B4987223
theorem B20217077 : Blo 1476558 20217077 := bstep (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) B1895351
theorem B1662331 : Blo 1476558 1662331 := bstep (se 1 (by rfl) ⟨1246748, by rfl⟩ : syracuseStep 1662331 = 2493497) B2493497
theorem B40443461 : Blo 1476558 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B3325535 : Blo 1476558 3325535 := bstep (se 1 (by rfl) ⟨2494151, by rfl⟩ : syracuseStep 3325535 = 4988303) B4988303
theorem B2662049 : Blo 1476558 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B3325751 : Blo 1476558 3325751 := bstep (se 1 (by rfl) ⟨2494313, by rfl⟩ : syracuseStep 3325751 = 4988627) B4988627
theorem B57614141 : Blo 1476558 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B1662799 : Blo 1476558 1662799 := bstep (se 1 (by rfl) ⟨1247099, by rfl⟩ : syracuseStep 1662799 = 2494199) B2494199
theorem B7479215 : Blo 1476558 7479215 := bstep (se 1 (by rfl) ⟨5609411, by rfl⟩ : syracuseStep 7479215 = 11218823) B11218823
theorem B5324935 : Blo 1476558 5324935 := bstep (se 1 (by rfl) ⟨3993701, by rfl⟩ : syracuseStep 5324935 = 7987403) B7987403
theorem B3326183 : Blo 1476558 3326183 := bstep (se 1 (by rfl) ⟨2494637, by rfl⟩ : syracuseStep 3326183 = 4989275) B4989275
theorem B4735351 : Blo 1476558 4735351 := bstep (se 1 (by rfl) ⟨3551513, by rfl⟩ : syracuseStep 4735351 = 7103027) B7103027
theorem B2367881 : Blo 1476558 2367881 := bstep (se 2 (by rfl) ⟨887955, by rfl⟩ : syracuseStep 2367881 = 1775911) B1775911
theorem B5611963 : Blo 1476558 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B18923975 : Blo 1476558 18923975 := bstep (se 1 (by rfl) ⟨14192981, by rfl⟩ : syracuseStep 18923975 = 28385963) B28385963
theorem B4989383 : Blo 1476558 4989383 := bstep (se 1 (by rfl) ⟨3742037, by rfl⟩ : syracuseStep 4989383 = 7484075) B7484075
theorem B12624457 : Blo 1476558 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B11977379 : Blo 1476558 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B3154697 : Blo 1476558 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B4989707 : Blo 1476558 4989707 := bstep (se 1 (by rfl) ⟨3742280, by rfl⟩ : syracuseStep 4989707 = 7484561) B7484561
theorem B85148657 : Blo 1476558 85148657 := bstep (se 2 (by rfl) ⟨31930746, by rfl⟩ : syracuseStep 85148657 = 63861493) B63861493
theorem B4989977 : Blo 1476558 4989977 := bstep (se 2 (by rfl) ⟨1871241, by rfl⟩ : syracuseStep 4989977 = 3742483) B3742483
theorem B11224169 : Blo 1476558 11224169 := bstep (se 2 (by rfl) ⟨4209063, by rfl⟩ : syracuseStep 11224169 = 8418127) B8418127
theorem B9463013 : Blo 1476558 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B47932721 : Blo 1476558 47932721 := bstep (se 2 (by rfl) ⟨17974770, by rfl⟩ : syracuseStep 47932721 = 35949541) B35949541
theorem B12625415 : Blo 1476558 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B6743567 : Blo 1476558 6743567 := bstep (se 1 (by rfl) ⟨5057675, by rfl⟩ : syracuseStep 6743567 = 10115351) B10115351
theorem B7096031 : Blo 1476558 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B2803423 : Blo 1476558 2803423 := bstep (se 1 (by rfl) ⟨2102567, by rfl⟩ : syracuseStep 2803423 = 4205135) B4205135
theorem B1476591 : Blo 1476558 1476591 := bstep (se 1 (by rfl) ⟨1107443, by rfl⟩ : syracuseStep 1476591 = 2214887) B2214887
theorem B1476763 : Blo 1476558 1476763 := bstep (se 1 (by rfl) ⟨1107572, by rfl⟩ : syracuseStep 1476763 = 2215145) B2215145
theorem B13478051 : Blo 1476558 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B1476799 : Blo 1476558 1476799 := bstep (se 1 (by rfl) ⟨1107599, by rfl⟩ : syracuseStep 1476799 = 2215199) B2215199
theorem B7096531 : Blo 1476558 7096531 := bstep (se 1 (by rfl) ⟨5322398, by rfl⟩ : syracuseStep 7096531 = 10644797) B10644797
theorem B5687545 : Blo 1476558 5687545 := bstep (se 2 (by rfl) ⟨2132829, by rfl⟩ : syracuseStep 5687545 = 4265659) B4265659
theorem B1476911 : Blo 1476558 1476911 := bstep (se 1 (by rfl) ⟨1107683, by rfl⟩ : syracuseStep 1476911 = 2215367) B2215367
theorem B2492795 : Blo 1476558 2492795 := bstep (se 1 (by rfl) ⟨1869596, by rfl⟩ : syracuseStep 2492795 = 3739193) B3739193
theorem B26962307 : Blo 1476558 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B7989761 : Blo 1476558 7989761 := bstep (se 2 (by rfl) ⟨2996160, by rfl⟩ : syracuseStep 7989761 = 5992321) B5992321
theorem B1477147 : Blo 1476558 1477147 := bstep (se 1 (by rfl) ⟨1107860, by rfl⟩ : syracuseStep 1477147 = 2215721) B2215721
theorem B2132507 : Blo 1476558 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B1477151 : Blo 1476558 1477151 := bstep (se 1 (by rfl) ⟨1107863, by rfl⟩ : syracuseStep 1477151 = 2215727) B2215727
theorem B2493065 : Blo 1476558 2493065 := bstep (se 2 (by rfl) ⟨934899, by rfl⟩ : syracuseStep 2493065 = 1869799) B1869799
theorem B34114193 : Blo 1476558 34114193 := bstep (se 2 (by rfl) ⟨12792822, by rfl⟩ : syracuseStep 34114193 = 25585645) B25585645
theorem B83143361 : Blo 1476558 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B5057335 : Blo 1476558 5057335 := bstep (se 1 (by rfl) ⟨3793001, by rfl⟩ : syracuseStep 5057335 = 7586003) B7586003
theorem B1477467 : Blo 1476558 1477467 := bstep (se 1 (by rfl) ⟨1108100, by rfl⟩ : syracuseStep 1477467 = 2216201) B2216201
theorem B1477535 : Blo 1476558 1477535 := bstep (se 1 (by rfl) ⟨1108151, by rfl⟩ : syracuseStep 1477535 = 2216303) B2216303
theorem B2214863 : Blo 1476558 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B3992555 : Blo 1476558 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B2214953 : Blo 1476558 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B2214959 : Blo 1476558 2214959 := bstep (se 1 (by rfl) ⟨1661219, by rfl⟩ : syracuseStep 2214959 = 3322439) B3322439
theorem B1477679 : Blo 1476558 1477679 := bstep (se 1 (by rfl) ⟨1108259, by rfl⟩ : syracuseStep 1477679 = 2216519) B2216519
theorem B2214983 : Blo 1476558 2214983 := bstep (se 1 (by rfl) ⟨1661237, by rfl⟩ : syracuseStep 2214983 = 3322475) B3322475
theorem B1477703 : Blo 1476558 1477703 := bstep (se 1 (by rfl) ⟨1108277, by rfl⟩ : syracuseStep 1477703 = 2216555) B2216555
theorem B4983929 : Blo 1476558 4983929 := bstep (se 2 (by rfl) ⟨1868973, by rfl⟩ : syracuseStep 4983929 = 3737947) B3737947
theorem B6311135 : Blo 1476558 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B1477855 : Blo 1476558 1477855 := bstep (se 1 (by rfl) ⟨1108391, by rfl⟩ : syracuseStep 1477855 = 2216783) B2216783
theorem B2215247 : Blo 1476558 2215247 := bstep (se 1 (by rfl) ⟨1661435, by rfl⟩ : syracuseStep 2215247 = 3322871) B3322871
theorem B2215337 : Blo 1476558 2215337 := bstep (se 2 (by rfl) ⟨830751, by rfl⟩ : syracuseStep 2215337 = 1661503) B1661503
theorem B4984253 : Blo 1476558 4984253 := bstep (se 3 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 4984253 = 1869095) B1869095
theorem B1478119 : Blo 1476558 1478119 := bstep (se 1 (by rfl) ⟨1108589, by rfl⟩ : syracuseStep 1478119 = 2217179) B2217179
theorem B40455719 : Blo 1476558 40455719 := bstep (se 1 (by rfl) ⟨30341789, by rfl⟩ : syracuseStep 40455719 = 60683579) B60683579
theorem B2215487 : Blo 1476558 2215487 := bstep (se 1 (by rfl) ⟨1661615, by rfl⟩ : syracuseStep 2215487 = 3323231) B3323231
theorem B3993151 : Blo 1476558 3993151 := bstep (se 1 (by rfl) ⟨2994863, by rfl⟩ : syracuseStep 3993151 = 5989727) B5989727
theorem B3550783 : Blo 1476558 3550783 := bstep (se 1 (by rfl) ⟨2663087, by rfl⟩ : syracuseStep 3550783 = 5326175) B5326175
theorem B1478235 : Blo 1476558 1478235 := bstep (se 1 (by rfl) ⟨1108676, by rfl⟩ : syracuseStep 1478235 = 2217353) B2217353
theorem B3739243 : Blo 1476558 3739243 := bstep (se 1 (by rfl) ⟨2804432, by rfl⟩ : syracuseStep 3739243 = 5608865) B5608865
theorem B3157679 : Blo 1476558 3157679 := bstep (se 1 (by rfl) ⟨2368259, by rfl⟩ : syracuseStep 3157679 = 4736519) B4736519
theorem B2215751 : Blo 1476558 2215751 := bstep (se 1 (by rfl) ⟨1661813, by rfl⟩ : syracuseStep 2215751 = 3323627) B3323627
theorem B1478471 : Blo 1476558 1478471 := bstep (se 1 (by rfl) ⟨1108853, by rfl⟩ : syracuseStep 1478471 = 2217707) B2217707
theorem B19181441 : Blo 1476558 19181441 := bstep (se 2 (by rfl) ⟨7193040, by rfl⟩ : syracuseStep 19181441 = 14386081) B14386081
theorem B2215835 : Blo 1476558 2215835 := bstep (se 1 (by rfl) ⟨1661876, by rfl⟩ : syracuseStep 2215835 = 3323753) B3323753
theorem B3739547 : Blo 1476558 3739547 := bstep (se 1 (by rfl) ⟨2804660, by rfl⟩ : syracuseStep 3739547 = 5609321) B5609321
theorem B11980781 : Blo 1476558 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B4984955 : Blo 1476558 4984955 := bstep (se 1 (by rfl) ⟨3738716, by rfl⟩ : syracuseStep 4984955 = 7477433) B7477433
theorem B2494651 : Blo 1476558 2494651 := bstep (se 1 (by rfl) ⟨1870988, by rfl⟩ : syracuseStep 2494651 = 3741977) B3741977
theorem B4985117 : Blo 1476558 4985117 := bstep (se 3 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 4985117 = 1869419) B1869419
theorem B8417627 : Blo 1476558 8417627 := bstep (se 1 (by rfl) ⟨6313220, by rfl⟩ : syracuseStep 8417627 = 12626441) B12626441
theorem B2494847 : Blo 1476558 2494847 := bstep (se 1 (by rfl) ⟨1871135, by rfl⟩ : syracuseStep 2494847 = 3742271) B3742271
theorem B4985225 : Blo 1476558 4985225 := bstep (se 2 (by rfl) ⟨1869459, by rfl⟩ : syracuseStep 4985225 = 3738919) B3738919
theorem B7098797 : Blo 1476558 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B2216399 : Blo 1476558 2216399 := bstep (se 1 (by rfl) ⟨1662299, by rfl⟩ : syracuseStep 2216399 = 3324599) B3324599
theorem B2216441 : Blo 1476558 2216441 := bstep (se 2 (by rfl) ⟨831165, by rfl⟩ : syracuseStep 2216441 = 1662331) B1662331
theorem B2216543 : Blo 1476558 2216543 := bstep (se 1 (by rfl) ⟨1662407, by rfl⟩ : syracuseStep 2216543 = 3324815) B3324815
theorem B3322529 : Blo 1476558 3322529 := bstep (se 2 (by rfl) ⟨1245948, by rfl⟩ : syracuseStep 3322529 = 2491897) B2491897
theorem B4207265 : Blo 1476558 4207265 := bstep (se 2 (by rfl) ⟨1577724, by rfl⟩ : syracuseStep 4207265 = 3155449) B3155449
theorem B10105559 : Blo 1476558 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B12628831 : Blo 1476558 12628831 := bstep (se 1 (by rfl) ⟨9471623, by rfl⟩ : syracuseStep 12628831 = 18943247) B18943247
theorem B3322889 : Blo 1476558 3322889 := bstep (se 2 (by rfl) ⟨1246083, by rfl⟩ : syracuseStep 3322889 = 2492167) B2492167
theorem B3740681 : Blo 1476558 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B3322943 : Blo 1476558 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B2217023 : Blo 1476558 2217023 := bstep (se 1 (by rfl) ⟨1662767, by rfl⟩ : syracuseStep 2217023 = 3325535) B3325535
theorem B2217065 : Blo 1476558 2217065 := bstep (se 2 (by rfl) ⟨831399, by rfl⟩ : syracuseStep 2217065 = 1662799) B1662799
theorem B2217167 : Blo 1476558 2217167 := bstep (se 1 (by rfl) ⟨1662875, by rfl⟩ : syracuseStep 2217167 = 3325751) B3325751
theorem B38409427 : Blo 1476558 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B4986143 : Blo 1476558 4986143 := bstep (se 1 (by rfl) ⟨3739607, by rfl⟩ : syracuseStep 4986143 = 7479215) B7479215
theorem B34133399 : Blo 1476558 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B2217371 : Blo 1476558 2217371 := bstep (se 1 (by rfl) ⟨1663028, by rfl⟩ : syracuseStep 2217371 = 3326057) B3326057
theorem B4494791 : Blo 1476558 4494791 := bstep (se 1 (by rfl) ⟨3371093, by rfl⟩ : syracuseStep 4494791 = 6742187) B6742187
theorem B2217593 : Blo 1476558 2217593 := bstep (se 2 (by rfl) ⟨831597, by rfl⟩ : syracuseStep 2217593 = 1663195) B1663195
theorem B2217695 : Blo 1476558 2217695 := bstep (se 1 (by rfl) ⟨1663271, by rfl⟩ : syracuseStep 2217695 = 3326543) B3326543
theorem B2217791 : Blo 1476558 2217791 := bstep (se 1 (by rfl) ⟨1663343, by rfl⟩ : syracuseStep 2217791 = 3326687) B3326687
theorem B9467729 : Blo 1476558 9467729 := bstep (se 2 (by rfl) ⟨3550398, by rfl⟩ : syracuseStep 9467729 = 7100797) B7100797
theorem B7583645 : Blo 1476558 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B7296983 : Blo 1476558 7296983 := bstep (se 1 (by rfl) ⟨5472737, by rfl⟩ : syracuseStep 7296983 = 10945475) B10945475
theorem B8411111 : Blo 1476558 8411111 := bstep (se 1 (by rfl) ⟨6308333, by rfl⟩ : syracuseStep 8411111 = 12616667) B12616667
theorem B3323879 : Blo 1476558 3323879 := bstep (se 1 (by rfl) ⟨2492909, by rfl⟩ : syracuseStep 3323879 = 4985819) B4985819
theorem B3323897 : Blo 1476558 3323897 := bstep (se 2 (by rfl) ⟨1246461, by rfl⟩ : syracuseStep 3323897 = 2492923) B2492923
theorem B26941517 : Blo 1476558 26941517 := bstep (se 3 (by rfl) ⟨5051534, by rfl⟩ : syracuseStep 26941517 = 10103069) B10103069
theorem B3323987 : Blo 1476558 3323987 := bstep (se 1 (by rfl) ⟨2492990, by rfl⟩ : syracuseStep 3323987 = 4985981) B4985981
theorem B4208723 : Blo 1476558 4208723 := bstep (se 1 (by rfl) ⟨3156542, by rfl⟩ : syracuseStep 4208723 = 6313085) B6313085
theorem B3324059 : Blo 1476558 3324059 := bstep (se 1 (by rfl) ⟨2493044, by rfl⟩ : syracuseStep 3324059 = 4986089) B4986089
theorem B3324167 : Blo 1476558 3324167 := bstep (se 1 (by rfl) ⟨2493125, by rfl⟩ : syracuseStep 3324167 = 4986251) B4986251
theorem B7100779 : Blo 1476558 7100779 := bstep (se 1 (by rfl) ⟨5325584, by rfl⟩ : syracuseStep 7100779 = 10651169) B10651169
theorem B25237979 : Blo 1476558 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B8419859 : Blo 1476558 8419859 := bstep (se 1 (by rfl) ⟨6314894, by rfl⟩ : syracuseStep 8419859 = 12629789) B12629789
theorem B1661467 : Blo 1476558 1661467 := bstep (se 1 (by rfl) ⟨1246100, by rfl⟩ : syracuseStep 1661467 = 2492201) B2492201
theorem B3324473 : Blo 1476558 3324473 := bstep (se 2 (by rfl) ⟨1246677, by rfl⟩ : syracuseStep 3324473 = 2493355) B2493355
theorem B26950333 : Blo 1476558 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B110803715 : Blo 1476558 110803715 := bstep (se 1 (by rfl) ⟨83102786, by rfl⟩ : syracuseStep 110803715 = 166205573) B166205573
theorem B6740779 : Blo 1476558 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B5610323 : Blo 1476558 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B6314861 : Blo 1476558 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B4988033 : Blo 1476558 4988033 := bstep (se 2 (by rfl) ⟨1870512, by rfl⟩ : syracuseStep 4988033 = 3741025) B3741025
theorem B11213963 : Blo 1476558 11213963 := bstep (se 1 (by rfl) ⟨8410472, by rfl⟩ : syracuseStep 11213963 = 16820945) B16820945
theorem B4988087 : Blo 1476558 4988087 := bstep (se 1 (by rfl) ⟨3741065, by rfl⟩ : syracuseStep 4988087 = 7482131) B7482131
theorem B6397181 : Blo 1476558 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B3325193 : Blo 1476558 3325193 := bstep (se 2 (by rfl) ⟨1246947, by rfl⟩ : syracuseStep 3325193 = 2493895) B2493895
theorem B443006221 : Blo 1476558 443006221 := bstep (se 3 (by rfl) ⟨83063666, by rfl⟩ : syracuseStep 443006221 = 166127333) B166127333
theorem B7101857 : Blo 1476558 7101857 := bstep (se 2 (by rfl) ⟨2663196, by rfl⟩ : syracuseStep 7101857 = 5326393) B5326393
theorem B1662439 : Blo 1476558 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B4988843 : Blo 1476558 4988843 := bstep (se 1 (by rfl) ⟨3741632, by rfl⟩ : syracuseStep 4988843 = 7483265) B7483265
theorem B1662943 : Blo 1476558 1662943 := bstep (se 1 (by rfl) ⟨1247207, by rfl⟩ : syracuseStep 1662943 = 2494415) B2494415
theorem B5611751 : Blo 1476558 5611751 := bstep (se 1 (by rfl) ⟨4208813, by rfl⟩ : syracuseStep 5611751 = 8417627) B8417627
theorem B3326201 : Blo 1476558 3326201 := bstep (se 2 (by rfl) ⟨1247325, by rfl⟩ : syracuseStep 3326201 = 2494651) B2494651
theorem B1663231 : Blo 1476558 1663231 := bstep (se 1 (by rfl) ⟨1247423, by rfl⟩ : syracuseStep 1663231 = 2494847) B2494847
theorem B9462041 : Blo 1476558 9462041 := bstep (se 2 (by rfl) ⟨3548265, by rfl⟩ : syracuseStep 9462041 = 7096531) B7096531
theorem B12615983 : Blo 1476558 12615983 := bstep (se 1 (by rfl) ⟨9461987, by rfl⟩ : syracuseStep 12615983 = 18923975) B18923975
theorem B3326255 : Blo 1476558 3326255 := bstep (se 1 (by rfl) ⟨2494691, by rfl⟩ : syracuseStep 3326255 = 4989383) B4989383
theorem B3326471 : Blo 1476558 3326471 := bstep (se 1 (by rfl) ⟨2494853, by rfl⟩ : syracuseStep 3326471 = 4989707) B4989707
theorem B3326651 : Blo 1476558 3326651 := bstep (se 1 (by rfl) ⟨2494988, by rfl⟩ : syracuseStep 3326651 = 4989977) B4989977
theorem B6308675 : Blo 1476558 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B8987705 : Blo 1476558 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B5686685 : Blo 1476558 5686685 := bstep (se 3 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 5686685 = 2132507) B2132507
theorem B17974871 : Blo 1476558 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B5326507 : Blo 1476558 5326507 := bstep (se 1 (by rfl) ⟨3994880, by rfl⟩ : syracuseStep 5326507 = 7989761) B7989761
theorem B5613239 : Blo 1476558 5613239 := bstep (se 1 (by rfl) ⟨4209929, by rfl⟩ : syracuseStep 5613239 = 8419859) B8419859
theorem B22742795 : Blo 1476558 22742795 := bstep (se 1 (by rfl) ⟨17057096, by rfl⟩ : syracuseStep 22742795 = 34114193) B34114193
theorem B55428907 : Blo 1476558 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B73869143 : Blo 1476558 73869143 := bstep (se 1 (by rfl) ⟨55401857, by rfl⟩ : syracuseStep 73869143 = 110803715) B110803715
theorem B1476575 : Blo 1476558 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B1476635 : Blo 1476558 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B1476639 : Blo 1476558 1476639 := bstep (se 1 (by rfl) ⟨1107479, by rfl⟩ : syracuseStep 1476639 = 2214959) B2214959
theorem B1476655 : Blo 1476558 1476655 := bstep (se 1 (by rfl) ⟨1107491, by rfl⟩ : syracuseStep 1476655 = 2214983) B2214983
theorem B1476831 : Blo 1476558 1476831 := bstep (se 1 (by rfl) ⟨1107623, by rfl⟩ : syracuseStep 1476831 = 2215247) B2215247
theorem B1476891 : Blo 1476558 1476891 := bstep (se 1 (by rfl) ⟨1107668, by rfl⟩ : syracuseStep 1476891 = 2215337) B2215337
theorem B3737897 : Blo 1476558 3737897 := bstep (se 2 (by rfl) ⟨1401711, by rfl⟩ : syracuseStep 3737897 = 2803423) B2803423
theorem B26970479 : Blo 1476558 26970479 := bstep (se 1 (by rfl) ⟨20227859, by rfl⟩ : syracuseStep 26970479 = 40455719) B40455719
theorem B1476991 : Blo 1476558 1476991 := bstep (se 1 (by rfl) ⟨1107743, by rfl⟩ : syracuseStep 1476991 = 2215487) B2215487
theorem B1477167 : Blo 1476558 1477167 := bstep (se 1 (by rfl) ⟨1107875, by rfl⟩ : syracuseStep 1477167 = 2215751) B2215751
theorem B1477223 : Blo 1476558 1477223 := bstep (se 1 (by rfl) ⟨1107917, by rfl⟩ : syracuseStep 1477223 = 2215835) B2215835
theorem B2493031 : Blo 1476558 2493031 := bstep (se 1 (by rfl) ⟨1869773, by rfl⟩ : syracuseStep 2493031 = 3739547) B3739547
theorem B1477599 : Blo 1476558 1477599 := bstep (se 1 (by rfl) ⟨1108199, by rfl⟩ : syracuseStep 1477599 = 2216399) B2216399
theorem B1477627 : Blo 1476558 1477627 := bstep (se 1 (by rfl) ⟨1108220, by rfl⟩ : syracuseStep 1477627 = 2216441) B2216441
theorem B1477695 : Blo 1476558 1477695 := bstep (se 1 (by rfl) ⟨1108271, by rfl⟩ : syracuseStep 1477695 = 2216543) B2216543
theorem B2215019 : Blo 1476558 2215019 := bstep (se 1 (by rfl) ⟨1661264, by rfl⟩ : syracuseStep 2215019 = 3322529) B3322529
theorem B2804843 : Blo 1476558 2804843 := bstep (se 1 (by rfl) ⟨2103632, by rfl⟩ : syracuseStep 2804843 = 4207265) B4207265
theorem B6737039 : Blo 1476558 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B7482617 : Blo 1476558 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B16829693 : Blo 1476558 16829693 := bstep (se 3 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 16829693 = 6311135) B6311135
theorem B56765771 : Blo 1476558 56765771 := bstep (se 1 (by rfl) ⟨42574328, by rfl⟩ : syracuseStep 56765771 = 85148657) B85148657
theorem B2215259 : Blo 1476558 2215259 := bstep (se 1 (by rfl) ⟨1661444, by rfl⟩ : syracuseStep 2215259 = 3322889) B3322889
theorem B2493787 : Blo 1476558 2493787 := bstep (se 1 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 2493787 = 3740681) B3740681
theorem B2215289 : Blo 1476558 2215289 := bstep (se 2 (by rfl) ⟨830733, by rfl⟩ : syracuseStep 2215289 = 1661467) B1661467
theorem B2215295 : Blo 1476558 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B1478015 : Blo 1476558 1478015 := bstep (se 1 (by rfl) ⟨1108511, by rfl⟩ : syracuseStep 1478015 = 2217023) B2217023
theorem B1478043 : Blo 1476558 1478043 := bstep (se 1 (by rfl) ⟨1108532, by rfl⟩ : syracuseStep 1478043 = 2217065) B2217065
theorem B7482779 : Blo 1476558 7482779 := bstep (se 1 (by rfl) ⟨5612084, by rfl⟩ : syracuseStep 7482779 = 11224169) B11224169
theorem B1478111 : Blo 1476558 1478111 := bstep (se 1 (by rfl) ⟨1108583, by rfl⟩ : syracuseStep 1478111 = 2217167) B2217167
theorem B35933777 : Blo 1476558 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B1478247 : Blo 1476558 1478247 := bstep (se 1 (by rfl) ⟨1108685, by rfl⟩ : syracuseStep 1478247 = 2217371) B2217371
theorem B8416943 : Blo 1476558 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B1478395 : Blo 1476558 1478395 := bstep (se 1 (by rfl) ⟨1108796, by rfl⟩ : syracuseStep 1478395 = 2217593) B2217593
theorem B16838441 : Blo 1476558 16838441 := bstep (se 2 (by rfl) ⟨6314415, by rfl⟩ : syracuseStep 16838441 = 12628831) B12628831
theorem B4730687 : Blo 1476558 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B1478463 : Blo 1476558 1478463 := bstep (se 1 (by rfl) ⟨1108847, by rfl⟩ : syracuseStep 1478463 = 2217695) B2217695
theorem B1478527 : Blo 1476558 1478527 := bstep (se 1 (by rfl) ⟨1108895, by rfl⟩ : syracuseStep 1478527 = 2217791) B2217791
theorem B6311819 : Blo 1476558 6311819 := bstep (se 1 (by rfl) ⟨4733864, by rfl⟩ : syracuseStep 6311819 = 9467729) B9467729
theorem B5607407 : Blo 1476558 5607407 := bstep (se 1 (by rfl) ⟨4205555, by rfl⟩ : syracuseStep 5607407 = 8411111) B8411111
theorem B2215919 : Blo 1476558 2215919 := bstep (se 1 (by rfl) ⟨1661939, by rfl⟩ : syracuseStep 2215919 = 3323879) B3323879
theorem B2215931 : Blo 1476558 2215931 := bstep (se 1 (by rfl) ⟨1661948, by rfl⟩ : syracuseStep 2215931 = 3323897) B3323897
theorem B17961011 : Blo 1476558 17961011 := bstep (se 1 (by rfl) ⟨13470758, by rfl⟩ : syracuseStep 17961011 = 26941517) B26941517
theorem B2215991 : Blo 1476558 2215991 := bstep (se 1 (by rfl) ⟨1661993, by rfl⟩ : syracuseStep 2215991 = 3323987) B3323987
theorem B2805815 : Blo 1476558 2805815 := bstep (se 1 (by rfl) ⟨2104361, by rfl⟩ : syracuseStep 2805815 = 4208723) B4208723
theorem B2216039 : Blo 1476558 2216039 := bstep (se 1 (by rfl) ⟨1662029, by rfl⟩ : syracuseStep 2216039 = 3324059) B3324059
theorem B2216111 : Blo 1476558 2216111 := bstep (se 1 (by rfl) ⟨1662083, by rfl⟩ : syracuseStep 2216111 = 3324167) B3324167
theorem B51212569 : Blo 1476558 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B26972453 : Blo 1476558 26972453 := bstep (se 4 (by rfl) ⟨2528667, by rfl⟩ : syracuseStep 26972453 = 5057335) B5057335
theorem B2216315 : Blo 1476558 2216315 := bstep (se 1 (by rfl) ⟨1662236, by rfl⟩ : syracuseStep 2216315 = 3324473) B3324473
theorem B3740215 : Blo 1476558 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B2216585 : Blo 1476558 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B3322619 : Blo 1476558 3322619 := bstep (se 1 (by rfl) ⟨2491964, by rfl⟩ : syracuseStep 3322619 = 4983929) B4983929
theorem B7475975 : Blo 1476558 7475975 := bstep (se 1 (by rfl) ⟨5606981, by rfl⟩ : syracuseStep 7475975 = 11213963) B11213963
theorem B4985657 : Blo 1476558 4985657 := bstep (se 2 (by rfl) ⟨1869621, by rfl⟩ : syracuseStep 4985657 = 3739243) B3739243
theorem B4264787 : Blo 1476558 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B2216795 : Blo 1476558 2216795 := bstep (se 1 (by rfl) ⟨1662596, by rfl⟩ : syracuseStep 2216795 = 3325193) B3325193
theorem B3322835 : Blo 1476558 3322835 := bstep (se 1 (by rfl) ⟨2492126, by rfl⟩ : syracuseStep 3322835 = 4984253) B4984253
theorem B20223053 : Blo 1476558 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B2217257 : Blo 1476558 2217257 := bstep (se 2 (by rfl) ⟨831471, by rfl⟩ : syracuseStep 2217257 = 1662943) B1662943
theorem B3323303 : Blo 1476558 3323303 := bstep (se 1 (by rfl) ⟨2492477, by rfl⟩ : syracuseStep 3323303 = 4984955) B4984955
theorem B2217455 : Blo 1476558 2217455 := bstep (se 1 (by rfl) ⟨1663091, by rfl⟩ : syracuseStep 2217455 = 3326183) B3326183
theorem B7099913 : Blo 1476558 7099913 := bstep (se 2 (by rfl) ⟨2662467, by rfl⟩ : syracuseStep 7099913 = 5324935) B5324935
theorem B3323411 : Blo 1476558 3323411 := bstep (se 1 (by rfl) ⟨2492558, by rfl⟩ : syracuseStep 3323411 = 4985117) B4985117
theorem B3323483 : Blo 1476558 3323483 := bstep (se 1 (by rfl) ⟨2492612, by rfl⟩ : syracuseStep 3323483 = 4985225) B4985225
theorem B1578587 : Blo 1476558 1578587 := bstep (se 1 (by rfl) ⟨1183940, by rfl⟩ : syracuseStep 1578587 = 2367881) B2367881
theorem B7583393 : Blo 1476558 7583393 := bstep (se 2 (by rfl) ⟨2843772, by rfl⟩ : syracuseStep 7583393 = 5687545) B5687545
theorem B7984919 : Blo 1476558 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B9467705 : Blo 1476558 9467705 := bstep (se 2 (by rfl) ⟨3550389, by rfl⟩ : syracuseStep 9467705 = 7100779) B7100779
theorem B6313801 : Blo 1476558 6313801 := bstep (se 2 (by rfl) ⟨2367675, by rfl⟩ : syracuseStep 6313801 = 4735351) B4735351
theorem B2103131 : Blo 1476558 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B16832609 : Blo 1476558 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B3324095 : Blo 1476558 3324095 := bstep (se 1 (by rfl) ⟨2493071, by rfl⟩ : syracuseStep 3324095 = 4986143) B4986143
theorem B31955147 : Blo 1476558 31955147 := bstep (se 1 (by rfl) ⟨23966360, by rfl⟩ : syracuseStep 31955147 = 47932721) B47932721
theorem B22755599 : Blo 1476558 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B2996527 : Blo 1476558 2996527 := bstep (se 1 (by rfl) ⟨2247395, by rfl⟩ : syracuseStep 2996527 = 4494791) B4494791
theorem B4495711 : Blo 1476558 4495711 := bstep (se 1 (by rfl) ⟨3371783, by rfl⟩ : syracuseStep 4495711 = 6743567) B6743567
theorem B18930125 : Blo 1476558 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B4864655 : Blo 1476558 4864655 := bstep (se 1 (by rfl) ⟨3648491, by rfl⟩ : syracuseStep 4864655 = 7296983) B7296983
theorem B8985367 : Blo 1476558 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B1661863 : Blo 1476558 1661863 := bstep (se 1 (by rfl) ⟨1246397, by rfl⟩ : syracuseStep 1661863 = 2492795) B2492795
theorem B16825319 : Blo 1476558 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B590674961 : Blo 1476558 590674961 := bstep (se 2 (by rfl) ⟨221503110, by rfl⟩ : syracuseStep 590674961 = 443006221) B443006221
theorem B1662043 : Blo 1476558 1662043 := bstep (se 1 (by rfl) ⟨1246532, by rfl⟩ : syracuseStep 1662043 = 2493065) B2493065
theorem B4209907 : Blo 1476558 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B2661703 : Blo 1476558 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B5324201 : Blo 1476558 5324201 := bstep (se 2 (by rfl) ⟨1996575, by rfl⟩ : syracuseStep 5324201 = 3993151) B3993151
theorem B4734377 : Blo 1476558 4734377 := bstep (se 2 (by rfl) ⟨1775391, by rfl⟩ : syracuseStep 4734377 = 3550783) B3550783
theorem B3325355 : Blo 1476558 3325355 := bstep (se 1 (by rfl) ⟨2494016, by rfl⟩ : syracuseStep 3325355 = 4988033) B4988033
theorem B3325391 : Blo 1476558 3325391 := bstep (se 1 (by rfl) ⟨2494043, by rfl⟩ : syracuseStep 3325391 = 4988087) B4988087
theorem B4734571 : Blo 1476558 4734571 := bstep (se 1 (by rfl) ⟨3550928, by rfl⟩ : syracuseStep 4734571 = 7101857) B7101857
theorem B2105119 : Blo 1476558 2105119 := bstep (se 1 (by rfl) ⟨1578839, by rfl⟩ : syracuseStep 2105119 = 3157679) B3157679
theorem B12787627 : Blo 1476558 12787627 := bstep (se 1 (by rfl) ⟨9590720, by rfl⟩ : syracuseStep 12787627 = 19181441) B19181441
theorem B3325895 : Blo 1476558 3325895 := bstep (se 1 (by rfl) ⟨2494421, by rfl⟩ : syracuseStep 3325895 = 4988843) B4988843
theorem B7987187 : Blo 1476558 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B1575133229 : Blo 1476558 1575133229 := bstep (se 3 (by rfl) ⟨295337480, by rfl⟩ : syracuseStep 1575133229 = 590674961) B590674961
theorem B6308027 : Blo 1476558 6308027 := bstep (se 1 (by rfl) ⟨4731020, by rfl⟩ : syracuseStep 6308027 = 9462041) B9462041
theorem B17981635 : Blo 1476558 17981635 := bstep (se 1 (by rfl) ⟨13486226, by rfl⟩ : syracuseStep 17981635 = 26972453) B26972453
theorem B2843191 : Blo 1476558 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B18933101 : Blo 1476558 18933101 := bstep (se 3 (by rfl) ⟨3549956, by rfl⟩ : syracuseStep 18933101 = 7099913) B7099913
theorem B2491931 : Blo 1476558 2491931 := bstep (se 1 (by rfl) ⟨1868948, by rfl⟩ : syracuseStep 2491931 = 3737897) B3737897
theorem B5613209 : Blo 1476558 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B11216879 : Blo 1476558 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B1476679 : Blo 1476558 1476679 := bstep (se 1 (by rfl) ⟨1107509, by rfl⟩ : syracuseStep 1476679 = 2215019) B2215019
theorem B1869895 : Blo 1476558 1869895 := bstep (se 1 (by rfl) ⟨1402421, by rfl⟩ : syracuseStep 1869895 = 2804843) B2804843
theorem B4491359 : Blo 1476558 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B1476839 : Blo 1476558 1476839 := bstep (se 1 (by rfl) ⟨1107629, by rfl⟩ : syracuseStep 1476839 = 2215259) B2215259
theorem B1476859 : Blo 1476558 1476859 := bstep (se 1 (by rfl) ⟨1107644, by rfl⟩ : syracuseStep 1476859 = 2215289) B2215289
theorem B1476863 : Blo 1476558 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B3549467 : Blo 1476558 3549467 := bstep (se 1 (by rfl) ⟨2662100, by rfl⟩ : syracuseStep 3549467 = 5324201) B5324201
theorem B3156251 : Blo 1476558 3156251 := bstep (se 1 (by rfl) ⟨2367188, by rfl⟩ : syracuseStep 3156251 = 4734377) B4734377
theorem B23955851 : Blo 1476558 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B11225627 : Blo 1476558 11225627 := bstep (se 1 (by rfl) ⟨8419220, by rfl⟩ : syracuseStep 11225627 = 16838441) B16838441
theorem B17050169 : Blo 1476558 17050169 := bstep (se 2 (by rfl) ⟨6393813, by rfl⟩ : syracuseStep 17050169 = 12787627) B12787627
theorem B3738271 : Blo 1476558 3738271 := bstep (se 1 (by rfl) ⟨2803703, by rfl⟩ : syracuseStep 3738271 = 5607407) B5607407
theorem B1477279 : Blo 1476558 1477279 := bstep (se 1 (by rfl) ⟨1107959, by rfl⟩ : syracuseStep 1477279 = 2215919) B2215919
theorem B1477287 : Blo 1476558 1477287 := bstep (se 1 (by rfl) ⟨1107965, by rfl⟩ : syracuseStep 1477287 = 2215931) B2215931
theorem B1477327 : Blo 1476558 1477327 := bstep (se 1 (by rfl) ⟨1107995, by rfl⟩ : syracuseStep 1477327 = 2215991) B2215991
theorem B1870543 : Blo 1476558 1870543 := bstep (se 1 (by rfl) ⟨1402907, by rfl⟩ : syracuseStep 1870543 = 2805815) B2805815
theorem B1477359 : Blo 1476558 1477359 := bstep (se 1 (by rfl) ⟨1108019, by rfl⟩ : syracuseStep 1477359 = 2216039) B2216039
theorem B1477407 : Blo 1476558 1477407 := bstep (se 1 (by rfl) ⟨1108055, by rfl⟩ : syracuseStep 1477407 = 2216111) B2216111
theorem B1477543 : Blo 1476558 1477543 := bstep (se 1 (by rfl) ⟨1108157, by rfl⟩ : syracuseStep 1477543 = 2216315) B2216315
theorem B68283425 : Blo 1476558 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B1477723 : Blo 1476558 1477723 := bstep (se 1 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 1477723 = 2216585) B2216585
theorem B2215079 : Blo 1476558 2215079 := bstep (se 1 (by rfl) ⟨1661309, by rfl⟩ : syracuseStep 2215079 = 3322619) B3322619
theorem B4983983 : Blo 1476558 4983983 := bstep (se 1 (by rfl) ⟨3737987, by rfl⟩ : syracuseStep 4983983 = 7475975) B7475975
theorem B4205783 : Blo 1476558 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B1477863 : Blo 1476558 1477863 := bstep (se 1 (by rfl) ⟨1108397, by rfl⟩ : syracuseStep 1477863 = 2216795) B2216795
theorem B2215223 : Blo 1476558 2215223 := bstep (se 1 (by rfl) ⟨1661417, by rfl⟩ : syracuseStep 2215223 = 3322835) B3322835
theorem B5991803 : Blo 1476558 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B1478171 : Blo 1476558 1478171 := bstep (se 1 (by rfl) ⟨1108628, by rfl⟩ : syracuseStep 1478171 = 2217257) B2217257
theorem B2215535 : Blo 1476558 2215535 := bstep (se 1 (by rfl) ⟨1661651, by rfl⟩ : syracuseStep 2215535 = 3323303) B3323303
theorem B1478303 : Blo 1476558 1478303 := bstep (se 1 (by rfl) ⟨1108727, by rfl⟩ : syracuseStep 1478303 = 2217455) B2217455
theorem B2215607 : Blo 1476558 2215607 := bstep (se 1 (by rfl) ⟨1661705, by rfl⟩ : syracuseStep 2215607 = 3323411) B3323411
theorem B11980489 : Blo 1476558 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B2215655 : Blo 1476558 2215655 := bstep (se 1 (by rfl) ⟨1661741, by rfl⟩ : syracuseStep 2215655 = 3323483) B3323483
theorem B6311803 : Blo 1476558 6311803 := bstep (se 1 (by rfl) ⟨4733852, by rfl⟩ : syracuseStep 6311803 = 9467705) B9467705
theorem B2215817 : Blo 1476558 2215817 := bstep (se 2 (by rfl) ⟨830931, by rfl⟩ : syracuseStep 2215817 = 1661863) B1661863
theorem B2216057 : Blo 1476558 2216057 := bstep (se 2 (by rfl) ⟨831021, by rfl⟩ : syracuseStep 2216057 = 1662043) B1662043
theorem B2216063 : Blo 1476558 2216063 := bstep (se 1 (by rfl) ⟨1662047, by rfl⟩ : syracuseStep 2216063 = 3324095) B3324095
theorem B21303431 : Blo 1476558 21303431 := bstep (se 1 (by rfl) ⟨15977573, by rfl⟩ : syracuseStep 21303431 = 31955147) B31955147
theorem B12620083 : Blo 1476558 12620083 := bstep (se 1 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 12620083 = 18930125) B18930125
theorem B12972413 : Blo 1476558 12972413 := bstep (se 3 (by rfl) ⟨2432327, by rfl⟩ : syracuseStep 12972413 = 4864655) B4864655
theorem B20222381 : Blo 1476558 20222381 := bstep (se 3 (by rfl) ⟨3791696, by rfl⟩ : syracuseStep 20222381 = 7583393) B7583393
theorem B6312761 : Blo 1476558 6312761 := bstep (se 2 (by rfl) ⟨2367285, by rfl⟩ : syracuseStep 6312761 = 4734571) B4734571
theorem B11219795 : Blo 1476558 11219795 := bstep (se 1 (by rfl) ⟨8414846, by rfl⟩ : syracuseStep 11219795 = 16829693) B16829693
theorem B37843847 : Blo 1476558 37843847 := bstep (se 1 (by rfl) ⟨28382885, by rfl⟩ : syracuseStep 37843847 = 56765771) B56765771
theorem B5608349 : Blo 1476558 5608349 := bstep (se 3 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 5608349 = 2103131) B2103131
theorem B2216903 : Blo 1476558 2216903 := bstep (se 1 (by rfl) ⟨1662677, by rfl⟩ : syracuseStep 2216903 = 3325355) B3325355
theorem B2216927 : Blo 1476558 2216927 := bstep (se 1 (by rfl) ⟨1662695, by rfl⟩ : syracuseStep 2216927 = 3325391) B3325391
theorem B2806825 : Blo 1476558 2806825 := bstep (se 2 (by rfl) ⟨1052559, by rfl⟩ : syracuseStep 2806825 = 2105119) B2105119
theorem B73905209 : Blo 1476558 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B8418401 : Blo 1476558 8418401 := bstep (se 2 (by rfl) ⟨3156900, by rfl⟩ : syracuseStep 8418401 = 6313801) B6313801
theorem B4207879 : Blo 1476558 4207879 := bstep (se 1 (by rfl) ⟨3155909, by rfl⟩ : syracuseStep 4207879 = 6311819) B6311819
theorem B2217263 : Blo 1476558 2217263 := bstep (se 1 (by rfl) ⟨1662947, by rfl⟩ : syracuseStep 2217263 = 3325895) B3325895
theorem B11974007 : Blo 1476558 11974007 := bstep (se 1 (by rfl) ⟨8980505, by rfl⟩ : syracuseStep 11974007 = 17961011) B17961011
theorem B3741167 : Blo 1476558 3741167 := bstep (se 1 (by rfl) ⟨2805875, by rfl⟩ : syracuseStep 3741167 = 5611751) B5611751
theorem B2217467 : Blo 1476558 2217467 := bstep (se 1 (by rfl) ⟨1663100, by rfl⟩ : syracuseStep 2217467 = 3326201) B3326201
theorem B8410655 : Blo 1476558 8410655 := bstep (se 1 (by rfl) ⟨6307991, by rfl⟩ : syracuseStep 8410655 = 12615983) B12615983
theorem B2217503 : Blo 1476558 2217503 := bstep (se 1 (by rfl) ⟨1663127, by rfl⟩ : syracuseStep 2217503 = 3326255) B3326255
theorem B2217641 : Blo 1476558 2217641 := bstep (se 2 (by rfl) ⟨831615, by rfl⟩ : syracuseStep 2217641 = 1663231) B1663231
theorem B2217647 : Blo 1476558 2217647 := bstep (se 1 (by rfl) ⟨1663235, by rfl⟩ : syracuseStep 2217647 = 3326471) B3326471
theorem B3995369 : Blo 1476558 3995369 := bstep (se 2 (by rfl) ⟨1498263, by rfl⟩ : syracuseStep 3995369 = 2996527) B2996527
theorem B2217767 : Blo 1476558 2217767 := bstep (se 1 (by rfl) ⟨1663325, by rfl⟩ : syracuseStep 2217767 = 3326651) B3326651
theorem B5994281 : Blo 1476558 5994281 := bstep (se 2 (by rfl) ⟨2247855, by rfl⟩ : syracuseStep 5994281 = 4495711) B4495711
theorem B3323771 : Blo 1476558 3323771 := bstep (se 1 (by rfl) ⟨2492828, by rfl⟩ : syracuseStep 3323771 = 4985657) B4985657
theorem B13482035 : Blo 1476558 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B4986953 : Blo 1476558 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B3324041 : Blo 1476558 3324041 := bstep (se 2 (by rfl) ⟨1246515, by rfl⟩ : syracuseStep 3324041 = 2493031) B2493031
theorem B3791123 : Blo 1476558 3791123 := bstep (se 1 (by rfl) ⟨2843342, by rfl⟩ : syracuseStep 3791123 = 5686685) B5686685
theorem B11983247 : Blo 1476558 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B3742159 : Blo 1476558 3742159 := bstep (se 1 (by rfl) ⟨2806619, by rfl⟩ : syracuseStep 3742159 = 5613239) B5613239
theorem B15161863 : Blo 1476558 15161863 := bstep (se 1 (by rfl) ⟨11371397, by rfl⟩ : syracuseStep 15161863 = 22742795) B22742795
theorem B5323279 : Blo 1476558 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B11221739 : Blo 1476558 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B15170399 : Blo 1476558 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B4209565 : Blo 1476558 4209565 := bstep (se 3 (by rfl) ⟨789293, by rfl⟩ : syracuseStep 4209565 = 1578587) B1578587
theorem B17980319 : Blo 1476558 17980319 := bstep (se 1 (by rfl) ⟨13485239, by rfl⟩ : syracuseStep 17980319 = 26970479) B26970479
theorem B14195749 : Blo 1476558 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B3325049 : Blo 1476558 3325049 := bstep (se 2 (by rfl) ⟨1246893, by rfl⟩ : syracuseStep 3325049 = 2493787) B2493787
theorem B4988411 : Blo 1476558 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B7102009 : Blo 1476558 7102009 := bstep (se 2 (by rfl) ⟨2663253, by rfl⟩ : syracuseStep 7102009 = 5326507) B5326507
theorem B196984381 : Blo 1476558 196984381 := bstep (se 3 (by rfl) ⟨36934571, by rfl⟩ : syracuseStep 196984381 = 73869143) B73869143
theorem B4988519 : Blo 1476558 4988519 := bstep (se 1 (by rfl) ⟨3741389, by rfl⟩ : syracuseStep 4988519 = 7482779) B7482779
theorem B5611295 : Blo 1476558 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B3153791 : Blo 1476558 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B5324791 : Blo 1476558 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B16826777 : Blo 1476558 16826777 := bstep (se 2 (by rfl) ⟨6310041, by rfl⟩ : syracuseStep 16826777 = 12620083) B12620083
theorem B7479863 : Blo 1476558 7479863 := bstep (se 1 (by rfl) ⟨5609897, by rfl⟩ : syracuseStep 7479863 = 11219795) B11219795
theorem B11215421 : Blo 1476558 11215421 := bstep (se 3 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 11215421 = 4205783) B4205783
theorem B4989545 : Blo 1476558 4989545 := bstep (se 2 (by rfl) ⟨1871079, by rfl⟩ : syracuseStep 4989545 = 3742159) B3742159
theorem B5612267 : Blo 1476558 5612267 := bstep (se 1 (by rfl) ⟨4209200, by rfl⟩ : syracuseStep 5612267 = 8418401) B8418401
theorem B2663579 : Blo 1476558 2663579 := bstep (se 1 (by rfl) ⟨1997684, by rfl⟩ : syracuseStep 2663579 = 3995369) B3995369
theorem B5612753 : Blo 1476558 5612753 := bstep (se 2 (by rfl) ⟨2104782, by rfl⟩ : syracuseStep 5612753 = 4209565) B4209565
theorem B8988023 : Blo 1476558 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B7988831 : Blo 1476558 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B7481159 : Blo 1476558 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B11986879 : Blo 1476558 11986879 := bstep (se 1 (by rfl) ⟨8990159, by rfl⟩ : syracuseStep 11986879 = 17980319) B17980319
theorem B262645841 : Blo 1476558 262645841 := bstep (se 2 (by rfl) ⟨98492190, by rfl⟩ : syracuseStep 262645841 = 196984381) B196984381
theorem B15984749 : Blo 1476558 15984749 := bstep (se 3 (by rfl) ⟨2997140, by rfl⟩ : syracuseStep 15984749 = 5994281) B5994281
theorem B1476719 : Blo 1476558 1476719 := bstep (se 1 (by rfl) ⟨1107539, by rfl⟩ : syracuseStep 1476719 = 2215079) B2215079
theorem B1476815 : Blo 1476558 1476815 := bstep (se 1 (by rfl) ⟨1107611, by rfl⟩ : syracuseStep 1476815 = 2215223) B2215223
theorem B1477023 : Blo 1476558 1477023 := bstep (se 1 (by rfl) ⟨1107767, by rfl⟩ : syracuseStep 1477023 = 2215535) B2215535
theorem B1477071 : Blo 1476558 1477071 := bstep (se 1 (by rfl) ⟨1107803, by rfl⟩ : syracuseStep 1477071 = 2215607) B2215607
theorem B1477103 : Blo 1476558 1477103 := bstep (se 1 (by rfl) ⟨1107827, by rfl⟩ : syracuseStep 1477103 = 2215655) B2215655
theorem B8415737 : Blo 1476558 8415737 := bstep (se 2 (by rfl) ⟨3155901, by rfl⟩ : syracuseStep 8415737 = 6311803) B6311803
theorem B1477211 : Blo 1476558 1477211 := bstep (se 1 (by rfl) ⟨1107908, by rfl⟩ : syracuseStep 1477211 = 2215817) B2215817
theorem B1477371 : Blo 1476558 1477371 := bstep (se 1 (by rfl) ⟨1108028, by rfl⟩ : syracuseStep 1477371 = 2216057) B2216057
theorem B1477375 : Blo 1476558 1477375 := bstep (se 1 (by rfl) ⟨1108031, by rfl⟩ : syracuseStep 1477375 = 2216063) B2216063
theorem B2493193 : Blo 1476558 2493193 := bstep (se 2 (by rfl) ⟨934947, by rfl⟩ : syracuseStep 2493193 = 1869895) B1869895
theorem B4205351 : Blo 1476558 4205351 := bstep (se 1 (by rfl) ⟨3154013, by rfl⟩ : syracuseStep 4205351 = 6308027) B6308027
theorem B3738899 : Blo 1476558 3738899 := bstep (se 1 (by rfl) ⟨2804174, by rfl⟩ : syracuseStep 3738899 = 5608349) B5608349
theorem B1477935 : Blo 1476558 1477935 := bstep (se 1 (by rfl) ⟨1108451, by rfl⟩ : syracuseStep 1477935 = 2216903) B2216903
theorem B1477951 : Blo 1476558 1477951 := bstep (se 1 (by rfl) ⟨1108463, by rfl⟩ : syracuseStep 1477951 = 2216927) B2216927
theorem B7097705 : Blo 1476558 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B49270139 : Blo 1476558 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B9465245 : Blo 1476558 9465245 := bstep (se 3 (by rfl) ⟨1774733, by rfl⟩ : syracuseStep 9465245 = 3549467) B3549467
theorem B8416669 : Blo 1476558 8416669 := bstep (se 3 (by rfl) ⟨1578125, by rfl⟩ : syracuseStep 8416669 = 3156251) B3156251
theorem B1478175 : Blo 1476558 1478175 := bstep (se 1 (by rfl) ⟨1108631, by rfl⟩ : syracuseStep 1478175 = 2217263) B2217263
theorem B4984361 : Blo 1476558 4984361 := bstep (se 2 (by rfl) ⟨1869135, by rfl⟩ : syracuseStep 4984361 = 3738271) B3738271
theorem B7982671 : Blo 1476558 7982671 := bstep (se 1 (by rfl) ⟨5987003, by rfl⟩ : syracuseStep 7982671 = 11974007) B11974007
theorem B2494057 : Blo 1476558 2494057 := bstep (se 2 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 2494057 = 1870543) B1870543
theorem B2494111 : Blo 1476558 2494111 := bstep (se 1 (by rfl) ⟨1870583, by rfl⟩ : syracuseStep 2494111 = 3741167) B3741167
theorem B1478311 : Blo 1476558 1478311 := bstep (se 1 (by rfl) ⟨1108733, by rfl⟩ : syracuseStep 1478311 = 2217467) B2217467
theorem B5607103 : Blo 1476558 5607103 := bstep (se 1 (by rfl) ⟨4205327, by rfl⟩ : syracuseStep 5607103 = 8410655) B8410655
theorem B1478335 : Blo 1476558 1478335 := bstep (se 1 (by rfl) ⟨1108751, by rfl⟩ : syracuseStep 1478335 = 2217503) B2217503
theorem B1478427 : Blo 1476558 1478427 := bstep (se 1 (by rfl) ⟨1108820, by rfl⟩ : syracuseStep 1478427 = 2217641) B2217641
theorem B1478431 : Blo 1476558 1478431 := bstep (se 1 (by rfl) ⟨1108823, by rfl⟩ : syracuseStep 1478431 = 2217647) B2217647
theorem B1478511 : Blo 1476558 1478511 := bstep (se 1 (by rfl) ⟨1108883, by rfl⟩ : syracuseStep 1478511 = 2217767) B2217767
theorem B2215847 : Blo 1476558 2215847 := bstep (se 1 (by rfl) ⟨1661885, by rfl⟩ : syracuseStep 2215847 = 3323771) B3323771
theorem B18927665 : Blo 1476558 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B2994239 : Blo 1476558 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B2216027 : Blo 1476558 2216027 := bstep (se 1 (by rfl) ⟨1662020, by rfl⟩ : syracuseStep 2216027 = 3324041) B3324041
theorem B2527415 : Blo 1476558 2527415 := bstep (se 1 (by rfl) ⟨1895561, by rfl⟩ : syracuseStep 2527415 = 3791123) B3791123
theorem B15970567 : Blo 1476558 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B7483751 : Blo 1476558 7483751 := bstep (se 1 (by rfl) ⟨5612813, by rfl⟩ : syracuseStep 7483751 = 11225627) B11225627
theorem B11366779 : Blo 1476558 11366779 := bstep (se 1 (by rfl) ⟨8525084, by rfl⟩ : syracuseStep 11366779 = 17050169) B17050169
theorem B10113599 : Blo 1476558 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B2216699 : Blo 1476558 2216699 := bstep (se 1 (by rfl) ⟨1662524, by rfl⟩ : syracuseStep 2216699 = 3325049) B3325049
theorem B3322655 : Blo 1476558 3322655 := bstep (se 1 (by rfl) ⟨2491991, by rfl⟩ : syracuseStep 3322655 = 4983983) B4983983
theorem B3994535 : Blo 1476558 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B3740863 : Blo 1476558 3740863 := bstep (se 1 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 3740863 = 5611295) B5611295
theorem B2102527 : Blo 1476558 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B7099721 : Blo 1476558 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B14202287 : Blo 1476558 14202287 := bstep (se 1 (by rfl) ⟨10651715, by rfl⟩ : syracuseStep 14202287 = 21303431) B21303431
theorem B4200355277 : Blo 1476558 4200355277 := bstep (se 3 (by rfl) ⟨787566614, by rfl⟩ : syracuseStep 4200355277 = 1575133229) B1575133229
theorem B23975513 : Blo 1476558 23975513 := bstep (se 2 (by rfl) ⟨8990817, by rfl⟩ : syracuseStep 23975513 = 17981635) B17981635
theorem B13481587 : Blo 1476558 13481587 := bstep (se 1 (by rfl) ⟨10111190, by rfl⟩ : syracuseStep 13481587 = 20222381) B20222381
theorem B4208507 : Blo 1476558 4208507 := bstep (se 1 (by rfl) ⟨3156380, by rfl⟩ : syracuseStep 4208507 = 6312761) B6312761
theorem B25229231 : Blo 1476558 25229231 := bstep (se 1 (by rfl) ⟨18921923, by rfl⟩ : syracuseStep 25229231 = 37843847) B37843847
theorem B20215817 : Blo 1476558 20215817 := bstep (se 2 (by rfl) ⟨7580931, by rfl⟩ : syracuseStep 20215817 = 15161863) B15161863
theorem B3790921 : Blo 1476558 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B12622067 : Blo 1476558 12622067 := bstep (se 1 (by rfl) ⟨9466550, by rfl⟩ : syracuseStep 12622067 = 18933101) B18933101
theorem B34593101 : Blo 1476558 34593101 := bstep (se 3 (by rfl) ⟨6486206, by rfl⟩ : syracuseStep 34593101 = 12972413) B12972413
theorem B1661287 : Blo 1476558 1661287 := bstep (se 1 (by rfl) ⟨1245965, by rfl⟩ : syracuseStep 1661287 = 2491931) B2491931
theorem B3742139 : Blo 1476558 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B7477919 : Blo 1476558 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B3324635 : Blo 1476558 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B3742433 : Blo 1476558 3742433 := bstep (se 2 (by rfl) ⟨1403412, by rfl⟩ : syracuseStep 3742433 = 2806825) B2806825
theorem B5610505 : Blo 1476558 5610505 := bstep (se 2 (by rfl) ⟨2103939, by rfl⟩ : syracuseStep 5610505 = 4207879) B4207879
theorem B45522283 : Blo 1476558 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B9469345 : Blo 1476558 9469345 := bstep (se 2 (by rfl) ⟨3551004, by rfl⟩ : syracuseStep 9469345 = 7102009) B7102009
theorem B15973985 : Blo 1476558 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B3325607 : Blo 1476558 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B3325679 : Blo 1476558 3325679 := bstep (se 1 (by rfl) ⟨2494259, by rfl⟩ : syracuseStep 3325679 = 4988519) B4988519
theorem B5054561 : Blo 1476558 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B4989167 : Blo 1476558 4989167 := bstep (se 1 (by rfl) ⟨3741875, by rfl⟩ : syracuseStep 4989167 = 7483751) B7483751
theorem B3326363 : Blo 1476558 3326363 := bstep (se 1 (by rfl) ⟨2494772, by rfl⟩ : syracuseStep 3326363 = 4989545) B4989545
theorem B15155705 : Blo 1476558 15155705 := bstep (se 2 (by rfl) ⟨5683389, by rfl⟩ : syracuseStep 15155705 = 11366779) B11366779
theorem B15983675 : Blo 1476558 15983675 := bstep (se 1 (by rfl) ⟨11987756, by rfl⟩ : syracuseStep 15983675 = 23975513) B23975513
theorem B5325887 : Blo 1476558 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B16819487 : Blo 1476558 16819487 := bstep (se 1 (by rfl) ⟨12614615, by rfl⟩ : syracuseStep 16819487 = 25229231) B25229231
theorem B13477211 : Blo 1476558 13477211 := bstep (se 1 (by rfl) ⟨10107908, by rfl⟩ : syracuseStep 13477211 = 20215817) B20215817
theorem B7480673 : Blo 1476558 7480673 := bstep (se 2 (by rfl) ⟨2805252, by rfl⟩ : syracuseStep 7480673 = 5610505) B5610505
theorem B175097227 : Blo 1476558 175097227 := bstep (se 1 (by rfl) ⟨131322920, by rfl⟩ : syracuseStep 175097227 = 262645841) B262645841
theorem B8414711 : Blo 1476558 8414711 := bstep (se 1 (by rfl) ⟨6311033, by rfl⟩ : syracuseStep 8414711 = 12622067) B12622067
theorem B26969597 : Blo 1476558 26969597 := bstep (se 3 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 26969597 = 10113599) B10113599
theorem B23062067 : Blo 1476558 23062067 := bstep (se 1 (by rfl) ⟨17296550, by rfl⟩ : syracuseStep 23062067 = 34593101) B34593101
theorem B60696377 : Blo 1476558 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B2803567 : Blo 1476558 2803567 := bstep (se 1 (by rfl) ⟨2102675, by rfl⟩ : syracuseStep 2803567 = 4205351) B4205351
theorem B12625793 : Blo 1476558 12625793 := bstep (se 2 (by rfl) ⟨4734672, by rfl⟩ : syracuseStep 12625793 = 9469345) B9469345
theorem B10643561 : Blo 1476558 10643561 := bstep (se 2 (by rfl) ⟨3991335, by rfl⟩ : syracuseStep 10643561 = 7982671) B7982671
theorem B17975449 : Blo 1476558 17975449 := bstep (se 2 (by rfl) ⟨6740793, by rfl⟩ : syracuseStep 17975449 = 13481587) B13481587
theorem B2492599 : Blo 1476558 2492599 := bstep (se 1 (by rfl) ⟨1869449, by rfl⟩ : syracuseStep 2492599 = 3738899) B3738899
theorem B6310163 : Blo 1476558 6310163 := bstep (se 1 (by rfl) ⟨4732622, by rfl⟩ : syracuseStep 6310163 = 9465245) B9465245
theorem B10652093 : Blo 1476558 10652093 := bstep (se 3 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 10652093 = 3994535) B3994535
theorem B1477231 : Blo 1476558 1477231 := bstep (se 1 (by rfl) ⟨1107923, by rfl⟩ : syracuseStep 1477231 = 2215847) B2215847
theorem B12618443 : Blo 1476558 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B1477351 : Blo 1476558 1477351 := bstep (se 1 (by rfl) ⟨1108013, by rfl⟩ : syracuseStep 1477351 = 2216027) B2216027
theorem B11217851 : Blo 1476558 11217851 := bstep (se 1 (by rfl) ⟨8413388, by rfl⟩ : syracuseStep 11217851 = 16826777) B16826777
theorem B42625997 : Blo 1476558 42625997 := bstep (se 3 (by rfl) ⟨7992374, by rfl⟩ : syracuseStep 42625997 = 15984749) B15984749
theorem B21294089 : Blo 1476558 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B2215049 : Blo 1476558 2215049 := bstep (se 2 (by rfl) ⟨830643, by rfl⟩ : syracuseStep 2215049 = 1661287) B1661287
theorem B1477799 : Blo 1476558 1477799 := bstep (se 1 (by rfl) ⟨1108349, by rfl⟩ : syracuseStep 1477799 = 2216699) B2216699
theorem B2215103 : Blo 1476558 2215103 := bstep (se 1 (by rfl) ⟨1661327, by rfl⟩ : syracuseStep 2215103 = 3322655) B3322655
theorem B5992015 : Blo 1476558 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B2805671 : Blo 1476558 2805671 := bstep (se 1 (by rfl) ⟨2104253, by rfl⟩ : syracuseStep 2805671 = 4208507) B4208507
theorem B2494759 : Blo 1476558 2494759 := bstep (se 1 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 2494759 = 3742139) B3742139
theorem B4985279 : Blo 1476558 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B2216423 : Blo 1476558 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B2494955 : Blo 1476558 2494955 := bstep (se 1 (by rfl) ⟨1871216, by rfl⟩ : syracuseStep 2494955 = 3742433) B3742433
theorem B4731803 : Blo 1476558 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B32846759 : Blo 1476558 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B7476137 : Blo 1476558 7476137 := bstep (se 2 (by rfl) ⟨2803551, by rfl⟩ : syracuseStep 7476137 = 5607103) B5607103
theorem B3322907 : Blo 1476558 3322907 := bstep (se 1 (by rfl) ⟨2492180, by rfl⟩ : syracuseStep 3322907 = 4984361) B4984361
theorem B2217071 : Blo 1476558 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B2217119 : Blo 1476558 2217119 := bstep (se 1 (by rfl) ⟨1662839, by rfl⟩ : syracuseStep 2217119 = 3325679) B3325679
theorem B1996159 : Blo 1476558 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B1684943 : Blo 1476558 1684943 := bstep (se 1 (by rfl) ⟨1263707, by rfl⟩ : syracuseStep 1684943 = 2527415) B2527415
theorem B4986575 : Blo 1476558 4986575 := bstep (se 1 (by rfl) ⟨3739931, by rfl⟩ : syracuseStep 4986575 = 7479863) B7479863
theorem B7476947 : Blo 1476558 7476947 := bstep (se 1 (by rfl) ⟨5607710, by rfl⟩ : syracuseStep 7476947 = 11215421) B11215421
theorem B3741511 : Blo 1476558 3741511 := bstep (se 1 (by rfl) ⟨2806133, by rfl⟩ : syracuseStep 3741511 = 5612267) B5612267
theorem B1775719 : Blo 1476558 1775719 := bstep (se 1 (by rfl) ⟨1331789, by rfl⟩ : syracuseStep 1775719 = 2663579) B2663579
theorem B3741835 : Blo 1476558 3741835 := bstep (se 1 (by rfl) ⟨2806376, by rfl⟩ : syracuseStep 3741835 = 5612753) B5612753
theorem B4733147 : Blo 1476558 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B9468191 : Blo 1476558 9468191 := bstep (se 1 (by rfl) ⟨7101143, by rfl⟩ : syracuseStep 9468191 = 14202287) B14202287
theorem B2800236851 : Blo 1476558 2800236851 := bstep (se 1 (by rfl) ⟨2100177638, by rfl⟩ : syracuseStep 2800236851 = 4200355277) B4200355277
theorem B3324257 : Blo 1476558 3324257 := bstep (se 2 (by rfl) ⟨1246596, by rfl⟩ : syracuseStep 3324257 = 2493193) B2493193
theorem B4987439 : Blo 1476558 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B11213477 : Blo 1476558 11213477 := bstep (se 4 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 11213477 = 2102527) B2102527
theorem B4987817 : Blo 1476558 4987817 := bstep (se 2 (by rfl) ⟨1870431, by rfl⟩ : syracuseStep 4987817 = 3740863) B3740863
theorem B5610491 : Blo 1476558 5610491 := bstep (se 1 (by rfl) ⟨4207868, by rfl⟩ : syracuseStep 5610491 = 8415737) B8415737
theorem B11222225 : Blo 1476558 11222225 := bstep (se 2 (by rfl) ⟨4208334, by rfl⟩ : syracuseStep 11222225 = 8416669) B8416669
theorem B3325409 : Blo 1476558 3325409 := bstep (se 2 (by rfl) ⟨1247028, by rfl⟩ : syracuseStep 3325409 = 2494057) B2494057
theorem B3325481 : Blo 1476558 3325481 := bstep (se 2 (by rfl) ⟨1247055, by rfl⟩ : syracuseStep 3325481 = 2494111) B2494111
theorem B10649323 : Blo 1476558 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B15982505 : Blo 1476558 15982505 := bstep (se 2 (by rfl) ⟨5993439, by rfl⟩ : syracuseStep 15982505 = 11986879) B11986879
theorem B2367625 : Blo 1476558 2367625 := bstep (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) B1775719
theorem B3326111 : Blo 1476558 3326111 := bstep (se 1 (by rfl) ⟨2494583, by rfl⟩ : syracuseStep 3326111 = 4989167) B4989167
theorem B4989113 : Blo 1476558 4989113 := bstep (se 2 (by rfl) ⟨1870917, by rfl⟩ : syracuseStep 4989113 = 3741835) B3741835
theorem B1663303 : Blo 1476558 1663303 := bstep (se 1 (by rfl) ⟨1247477, by rfl⟩ : syracuseStep 1663303 = 2494955) B2494955
theorem B3326345 : Blo 1476558 3326345 := bstep (se 2 (by rfl) ⟨1247379, by rfl⟩ : syracuseStep 3326345 = 2494759) B2494759
theorem B3154535 : Blo 1476558 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B21897839 : Blo 1476558 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B7095707 : Blo 1476558 7095707 := bstep (se 1 (by rfl) ⟨5321780, by rfl⟩ : syracuseStep 7095707 = 10643561) B10643561
theorem B3155431 : Blo 1476558 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B1476699 : Blo 1476558 1476699 := bstep (se 1 (by rfl) ⟨1107524, by rfl⟩ : syracuseStep 1476699 = 2215049) B2215049
theorem B7989353 : Blo 1476558 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B1476735 : Blo 1476558 1476735 := bstep (se 1 (by rfl) ⟨1107551, by rfl⟩ : syracuseStep 1476735 = 2215103) B2215103
theorem B7481483 : Blo 1476558 7481483 := bstep (se 1 (by rfl) ⟨5611112, by rfl⟩ : syracuseStep 7481483 = 11222225) B11222225
theorem B14199097 : Blo 1476558 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B3738089 : Blo 1476558 3738089 := bstep (se 2 (by rfl) ⟨1401783, by rfl⟩ : syracuseStep 3738089 = 2803567) B2803567
theorem B1870447 : Blo 1476558 1870447 := bstep (se 1 (by rfl) ⟨1402835, by rfl⟩ : syracuseStep 1870447 = 2805671) B2805671
theorem B3369707 : Blo 1476558 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B1477615 : Blo 1476558 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B4984091 : Blo 1476558 4984091 := bstep (se 1 (by rfl) ⟨3738068, by rfl⟩ : syracuseStep 4984091 = 7476137) B7476137
theorem B2215271 : Blo 1476558 2215271 := bstep (se 1 (by rfl) ⟨1661453, by rfl⟩ : syracuseStep 2215271 = 3322907) B3322907
theorem B3550591 : Blo 1476558 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B1478047 : Blo 1476558 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B1478079 : Blo 1476558 1478079 := bstep (se 1 (by rfl) ⟨1108559, by rfl⟩ : syracuseStep 1478079 = 2217119) B2217119
theorem B4984631 : Blo 1476558 4984631 := bstep (se 1 (by rfl) ⟨3738473, by rfl⟩ : syracuseStep 4984631 = 7476947) B7476947
theorem B40464251 : Blo 1476558 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B8417195 : Blo 1476558 8417195 := bstep (se 1 (by rfl) ⟨6312896, by rfl⟩ : syracuseStep 8417195 = 12625793) B12625793
theorem B40415213 : Blo 1476558 40415213 := bstep (se 3 (by rfl) ⟨7577852, by rfl⟩ : syracuseStep 40415213 = 15155705) B15155705
theorem B4206775 : Blo 1476558 4206775 := bstep (se 1 (by rfl) ⟨3155081, by rfl⟩ : syracuseStep 4206775 = 6310163) B6310163
theorem B6312127 : Blo 1476558 6312127 := bstep (se 1 (by rfl) ⟨4734095, by rfl⟩ : syracuseStep 6312127 = 9468191) B9468191
theorem B2216171 : Blo 1476558 2216171 := bstep (se 1 (by rfl) ⟨1662128, by rfl⟩ : syracuseStep 2216171 = 3324257) B3324257
theorem B7475651 : Blo 1476558 7475651 := bstep (se 1 (by rfl) ⟨5606738, by rfl⟩ : syracuseStep 7475651 = 11213477) B11213477
theorem B3740327 : Blo 1476558 3740327 := bstep (se 1 (by rfl) ⟨2805245, by rfl⟩ : syracuseStep 3740327 = 5610491) B5610491
theorem B2216939 : Blo 1476558 2216939 := bstep (se 1 (by rfl) ⟨1662704, by rfl⟩ : syracuseStep 2216939 = 3325409) B3325409
theorem B2216987 : Blo 1476558 2216987 := bstep (se 1 (by rfl) ⟨1662740, by rfl⟩ : syracuseStep 2216987 = 3325481) B3325481
theorem B10655003 : Blo 1476558 10655003 := bstep (se 1 (by rfl) ⟨7991252, by rfl⟩ : syracuseStep 10655003 = 15982505) B15982505
theorem B23967265 : Blo 1476558 23967265 := bstep (se 2 (by rfl) ⟨8987724, by rfl⟩ : syracuseStep 23967265 = 17975449) B17975449
theorem B3323465 : Blo 1476558 3323465 := bstep (se 2 (by rfl) ⟨1246299, by rfl⟩ : syracuseStep 3323465 = 2492599) B2492599
theorem B2217575 : Blo 1476558 2217575 := bstep (se 1 (by rfl) ⟨1663181, by rfl⟩ : syracuseStep 2217575 = 3326363) B3326363
theorem B3323519 : Blo 1476558 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B10655783 : Blo 1476558 10655783 := bstep (se 1 (by rfl) ⟨7991837, by rfl⟩ : syracuseStep 10655783 = 15983675) B15983675
theorem B11212991 : Blo 1476558 11212991 := bstep (se 1 (by rfl) ⟨8409743, by rfl⟩ : syracuseStep 11212991 = 16819487) B16819487
theorem B8984807 : Blo 1476558 8984807 := bstep (se 1 (by rfl) ⟨6738605, by rfl⟩ : syracuseStep 8984807 = 13477211) B13477211
theorem B4987115 : Blo 1476558 4987115 := bstep (se 1 (by rfl) ⟨3740336, by rfl⟩ : syracuseStep 4987115 = 7480673) B7480673
theorem B5609807 : Blo 1476558 5609807 := bstep (se 1 (by rfl) ⟨4207355, by rfl⟩ : syracuseStep 5609807 = 8414711) B8414711
theorem B17979731 : Blo 1476558 17979731 := bstep (se 1 (by rfl) ⟨13484798, by rfl⟩ : syracuseStep 17979731 = 26969597) B26969597
theorem B15374711 : Blo 1476558 15374711 := bstep (se 1 (by rfl) ⟨11531033, by rfl⟩ : syracuseStep 15374711 = 23062067) B23062067
theorem B3324383 : Blo 1476558 3324383 := bstep (se 1 (by rfl) ⟨2493287, by rfl⟩ : syracuseStep 3324383 = 4986575) B4986575
theorem B1866824567 : Blo 1476558 1866824567 := bstep (se 1 (by rfl) ⟨1400118425, by rfl⟩ : syracuseStep 1866824567 = 2800236851) B2800236851
theorem B7101395 : Blo 1476558 7101395 := bstep (se 1 (by rfl) ⟨5326046, by rfl⟩ : syracuseStep 7101395 = 10652093) B10652093
theorem B3324959 : Blo 1476558 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B8412295 : Blo 1476558 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B2661545 : Blo 1476558 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B233462969 : Blo 1476558 233462969 := bstep (se 2 (by rfl) ⟨87548613, by rfl⟩ : syracuseStep 233462969 = 175097227) B175097227
theorem B3325211 : Blo 1476558 3325211 := bstep (se 1 (by rfl) ⟨2493908, by rfl⟩ : syracuseStep 3325211 = 4987817) B4987817
theorem B7478567 : Blo 1476558 7478567 := bstep (se 1 (by rfl) ⟨5608925, by rfl⟩ : syracuseStep 7478567 = 11217851) B11217851
theorem B28417331 : Blo 1476558 28417331 := bstep (se 1 (by rfl) ⟨21312998, by rfl⟩ : syracuseStep 28417331 = 42625997) B42625997
theorem B14196059 : Blo 1476558 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B17972725 : Blo 1476558 17972725 := bstep (se 5 (by rfl) ⟨842471, by rfl⟩ : syracuseStep 17972725 = 1684943) B1684943
theorem B4988681 : Blo 1476558 4988681 := bstep (se 2 (by rfl) ⟨1870755, by rfl⟩ : syracuseStep 4988681 = 3741511) B3741511
theorem B3326075 : Blo 1476558 3326075 := bstep (se 1 (by rfl) ⟨2494556, by rfl⟩ : syracuseStep 3326075 = 4989113) B4989113
theorem B14598559 : Blo 1476558 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B18932129 : Blo 1476558 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B7103335 : Blo 1476558 7103335 := bstep (se 1 (by rfl) ⟨5327501, by rfl⟩ : syracuseStep 7103335 = 10655003) B10655003
theorem B7103855 : Blo 1476558 7103855 := bstep (se 1 (by rfl) ⟨5327891, by rfl⟩ : syracuseStep 7103855 = 10655783) B10655783
theorem B5326235 : Blo 1476558 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B5989871 : Blo 1476558 5989871 := bstep (se 1 (by rfl) ⟨4492403, by rfl⟩ : syracuseStep 5989871 = 8984807) B8984807
theorem B11216393 : Blo 1476558 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B11986487 : Blo 1476558 11986487 := bstep (se 1 (by rfl) ⟨8989865, by rfl⟩ : syracuseStep 11986487 = 17979731) B17979731
theorem B2492059 : Blo 1476558 2492059 := bstep (se 1 (by rfl) ⟨1869044, by rfl⟩ : syracuseStep 2492059 = 3738089) B3738089
theorem B2246471 : Blo 1476558 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B23963633 : Blo 1476558 23963633 := bstep (se 2 (by rfl) ⟨8986362, by rfl⟩ : syracuseStep 23963633 = 17972725) B17972725
theorem B155641979 : Blo 1476558 155641979 := bstep (se 1 (by rfl) ⟨116731484, by rfl⟩ : syracuseStep 155641979 = 233462969) B233462969
theorem B9464039 : Blo 1476558 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B1476847 : Blo 1476558 1476847 := bstep (se 1 (by rfl) ⟨1107635, by rfl⟩ : syracuseStep 1476847 = 2215271) B2215271
theorem B1477447 : Blo 1476558 1477447 := bstep (se 1 (by rfl) ⟨1108085, by rfl⟩ : syracuseStep 1477447 = 2216171) B2216171
theorem B3156833 : Blo 1476558 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B8416169 : Blo 1476558 8416169 := bstep (se 2 (by rfl) ⟨3156063, by rfl⟩ : syracuseStep 8416169 = 6312127) B6312127
theorem B4983767 : Blo 1476558 4983767 := bstep (se 1 (by rfl) ⟨3737825, by rfl⟩ : syracuseStep 4983767 = 7475651) B7475651
theorem B7097453 : Blo 1476558 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B2493551 : Blo 1476558 2493551 := bstep (se 1 (by rfl) ⟨1870163, by rfl⟩ : syracuseStep 2493551 = 3740327) B3740327
theorem B1477959 : Blo 1476558 1477959 := bstep (se 1 (by rfl) ⟨1108469, by rfl⟩ : syracuseStep 1477959 = 2216939) B2216939
theorem B1477991 : Blo 1476558 1477991 := bstep (se 1 (by rfl) ⟨1108493, by rfl⟩ : syracuseStep 1477991 = 2216987) B2216987
theorem B2493929 : Blo 1476558 2493929 := bstep (se 2 (by rfl) ⟨935223, by rfl⟩ : syracuseStep 2493929 = 1870447) B1870447
theorem B4730471 : Blo 1476558 4730471 := bstep (se 1 (by rfl) ⟨3547853, by rfl⟩ : syracuseStep 4730471 = 7095707) B7095707
theorem B2215643 : Blo 1476558 2215643 := bstep (se 1 (by rfl) ⟨1661732, by rfl⟩ : syracuseStep 2215643 = 3323465) B3323465
theorem B1478383 : Blo 1476558 1478383 := bstep (se 1 (by rfl) ⟨1108787, by rfl⟩ : syracuseStep 1478383 = 2217575) B2217575
theorem B2215679 : Blo 1476558 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B7475327 : Blo 1476558 7475327 := bstep (se 1 (by rfl) ⟨5606495, by rfl⟩ : syracuseStep 7475327 = 11212991) B11212991
theorem B3739871 : Blo 1476558 3739871 := bstep (se 1 (by rfl) ⟨2804903, by rfl⟩ : syracuseStep 3739871 = 5609807) B5609807
theorem B2216255 : Blo 1476558 2216255 := bstep (se 1 (by rfl) ⟨1662191, by rfl⟩ : syracuseStep 2216255 = 3324383) B3324383
theorem B1244549711 : Blo 1476558 1244549711 := bstep (se 1 (by rfl) ⟨933412283, by rfl⟩ : syracuseStep 1244549711 = 1866824567) B1866824567
theorem B4207241 : Blo 1476558 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B2216639 : Blo 1476558 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B3322727 : Blo 1476558 3322727 := bstep (se 1 (by rfl) ⟨2492045, by rfl⟩ : syracuseStep 3322727 = 4984091) B4984091
theorem B2216807 : Blo 1476558 2216807 := bstep (se 1 (by rfl) ⟨1662605, by rfl⟩ : syracuseStep 2216807 = 3325211) B3325211
theorem B4985711 : Blo 1476558 4985711 := bstep (se 1 (by rfl) ⟨3739283, by rfl⟩ : syracuseStep 4985711 = 7478567) B7478567
theorem B18944887 : Blo 1476558 18944887 := bstep (se 1 (by rfl) ⟨14208665, by rfl⟩ : syracuseStep 18944887 = 28417331) B28417331
theorem B3323087 : Blo 1476558 3323087 := bstep (se 1 (by rfl) ⟨2492315, by rfl⟩ : syracuseStep 3323087 = 4984631) B4984631
theorem B2217407 : Blo 1476558 2217407 := bstep (se 1 (by rfl) ⟨1663055, by rfl⟩ : syracuseStep 2217407 = 3326111) B3326111
theorem B5609033 : Blo 1476558 5609033 := bstep (se 2 (by rfl) ⟨2103387, by rfl⟩ : syracuseStep 5609033 = 4206775) B4206775
theorem B2217563 : Blo 1476558 2217563 := bstep (se 1 (by rfl) ⟨1663172, by rfl⟩ : syracuseStep 2217563 = 3326345) B3326345
theorem B2103023 : Blo 1476558 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B2217737 : Blo 1476558 2217737 := bstep (se 2 (by rfl) ⟨831651, by rfl⟩ : syracuseStep 2217737 = 1663303) B1663303
theorem B40999229 : Blo 1476558 40999229 := bstep (se 3 (by rfl) ⟨7687355, by rfl⟩ : syracuseStep 40999229 = 15374711) B15374711
theorem B4987655 : Blo 1476558 4987655 := bstep (se 1 (by rfl) ⟨3740741, by rfl⟩ : syracuseStep 4987655 = 7481483) B7481483
theorem B3324743 : Blo 1476558 3324743 := bstep (se 1 (by rfl) ⟨2493557, by rfl⟩ : syracuseStep 3324743 = 4987115) B4987115
theorem B4734121 : Blo 1476558 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B4734263 : Blo 1476558 4734263 := bstep (se 1 (by rfl) ⟨3550697, by rfl⟩ : syracuseStep 4734263 = 7101395) B7101395
theorem B31956353 : Blo 1476558 31956353 := bstep (se 2 (by rfl) ⟨11983632, by rfl⟩ : syracuseStep 31956353 = 23967265) B23967265
theorem B3325787 : Blo 1476558 3325787 := bstep (se 1 (by rfl) ⟨2494340, by rfl⟩ : syracuseStep 3325787 = 4988681) B4988681
theorem B26976167 : Blo 1476558 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B5611463 : Blo 1476558 5611463 := bstep (se 1 (by rfl) ⟨4208597, by rfl⟩ : syracuseStep 5611463 = 8417195) B8417195
theorem B26943475 : Blo 1476558 26943475 := bstep (se 1 (by rfl) ⟨20207606, by rfl⟩ : syracuseStep 26943475 = 40415213) B40415213
theorem B19464745 : Blo 1476558 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B4735903 : Blo 1476558 4735903 := bstep (se 1 (by rfl) ⟨3551927, by rfl⟩ : syracuseStep 4735903 = 7103855) B7103855
theorem B9471113 : Blo 1476558 9471113 := bstep (se 2 (by rfl) ⟨3551667, by rfl⟩ : syracuseStep 9471113 = 7103335) B7103335
theorem B15975755 : Blo 1476558 15975755 := bstep (se 1 (by rfl) ⟨11981816, by rfl⟩ : syracuseStep 15975755 = 23963633) B23963633
theorem B103761319 : Blo 1476558 103761319 := bstep (se 1 (by rfl) ⟨77820989, by rfl⟩ : syracuseStep 103761319 = 155641979) B155641979
theorem B6309359 : Blo 1476558 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B3156175 : Blo 1476558 3156175 := bstep (se 1 (by rfl) ⟨2367131, by rfl⟩ : syracuseStep 3156175 = 4734263) B4734263
theorem B1477095 : Blo 1476558 1477095 := bstep (se 1 (by rfl) ⟨1107821, by rfl⟩ : syracuseStep 1477095 = 2215643) B2215643
theorem B1477119 : Blo 1476558 1477119 := bstep (se 1 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 1477119 = 2215679) B2215679
theorem B17984111 : Blo 1476558 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B35924633 : Blo 1476558 35924633 := bstep (se 2 (by rfl) ⟨13471737, by rfl⟩ : syracuseStep 35924633 = 26943475) B26943475
theorem B4983551 : Blo 1476558 4983551 := bstep (se 1 (by rfl) ⟨3737663, by rfl⟩ : syracuseStep 4983551 = 7475327) B7475327
theorem B2493247 : Blo 1476558 2493247 := bstep (se 1 (by rfl) ⟨1869935, by rfl⟩ : syracuseStep 2493247 = 3739871) B3739871
theorem B1477503 : Blo 1476558 1477503 := bstep (se 1 (by rfl) ⟨1108127, by rfl⟩ : syracuseStep 1477503 = 2216255) B2216255
theorem B1477759 : Blo 1476558 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B2215151 : Blo 1476558 2215151 := bstep (se 1 (by rfl) ⟨1661363, by rfl⟩ : syracuseStep 2215151 = 3322727) B3322727
theorem B1477871 : Blo 1476558 1477871 := bstep (se 1 (by rfl) ⟨1108403, by rfl⟩ : syracuseStep 1477871 = 2216807) B2216807
theorem B2215391 : Blo 1476558 2215391 := bstep (se 1 (by rfl) ⟨1661543, by rfl⟩ : syracuseStep 2215391 = 3323087) B3323087
theorem B3550823 : Blo 1476558 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B1478271 : Blo 1476558 1478271 := bstep (se 1 (by rfl) ⟨1108703, by rfl⟩ : syracuseStep 1478271 = 2217407) B2217407
theorem B3993247 : Blo 1476558 3993247 := bstep (se 1 (by rfl) ⟨2994935, by rfl⟩ : syracuseStep 3993247 = 5989871) B5989871
theorem B7990991 : Blo 1476558 7990991 := bstep (se 1 (by rfl) ⟨5993243, by rfl⟩ : syracuseStep 7990991 = 11986487) B11986487
theorem B3739355 : Blo 1476558 3739355 := bstep (se 1 (by rfl) ⟨2804516, by rfl⟩ : syracuseStep 3739355 = 5609033) B5609033
theorem B1478375 : Blo 1476558 1478375 := bstep (se 1 (by rfl) ⟨1108781, by rfl⟩ : syracuseStep 1478375 = 2217563) B2217563
theorem B25259849 : Blo 1476558 25259849 := bstep (se 2 (by rfl) ⟨9472443, by rfl⟩ : syracuseStep 25259849 = 18944887) B18944887
theorem B1478491 : Blo 1476558 1478491 := bstep (se 1 (by rfl) ⟨1108868, by rfl⟩ : syracuseStep 1478491 = 2217737) B2217737
theorem B27332819 : Blo 1476558 27332819 := bstep (se 1 (by rfl) ⟨20499614, by rfl⟩ : syracuseStep 27332819 = 40999229) B40999229
theorem B6312161 : Blo 1476558 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B11219309 : Blo 1476558 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B2216495 : Blo 1476558 2216495 := bstep (se 1 (by rfl) ⟨1662371, by rfl⟩ : syracuseStep 2216495 = 3324743) B3324743
theorem B5608061 : Blo 1476558 5608061 := bstep (se 3 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 5608061 = 2103023) B2103023
theorem B3322511 : Blo 1476558 3322511 := bstep (se 1 (by rfl) ⟨2491883, by rfl⟩ : syracuseStep 3322511 = 4983767) B4983767
theorem B4731635 : Blo 1476558 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B3322745 : Blo 1476558 3322745 := bstep (se 2 (by rfl) ⟨1246029, by rfl⟩ : syracuseStep 3322745 = 2492059) B2492059
theorem B21304235 : Blo 1476558 21304235 := bstep (se 1 (by rfl) ⟨15978176, by rfl⟩ : syracuseStep 21304235 = 31956353) B31956353
theorem B2217191 : Blo 1476558 2217191 := bstep (se 1 (by rfl) ⟨1662893, by rfl⟩ : syracuseStep 2217191 = 3325787) B3325787
theorem B3740975 : Blo 1476558 3740975 := bstep (se 1 (by rfl) ⟨2805731, by rfl⟩ : syracuseStep 3740975 = 5611463) B5611463
theorem B2217383 : Blo 1476558 2217383 := bstep (se 1 (by rfl) ⟨1663037, by rfl⟩ : syracuseStep 2217383 = 3326075) B3326075
theorem B12621419 : Blo 1476558 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B829699807 : Blo 1476558 829699807 := bstep (se 1 (by rfl) ⟨622274855, by rfl⟩ : syracuseStep 829699807 = 1244549711) B1244549711
theorem B3323807 : Blo 1476558 3323807 := bstep (se 1 (by rfl) ⟨2492855, by rfl⟩ : syracuseStep 3323807 = 4985711) B4985711
theorem B7477595 : Blo 1476558 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B1497647 : Blo 1476558 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B3325103 : Blo 1476558 3325103 := bstep (se 1 (by rfl) ⟨2493827, by rfl⟩ : syracuseStep 3325103 = 4987655) B4987655
theorem B2104555 : Blo 1476558 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B5610779 : Blo 1476558 5610779 := bstep (se 1 (by rfl) ⟨4208084, by rfl⟩ : syracuseStep 5610779 = 8416169) B8416169
theorem B1662367 : Blo 1476558 1662367 := bstep (se 1 (by rfl) ⟨1246775, by rfl⟩ : syracuseStep 1662367 = 2493551) B2493551
theorem B1662619 : Blo 1476558 1662619 := bstep (se 1 (by rfl) ⟨1246964, by rfl⟩ : syracuseStep 1662619 = 2493929) B2493929
theorem B3153647 : Blo 1476558 3153647 := bstep (se 1 (by rfl) ⟨2365235, by rfl⟩ : syracuseStep 3153647 = 4730471) B4730471
theorem B7479539 : Blo 1476558 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B25952993 : Blo 1476558 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B10650503 : Blo 1476558 10650503 := bstep (se 1 (by rfl) ⟨7987877, by rfl⟩ : syracuseStep 10650503 = 15975755) B15975755
theorem B8414279 : Blo 1476558 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B47957629 : Blo 1476558 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B138348425 : Blo 1476558 138348425 := bstep (se 2 (by rfl) ⟨51880659, by rfl⟩ : syracuseStep 138348425 = 103761319) B103761319
theorem B12617693 : Blo 1476558 12617693 := bstep (se 3 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 12617693 = 4731635) B4731635
theorem B1476767 : Blo 1476558 1476767 := bstep (se 1 (by rfl) ⟨1107575, by rfl⟩ : syracuseStep 1476767 = 2215151) B2215151
theorem B1106266409 : Blo 1476558 1106266409 := bstep (se 2 (by rfl) ⟨414849903, by rfl⟩ : syracuseStep 1106266409 = 829699807) B829699807
theorem B1476927 : Blo 1476558 1476927 := bstep (se 1 (by rfl) ⟨1107695, by rfl⟩ : syracuseStep 1476927 = 2215391) B2215391
theorem B5327327 : Blo 1476558 5327327 := bstep (se 1 (by rfl) ⟨3995495, by rfl⟩ : syracuseStep 5327327 = 7990991) B7990991
theorem B2492903 : Blo 1476558 2492903 := bstep (se 1 (by rfl) ⟨1869677, by rfl⟩ : syracuseStep 2492903 = 3739355) B3739355
theorem B18221879 : Blo 1476558 18221879 := bstep (se 1 (by rfl) ⟨13666409, by rfl⟩ : syracuseStep 18221879 = 27332819) B27332819
theorem B1477663 : Blo 1476558 1477663 := bstep (se 1 (by rfl) ⟨1108247, by rfl⟩ : syracuseStep 1477663 = 2216495) B2216495
theorem B3738707 : Blo 1476558 3738707 := bstep (se 1 (by rfl) ⟨2804030, by rfl⟩ : syracuseStep 3738707 = 5608061) B5608061
theorem B2215007 : Blo 1476558 2215007 := bstep (se 1 (by rfl) ⟨1661255, by rfl⟩ : syracuseStep 2215007 = 3322511) B3322511
theorem B2215163 : Blo 1476558 2215163 := bstep (se 1 (by rfl) ⟨1661372, by rfl⟩ : syracuseStep 2215163 = 3322745) B3322745
theorem B1478127 : Blo 1476558 1478127 := bstep (se 1 (by rfl) ⟨1108595, by rfl⟩ : syracuseStep 1478127 = 2217191) B2217191
theorem B2493983 : Blo 1476558 2493983 := bstep (se 1 (by rfl) ⟨1870487, by rfl⟩ : syracuseStep 2493983 = 3740975) B3740975
theorem B1478255 : Blo 1476558 1478255 := bstep (se 1 (by rfl) ⟨1108691, by rfl⟩ : syracuseStep 1478255 = 2217383) B2217383
theorem B4206239 : Blo 1476558 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B2215871 : Blo 1476558 2215871 := bstep (se 1 (by rfl) ⟨1661903, by rfl⟩ : syracuseStep 2215871 = 3323807) B3323807
theorem B3993725 : Blo 1476558 3993725 := bstep (se 3 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 3993725 = 1497647) B1497647
theorem B4985063 : Blo 1476558 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B2806073 : Blo 1476558 2806073 := bstep (se 2 (by rfl) ⟨1052277, by rfl⟩ : syracuseStep 2806073 = 2104555) B2104555
theorem B23949755 : Blo 1476558 23949755 := bstep (se 1 (by rfl) ⟨17962316, by rfl⟩ : syracuseStep 23949755 = 35924633) B35924633
theorem B3322367 : Blo 1476558 3322367 := bstep (se 1 (by rfl) ⟨2491775, by rfl⟩ : syracuseStep 3322367 = 4983551) B4983551
theorem B2216489 : Blo 1476558 2216489 := bstep (se 2 (by rfl) ⟨831183, by rfl⟩ : syracuseStep 2216489 = 1662367) B1662367
theorem B2216735 : Blo 1476558 2216735 := bstep (se 1 (by rfl) ⟨1662551, by rfl⟩ : syracuseStep 2216735 = 3325103) B3325103
theorem B3740519 : Blo 1476558 3740519 := bstep (se 1 (by rfl) ⟨2805389, by rfl⟩ : syracuseStep 3740519 = 5610779) B5610779
theorem B2216825 : Blo 1476558 2216825 := bstep (se 2 (by rfl) ⟨831309, by rfl⟩ : syracuseStep 2216825 = 1662619) B1662619
theorem B2102431 : Blo 1476558 2102431 := bstep (se 1 (by rfl) ⟨1576823, by rfl⟩ : syracuseStep 2102431 = 3153647) B3153647
theorem B16839899 : Blo 1476558 16839899 := bstep (se 1 (by rfl) ⟨12629924, by rfl⟩ : syracuseStep 16839899 = 25259849) B25259849
theorem B4208107 : Blo 1476558 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B4208233 : Blo 1476558 4208233 := bstep (se 2 (by rfl) ⟨1578087, by rfl⟩ : syracuseStep 4208233 = 3156175) B3156175
theorem B14202823 : Blo 1476558 14202823 := bstep (se 1 (by rfl) ⟨10652117, by rfl⟩ : syracuseStep 14202823 = 21304235) B21304235
theorem B6314075 : Blo 1476558 6314075 := bstep (se 1 (by rfl) ⟨4735556, by rfl⟩ : syracuseStep 6314075 = 9471113) B9471113
theorem B3324329 : Blo 1476558 3324329 := bstep (se 2 (by rfl) ⟨1246623, by rfl⟩ : syracuseStep 3324329 = 2493247) B2493247
theorem B6314537 : Blo 1476558 6314537 := bstep (se 2 (by rfl) ⟨2367951, by rfl⟩ : syracuseStep 6314537 = 4735903) B4735903
theorem B5324329 : Blo 1476558 5324329 := bstep (se 2 (by rfl) ⟨1996623, by rfl⟩ : syracuseStep 5324329 = 3993247) B3993247
theorem B2367215 : Blo 1476558 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B2662483 : Blo 1476558 2662483 := bstep (se 1 (by rfl) ⟨1996862, by rfl⟩ : syracuseStep 2662483 = 3993725) B3993725
theorem B15966503 : Blo 1476558 15966503 := bstep (se 1 (by rfl) ⟨11974877, by rfl⟩ : syracuseStep 15966503 = 23949755) B23949755
theorem B17301995 : Blo 1476558 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B14206205 : Blo 1476558 14206205 := bstep (se 3 (by rfl) ⟨2663663, by rfl⟩ : syracuseStep 14206205 = 5327327) B5327327
theorem B737510939 : Blo 1476558 737510939 := bstep (se 1 (by rfl) ⟨553133204, by rfl⟩ : syracuseStep 737510939 = 1106266409) B1106266409
theorem B2803241 : Blo 1476558 2803241 := bstep (se 2 (by rfl) ⟨1051215, by rfl⟩ : syracuseStep 2803241 = 2102431) B2102431
theorem B2492471 : Blo 1476558 2492471 := bstep (se 1 (by rfl) ⟨1869353, by rfl⟩ : syracuseStep 2492471 = 3738707) B3738707
theorem B1476671 : Blo 1476558 1476671 := bstep (se 1 (by rfl) ⟨1107503, by rfl⟩ : syracuseStep 1476671 = 2215007) B2215007
theorem B1476775 : Blo 1476558 1476775 := bstep (se 1 (by rfl) ⟨1107581, by rfl⟩ : syracuseStep 1476775 = 2215163) B2215163
theorem B2804159 : Blo 1476558 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B1477247 : Blo 1476558 1477247 := bstep (se 1 (by rfl) ⟨1107935, by rfl⟩ : syracuseStep 1477247 = 2215871) B2215871
theorem B1870715 : Blo 1476558 1870715 := bstep (se 1 (by rfl) ⟨1403036, by rfl⟩ : syracuseStep 1870715 = 2806073) B2806073
theorem B2214911 : Blo 1476558 2214911 := bstep (se 1 (by rfl) ⟨1661183, by rfl⟩ : syracuseStep 2214911 = 3322367) B3322367
theorem B1477659 : Blo 1476558 1477659 := bstep (se 1 (by rfl) ⟨1108244, by rfl⟩ : syracuseStep 1477659 = 2216489) B2216489
theorem B1477823 : Blo 1476558 1477823 := bstep (se 1 (by rfl) ⟨1108367, by rfl⟩ : syracuseStep 1477823 = 2216735) B2216735
theorem B2493679 : Blo 1476558 2493679 := bstep (se 1 (by rfl) ⟨1870259, by rfl⟩ : syracuseStep 2493679 = 3740519) B3740519
theorem B1477883 : Blo 1476558 1477883 := bstep (se 1 (by rfl) ⟨1108412, by rfl⟩ : syracuseStep 1477883 = 2216825) B2216825
theorem B11226599 : Blo 1476558 11226599 := bstep (se 1 (by rfl) ⟨8419949, by rfl⟩ : syracuseStep 11226599 = 16839899) B16839899
theorem B2216219 : Blo 1476558 2216219 := bstep (se 1 (by rfl) ⟨1662164, by rfl⟩ : syracuseStep 2216219 = 3324329) B3324329
theorem B7099105 : Blo 1476558 7099105 := bstep (se 2 (by rfl) ⟨2662164, by rfl⟩ : syracuseStep 7099105 = 5324329) B5324329
theorem B48591677 : Blo 1476558 48591677 := bstep (se 3 (by rfl) ⟨9110939, by rfl⟩ : syracuseStep 48591677 = 18221879) B18221879
theorem B63943505 : Blo 1476558 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B1578143 : Blo 1476558 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B18937097 : Blo 1476558 18937097 := bstep (se 2 (by rfl) ⟨7101411, by rfl⟩ : syracuseStep 18937097 = 14202823) B14202823
theorem B3323375 : Blo 1476558 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B4986359 : Blo 1476558 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B7100335 : Blo 1476558 7100335 := bstep (se 1 (by rfl) ⟨5325251, by rfl⟩ : syracuseStep 7100335 = 10650503) B10650503
theorem B5609519 : Blo 1476558 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B92232283 : Blo 1476558 92232283 := bstep (se 1 (by rfl) ⟨69174212, by rfl⟩ : syracuseStep 92232283 = 138348425) B138348425
theorem B8411795 : Blo 1476558 8411795 := bstep (se 1 (by rfl) ⟨6308846, by rfl⟩ : syracuseStep 8411795 = 12617693) B12617693
theorem B4209383 : Blo 1476558 4209383 := bstep (se 1 (by rfl) ⟨3157037, by rfl⟩ : syracuseStep 4209383 = 6314075) B6314075
theorem B1661935 : Blo 1476558 1661935 := bstep (se 1 (by rfl) ⟨1246451, by rfl⟩ : syracuseStep 1661935 = 2492903) B2492903
theorem B4209691 : Blo 1476558 4209691 := bstep (se 1 (by rfl) ⟨3157268, by rfl⟩ : syracuseStep 4209691 = 6314537) B6314537
theorem B5610809 : Blo 1476558 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B5610977 : Blo 1476558 5610977 := bstep (se 2 (by rfl) ⟨2104116, by rfl⟩ : syracuseStep 5610977 = 4208233) B4208233
theorem B1662655 : Blo 1476558 1662655 := bstep (se 1 (by rfl) ⟨1246991, by rfl⟩ : syracuseStep 1662655 = 2493983) B2493983
theorem B11534663 : Blo 1476558 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B12624731 : Blo 1476558 12624731 := bstep (se 1 (by rfl) ⟨9468548, by rfl⟩ : syracuseStep 12624731 = 18937097) B18937097
theorem B1868827 : Blo 1476558 1868827 := bstep (se 1 (by rfl) ⟨1401620, by rfl⟩ : syracuseStep 1868827 = 2803241) B2803241
theorem B5612921 : Blo 1476558 5612921 := bstep (se 2 (by rfl) ⟨2104845, by rfl⟩ : syracuseStep 5612921 = 4209691) B4209691
theorem B1476607 : Blo 1476558 1476607 := bstep (se 1 (by rfl) ⟨1107455, by rfl⟩ : syracuseStep 1476607 = 2214911) B2214911
theorem B3549977 : Blo 1476558 3549977 := bstep (se 2 (by rfl) ⟨1331241, by rfl⟩ : syracuseStep 3549977 = 2662483) B2662483
theorem B1477479 : Blo 1476558 1477479 := bstep (se 1 (by rfl) ⟨1108109, by rfl⟩ : syracuseStep 1477479 = 2216219) B2216219
theorem B10644335 : Blo 1476558 10644335 := bstep (se 1 (by rfl) ⟨7983251, by rfl⟩ : syracuseStep 10644335 = 15966503) B15966503
theorem B37883213 : Blo 1476558 37883213 := bstep (se 3 (by rfl) ⟨7103102, by rfl⟩ : syracuseStep 37883213 = 14206205) B14206205
theorem B9465473 : Blo 1476558 9465473 := bstep (se 2 (by rfl) ⟨3549552, by rfl⟩ : syracuseStep 9465473 = 7099105) B7099105
theorem B2215583 : Blo 1476558 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B2215913 : Blo 1476558 2215913 := bstep (se 2 (by rfl) ⟨830967, by rfl⟩ : syracuseStep 2215913 = 1661935) B1661935
theorem B3739679 : Blo 1476558 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B5607863 : Blo 1476558 5607863 := bstep (se 1 (by rfl) ⟨4205897, by rfl⟩ : syracuseStep 5607863 = 8411795) B8411795
theorem B2806255 : Blo 1476558 2806255 := bstep (se 1 (by rfl) ⟨2104691, by rfl⟩ : syracuseStep 2806255 = 4209383) B4209383
theorem B129577805 : Blo 1476558 129577805 := bstep (se 3 (by rfl) ⟨24295838, by rfl⟩ : syracuseStep 129577805 = 48591677) B48591677
theorem B3740539 : Blo 1476558 3740539 := bstep (se 1 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 3740539 = 5610809) B5610809
theorem B2216873 : Blo 1476558 2216873 := bstep (se 2 (by rfl) ⟨831327, by rfl⟩ : syracuseStep 2216873 = 1662655) B1662655
theorem B3740651 : Blo 1476558 3740651 := bstep (se 1 (by rfl) ⟨2805488, by rfl⟩ : syracuseStep 3740651 = 5610977) B5610977
theorem B7484399 : Blo 1476558 7484399 := bstep (se 1 (by rfl) ⟨5613299, by rfl⟩ : syracuseStep 7484399 = 11226599) B11226599
theorem B9467113 : Blo 1476558 9467113 := bstep (se 2 (by rfl) ⟨3550167, by rfl⟩ : syracuseStep 9467113 = 7100335) B7100335
theorem B4208381 : Blo 1476558 4208381 := bstep (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) B1578143
theorem B42629003 : Blo 1476558 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B122976377 : Blo 1476558 122976377 := bstep (se 2 (by rfl) ⟨46116141, by rfl⟩ : syracuseStep 122976377 = 92232283) B92232283
theorem B3324239 : Blo 1476558 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B491673959 : Blo 1476558 491673959 := bstep (se 1 (by rfl) ⟨368755469, by rfl⟩ : syracuseStep 491673959 = 737510939) B737510939
theorem B7477757 : Blo 1476558 7477757 := bstep (se 3 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 7477757 = 2804159) B2804159
theorem B1661647 : Blo 1476558 1661647 := bstep (se 1 (by rfl) ⟨1246235, by rfl⟩ : syracuseStep 1661647 = 2492471) B2492471
theorem B3324905 : Blo 1476558 3324905 := bstep (se 2 (by rfl) ⟨1246839, by rfl⟩ : syracuseStep 3324905 = 2493679) B2493679
theorem B4988573 : Blo 1476558 4988573 := bstep (se 3 (by rfl) ⟨935357, by rfl⟩ : syracuseStep 4988573 = 1870715) B1870715
theorem B86385203 : Blo 1476558 86385203 := bstep (se 1 (by rfl) ⟨64788902, by rfl⟩ : syracuseStep 86385203 = 129577805) B129577805
theorem B4989599 : Blo 1476558 4989599 := bstep (se 1 (by rfl) ⟨3742199, by rfl⟩ : syracuseStep 4989599 = 7484399) B7484399
theorem B28419335 : Blo 1476558 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B2491769 : Blo 1476558 2491769 := bstep (se 2 (by rfl) ⟨934413, by rfl⟩ : syracuseStep 2491769 = 1868827) B1868827
theorem B7096223 : Blo 1476558 7096223 := bstep (se 1 (by rfl) ⟨5322167, by rfl⟩ : syracuseStep 7096223 = 10644335) B10644335
theorem B6310315 : Blo 1476558 6310315 := bstep (se 1 (by rfl) ⟨4732736, by rfl⟩ : syracuseStep 6310315 = 9465473) B9465473
theorem B1477055 : Blo 1476558 1477055 := bstep (se 1 (by rfl) ⟨1107791, by rfl⟩ : syracuseStep 1477055 = 2215583) B2215583
theorem B1477275 : Blo 1476558 1477275 := bstep (se 1 (by rfl) ⟨1107956, by rfl⟩ : syracuseStep 1477275 = 2215913) B2215913
theorem B2493119 : Blo 1476558 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B3738575 : Blo 1476558 3738575 := bstep (se 1 (by rfl) ⟨2803931, by rfl⟩ : syracuseStep 3738575 = 5607863) B5607863
theorem B8416487 : Blo 1476558 8416487 := bstep (se 1 (by rfl) ⟨6312365, by rfl⟩ : syracuseStep 8416487 = 12624731) B12624731
theorem B1477915 : Blo 1476558 1477915 := bstep (se 1 (by rfl) ⟨1108436, by rfl⟩ : syracuseStep 1477915 = 2216873) B2216873
theorem B2493767 : Blo 1476558 2493767 := bstep (se 1 (by rfl) ⟨1870325, by rfl⟩ : syracuseStep 2493767 = 3740651) B3740651
theorem B2215529 : Blo 1476558 2215529 := bstep (se 2 (by rfl) ⟨830823, by rfl⟩ : syracuseStep 2215529 = 1661647) B1661647
theorem B2805587 : Blo 1476558 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B2216159 : Blo 1476558 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B327782639 : Blo 1476558 327782639 := bstep (se 1 (by rfl) ⟨245836979, by rfl⟩ : syracuseStep 327782639 = 491673959) B491673959
theorem B4985171 : Blo 1476558 4985171 := bstep (se 1 (by rfl) ⟨3738878, by rfl⟩ : syracuseStep 4985171 = 7477757) B7477757
theorem B2216603 : Blo 1476558 2216603 := bstep (se 1 (by rfl) ⟨1662452, by rfl⟩ : syracuseStep 2216603 = 3324905) B3324905
theorem B7689775 : Blo 1476558 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B3741673 : Blo 1476558 3741673 := bstep (se 2 (by rfl) ⟨1403127, by rfl⟩ : syracuseStep 3741673 = 2806255) B2806255
theorem B3741947 : Blo 1476558 3741947 := bstep (se 1 (by rfl) ⟨2806460, by rfl⟩ : syracuseStep 3741947 = 5612921) B5612921
theorem B4987385 : Blo 1476558 4987385 := bstep (se 2 (by rfl) ⟨1870269, by rfl⟩ : syracuseStep 4987385 = 3740539) B3740539
theorem B81984251 : Blo 1476558 81984251 := bstep (se 1 (by rfl) ⟨61488188, by rfl⟩ : syracuseStep 81984251 = 122976377) B122976377
theorem B12622817 : Blo 1476558 12622817 := bstep (se 2 (by rfl) ⟨4733556, by rfl⟩ : syracuseStep 12622817 = 9467113) B9467113
theorem B2366651 : Blo 1476558 2366651 := bstep (se 1 (by rfl) ⟨1774988, by rfl⟩ : syracuseStep 2366651 = 3549977) B3549977
theorem B25255475 : Blo 1476558 25255475 := bstep (se 1 (by rfl) ⟨18941606, by rfl⟩ : syracuseStep 25255475 = 37883213) B37883213
theorem B3325715 : Blo 1476558 3325715 := bstep (se 1 (by rfl) ⟨2494286, by rfl⟩ : syracuseStep 3325715 = 4988573) B4988573
theorem B218521759 : Blo 1476558 218521759 := bstep (se 1 (by rfl) ⟨163891319, by rfl⟩ : syracuseStep 218521759 = 327782639) B327782639
theorem B57590135 : Blo 1476558 57590135 := bstep (se 1 (by rfl) ⟨43192601, by rfl⟩ : syracuseStep 57590135 = 86385203) B86385203
theorem B3326399 : Blo 1476558 3326399 := bstep (se 1 (by rfl) ⟨2494799, by rfl⟩ : syracuseStep 3326399 = 4989599) B4989599
theorem B8413753 : Blo 1476558 8413753 := bstep (se 2 (by rfl) ⟨3155157, by rfl⟩ : syracuseStep 8413753 = 6310315) B6310315
theorem B2492383 : Blo 1476558 2492383 := bstep (se 1 (by rfl) ⟨1869287, by rfl⟩ : syracuseStep 2492383 = 3738575) B3738575
theorem B8415211 : Blo 1476558 8415211 := bstep (se 1 (by rfl) ⟨6311408, by rfl⟩ : syracuseStep 8415211 = 12622817) B12622817
theorem B16836983 : Blo 1476558 16836983 := bstep (se 1 (by rfl) ⟨12627737, by rfl⟩ : syracuseStep 16836983 = 25255475) B25255475
theorem B1477019 : Blo 1476558 1477019 := bstep (se 1 (by rfl) ⟨1107764, by rfl⟩ : syracuseStep 1477019 = 2215529) B2215529
theorem B1870391 : Blo 1476558 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B1477439 : Blo 1476558 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B1477735 : Blo 1476558 1477735 := bstep (se 1 (by rfl) ⟨1108301, by rfl⟩ : syracuseStep 1477735 = 2216603) B2216603
theorem B4730815 : Blo 1476558 4730815 := bstep (se 1 (by rfl) ⟨3548111, by rfl⟩ : syracuseStep 4730815 = 7096223) B7096223
theorem B2494631 : Blo 1476558 2494631 := bstep (se 1 (by rfl) ⟨1870973, by rfl⟩ : syracuseStep 2494631 = 3741947) B3741947
theorem B10253033 : Blo 1476558 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1577767 : Blo 1476558 1577767 := bstep (se 1 (by rfl) ⟨1183325, by rfl⟩ : syracuseStep 1577767 = 2366651) B2366651
theorem B2217143 : Blo 1476558 2217143 := bstep (se 1 (by rfl) ⟨1662857, by rfl⟩ : syracuseStep 2217143 = 3325715) B3325715
theorem B3323447 : Blo 1476558 3323447 := bstep (se 1 (by rfl) ⟨2492585, by rfl⟩ : syracuseStep 3323447 = 4985171) B4985171
theorem B18946223 : Blo 1476558 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B1661179 : Blo 1476558 1661179 := bstep (se 1 (by rfl) ⟨1245884, by rfl⟩ : syracuseStep 1661179 = 2491769) B2491769
theorem B3324923 : Blo 1476558 3324923 := bstep (se 1 (by rfl) ⟨2493692, by rfl⟩ : syracuseStep 3324923 = 4987385) B4987385
theorem B1662079 : Blo 1476558 1662079 := bstep (se 1 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 1662079 = 2493119) B2493119
theorem B54656167 : Blo 1476558 54656167 := bstep (se 1 (by rfl) ⟨40992125, by rfl⟩ : syracuseStep 54656167 = 81984251) B81984251
theorem B5610991 : Blo 1476558 5610991 := bstep (se 1 (by rfl) ⟨4208243, by rfl⟩ : syracuseStep 5610991 = 8416487) B8416487
theorem B1662511 : Blo 1476558 1662511 := bstep (se 1 (by rfl) ⟨1246883, by rfl⟩ : syracuseStep 1662511 = 2493767) B2493767
theorem B4988897 : Blo 1476558 4988897 := bstep (se 2 (by rfl) ⟨1870836, by rfl⟩ : syracuseStep 4988897 = 3741673) B3741673
theorem B1663087 : Blo 1476558 1663087 := bstep (se 1 (by rfl) ⟨1247315, by rfl⟩ : syracuseStep 1663087 = 2494631) B2494631
theorem B11224655 : Blo 1476558 11224655 := bstep (se 1 (by rfl) ⟨8418491, by rfl⟩ : syracuseStep 11224655 = 16836983) B16836983
theorem B7481321 : Blo 1476558 7481321 := bstep (se 2 (by rfl) ⟨2805495, by rfl⟩ : syracuseStep 7481321 = 5610991) B5610991
theorem B2214905 : Blo 1476558 2214905 := bstep (se 2 (by rfl) ⟨830589, by rfl⟩ : syracuseStep 2214905 = 1661179) B1661179
theorem B6835355 : Blo 1476558 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B11218337 : Blo 1476558 11218337 := bstep (se 2 (by rfl) ⟨4206876, by rfl⟩ : syracuseStep 11218337 = 8413753) B8413753
theorem B1478095 : Blo 1476558 1478095 := bstep (se 1 (by rfl) ⟨1108571, by rfl⟩ : syracuseStep 1478095 = 2217143) B2217143
theorem B2215631 : Blo 1476558 2215631 := bstep (se 1 (by rfl) ⟨1661723, by rfl⟩ : syracuseStep 2215631 = 3323447) B3323447
theorem B2216105 : Blo 1476558 2216105 := bstep (se 2 (by rfl) ⟨831039, by rfl⟩ : syracuseStep 2216105 = 1662079) B1662079
theorem B2216615 : Blo 1476558 2216615 := bstep (se 1 (by rfl) ⟨1662461, by rfl⟩ : syracuseStep 2216615 = 3324923) B3324923
theorem B2216681 : Blo 1476558 2216681 := bstep (se 2 (by rfl) ⟨831255, by rfl⟩ : syracuseStep 2216681 = 1662511) B1662511
theorem B3323177 : Blo 1476558 3323177 := bstep (se 2 (by rfl) ⟨1246191, by rfl⟩ : syracuseStep 3323177 = 2492383) B2492383
theorem B11220281 : Blo 1476558 11220281 := bstep (se 2 (by rfl) ⟨4207605, by rfl⟩ : syracuseStep 11220281 = 8415211) B8415211
theorem B291362345 : Blo 1476558 291362345 := bstep (se 2 (by rfl) ⟨109260879, by rfl⟩ : syracuseStep 291362345 = 218521759) B218521759
theorem B38393423 : Blo 1476558 38393423 := bstep (se 1 (by rfl) ⟨28795067, by rfl⟩ : syracuseStep 38393423 = 57590135) B57590135
theorem B2217599 : Blo 1476558 2217599 := bstep (se 1 (by rfl) ⟨1663199, by rfl⟩ : syracuseStep 2217599 = 3326399) B3326399
theorem B2103689 : Blo 1476558 2103689 := bstep (se 2 (by rfl) ⟨788883, by rfl⟩ : syracuseStep 2103689 = 1577767) B1577767
theorem B12630815 : Blo 1476558 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B4987709 : Blo 1476558 4987709 := bstep (se 3 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 4987709 = 1870391) B1870391
theorem B72874889 : Blo 1476558 72874889 := bstep (se 2 (by rfl) ⟨27328083, by rfl⟩ : syracuseStep 72874889 = 54656167) B54656167
theorem B6307753 : Blo 1476558 6307753 := bstep (se 2 (by rfl) ⟨2365407, by rfl⟩ : syracuseStep 6307753 = 4730815) B4730815
theorem B3325931 : Blo 1476558 3325931 := bstep (se 1 (by rfl) ⟨2494448, by rfl⟩ : syracuseStep 3325931 = 4988897) B4988897
theorem B7480187 : Blo 1476558 7480187 := bstep (se 1 (by rfl) ⟨5610140, by rfl⟩ : syracuseStep 7480187 = 11220281) B11220281
theorem B194241563 : Blo 1476558 194241563 := bstep (se 1 (by rfl) ⟨145681172, by rfl⟩ : syracuseStep 194241563 = 291362345) B291362345
theorem B1476603 : Blo 1476558 1476603 := bstep (se 1 (by rfl) ⟨1107452, by rfl⟩ : syracuseStep 1476603 = 2214905) B2214905
theorem B4556903 : Blo 1476558 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B1477087 : Blo 1476558 1477087 := bstep (se 1 (by rfl) ⟨1107815, by rfl⟩ : syracuseStep 1477087 = 2215631) B2215631
theorem B1477403 : Blo 1476558 1477403 := bstep (se 1 (by rfl) ⟨1108052, by rfl⟩ : syracuseStep 1477403 = 2216105) B2216105
theorem B1477743 : Blo 1476558 1477743 := bstep (se 1 (by rfl) ⟨1108307, by rfl⟩ : syracuseStep 1477743 = 2216615) B2216615
theorem B1477787 : Blo 1476558 1477787 := bstep (se 1 (by rfl) ⟨1108340, by rfl⟩ : syracuseStep 1477787 = 2216681) B2216681
theorem B2215451 : Blo 1476558 2215451 := bstep (se 1 (by rfl) ⟨1661588, by rfl⟩ : syracuseStep 2215451 = 3323177) B3323177
theorem B25595615 : Blo 1476558 25595615 := bstep (se 1 (by rfl) ⟨19196711, by rfl⟩ : syracuseStep 25595615 = 38393423) B38393423
theorem B7483103 : Blo 1476558 7483103 := bstep (se 1 (by rfl) ⟨5612327, by rfl⟩ : syracuseStep 7483103 = 11224655) B11224655
theorem B1478399 : Blo 1476558 1478399 := bstep (se 1 (by rfl) ⟨1108799, by rfl⟩ : syracuseStep 1478399 = 2217599) B2217599
theorem B48583259 : Blo 1476558 48583259 := bstep (se 1 (by rfl) ⟨36437444, by rfl⟩ : syracuseStep 48583259 = 72874889) B72874889
theorem B8410337 : Blo 1476558 8410337 := bstep (se 2 (by rfl) ⟨3153876, by rfl⟩ : syracuseStep 8410337 = 6307753) B6307753
theorem B2217287 : Blo 1476558 2217287 := bstep (se 1 (by rfl) ⟨1662965, by rfl⟩ : syracuseStep 2217287 = 3325931) B3325931
theorem B2217449 : Blo 1476558 2217449 := bstep (se 2 (by rfl) ⟨831543, by rfl⟩ : syracuseStep 2217449 = 1663087) B1663087
theorem B5609837 : Blo 1476558 5609837 := bstep (se 3 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 5609837 = 2103689) B2103689
theorem B4987547 : Blo 1476558 4987547 := bstep (se 1 (by rfl) ⟨3740660, by rfl⟩ : syracuseStep 4987547 = 7481321) B7481321
theorem B8420543 : Blo 1476558 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B3325139 : Blo 1476558 3325139 := bstep (se 1 (by rfl) ⟨2493854, by rfl⟩ : syracuseStep 3325139 = 4987709) B4987709
theorem B7478891 : Blo 1476558 7478891 := bstep (se 1 (by rfl) ⟨5609168, by rfl⟩ : syracuseStep 7478891 = 11218337) B11218337
theorem B5613695 : Blo 1476558 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B1476967 : Blo 1476558 1476967 := bstep (se 1 (by rfl) ⟨1107725, by rfl⟩ : syracuseStep 1476967 = 2215451) B2215451
theorem B129494375 : Blo 1476558 129494375 := bstep (se 1 (by rfl) ⟨97120781, by rfl⟩ : syracuseStep 129494375 = 194241563) B194241563
theorem B5606891 : Blo 1476558 5606891 := bstep (se 1 (by rfl) ⟨4205168, by rfl⟩ : syracuseStep 5606891 = 8410337) B8410337
theorem B1478191 : Blo 1476558 1478191 := bstep (se 1 (by rfl) ⟨1108643, by rfl⟩ : syracuseStep 1478191 = 2217287) B2217287
theorem B1478299 : Blo 1476558 1478299 := bstep (se 1 (by rfl) ⟨1108724, by rfl⟩ : syracuseStep 1478299 = 2217449) B2217449
theorem B48606965 : Blo 1476558 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B3739891 : Blo 1476558 3739891 := bstep (se 1 (by rfl) ⟨2804918, by rfl⟩ : syracuseStep 3739891 = 5609837) B5609837
theorem B2216759 : Blo 1476558 2216759 := bstep (se 1 (by rfl) ⟨1662569, by rfl⟩ : syracuseStep 2216759 = 3325139) B3325139
theorem B4985927 : Blo 1476558 4985927 := bstep (se 1 (by rfl) ⟨3739445, by rfl⟩ : syracuseStep 4985927 = 7478891) B7478891
theorem B32388839 : Blo 1476558 32388839 := bstep (se 1 (by rfl) ⟨24291629, by rfl⟩ : syracuseStep 32388839 = 48583259) B48583259
theorem B4986791 : Blo 1476558 4986791 := bstep (se 1 (by rfl) ⟨3740093, by rfl⟩ : syracuseStep 4986791 = 7480187) B7480187
theorem B3325031 : Blo 1476558 3325031 := bstep (se 1 (by rfl) ⟨2493773, by rfl⟩ : syracuseStep 3325031 = 4987547) B4987547
theorem B68254973 : Blo 1476558 68254973 := bstep (se 3 (by rfl) ⟨12797807, by rfl⟩ : syracuseStep 68254973 = 25595615) B25595615
theorem B4988735 : Blo 1476558 4988735 := bstep (se 1 (by rfl) ⟨3741551, by rfl⟩ : syracuseStep 4988735 = 7483103) B7483103
theorem B86329583 : Blo 1476558 86329583 := bstep (se 1 (by rfl) ⟨64747187, by rfl⟩ : syracuseStep 86329583 = 129494375) B129494375
theorem B3737927 : Blo 1476558 3737927 := bstep (se 1 (by rfl) ⟨2803445, by rfl⟩ : syracuseStep 3737927 = 5606891) B5606891
theorem B1477839 : Blo 1476558 1477839 := bstep (se 1 (by rfl) ⟨1108379, by rfl⟩ : syracuseStep 1477839 = 2216759) B2216759
theorem B2216687 : Blo 1476558 2216687 := bstep (se 1 (by rfl) ⟨1662515, by rfl⟩ : syracuseStep 2216687 = 3325031) B3325031
theorem B45503315 : Blo 1476558 45503315 := bstep (se 1 (by rfl) ⟨34127486, by rfl⟩ : syracuseStep 45503315 = 68254973) B68254973
theorem B32404643 : Blo 1476558 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B4986521 : Blo 1476558 4986521 := bstep (se 2 (by rfl) ⟨1869945, by rfl⟩ : syracuseStep 4986521 = 3739891) B3739891
theorem B3323951 : Blo 1476558 3323951 := bstep (se 1 (by rfl) ⟨2492963, by rfl⟩ : syracuseStep 3323951 = 4985927) B4985927
theorem B21592559 : Blo 1476558 21592559 := bstep (se 1 (by rfl) ⟨16194419, by rfl⟩ : syracuseStep 21592559 = 32388839) B32388839
theorem B3324527 : Blo 1476558 3324527 := bstep (se 1 (by rfl) ⟨2493395, by rfl⟩ : syracuseStep 3324527 = 4986791) B4986791
theorem B3742463 : Blo 1476558 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B3325823 : Blo 1476558 3325823 := bstep (se 1 (by rfl) ⟨2494367, by rfl⟩ : syracuseStep 3325823 = 4988735) B4988735
theorem B30335543 : Blo 1476558 30335543 := bstep (se 1 (by rfl) ⟨22751657, by rfl⟩ : syracuseStep 30335543 = 45503315) B45503315
theorem B21603095 : Blo 1476558 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B2491951 : Blo 1476558 2491951 := bstep (se 1 (by rfl) ⟨1868963, by rfl⟩ : syracuseStep 2491951 = 3737927) B3737927
theorem B14395039 : Blo 1476558 14395039 := bstep (se 1 (by rfl) ⟨10796279, by rfl⟩ : syracuseStep 14395039 = 21592559) B21592559
theorem B1477791 : Blo 1476558 1477791 := bstep (se 1 (by rfl) ⟨1108343, by rfl⟩ : syracuseStep 1477791 = 2216687) B2216687
theorem B2215967 : Blo 1476558 2215967 := bstep (se 1 (by rfl) ⟨1661975, by rfl⟩ : syracuseStep 2215967 = 3323951) B3323951
theorem B57553055 : Blo 1476558 57553055 := bstep (se 1 (by rfl) ⟨43164791, by rfl⟩ : syracuseStep 57553055 = 86329583) B86329583
theorem B2216351 : Blo 1476558 2216351 := bstep (se 1 (by rfl) ⟨1662263, by rfl⟩ : syracuseStep 2216351 = 3324527) B3324527
theorem B2494975 : Blo 1476558 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B2217215 : Blo 1476558 2217215 := bstep (se 1 (by rfl) ⟨1662911, by rfl⟩ : syracuseStep 2217215 = 3325823) B3325823
theorem B3324347 : Blo 1476558 3324347 := bstep (se 1 (by rfl) ⟨2493260, by rfl⟩ : syracuseStep 3324347 = 4986521) B4986521
theorem B14402063 : Blo 1476558 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B3326633 : Blo 1476558 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B1477311 : Blo 1476558 1477311 := bstep (se 1 (by rfl) ⟨1107983, by rfl⟩ : syracuseStep 1477311 = 2215967) B2215967
theorem B1477567 : Blo 1476558 1477567 := bstep (se 1 (by rfl) ⟨1108175, by rfl⟩ : syracuseStep 1477567 = 2216351) B2216351
theorem B1478143 : Blo 1476558 1478143 := bstep (se 1 (by rfl) ⟨1108607, by rfl⟩ : syracuseStep 1478143 = 2217215) B2217215
theorem B2216231 : Blo 1476558 2216231 := bstep (se 1 (by rfl) ⟨1662173, by rfl⟩ : syracuseStep 2216231 = 3324347) B3324347
theorem B3322601 : Blo 1476558 3322601 := bstep (se 2 (by rfl) ⟨1245975, by rfl⟩ : syracuseStep 3322601 = 2491951) B2491951
theorem B38368703 : Blo 1476558 38368703 := bstep (se 1 (by rfl) ⟨28776527, by rfl⟩ : syracuseStep 38368703 = 57553055) B57553055
theorem B20223695 : Blo 1476558 20223695 := bstep (se 1 (by rfl) ⟨15167771, by rfl⟩ : syracuseStep 20223695 = 30335543) B30335543
theorem B76773541 : Blo 1476558 76773541 := bstep (se 4 (by rfl) ⟨7197519, by rfl⟩ : syracuseStep 76773541 = 14395039) B14395039
theorem B9601375 : Blo 1476558 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B1477487 : Blo 1476558 1477487 := bstep (se 1 (by rfl) ⟨1108115, by rfl⟩ : syracuseStep 1477487 = 2216231) B2216231
theorem B2215067 : Blo 1476558 2215067 := bstep (se 1 (by rfl) ⟨1661300, by rfl⟩ : syracuseStep 2215067 = 3322601) B3322601
theorem B25579135 : Blo 1476558 25579135 := bstep (se 1 (by rfl) ⟨19184351, by rfl⟩ : syracuseStep 25579135 = 38368703) B38368703
theorem B102364721 : Blo 1476558 102364721 := bstep (se 2 (by rfl) ⟨38386770, by rfl⟩ : syracuseStep 102364721 = 76773541) B76773541
theorem B2217755 : Blo 1476558 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B13482463 : Blo 1476558 13482463 := bstep (se 1 (by rfl) ⟨10111847, by rfl⟩ : syracuseStep 13482463 = 20223695) B20223695
theorem B136422053 : Blo 1476558 136422053 := bstep (se 4 (by rfl) ⟨12789567, by rfl⟩ : syracuseStep 136422053 = 25579135) B25579135
theorem B1476711 : Blo 1476558 1476711 := bstep (se 1 (by rfl) ⟨1107533, by rfl⟩ : syracuseStep 1476711 = 2215067) B2215067
theorem B17976617 : Blo 1476558 17976617 := bstep (se 2 (by rfl) ⟨6741231, by rfl⟩ : syracuseStep 17976617 = 13482463) B13482463
theorem B68243147 : Blo 1476558 68243147 := bstep (se 1 (by rfl) ⟨51182360, by rfl⟩ : syracuseStep 68243147 = 102364721) B102364721
theorem B1478503 : Blo 1476558 1478503 := bstep (se 1 (by rfl) ⟨1108877, by rfl⟩ : syracuseStep 1478503 = 2217755) B2217755
theorem B12801833 : Blo 1476558 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B90948035 : Blo 1476558 90948035 := bstep (se 1 (by rfl) ⟨68211026, by rfl⟩ : syracuseStep 90948035 = 136422053) B136422053
theorem B45495431 : Blo 1476558 45495431 := bstep (se 1 (by rfl) ⟨34121573, by rfl⟩ : syracuseStep 45495431 = 68243147) B68243147
theorem B8534555 : Blo 1476558 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B11984411 : Blo 1476558 11984411 := bstep (se 1 (by rfl) ⟨8988308, by rfl⟩ : syracuseStep 11984411 = 17976617) B17976617
theorem B7989607 : Blo 1476558 7989607 := bstep (se 1 (by rfl) ⟨5992205, by rfl⟩ : syracuseStep 7989607 = 11984411) B11984411
theorem B60632023 : Blo 1476558 60632023 := bstep (se 1 (by rfl) ⟨45474017, by rfl⟩ : syracuseStep 60632023 = 90948035) B90948035
theorem B30330287 : Blo 1476558 30330287 := bstep (se 1 (by rfl) ⟨22747715, by rfl⟩ : syracuseStep 30330287 = 45495431) B45495431
theorem B5689703 : Blo 1476558 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B15172541 : Blo 1476558 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B20220191 : Blo 1476558 20220191 := bstep (se 1 (by rfl) ⟨15165143, by rfl⟩ : syracuseStep 20220191 = 30330287) B30330287
theorem B10652809 : Blo 1476558 10652809 := bstep (se 2 (by rfl) ⟨3994803, by rfl⟩ : syracuseStep 10652809 = 7989607) B7989607
theorem B80842697 : Blo 1476558 80842697 := bstep (se 2 (by rfl) ⟨30316011, by rfl⟩ : syracuseStep 80842697 = 60632023) B60632023
theorem B13480127 : Blo 1476558 13480127 := bstep (se 1 (by rfl) ⟨10110095, by rfl⟩ : syracuseStep 13480127 = 20220191) B20220191
theorem B10115027 : Blo 1476558 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B14203745 : Blo 1476558 14203745 := bstep (se 2 (by rfl) ⟨5326404, by rfl⟩ : syracuseStep 14203745 = 10652809) B10652809
theorem B53895131 : Blo 1476558 53895131 := bstep (se 1 (by rfl) ⟨40421348, by rfl⟩ : syracuseStep 53895131 = 80842697) B80842697
theorem B8986751 : Blo 1476558 8986751 := bstep (se 1 (by rfl) ⟨6740063, by rfl⟩ : syracuseStep 8986751 = 13480127) B13480127
theorem B6743351 : Blo 1476558 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B9469163 : Blo 1476558 9469163 := bstep (se 1 (by rfl) ⟨7101872, by rfl⟩ : syracuseStep 9469163 = 14203745) B14203745
theorem B35930087 : Blo 1476558 35930087 := bstep (se 1 (by rfl) ⟨26947565, by rfl⟩ : syracuseStep 35930087 = 53895131) B53895131
theorem B5991167 : Blo 1476558 5991167 := bstep (se 1 (by rfl) ⟨4493375, by rfl⟩ : syracuseStep 5991167 = 8986751) B8986751
theorem B25251101 : Blo 1476558 25251101 := bstep (se 3 (by rfl) ⟨4734581, by rfl⟩ : syracuseStep 25251101 = 9469163) B9469163
theorem B4495567 : Blo 1476558 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B23953391 : Blo 1476558 23953391 := bstep (se 1 (by rfl) ⟨17965043, by rfl⟩ : syracuseStep 23953391 = 35930087) B35930087
theorem B15976445 : Blo 1476558 15976445 := bstep (se 3 (by rfl) ⟨2995583, by rfl⟩ : syracuseStep 15976445 = 5991167) B5991167
theorem B15968927 : Blo 1476558 15968927 := bstep (se 1 (by rfl) ⟨11976695, by rfl⟩ : syracuseStep 15968927 = 23953391) B23953391
theorem B5994089 : Blo 1476558 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B16834067 : Blo 1476558 16834067 := bstep (se 1 (by rfl) ⟨12625550, by rfl⟩ : syracuseStep 16834067 = 25251101) B25251101
theorem B10645951 : Blo 1476558 10645951 := bstep (se 1 (by rfl) ⟨7984463, by rfl⟩ : syracuseStep 10645951 = 15968927) B15968927
theorem B42603853 : Blo 1476558 42603853 := bstep (se 3 (by rfl) ⟨7988222, by rfl⟩ : syracuseStep 42603853 = 15976445) B15976445
theorem B3996059 : Blo 1476558 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B11222711 : Blo 1476558 11222711 := bstep (se 1 (by rfl) ⟨8417033, by rfl⟩ : syracuseStep 11222711 = 16834067) B16834067
theorem B56805137 : Blo 1476558 56805137 := bstep (se 2 (by rfl) ⟨21301926, by rfl⟩ : syracuseStep 56805137 = 42603853) B42603853
theorem B7481807 : Blo 1476558 7481807 := bstep (se 1 (by rfl) ⟨5611355, by rfl⟩ : syracuseStep 7481807 = 11222711) B11222711
theorem B14194601 : Blo 1476558 14194601 := bstep (se 2 (by rfl) ⟨5322975, by rfl⟩ : syracuseStep 14194601 = 10645951) B10645951
theorem B10656157 : Blo 1476558 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B9463067 : Blo 1476558 9463067 := bstep (se 1 (by rfl) ⟨7097300, by rfl⟩ : syracuseStep 9463067 = 14194601) B14194601
theorem B14208209 : Blo 1476558 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B37870091 : Blo 1476558 37870091 := bstep (se 1 (by rfl) ⟨28402568, by rfl⟩ : syracuseStep 37870091 = 56805137) B56805137
theorem B4987871 : Blo 1476558 4987871 := bstep (se 1 (by rfl) ⟨3740903, by rfl⟩ : syracuseStep 4987871 = 7481807) B7481807
theorem B6308711 : Blo 1476558 6308711 := bstep (se 1 (by rfl) ⟨4731533, by rfl⟩ : syracuseStep 6308711 = 9463067) B9463067
theorem B9472139 : Blo 1476558 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B25246727 : Blo 1476558 25246727 := bstep (se 1 (by rfl) ⟨18935045, by rfl⟩ : syracuseStep 25246727 = 37870091) B37870091
theorem B3325247 : Blo 1476558 3325247 := bstep (se 1 (by rfl) ⟨2493935, by rfl⟩ : syracuseStep 3325247 = 4987871) B4987871
theorem B4205807 : Blo 1476558 4205807 := bstep (se 1 (by rfl) ⟨3154355, by rfl⟩ : syracuseStep 4205807 = 6308711) B6308711
theorem B16831151 : Blo 1476558 16831151 := bstep (se 1 (by rfl) ⟨12623363, by rfl⟩ : syracuseStep 16831151 = 25246727) B25246727
theorem B2216831 : Blo 1476558 2216831 := bstep (se 1 (by rfl) ⟨1662623, by rfl⟩ : syracuseStep 2216831 = 3325247) B3325247
theorem B6314759 : Blo 1476558 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B2803871 : Blo 1476558 2803871 := bstep (se 1 (by rfl) ⟨2102903, by rfl⟩ : syracuseStep 2803871 = 4205807) B4205807
theorem B1477887 : Blo 1476558 1477887 := bstep (se 1 (by rfl) ⟨1108415, by rfl⟩ : syracuseStep 1477887 = 2216831) B2216831
theorem B11220767 : Blo 1476558 11220767 := bstep (se 1 (by rfl) ⟨8415575, by rfl⟩ : syracuseStep 11220767 = 16831151) B16831151
theorem B4209839 : Blo 1476558 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B7480511 : Blo 1476558 7480511 := bstep (se 1 (by rfl) ⟨5610383, by rfl⟩ : syracuseStep 7480511 = 11220767) B11220767
theorem B1869247 : Blo 1476558 1869247 := bstep (se 1 (by rfl) ⟨1401935, by rfl⟩ : syracuseStep 1869247 = 2803871) B2803871
theorem B2806559 : Blo 1476558 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B2492329 : Blo 1476558 2492329 := bstep (se 2 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 2492329 = 1869247) B1869247
theorem B1871039 : Blo 1476558 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B4987007 : Blo 1476558 4987007 := bstep (se 1 (by rfl) ⟨3740255, by rfl⟩ : syracuseStep 4987007 = 7480511) B7480511
theorem B4989437 : Blo 1476558 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B3323105 : Blo 1476558 3323105 := bstep (se 2 (by rfl) ⟨1246164, by rfl⟩ : syracuseStep 3323105 = 2492329) B2492329
theorem B3324671 : Blo 1476558 3324671 := bstep (se 1 (by rfl) ⟨2493503, by rfl⟩ : syracuseStep 3324671 = 4987007) B4987007
theorem B3326291 : Blo 1476558 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B2215403 : Blo 1476558 2215403 := bstep (se 1 (by rfl) ⟨1661552, by rfl⟩ : syracuseStep 2215403 = 3323105) B3323105
theorem B2216447 : Blo 1476558 2216447 := bstep (se 1 (by rfl) ⟨1662335, by rfl⟩ : syracuseStep 2216447 = 3324671) B3324671
theorem B1476935 : Blo 1476558 1476935 := bstep (se 1 (by rfl) ⟨1107701, by rfl⟩ : syracuseStep 1476935 = 2215403) B2215403
theorem B1477631 : Blo 1476558 1477631 := bstep (se 1 (by rfl) ⟨1108223, by rfl⟩ : syracuseStep 1477631 = 2216447) B2216447
theorem B2217527 : Blo 1476558 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B1478351 : Blo 1476558 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527

theorem C0 (j : ℕ) (h1 : 369139 ≤ j) (h2 : j ≤ 369638) : Blo 1476558 (4 * j + 3) := by
  interval_cases j
  · exact B1476559
  · exact B1476563
  · exact B1476567
  · exact B1476571
  · exact B1476575
  · exact B1476579
  · exact B1476583
  · exact B1476587
  · exact B1476591
  · exact B1476595
  · exact B1476599
  · exact B1476603
  · exact B1476607
  · exact B1476611
  · exact B1476615
  · exact B1476619
  · exact B1476623
  · exact B1476627
  · exact B1476631
  · exact B1476635
  · exact B1476639
  · exact B1476643
  · exact B1476647
  · exact B1476651
  · exact B1476655
  · exact B1476659
  · exact B1476663
  · exact B1476667
  · exact B1476671
  · exact B1476675
  · exact B1476679
  · exact B1476683
  · exact B1476687
  · exact B1476691
  · exact B1476695
  · exact B1476699
  · exact B1476703
  · exact B1476707
  · exact B1476711
  · exact B1476715
  · exact B1476719
  · exact B1476723
  · exact B1476727
  · exact B1476731
  · exact B1476735
  · exact B1476739
  · exact B1476743
  · exact B1476747
  · exact B1476751
  · exact B1476755
  · exact B1476759
  · exact B1476763
  · exact B1476767
  · exact B1476771
  · exact B1476775
  · exact B1476779
  · exact B1476783
  · exact B1476787
  · exact B1476791
  · exact B1476795
  · exact B1476799
  · exact B1476803
  · exact B1476807
  · exact B1476811
  · exact B1476815
  · exact B1476819
  · exact B1476823
  · exact B1476827
  · exact B1476831
  · exact B1476835
  · exact B1476839
  · exact B1476843
  · exact B1476847
  · exact B1476851
  · exact B1476855
  · exact B1476859
  · exact B1476863
  · exact B1476867
  · exact B1476871
  · exact B1476875
  · exact B1476879
  · exact B1476883
  · exact B1476887
  · exact B1476891
  · exact B1476895
  · exact B1476899
  · exact B1476903
  · exact B1476907
  · exact B1476911
  · exact B1476915
  · exact B1476919
  · exact B1476923
  · exact B1476927
  · exact B1476931
  · exact B1476935
  · exact B1476939
  · exact B1476943
  · exact B1476947
  · exact B1476951
  · exact B1476955
  · exact B1476959
  · exact B1476963
  · exact B1476967
  · exact B1476971
  · exact B1476975
  · exact B1476979
  · exact B1476983
  · exact B1476987
  · exact B1476991
  · exact B1476995
  · exact B1476999
  · exact B1477003
  · exact B1477007
  · exact B1477011
  · exact B1477015
  · exact B1477019
  · exact B1477023
  · exact B1477027
  · exact B1477031
  · exact B1477035
  · exact B1477039
  · exact B1477043
  · exact B1477047
  · exact B1477051
  · exact B1477055
  · exact B1477059
  · exact B1477063
  · exact B1477067
  · exact B1477071
  · exact B1477075
  · exact B1477079
  · exact B1477083
  · exact B1477087
  · exact B1477091
  · exact B1477095
  · exact B1477099
  · exact B1477103
  · exact B1477107
  · exact B1477111
  · exact B1477115
  · exact B1477119
  · exact B1477123
  · exact B1477127
  · exact B1477131
  · exact B1477135
  · exact B1477139
  · exact B1477143
  · exact B1477147
  · exact B1477151
  · exact B1477155
  · exact B1477159
  · exact B1477163
  · exact B1477167
  · exact B1477171
  · exact B1477175
  · exact B1477179
  · exact B1477183
  · exact B1477187
  · exact B1477191
  · exact B1477195
  · exact B1477199
  · exact B1477203
  · exact B1477207
  · exact B1477211
  · exact B1477215
  · exact B1477219
  · exact B1477223
  · exact B1477227
  · exact B1477231
  · exact B1477235
  · exact B1477239
  · exact B1477243
  · exact B1477247
  · exact B1477251
  · exact B1477255
  · exact B1477259
  · exact B1477263
  · exact B1477267
  · exact B1477271
  · exact B1477275
  · exact B1477279
  · exact B1477283
  · exact B1477287
  · exact B1477291
  · exact B1477295
  · exact B1477299
  · exact B1477303
  · exact B1477307
  · exact B1477311
  · exact B1477315
  · exact B1477319
  · exact B1477323
  · exact B1477327
  · exact B1477331
  · exact B1477335
  · exact B1477339
  · exact B1477343
  · exact B1477347
  · exact B1477351
  · exact B1477355
  · exact B1477359
  · exact B1477363
  · exact B1477367
  · exact B1477371
  · exact B1477375
  · exact B1477379
  · exact B1477383
  · exact B1477387
  · exact B1477391
  · exact B1477395
  · exact B1477399
  · exact B1477403
  · exact B1477407
  · exact B1477411
  · exact B1477415
  · exact B1477419
  · exact B1477423
  · exact B1477427
  · exact B1477431
  · exact B1477435
  · exact B1477439
  · exact B1477443
  · exact B1477447
  · exact B1477451
  · exact B1477455
  · exact B1477459
  · exact B1477463
  · exact B1477467
  · exact B1477471
  · exact B1477475
  · exact B1477479
  · exact B1477483
  · exact B1477487
  · exact B1477491
  · exact B1477495
  · exact B1477499
  · exact B1477503
  · exact B1477507
  · exact B1477511
  · exact B1477515
  · exact B1477519
  · exact B1477523
  · exact B1477527
  · exact B1477531
  · exact B1477535
  · exact B1477539
  · exact B1477543
  · exact B1477547
  · exact B1477551
  · exact B1477555
  · exact B1477559
  · exact B1477563
  · exact B1477567
  · exact B1477571
  · exact B1477575
  · exact B1477579
  · exact B1477583
  · exact B1477587
  · exact B1477591
  · exact B1477595
  · exact B1477599
  · exact B1477603
  · exact B1477607
  · exact B1477611
  · exact B1477615
  · exact B1477619
  · exact B1477623
  · exact B1477627
  · exact B1477631
  · exact B1477635
  · exact B1477639
  · exact B1477643
  · exact B1477647
  · exact B1477651
  · exact B1477655
  · exact B1477659
  · exact B1477663
  · exact B1477667
  · exact B1477671
  · exact B1477675
  · exact B1477679
  · exact B1477683
  · exact B1477687
  · exact B1477691
  · exact B1477695
  · exact B1477699
  · exact B1477703
  · exact B1477707
  · exact B1477711
  · exact B1477715
  · exact B1477719
  · exact B1477723
  · exact B1477727
  · exact B1477731
  · exact B1477735
  · exact B1477739
  · exact B1477743
  · exact B1477747
  · exact B1477751
  · exact B1477755
  · exact B1477759
  · exact B1477763
  · exact B1477767
  · exact B1477771
  · exact B1477775
  · exact B1477779
  · exact B1477783
  · exact B1477787
  · exact B1477791
  · exact B1477795
  · exact B1477799
  · exact B1477803
  · exact B1477807
  · exact B1477811
  · exact B1477815
  · exact B1477819
  · exact B1477823
  · exact B1477827
  · exact B1477831
  · exact B1477835
  · exact B1477839
  · exact B1477843
  · exact B1477847
  · exact B1477851
  · exact B1477855
  · exact B1477859
  · exact B1477863
  · exact B1477867
  · exact B1477871
  · exact B1477875
  · exact B1477879
  · exact B1477883
  · exact B1477887
  · exact B1477891
  · exact B1477895
  · exact B1477899
  · exact B1477903
  · exact B1477907
  · exact B1477911
  · exact B1477915
  · exact B1477919
  · exact B1477923
  · exact B1477927
  · exact B1477931
  · exact B1477935
  · exact B1477939
  · exact B1477943
  · exact B1477947
  · exact B1477951
  · exact B1477955
  · exact B1477959
  · exact B1477963
  · exact B1477967
  · exact B1477971
  · exact B1477975
  · exact B1477979
  · exact B1477983
  · exact B1477987
  · exact B1477991
  · exact B1477995
  · exact B1477999
  · exact B1478003
  · exact B1478007
  · exact B1478011
  · exact B1478015
  · exact B1478019
  · exact B1478023
  · exact B1478027
  · exact B1478031
  · exact B1478035
  · exact B1478039
  · exact B1478043
  · exact B1478047
  · exact B1478051
  · exact B1478055
  · exact B1478059
  · exact B1478063
  · exact B1478067
  · exact B1478071
  · exact B1478075
  · exact B1478079
  · exact B1478083
  · exact B1478087
  · exact B1478091
  · exact B1478095
  · exact B1478099
  · exact B1478103
  · exact B1478107
  · exact B1478111
  · exact B1478115
  · exact B1478119
  · exact B1478123
  · exact B1478127
  · exact B1478131
  · exact B1478135
  · exact B1478139
  · exact B1478143
  · exact B1478147
  · exact B1478151
  · exact B1478155
  · exact B1478159
  · exact B1478163
  · exact B1478167
  · exact B1478171
  · exact B1478175
  · exact B1478179
  · exact B1478183
  · exact B1478187
  · exact B1478191
  · exact B1478195
  · exact B1478199
  · exact B1478203
  · exact B1478207
  · exact B1478211
  · exact B1478215
  · exact B1478219
  · exact B1478223
  · exact B1478227
  · exact B1478231
  · exact B1478235
  · exact B1478239
  · exact B1478243
  · exact B1478247
  · exact B1478251
  · exact B1478255
  · exact B1478259
  · exact B1478263
  · exact B1478267
  · exact B1478271
  · exact B1478275
  · exact B1478279
  · exact B1478283
  · exact B1478287
  · exact B1478291
  · exact B1478295
  · exact B1478299
  · exact B1478303
  · exact B1478307
  · exact B1478311
  · exact B1478315
  · exact B1478319
  · exact B1478323
  · exact B1478327
  · exact B1478331
  · exact B1478335
  · exact B1478339
  · exact B1478343
  · exact B1478347
  · exact B1478351
  · exact B1478355
  · exact B1478359
  · exact B1478363
  · exact B1478367
  · exact B1478371
  · exact B1478375
  · exact B1478379
  · exact B1478383
  · exact B1478387
  · exact B1478391
  · exact B1478395
  · exact B1478399
  · exact B1478403
  · exact B1478407
  · exact B1478411
  · exact B1478415
  · exact B1478419
  · exact B1478423
  · exact B1478427
  · exact B1478431
  · exact B1478435
  · exact B1478439
  · exact B1478443
  · exact B1478447
  · exact B1478451
  · exact B1478455
  · exact B1478459
  · exact B1478463
  · exact B1478467
  · exact B1478471
  · exact B1478475
  · exact B1478479
  · exact B1478483
  · exact B1478487
  · exact B1478491
  · exact B1478495
  · exact B1478499
  · exact B1478503
  · exact B1478507
  · exact B1478511
  · exact B1478515
  · exact B1478519
  · exact B1478523
  · exact B1478527
  · exact B1478531
  · exact B1478535
  · exact B1478539
  · exact B1478543
  · exact B1478547
  · exact B1478551
  · exact B1478555

theorem solution (m : ℕ) (hlo : 1476558 ≤ m) (hhi : m ≤ 1478558) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 369139 ≤ j := by omega
    have hj2 : j ≤ 369638 := by omega
    have hb : Blo 1476558 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
