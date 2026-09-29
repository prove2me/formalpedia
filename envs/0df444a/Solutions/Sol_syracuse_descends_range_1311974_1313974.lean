-- Prove2me | solution 1 for syracuse_descends_range_1311974_1313974
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:31.874386+00:00
-- url     : https://prove2.me/submissions/e21e209a-58ac-48de-9d3d-1e3d6ed1faff

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


theorem B3325981 : Blo 1311974 3325981 := bbase (se 3 (by rfl) ⟨623621, by rfl⟩ : syracuseStep 3325981 = 1247243) (by norm_num)
theorem B6643781 : Blo 1311974 6643781 := bbase (se 4 (by rfl) ⟨622854, by rfl⟩ : syracuseStep 6643781 = 1245709) (by norm_num)
theorem B4431941 : Blo 1311974 4431941 := bbase (se 4 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 4431941 = 830989) (by norm_num)
theorem B12623957 : Blo 1311974 12623957 := bbase (se 8 (by rfl) ⟨73968, by rfl⟩ : syracuseStep 12623957 = 147937) (by norm_num)
theorem B3547525 : Blo 1311974 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B7479701 : Blo 1311974 7479701 := bbase (se 6 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 7479701 = 350611) (by norm_num)
theorem B4735397 : Blo 1311974 4735397 := bbase (se 4 (by rfl) ⟨443943, by rfl⟩ : syracuseStep 4735397 = 887887) (by norm_num)
theorem B2130349 : Blo 1311974 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B4432373 : Blo 1311974 4432373 := bbase (se 5 (by rfl) ⟨207767, by rfl⟩ : syracuseStep 4432373 = 415535) (by norm_num)
theorem B1868285 : Blo 1311974 1868285 := bbase (se 3 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 1868285 = 700607) (by norm_num)
theorem B2802197 : Blo 1311974 2802197 := bbase (se 6 (by rfl) ⟨65676, by rfl⟩ : syracuseStep 2802197 = 131353) (by norm_num)
theorem B2490925 : Blo 1311974 2490925 := bbase (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) (by norm_num)
theorem B2663045 : Blo 1311974 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B3367565 : Blo 1311974 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B2491069 : Blo 1311974 2491069 := bbase (se 3 (by rfl) ⟨467075, by rfl⟩ : syracuseStep 2491069 = 934151) (by norm_num)
theorem B3195677 : Blo 1311974 3195677 := bbase (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) (by norm_num)
theorem B9462581 : Blo 1311974 9462581 := bbase (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) (by norm_num)
theorem B2491229 : Blo 1311974 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B4981621 : Blo 1311974 4981621 := bbase (se 5 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 4981621 = 467027) (by norm_num)
theorem B1598341 : Blo 1311974 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B3367813 : Blo 1311974 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B4432805 : Blo 1311974 4432805 := bbase (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) (by norm_num)
theorem B1401833 : Blo 1311974 1401833 := bbase (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) (by norm_num)
theorem B2491373 : Blo 1311974 2491373 := bbase (se 3 (by rfl) ⟨467132, by rfl⟩ : syracuseStep 2491373 = 934265) (by norm_num)
theorem B2802701 : Blo 1311974 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B2802709 : Blo 1311974 2802709 := bbase (se 6 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 2802709 = 131377) (by norm_num)
theorem B1868837 : Blo 1311974 1868837 := bbase (se 4 (by rfl) ⟨175203, by rfl⟩ : syracuseStep 1868837 = 350407) (by norm_num)
theorem B4981925 : Blo 1311974 4981925 := bbase (se 4 (by rfl) ⟨467055, by rfl⟩ : syracuseStep 4981925 = 934111) (by norm_num)
theorem B2491661 : Blo 1311974 2491661 := bbase (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) (by norm_num)
theorem B2663693 : Blo 1311974 2663693 := bbase (se 3 (by rfl) ⟨499442, by rfl⟩ : syracuseStep 2663693 = 998885) (by norm_num)
theorem B3990869 : Blo 1311974 3990869 := bbase (se 12 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 3990869 = 2923) (by norm_num)
theorem B6645077 : Blo 1311974 6645077 := bbase (se 12 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 6645077 = 4867) (by norm_num)
theorem B4433237 : Blo 1311974 4433237 := bbase (se 12 (by rfl) ⟨1623, by rfl⟩ : syracuseStep 4433237 = 3247) (by norm_num)
theorem B1475977 : Blo 1311974 1475977 := bbase (se 2 (by rfl) ⟨553491, by rfl⟩ : syracuseStep 1475977 = 1106983) (by norm_num)
theorem B26936725 : Blo 1311974 26936725 := bbase (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) (by norm_num)
theorem B2491813 : Blo 1311974 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B1402277 : Blo 1311974 1402277 := bbase (se 4 (by rfl) ⟨131463, by rfl⟩ : syracuseStep 1402277 = 262927) (by norm_num)
theorem B1476013 : Blo 1311974 1476013 := bbase (se 3 (by rfl) ⟨276752, by rfl⟩ : syracuseStep 1476013 = 553505) (by norm_num)
theorem B1476049 : Blo 1311974 1476049 := bbase (se 2 (by rfl) ⟨553518, by rfl⟩ : syracuseStep 1476049 = 1107037) (by norm_num)
theorem B1476085 : Blo 1311974 1476085 := bbase (se 5 (by rfl) ⟨69191, by rfl⟩ : syracuseStep 1476085 = 138383) (by norm_num)
theorem B1476121 : Blo 1311974 1476121 := bbase (se 2 (by rfl) ⟨553545, by rfl⟩ : syracuseStep 1476121 = 1107091) (by norm_num)
theorem B1476157 : Blo 1311974 1476157 := bbase (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) (by norm_num)
theorem B3737173 : Blo 1311974 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B1476193 : Blo 1311974 1476193 := bbase (se 2 (by rfl) ⟨553572, by rfl⟩ : syracuseStep 1476193 = 1107145) (by norm_num)
theorem B3368549 : Blo 1311974 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B1476229 : Blo 1311974 1476229 := bbase (se 4 (by rfl) ⟨138396, by rfl⟩ : syracuseStep 1476229 = 276793) (by norm_num)
theorem B1402525 : Blo 1311974 1402525 := bbase (se 3 (by rfl) ⟨262973, by rfl⟩ : syracuseStep 1402525 = 525947) (by norm_num)
theorem B1476265 : Blo 1311974 1476265 := bbase (se 2 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 1476265 = 1107199) (by norm_num)
theorem B1476301 : Blo 1311974 1476301 := bbase (se 3 (by rfl) ⟨276806, by rfl⟩ : syracuseStep 1476301 = 553613) (by norm_num)
theorem B2492117 : Blo 1311974 2492117 := bbase (se 7 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 2492117 = 58409) (by norm_num)
theorem B2246357 : Blo 1311974 2246357 := bbase (se 7 (by rfl) ⟨26324, by rfl⟩ : syracuseStep 2246357 = 52649) (by norm_num)
theorem B1476337 : Blo 1311974 1476337 := bbase (se 2 (by rfl) ⟨553626, by rfl⟩ : syracuseStep 1476337 = 1107253) (by norm_num)
theorem B3737333 : Blo 1311974 3737333 := bbase (se 5 (by rfl) ⟨175187, by rfl⟩ : syracuseStep 3737333 = 350375) (by norm_num)
theorem B3155701 : Blo 1311974 3155701 := bbase (se 5 (by rfl) ⟨147923, by rfl⟩ : syracuseStep 3155701 = 295847) (by norm_num)
theorem B4433669 : Blo 1311974 4433669 := bbase (se 4 (by rfl) ⟨415656, by rfl⟩ : syracuseStep 4433669 = 831313) (by norm_num)
theorem B1476373 : Blo 1311974 1476373 := bbase (se 6 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 1476373 = 69205) (by norm_num)
theorem B1869589 : Blo 1311974 1869589 := bbase (se 6 (by rfl) ⟨43818, by rfl⟩ : syracuseStep 1869589 = 87637) (by norm_num)
theorem B1476409 : Blo 1311974 1476409 := bbase (se 2 (by rfl) ⟨553653, by rfl⟩ : syracuseStep 1476409 = 1107307) (by norm_num)
theorem B15976277 : Blo 1311974 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B1476445 : Blo 1311974 1476445 := bbase (se 3 (by rfl) ⟨276833, by rfl⟩ : syracuseStep 1476445 = 553667) (by norm_num)
theorem B1967981 : Blo 1311974 1967981 := bbase (se 3 (by rfl) ⟨368996, by rfl⟩ : syracuseStep 1967981 = 737993) (by norm_num)
theorem B1476481 : Blo 1311974 1476481 := bbase (se 2 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 1476481 = 1107361) (by norm_num)
theorem B1968005 : Blo 1311974 1968005 := bbase (se 4 (by rfl) ⟨184500, by rfl⟩ : syracuseStep 1968005 = 369001) (by norm_num)
theorem B1968029 : Blo 1311974 1968029 := bbase (se 3 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 1968029 = 738011) (by norm_num)
theorem B1476517 : Blo 1311974 1476517 := bbase (se 4 (by rfl) ⟨138423, by rfl⟩ : syracuseStep 1476517 = 276847) (by norm_num)
theorem B1968053 : Blo 1311974 1968053 := bbase (se 5 (by rfl) ⟨92252, by rfl⟩ : syracuseStep 1968053 = 184505) (by norm_num)
theorem B1476553 : Blo 1311974 1476553 := bbase (se 2 (by rfl) ⟨553707, by rfl⟩ : syracuseStep 1476553 = 1107415) (by norm_num)
theorem B1968077 : Blo 1311974 1968077 := bbase (se 3 (by rfl) ⟨369014, by rfl⟩ : syracuseStep 1968077 = 738029) (by norm_num)
theorem B14378965 : Blo 1311974 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B40454101 : Blo 1311974 40454101 := bbase (se 7 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 40454101 = 948143) (by norm_num)
theorem B1968101 : Blo 1311974 1968101 := bbase (se 4 (by rfl) ⟨184509, by rfl⟩ : syracuseStep 1968101 = 369019) (by norm_num)
theorem B3737573 : Blo 1311974 3737573 := bbase (se 4 (by rfl) ⟨350397, by rfl⟩ : syracuseStep 3737573 = 700795) (by norm_num)
theorem B1476589 : Blo 1311974 1476589 := bbase (se 3 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 1476589 = 553721) (by norm_num)
theorem B1968125 : Blo 1311974 1968125 := bbase (se 3 (by rfl) ⟨369023, by rfl⟩ : syracuseStep 1968125 = 738047) (by norm_num)
theorem B1476625 : Blo 1311974 1476625 := bbase (se 2 (by rfl) ⟨553734, by rfl⟩ : syracuseStep 1476625 = 1107469) (by norm_num)
theorem B1968149 : Blo 1311974 1968149 := bbase (se 6 (by rfl) ⟨46128, by rfl⟩ : syracuseStep 1968149 = 92257) (by norm_num)
theorem B1968173 : Blo 1311974 1968173 := bbase (se 3 (by rfl) ⟨369032, by rfl⟩ : syracuseStep 1968173 = 738065) (by norm_num)
theorem B1476661 : Blo 1311974 1476661 := bbase (se 5 (by rfl) ⟨69218, by rfl⟩ : syracuseStep 1476661 = 138437) (by norm_num)
theorem B1968197 : Blo 1311974 1968197 := bbase (se 4 (by rfl) ⟨184518, by rfl⟩ : syracuseStep 1968197 = 369037) (by norm_num)
theorem B2246725 : Blo 1311974 2246725 := bbase (se 4 (by rfl) ⟨210630, by rfl⟩ : syracuseStep 2246725 = 421261) (by norm_num)
theorem B1402957 : Blo 1311974 1402957 := bbase (se 3 (by rfl) ⟨263054, by rfl⟩ : syracuseStep 1402957 = 526109) (by norm_num)
theorem B1476697 : Blo 1311974 1476697 := bbase (se 2 (by rfl) ⟨553761, by rfl⟩ : syracuseStep 1476697 = 1107523) (by norm_num)
theorem B1968221 : Blo 1311974 1968221 := bbase (se 3 (by rfl) ⟨369041, by rfl⟩ : syracuseStep 1968221 = 738083) (by norm_num)
theorem B1968245 : Blo 1311974 1968245 := bbase (se 5 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 1968245 = 184523) (by norm_num)
theorem B2214013 : Blo 1311974 2214013 := bbase (se 3 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 2214013 = 830255) (by norm_num)
theorem B1476733 : Blo 1311974 1476733 := bbase (se 3 (by rfl) ⟨276887, by rfl⟩ : syracuseStep 1476733 = 553775) (by norm_num)
theorem B2803837 : Blo 1311974 2803837 := bbase (se 3 (by rfl) ⟨525719, by rfl⟩ : syracuseStep 2803837 = 1051439) (by norm_num)
theorem B1968269 : Blo 1311974 1968269 := bbase (se 3 (by rfl) ⟨369050, by rfl⟩ : syracuseStep 1968269 = 738101) (by norm_num)
theorem B1403029 : Blo 1311974 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B1476769 : Blo 1311974 1476769 := bbase (se 2 (by rfl) ⟨553788, by rfl⟩ : syracuseStep 1476769 = 1107577) (by norm_num)
theorem B1968293 : Blo 1311974 1968293 := bbase (se 4 (by rfl) ⟨184527, by rfl⟩ : syracuseStep 1968293 = 369055) (by norm_num)
theorem B3737765 : Blo 1311974 3737765 := bbase (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) (by norm_num)
theorem B4434101 : Blo 1311974 4434101 := bbase (se 5 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 4434101 = 415697) (by norm_num)
theorem B1968317 : Blo 1311974 1968317 := bbase (se 3 (by rfl) ⟨369059, by rfl⟩ : syracuseStep 1968317 = 738119) (by norm_num)
theorem B1476805 : Blo 1311974 1476805 := bbase (se 4 (by rfl) ⟨138450, by rfl⟩ : syracuseStep 1476805 = 276901) (by norm_num)
theorem B2214101 : Blo 1311974 2214101 := bbase (se 7 (by rfl) ⟨25946, by rfl⟩ : syracuseStep 2214101 = 51893) (by norm_num)
theorem B1968341 : Blo 1311974 1968341 := bbase (se 7 (by rfl) ⟨23066, by rfl⟩ : syracuseStep 1968341 = 46133) (by norm_num)
theorem B1476841 : Blo 1311974 1476841 := bbase (se 2 (by rfl) ⟨553815, by rfl⟩ : syracuseStep 1476841 = 1107631) (by norm_num)
theorem B1968365 : Blo 1311974 1968365 := bbase (se 3 (by rfl) ⟨369068, by rfl⟩ : syracuseStep 1968365 = 738137) (by norm_num)
theorem B6310133 : Blo 1311974 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B3156221 : Blo 1311974 3156221 := bbase (se 3 (by rfl) ⟨591791, by rfl⟩ : syracuseStep 3156221 = 1183583) (by norm_num)
theorem B1968389 : Blo 1311974 1968389 := bbase (se 4 (by rfl) ⟨184536, by rfl⟩ : syracuseStep 1968389 = 369073) (by norm_num)
theorem B1476877 : Blo 1311974 1476877 := bbase (se 3 (by rfl) ⟨276914, by rfl⟩ : syracuseStep 1476877 = 553829) (by norm_num)
theorem B1968413 : Blo 1311974 1968413 := bbase (se 3 (by rfl) ⟨369077, by rfl⟩ : syracuseStep 1968413 = 738155) (by norm_num)
theorem B1476913 : Blo 1311974 1476913 := bbase (se 2 (by rfl) ⟨553842, by rfl⟩ : syracuseStep 1476913 = 1107685) (by norm_num)
theorem B1968437 : Blo 1311974 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B1968461 : Blo 1311974 1968461 := bbase (se 3 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 1968461 = 738173) (by norm_num)
theorem B2214229 : Blo 1311974 2214229 := bbase (se 10 (by rfl) ⟨3243, by rfl⟩ : syracuseStep 2214229 = 6487) (by norm_num)
theorem B1476949 : Blo 1311974 1476949 := bbase (se 10 (by rfl) ⟨2163, by rfl⟩ : syracuseStep 1476949 = 4327) (by norm_num)
theorem B3156317 : Blo 1311974 3156317 := bbase (se 3 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 3156317 = 1183619) (by norm_num)
theorem B1968485 : Blo 1311974 1968485 := bbase (se 4 (by rfl) ⟨184545, by rfl⟩ : syracuseStep 1968485 = 369091) (by norm_num)
theorem B1476985 : Blo 1311974 1476985 := bbase (se 2 (by rfl) ⟨553869, by rfl⟩ : syracuseStep 1476985 = 1107739) (by norm_num)
theorem B1968509 : Blo 1311974 1968509 := bbase (se 3 (by rfl) ⟨369095, by rfl⟩ : syracuseStep 1968509 = 738191) (by norm_num)
theorem B2247053 : Blo 1311974 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B1968533 : Blo 1311974 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B1477021 : Blo 1311974 1477021 := bbase (se 3 (by rfl) ⟨276941, by rfl⟩ : syracuseStep 1477021 = 553883) (by norm_num)
theorem B2214317 : Blo 1311974 2214317 := bbase (se 3 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 2214317 = 830369) (by norm_num)
theorem B1968557 : Blo 1311974 1968557 := bbase (se 3 (by rfl) ⟨369104, by rfl⟩ : syracuseStep 1968557 = 738209) (by norm_num)
theorem B1477057 : Blo 1311974 1477057 := bbase (se 2 (by rfl) ⟨553896, by rfl⟩ : syracuseStep 1477057 = 1107793) (by norm_num)
theorem B1968581 : Blo 1311974 1968581 := bbase (se 4 (by rfl) ⟨184554, by rfl⟩ : syracuseStep 1968581 = 369109) (by norm_num)
theorem B2492869 : Blo 1311974 2492869 := bbase (se 4 (by rfl) ⟨233706, by rfl⟩ : syracuseStep 2492869 = 467413) (by norm_num)
theorem B11217365 : Blo 1311974 11217365 := bbase (se 7 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 11217365 = 262907) (by norm_num)
theorem B1968605 : Blo 1311974 1968605 := bbase (se 3 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 1968605 = 738227) (by norm_num)
theorem B1477093 : Blo 1311974 1477093 := bbase (se 4 (by rfl) ⟨138477, by rfl⟩ : syracuseStep 1477093 = 276955) (by norm_num)
theorem B1968629 : Blo 1311974 1968629 := bbase (se 5 (by rfl) ⟨92279, by rfl⟩ : syracuseStep 1968629 = 184559) (by norm_num)
theorem B2804213 : Blo 1311974 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B1477129 : Blo 1311974 1477129 := bbase (se 2 (by rfl) ⟨553923, by rfl⟩ : syracuseStep 1477129 = 1107847) (by norm_num)
theorem B1968653 : Blo 1311974 1968653 := bbase (se 3 (by rfl) ⟨369122, by rfl⟩ : syracuseStep 1968653 = 738245) (by norm_num)
theorem B1968677 : Blo 1311974 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B2214445 : Blo 1311974 2214445 := bbase (se 3 (by rfl) ⟨415208, by rfl⟩ : syracuseStep 2214445 = 830417) (by norm_num)
theorem B1477165 : Blo 1311974 1477165 := bbase (se 3 (by rfl) ⟨276968, by rfl⟩ : syracuseStep 1477165 = 553937) (by norm_num)
theorem B1870381 : Blo 1311974 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B7481909 : Blo 1311974 7481909 := bbase (se 5 (by rfl) ⟨350714, by rfl⟩ : syracuseStep 7481909 = 701429) (by norm_num)
theorem B1968701 : Blo 1311974 1968701 := bbase (se 3 (by rfl) ⟨369131, by rfl⟩ : syracuseStep 1968701 = 738263) (by norm_num)
theorem B2247245 : Blo 1311974 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B1477201 : Blo 1311974 1477201 := bbase (se 2 (by rfl) ⟨553950, by rfl⟩ : syracuseStep 1477201 = 1107901) (by norm_num)
theorem B1968725 : Blo 1311974 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B4205141 : Blo 1311974 4205141 := bbase (se 8 (by rfl) ⟨24639, by rfl⟩ : syracuseStep 4205141 = 49279) (by norm_num)
theorem B2493013 : Blo 1311974 2493013 := bbase (se 8 (by rfl) ⟨14607, by rfl⟩ : syracuseStep 2493013 = 29215) (by norm_num)
theorem B6646373 : Blo 1311974 6646373 := bbase (se 4 (by rfl) ⟨623097, by rfl⟩ : syracuseStep 6646373 = 1246195) (by norm_num)
theorem B4434533 : Blo 1311974 4434533 := bbase (se 4 (by rfl) ⟨415737, by rfl⟩ : syracuseStep 4434533 = 831475) (by norm_num)
theorem B1968749 : Blo 1311974 1968749 := bbase (se 3 (by rfl) ⟨369140, by rfl⟩ : syracuseStep 1968749 = 738281) (by norm_num)
theorem B1477237 : Blo 1311974 1477237 := bbase (se 5 (by rfl) ⟨69245, by rfl⟩ : syracuseStep 1477237 = 138491) (by norm_num)
theorem B2214533 : Blo 1311974 2214533 := bbase (se 4 (by rfl) ⟨207612, by rfl⟩ : syracuseStep 2214533 = 415225) (by norm_num)
theorem B1968773 : Blo 1311974 1968773 := bbase (se 4 (by rfl) ⟨184572, by rfl⟩ : syracuseStep 1968773 = 369145) (by norm_num)
theorem B1477273 : Blo 1311974 1477273 := bbase (se 2 (by rfl) ⟨553977, by rfl⟩ : syracuseStep 1477273 = 1107955) (by norm_num)
theorem B1968797 : Blo 1311974 1968797 := bbase (se 3 (by rfl) ⟨369149, by rfl⟩ : syracuseStep 1968797 = 738299) (by norm_num)
theorem B1968821 : Blo 1311974 1968821 := bbase (se 5 (by rfl) ⟨92288, by rfl⟩ : syracuseStep 1968821 = 184577) (by norm_num)
theorem B1477309 : Blo 1311974 1477309 := bbase (se 3 (by rfl) ⟨276995, by rfl⟩ : syracuseStep 1477309 = 553991) (by norm_num)
theorem B1968845 : Blo 1311974 1968845 := bbase (se 3 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 1968845 = 738317) (by norm_num)
theorem B5606101 : Blo 1311974 5606101 := bbase (se 7 (by rfl) ⟨65696, by rfl⟩ : syracuseStep 5606101 = 131393) (by norm_num)
theorem B1477345 : Blo 1311974 1477345 := bbase (se 2 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 1477345 = 1108009) (by norm_num)
theorem B1968869 : Blo 1311974 1968869 := bbase (se 4 (by rfl) ⟨184581, by rfl⟩ : syracuseStep 1968869 = 369163) (by norm_num)
theorem B2493173 : Blo 1311974 2493173 := bbase (se 5 (by rfl) ⟨116867, by rfl⟩ : syracuseStep 2493173 = 233735) (by norm_num)
theorem B1968893 : Blo 1311974 1968893 := bbase (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) (by norm_num)
theorem B2214661 : Blo 1311974 2214661 := bbase (se 4 (by rfl) ⟨207624, by rfl⟩ : syracuseStep 2214661 = 415249) (by norm_num)
theorem B1477381 : Blo 1311974 1477381 := bbase (se 4 (by rfl) ⟨138504, by rfl⟩ : syracuseStep 1477381 = 277009) (by norm_num)
theorem B1968917 : Blo 1311974 1968917 := bbase (se 6 (by rfl) ⟨46146, by rfl⟩ : syracuseStep 1968917 = 92293) (by norm_num)
theorem B8416021 : Blo 1311974 8416021 := bbase (se 6 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 8416021 = 394501) (by norm_num)
theorem B1477417 : Blo 1311974 1477417 := bbase (se 2 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 1477417 = 1108063) (by norm_num)
theorem B2951981 : Blo 1311974 2951981 := bbase (se 3 (by rfl) ⟨553496, by rfl⟩ : syracuseStep 2951981 = 1106993) (by norm_num)
theorem B1968941 : Blo 1311974 1968941 := bbase (se 3 (by rfl) ⟨369176, by rfl⟩ : syracuseStep 1968941 = 738353) (by norm_num)
theorem B1968965 : Blo 1311974 1968965 := bbase (se 4 (by rfl) ⟨184590, by rfl⟩ : syracuseStep 1968965 = 369181) (by norm_num)
theorem B1477453 : Blo 1311974 1477453 := bbase (se 3 (by rfl) ⟨277022, by rfl⟩ : syracuseStep 1477453 = 554045) (by norm_num)
theorem B2214749 : Blo 1311974 2214749 := bbase (se 3 (by rfl) ⟨415265, by rfl⟩ : syracuseStep 2214749 = 830531) (by norm_num)
theorem B1968989 : Blo 1311974 1968989 := bbase (se 3 (by rfl) ⟨369185, by rfl⟩ : syracuseStep 1968989 = 738371) (by norm_num)
theorem B1477489 : Blo 1311974 1477489 := bbase (se 2 (by rfl) ⟨554058, by rfl⟩ : syracuseStep 1477489 = 1108117) (by norm_num)
theorem B2952053 : Blo 1311974 2952053 := bbase (se 5 (by rfl) ⟨138377, by rfl⟩ : syracuseStep 2952053 = 276755) (by norm_num)
theorem B1969013 : Blo 1311974 1969013 := bbase (se 5 (by rfl) ⟨92297, by rfl⟩ : syracuseStep 1969013 = 184595) (by norm_num)
theorem B1870717 : Blo 1311974 1870717 := bbase (se 3 (by rfl) ⟨350759, by rfl⟩ : syracuseStep 1870717 = 701519) (by norm_num)
theorem B4492165 : Blo 1311974 4492165 := bbase (se 4 (by rfl) ⟨421140, by rfl⟩ : syracuseStep 4492165 = 842281) (by norm_num)
theorem B2493317 : Blo 1311974 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B1969037 : Blo 1311974 1969037 := bbase (se 3 (by rfl) ⟨369194, by rfl⟩ : syracuseStep 1969037 = 738389) (by norm_num)
theorem B1477525 : Blo 1311974 1477525 := bbase (se 6 (by rfl) ⟨34629, by rfl⟩ : syracuseStep 1477525 = 69259) (by norm_num)
theorem B4795301 : Blo 1311974 4795301 := bbase (se 4 (by rfl) ⟨449559, by rfl⟩ : syracuseStep 4795301 = 899119) (by norm_num)
theorem B1969061 : Blo 1311974 1969061 := bbase (se 4 (by rfl) ⟨184599, by rfl⟩ : syracuseStep 1969061 = 369199) (by norm_num)
theorem B1477561 : Blo 1311974 1477561 := bbase (se 2 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 1477561 = 1108171) (by norm_num)
theorem B2952125 : Blo 1311974 2952125 := bbase (se 3 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 2952125 = 1107047) (by norm_num)
theorem B1969085 : Blo 1311974 1969085 := bbase (se 3 (by rfl) ⟨369203, by rfl⟩ : syracuseStep 1969085 = 738407) (by norm_num)
theorem B1969109 : Blo 1311974 1969109 := bbase (se 7 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 1969109 = 46151) (by norm_num)
theorem B2214877 : Blo 1311974 2214877 := bbase (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) (by norm_num)
theorem B1477597 : Blo 1311974 1477597 := bbase (se 3 (by rfl) ⟨277049, by rfl⟩ : syracuseStep 1477597 = 554099) (by norm_num)
theorem B1969133 : Blo 1311974 1969133 := bbase (se 3 (by rfl) ⟨369212, by rfl⟩ : syracuseStep 1969133 = 738425) (by norm_num)
theorem B1477633 : Blo 1311974 1477633 := bbase (se 2 (by rfl) ⟨554112, by rfl⟩ : syracuseStep 1477633 = 1108225) (by norm_num)
theorem B2952197 : Blo 1311974 2952197 := bbase (se 4 (by rfl) ⟨276768, by rfl⟩ : syracuseStep 2952197 = 553537) (by norm_num)
theorem B1969157 : Blo 1311974 1969157 := bbase (se 4 (by rfl) ⟨184608, by rfl⟩ : syracuseStep 1969157 = 369217) (by norm_num)
theorem B1969181 : Blo 1311974 1969181 := bbase (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) (by norm_num)
theorem B1477669 : Blo 1311974 1477669 := bbase (se 4 (by rfl) ⟨138531, by rfl⟩ : syracuseStep 1477669 = 277063) (by norm_num)
theorem B2214965 : Blo 1311974 2214965 := bbase (se 5 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 2214965 = 207653) (by norm_num)
theorem B1969205 : Blo 1311974 1969205 := bbase (se 5 (by rfl) ⟨92306, by rfl⟩ : syracuseStep 1969205 = 184613) (by norm_num)
theorem B1477705 : Blo 1311974 1477705 := bbase (se 2 (by rfl) ⟨554139, by rfl⟩ : syracuseStep 1477705 = 1108279) (by norm_num)
theorem B2952269 : Blo 1311974 2952269 := bbase (se 3 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 2952269 = 1107101) (by norm_num)
theorem B1969229 : Blo 1311974 1969229 := bbase (se 3 (by rfl) ⟨369230, by rfl⟩ : syracuseStep 1969229 = 738461) (by norm_num)
theorem B1969253 : Blo 1311974 1969253 := bbase (se 4 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 1969253 = 369235) (by norm_num)
theorem B1477741 : Blo 1311974 1477741 := bbase (se 3 (by rfl) ⟨277076, by rfl⟩ : syracuseStep 1477741 = 554153) (by norm_num)
theorem B1969277 : Blo 1311974 1969277 := bbase (se 3 (by rfl) ⟨369239, by rfl⟩ : syracuseStep 1969277 = 738479) (by norm_num)
theorem B3738757 : Blo 1311974 3738757 := bbase (se 4 (by rfl) ⟨350508, by rfl⟩ : syracuseStep 3738757 = 701017) (by norm_num)
theorem B1477777 : Blo 1311974 1477777 := bbase (se 2 (by rfl) ⟨554166, by rfl⟩ : syracuseStep 1477777 = 1108333) (by norm_num)
theorem B2952341 : Blo 1311974 2952341 := bbase (se 6 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 2952341 = 138391) (by norm_num)
theorem B1969301 : Blo 1311974 1969301 := bbase (se 6 (by rfl) ⟨46155, by rfl⟩ : syracuseStep 1969301 = 92311) (by norm_num)
theorem B4730021 : Blo 1311974 4730021 := bbase (se 4 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 4730021 = 886879) (by norm_num)
theorem B2493605 : Blo 1311974 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B1969325 : Blo 1311974 1969325 := bbase (se 3 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 1969325 = 738497) (by norm_num)
theorem B2215093 : Blo 1311974 2215093 := bbase (se 5 (by rfl) ⟨103832, by rfl⟩ : syracuseStep 2215093 = 207665) (by norm_num)
theorem B1477813 : Blo 1311974 1477813 := bbase (se 5 (by rfl) ⟨69272, by rfl⟩ : syracuseStep 1477813 = 138545) (by norm_num)
theorem B1969349 : Blo 1311974 1969349 := bbase (se 4 (by rfl) ⟨184626, by rfl⟩ : syracuseStep 1969349 = 369253) (by norm_num)
theorem B1477849 : Blo 1311974 1477849 := bbase (se 2 (by rfl) ⟨554193, by rfl⟩ : syracuseStep 1477849 = 1108387) (by norm_num)
theorem B2952413 : Blo 1311974 2952413 := bbase (se 3 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 2952413 = 1107155) (by norm_num)
theorem B1969373 : Blo 1311974 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B4984037 : Blo 1311974 4984037 := bbase (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) (by norm_num)
theorem B1969397 : Blo 1311974 1969397 := bbase (se 5 (by rfl) ⟨92315, by rfl⟩ : syracuseStep 1969397 = 184631) (by norm_num)
theorem B1477885 : Blo 1311974 1477885 := bbase (se 3 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 1477885 = 554207) (by norm_num)
theorem B3321101 : Blo 1311974 3321101 := bbase (se 3 (by rfl) ⟨622706, by rfl⟩ : syracuseStep 3321101 = 1245413) (by norm_num)
theorem B2215181 : Blo 1311974 2215181 := bbase (se 3 (by rfl) ⟨415346, by rfl⟩ : syracuseStep 2215181 = 830693) (by norm_num)
theorem B1969421 : Blo 1311974 1969421 := bbase (se 3 (by rfl) ⟨369266, by rfl⟩ : syracuseStep 1969421 = 738533) (by norm_num)
theorem B1477921 : Blo 1311974 1477921 := bbase (se 2 (by rfl) ⟨554220, by rfl⟩ : syracuseStep 1477921 = 1108441) (by norm_num)
theorem B2952485 : Blo 1311974 2952485 := bbase (se 4 (by rfl) ⟨276795, by rfl⟩ : syracuseStep 2952485 = 553591) (by norm_num)
theorem B1969445 : Blo 1311974 1969445 := bbase (se 4 (by rfl) ⟨184635, by rfl⟩ : syracuseStep 1969445 = 369271) (by norm_num)
theorem B1969469 : Blo 1311974 1969469 := bbase (se 3 (by rfl) ⟨369275, by rfl⟩ : syracuseStep 1969469 = 738551) (by norm_num)
theorem B2493757 : Blo 1311974 2493757 := bbase (se 3 (by rfl) ⟨467579, by rfl⟩ : syracuseStep 2493757 = 935159) (by norm_num)
theorem B1477957 : Blo 1311974 1477957 := bbase (se 4 (by rfl) ⟨138558, by rfl⟩ : syracuseStep 1477957 = 277117) (by norm_num)
theorem B1576265 : Blo 1311974 1576265 := bbase (se 2 (by rfl) ⟨591099, by rfl⟩ : syracuseStep 1576265 = 1182199) (by norm_num)
theorem B1969493 : Blo 1311974 1969493 := bbase (se 11 (by rfl) ⟨1442, by rfl⟩ : syracuseStep 1969493 = 2885) (by norm_num)
theorem B1477993 : Blo 1311974 1477993 := bbase (se 2 (by rfl) ⟨554247, by rfl⟩ : syracuseStep 1477993 = 1108495) (by norm_num)
theorem B2952557 : Blo 1311974 2952557 := bbase (se 3 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 2952557 = 1107209) (by norm_num)
theorem B1969517 : Blo 1311974 1969517 := bbase (se 3 (by rfl) ⟨369284, by rfl⟩ : syracuseStep 1969517 = 738569) (by norm_num)
theorem B1330549 : Blo 1311974 1330549 := bbase (se 5 (by rfl) ⟨62369, by rfl⟩ : syracuseStep 1330549 = 124739) (by norm_num)
theorem B1969541 : Blo 1311974 1969541 := bbase (se 4 (by rfl) ⟨184644, by rfl⟩ : syracuseStep 1969541 = 369289) (by norm_num)
theorem B2215309 : Blo 1311974 2215309 := bbase (se 3 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 2215309 = 830741) (by norm_num)
theorem B1478029 : Blo 1311974 1478029 := bbase (se 3 (by rfl) ⟨277130, by rfl⟩ : syracuseStep 1478029 = 554261) (by norm_num)
theorem B1969565 : Blo 1311974 1969565 := bbase (se 3 (by rfl) ⟨369293, by rfl⟩ : syracuseStep 1969565 = 738587) (by norm_num)
theorem B1478065 : Blo 1311974 1478065 := bbase (se 2 (by rfl) ⟨554274, by rfl⟩ : syracuseStep 1478065 = 1108549) (by norm_num)
theorem B2952629 : Blo 1311974 2952629 := bbase (se 5 (by rfl) ⟨138404, by rfl⟩ : syracuseStep 2952629 = 276809) (by norm_num)
theorem B1969589 : Blo 1311974 1969589 := bbase (se 5 (by rfl) ⟨92324, by rfl⟩ : syracuseStep 1969589 = 184649) (by norm_num)
theorem B1969613 : Blo 1311974 1969613 := bbase (se 3 (by rfl) ⟨369302, by rfl⟩ : syracuseStep 1969613 = 738605) (by norm_num)
theorem B9973205 : Blo 1311974 9973205 := bbase (se 7 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 9973205 = 233747) (by norm_num)
theorem B1478101 : Blo 1311974 1478101 := bbase (se 7 (by rfl) ⟨17321, by rfl⟩ : syracuseStep 1478101 = 34643) (by norm_num)
theorem B2215397 : Blo 1311974 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B1969637 : Blo 1311974 1969637 := bbase (se 4 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 1969637 = 369307) (by norm_num)
theorem B1478137 : Blo 1311974 1478137 := bbase (se 2 (by rfl) ⟨554301, by rfl⟩ : syracuseStep 1478137 = 1108603) (by norm_num)
theorem B2952701 : Blo 1311974 2952701 := bbase (se 3 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 2952701 = 1107263) (by norm_num)
theorem B1969661 : Blo 1311974 1969661 := bbase (se 3 (by rfl) ⟨369311, by rfl⟩ : syracuseStep 1969661 = 738623) (by norm_num)
theorem B4984325 : Blo 1311974 4984325 := bbase (se 4 (by rfl) ⟨467280, by rfl⟩ : syracuseStep 4984325 = 934561) (by norm_num)
theorem B1969685 : Blo 1311974 1969685 := bbase (se 6 (by rfl) ⟨46164, by rfl⟩ : syracuseStep 1969685 = 92329) (by norm_num)
theorem B1478173 : Blo 1311974 1478173 := bbase (se 3 (by rfl) ⟨277157, by rfl⟩ : syracuseStep 1478173 = 554315) (by norm_num)
theorem B1969709 : Blo 1311974 1969709 := bbase (se 3 (by rfl) ⟨369320, by rfl⟩ : syracuseStep 1969709 = 738641) (by norm_num)
theorem B6311477 : Blo 1311974 6311477 := bbase (se 5 (by rfl) ⟨295850, by rfl⟩ : syracuseStep 6311477 = 591701) (by norm_num)
theorem B1478209 : Blo 1311974 1478209 := bbase (se 2 (by rfl) ⟨554328, by rfl⟩ : syracuseStep 1478209 = 1108657) (by norm_num)
theorem B2952773 : Blo 1311974 2952773 := bbase (se 4 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 2952773 = 553645) (by norm_num)
theorem B1969733 : Blo 1311974 1969733 := bbase (se 4 (by rfl) ⟨184662, by rfl⟩ : syracuseStep 1969733 = 369325) (by norm_num)
theorem B1969757 : Blo 1311974 1969757 := bbase (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) (by norm_num)
theorem B3321445 : Blo 1311974 3321445 := bbase (se 4 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 3321445 = 622771) (by norm_num)
theorem B2215525 : Blo 1311974 2215525 := bbase (se 4 (by rfl) ⟨207705, by rfl⟩ : syracuseStep 2215525 = 415411) (by norm_num)
theorem B2494061 : Blo 1311974 2494061 := bbase (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) (by norm_num)
theorem B1969781 : Blo 1311974 1969781 := bbase (se 5 (by rfl) ⟨92333, by rfl⟩ : syracuseStep 1969781 = 184667) (by norm_num)
theorem B2952845 : Blo 1311974 2952845 := bbase (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) (by norm_num)
theorem B1969805 : Blo 1311974 1969805 := bbase (se 3 (by rfl) ⟨369338, by rfl⟩ : syracuseStep 1969805 = 738677) (by norm_num)
theorem B1576597 : Blo 1311974 1576597 := bbase (se 6 (by rfl) ⟨36951, by rfl⟩ : syracuseStep 1576597 = 73903) (by norm_num)
theorem B1969829 : Blo 1311974 1969829 := bbase (se 4 (by rfl) ⟨184671, by rfl⟩ : syracuseStep 1969829 = 369343) (by norm_num)
theorem B2215613 : Blo 1311974 2215613 := bbase (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) (by norm_num)
theorem B1969853 : Blo 1311974 1969853 := bbase (se 3 (by rfl) ⟨369347, by rfl⟩ : syracuseStep 1969853 = 738695) (by norm_num)
theorem B3321557 : Blo 1311974 3321557 := bbase (se 7 (by rfl) ⟨38924, by rfl⟩ : syracuseStep 3321557 = 77849) (by norm_num)
theorem B2952917 : Blo 1311974 2952917 := bbase (se 7 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 2952917 = 69209) (by norm_num)
theorem B1969877 : Blo 1311974 1969877 := bbase (se 7 (by rfl) ⟨23084, by rfl⟩ : syracuseStep 1969877 = 46169) (by norm_num)
theorem B1969901 : Blo 1311974 1969901 := bbase (se 3 (by rfl) ⟨369356, by rfl⟩ : syracuseStep 1969901 = 738713) (by norm_num)
theorem B1969925 : Blo 1311974 1969925 := bbase (se 4 (by rfl) ⟨184680, by rfl⟩ : syracuseStep 1969925 = 369361) (by norm_num)
theorem B2952989 : Blo 1311974 2952989 := bbase (se 3 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 2952989 = 1107371) (by norm_num)
theorem B1969949 : Blo 1311974 1969949 := bbase (se 3 (by rfl) ⟨369365, by rfl⟩ : syracuseStep 1969949 = 738731) (by norm_num)
theorem B1969973 : Blo 1311974 1969973 := bbase (se 5 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 1969973 = 184685) (by norm_num)
theorem B2215741 : Blo 1311974 2215741 := bbase (se 3 (by rfl) ⟨415451, by rfl⟩ : syracuseStep 2215741 = 830903) (by norm_num)
theorem B1969997 : Blo 1311974 1969997 := bbase (se 3 (by rfl) ⟨369374, by rfl⟩ : syracuseStep 1969997 = 738749) (by norm_num)
theorem B4206421 : Blo 1311974 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B2953061 : Blo 1311974 2953061 := bbase (se 4 (by rfl) ⟨276849, by rfl⟩ : syracuseStep 2953061 = 553699) (by norm_num)
theorem B1970021 : Blo 1311974 1970021 := bbase (se 4 (by rfl) ⟨184689, by rfl⟩ : syracuseStep 1970021 = 369379) (by norm_num)
theorem B9965429 : Blo 1311974 9965429 := bbase (se 5 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 9965429 = 934259) (by norm_num)
theorem B6647669 : Blo 1311974 6647669 := bbase (se 5 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 6647669 = 623219) (by norm_num)
theorem B1970045 : Blo 1311974 1970045 := bbase (se 3 (by rfl) ⟨369383, by rfl⟩ : syracuseStep 1970045 = 738767) (by norm_num)
theorem B3321749 : Blo 1311974 3321749 := bbase (se 6 (by rfl) ⟨77853, by rfl⟩ : syracuseStep 3321749 = 155707) (by norm_num)
theorem B2215829 : Blo 1311974 2215829 := bbase (se 6 (by rfl) ⟨51933, by rfl⟩ : syracuseStep 2215829 = 103867) (by norm_num)
theorem B1970069 : Blo 1311974 1970069 := bbase (se 6 (by rfl) ⟨46173, by rfl⟩ : syracuseStep 1970069 = 92347) (by norm_num)
theorem B1331101 : Blo 1311974 1331101 := bbase (se 3 (by rfl) ⟨249581, by rfl⟩ : syracuseStep 1331101 = 499163) (by norm_num)
theorem B2953133 : Blo 1311974 2953133 := bbase (se 3 (by rfl) ⟨553712, by rfl⟩ : syracuseStep 2953133 = 1107425) (by norm_num)
theorem B1970093 : Blo 1311974 1970093 := bbase (se 3 (by rfl) ⟨369392, by rfl⟩ : syracuseStep 1970093 = 738785) (by norm_num)
theorem B1970117 : Blo 1311974 1970117 := bbase (se 4 (by rfl) ⟨184698, by rfl⟩ : syracuseStep 1970117 = 369397) (by norm_num)
theorem B17977301 : Blo 1311974 17977301 := bbase (se 7 (by rfl) ⟨210671, by rfl⟩ : syracuseStep 17977301 = 421343) (by norm_num)
theorem B1970141 : Blo 1311974 1970141 := bbase (se 3 (by rfl) ⟨369401, by rfl⟩ : syracuseStep 1970141 = 738803) (by norm_num)
theorem B2953205 : Blo 1311974 2953205 := bbase (se 5 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 2953205 = 276863) (by norm_num)
theorem B1970165 : Blo 1311974 1970165 := bbase (se 5 (by rfl) ⟨92351, by rfl⟩ : syracuseStep 1970165 = 184703) (by norm_num)
theorem B1970189 : Blo 1311974 1970189 := bbase (se 3 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 1970189 = 738821) (by norm_num)
theorem B2215957 : Blo 1311974 2215957 := bbase (se 6 (by rfl) ⟨51936, by rfl⟩ : syracuseStep 2215957 = 103873) (by norm_num)
theorem B5836837 : Blo 1311974 5836837 := bbase (se 4 (by rfl) ⟨547203, by rfl⟩ : syracuseStep 5836837 = 1094407) (by norm_num)
theorem B1970213 : Blo 1311974 1970213 := bbase (se 4 (by rfl) ⟨184707, by rfl⟩ : syracuseStep 1970213 = 369415) (by norm_num)
theorem B2953277 : Blo 1311974 2953277 := bbase (se 3 (by rfl) ⟨553739, by rfl⟩ : syracuseStep 2953277 = 1107479) (by norm_num)
theorem B1970237 : Blo 1311974 1970237 := bbase (se 3 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 1970237 = 738839) (by norm_num)
theorem B1970261 : Blo 1311974 1970261 := bbase (se 8 (by rfl) ⟨11544, by rfl⟩ : syracuseStep 1970261 = 23089) (by norm_num)
theorem B2805853 : Blo 1311974 2805853 := bbase (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) (by norm_num)
theorem B2216045 : Blo 1311974 2216045 := bbase (se 3 (by rfl) ⟨415508, by rfl⟩ : syracuseStep 2216045 = 831017) (by norm_num)
theorem B1970285 : Blo 1311974 1970285 := bbase (se 3 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 1970285 = 738857) (by norm_num)
theorem B2953349 : Blo 1311974 2953349 := bbase (se 4 (by rfl) ⟨276876, by rfl⟩ : syracuseStep 2953349 = 553753) (by norm_num)
theorem B1970309 : Blo 1311974 1970309 := bbase (se 4 (by rfl) ⟨184716, by rfl⟩ : syracuseStep 1970309 = 369433) (by norm_num)
theorem B1970333 : Blo 1311974 1970333 := bbase (se 3 (by rfl) ⟨369437, by rfl⟩ : syracuseStep 1970333 = 738875) (by norm_num)
theorem B5607589 : Blo 1311974 5607589 := bbase (se 4 (by rfl) ⟨525711, by rfl⟩ : syracuseStep 5607589 = 1051423) (by norm_num)
theorem B5607605 : Blo 1311974 5607605 := bbase (se 5 (by rfl) ⟨262856, by rfl⟩ : syracuseStep 5607605 = 525713) (by norm_num)
theorem B1970357 : Blo 1311974 1970357 := bbase (se 5 (by rfl) ⟨92360, by rfl⟩ : syracuseStep 1970357 = 184721) (by norm_num)
theorem B2953421 : Blo 1311974 2953421 := bbase (se 3 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 2953421 = 1107533) (by norm_num)
theorem B1970381 : Blo 1311974 1970381 := bbase (se 3 (by rfl) ⟨369446, by rfl⟩ : syracuseStep 1970381 = 738893) (by norm_num)
theorem B8523989 : Blo 1311974 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B3739861 : Blo 1311974 3739861 := bbase (se 7 (by rfl) ⟨43826, by rfl⟩ : syracuseStep 3739861 = 87653) (by norm_num)
theorem B1970405 : Blo 1311974 1970405 := bbase (se 4 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 1970405 = 369451) (by norm_num)
theorem B3322093 : Blo 1311974 3322093 := bbase (se 3 (by rfl) ⟨622892, by rfl⟩ : syracuseStep 3322093 = 1245785) (by norm_num)
theorem B2216173 : Blo 1311974 2216173 := bbase (se 3 (by rfl) ⟨415532, by rfl⟩ : syracuseStep 2216173 = 831065) (by norm_num)
theorem B1970429 : Blo 1311974 1970429 := bbase (se 3 (by rfl) ⟨369455, by rfl⟩ : syracuseStep 1970429 = 738911) (by norm_num)
theorem B4428053 : Blo 1311974 4428053 := bbase (se 6 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 4428053 = 207565) (by norm_num)
theorem B2953493 : Blo 1311974 2953493 := bbase (se 6 (by rfl) ⟨69222, by rfl⟩ : syracuseStep 2953493 = 138445) (by norm_num)
theorem B1970453 : Blo 1311974 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B1970477 : Blo 1311974 1970477 := bbase (se 3 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 1970477 = 738929) (by norm_num)
theorem B2101565 : Blo 1311974 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B2216261 : Blo 1311974 2216261 := bbase (se 4 (by rfl) ⟨207774, by rfl⟩ : syracuseStep 2216261 = 415549) (by norm_num)
theorem B1970501 : Blo 1311974 1970501 := bbase (se 4 (by rfl) ⟨184734, by rfl⟩ : syracuseStep 1970501 = 369469) (by norm_num)
theorem B3322205 : Blo 1311974 3322205 := bbase (se 3 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 3322205 = 1245827) (by norm_num)
theorem B2953565 : Blo 1311974 2953565 := bbase (se 3 (by rfl) ⟨553793, by rfl⟩ : syracuseStep 2953565 = 1107587) (by norm_num)
theorem B1970525 : Blo 1311974 1970525 := bbase (se 3 (by rfl) ⟨369473, by rfl⟩ : syracuseStep 1970525 = 738947) (by norm_num)
theorem B1970549 : Blo 1311974 1970549 := bbase (se 5 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 1970549 = 184739) (by norm_num)
theorem B1970573 : Blo 1311974 1970573 := bbase (se 3 (by rfl) ⟨369482, by rfl⟩ : syracuseStep 1970573 = 738965) (by norm_num)
theorem B2953637 : Blo 1311974 2953637 := bbase (se 4 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 2953637 = 553807) (by norm_num)
theorem B1970597 : Blo 1311974 1970597 := bbase (se 4 (by rfl) ⟨184743, by rfl⟩ : syracuseStep 1970597 = 369487) (by norm_num)
theorem B1798573 : Blo 1311974 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1970621 : Blo 1311974 1970621 := bbase (se 3 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 1970621 = 738983) (by norm_num)
theorem B1995205 : Blo 1311974 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B2216389 : Blo 1311974 2216389 := bbase (se 4 (by rfl) ⟨207786, by rfl⟩ : syracuseStep 2216389 = 415573) (by norm_num)
theorem B4493765 : Blo 1311974 4493765 := bbase (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) (by norm_num)
theorem B1348045 : Blo 1311974 1348045 := bbase (se 3 (by rfl) ⟨252758, by rfl⟩ : syracuseStep 1348045 = 505517) (by norm_num)
theorem B5681621 : Blo 1311974 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B1970645 : Blo 1311974 1970645 := bbase (se 7 (by rfl) ⟨23093, by rfl⟩ : syracuseStep 1970645 = 46187) (by norm_num)
theorem B2953709 : Blo 1311974 2953709 := bbase (se 3 (by rfl) ⟨553820, by rfl⟩ : syracuseStep 2953709 = 1107641) (by norm_num)
theorem B1970669 : Blo 1311974 1970669 := bbase (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) (by norm_num)
theorem B1970693 : Blo 1311974 1970693 := bbase (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) (by norm_num)
theorem B1577485 : Blo 1311974 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B3322397 : Blo 1311974 3322397 := bbase (se 3 (by rfl) ⟨622949, by rfl⟩ : syracuseStep 3322397 = 1245899) (by norm_num)
theorem B1774109 : Blo 1311974 1774109 := bbase (se 3 (by rfl) ⟨332645, by rfl⟩ : syracuseStep 1774109 = 665291) (by norm_num)
theorem B2216477 : Blo 1311974 2216477 := bbase (se 3 (by rfl) ⟨415589, by rfl⟩ : syracuseStep 2216477 = 831179) (by norm_num)
theorem B1970717 : Blo 1311974 1970717 := bbase (se 3 (by rfl) ⟨369509, by rfl⟩ : syracuseStep 1970717 = 739019) (by norm_num)
theorem B2953781 : Blo 1311974 2953781 := bbase (se 5 (by rfl) ⟨138458, by rfl⟩ : syracuseStep 2953781 = 276917) (by norm_num)
theorem B1970741 : Blo 1311974 1970741 := bbase (se 5 (by rfl) ⟨92378, by rfl⟩ : syracuseStep 1970741 = 184757) (by norm_num)
theorem B1970765 : Blo 1311974 1970765 := bbase (se 3 (by rfl) ⟨369518, by rfl⟩ : syracuseStep 1970765 = 739037) (by norm_num)
theorem B1970789 : Blo 1311974 1970789 := bbase (se 4 (by rfl) ⟨184761, by rfl⟩ : syracuseStep 1970789 = 369523) (by norm_num)
theorem B2953853 : Blo 1311974 2953853 := bbase (se 3 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 2953853 = 1107695) (by norm_num)
theorem B1970813 : Blo 1311974 1970813 := bbase (se 3 (by rfl) ⟨369527, by rfl⟩ : syracuseStep 1970813 = 739055) (by norm_num)
theorem B1970837 : Blo 1311974 1970837 := bbase (se 6 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 1970837 = 92383) (by norm_num)
theorem B2216605 : Blo 1311974 2216605 := bbase (se 3 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 2216605 = 831227) (by norm_num)
theorem B4985509 : Blo 1311974 4985509 := bbase (se 4 (by rfl) ⟨467391, by rfl⟩ : syracuseStep 4985509 = 934783) (by norm_num)
theorem B1970861 : Blo 1311974 1970861 := bbase (se 3 (by rfl) ⟨369536, by rfl⟩ : syracuseStep 1970861 = 739073) (by norm_num)
theorem B4428485 : Blo 1311974 4428485 := bbase (se 4 (by rfl) ⟨415170, by rfl⟩ : syracuseStep 4428485 = 830341) (by norm_num)
theorem B2953925 : Blo 1311974 2953925 := bbase (se 4 (by rfl) ⟨276930, by rfl⟩ : syracuseStep 2953925 = 553861) (by norm_num)
theorem B1970885 : Blo 1311974 1970885 := bbase (se 4 (by rfl) ⟨184770, by rfl⟩ : syracuseStep 1970885 = 369541) (by norm_num)
theorem B1970909 : Blo 1311974 1970909 := bbase (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) (by norm_num)
theorem B2216693 : Blo 1311974 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B1970933 : Blo 1311974 1970933 := bbase (se 5 (by rfl) ⟨92387, by rfl⟩ : syracuseStep 1970933 = 184775) (by norm_num)
theorem B5985029 : Blo 1311974 5985029 := bbase (se 4 (by rfl) ⟨561096, by rfl⟩ : syracuseStep 5985029 = 1122193) (by norm_num)
theorem B3994373 : Blo 1311974 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B2953997 : Blo 1311974 2953997 := bbase (se 3 (by rfl) ⟨553874, by rfl⟩ : syracuseStep 2953997 = 1107749) (by norm_num)
theorem B1970957 : Blo 1311974 1970957 := bbase (se 3 (by rfl) ⟨369554, by rfl⟩ : syracuseStep 1970957 = 739109) (by norm_num)
theorem B2700101 : Blo 1311974 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B2954069 : Blo 1311974 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B3322741 : Blo 1311974 3322741 := bbase (se 5 (by rfl) ⟨155753, by rfl⟩ : syracuseStep 3322741 = 311507) (by norm_num)
theorem B2216821 : Blo 1311974 2216821 := bbase (se 5 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 2216821 = 207827) (by norm_num)
theorem B2954141 : Blo 1311974 2954141 := bbase (se 3 (by rfl) ⟨553901, by rfl⟩ : syracuseStep 2954141 = 1107803) (by norm_num)
theorem B2216909 : Blo 1311974 2216909 := bbase (se 3 (by rfl) ⟨415670, by rfl⟩ : syracuseStep 2216909 = 831341) (by norm_num)
theorem B4985813 : Blo 1311974 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B3322853 : Blo 1311974 3322853 := bbase (se 4 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 3322853 = 623035) (by norm_num)
theorem B2954213 : Blo 1311974 2954213 := bbase (se 4 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 2954213 = 553915) (by norm_num)
theorem B2954285 : Blo 1311974 2954285 := bbase (se 3 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 2954285 = 1107857) (by norm_num)
theorem B2217037 : Blo 1311974 2217037 := bbase (se 3 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 2217037 = 831389) (by norm_num)
theorem B2102365 : Blo 1311974 2102365 := bbase (se 3 (by rfl) ⟨394193, by rfl⟩ : syracuseStep 2102365 = 788387) (by norm_num)
theorem B4428917 : Blo 1311974 4428917 := bbase (se 5 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 4428917 = 415211) (by norm_num)
theorem B2954357 : Blo 1311974 2954357 := bbase (se 5 (by rfl) ⟨138485, by rfl⟩ : syracuseStep 2954357 = 276971) (by norm_num)
theorem B6648965 : Blo 1311974 6648965 := bbase (se 4 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 6648965 = 1246681) (by norm_num)
theorem B1348745 : Blo 1311974 1348745 := bbase (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) (by norm_num)
theorem B3323045 : Blo 1311974 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B4207781 : Blo 1311974 4207781 := bbase (se 4 (by rfl) ⟨394479, by rfl⟩ : syracuseStep 4207781 = 788959) (by norm_num)
theorem B2217125 : Blo 1311974 2217125 := bbase (se 4 (by rfl) ⟨207855, by rfl⟩ : syracuseStep 2217125 = 415711) (by norm_num)
theorem B2954429 : Blo 1311974 2954429 := bbase (se 3 (by rfl) ⟨553955, by rfl⟩ : syracuseStep 2954429 = 1107911) (by norm_num)
theorem B5125349 : Blo 1311974 5125349 := bbase (se 4 (by rfl) ⟨480501, by rfl⟩ : syracuseStep 5125349 = 961003) (by norm_num)
theorem B2954501 : Blo 1311974 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B4207909 : Blo 1311974 4207909 := bbase (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) (by norm_num)
theorem B2217253 : Blo 1311974 2217253 := bbase (se 4 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 2217253 = 415735) (by norm_num)
theorem B7476533 : Blo 1311974 7476533 := bbase (se 5 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 7476533 = 700925) (by norm_num)
theorem B12621109 : Blo 1311974 12621109 := bbase (se 5 (by rfl) ⟨591614, by rfl⟩ : syracuseStep 12621109 = 1183229) (by norm_num)
theorem B1774909 : Blo 1311974 1774909 := bbase (se 3 (by rfl) ⟨332795, by rfl⟩ : syracuseStep 1774909 = 665591) (by norm_num)
theorem B2954573 : Blo 1311974 2954573 := bbase (se 3 (by rfl) ⟨553982, by rfl⟩ : syracuseStep 2954573 = 1107965) (by norm_num)
theorem B2954645 : Blo 1311974 2954645 := bbase (se 6 (by rfl) ⟨69249, by rfl⟩ : syracuseStep 2954645 = 138499) (by norm_num)
theorem B1996213 : Blo 1311974 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B42563029 : Blo 1311974 42563029 := bbase (se 7 (by rfl) ⟨498785, by rfl⟩ : syracuseStep 42563029 = 997571) (by norm_num)
theorem B5469653 : Blo 1311974 5469653 := bbase (se 7 (by rfl) ⟨64097, by rfl⟩ : syracuseStep 5469653 = 128195) (by norm_num)
theorem B2954717 : Blo 1311974 2954717 := bbase (se 3 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 2954717 = 1108019) (by norm_num)
theorem B1496549 : Blo 1311974 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B3323389 : Blo 1311974 3323389 := bbase (se 3 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 3323389 = 1246271) (by norm_num)
theorem B6313477 : Blo 1311974 6313477 := bbase (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) (by norm_num)
theorem B4429349 : Blo 1311974 4429349 := bbase (se 4 (by rfl) ⟨415251, by rfl⟩ : syracuseStep 4429349 = 830503) (by norm_num)
theorem B2954789 : Blo 1311974 2954789 := bbase (se 4 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 2954789 = 554023) (by norm_num)
theorem B4208165 : Blo 1311974 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B1578533 : Blo 1311974 1578533 := bbase (se 4 (by rfl) ⟨147987, by rfl⟩ : syracuseStep 1578533 = 295975) (by norm_num)
theorem B3995237 : Blo 1311974 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B3323501 : Blo 1311974 3323501 := bbase (se 3 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 3323501 = 1246313) (by norm_num)
theorem B2954861 : Blo 1311974 2954861 := bbase (se 3 (by rfl) ⟨554036, by rfl⟩ : syracuseStep 2954861 = 1108073) (by norm_num)
theorem B2102917 : Blo 1311974 2102917 := bbase (se 4 (by rfl) ⟨197148, by rfl⟩ : syracuseStep 2102917 = 394297) (by norm_num)
theorem B2954933 : Blo 1311974 2954933 := bbase (se 5 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 2954933 = 277025) (by norm_num)
theorem B3741365 : Blo 1311974 3741365 := bbase (se 5 (by rfl) ⟨175376, by rfl⟩ : syracuseStep 3741365 = 350753) (by norm_num)
theorem B1660601 : Blo 1311974 1660601 := bbase (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) (by norm_num)
theorem B1660657 : Blo 1311974 1660657 := bbase (se 2 (by rfl) ⟨622746, by rfl⟩ : syracuseStep 1660657 = 1245493) (by norm_num)
theorem B2955005 : Blo 1311974 2955005 := bbase (se 3 (by rfl) ⟨554063, by rfl⟩ : syracuseStep 2955005 = 1108127) (by norm_num)
theorem B2660125 : Blo 1311974 2660125 := bbase (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) (by norm_num)
theorem B3323693 : Blo 1311974 3323693 := bbase (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) (by norm_num)
theorem B2955077 : Blo 1311974 2955077 := bbase (se 4 (by rfl) ⟨277038, by rfl⟩ : syracuseStep 2955077 = 554077) (by norm_num)
theorem B1660753 : Blo 1311974 1660753 := bbase (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) (by norm_num)
theorem B4732789 : Blo 1311974 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B2103173 : Blo 1311974 2103173 := bbase (se 4 (by rfl) ⟨197172, by rfl⟩ : syracuseStep 2103173 = 394345) (by norm_num)
theorem B2955149 : Blo 1311974 2955149 := bbase (se 3 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 2955149 = 1108181) (by norm_num)
theorem B7985045 : Blo 1311974 7985045 := bbase (se 6 (by rfl) ⟨187149, by rfl⟩ : syracuseStep 7985045 = 374299) (by norm_num)
theorem B2365357 : Blo 1311974 2365357 := bbase (se 3 (by rfl) ⟨443504, by rfl⟩ : syracuseStep 2365357 = 887009) (by norm_num)
theorem B4429781 : Blo 1311974 4429781 := bbase (se 7 (by rfl) ⟨51911, by rfl⟩ : syracuseStep 4429781 = 103823) (by norm_num)
theorem B2955221 : Blo 1311974 2955221 := bbase (se 7 (by rfl) ⟨34631, by rfl⟩ : syracuseStep 2955221 = 69263) (by norm_num)
theorem B1660925 : Blo 1311974 1660925 := bbase (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) (by norm_num)
theorem B2955293 : Blo 1311974 2955293 := bbase (se 3 (by rfl) ⟨554117, by rfl⟩ : syracuseStep 2955293 = 1108235) (by norm_num)
theorem B1660981 : Blo 1311974 1660981 := bbase (se 5 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 1660981 = 155717) (by norm_num)
theorem B2955365 : Blo 1311974 2955365 := bbase (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) (by norm_num)
theorem B3324037 : Blo 1311974 3324037 := bbase (se 4 (by rfl) ⟨311628, by rfl⟩ : syracuseStep 3324037 = 623257) (by norm_num)
theorem B6305941 : Blo 1311974 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B1661077 : Blo 1311974 1661077 := bbase (se 6 (by rfl) ⟨38931, by rfl⟩ : syracuseStep 1661077 = 77863) (by norm_num)
theorem B2955437 : Blo 1311974 2955437 := bbase (se 3 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 2955437 = 1108289) (by norm_num)
theorem B2463925 : Blo 1311974 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B3324149 : Blo 1311974 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B2955509 : Blo 1311974 2955509 := bbase (se 5 (by rfl) ⟨138539, by rfl⟩ : syracuseStep 2955509 = 277079) (by norm_num)
theorem B2955581 : Blo 1311974 2955581 := bbase (se 3 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 2955581 = 1108343) (by norm_num)
theorem B1661249 : Blo 1311974 1661249 := bbase (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) (by norm_num)
theorem B2881885 : Blo 1311974 2881885 := bbase (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) (by norm_num)
theorem B1661305 : Blo 1311974 1661305 := bbase (se 2 (by rfl) ⟨622989, by rfl⟩ : syracuseStep 1661305 = 1245979) (by norm_num)
theorem B4430213 : Blo 1311974 4430213 := bbase (se 4 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 4430213 = 830665) (by norm_num)
theorem B5609861 : Blo 1311974 5609861 := bbase (se 4 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 5609861 = 1051849) (by norm_num)
theorem B2955653 : Blo 1311974 2955653 := bbase (se 4 (by rfl) ⟨277092, by rfl⟩ : syracuseStep 2955653 = 554185) (by norm_num)
theorem B6650261 : Blo 1311974 6650261 := bbase (se 6 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 6650261 = 311731) (by norm_num)
theorem B2365853 : Blo 1311974 2365853 := bbase (se 3 (by rfl) ⟨443597, by rfl⟩ : syracuseStep 2365853 = 887195) (by norm_num)
theorem B3324341 : Blo 1311974 3324341 := bbase (se 5 (by rfl) ⟨155828, by rfl⟩ : syracuseStep 3324341 = 311657) (by norm_num)
theorem B2955725 : Blo 1311974 2955725 := bbase (se 3 (by rfl) ⟨554198, by rfl⟩ : syracuseStep 2955725 = 1108397) (by norm_num)
theorem B7477717 : Blo 1311974 7477717 := bbase (se 7 (by rfl) ⟨87629, by rfl⟩ : syracuseStep 7477717 = 175259) (by norm_num)
theorem B1661401 : Blo 1311974 1661401 := bbase (se 2 (by rfl) ⟨623025, by rfl⟩ : syracuseStep 1661401 = 1246051) (by norm_num)
theorem B3594725 : Blo 1311974 3594725 := bbase (se 4 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 3594725 = 674011) (by norm_num)
theorem B2955797 : Blo 1311974 2955797 := bbase (se 6 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 2955797 = 138553) (by norm_num)
theorem B2103877 : Blo 1311974 2103877 := bbase (se 4 (by rfl) ⟨197238, by rfl⟩ : syracuseStep 2103877 = 394477) (by norm_num)
theorem B2398805 : Blo 1311974 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B2955869 : Blo 1311974 2955869 := bbase (se 3 (by rfl) ⟨554225, by rfl⟩ : syracuseStep 2955869 = 1108451) (by norm_num)
theorem B1661573 : Blo 1311974 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B2955941 : Blo 1311974 2955941 := bbase (se 4 (by rfl) ⟨277119, by rfl⟩ : syracuseStep 2955941 = 554239) (by norm_num)
theorem B1661629 : Blo 1311974 1661629 := bbase (se 3 (by rfl) ⟨311555, by rfl⟩ : syracuseStep 1661629 = 623111) (by norm_num)
theorem B2956013 : Blo 1311974 2956013 := bbase (se 3 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 2956013 = 1108505) (by norm_num)
theorem B3324685 : Blo 1311974 3324685 := bbase (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) (by norm_num)
theorem B1661725 : Blo 1311974 1661725 := bbase (se 3 (by rfl) ⟨311573, by rfl⟩ : syracuseStep 1661725 = 623147) (by norm_num)
theorem B6642485 : Blo 1311974 6642485 := bbase (se 5 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 6642485 = 622733) (by norm_num)
theorem B4430645 : Blo 1311974 4430645 := bbase (se 5 (by rfl) ⟨207686, by rfl⟩ : syracuseStep 4430645 = 415373) (by norm_num)
theorem B2956085 : Blo 1311974 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B3324797 : Blo 1311974 3324797 := bbase (se 3 (by rfl) ⟨623399, by rfl⟩ : syracuseStep 3324797 = 1246799) (by norm_num)
theorem B2956157 : Blo 1311974 2956157 := bbase (se 3 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 2956157 = 1108559) (by norm_num)
theorem B1498009 : Blo 1311974 1498009 := bbase (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) (by norm_num)
theorem B2956229 : Blo 1311974 2956229 := bbase (se 4 (by rfl) ⟨277146, by rfl⟩ : syracuseStep 2956229 = 554293) (by norm_num)
theorem B1661897 : Blo 1311974 1661897 := bbase (se 2 (by rfl) ⟨623211, by rfl⟩ : syracuseStep 1661897 = 1246423) (by norm_num)
theorem B2104301 : Blo 1311974 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B1661953 : Blo 1311974 1661953 := bbase (se 2 (by rfl) ⟨623232, by rfl⟩ : syracuseStep 1661953 = 1246465) (by norm_num)
theorem B2956301 : Blo 1311974 2956301 := bbase (se 3 (by rfl) ⟨554306, by rfl⟩ : syracuseStep 2956301 = 1108613) (by norm_num)
theorem B9460757 : Blo 1311974 9460757 := bbase (se 6 (by rfl) ⟨221736, by rfl⟩ : syracuseStep 9460757 = 443473) (by norm_num)
theorem B4987925 : Blo 1311974 4987925 := bbase (se 6 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 4987925 = 233809) (by norm_num)
theorem B3152933 : Blo 1311974 3152933 := bbase (se 4 (by rfl) ⟨295587, by rfl⟩ : syracuseStep 3152933 = 591175) (by norm_num)
theorem B3324989 : Blo 1311974 3324989 := bbase (se 3 (by rfl) ⟨623435, by rfl⟩ : syracuseStep 3324989 = 1246871) (by norm_num)
theorem B2956373 : Blo 1311974 2956373 := bbase (se 8 (by rfl) ⟨17322, by rfl⟩ : syracuseStep 2956373 = 34645) (by norm_num)
theorem B1662049 : Blo 1311974 1662049 := bbase (se 2 (by rfl) ⟨623268, by rfl⟩ : syracuseStep 1662049 = 1246537) (by norm_num)
theorem B2276573 : Blo 1311974 2276573 := bbase (se 3 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 2276573 = 853715) (by norm_num)
theorem B4431077 : Blo 1311974 4431077 := bbase (se 4 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 4431077 = 830827) (by norm_num)
theorem B8428789 : Blo 1311974 8428789 := bbase (se 5 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 8428789 = 790199) (by norm_num)
theorem B1662221 : Blo 1311974 1662221 := bbase (se 3 (by rfl) ⟨311666, by rfl⟩ : syracuseStep 1662221 = 623333) (by norm_num)
theorem B2104589 : Blo 1311974 2104589 := bbase (se 3 (by rfl) ⟨394610, by rfl⟩ : syracuseStep 2104589 = 789221) (by norm_num)
theorem B2366741 : Blo 1311974 2366741 := bbase (se 6 (by rfl) ⟨55470, by rfl⟩ : syracuseStep 2366741 = 110941) (by norm_num)
theorem B4988213 : Blo 1311974 4988213 := bbase (se 5 (by rfl) ⟨233822, by rfl⟩ : syracuseStep 4988213 = 467645) (by norm_num)
theorem B1662277 : Blo 1311974 1662277 := bbase (se 4 (by rfl) ⟨155838, by rfl⟩ : syracuseStep 1662277 = 311677) (by norm_num)
theorem B2661781 : Blo 1311974 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B3325333 : Blo 1311974 3325333 := bbase (se 6 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 3325333 = 155875) (by norm_num)
theorem B1662373 : Blo 1311974 1662373 := bbase (se 4 (by rfl) ⟨155847, by rfl⟩ : syracuseStep 1662373 = 311695) (by norm_num)
theorem B3325445 : Blo 1311974 3325445 := bbase (se 4 (by rfl) ⟨311760, by rfl⟩ : syracuseStep 3325445 = 623521) (by norm_num)
theorem B11214389 : Blo 1311974 11214389 := bbase (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) (by norm_num)
theorem B2367029 : Blo 1311974 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B5766709 : Blo 1311974 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1662545 : Blo 1311974 1662545 := bbase (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) (by norm_num)
theorem B1662601 : Blo 1311974 1662601 := bbase (se 2 (by rfl) ⟨623475, by rfl⟩ : syracuseStep 1662601 = 1246951) (by norm_num)
theorem B8412821 : Blo 1311974 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B4431509 : Blo 1311974 4431509 := bbase (se 6 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 4431509 = 207727) (by norm_num)
theorem B6651557 : Blo 1311974 6651557 := bbase (se 4 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 6651557 = 1247167) (by norm_num)
theorem B3325637 : Blo 1311974 3325637 := bbase (se 4 (by rfl) ⟨311778, by rfl⟩ : syracuseStep 3325637 = 623557) (by norm_num)
theorem B1662697 : Blo 1311974 1662697 := bbase (se 2 (by rfl) ⟨623511, by rfl⟩ : syracuseStep 1662697 = 1247023) (by norm_num)
theorem B3546965 : Blo 1311974 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B1662869 : Blo 1311974 1662869 := bbase (se 6 (by rfl) ⟨38973, by rfl⟩ : syracuseStep 1662869 = 77947) (by norm_num)
theorem B2662301 : Blo 1311974 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B1662925 : Blo 1311974 1662925 := bbase (se 3 (by rfl) ⟨311798, by rfl⟩ : syracuseStep 1662925 = 623597) (by norm_num)
theorem B7782449 : Blo 1311974 7782449 := bstep (se 2 (by rfl) ⟨2918418, by rfl⟩ : syracuseStep 7782449 = 5836837) B5836837
theorem B8413253 : Blo 1311974 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B4432049 : Blo 1311974 4432049 := bstep (se 2 (by rfl) ⟨1662018, by rfl⟩ : syracuseStep 4432049 = 3324037) B3324037
theorem B3285233 : Blo 1311974 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B1868131 : Blo 1311974 1868131 := bstep (se 1 (by rfl) ⟨1401098, by rfl⟩ : syracuseStep 1868131 = 2802197) B2802197
theorem B3596653 : Blo 1311974 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B2245043 : Blo 1311974 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B3842513 : Blo 1311974 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B3990019 : Blo 1311974 3990019 := bstep (se 1 (by rfl) ⟨2992514, by rfl⟩ : syracuseStep 3990019 = 5985029) B5985029
theorem B2662915 : Blo 1311974 2662915 := bstep (se 1 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 2662915 = 3994373) B3994373
theorem B6308387 : Blo 1311974 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B6070861 : Blo 1311974 6070861 := bstep (se 3 (by rfl) ⟨1138286, by rfl⟩ : syracuseStep 6070861 = 2276573) B2276573
theorem B9970289 : Blo 1311974 9970289 := bstep (se 2 (by rfl) ⟨3738858, by rfl⟩ : syracuseStep 9970289 = 7477717) B7477717
theorem B6644429 : Blo 1311974 6644429 := bstep (se 3 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 6644429 = 2491661) B2491661
theorem B4432589 : Blo 1311974 4432589 := bstep (se 3 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 4432589 = 1662221) B1662221
theorem B5612237 : Blo 1311974 5612237 := bstep (se 3 (by rfl) ⟨1052294, by rfl⟩ : syracuseStep 5612237 = 2104589) B2104589
theorem B4432643 : Blo 1311974 4432643 := bstep (se 1 (by rfl) ⟨3324482, by rfl⟩ : syracuseStep 4432643 = 6648965) B6648965
theorem B23970613 : Blo 1311974 23970613 := bstep (se 5 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 23970613 = 2247245) B2247245
theorem B3416899 : Blo 1311974 3416899 := bstep (se 1 (by rfl) ⟨2562674, by rfl⟩ : syracuseStep 3416899 = 5125349) B5125349
theorem B7480133 : Blo 1311974 7480133 := bstep (se 4 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 7480133 = 1402525) B1402525
theorem B5604173 : Blo 1311974 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B4203373 : Blo 1311974 4203373 := bstep (se 3 (by rfl) ⟨788132, by rfl⟩ : syracuseStep 4203373 = 1576265) B1576265
theorem B4432913 : Blo 1311974 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B2245699 : Blo 1311974 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2663491 : Blo 1311974 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B6308941 : Blo 1311974 6308941 := bstep (se 3 (by rfl) ⟨1182926, by rfl⟩ : syracuseStep 6308941 = 2365853) B2365853
theorem B2491555 : Blo 1311974 2491555 := bstep (se 1 (by rfl) ⟨1868666, by rfl⟩ : syracuseStep 2491555 = 3737333) B3737333
theorem B2131121 : Blo 1311974 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B4490417 : Blo 1311974 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B5989553 : Blo 1311974 5989553 := bstep (se 2 (by rfl) ⟨2246082, by rfl⟩ : syracuseStep 5989553 = 4492165) B4492165
theorem B10650851 : Blo 1311974 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B1311987 : Blo 1311974 1311987 := bstep (se 1 (by rfl) ⟨983990, by rfl⟩ : syracuseStep 1311987 = 1967981) B1967981
theorem B1312003 : Blo 1311974 1312003 := bstep (se 1 (by rfl) ⟨984002, by rfl⟩ : syracuseStep 1312003 = 1968005) B1968005
theorem B1402115 : Blo 1311974 1402115 := bstep (se 1 (by rfl) ⟨1051586, by rfl⟩ : syracuseStep 1402115 = 2103173) B2103173
theorem B3990797 : Blo 1311974 3990797 := bstep (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) B1496549
theorem B1312019 : Blo 1311974 1312019 := bstep (se 1 (by rfl) ⟨984014, by rfl⟩ : syracuseStep 1312019 = 1968029) B1968029
theorem B1312035 : Blo 1311974 1312035 := bstep (se 1 (by rfl) ⟨984026, by rfl⟩ : syracuseStep 1312035 = 1968053) B1968053
theorem B1312051 : Blo 1311974 1312051 := bstep (se 1 (by rfl) ⟨984038, by rfl⟩ : syracuseStep 1312051 = 1968077) B1968077
theorem B1312067 : Blo 1311974 1312067 := bstep (se 1 (by rfl) ⟨984050, by rfl⟩ : syracuseStep 1312067 = 1968101) B1968101
theorem B2491715 : Blo 1311974 2491715 := bstep (se 1 (by rfl) ⟨1868786, by rfl⟩ : syracuseStep 2491715 = 3737573) B3737573
theorem B4982093 : Blo 1311974 4982093 := bstep (se 3 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 4982093 = 1868285) B1868285
theorem B1312083 : Blo 1311974 1312083 := bstep (se 1 (by rfl) ⟨984062, by rfl⟩ : syracuseStep 1312083 = 1968125) B1968125
theorem B1312099 : Blo 1311974 1312099 := bstep (se 1 (by rfl) ⟨984074, by rfl⟩ : syracuseStep 1312099 = 1968149) B1968149
theorem B3736945 : Blo 1311974 3736945 := bstep (se 2 (by rfl) ⟨1401354, by rfl⟩ : syracuseStep 3736945 = 2802709) B2802709
theorem B1312115 : Blo 1311974 1312115 := bstep (se 1 (by rfl) ⟨984086, by rfl⟩ : syracuseStep 1312115 = 1968173) B1968173
theorem B1312131 : Blo 1311974 1312131 := bstep (se 1 (by rfl) ⟨984098, by rfl⟩ : syracuseStep 1312131 = 1968197) B1968197
theorem B1312147 : Blo 1311974 1312147 := bstep (se 1 (by rfl) ⟨984110, by rfl⟩ : syracuseStep 1312147 = 1968221) B1968221
theorem B1312163 : Blo 1311974 1312163 := bstep (se 1 (by rfl) ⟨984122, by rfl⟩ : syracuseStep 1312163 = 1968245) B1968245
theorem B1312179 : Blo 1311974 1312179 := bstep (se 1 (by rfl) ⟨984134, by rfl⟩ : syracuseStep 1312179 = 1968269) B1968269
theorem B1312195 : Blo 1311974 1312195 := bstep (se 1 (by rfl) ⟨984146, by rfl⟩ : syracuseStep 1312195 = 1968293) B1968293
theorem B1312211 : Blo 1311974 1312211 := bstep (se 1 (by rfl) ⟨984158, by rfl⟩ : syracuseStep 1312211 = 1968317) B1968317
theorem B1476067 : Blo 1311974 1476067 := bstep (se 1 (by rfl) ⟨1107050, by rfl⟩ : syracuseStep 1476067 = 2214101) B2214101
theorem B1312227 : Blo 1311974 1312227 := bstep (se 1 (by rfl) ⟨984170, by rfl⟩ : syracuseStep 1312227 = 1968341) B1968341
theorem B1312243 : Blo 1311974 1312243 := bstep (se 1 (by rfl) ⟨984182, by rfl⟩ : syracuseStep 1312243 = 1968365) B1968365
theorem B1312259 : Blo 1311974 1312259 := bstep (se 1 (by rfl) ⟨984194, by rfl⟩ : syracuseStep 1312259 = 1968389) B1968389
theorem B1312275 : Blo 1311974 1312275 := bstep (se 1 (by rfl) ⟨984206, by rfl⟩ : syracuseStep 1312275 = 1968413) B1968413
theorem B1312291 : Blo 1311974 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B4433453 : Blo 1311974 4433453 := bstep (se 3 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 4433453 = 1662545) B1662545
theorem B1312307 : Blo 1311974 1312307 := bstep (se 1 (by rfl) ⟨984230, by rfl⟩ : syracuseStep 1312307 = 1968461) B1968461
theorem B1312323 : Blo 1311974 1312323 := bstep (se 1 (by rfl) ⟨984242, by rfl⟩ : syracuseStep 1312323 = 1968485) B1968485
theorem B1312339 : Blo 1311974 1312339 := bstep (se 1 (by rfl) ⟨984254, by rfl⟩ : syracuseStep 1312339 = 1968509) B1968509
theorem B1312355 : Blo 1311974 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B4433507 : Blo 1311974 4433507 := bstep (se 1 (by rfl) ⟨3325130, by rfl⟩ : syracuseStep 4433507 = 6650261) B6650261
theorem B1476211 : Blo 1311974 1476211 := bstep (se 1 (by rfl) ⟨1107158, by rfl⟩ : syracuseStep 1476211 = 2214317) B2214317
theorem B1312371 : Blo 1311974 1312371 := bstep (se 1 (by rfl) ⟨984278, by rfl⟩ : syracuseStep 1312371 = 1968557) B1968557
theorem B1312387 : Blo 1311974 1312387 := bstep (se 1 (by rfl) ⟨984290, by rfl⟩ : syracuseStep 1312387 = 1968581) B1968581
theorem B1312403 : Blo 1311974 1312403 := bstep (se 1 (by rfl) ⟨984302, by rfl⟩ : syracuseStep 1312403 = 1968605) B1968605
theorem B1312419 : Blo 1311974 1312419 := bstep (se 1 (by rfl) ⟨984314, by rfl⟩ : syracuseStep 1312419 = 1968629) B1968629
theorem B1869475 : Blo 1311974 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B1312435 : Blo 1311974 1312435 := bstep (se 1 (by rfl) ⟨984326, by rfl⟩ : syracuseStep 1312435 = 1968653) B1968653
theorem B1312451 : Blo 1311974 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B1312467 : Blo 1311974 1312467 := bstep (se 1 (by rfl) ⟨984350, by rfl⟩ : syracuseStep 1312467 = 1968701) B1968701
theorem B1312483 : Blo 1311974 1312483 := bstep (se 1 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 1312483 = 1968725) B1968725
theorem B2803427 : Blo 1311974 2803427 := bstep (se 1 (by rfl) ⟨2102570, by rfl⟩ : syracuseStep 2803427 = 4205141) B4205141
theorem B1599203 : Blo 1311974 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B16828145 : Blo 1311974 16828145 := bstep (se 2 (by rfl) ⟨6310554, by rfl⟩ : syracuseStep 16828145 = 12621109) B12621109
theorem B1312499 : Blo 1311974 1312499 := bstep (se 1 (by rfl) ⟨984374, by rfl⟩ : syracuseStep 1312499 = 1968749) B1968749
theorem B1476355 : Blo 1311974 1476355 := bstep (se 1 (by rfl) ⟨1107266, by rfl⟩ : syracuseStep 1476355 = 2214533) B2214533
theorem B1312515 : Blo 1311974 1312515 := bstep (se 1 (by rfl) ⟨984386, by rfl⟩ : syracuseStep 1312515 = 1968773) B1968773
theorem B1312531 : Blo 1311974 1312531 := bstep (se 1 (by rfl) ⟨984398, by rfl⟩ : syracuseStep 1312531 = 1968797) B1968797
theorem B1312547 : Blo 1311974 1312547 := bstep (se 1 (by rfl) ⟨984410, by rfl⟩ : syracuseStep 1312547 = 1968821) B1968821
theorem B1312563 : Blo 1311974 1312563 := bstep (se 1 (by rfl) ⟨984422, by rfl⟩ : syracuseStep 1312563 = 1968845) B1968845
theorem B1312579 : Blo 1311974 1312579 := bstep (se 1 (by rfl) ⟨984434, by rfl⟩ : syracuseStep 1312579 = 1968869) B1968869
theorem B1312595 : Blo 1311974 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1967969 : Blo 1311974 1967969 := bstep (se 2 (by rfl) ⟨737988, by rfl⟩ : syracuseStep 1967969 = 1475977) B1475977
theorem B1312611 : Blo 1311974 1312611 := bstep (se 1 (by rfl) ⟨984458, by rfl⟩ : syracuseStep 1312611 = 1968917) B1968917
theorem B35915633 : Blo 1311974 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B3549041 : Blo 1311974 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B1967987 : Blo 1311974 1967987 := bstep (se 1 (by rfl) ⟨1475990, by rfl⟩ : syracuseStep 1967987 = 2951981) B2951981
theorem B1312627 : Blo 1311974 1312627 := bstep (se 1 (by rfl) ⟨984470, by rfl⟩ : syracuseStep 1312627 = 1968941) B1968941
theorem B4433777 : Blo 1311974 4433777 := bstep (se 2 (by rfl) ⟨1662666, by rfl⟩ : syracuseStep 4433777 = 3325333) B3325333
theorem B1312643 : Blo 1311974 1312643 := bstep (se 1 (by rfl) ⟨984482, by rfl⟩ : syracuseStep 1312643 = 1968965) B1968965
theorem B1968017 : Blo 1311974 1968017 := bstep (se 2 (by rfl) ⟨738006, by rfl⟩ : syracuseStep 1968017 = 1476013) B1476013
theorem B1476499 : Blo 1311974 1476499 := bstep (se 1 (by rfl) ⟨1107374, by rfl⟩ : syracuseStep 1476499 = 2214749) B2214749
theorem B1312659 : Blo 1311974 1312659 := bstep (se 1 (by rfl) ⟨984494, by rfl⟩ : syracuseStep 1312659 = 1968989) B1968989
theorem B1968035 : Blo 1311974 1968035 := bstep (se 1 (by rfl) ⟨1476026, by rfl⟩ : syracuseStep 1968035 = 2952053) B2952053
theorem B1312675 : Blo 1311974 1312675 := bstep (se 1 (by rfl) ⟨984506, by rfl⟩ : syracuseStep 1312675 = 1969013) B1969013
theorem B1312691 : Blo 1311974 1312691 := bstep (se 1 (by rfl) ⟨984518, by rfl⟩ : syracuseStep 1312691 = 1969037) B1969037
theorem B1968065 : Blo 1311974 1968065 := bstep (se 2 (by rfl) ⟨738024, by rfl⟩ : syracuseStep 1968065 = 1476049) B1476049
theorem B3196867 : Blo 1311974 3196867 := bstep (se 1 (by rfl) ⟨2397650, by rfl⟩ : syracuseStep 3196867 = 4795301) B4795301
theorem B7096261 : Blo 1311974 7096261 := bstep (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) B1330549
theorem B1312707 : Blo 1311974 1312707 := bstep (se 1 (by rfl) ⟨984530, by rfl⟩ : syracuseStep 1312707 = 1969061) B1969061
theorem B1968083 : Blo 1311974 1968083 := bstep (se 1 (by rfl) ⟨1476062, by rfl⟩ : syracuseStep 1968083 = 2952125) B2952125
theorem B1312723 : Blo 1311974 1312723 := bstep (se 1 (by rfl) ⟨984542, by rfl⟩ : syracuseStep 1312723 = 1969085) B1969085
theorem B1312739 : Blo 1311974 1312739 := bstep (se 1 (by rfl) ⟨984554, by rfl⟩ : syracuseStep 1312739 = 1969109) B1969109
theorem B1968113 : Blo 1311974 1968113 := bstep (se 2 (by rfl) ⟨738042, by rfl⟩ : syracuseStep 1968113 = 1476085) B1476085
theorem B1312755 : Blo 1311974 1312755 := bstep (se 1 (by rfl) ⟨984566, by rfl⟩ : syracuseStep 1312755 = 1969133) B1969133
theorem B1402867 : Blo 1311974 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B1968131 : Blo 1311974 1968131 := bstep (se 1 (by rfl) ⟨1476098, by rfl⟩ : syracuseStep 1968131 = 2952197) B2952197
theorem B1312771 : Blo 1311974 1312771 := bstep (se 1 (by rfl) ⟨984578, by rfl⟩ : syracuseStep 1312771 = 1969157) B1969157
theorem B1312787 : Blo 1311974 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B1968161 : Blo 1311974 1968161 := bstep (se 2 (by rfl) ⟨738060, by rfl⟩ : syracuseStep 1968161 = 1476121) B1476121
theorem B1476643 : Blo 1311974 1476643 := bstep (se 1 (by rfl) ⟨1107482, by rfl⟩ : syracuseStep 1476643 = 2214965) B2214965
theorem B1312803 : Blo 1311974 1312803 := bstep (se 1 (by rfl) ⟨984602, by rfl⟩ : syracuseStep 1312803 = 1969205) B1969205
theorem B1968179 : Blo 1311974 1968179 := bstep (se 1 (by rfl) ⟨1476134, by rfl⟩ : syracuseStep 1968179 = 2952269) B2952269
theorem B1312819 : Blo 1311974 1312819 := bstep (se 1 (by rfl) ⟨984614, by rfl⟩ : syracuseStep 1312819 = 1969229) B1969229
theorem B1312835 : Blo 1311974 1312835 := bstep (se 1 (by rfl) ⟨984626, by rfl⟩ : syracuseStep 1312835 = 1969253) B1969253
theorem B8521805 : Blo 1311974 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B1968209 : Blo 1311974 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B1312851 : Blo 1311974 1312851 := bstep (se 1 (by rfl) ⟨984638, by rfl⟩ : syracuseStep 1312851 = 1969277) B1969277
theorem B1968227 : Blo 1311974 1968227 := bstep (se 1 (by rfl) ⟨1476170, by rfl⟩ : syracuseStep 1968227 = 2952341) B2952341
theorem B1312867 : Blo 1311974 1312867 := bstep (se 1 (by rfl) ⟨984650, by rfl⟩ : syracuseStep 1312867 = 1969301) B1969301
theorem B4982897 : Blo 1311974 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B1312883 : Blo 1311974 1312883 := bstep (se 1 (by rfl) ⟨984662, by rfl⟩ : syracuseStep 1312883 = 1969325) B1969325
theorem B1968257 : Blo 1311974 1968257 := bstep (se 2 (by rfl) ⟨738096, by rfl⟩ : syracuseStep 1968257 = 1476193) B1476193
theorem B1312899 : Blo 1311974 1312899 := bstep (se 1 (by rfl) ⟨984674, by rfl⟩ : syracuseStep 1312899 = 1969349) B1969349
theorem B1968275 : Blo 1311974 1968275 := bstep (se 1 (by rfl) ⟨1476206, by rfl⟩ : syracuseStep 1968275 = 2952413) B2952413
theorem B1312915 : Blo 1311974 1312915 := bstep (se 1 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 1312915 = 1969373) B1969373
theorem B1312931 : Blo 1311974 1312931 := bstep (se 1 (by rfl) ⟨984698, by rfl⟩ : syracuseStep 1312931 = 1969397) B1969397
theorem B1968305 : Blo 1311974 1968305 := bstep (se 2 (by rfl) ⟨738114, by rfl⟩ : syracuseStep 1968305 = 1476229) B1476229
theorem B2803889 : Blo 1311974 2803889 := bstep (se 2 (by rfl) ⟨1051458, by rfl⟩ : syracuseStep 2803889 = 2102917) B2102917
theorem B2214067 : Blo 1311974 2214067 := bstep (se 1 (by rfl) ⟨1660550, by rfl⟩ : syracuseStep 2214067 = 3321101) B3321101
theorem B1476787 : Blo 1311974 1476787 := bstep (se 1 (by rfl) ⟨1107590, by rfl⟩ : syracuseStep 1476787 = 2215181) B2215181
theorem B1312947 : Blo 1311974 1312947 := bstep (se 1 (by rfl) ⟨984710, by rfl⟩ : syracuseStep 1312947 = 1969421) B1969421
theorem B1968323 : Blo 1311974 1968323 := bstep (se 1 (by rfl) ⟨1476242, by rfl⟩ : syracuseStep 1968323 = 2952485) B2952485
theorem B1312963 : Blo 1311974 1312963 := bstep (se 1 (by rfl) ⟨984722, by rfl⟩ : syracuseStep 1312963 = 1969445) B1969445
theorem B1312979 : Blo 1311974 1312979 := bstep (se 1 (by rfl) ⟨984734, by rfl⟩ : syracuseStep 1312979 = 1969469) B1969469
theorem B1968353 : Blo 1311974 1968353 := bstep (se 2 (by rfl) ⟨738132, by rfl⟩ : syracuseStep 1968353 = 1476265) B1476265
theorem B1312995 : Blo 1311974 1312995 := bstep (se 1 (by rfl) ⟨984746, by rfl⟩ : syracuseStep 1312995 = 1969493) B1969493
theorem B1968371 : Blo 1311974 1968371 := bstep (se 1 (by rfl) ⟨1476278, by rfl⟩ : syracuseStep 1968371 = 2952557) B2952557
theorem B1313011 : Blo 1311974 1313011 := bstep (se 1 (by rfl) ⟨984758, by rfl⟩ : syracuseStep 1313011 = 1969517) B1969517
theorem B1313027 : Blo 1311974 1313027 := bstep (se 1 (by rfl) ⟨984770, by rfl⟩ : syracuseStep 1313027 = 1969541) B1969541
theorem B1968401 : Blo 1311974 1968401 := bstep (se 2 (by rfl) ⟨738150, by rfl⟩ : syracuseStep 1968401 = 1476301) B1476301
theorem B1313043 : Blo 1311974 1313043 := bstep (se 1 (by rfl) ⟨984782, by rfl⟩ : syracuseStep 1313043 = 1969565) B1969565
theorem B1968419 : Blo 1311974 1968419 := bstep (se 1 (by rfl) ⟨1476314, by rfl⟩ : syracuseStep 1968419 = 2952629) B2952629
theorem B1313059 : Blo 1311974 1313059 := bstep (se 1 (by rfl) ⟨984794, by rfl⟩ : syracuseStep 1313059 = 1969589) B1969589
theorem B1313075 : Blo 1311974 1313075 := bstep (se 1 (by rfl) ⟨984806, by rfl⟩ : syracuseStep 1313075 = 1969613) B1969613
theorem B2214209 : Blo 1311974 2214209 := bstep (se 2 (by rfl) ⟨830328, by rfl⟩ : syracuseStep 2214209 = 1660657) B1660657
theorem B1968449 : Blo 1311974 1968449 := bstep (se 2 (by rfl) ⟨738168, by rfl⟩ : syracuseStep 1968449 = 1476337) B1476337
theorem B1476931 : Blo 1311974 1476931 := bstep (se 1 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 1476931 = 2215397) B2215397
theorem B1313091 : Blo 1311974 1313091 := bstep (se 1 (by rfl) ⟨984818, by rfl⟩ : syracuseStep 1313091 = 1969637) B1969637
theorem B1968467 : Blo 1311974 1968467 := bstep (se 1 (by rfl) ⟨1476350, by rfl⟩ : syracuseStep 1968467 = 2952701) B2952701
theorem B1313107 : Blo 1311974 1313107 := bstep (se 1 (by rfl) ⟨984830, by rfl⟩ : syracuseStep 1313107 = 1969661) B1969661
theorem B1313123 : Blo 1311974 1313123 := bstep (se 1 (by rfl) ⟨984842, by rfl⟩ : syracuseStep 1313123 = 1969685) B1969685
theorem B1968497 : Blo 1311974 1968497 := bstep (se 2 (by rfl) ⟨738186, by rfl⟩ : syracuseStep 1968497 = 1476373) B1476373
theorem B2492785 : Blo 1311974 2492785 := bstep (se 2 (by rfl) ⟨934794, by rfl⟩ : syracuseStep 2492785 = 1869589) B1869589
theorem B1313139 : Blo 1311974 1313139 := bstep (se 1 (by rfl) ⟨984854, by rfl⟩ : syracuseStep 1313139 = 1969709) B1969709
theorem B1968515 : Blo 1311974 1968515 := bstep (se 1 (by rfl) ⟨1476386, by rfl⟩ : syracuseStep 1968515 = 2952773) B2952773
theorem B1313155 : Blo 1311974 1313155 := bstep (se 1 (by rfl) ⟨984866, by rfl⟩ : syracuseStep 1313155 = 1969733) B1969733
theorem B4434317 : Blo 1311974 4434317 := bstep (se 3 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 4434317 = 1662869) B1662869
theorem B1313171 : Blo 1311974 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B1968545 : Blo 1311974 1968545 := bstep (se 2 (by rfl) ⟨738204, by rfl⟩ : syracuseStep 1968545 = 1476409) B1476409
theorem B1313187 : Blo 1311974 1313187 := bstep (se 1 (by rfl) ⟨984890, by rfl⟩ : syracuseStep 1313187 = 1969781) B1969781
theorem B1968563 : Blo 1311974 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B1313203 : Blo 1311974 1313203 := bstep (se 1 (by rfl) ⟨984902, by rfl⟩ : syracuseStep 1313203 = 1969805) B1969805
theorem B2214337 : Blo 1311974 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B76687813 : Blo 1311974 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B1313219 : Blo 1311974 1313219 := bstep (se 1 (by rfl) ⟨984914, by rfl⟩ : syracuseStep 1313219 = 1969829) B1969829
theorem B4434371 : Blo 1311974 4434371 := bstep (se 1 (by rfl) ⟨3325778, by rfl⟩ : syracuseStep 4434371 = 6651557) B6651557
theorem B1968593 : Blo 1311974 1968593 := bstep (se 2 (by rfl) ⟨738222, by rfl⟩ : syracuseStep 1968593 = 1476445) B1476445
theorem B1477075 : Blo 1311974 1477075 := bstep (se 1 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 1477075 = 2215613) B2215613
theorem B1313235 : Blo 1311974 1313235 := bstep (se 1 (by rfl) ⟨984926, by rfl⟩ : syracuseStep 1313235 = 1969853) B1969853
theorem B2214371 : Blo 1311974 2214371 := bstep (se 1 (by rfl) ⟨1660778, by rfl⟩ : syracuseStep 2214371 = 3321557) B3321557
theorem B1968611 : Blo 1311974 1968611 := bstep (se 1 (by rfl) ⟨1476458, by rfl⟩ : syracuseStep 1968611 = 2952917) B2952917
theorem B1313251 : Blo 1311974 1313251 := bstep (se 1 (by rfl) ⟨984938, by rfl⟩ : syracuseStep 1313251 = 1969877) B1969877
theorem B6310385 : Blo 1311974 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B1313267 : Blo 1311974 1313267 := bstep (se 1 (by rfl) ⟨984950, by rfl⟩ : syracuseStep 1313267 = 1969901) B1969901
theorem B1968641 : Blo 1311974 1968641 := bstep (se 2 (by rfl) ⟨738240, by rfl⟩ : syracuseStep 1968641 = 1476481) B1476481
theorem B1313283 : Blo 1311974 1313283 := bstep (se 1 (by rfl) ⟨984962, by rfl⟩ : syracuseStep 1313283 = 1969925) B1969925
theorem B1968659 : Blo 1311974 1968659 := bstep (se 1 (by rfl) ⟨1476494, by rfl⟩ : syracuseStep 1968659 = 2952989) B2952989
theorem B1313299 : Blo 1311974 1313299 := bstep (se 1 (by rfl) ⟨984974, by rfl⟩ : syracuseStep 1313299 = 1969949) B1969949
theorem B1313315 : Blo 1311974 1313315 := bstep (se 1 (by rfl) ⟨984986, by rfl⟩ : syracuseStep 1313315 = 1969973) B1969973
theorem B1968689 : Blo 1311974 1968689 := bstep (se 2 (by rfl) ⟨738258, by rfl⟩ : syracuseStep 1968689 = 1476517) B1476517
theorem B1313331 : Blo 1311974 1313331 := bstep (se 1 (by rfl) ⟨984998, by rfl⟩ : syracuseStep 1313331 = 1969997) B1969997
theorem B1968707 : Blo 1311974 1968707 := bstep (se 1 (by rfl) ⟨1476530, by rfl⟩ : syracuseStep 1968707 = 2953061) B2953061
theorem B1313347 : Blo 1311974 1313347 := bstep (se 1 (by rfl) ⟨985010, by rfl⟩ : syracuseStep 1313347 = 1970021) B1970021
theorem B1313363 : Blo 1311974 1313363 := bstep (se 1 (by rfl) ⟨985022, by rfl⟩ : syracuseStep 1313363 = 1970045) B1970045
theorem B1968737 : Blo 1311974 1968737 := bstep (se 2 (by rfl) ⟨738276, by rfl⟩ : syracuseStep 1968737 = 1476553) B1476553
theorem B2214499 : Blo 1311974 2214499 := bstep (se 1 (by rfl) ⟨1660874, by rfl⟩ : syracuseStep 2214499 = 3321749) B3321749
theorem B1477219 : Blo 1311974 1477219 := bstep (se 1 (by rfl) ⟨1107914, by rfl⟩ : syracuseStep 1477219 = 2215829) B2215829
theorem B1313379 : Blo 1311974 1313379 := bstep (se 1 (by rfl) ⟨985034, by rfl⟩ : syracuseStep 1313379 = 1970069) B1970069
theorem B3738221 : Blo 1311974 3738221 := bstep (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) B1401833
theorem B53938801 : Blo 1311974 53938801 := bstep (se 2 (by rfl) ⟨20227050, by rfl⟩ : syracuseStep 53938801 = 40454101) B40454101
theorem B1968755 : Blo 1311974 1968755 := bstep (se 1 (by rfl) ⟨1476566, by rfl⟩ : syracuseStep 1968755 = 2953133) B2953133
theorem B1313395 : Blo 1311974 1313395 := bstep (se 1 (by rfl) ⟨985046, by rfl⟩ : syracuseStep 1313395 = 1970093) B1970093
theorem B1313411 : Blo 1311974 1313411 := bstep (se 1 (by rfl) ⟨985058, by rfl⟩ : syracuseStep 1313411 = 1970117) B1970117
theorem B1968785 : Blo 1311974 1968785 := bstep (se 2 (by rfl) ⟨738294, by rfl⟩ : syracuseStep 1968785 = 1476589) B1476589
theorem B1313427 : Blo 1311974 1313427 := bstep (se 1 (by rfl) ⟨985070, by rfl⟩ : syracuseStep 1313427 = 1970141) B1970141
theorem B1968803 : Blo 1311974 1968803 := bstep (se 1 (by rfl) ⟨1476602, by rfl⟩ : syracuseStep 1968803 = 2953205) B2953205
theorem B1313443 : Blo 1311974 1313443 := bstep (se 1 (by rfl) ⟨985082, by rfl⟩ : syracuseStep 1313443 = 1970165) B1970165
theorem B1313459 : Blo 1311974 1313459 := bstep (se 1 (by rfl) ⟨985094, by rfl⟩ : syracuseStep 1313459 = 1970189) B1970189
theorem B1968833 : Blo 1311974 1968833 := bstep (se 2 (by rfl) ⟨738312, by rfl⟩ : syracuseStep 1968833 = 1476625) B1476625
theorem B1313475 : Blo 1311974 1313475 := bstep (se 1 (by rfl) ⟨985106, by rfl⟩ : syracuseStep 1313475 = 1970213) B1970213
theorem B7473869 : Blo 1311974 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B1968851 : Blo 1311974 1968851 := bstep (se 1 (by rfl) ⟨1476638, by rfl⟩ : syracuseStep 1968851 = 2953277) B2953277
theorem B1313491 : Blo 1311974 1313491 := bstep (se 1 (by rfl) ⟨985118, by rfl⟩ : syracuseStep 1313491 = 1970237) B1970237
theorem B4434641 : Blo 1311974 4434641 := bstep (se 2 (by rfl) ⟨1662990, by rfl⟩ : syracuseStep 4434641 = 3325981) B3325981
theorem B1313507 : Blo 1311974 1313507 := bstep (se 1 (by rfl) ⟨985130, by rfl⟩ : syracuseStep 1313507 = 1970261) B1970261
theorem B8415971 : Blo 1311974 8415971 := bstep (se 1 (by rfl) ⟨6311978, by rfl⟩ : syracuseStep 8415971 = 12623957) B12623957
theorem B2214641 : Blo 1311974 2214641 := bstep (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) B1660981
theorem B1968881 : Blo 1311974 1968881 := bstep (se 2 (by rfl) ⟨738330, by rfl⟩ : syracuseStep 1968881 = 1476661) B1476661
theorem B1477363 : Blo 1311974 1477363 := bstep (se 1 (by rfl) ⟨1108022, by rfl⟩ : syracuseStep 1477363 = 2216045) B2216045
theorem B1313523 : Blo 1311974 1313523 := bstep (se 1 (by rfl) ⟨985142, by rfl⟩ : syracuseStep 1313523 = 1970285) B1970285
theorem B1968899 : Blo 1311974 1968899 := bstep (se 1 (by rfl) ⟨1476674, by rfl⟩ : syracuseStep 1968899 = 2953349) B2953349
theorem B1313539 : Blo 1311974 1313539 := bstep (se 1 (by rfl) ⟨985154, by rfl⟩ : syracuseStep 1313539 = 1970309) B1970309
theorem B4983565 : Blo 1311974 4983565 := bstep (se 3 (by rfl) ⟨934418, by rfl⟩ : syracuseStep 4983565 = 1868837) B1868837
theorem B1870609 : Blo 1311974 1870609 := bstep (se 2 (by rfl) ⟨701478, by rfl⟩ : syracuseStep 1870609 = 1402957) B1402957
theorem B1313555 : Blo 1311974 1313555 := bstep (se 1 (by rfl) ⟨985166, by rfl⟩ : syracuseStep 1313555 = 1970333) B1970333
theorem B1968929 : Blo 1311974 1968929 := bstep (se 2 (by rfl) ⟨738348, by rfl⟩ : syracuseStep 1968929 = 1476697) B1476697
theorem B3738403 : Blo 1311974 3738403 := bstep (se 1 (by rfl) ⟨2803802, by rfl⟩ : syracuseStep 3738403 = 5607605) B5607605
theorem B1313571 : Blo 1311974 1313571 := bstep (se 1 (by rfl) ⟨985178, by rfl⟩ : syracuseStep 1313571 = 1970357) B1970357
theorem B1968947 : Blo 1311974 1968947 := bstep (se 1 (by rfl) ⟨1476710, by rfl⟩ : syracuseStep 1968947 = 2953421) B2953421
theorem B1313587 : Blo 1311974 1313587 := bstep (se 1 (by rfl) ⟨985190, by rfl⟩ : syracuseStep 1313587 = 1970381) B1970381
theorem B1313603 : Blo 1311974 1313603 := bstep (se 1 (by rfl) ⟨985202, by rfl⟩ : syracuseStep 1313603 = 1970405) B1970405
theorem B2952017 : Blo 1311974 2952017 := bstep (se 2 (by rfl) ⟨1107006, by rfl⟩ : syracuseStep 2952017 = 2214013) B2214013
theorem B1968977 : Blo 1311974 1968977 := bstep (se 2 (by rfl) ⟨738366, by rfl⟩ : syracuseStep 1968977 = 1476733) B1476733
theorem B3738449 : Blo 1311974 3738449 := bstep (se 2 (by rfl) ⟨1401918, by rfl⟩ : syracuseStep 3738449 = 2803837) B2803837
theorem B1313619 : Blo 1311974 1313619 := bstep (se 1 (by rfl) ⟨985214, by rfl⟩ : syracuseStep 1313619 = 1970429) B1970429
theorem B2952035 : Blo 1311974 2952035 := bstep (se 1 (by rfl) ⟨2214026, by rfl⟩ : syracuseStep 2952035 = 4428053) B4428053
theorem B1968995 : Blo 1311974 1968995 := bstep (se 1 (by rfl) ⟨1476746, by rfl⟩ : syracuseStep 1968995 = 2953493) B2953493
theorem B1313635 : Blo 1311974 1313635 := bstep (se 1 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 1313635 = 1970453) B1970453
theorem B2214769 : Blo 1311974 2214769 := bstep (se 2 (by rfl) ⟨830538, by rfl⟩ : syracuseStep 2214769 = 1661077) B1661077
theorem B1313651 : Blo 1311974 1313651 := bstep (se 1 (by rfl) ⟨985238, by rfl⟩ : syracuseStep 1313651 = 1970477) B1970477
theorem B1870705 : Blo 1311974 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B1969025 : Blo 1311974 1969025 := bstep (se 2 (by rfl) ⟨738384, by rfl⟩ : syracuseStep 1969025 = 1476769) B1476769
theorem B1477507 : Blo 1311974 1477507 := bstep (se 1 (by rfl) ⟨1108130, by rfl⟩ : syracuseStep 1477507 = 2216261) B2216261
theorem B1313667 : Blo 1311974 1313667 := bstep (se 1 (by rfl) ⟨985250, by rfl⟩ : syracuseStep 1313667 = 1970501) B1970501
theorem B2214803 : Blo 1311974 2214803 := bstep (se 1 (by rfl) ⟨1661102, by rfl⟩ : syracuseStep 2214803 = 3322205) B3322205
theorem B1969043 : Blo 1311974 1969043 := bstep (se 1 (by rfl) ⟨1476782, by rfl⟩ : syracuseStep 1969043 = 2953565) B2953565
theorem B1313683 : Blo 1311974 1313683 := bstep (se 1 (by rfl) ⟨985262, by rfl⟩ : syracuseStep 1313683 = 1970525) B1970525
theorem B1313699 : Blo 1311974 1313699 := bstep (se 1 (by rfl) ⟨985274, by rfl⟩ : syracuseStep 1313699 = 1970549) B1970549
theorem B1969073 : Blo 1311974 1969073 := bstep (se 2 (by rfl) ⟨738402, by rfl⟩ : syracuseStep 1969073 = 1476805) B1476805
theorem B1313715 : Blo 1311974 1313715 := bstep (se 1 (by rfl) ⟨985286, by rfl⟩ : syracuseStep 1313715 = 1970573) B1970573
theorem B1969091 : Blo 1311974 1969091 := bstep (se 1 (by rfl) ⟨1476818, by rfl⟩ : syracuseStep 1969091 = 2953637) B2953637
theorem B1313731 : Blo 1311974 1313731 := bstep (se 1 (by rfl) ⟨985298, by rfl⟩ : syracuseStep 1313731 = 1970597) B1970597
theorem B3156931 : Blo 1311974 3156931 := bstep (se 1 (by rfl) ⟨2367698, by rfl⟩ : syracuseStep 3156931 = 4735397) B4735397
theorem B1313747 : Blo 1311974 1313747 := bstep (se 1 (by rfl) ⟨985310, by rfl⟩ : syracuseStep 1313747 = 1970621) B1970621
theorem B1969121 : Blo 1311974 1969121 := bstep (se 2 (by rfl) ⟨738420, by rfl⟩ : syracuseStep 1969121 = 1476841) B1476841
theorem B1313763 : Blo 1311974 1313763 := bstep (se 1 (by rfl) ⟨985322, by rfl⟩ : syracuseStep 1313763 = 1970645) B1970645
theorem B1969139 : Blo 1311974 1969139 := bstep (se 1 (by rfl) ⟨1476854, by rfl⟩ : syracuseStep 1969139 = 2953709) B2953709
theorem B1313779 : Blo 1311974 1313779 := bstep (se 1 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 1313779 = 1970669) B1970669
theorem B1313795 : Blo 1311974 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B1969169 : Blo 1311974 1969169 := bstep (se 2 (by rfl) ⟨738438, by rfl⟩ : syracuseStep 1969169 = 1476877) B1476877
theorem B2214931 : Blo 1311974 2214931 := bstep (se 1 (by rfl) ⟨1661198, by rfl⟩ : syracuseStep 2214931 = 3322397) B3322397
theorem B1477651 : Blo 1311974 1477651 := bstep (se 1 (by rfl) ⟨1108238, by rfl⟩ : syracuseStep 1477651 = 2216477) B2216477
theorem B1313811 : Blo 1311974 1313811 := bstep (se 1 (by rfl) ⟨985358, by rfl⟩ : syracuseStep 1313811 = 1970717) B1970717
theorem B1969187 : Blo 1311974 1969187 := bstep (se 1 (by rfl) ⟨1476890, by rfl⟩ : syracuseStep 1969187 = 2953781) B2953781
theorem B1313827 : Blo 1311974 1313827 := bstep (se 1 (by rfl) ⟨985370, by rfl⟩ : syracuseStep 1313827 = 1970741) B1970741
theorem B1313843 : Blo 1311974 1313843 := bstep (se 1 (by rfl) ⟨985382, by rfl⟩ : syracuseStep 1313843 = 1970765) B1970765
theorem B1969217 : Blo 1311974 1969217 := bstep (se 2 (by rfl) ⟨738456, by rfl⟩ : syracuseStep 1969217 = 1476913) B1476913
theorem B1313859 : Blo 1311974 1313859 := bstep (se 1 (by rfl) ⟨985394, by rfl⟩ : syracuseStep 1313859 = 1970789) B1970789
theorem B1969235 : Blo 1311974 1969235 := bstep (se 1 (by rfl) ⟨1476926, by rfl⟩ : syracuseStep 1969235 = 2953853) B2953853
theorem B1313875 : Blo 1311974 1313875 := bstep (se 1 (by rfl) ⟨985406, by rfl⟩ : syracuseStep 1313875 = 1970813) B1970813
theorem B1313891 : Blo 1311974 1313891 := bstep (se 1 (by rfl) ⟨985418, by rfl⟩ : syracuseStep 1313891 = 1970837) B1970837
theorem B2952305 : Blo 1311974 2952305 := bstep (se 2 (by rfl) ⟨1107114, by rfl⟩ : syracuseStep 2952305 = 2214229) B2214229
theorem B1969265 : Blo 1311974 1969265 := bstep (se 2 (by rfl) ⟨738474, by rfl⟩ : syracuseStep 1969265 = 1476949) B1476949
theorem B1313907 : Blo 1311974 1313907 := bstep (se 1 (by rfl) ⟨985430, by rfl⟩ : syracuseStep 1313907 = 1970861) B1970861
theorem B2952323 : Blo 1311974 2952323 := bstep (se 1 (by rfl) ⟨2214242, by rfl⟩ : syracuseStep 2952323 = 4428485) B4428485
theorem B1969283 : Blo 1311974 1969283 := bstep (se 1 (by rfl) ⟨1476962, by rfl⟩ : syracuseStep 1969283 = 2953925) B2953925
theorem B1313923 : Blo 1311974 1313923 := bstep (se 1 (by rfl) ⟨985442, by rfl⟩ : syracuseStep 1313923 = 1970885) B1970885
theorem B1313939 : Blo 1311974 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B2215073 : Blo 1311974 2215073 := bstep (se 2 (by rfl) ⟨830652, by rfl⟩ : syracuseStep 2215073 = 1661305) B1661305
theorem B1969313 : Blo 1311974 1969313 := bstep (se 2 (by rfl) ⟨738492, by rfl⟩ : syracuseStep 1969313 = 1476985) B1476985
theorem B1477795 : Blo 1311974 1477795 := bstep (se 1 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 1477795 = 2216693) B2216693
theorem B1313955 : Blo 1311974 1313955 := bstep (se 1 (by rfl) ⟨985466, by rfl⟩ : syracuseStep 1313955 = 1970933) B1970933
theorem B4730033 : Blo 1311974 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B1969331 : Blo 1311974 1969331 := bstep (se 1 (by rfl) ⟨1476998, by rfl⟩ : syracuseStep 1969331 = 2953997) B2953997
theorem B1313971 : Blo 1311974 1313971 := bstep (se 1 (by rfl) ⟨985478, by rfl⟩ : syracuseStep 1313971 = 1970957) B1970957
theorem B1969361 : Blo 1311974 1969361 := bstep (se 2 (by rfl) ⟨738510, by rfl⟩ : syracuseStep 1969361 = 1477021) B1477021
theorem B1969379 : Blo 1311974 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B1969409 : Blo 1311974 1969409 := bstep (se 2 (by rfl) ⟨738528, by rfl⟩ : syracuseStep 1969409 = 1477057) B1477057
theorem B1969427 : Blo 1311974 1969427 := bstep (se 1 (by rfl) ⟨1477070, by rfl⟩ : syracuseStep 1969427 = 2954141) B2954141
theorem B2215201 : Blo 1311974 2215201 := bstep (se 2 (by rfl) ⟨830700, by rfl⟩ : syracuseStep 2215201 = 1661401) B1661401
theorem B1969457 : Blo 1311974 1969457 := bstep (se 2 (by rfl) ⟨738546, by rfl⟩ : syracuseStep 1969457 = 1477093) B1477093
theorem B1477939 : Blo 1311974 1477939 := bstep (se 1 (by rfl) ⟨1108454, by rfl⟩ : syracuseStep 1477939 = 2216909) B2216909
theorem B2215235 : Blo 1311974 2215235 := bstep (se 1 (by rfl) ⟨1661426, by rfl⟩ : syracuseStep 2215235 = 3322853) B3322853
theorem B1969475 : Blo 1311974 1969475 := bstep (se 1 (by rfl) ⟨1477106, by rfl⟩ : syracuseStep 1969475 = 2954213) B2954213
theorem B1969505 : Blo 1311974 1969505 := bstep (se 2 (by rfl) ⟨738564, by rfl⟩ : syracuseStep 1969505 = 1477129) B1477129
theorem B1969523 : Blo 1311974 1969523 := bstep (se 1 (by rfl) ⟨1477142, by rfl⟩ : syracuseStep 1969523 = 2954285) B2954285
theorem B3321233 : Blo 1311974 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B2952593 : Blo 1311974 2952593 := bstep (se 2 (by rfl) ⟨1107222, by rfl⟩ : syracuseStep 2952593 = 2214445) B2214445
theorem B1969553 : Blo 1311974 1969553 := bstep (se 2 (by rfl) ⟨738582, by rfl⟩ : syracuseStep 1969553 = 1477165) B1477165
theorem B2493841 : Blo 1311974 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B2952611 : Blo 1311974 2952611 := bstep (se 1 (by rfl) ⟨2214458, by rfl⟩ : syracuseStep 2952611 = 4428917) B4428917
theorem B1969571 : Blo 1311974 1969571 := bstep (se 1 (by rfl) ⟨1477178, by rfl⟩ : syracuseStep 1969571 = 2954357) B2954357
theorem B1969601 : Blo 1311974 1969601 := bstep (se 2 (by rfl) ⟨738600, by rfl⟩ : syracuseStep 1969601 = 1477201) B1477201
theorem B3321283 : Blo 1311974 3321283 := bstep (se 1 (by rfl) ⟨2490962, by rfl⟩ : syracuseStep 3321283 = 4981925) B4981925
theorem B2215363 : Blo 1311974 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B33631685 : Blo 1311974 33631685 := bstep (se 4 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 33631685 = 6305941) B6305941
theorem B2805187 : Blo 1311974 2805187 := bstep (se 1 (by rfl) ⟨2103890, by rfl⟩ : syracuseStep 2805187 = 4207781) B4207781
theorem B1478083 : Blo 1311974 1478083 := bstep (se 1 (by rfl) ⟨1108562, by rfl⟩ : syracuseStep 1478083 = 2217125) B2217125
theorem B1969619 : Blo 1311974 1969619 := bstep (se 1 (by rfl) ⟨1477214, by rfl⟩ : syracuseStep 1969619 = 2954429) B2954429
theorem B1969649 : Blo 1311974 1969649 := bstep (se 2 (by rfl) ⟨738618, by rfl⟩ : syracuseStep 1969649 = 1477237) B1477237
theorem B1969667 : Blo 1311974 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B1969697 : Blo 1311974 1969697 := bstep (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) B1477273
theorem B4984355 : Blo 1311974 4984355 := bstep (se 1 (by rfl) ⟨3738266, by rfl⟩ : syracuseStep 4984355 = 7476533) B7476533
theorem B6647345 : Blo 1311974 6647345 := bstep (se 2 (by rfl) ⟨2492754, by rfl⟩ : syracuseStep 6647345 = 4985509) B4985509
theorem B1969715 : Blo 1311974 1969715 := bstep (se 1 (by rfl) ⟨1477286, by rfl⟩ : syracuseStep 1969715 = 2954573) B2954573
theorem B3321425 : Blo 1311974 3321425 := bstep (se 2 (by rfl) ⟨1245534, by rfl⟩ : syracuseStep 3321425 = 2491069) B2491069
theorem B2215505 : Blo 1311974 2215505 := bstep (se 2 (by rfl) ⟨830814, by rfl⟩ : syracuseStep 2215505 = 1661629) B1661629
theorem B1969745 : Blo 1311974 1969745 := bstep (se 2 (by rfl) ⟨738654, by rfl⟩ : syracuseStep 1969745 = 1477309) B1477309
theorem B1969763 : Blo 1311974 1969763 := bstep (se 1 (by rfl) ⟨1477322, by rfl⟩ : syracuseStep 1969763 = 2954645) B2954645
theorem B7474801 : Blo 1311974 7474801 := bstep (se 2 (by rfl) ⟨2803050, by rfl⟩ : syracuseStep 7474801 = 5606101) B5606101
theorem B1969793 : Blo 1311974 1969793 := bstep (se 2 (by rfl) ⟨738672, by rfl⟩ : syracuseStep 1969793 = 1477345) B1477345
theorem B1969811 : Blo 1311974 1969811 := bstep (se 1 (by rfl) ⟨1477358, by rfl⟩ : syracuseStep 1969811 = 2954717) B2954717
theorem B2952881 : Blo 1311974 2952881 := bstep (se 2 (by rfl) ⟨1107330, by rfl⟩ : syracuseStep 2952881 = 2214661) B2214661
theorem B1969841 : Blo 1311974 1969841 := bstep (se 2 (by rfl) ⟨738690, by rfl⟩ : syracuseStep 1969841 = 1477381) B1477381
theorem B2952899 : Blo 1311974 2952899 := bstep (se 1 (by rfl) ⟨2214674, by rfl⟩ : syracuseStep 2952899 = 4429349) B4429349
theorem B1969859 : Blo 1311974 1969859 := bstep (se 1 (by rfl) ⟨1477394, by rfl⟩ : syracuseStep 1969859 = 2954789) B2954789
theorem B2805443 : Blo 1311974 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B5992141 : Blo 1311974 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B2215633 : Blo 1311974 2215633 := bstep (se 2 (by rfl) ⟨830862, by rfl⟩ : syracuseStep 2215633 = 1661725) B1661725
theorem B1969889 : Blo 1311974 1969889 := bstep (se 2 (by rfl) ⟨738708, by rfl⟩ : syracuseStep 1969889 = 1477417) B1477417
theorem B2215667 : Blo 1311974 2215667 := bstep (se 1 (by rfl) ⟨1661750, by rfl⟩ : syracuseStep 2215667 = 3323501) B3323501
theorem B1969907 : Blo 1311974 1969907 := bstep (se 1 (by rfl) ⟨1477430, by rfl⟩ : syracuseStep 1969907 = 2954861) B2954861
theorem B1969937 : Blo 1311974 1969937 := bstep (se 2 (by rfl) ⟨738726, by rfl⟩ : syracuseStep 1969937 = 1477453) B1477453
theorem B1969955 : Blo 1311974 1969955 := bstep (se 1 (by rfl) ⟨1477466, by rfl⟩ : syracuseStep 1969955 = 2954933) B2954933
theorem B2494243 : Blo 1311974 2494243 := bstep (se 1 (by rfl) ⟨1870682, by rfl⟩ : syracuseStep 2494243 = 3741365) B3741365
theorem B1969985 : Blo 1311974 1969985 := bstep (se 2 (by rfl) ⟨738744, by rfl⟩ : syracuseStep 1969985 = 1477489) B1477489
theorem B2494289 : Blo 1311974 2494289 := bstep (se 2 (by rfl) ⟨935358, by rfl⟩ : syracuseStep 2494289 = 1870717) B1870717
theorem B1970003 : Blo 1311974 1970003 := bstep (se 1 (by rfl) ⟨1477502, by rfl⟩ : syracuseStep 1970003 = 2955005) B2955005
theorem B1970033 : Blo 1311974 1970033 := bstep (se 2 (by rfl) ⟨738762, by rfl⟩ : syracuseStep 1970033 = 1477525) B1477525
theorem B2215795 : Blo 1311974 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B1970051 : Blo 1311974 1970051 := bstep (se 1 (by rfl) ⟨1477538, by rfl⟩ : syracuseStep 1970051 = 2955077) B2955077
theorem B15150989 : Blo 1311974 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B14585741 : Blo 1311974 14585741 := bstep (se 3 (by rfl) ⟨2734826, by rfl⟩ : syracuseStep 14585741 = 5469653) B5469653
theorem B1970081 : Blo 1311974 1970081 := bstep (se 2 (by rfl) ⟨738780, by rfl⟩ : syracuseStep 1970081 = 1477561) B1477561
theorem B1970099 : Blo 1311974 1970099 := bstep (se 1 (by rfl) ⟨1477574, by rfl⟩ : syracuseStep 1970099 = 2955149) B2955149
theorem B2953169 : Blo 1311974 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B1970129 : Blo 1311974 1970129 := bstep (se 2 (by rfl) ⟨738798, by rfl⟩ : syracuseStep 1970129 = 1477597) B1477597
theorem B2953187 : Blo 1311974 2953187 := bstep (se 1 (by rfl) ⟨2214890, by rfl⟩ : syracuseStep 2953187 = 4429781) B4429781
theorem B1970147 : Blo 1311974 1970147 := bstep (se 1 (by rfl) ⟨1477610, by rfl⟩ : syracuseStep 1970147 = 2955221) B2955221
theorem B2215937 : Blo 1311974 2215937 := bstep (se 2 (by rfl) ⟨830976, by rfl⟩ : syracuseStep 2215937 = 1661953) B1661953
theorem B1970177 : Blo 1311974 1970177 := bstep (se 2 (by rfl) ⟨738816, by rfl⟩ : syracuseStep 1970177 = 1477633) B1477633
theorem B1970195 : Blo 1311974 1970195 := bstep (se 1 (by rfl) ⟨1477646, by rfl⟩ : syracuseStep 1970195 = 2955293) B2955293
theorem B1970225 : Blo 1311974 1970225 := bstep (se 2 (by rfl) ⟨738834, by rfl⟩ : syracuseStep 1970225 = 1477669) B1477669
theorem B1970243 : Blo 1311974 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B4730957 : Blo 1311974 4730957 := bstep (se 3 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 4730957 = 1774109) B1774109
theorem B1970273 : Blo 1311974 1970273 := bstep (se 2 (by rfl) ⟨738852, by rfl⟩ : syracuseStep 1970273 = 1477705) B1477705
theorem B1970291 : Blo 1311974 1970291 := bstep (se 1 (by rfl) ⟨1477718, by rfl⟩ : syracuseStep 1970291 = 2955437) B2955437
theorem B2216065 : Blo 1311974 2216065 := bstep (se 2 (by rfl) ⟨831024, by rfl⟩ : syracuseStep 2216065 = 1662049) B1662049
theorem B16830605 : Blo 1311974 16830605 := bstep (se 3 (by rfl) ⟨3155738, by rfl⟩ : syracuseStep 16830605 = 6311477) B6311477
theorem B6312077 : Blo 1311974 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B1970321 : Blo 1311974 1970321 := bstep (se 2 (by rfl) ⟨738870, by rfl⟩ : syracuseStep 1970321 = 1477741) B1477741
theorem B4206755 : Blo 1311974 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B2216099 : Blo 1311974 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B1970339 : Blo 1311974 1970339 := bstep (se 1 (by rfl) ⟨1477754, by rfl⟩ : syracuseStep 1970339 = 2955509) B2955509
theorem B4985009 : Blo 1311974 4985009 := bstep (se 2 (by rfl) ⟨1869378, by rfl⟩ : syracuseStep 4985009 = 3738757) B3738757
theorem B1970369 : Blo 1311974 1970369 := bstep (se 2 (by rfl) ⟨738888, by rfl⟩ : syracuseStep 1970369 = 1477777) B1477777
theorem B1970387 : Blo 1311974 1970387 := bstep (se 1 (by rfl) ⟨1477790, by rfl⟩ : syracuseStep 1970387 = 2955581) B2955581
theorem B2953457 : Blo 1311974 2953457 := bstep (se 2 (by rfl) ⟨1107546, by rfl⟩ : syracuseStep 2953457 = 2215093) B2215093
theorem B1970417 : Blo 1311974 1970417 := bstep (se 2 (by rfl) ⟨738906, by rfl⟩ : syracuseStep 1970417 = 1477813) B1477813
theorem B2953475 : Blo 1311974 2953475 := bstep (se 1 (by rfl) ⟨2215106, by rfl⟩ : syracuseStep 2953475 = 4430213) B4430213
theorem B3739907 : Blo 1311974 3739907 := bstep (se 1 (by rfl) ⟨2804930, by rfl⟩ : syracuseStep 3739907 = 5609861) B5609861
theorem B1970435 : Blo 1311974 1970435 := bstep (se 1 (by rfl) ⟨1477826, by rfl⟩ : syracuseStep 1970435 = 2955653) B2955653
theorem B1970465 : Blo 1311974 1970465 := bstep (se 2 (by rfl) ⟨738924, by rfl⟩ : syracuseStep 1970465 = 1477849) B1477849
theorem B2216227 : Blo 1311974 2216227 := bstep (se 1 (by rfl) ⟨1662170, by rfl⟩ : syracuseStep 2216227 = 3324341) B3324341
theorem B1970483 : Blo 1311974 1970483 := bstep (se 1 (by rfl) ⟨1477862, by rfl⟩ : syracuseStep 1970483 = 2955725) B2955725
theorem B2396483 : Blo 1311974 2396483 := bstep (se 1 (by rfl) ⟨1797362, by rfl⟩ : syracuseStep 2396483 = 3594725) B3594725
theorem B1970513 : Blo 1311974 1970513 := bstep (se 2 (by rfl) ⟨738942, by rfl⟩ : syracuseStep 1970513 = 1477885) B1477885
theorem B1970531 : Blo 1311974 1970531 := bstep (se 1 (by rfl) ⟨1477898, by rfl⟩ : syracuseStep 1970531 = 2955797) B2955797
theorem B1970561 : Blo 1311974 1970561 := bstep (se 2 (by rfl) ⟨738960, by rfl⟩ : syracuseStep 1970561 = 1477921) B1477921
theorem B1970579 : Blo 1311974 1970579 := bstep (se 1 (by rfl) ⟨1477934, by rfl⟩ : syracuseStep 1970579 = 2955869) B2955869
theorem B2216369 : Blo 1311974 2216369 := bstep (se 2 (by rfl) ⟨831138, by rfl⟩ : syracuseStep 2216369 = 1662277) B1662277
theorem B1970609 : Blo 1311974 1970609 := bstep (se 2 (by rfl) ⟨738978, by rfl⟩ : syracuseStep 1970609 = 1477957) B1477957
theorem B1970627 : Blo 1311974 1970627 := bstep (se 1 (by rfl) ⟨1477970, by rfl⟩ : syracuseStep 1970627 = 2955941) B2955941
theorem B22434245 : Blo 1311974 22434245 := bstep (se 4 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 22434245 = 4206421) B4206421
theorem B1970657 : Blo 1311974 1970657 := bstep (se 2 (by rfl) ⟨738996, by rfl⟩ : syracuseStep 1970657 = 1477993) B1477993
theorem B4428269 : Blo 1311974 4428269 := bstep (se 3 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 4428269 = 1660601) B1660601
theorem B1970675 : Blo 1311974 1970675 := bstep (se 1 (by rfl) ⟨1478006, by rfl⟩ : syracuseStep 1970675 = 2956013) B2956013
theorem B2953745 : Blo 1311974 2953745 := bstep (se 2 (by rfl) ⟨1107654, by rfl⟩ : syracuseStep 2953745 = 2215309) B2215309
theorem B1970705 : Blo 1311974 1970705 := bstep (se 2 (by rfl) ⟨739014, by rfl⟩ : syracuseStep 1970705 = 1478029) B1478029
theorem B4428323 : Blo 1311974 4428323 := bstep (se 1 (by rfl) ⟨3321242, by rfl⟩ : syracuseStep 4428323 = 6642485) B6642485
theorem B2953763 : Blo 1311974 2953763 := bstep (se 1 (by rfl) ⟨2215322, by rfl⟩ : syracuseStep 2953763 = 4430645) B4430645
theorem B1970723 : Blo 1311974 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B3322417 : Blo 1311974 3322417 := bstep (se 2 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 3322417 = 2491813) B2491813
theorem B2216497 : Blo 1311974 2216497 := bstep (se 2 (by rfl) ⟨831186, by rfl⟩ : syracuseStep 2216497 = 1662373) B1662373
theorem B1970753 : Blo 1311974 1970753 := bstep (se 2 (by rfl) ⟨739032, by rfl⟩ : syracuseStep 1970753 = 1478065) B1478065
theorem B2216531 : Blo 1311974 2216531 := bstep (se 1 (by rfl) ⟨1662398, by rfl⟩ : syracuseStep 2216531 = 3324797) B3324797
theorem B1970771 : Blo 1311974 1970771 := bstep (se 1 (by rfl) ⟨1478078, by rfl⟩ : syracuseStep 1970771 = 2956157) B2956157
theorem B56750705 : Blo 1311974 56750705 := bstep (se 2 (by rfl) ⟨21281514, by rfl⟩ : syracuseStep 56750705 = 42563029) B42563029
theorem B1970801 : Blo 1311974 1970801 := bstep (se 2 (by rfl) ⟨739050, by rfl⟩ : syracuseStep 1970801 = 1478101) B1478101
theorem B1970819 : Blo 1311974 1970819 := bstep (se 1 (by rfl) ⟨1478114, by rfl⟩ : syracuseStep 1970819 = 2956229) B2956229
theorem B1970849 : Blo 1311974 1970849 := bstep (se 2 (by rfl) ⟨739068, by rfl⟩ : syracuseStep 1970849 = 1478137) B1478137
theorem B8417969 : Blo 1311974 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B1970867 : Blo 1311974 1970867 := bstep (se 1 (by rfl) ⟨1478150, by rfl⟩ : syracuseStep 1970867 = 2956301) B2956301
theorem B2101955 : Blo 1311974 2101955 := bstep (se 1 (by rfl) ⟨1576466, by rfl⟩ : syracuseStep 2101955 = 3152933) B3152933
theorem B1970897 : Blo 1311974 1970897 := bstep (se 2 (by rfl) ⟨739086, by rfl⟩ : syracuseStep 1970897 = 1478173) B1478173
theorem B2216659 : Blo 1311974 2216659 := bstep (se 1 (by rfl) ⟨1662494, by rfl⟩ : syracuseStep 2216659 = 3324989) B3324989
theorem B1970915 : Blo 1311974 1970915 := bstep (se 1 (by rfl) ⟨1478186, by rfl⟩ : syracuseStep 1970915 = 2956373) B2956373
theorem B7688945 : Blo 1311974 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1970945 : Blo 1311974 1970945 := bstep (se 2 (by rfl) ⟨739104, by rfl⟩ : syracuseStep 1970945 = 1478209) B1478209
theorem B4428593 : Blo 1311974 4428593 := bstep (se 2 (by rfl) ⟨1660722, by rfl⟩ : syracuseStep 4428593 = 3321445) B3321445
theorem B2954033 : Blo 1311974 2954033 := bstep (se 2 (by rfl) ⟨1107762, by rfl⟩ : syracuseStep 2954033 = 2215525) B2215525
theorem B3322691 : Blo 1311974 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B2954051 : Blo 1311974 2954051 := bstep (se 1 (by rfl) ⟨2215538, by rfl⟩ : syracuseStep 2954051 = 4431077) B4431077
theorem B2216801 : Blo 1311974 2216801 := bstep (se 2 (by rfl) ⟨831300, by rfl⟩ : syracuseStep 2216801 = 1662601) B1662601
theorem B1577827 : Blo 1311974 1577827 := bstep (se 1 (by rfl) ⟨1183370, by rfl⟩ : syracuseStep 1577827 = 2366741) B2366741
theorem B2102129 : Blo 1311974 2102129 := bstep (se 2 (by rfl) ⟨788298, by rfl⟩ : syracuseStep 2102129 = 1576597) B1576597
theorem B2216929 : Blo 1311974 2216929 := bstep (se 2 (by rfl) ⟨831348, by rfl⟩ : syracuseStep 2216929 = 1662697) B1662697
theorem B6648803 : Blo 1311974 6648803 := bstep (se 1 (by rfl) ⟨4986602, by rfl⟩ : syracuseStep 6648803 = 9973205) B9973205
theorem B4207601 : Blo 1311974 4207601 := bstep (se 2 (by rfl) ⟨1577850, by rfl⟩ : syracuseStep 4207601 = 3155701) B3155701
theorem B3322883 : Blo 1311974 3322883 := bstep (se 1 (by rfl) ⟨2492162, by rfl⟩ : syracuseStep 3322883 = 4984325) B4984325
theorem B2216963 : Blo 1311974 2216963 := bstep (se 1 (by rfl) ⟨1662722, by rfl⟩ : syracuseStep 2216963 = 3325445) B3325445
theorem B7476259 : Blo 1311974 7476259 := bstep (se 1 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 7476259 = 11214389) B11214389
theorem B7189573 : Blo 1311974 7189573 := bstep (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) B1348045
theorem B2954321 : Blo 1311974 2954321 := bstep (se 2 (by rfl) ⟨1107870, by rfl⟩ : syracuseStep 2954321 = 2215741) B2215741
theorem B5608547 : Blo 1311974 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B2954339 : Blo 1311974 2954339 := bstep (se 1 (by rfl) ⟨2215754, by rfl⟩ : syracuseStep 2954339 = 4431509) B4431509
theorem B2217091 : Blo 1311974 2217091 := bstep (se 1 (by rfl) ⟨1662818, by rfl⟩ : syracuseStep 2217091 = 3325637) B3325637
theorem B1774801 : Blo 1311974 1774801 := bstep (se 2 (by rfl) ⟨665550, by rfl⟩ : syracuseStep 1774801 = 1331101) B1331101
theorem B2364643 : Blo 1311974 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B2217233 : Blo 1311974 2217233 := bstep (se 2 (by rfl) ⟨831462, by rfl⟩ : syracuseStep 2217233 = 1662925) B1662925
theorem B1774867 : Blo 1311974 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B4429133 : Blo 1311974 4429133 := bstep (se 3 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 4429133 = 1660925) B1660925
theorem B2954609 : Blo 1311974 2954609 := bstep (se 2 (by rfl) ⟨1107978, by rfl⟩ : syracuseStep 2954609 = 2215957) B2215957
theorem B4429187 : Blo 1311974 4429187 := bstep (se 1 (by rfl) ⟨3321890, by rfl⟩ : syracuseStep 4429187 = 6643781) B6643781
theorem B2954627 : Blo 1311974 2954627 := bstep (se 1 (by rfl) ⟨2215970, by rfl⟩ : syracuseStep 2954627 = 4431941) B4431941
theorem B25228685 : Blo 1311974 25228685 := bstep (se 3 (by rfl) ⟨4730378, by rfl⟩ : syracuseStep 25228685 = 9460757) B9460757
theorem B2995633 : Blo 1311974 2995633 := bstep (se 2 (by rfl) ⟨1123362, by rfl⟩ : syracuseStep 2995633 = 2246725) B2246725
theorem B3741137 : Blo 1311974 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B5682659 : Blo 1311974 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B7476785 : Blo 1311974 7476785 := bstep (se 2 (by rfl) ⟨2803794, by rfl⟩ : syracuseStep 7476785 = 5607589) B5607589
theorem B4986467 : Blo 1311974 4986467 := bstep (se 1 (by rfl) ⟨3739850, by rfl⟩ : syracuseStep 4986467 = 7479701) B7479701
theorem B4986481 : Blo 1311974 4986481 := bstep (se 2 (by rfl) ⟨1869930, by rfl⟩ : syracuseStep 4986481 = 3739861) B3739861
theorem B4429457 : Blo 1311974 4429457 := bstep (se 2 (by rfl) ⟨1661046, by rfl⟩ : syracuseStep 4429457 = 3322093) B3322093
theorem B2954897 : Blo 1311974 2954897 := bstep (se 2 (by rfl) ⟨1108086, by rfl⟩ : syracuseStep 2954897 = 2216173) B2216173
theorem B2954915 : Blo 1311974 2954915 := bstep (se 1 (by rfl) ⟨2216186, by rfl⟩ : syracuseStep 2954915 = 4432373) B4432373
theorem B11220677 : Blo 1311974 11220677 := bstep (se 4 (by rfl) ⟨1051938, by rfl⟩ : syracuseStep 11220677 = 2103877) B2103877
theorem B1775363 : Blo 1311974 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B9967373 : Blo 1311974 9967373 := bstep (se 3 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 9967373 = 3737765) B3737765
theorem B6649613 : Blo 1311974 6649613 := bstep (se 3 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 6649613 = 2493605) B2493605
theorem B11212613 : Blo 1311974 11212613 := bstep (se 4 (by rfl) ⟨1051182, by rfl⟩ : syracuseStep 11212613 = 2102365) B2102365
theorem B2840465 : Blo 1311974 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B2398097 : Blo 1311974 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B1660819 : Blo 1311974 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B2660273 : Blo 1311974 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B3323825 : Blo 1311974 3323825 := bstep (se 2 (by rfl) ⟨1246434, by rfl⟩ : syracuseStep 3323825 = 2492869) B2492869
theorem B2955185 : Blo 1311974 2955185 := bstep (se 2 (by rfl) ⟨1108194, by rfl⟩ : syracuseStep 2955185 = 2216389) B2216389
theorem B2955203 : Blo 1311974 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B3323875 : Blo 1311974 3323875 := bstep (se 1 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 3323875 = 4985813) B4985813
theorem B1660915 : Blo 1311974 1660915 := bstep (se 1 (by rfl) ⟨1245686, by rfl⟩ : syracuseStep 1660915 = 2491373) B2491373
theorem B3324017 : Blo 1311974 3324017 := bstep (se 2 (by rfl) ⟨1246506, by rfl⟩ : syracuseStep 3324017 = 2493013) B2493013
theorem B4429997 : Blo 1311974 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B1775795 : Blo 1311974 1775795 := bstep (se 1 (by rfl) ⟨1331846, by rfl⟩ : syracuseStep 1775795 = 2663693) B2663693
theorem B2955473 : Blo 1311974 2955473 := bstep (se 2 (by rfl) ⟨1108302, by rfl⟩ : syracuseStep 2955473 = 2216605) B2216605
theorem B2660579 : Blo 1311974 2660579 := bstep (se 1 (by rfl) ⟨1995434, by rfl⟩ : syracuseStep 2660579 = 3990869) B3990869
theorem B4430051 : Blo 1311974 4430051 := bstep (se 1 (by rfl) ⟨3322538, by rfl⟩ : syracuseStep 4430051 = 6645077) B6645077
theorem B2955491 : Blo 1311974 2955491 := bstep (se 1 (by rfl) ⟨2216618, by rfl⟩ : syracuseStep 2955491 = 4433237) B4433237
theorem B11221361 : Blo 1311974 11221361 := bstep (se 2 (by rfl) ⟨4208010, by rfl⟩ : syracuseStep 11221361 = 8416021) B8416021
theorem B1661411 : Blo 1311974 1661411 := bstep (se 1 (by rfl) ⟨1246058, by rfl⟩ : syracuseStep 1661411 = 2492117) B2492117
theorem B1497571 : Blo 1311974 1497571 := bstep (se 1 (by rfl) ⟨1123178, by rfl⟩ : syracuseStep 1497571 = 2246357) B2246357
theorem B6642161 : Blo 1311974 6642161 := bstep (se 2 (by rfl) ⟨2490810, by rfl⟩ : syracuseStep 6642161 = 4981621) B4981621
theorem B4430321 : Blo 1311974 4430321 := bstep (se 2 (by rfl) ⟨1661370, by rfl⟩ : syracuseStep 4430321 = 3322741) B3322741
theorem B2955761 : Blo 1311974 2955761 := bstep (se 2 (by rfl) ⟨1108410, by rfl⟩ : syracuseStep 2955761 = 2216821) B2216821
theorem B2955779 : Blo 1311974 2955779 := bstep (se 1 (by rfl) ⟨2216834, by rfl⟩ : syracuseStep 2955779 = 4433669) B4433669
theorem B11983373 : Blo 1311974 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B1997345 : Blo 1311974 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B5323363 : Blo 1311974 5323363 := bstep (se 1 (by rfl) ⟨3992522, by rfl⟩ : syracuseStep 5323363 = 7985045) B7985045
theorem B4209421 : Blo 1311974 4209421 := bstep (se 3 (by rfl) ⟨789266, by rfl⟩ : syracuseStep 4209421 = 1578533) B1578533
theorem B2956049 : Blo 1311974 2956049 := bstep (se 2 (by rfl) ⟨1108518, by rfl⟩ : syracuseStep 2956049 = 2217037) B2217037
theorem B2956067 : Blo 1311974 2956067 := bstep (se 1 (by rfl) ⟨2217050, by rfl⟩ : syracuseStep 2956067 = 4434101) B4434101
theorem B2104147 : Blo 1311974 2104147 := bstep (se 1 (by rfl) ⟨1578110, by rfl⟩ : syracuseStep 2104147 = 3156221) B3156221
theorem B2104211 : Blo 1311974 2104211 := bstep (se 1 (by rfl) ⟨1578158, by rfl⟩ : syracuseStep 2104211 = 3156317) B3156317
theorem B7478243 : Blo 1311974 7478243 := bstep (se 1 (by rfl) ⟨5608682, by rfl⟩ : syracuseStep 7478243 = 11217365) B11217365
theorem B11238385 : Blo 1311974 11238385 := bstep (se 2 (by rfl) ⟨4214394, by rfl⟩ : syracuseStep 11238385 = 8428789) B8428789
theorem B4430861 : Blo 1311974 4430861 := bstep (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) B1661573
theorem B4987939 : Blo 1311974 4987939 := bstep (se 1 (by rfl) ⟨3740954, by rfl⟩ : syracuseStep 4987939 = 7481909) B7481909
theorem B5610545 : Blo 1311974 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B2956337 : Blo 1311974 2956337 := bstep (se 2 (by rfl) ⟨1108626, by rfl⟩ : syracuseStep 2956337 = 2217253) B2217253
theorem B14957621 : Blo 1311974 14957621 := bstep (se 5 (by rfl) ⟨701138, by rfl⟩ : syracuseStep 14957621 = 1402277) B1402277
theorem B4430915 : Blo 1311974 4430915 := bstep (se 1 (by rfl) ⟨3323186, by rfl⟩ : syracuseStep 4430915 = 6646373) B6646373
theorem B2956355 : Blo 1311974 2956355 := bstep (se 1 (by rfl) ⟨2217266, by rfl⟩ : syracuseStep 2956355 = 4434533) B4434533
theorem B2366545 : Blo 1311974 2366545 := bstep (se 2 (by rfl) ⟨887454, by rfl⟩ : syracuseStep 2366545 = 1774909) B1774909
theorem B3325009 : Blo 1311974 3325009 := bstep (se 2 (by rfl) ⟨1246878, by rfl⟩ : syracuseStep 3325009 = 2493757) B2493757
theorem B1662115 : Blo 1311974 1662115 := bstep (se 1 (by rfl) ⟨1246586, by rfl⟩ : syracuseStep 1662115 = 2493173) B2493173
theorem B2661617 : Blo 1311974 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B1662211 : Blo 1311974 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B4431185 : Blo 1311974 4431185 := bstep (se 2 (by rfl) ⟨1661694, by rfl⟩ : syracuseStep 4431185 = 3323389) B3323389
theorem B3325283 : Blo 1311974 3325283 := bstep (se 1 (by rfl) ⟨2493962, by rfl⟩ : syracuseStep 3325283 = 4987925) B4987925
theorem B3153347 : Blo 1311974 3153347 := bstep (se 1 (by rfl) ⟨2365010, by rfl⟩ : syracuseStep 3153347 = 4730021) B4730021
theorem B7200269 : Blo 1311974 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B3325475 : Blo 1311974 3325475 := bstep (se 1 (by rfl) ⟨2494106, by rfl⟩ : syracuseStep 3325475 = 4988213) B4988213
theorem B3546833 : Blo 1311974 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B1662707 : Blo 1311974 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B4431725 : Blo 1311974 4431725 := bstep (se 3 (by rfl) ⟨830948, by rfl⟩ : syracuseStep 4431725 = 1661897) B1661897
theorem B3153809 : Blo 1311974 3153809 := bstep (se 2 (by rfl) ⟨1182678, by rfl⟩ : syracuseStep 3153809 = 2365357) B2365357
theorem B6643619 : Blo 1311974 6643619 := bstep (se 1 (by rfl) ⟨4982714, by rfl⟩ : syracuseStep 6643619 = 9965429) B9965429
theorem B4431779 : Blo 1311974 4431779 := bstep (se 1 (by rfl) ⟨3323834, by rfl⟩ : syracuseStep 4431779 = 6647669) B6647669
theorem B11984867 : Blo 1311974 11984867 := bstep (se 1 (by rfl) ⟨8988650, by rfl⟩ : syracuseStep 11984867 = 17977301) B17977301
theorem B3153971 : Blo 1311974 3153971 := bstep (se 1 (by rfl) ⟨2365478, by rfl⟩ : syracuseStep 3153971 = 4730957) B4730957
theorem B22724813 : Blo 1311974 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B1597655 : Blo 1311974 1597655 := bstep (se 1 (by rfl) ⟨1198241, by rfl⟩ : syracuseStep 1597655 = 2396483) B2396483
theorem B5611979 : Blo 1311974 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B2490841 : Blo 1311974 2490841 := bstep (se 2 (by rfl) ⟨934065, by rfl⟩ : syracuseStep 2490841 = 1868131) B1868131
theorem B3736115 : Blo 1311974 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B1401419 : Blo 1311974 1401419 := bstep (se 1 (by rfl) ⟨1051064, by rfl⟩ : syracuseStep 1401419 = 2102129) B2102129
theorem B4432535 : Blo 1311974 4432535 := bstep (se 1 (by rfl) ⟨3324401, by rfl⟩ : syracuseStep 4432535 = 6648803) B6648803
theorem B8094481 : Blo 1311974 8094481 := bstep (se 2 (by rfl) ⟨3035430, by rfl⟩ : syracuseStep 8094481 = 6070861) B6070861
theorem B71918401 : Blo 1311974 71918401 := bstep (se 2 (by rfl) ⟨26969400, by rfl⟩ : syracuseStep 71918401 = 53938801) B53938801
theorem B16819123 : Blo 1311974 16819123 := bstep (se 1 (by rfl) ⟨12614342, by rfl⟩ : syracuseStep 16819123 = 25228685) B25228685
theorem B6644753 : Blo 1311974 6644753 := bstep (se 2 (by rfl) ⟨2491782, by rfl⟩ : syracuseStep 6644753 = 4983565) B4983565
theorem B5612561 : Blo 1311974 5612561 := bstep (se 2 (by rfl) ⟨2104710, by rfl⟩ : syracuseStep 5612561 = 4209421) B4209421
theorem B4555865 : Blo 1311974 4555865 := bstep (se 2 (by rfl) ⟨1708449, by rfl⟩ : syracuseStep 4555865 = 3416899) B3416899
theorem B7480451 : Blo 1311974 7480451 := bstep (se 1 (by rfl) ⟨5610338, by rfl⟩ : syracuseStep 7480451 = 11220677) B11220677
theorem B5604497 : Blo 1311974 5604497 := bstep (se 2 (by rfl) ⟨2101686, by rfl⟩ : syracuseStep 5604497 = 4203373) B4203373
theorem B1868951 : Blo 1311974 1868951 := bstep (se 1 (by rfl) ⟨1401713, by rfl⟩ : syracuseStep 1868951 = 2803427) B2803427
theorem B6644915 : Blo 1311974 6644915 := bstep (se 1 (by rfl) ⟨4983686, by rfl⟩ : syracuseStep 6644915 = 9967373) B9967373
theorem B4433075 : Blo 1311974 4433075 := bstep (se 1 (by rfl) ⟨3324806, by rfl⟩ : syracuseStep 4433075 = 6649613) B6649613
theorem B1311979 : Blo 1311974 1311979 := bstep (se 1 (by rfl) ⟨983984, by rfl⟩ : syracuseStep 1311979 = 1967969) B1967969
theorem B1311991 : Blo 1311974 1311991 := bstep (se 1 (by rfl) ⟨983993, by rfl⟩ : syracuseStep 1311991 = 1967987) B1967987
theorem B1312011 : Blo 1311974 1312011 := bstep (se 1 (by rfl) ⟨984008, by rfl⟩ : syracuseStep 1312011 = 1968017) B1968017
theorem B1312023 : Blo 1311974 1312023 := bstep (se 1 (by rfl) ⟨984017, by rfl⟩ : syracuseStep 1312023 = 1968035) B1968035
theorem B1312043 : Blo 1311974 1312043 := bstep (se 1 (by rfl) ⟨984032, by rfl⟩ : syracuseStep 1312043 = 1968065) B1968065
theorem B1312055 : Blo 1311974 1312055 := bstep (se 1 (by rfl) ⟨984041, by rfl⟩ : syracuseStep 1312055 = 1968083) B1968083
theorem B14984513 : Blo 1311974 14984513 := bstep (se 2 (by rfl) ⟨5619192, by rfl⟩ : syracuseStep 14984513 = 11238385) B11238385
theorem B1312075 : Blo 1311974 1312075 := bstep (se 1 (by rfl) ⟨984056, by rfl⟩ : syracuseStep 1312075 = 1968113) B1968113
theorem B1312087 : Blo 1311974 1312087 := bstep (se 1 (by rfl) ⟨984065, by rfl⟩ : syracuseStep 1312087 = 1968131) B1968131
theorem B1312107 : Blo 1311974 1312107 := bstep (se 1 (by rfl) ⟨984080, by rfl⟩ : syracuseStep 1312107 = 1968161) B1968161
theorem B1312119 : Blo 1311974 1312119 := bstep (se 1 (by rfl) ⟨984089, by rfl⟩ : syracuseStep 1312119 = 1968179) B1968179
theorem B1312139 : Blo 1311974 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B1312151 : Blo 1311974 1312151 := bstep (se 1 (by rfl) ⟨984113, by rfl⟩ : syracuseStep 1312151 = 1968227) B1968227
theorem B1312171 : Blo 1311974 1312171 := bstep (se 1 (by rfl) ⟨984128, by rfl⟩ : syracuseStep 1312171 = 1968257) B1968257
theorem B9586097 : Blo 1311974 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B1312183 : Blo 1311974 1312183 := bstep (se 1 (by rfl) ⟨984137, by rfl⟩ : syracuseStep 1312183 = 1968275) B1968275
theorem B3155393 : Blo 1311974 3155393 := bstep (se 2 (by rfl) ⟨1183272, by rfl⟩ : syracuseStep 3155393 = 2366545) B2366545
theorem B4433345 : Blo 1311974 4433345 := bstep (se 2 (by rfl) ⟨1662504, by rfl⟩ : syracuseStep 4433345 = 3325009) B3325009
theorem B1312203 : Blo 1311974 1312203 := bstep (se 1 (by rfl) ⟨984152, by rfl⟩ : syracuseStep 1312203 = 1968305) B1968305
theorem B1869259 : Blo 1311974 1869259 := bstep (se 1 (by rfl) ⟨1401944, by rfl⟩ : syracuseStep 1869259 = 2803889) B2803889
theorem B1312215 : Blo 1311974 1312215 := bstep (se 1 (by rfl) ⟨984161, by rfl⟩ : syracuseStep 1312215 = 1968323) B1968323
theorem B1312235 : Blo 1311974 1312235 := bstep (se 1 (by rfl) ⟨984176, by rfl⟩ : syracuseStep 1312235 = 1968353) B1968353
theorem B1312247 : Blo 1311974 1312247 := bstep (se 1 (by rfl) ⟨984185, by rfl⟩ : syracuseStep 1312247 = 1968371) B1968371
theorem B1312267 : Blo 1311974 1312267 := bstep (se 1 (by rfl) ⟨984200, by rfl⟩ : syracuseStep 1312267 = 1968401) B1968401
theorem B1312279 : Blo 1311974 1312279 := bstep (se 1 (by rfl) ⟨984209, by rfl⟩ : syracuseStep 1312279 = 1968419) B1968419
theorem B1476139 : Blo 1311974 1476139 := bstep (se 1 (by rfl) ⟨1107104, by rfl⟩ : syracuseStep 1476139 = 2214209) B2214209
theorem B1312299 : Blo 1311974 1312299 := bstep (se 1 (by rfl) ⟨984224, by rfl⟩ : syracuseStep 1312299 = 1968449) B1968449
theorem B1312311 : Blo 1311974 1312311 := bstep (se 1 (by rfl) ⟨984233, by rfl⟩ : syracuseStep 1312311 = 1968467) B1968467
theorem B1312331 : Blo 1311974 1312331 := bstep (se 1 (by rfl) ⟨984248, by rfl⟩ : syracuseStep 1312331 = 1968497) B1968497
theorem B7480907 : Blo 1311974 7480907 := bstep (se 1 (by rfl) ⟨5610680, by rfl⟩ : syracuseStep 7480907 = 11221361) B11221361
theorem B1312343 : Blo 1311974 1312343 := bstep (se 1 (by rfl) ⟨984257, by rfl⟩ : syracuseStep 1312343 = 1968515) B1968515
theorem B1312363 : Blo 1311974 1312363 := bstep (se 1 (by rfl) ⟨984272, by rfl⟩ : syracuseStep 1312363 = 1968545) B1968545
theorem B1312375 : Blo 1311974 1312375 := bstep (se 1 (by rfl) ⟨984281, by rfl⟩ : syracuseStep 1312375 = 1968563) B1968563
theorem B1312395 : Blo 1311974 1312395 := bstep (se 1 (by rfl) ⟨984296, by rfl⟩ : syracuseStep 1312395 = 1968593) B1968593
theorem B1476247 : Blo 1311974 1476247 := bstep (se 1 (by rfl) ⟨1107185, by rfl⟩ : syracuseStep 1476247 = 2214371) B2214371
theorem B1312407 : Blo 1311974 1312407 := bstep (se 1 (by rfl) ⟨984305, by rfl⟩ : syracuseStep 1312407 = 1968611) B1968611
theorem B1312427 : Blo 1311974 1312427 := bstep (se 1 (by rfl) ⟨984320, by rfl⟩ : syracuseStep 1312427 = 1968641) B1968641
theorem B7988915 : Blo 1311974 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B1312439 : Blo 1311974 1312439 := bstep (se 1 (by rfl) ⟨984329, by rfl⟩ : syracuseStep 1312439 = 1968659) B1968659
theorem B1312459 : Blo 1311974 1312459 := bstep (se 1 (by rfl) ⟨984344, by rfl⟩ : syracuseStep 1312459 = 1968689) B1968689
theorem B1312471 : Blo 1311974 1312471 := bstep (se 1 (by rfl) ⟨984353, by rfl⟩ : syracuseStep 1312471 = 1968707) B1968707
theorem B1312491 : Blo 1311974 1312491 := bstep (se 1 (by rfl) ⟨984368, by rfl⟩ : syracuseStep 1312491 = 1968737) B1968737
theorem B2492147 : Blo 1311974 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B1312503 : Blo 1311974 1312503 := bstep (se 1 (by rfl) ⟨984377, by rfl⟩ : syracuseStep 1312503 = 1968755) B1968755
theorem B1312523 : Blo 1311974 1312523 := bstep (se 1 (by rfl) ⟨984392, by rfl⟩ : syracuseStep 1312523 = 1968785) B1968785
theorem B1312535 : Blo 1311974 1312535 := bstep (se 1 (by rfl) ⟨984401, by rfl⟩ : syracuseStep 1312535 = 1968803) B1968803
theorem B1312555 : Blo 1311974 1312555 := bstep (se 1 (by rfl) ⟨984416, by rfl⟩ : syracuseStep 1312555 = 1968833) B1968833
theorem B4982579 : Blo 1311974 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B1312567 : Blo 1311974 1312567 := bstep (se 1 (by rfl) ⟨984425, by rfl⟩ : syracuseStep 1312567 = 1968851) B1968851
theorem B4982593 : Blo 1311974 4982593 := bstep (se 2 (by rfl) ⟨1868472, by rfl⟩ : syracuseStep 4982593 = 3736945) B3736945
theorem B1476427 : Blo 1311974 1476427 := bstep (se 1 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 1476427 = 2214641) B2214641
theorem B1312587 : Blo 1311974 1312587 := bstep (se 1 (by rfl) ⟨984440, by rfl⟩ : syracuseStep 1312587 = 1968881) B1968881
theorem B1312599 : Blo 1311974 1312599 := bstep (se 1 (by rfl) ⟨984449, by rfl⟩ : syracuseStep 1312599 = 1968899) B1968899
theorem B5605213 : Blo 1311974 5605213 := bstep (se 3 (by rfl) ⟨1050977, by rfl⟩ : syracuseStep 5605213 = 2101955) B2101955
theorem B1312619 : Blo 1311974 1312619 := bstep (se 1 (by rfl) ⟨984464, by rfl⟩ : syracuseStep 1312619 = 1968929) B1968929
theorem B18941813 : Blo 1311974 18941813 := bstep (se 5 (by rfl) ⟨887897, by rfl⟩ : syracuseStep 18941813 = 1775795) B1775795
theorem B1312631 : Blo 1311974 1312631 := bstep (se 1 (by rfl) ⟨984473, by rfl⟩ : syracuseStep 1312631 = 1968947) B1968947
theorem B1968011 : Blo 1311974 1968011 := bstep (se 1 (by rfl) ⟨1476008, by rfl⟩ : syracuseStep 1968011 = 2952017) B2952017
theorem B1312651 : Blo 1311974 1312651 := bstep (se 1 (by rfl) ⟨984488, by rfl⟩ : syracuseStep 1312651 = 1968977) B1968977
theorem B2492299 : Blo 1311974 2492299 := bstep (se 1 (by rfl) ⟨1869224, by rfl⟩ : syracuseStep 2492299 = 3738449) B3738449
theorem B1968023 : Blo 1311974 1968023 := bstep (se 1 (by rfl) ⟨1476017, by rfl⟩ : syracuseStep 1968023 = 2952035) B2952035
theorem B1312663 : Blo 1311974 1312663 := bstep (se 1 (by rfl) ⟨984497, by rfl⟩ : syracuseStep 1312663 = 1968995) B1968995
theorem B1312683 : Blo 1311974 1312683 := bstep (se 1 (by rfl) ⟨984512, by rfl⟩ : syracuseStep 1312683 = 1969025) B1969025
theorem B1476535 : Blo 1311974 1476535 := bstep (se 1 (by rfl) ⟨1107401, by rfl⟩ : syracuseStep 1476535 = 2214803) B2214803
theorem B1312695 : Blo 1311974 1312695 := bstep (se 1 (by rfl) ⟨984521, by rfl⟩ : syracuseStep 1312695 = 1969043) B1969043
theorem B1402807 : Blo 1311974 1402807 := bstep (se 1 (by rfl) ⟨1052105, by rfl⟩ : syracuseStep 1402807 = 2104211) B2104211
theorem B1312715 : Blo 1311974 1312715 := bstep (se 1 (by rfl) ⟨984536, by rfl⟩ : syracuseStep 1312715 = 1969073) B1969073
theorem B1312727 : Blo 1311974 1312727 := bstep (se 1 (by rfl) ⟨984545, by rfl⟩ : syracuseStep 1312727 = 1969091) B1969091
theorem B1968089 : Blo 1311974 1968089 := bstep (se 2 (by rfl) ⟨738033, by rfl⟩ : syracuseStep 1968089 = 1476067) B1476067
theorem B4433885 : Blo 1311974 4433885 := bstep (se 3 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 4433885 = 1662707) B1662707
theorem B1312747 : Blo 1311974 1312747 := bstep (se 1 (by rfl) ⟨984560, by rfl⟩ : syracuseStep 1312747 = 1969121) B1969121
theorem B1312759 : Blo 1311974 1312759 := bstep (se 1 (by rfl) ⟨984569, by rfl⟩ : syracuseStep 1312759 = 1969139) B1969139
theorem B1312779 : Blo 1311974 1312779 := bstep (se 1 (by rfl) ⟨984584, by rfl⟩ : syracuseStep 1312779 = 1969169) B1969169
theorem B1312791 : Blo 1311974 1312791 := bstep (se 1 (by rfl) ⟨984593, by rfl⟩ : syracuseStep 1312791 = 1969187) B1969187
theorem B9971747 : Blo 1311974 9971747 := bstep (se 1 (by rfl) ⟨7478810, by rfl⟩ : syracuseStep 9971747 = 14957621) B14957621
theorem B1312811 : Blo 1311974 1312811 := bstep (se 1 (by rfl) ⟨984608, by rfl⟩ : syracuseStep 1312811 = 1969217) B1969217
theorem B1312823 : Blo 1311974 1312823 := bstep (se 1 (by rfl) ⟨984617, by rfl⟩ : syracuseStep 1312823 = 1969235) B1969235
theorem B1968203 : Blo 1311974 1968203 := bstep (se 1 (by rfl) ⟨1476152, by rfl⟩ : syracuseStep 1968203 = 2952305) B2952305
theorem B1312843 : Blo 1311974 1312843 := bstep (se 1 (by rfl) ⟨984632, by rfl⟩ : syracuseStep 1312843 = 1969265) B1969265
theorem B1968215 : Blo 1311974 1968215 := bstep (se 1 (by rfl) ⟨1476161, by rfl⟩ : syracuseStep 1968215 = 2952323) B2952323
theorem B1312855 : Blo 1311974 1312855 := bstep (se 1 (by rfl) ⟨984641, by rfl⟩ : syracuseStep 1312855 = 1969283) B1969283
theorem B1476715 : Blo 1311974 1476715 := bstep (se 1 (by rfl) ⟨1107536, by rfl⟩ : syracuseStep 1476715 = 2215073) B2215073
theorem B1312875 : Blo 1311974 1312875 := bstep (se 1 (by rfl) ⟨984656, by rfl⟩ : syracuseStep 1312875 = 1969313) B1969313
theorem B1312887 : Blo 1311974 1312887 := bstep (se 1 (by rfl) ⟨984665, by rfl⟩ : syracuseStep 1312887 = 1969331) B1969331
theorem B1312907 : Blo 1311974 1312907 := bstep (se 1 (by rfl) ⟨984680, by rfl⟩ : syracuseStep 1312907 = 1969361) B1969361
theorem B1312919 : Blo 1311974 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B1968281 : Blo 1311974 1968281 := bstep (se 2 (by rfl) ⟨738105, by rfl⟩ : syracuseStep 1968281 = 1476211) B1476211
theorem B1312939 : Blo 1311974 1312939 := bstep (se 1 (by rfl) ⟨984704, by rfl⟩ : syracuseStep 1312939 = 1969409) B1969409
theorem B1312951 : Blo 1311974 1312951 := bstep (se 1 (by rfl) ⟨984713, by rfl⟩ : syracuseStep 1312951 = 1969427) B1969427
theorem B1312971 : Blo 1311974 1312971 := bstep (se 1 (by rfl) ⟨984728, by rfl⟩ : syracuseStep 1312971 = 1969457) B1969457
theorem B1476823 : Blo 1311974 1476823 := bstep (se 1 (by rfl) ⟨1107617, by rfl⟩ : syracuseStep 1476823 = 2215235) B2215235
theorem B1312983 : Blo 1311974 1312983 := bstep (se 1 (by rfl) ⟨984737, by rfl⟩ : syracuseStep 1312983 = 1969475) B1969475
theorem B2492633 : Blo 1311974 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B1313003 : Blo 1311974 1313003 := bstep (se 1 (by rfl) ⟨984752, by rfl⟩ : syracuseStep 1313003 = 1969505) B1969505
theorem B1313015 : Blo 1311974 1313015 := bstep (se 1 (by rfl) ⟨984761, by rfl⟩ : syracuseStep 1313015 = 1969523) B1969523
theorem B15976709 : Blo 1311974 15976709 := bstep (se 4 (by rfl) ⟨1497816, by rfl⟩ : syracuseStep 15976709 = 2995633) B2995633
theorem B2214155 : Blo 1311974 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B1968395 : Blo 1311974 1968395 := bstep (se 1 (by rfl) ⟨1476296, by rfl⟩ : syracuseStep 1968395 = 2952593) B2952593
theorem B1313035 : Blo 1311974 1313035 := bstep (se 1 (by rfl) ⟨984776, by rfl⟩ : syracuseStep 1313035 = 1969553) B1969553
theorem B7989521 : Blo 1311974 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B1968407 : Blo 1311974 1968407 := bstep (se 1 (by rfl) ⟨1476305, by rfl⟩ : syracuseStep 1968407 = 2952611) B2952611
theorem B1313047 : Blo 1311974 1313047 := bstep (se 1 (by rfl) ⟨984785, by rfl⟩ : syracuseStep 1313047 = 1969571) B1969571
theorem B1313067 : Blo 1311974 1313067 := bstep (se 1 (by rfl) ⟨984800, by rfl⟩ : syracuseStep 1313067 = 1969601) B1969601
theorem B1313079 : Blo 1311974 1313079 := bstep (se 1 (by rfl) ⟨984809, by rfl⟩ : syracuseStep 1313079 = 1969619) B1969619
theorem B1313099 : Blo 1311974 1313099 := bstep (se 1 (by rfl) ⟨984824, by rfl⟩ : syracuseStep 1313099 = 1969649) B1969649
theorem B1313111 : Blo 1311974 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B1968473 : Blo 1311974 1968473 := bstep (se 2 (by rfl) ⟨738177, by rfl⟩ : syracuseStep 1968473 = 1476355) B1476355
theorem B1313131 : Blo 1311974 1313131 := bstep (se 1 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 1313131 = 1969697) B1969697
theorem B60615029 : Blo 1311974 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B1313143 : Blo 1311974 1313143 := bstep (se 1 (by rfl) ⟨984857, by rfl⟩ : syracuseStep 1313143 = 1969715) B1969715
theorem B2214283 : Blo 1311974 2214283 := bstep (se 1 (by rfl) ⟨1660712, by rfl⟩ : syracuseStep 2214283 = 3321425) B3321425
theorem B1477003 : Blo 1311974 1477003 := bstep (se 1 (by rfl) ⟨1107752, by rfl⟩ : syracuseStep 1477003 = 2215505) B2215505
theorem B1313163 : Blo 1311974 1313163 := bstep (se 1 (by rfl) ⟨984872, by rfl⟩ : syracuseStep 1313163 = 1969745) B1969745
theorem B1313175 : Blo 1311974 1313175 := bstep (se 1 (by rfl) ⟨984881, by rfl⟩ : syracuseStep 1313175 = 1969763) B1969763
theorem B1313195 : Blo 1311974 1313195 := bstep (se 1 (by rfl) ⟨984896, by rfl⟩ : syracuseStep 1313195 = 1969793) B1969793
theorem B1313207 : Blo 1311974 1313207 := bstep (se 1 (by rfl) ⟨984905, by rfl⟩ : syracuseStep 1313207 = 1969811) B1969811
theorem B1968587 : Blo 1311974 1968587 := bstep (se 1 (by rfl) ⟨1476440, by rfl⟩ : syracuseStep 1968587 = 2952881) B2952881
theorem B1313227 : Blo 1311974 1313227 := bstep (se 1 (by rfl) ⟨984920, by rfl⟩ : syracuseStep 1313227 = 1969841) B1969841
theorem B1968599 : Blo 1311974 1968599 := bstep (se 1 (by rfl) ⟨1476449, by rfl⟩ : syracuseStep 1968599 = 2952899) B2952899
theorem B1313239 : Blo 1311974 1313239 := bstep (se 1 (by rfl) ⟨984929, by rfl⟩ : syracuseStep 1313239 = 1969859) B1969859
theorem B1870295 : Blo 1311974 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B1313259 : Blo 1311974 1313259 := bstep (se 1 (by rfl) ⟨984944, by rfl⟩ : syracuseStep 1313259 = 1969889) B1969889
theorem B1477111 : Blo 1311974 1477111 := bstep (se 1 (by rfl) ⟨1107833, by rfl⟩ : syracuseStep 1477111 = 2215667) B2215667
theorem B1313271 : Blo 1311974 1313271 := bstep (se 1 (by rfl) ⟨984953, by rfl⟩ : syracuseStep 1313271 = 1969907) B1969907
theorem B1313291 : Blo 1311974 1313291 := bstep (se 1 (by rfl) ⟨984968, by rfl⟩ : syracuseStep 1313291 = 1969937) B1969937
theorem B1313303 : Blo 1311974 1313303 := bstep (se 1 (by rfl) ⟨984977, by rfl⟩ : syracuseStep 1313303 = 1969955) B1969955
theorem B2214425 : Blo 1311974 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B1968665 : Blo 1311974 1968665 := bstep (se 2 (by rfl) ⟨738249, by rfl⟩ : syracuseStep 1968665 = 1476499) B1476499
theorem B1313323 : Blo 1311974 1313323 := bstep (se 1 (by rfl) ⟨984992, by rfl⟩ : syracuseStep 1313323 = 1969985) B1969985
theorem B1313335 : Blo 1311974 1313335 := bstep (se 1 (by rfl) ⟨985001, by rfl⟩ : syracuseStep 1313335 = 1970003) B1970003
theorem B1313355 : Blo 1311974 1313355 := bstep (se 1 (by rfl) ⟨985016, by rfl⟩ : syracuseStep 1313355 = 1970033) B1970033
theorem B4262489 : Blo 1311974 4262489 := bstep (se 2 (by rfl) ⟨1598433, by rfl⟩ : syracuseStep 4262489 = 3196867) B3196867
theorem B1313367 : Blo 1311974 1313367 := bstep (se 1 (by rfl) ⟨985025, by rfl⟩ : syracuseStep 1313367 = 1970051) B1970051
theorem B1313387 : Blo 1311974 1313387 := bstep (se 1 (by rfl) ⟨985040, by rfl⟩ : syracuseStep 1313387 = 1970081) B1970081
theorem B1313399 : Blo 1311974 1313399 := bstep (se 1 (by rfl) ⟨985049, by rfl⟩ : syracuseStep 1313399 = 1970099) B1970099
theorem B1968779 : Blo 1311974 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B1313419 : Blo 1311974 1313419 := bstep (se 1 (by rfl) ⟨985064, by rfl⟩ : syracuseStep 1313419 = 1970129) B1970129
theorem B1968791 : Blo 1311974 1968791 := bstep (se 1 (by rfl) ⟨1476593, by rfl⟩ : syracuseStep 1968791 = 2953187) B2953187
theorem B1313431 : Blo 1311974 1313431 := bstep (se 1 (by rfl) ⟨985073, by rfl⟩ : syracuseStep 1313431 = 1970147) B1970147
theorem B2214553 : Blo 1311974 2214553 := bstep (se 2 (by rfl) ⟨830457, by rfl⟩ : syracuseStep 2214553 = 1660915) B1660915
theorem B1870489 : Blo 1311974 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B7989911 : Blo 1311974 7989911 := bstep (se 1 (by rfl) ⟨5992433, by rfl⟩ : syracuseStep 7989911 = 11984867) B11984867
theorem B1477291 : Blo 1311974 1477291 := bstep (se 1 (by rfl) ⟨1107968, by rfl⟩ : syracuseStep 1477291 = 2215937) B2215937
theorem B1313451 : Blo 1311974 1313451 := bstep (se 1 (by rfl) ⟨985088, by rfl⟩ : syracuseStep 1313451 = 1970177) B1970177
theorem B1313463 : Blo 1311974 1313463 := bstep (se 1 (by rfl) ⟨985097, by rfl⟩ : syracuseStep 1313463 = 1970195) B1970195
theorem B1313483 : Blo 1311974 1313483 := bstep (se 1 (by rfl) ⟨985112, by rfl⟩ : syracuseStep 1313483 = 1970225) B1970225
theorem B1313495 : Blo 1311974 1313495 := bstep (se 1 (by rfl) ⟨985121, by rfl⟩ : syracuseStep 1313495 = 1970243) B1970243
theorem B1968857 : Blo 1311974 1968857 := bstep (se 2 (by rfl) ⟨738321, by rfl⟩ : syracuseStep 1968857 = 1476643) B1476643
theorem B1313515 : Blo 1311974 1313515 := bstep (se 1 (by rfl) ⟨985136, by rfl⟩ : syracuseStep 1313515 = 1970273) B1970273
theorem B1313527 : Blo 1311974 1313527 := bstep (se 1 (by rfl) ⟨985145, by rfl⟩ : syracuseStep 1313527 = 1970291) B1970291
theorem B1313547 : Blo 1311974 1313547 := bstep (se 1 (by rfl) ⟨985160, by rfl⟩ : syracuseStep 1313547 = 1970321) B1970321
theorem B1477399 : Blo 1311974 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B1313559 : Blo 1311974 1313559 := bstep (se 1 (by rfl) ⟨985169, by rfl⟩ : syracuseStep 1313559 = 1970339) B1970339
theorem B1313579 : Blo 1311974 1313579 := bstep (se 1 (by rfl) ⟨985184, by rfl⟩ : syracuseStep 1313579 = 1970369) B1970369
theorem B1313591 : Blo 1311974 1313591 := bstep (se 1 (by rfl) ⟨985193, by rfl⟩ : syracuseStep 1313591 = 1970387) B1970387
theorem B1968971 : Blo 1311974 1968971 := bstep (se 1 (by rfl) ⟨1476728, by rfl⟩ : syracuseStep 1968971 = 2953457) B2953457
theorem B1313611 : Blo 1311974 1313611 := bstep (se 1 (by rfl) ⟨985208, by rfl⟩ : syracuseStep 1313611 = 1970417) B1970417
theorem B1968983 : Blo 1311974 1968983 := bstep (se 1 (by rfl) ⟨1476737, by rfl⟩ : syracuseStep 1968983 = 2953475) B2953475
theorem B2493271 : Blo 1311974 2493271 := bstep (se 1 (by rfl) ⟨1869953, by rfl⟩ : syracuseStep 2493271 = 3739907) B3739907
theorem B1313623 : Blo 1311974 1313623 := bstep (se 1 (by rfl) ⟨985217, by rfl⟩ : syracuseStep 1313623 = 1970435) B1970435
theorem B1313643 : Blo 1311974 1313643 := bstep (se 1 (by rfl) ⟨985232, by rfl⟩ : syracuseStep 1313643 = 1970465) B1970465
theorem B1313655 : Blo 1311974 1313655 := bstep (se 1 (by rfl) ⟨985241, by rfl⟩ : syracuseStep 1313655 = 1970483) B1970483
theorem B1313675 : Blo 1311974 1313675 := bstep (se 1 (by rfl) ⟨985256, by rfl⟩ : syracuseStep 1313675 = 1970513) B1970513
theorem B1313687 : Blo 1311974 1313687 := bstep (se 1 (by rfl) ⟨985265, by rfl⟩ : syracuseStep 1313687 = 1970531) B1970531
theorem B2952089 : Blo 1311974 2952089 := bstep (se 2 (by rfl) ⟨1107033, by rfl⟩ : syracuseStep 2952089 = 2214067) B2214067
theorem B1969049 : Blo 1311974 1969049 := bstep (se 2 (by rfl) ⟨738393, by rfl⟩ : syracuseStep 1969049 = 1476787) B1476787
theorem B1313707 : Blo 1311974 1313707 := bstep (se 1 (by rfl) ⟨985280, by rfl⟩ : syracuseStep 1313707 = 1970561) B1970561
theorem B1313719 : Blo 1311974 1313719 := bstep (se 1 (by rfl) ⟨985289, by rfl⟩ : syracuseStep 1313719 = 1970579) B1970579
theorem B1477579 : Blo 1311974 1477579 := bstep (se 1 (by rfl) ⟨1108184, by rfl⟩ : syracuseStep 1477579 = 2216369) B2216369
theorem B1313739 : Blo 1311974 1313739 := bstep (se 1 (by rfl) ⟨985304, by rfl⟩ : syracuseStep 1313739 = 1970609) B1970609
theorem B1313751 : Blo 1311974 1313751 := bstep (se 1 (by rfl) ⟨985313, by rfl⟩ : syracuseStep 1313751 = 1970627) B1970627
theorem B1313771 : Blo 1311974 1313771 := bstep (se 1 (by rfl) ⟨985328, by rfl⟩ : syracuseStep 1313771 = 1970657) B1970657
theorem B2952179 : Blo 1311974 2952179 := bstep (se 1 (by rfl) ⟨2214134, by rfl⟩ : syracuseStep 2952179 = 4428269) B4428269
theorem B1313783 : Blo 1311974 1313783 := bstep (se 1 (by rfl) ⟨985337, by rfl⟩ : syracuseStep 1313783 = 1970675) B1970675
theorem B1969163 : Blo 1311974 1969163 := bstep (se 1 (by rfl) ⟨1476872, by rfl⟩ : syracuseStep 1969163 = 2953745) B2953745
theorem B1313803 : Blo 1311974 1313803 := bstep (se 1 (by rfl) ⟨985352, by rfl⟩ : syracuseStep 1313803 = 1970705) B1970705
theorem B2952215 : Blo 1311974 2952215 := bstep (se 1 (by rfl) ⟨2214161, by rfl⟩ : syracuseStep 2952215 = 4428323) B4428323
theorem B4205591 : Blo 1311974 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B1969175 : Blo 1311974 1969175 := bstep (se 1 (by rfl) ⟨1476881, by rfl⟩ : syracuseStep 1969175 = 2953763) B2953763
theorem B1313815 : Blo 1311974 1313815 := bstep (se 1 (by rfl) ⟨985361, by rfl⟩ : syracuseStep 1313815 = 1970723) B1970723
theorem B1313835 : Blo 1311974 1313835 := bstep (se 1 (by rfl) ⟨985376, by rfl⟩ : syracuseStep 1313835 = 1970753) B1970753
theorem B1477687 : Blo 1311974 1477687 := bstep (se 1 (by rfl) ⟨1108265, by rfl⟩ : syracuseStep 1477687 = 2216531) B2216531
theorem B1313847 : Blo 1311974 1313847 := bstep (se 1 (by rfl) ⟨985385, by rfl⟩ : syracuseStep 1313847 = 1970771) B1970771
theorem B37833803 : Blo 1311974 37833803 := bstep (se 1 (by rfl) ⟨28375352, by rfl⟩ : syracuseStep 37833803 = 56750705) B56750705
theorem B6646859 : Blo 1311974 6646859 := bstep (se 1 (by rfl) ⟨4985144, by rfl⟩ : syracuseStep 6646859 = 9970289) B9970289
theorem B1313867 : Blo 1311974 1313867 := bstep (se 1 (by rfl) ⟨985400, by rfl⟩ : syracuseStep 1313867 = 1970801) B1970801
theorem B1313879 : Blo 1311974 1313879 := bstep (se 1 (by rfl) ⟨985409, by rfl⟩ : syracuseStep 1313879 = 1970819) B1970819
theorem B1969241 : Blo 1311974 1969241 := bstep (se 2 (by rfl) ⟨738465, by rfl⟩ : syracuseStep 1969241 = 1476931) B1476931
theorem B11218013 : Blo 1311974 11218013 := bstep (se 3 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 11218013 = 4206755) B4206755
theorem B1313899 : Blo 1311974 1313899 := bstep (se 1 (by rfl) ⟨985424, by rfl⟩ : syracuseStep 1313899 = 1970849) B1970849
theorem B1313911 : Blo 1311974 1313911 := bstep (se 1 (by rfl) ⟨985433, by rfl⟩ : syracuseStep 1313911 = 1970867) B1970867
theorem B1313931 : Blo 1311974 1313931 := bstep (se 1 (by rfl) ⟨985448, by rfl⟩ : syracuseStep 1313931 = 1970897) B1970897
theorem B4795537 : Blo 1311974 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B1313943 : Blo 1311974 1313943 := bstep (se 1 (by rfl) ⟨985457, by rfl⟩ : syracuseStep 1313943 = 1970915) B1970915
theorem B1313963 : Blo 1311974 1313963 := bstep (se 1 (by rfl) ⟨985472, by rfl⟩ : syracuseStep 1313963 = 1970945) B1970945
theorem B83012789 : Blo 1311974 83012789 := bstep (se 5 (by rfl) ⟨3891224, by rfl⟩ : syracuseStep 83012789 = 7782449) B7782449
theorem B2952395 : Blo 1311974 2952395 := bstep (se 1 (by rfl) ⟨2214296, by rfl⟩ : syracuseStep 2952395 = 4428593) B4428593
theorem B1969355 : Blo 1311974 1969355 := bstep (se 1 (by rfl) ⟨1477016, by rfl⟩ : syracuseStep 1969355 = 2954033) B2954033
theorem B2215127 : Blo 1311974 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B1969367 : Blo 1311974 1969367 := bstep (se 1 (by rfl) ⟨1477025, by rfl⟩ : syracuseStep 1969367 = 2954051) B2954051
theorem B1477867 : Blo 1311974 1477867 := bstep (se 1 (by rfl) ⟨1108400, by rfl⟩ : syracuseStep 1477867 = 2216801) B2216801
theorem B2952449 : Blo 1311974 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B1969433 : Blo 1311974 1969433 := bstep (se 2 (by rfl) ⟨738537, by rfl⟩ : syracuseStep 1969433 = 1477075) B1477075
theorem B7097645 : Blo 1311974 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B2805067 : Blo 1311974 2805067 := bstep (se 1 (by rfl) ⟨2103800, by rfl⟩ : syracuseStep 2805067 = 4207601) B4207601
theorem B2215255 : Blo 1311974 2215255 := bstep (se 1 (by rfl) ⟨1661441, by rfl⟩ : syracuseStep 2215255 = 3322883) B3322883
theorem B1477975 : Blo 1311974 1477975 := bstep (se 1 (by rfl) ⟨1108481, by rfl⟩ : syracuseStep 1477975 = 2216963) B2216963
theorem B5320025 : Blo 1311974 5320025 := bstep (se 2 (by rfl) ⟨1995009, by rfl⟩ : syracuseStep 5320025 = 3990019) B3990019
theorem B3550553 : Blo 1311974 3550553 := bstep (se 2 (by rfl) ⟨1331457, by rfl⟩ : syracuseStep 3550553 = 2662915) B2662915
theorem B3738973 : Blo 1311974 3738973 := bstep (se 3 (by rfl) ⟨701057, by rfl⟩ : syracuseStep 3738973 = 1402115) B1402115
theorem B1969547 : Blo 1311974 1969547 := bstep (se 1 (by rfl) ⟨1477160, by rfl⟩ : syracuseStep 1969547 = 2954321) B2954321
theorem B3739031 : Blo 1311974 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B1969559 : Blo 1311974 1969559 := bstep (se 1 (by rfl) ⟨1477169, by rfl⟩ : syracuseStep 1969559 = 2954339) B2954339
theorem B1420747 : Blo 1311974 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B2993611 : Blo 1311974 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B3993035 : Blo 1311974 3993035 := bstep (se 1 (by rfl) ⟨2994776, by rfl⟩ : syracuseStep 3993035 = 5989553) B5989553
theorem B2952665 : Blo 1311974 2952665 := bstep (se 2 (by rfl) ⟨1107249, by rfl⟩ : syracuseStep 2952665 = 2214499) B2214499
theorem B1969625 : Blo 1311974 1969625 := bstep (se 2 (by rfl) ⟨738609, by rfl⟩ : syracuseStep 1969625 = 1477219) B1477219
theorem B1478155 : Blo 1311974 1478155 := bstep (se 1 (by rfl) ⟨1108616, by rfl⟩ : syracuseStep 1478155 = 2217233) B2217233
theorem B3321395 : Blo 1311974 3321395 := bstep (se 1 (by rfl) ⟨2491046, by rfl⟩ : syracuseStep 3321395 = 4982093) B4982093
theorem B2952755 : Blo 1311974 2952755 := bstep (se 1 (by rfl) ⟨2214566, by rfl⟩ : syracuseStep 2952755 = 4429133) B4429133
theorem B1969739 : Blo 1311974 1969739 := bstep (se 1 (by rfl) ⟨1477304, by rfl⟩ : syracuseStep 1969739 = 2954609) B2954609
theorem B2952791 : Blo 1311974 2952791 := bstep (se 1 (by rfl) ⟨2214593, by rfl⟩ : syracuseStep 2952791 = 4429187) B4429187
theorem B1969751 : Blo 1311974 1969751 := bstep (se 1 (by rfl) ⟨1477313, by rfl⟩ : syracuseStep 1969751 = 2954627) B2954627
theorem B2494091 : Blo 1311974 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1969817 : Blo 1311974 1969817 := bstep (se 2 (by rfl) ⟨738681, by rfl⟩ : syracuseStep 1969817 = 1477363) B1477363
theorem B2494145 : Blo 1311974 2494145 := bstep (se 2 (by rfl) ⟨935304, by rfl⟩ : syracuseStep 2494145 = 1870609) B1870609
theorem B4984523 : Blo 1311974 4984523 := bstep (se 1 (by rfl) ⟨3738392, by rfl⟩ : syracuseStep 4984523 = 7476785) B7476785
theorem B4984537 : Blo 1311974 4984537 := bstep (se 2 (by rfl) ⟨1869201, by rfl⟩ : syracuseStep 4984537 = 3738403) B3738403
theorem B31960817 : Blo 1311974 31960817 := bstep (se 2 (by rfl) ⟨11985306, by rfl⟩ : syracuseStep 31960817 = 23970613) B23970613
theorem B2952971 : Blo 1311974 2952971 := bstep (se 1 (by rfl) ⟨2214728, by rfl⟩ : syracuseStep 2952971 = 4429457) B4429457
theorem B1969931 : Blo 1311974 1969931 := bstep (se 1 (by rfl) ⟨1477448, by rfl⟩ : syracuseStep 1969931 = 2954897) B2954897
theorem B1969943 : Blo 1311974 1969943 := bstep (se 1 (by rfl) ⟨1477457, by rfl⟩ : syracuseStep 1969943 = 2954915) B2954915
theorem B2805529 : Blo 1311974 2805529 := bstep (se 2 (by rfl) ⟨1052073, by rfl⟩ : syracuseStep 2805529 = 2104147) B2104147
theorem B2953025 : Blo 1311974 2953025 := bstep (se 2 (by rfl) ⟨1107384, by rfl⟩ : syracuseStep 2953025 = 2214769) B2214769
theorem B11218763 : Blo 1311974 11218763 := bstep (se 1 (by rfl) ⟨8414072, by rfl⟩ : syracuseStep 11218763 = 16828145) B16828145
theorem B1970009 : Blo 1311974 1970009 := bstep (se 2 (by rfl) ⟨738753, by rfl⟩ : syracuseStep 1970009 = 1477507) B1477507
theorem B7475075 : Blo 1311974 7475075 := bstep (se 1 (by rfl) ⟨5606306, by rfl⟩ : syracuseStep 7475075 = 11212613) B11212613
theorem B1773515 : Blo 1311974 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B2215883 : Blo 1311974 2215883 := bstep (se 1 (by rfl) ⟨1661912, by rfl⟩ : syracuseStep 2215883 = 3323825) B3323825
theorem B1970123 : Blo 1311974 1970123 := bstep (se 1 (by rfl) ⟨1477592, by rfl⟩ : syracuseStep 1970123 = 2955185) B2955185
theorem B1970135 : Blo 1311974 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B2953241 : Blo 1311974 2953241 := bstep (se 2 (by rfl) ⟨1107465, by rfl⟩ : syracuseStep 2953241 = 2214931) B2214931
theorem B1970201 : Blo 1311974 1970201 := bstep (se 2 (by rfl) ⟨738825, by rfl⟩ : syracuseStep 1970201 = 1477651) B1477651
theorem B3321931 : Blo 1311974 3321931 := bstep (se 1 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 3321931 = 4982897) B4982897
theorem B2216011 : Blo 1311974 2216011 := bstep (se 1 (by rfl) ⟨1662008, by rfl⟩ : syracuseStep 2216011 = 3324017) B3324017
theorem B2994265 : Blo 1311974 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B3551321 : Blo 1311974 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B2953331 : Blo 1311974 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B1970315 : Blo 1311974 1970315 := bstep (se 1 (by rfl) ⟨1477736, by rfl⟩ : syracuseStep 1970315 = 2955473) B2955473
theorem B1773719 : Blo 1311974 1773719 := bstep (se 1 (by rfl) ⟨1330289, by rfl⟩ : syracuseStep 1773719 = 2660579) B2660579
theorem B2953367 : Blo 1311974 2953367 := bstep (se 1 (by rfl) ⟨2215025, by rfl⟩ : syracuseStep 2953367 = 4430051) B4430051
theorem B1970327 : Blo 1311974 1970327 := bstep (se 1 (by rfl) ⟨1477745, by rfl⟩ : syracuseStep 1970327 = 2955491) B2955491
theorem B3322073 : Blo 1311974 3322073 := bstep (se 2 (by rfl) ⟨1245777, by rfl⟩ : syracuseStep 3322073 = 2491555) B2491555
theorem B2216153 : Blo 1311974 2216153 := bstep (se 2 (by rfl) ⟨831057, by rfl⟩ : syracuseStep 2216153 = 1662115) B1662115
theorem B1970393 : Blo 1311974 1970393 := bstep (se 2 (by rfl) ⟨738897, by rfl⟩ : syracuseStep 1970393 = 1477795) B1477795
theorem B4428107 : Blo 1311974 4428107 := bstep (se 1 (by rfl) ⟨3321080, by rfl⟩ : syracuseStep 4428107 = 6642161) B6642161
theorem B2953547 : Blo 1311974 2953547 := bstep (se 1 (by rfl) ⟨2215160, by rfl⟩ : syracuseStep 2953547 = 4430321) B4430321
theorem B4206923 : Blo 1311974 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B1970507 : Blo 1311974 1970507 := bstep (se 1 (by rfl) ⟨1477880, by rfl⟩ : syracuseStep 1970507 = 2955761) B2955761
theorem B1970519 : Blo 1311974 1970519 := bstep (se 1 (by rfl) ⟨1477889, by rfl⟩ : syracuseStep 1970519 = 2955779) B2955779
theorem B2216281 : Blo 1311974 2216281 := bstep (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) B1662211
theorem B1331563 : Blo 1311974 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B2953601 : Blo 1311974 2953601 := bstep (se 2 (by rfl) ⟨1107600, by rfl⟩ : syracuseStep 2953601 = 2215201) B2215201
theorem B1970585 : Blo 1311974 1970585 := bstep (se 2 (by rfl) ⟨738969, by rfl⟩ : syracuseStep 1970585 = 1477939) B1477939
theorem B1970699 : Blo 1311974 1970699 := bstep (se 1 (by rfl) ⟨1478024, by rfl⟩ : syracuseStep 1970699 = 2956049) B2956049
theorem B1970711 : Blo 1311974 1970711 := bstep (se 1 (by rfl) ⟨1478033, by rfl⟩ : syracuseStep 1970711 = 2956067) B2956067
theorem B9458221 : Blo 1311974 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B4428377 : Blo 1311974 4428377 := bstep (se 2 (by rfl) ⟨1660641, by rfl⟩ : syracuseStep 4428377 = 3321283) B3321283
theorem B2953817 : Blo 1311974 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B3740249 : Blo 1311974 3740249 := bstep (se 2 (by rfl) ⟨1402593, by rfl⟩ : syracuseStep 3740249 = 2805187) B2805187
theorem B1970777 : Blo 1311974 1970777 := bstep (se 2 (by rfl) ⟨739041, by rfl⟩ : syracuseStep 1970777 = 1478083) B1478083
theorem B4264541 : Blo 1311974 4264541 := bstep (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) B1599203
theorem B4985495 : Blo 1311974 4985495 := bstep (se 1 (by rfl) ⟨3739121, by rfl⟩ : syracuseStep 4985495 = 7478243) B7478243
theorem B2953907 : Blo 1311974 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B3740363 : Blo 1311974 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B1970891 : Blo 1311974 1970891 := bstep (se 1 (by rfl) ⟨1478168, by rfl⟩ : syracuseStep 1970891 = 2956337) B2956337
theorem B2953943 : Blo 1311974 2953943 := bstep (se 1 (by rfl) ⟨2215457, by rfl⟩ : syracuseStep 2953943 = 4430915) B4430915
theorem B1970903 : Blo 1311974 1970903 := bstep (se 1 (by rfl) ⟨1478177, by rfl⟩ : syracuseStep 1970903 = 2956355) B2956355
theorem B9966401 : Blo 1311974 9966401 := bstep (se 2 (by rfl) ⟨3737400, by rfl⟩ : syracuseStep 9966401 = 7474801) B7474801
theorem B6648641 : Blo 1311974 6648641 := bstep (se 2 (by rfl) ⟨2493240, by rfl⟩ : syracuseStep 6648641 = 4986481) B4986481
theorem B2954123 : Blo 1311974 2954123 := bstep (se 1 (by rfl) ⟨2215592, by rfl⟩ : syracuseStep 2954123 = 4431185) B4431185
theorem B2216855 : Blo 1311974 2216855 := bstep (se 1 (by rfl) ⟨1662641, by rfl⟩ : syracuseStep 2216855 = 3325283) B3325283
theorem B2954177 : Blo 1311974 2954177 := bstep (se 2 (by rfl) ⟨1107816, by rfl⟩ : syracuseStep 2954177 = 2215633) B2215633
theorem B2102231 : Blo 1311974 2102231 := bstep (se 1 (by rfl) ⟨1576673, by rfl⟩ : syracuseStep 2102231 = 3153347) B3153347
theorem B3322903 : Blo 1311974 3322903 := bstep (se 1 (by rfl) ⟨2492177, by rfl⟩ : syracuseStep 3322903 = 4984355) B4984355
theorem B2216983 : Blo 1311974 2216983 := bstep (se 1 (by rfl) ⟨1662737, by rfl⟩ : syracuseStep 2216983 = 3325475) B3325475
theorem B7574573 : Blo 1311974 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B6394925 : Blo 1311974 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B2954393 : Blo 1311974 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B35042485 : Blo 1311974 35042485 := bstep (se 5 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 35042485 = 3285233) B3285233
theorem B2954483 : Blo 1311974 2954483 := bstep (se 1 (by rfl) ⟨2215862, by rfl⟩ : syracuseStep 2954483 = 4431725) B4431725
theorem B2102539 : Blo 1311974 2102539 := bstep (se 1 (by rfl) ⟨1576904, by rfl⟩ : syracuseStep 2102539 = 3153809) B3153809
theorem B4429079 : Blo 1311974 4429079 := bstep (se 1 (by rfl) ⟨3321809, by rfl⟩ : syracuseStep 4429079 = 6643619) B6643619
theorem B2954519 : Blo 1311974 2954519 := bstep (se 1 (by rfl) ⟨2215889, by rfl⟩ : syracuseStep 2954519 = 4431779) B4431779
theorem B5608835 : Blo 1311974 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B11220403 : Blo 1311974 11220403 := bstep (se 1 (by rfl) ⟨8415302, by rfl⟩ : syracuseStep 11220403 = 16830605) B16830605
theorem B4208051 : Blo 1311974 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B3323339 : Blo 1311974 3323339 := bstep (se 1 (by rfl) ⟨2492504, by rfl⟩ : syracuseStep 3323339 = 4985009) B4985009
theorem B2954699 : Blo 1311974 2954699 := bstep (se 1 (by rfl) ⟨2216024, by rfl⟩ : syracuseStep 2954699 = 4432049) B4432049
theorem B2954753 : Blo 1311974 2954753 := bstep (se 2 (by rfl) ⟨1108032, by rfl⟩ : syracuseStep 2954753 = 2216065) B2216065
theorem B14956163 : Blo 1311974 14956163 := bstep (se 1 (by rfl) ⟨11217122, by rfl⟩ : syracuseStep 14956163 = 22434245) B22434245
theorem B2561675 : Blo 1311974 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B2954969 : Blo 1311974 2954969 := bstep (se 2 (by rfl) ⟨1108113, by rfl⟩ : syracuseStep 2954969 = 2216227) B2216227
theorem B12613421 : Blo 1311974 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B4429619 : Blo 1311974 4429619 := bstep (se 1 (by rfl) ⟨3322214, by rfl⟩ : syracuseStep 4429619 = 6644429) B6644429
theorem B2955059 : Blo 1311974 2955059 := bstep (se 1 (by rfl) ⟨2216294, by rfl⟩ : syracuseStep 2955059 = 4432589) B4432589
theorem B3741491 : Blo 1311974 3741491 := bstep (se 1 (by rfl) ⟨2806118, by rfl⟩ : syracuseStep 3741491 = 5612237) B5612237
theorem B3323713 : Blo 1311974 3323713 := bstep (se 2 (by rfl) ⟨1246392, by rfl⟩ : syracuseStep 3323713 = 2492785) B2492785
theorem B5125963 : Blo 1311974 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B2955095 : Blo 1311974 2955095 := bstep (se 1 (by rfl) ⟨2216321, by rfl⟩ : syracuseStep 2955095 = 4432643) B4432643
theorem B28391269 : Blo 1311974 28391269 := bstep (se 4 (by rfl) ⟨2661681, by rfl⟩ : syracuseStep 28391269 = 5323363) B5323363
theorem B4986755 : Blo 1311974 4986755 := bstep (se 1 (by rfl) ⟨3740066, by rfl⟩ : syracuseStep 4986755 = 7480133) B7480133
theorem B2955275 : Blo 1311974 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B4429889 : Blo 1311974 4429889 := bstep (se 2 (by rfl) ⟨1661208, by rfl⟩ : syracuseStep 4429889 = 3322417) B3322417
theorem B2955329 : Blo 1311974 2955329 := bstep (se 2 (by rfl) ⟨1108248, by rfl⟩ : syracuseStep 2955329 = 2216497) B2216497
theorem B7100567 : Blo 1311974 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B2660531 : Blo 1311974 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B1661143 : Blo 1311974 1661143 := bstep (se 1 (by rfl) ⟨1245857, by rfl⟩ : syracuseStep 1661143 = 2491715) B2491715
theorem B2955545 : Blo 1311974 2955545 := bstep (se 2 (by rfl) ⟨1108329, by rfl⟩ : syracuseStep 2955545 = 2216659) B2216659
theorem B2955635 : Blo 1311974 2955635 := bstep (se 1 (by rfl) ⟨2216726, by rfl⟩ : syracuseStep 2955635 = 4433453) B4433453
theorem B3324311 : Blo 1311974 3324311 := bstep (se 1 (by rfl) ⟨2493233, by rfl⟩ : syracuseStep 3324311 = 4986467) B4986467
theorem B2955671 : Blo 1311974 2955671 := bstep (se 1 (by rfl) ⟨2216753, by rfl⟩ : syracuseStep 2955671 = 4433507) B4433507
theorem B2103769 : Blo 1311974 2103769 := bstep (se 2 (by rfl) ⟨788913, by rfl⟩ : syracuseStep 2103769 = 1577827) B1577827
theorem B5986781 : Blo 1311974 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B23943755 : Blo 1311974 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B2366027 : Blo 1311974 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B2955851 : Blo 1311974 2955851 := bstep (se 1 (by rfl) ⟨2216888, by rfl⟩ : syracuseStep 2955851 = 4433777) B4433777
theorem B4209241 : Blo 1311974 4209241 := bstep (se 2 (by rfl) ⟨1578465, by rfl⟩ : syracuseStep 4209241 = 3156931) B3156931
theorem B4430429 : Blo 1311974 4430429 := bstep (se 3 (by rfl) ⟨830705, by rfl⟩ : syracuseStep 4430429 = 1661411) B1661411
theorem B2955905 : Blo 1311974 2955905 := bstep (se 2 (by rfl) ⟨1108464, by rfl⟩ : syracuseStep 2955905 = 2216929) B2216929
theorem B9968345 : Blo 1311974 9968345 := bstep (se 2 (by rfl) ⟨3738129, by rfl⟩ : syracuseStep 9968345 = 7476259) B7476259
theorem B6650585 : Blo 1311974 6650585 := bstep (se 2 (by rfl) ⟨2493969, by rfl⟩ : syracuseStep 6650585 = 4987939) B4987939
theorem B8411921 : Blo 1311974 8411921 := bstep (se 2 (by rfl) ⟨3154470, by rfl⟩ : syracuseStep 8411921 = 6308941) B6308941
theorem B2956121 : Blo 1311974 2956121 := bstep (se 2 (by rfl) ⟨1108545, by rfl⟩ : syracuseStep 2956121 = 2217091) B2217091
theorem B2956211 : Blo 1311974 2956211 := bstep (se 1 (by rfl) ⟨2217158, by rfl⟩ : syracuseStep 2956211 = 4434317) B4434317
theorem B2366401 : Blo 1311974 2366401 := bstep (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) B1774801
theorem B3152857 : Blo 1311974 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B2956247 : Blo 1311974 2956247 := bstep (se 1 (by rfl) ⟨2217185, by rfl⟩ : syracuseStep 2956247 = 4434371) B4434371
theorem B2366489 : Blo 1311974 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2956427 : Blo 1311974 2956427 := bstep (se 1 (by rfl) ⟨2217320, by rfl⟩ : syracuseStep 2956427 = 4434641) B4434641
theorem B5610647 : Blo 1311974 5610647 := bstep (se 1 (by rfl) ⟨4207985, by rfl⟩ : syracuseStep 5610647 = 8415971) B8415971
theorem B3325121 : Blo 1311974 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B9977093 : Blo 1311974 9977093 := bstep (se 4 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 9977093 = 1870705) B1870705
theorem B4734301 : Blo 1311974 4734301 := bstep (se 3 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 4734301 = 1775363) B1775363
theorem B22421123 : Blo 1311974 22421123 := bstep (se 1 (by rfl) ⟨16815842, by rfl⟩ : syracuseStep 22421123 = 33631685) B33631685
theorem B4800179 : Blo 1311974 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B409001669 : Blo 1311974 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B4431563 : Blo 1311974 4431563 := bstep (se 1 (by rfl) ⟨3323672, by rfl⟩ : syracuseStep 4431563 = 6647345) B6647345
theorem B40402637 : Blo 1311974 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B3325657 : Blo 1311974 3325657 := bstep (se 2 (by rfl) ⟨1247121, by rfl⟩ : syracuseStep 3325657 = 2494243) B2494243
theorem B7987045 : Blo 1311974 7987045 := bstep (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) B1497571
theorem B1662859 : Blo 1311974 1662859 := bstep (se 1 (by rfl) ⟨1247144, by rfl⟩ : syracuseStep 1662859 = 2494289) B2494289
theorem B9461681 : Blo 1311974 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B9723827 : Blo 1311974 9723827 := bstep (se 1 (by rfl) ⟨7292870, by rfl⟩ : syracuseStep 9723827 = 14585741) B14585741
theorem B4431833 : Blo 1311974 4431833 := bstep (se 2 (by rfl) ⟨1661937, by rfl⟩ : syracuseStep 4431833 = 3323875) B3323875
theorem B12148973 : Blo 1311974 12148973 := bstep (se 3 (by rfl) ⟨2277932, by rfl⟩ : syracuseStep 12148973 = 4555865) B4555865
theorem B9470189 : Blo 1311974 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B2490743 : Blo 1311974 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B2843027 : Blo 1311974 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B7094749 : Blo 1311974 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B6644267 : Blo 1311974 6644267 := bstep (se 1 (by rfl) ⟨4983200, by rfl⟩ : syracuseStep 6644267 = 9966401) B9966401
theorem B4432427 : Blo 1311974 4432427 := bstep (se 1 (by rfl) ⟨3324320, by rfl⟩ : syracuseStep 4432427 = 6648641) B6648641
theorem B4260413 : Blo 1311974 4260413 := bstep (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) B1597655
theorem B3736331 : Blo 1311974 3736331 := bstep (se 1 (by rfl) ⟨2802248, by rfl⟩ : syracuseStep 3736331 = 5604497) B5604497
theorem B5612321 : Blo 1311974 5612321 := bstep (se 2 (by rfl) ⟨2104620, by rfl⟩ : syracuseStep 5612321 = 4209241) B4209241
theorem B6390731 : Blo 1311974 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B9970775 : Blo 1311974 9970775 := bstep (se 1 (by rfl) ⟨7478081, by rfl⟩ : syracuseStep 9970775 = 14956163) B14956163
theorem B8414381 : Blo 1311974 8414381 := bstep (se 3 (by rfl) ⟨1577696, by rfl⟩ : syracuseStep 8414381 = 3155393) B3155393
theorem B3155201 : Blo 1311974 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B1312007 : Blo 1311974 1312007 := bstep (se 1 (by rfl) ⟨984005, by rfl⟩ : syracuseStep 1312007 = 1968011) B1968011
theorem B1312015 : Blo 1311974 1312015 := bstep (se 1 (by rfl) ⟨984011, by rfl⟩ : syracuseStep 1312015 = 1968023) B1968023
theorem B4203809 : Blo 1311974 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B1312059 : Blo 1311974 1312059 := bstep (se 1 (by rfl) ⟨984044, by rfl⟩ : syracuseStep 1312059 = 1968089) B1968089
theorem B1312135 : Blo 1311974 1312135 := bstep (se 1 (by rfl) ⟨984101, by rfl⟩ : syracuseStep 1312135 = 1968203) B1968203
theorem B1312143 : Blo 1311974 1312143 := bstep (se 1 (by rfl) ⟨984107, by rfl⟩ : syracuseStep 1312143 = 1968215) B1968215
theorem B1312187 : Blo 1311974 1312187 := bstep (se 1 (by rfl) ⟨984140, by rfl⟩ : syracuseStep 1312187 = 1968281) B1968281
theorem B10651139 : Blo 1311974 10651139 := bstep (se 1 (by rfl) ⟨7988354, by rfl⟩ : syracuseStep 10651139 = 15976709) B15976709
theorem B1476103 : Blo 1311974 1476103 := bstep (se 1 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 1476103 = 2214155) B2214155
theorem B1312263 : Blo 1311974 1312263 := bstep (se 1 (by rfl) ⟨984197, by rfl⟩ : syracuseStep 1312263 = 1968395) B1968395
theorem B1312271 : Blo 1311974 1312271 := bstep (se 1 (by rfl) ⟨984203, by rfl⟩ : syracuseStep 1312271 = 1968407) B1968407
theorem B3737117 : Blo 1311974 3737117 := bstep (se 3 (by rfl) ⟨700709, by rfl⟩ : syracuseStep 3737117 = 1401419) B1401419
theorem B1312315 : Blo 1311974 1312315 := bstep (se 1 (by rfl) ⟨984236, by rfl⟩ : syracuseStep 1312315 = 1968473) B1968473
theorem B1312391 : Blo 1311974 1312391 := bstep (se 1 (by rfl) ⟨984293, by rfl⟩ : syracuseStep 1312391 = 1968587) B1968587
theorem B1312399 : Blo 1311974 1312399 := bstep (se 1 (by rfl) ⟨984299, by rfl⟩ : syracuseStep 1312399 = 1968599) B1968599
theorem B3991187 : Blo 1311974 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B2803385 : Blo 1311974 2803385 := bstep (se 2 (by rfl) ⟨1051269, by rfl⟩ : syracuseStep 2803385 = 2102539) B2102539
theorem B1476283 : Blo 1311974 1476283 := bstep (se 1 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 1476283 = 2214425) B2214425
theorem B1312443 : Blo 1311974 1312443 := bstep (se 1 (by rfl) ⟨984332, by rfl⟩ : syracuseStep 1312443 = 1968665) B1968665
theorem B1312519 : Blo 1311974 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B1312527 : Blo 1311974 1312527 := bstep (se 1 (by rfl) ⟨984395, by rfl⟩ : syracuseStep 1312527 = 1968791) B1968791
theorem B5326607 : Blo 1311974 5326607 := bstep (se 1 (by rfl) ⟨3994955, by rfl⟩ : syracuseStep 5326607 = 7989911) B7989911
theorem B1312571 : Blo 1311974 1312571 := bstep (se 1 (by rfl) ⟨984428, by rfl⟩ : syracuseStep 1312571 = 1968857) B1968857
theorem B6645563 : Blo 1311974 6645563 := bstep (se 1 (by rfl) ⟨4984172, by rfl⟩ : syracuseStep 6645563 = 9968345) B9968345
theorem B4433723 : Blo 1311974 4433723 := bstep (se 1 (by rfl) ⟨3325292, by rfl⟩ : syracuseStep 4433723 = 6650585) B6650585
theorem B1312647 : Blo 1311974 1312647 := bstep (se 1 (by rfl) ⟨984485, by rfl⟩ : syracuseStep 1312647 = 1968971) B1968971
theorem B1312655 : Blo 1311974 1312655 := bstep (se 1 (by rfl) ⟨984491, by rfl⟩ : syracuseStep 1312655 = 1968983) B1968983
theorem B14960537 : Blo 1311974 14960537 := bstep (se 2 (by rfl) ⟨5610201, by rfl⟩ : syracuseStep 14960537 = 11220403) B11220403
theorem B3991481 : Blo 1311974 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B2492345 : Blo 1311974 2492345 := bstep (se 2 (by rfl) ⟨934629, by rfl⟩ : syracuseStep 2492345 = 1869259) B1869259
theorem B1968059 : Blo 1311974 1968059 := bstep (se 1 (by rfl) ⟨1476044, by rfl⟩ : syracuseStep 1968059 = 2952089) B2952089
theorem B1312699 : Blo 1311974 1312699 := bstep (se 1 (by rfl) ⟨984524, by rfl⟩ : syracuseStep 1312699 = 1969049) B1969049
theorem B6645725 : Blo 1311974 6645725 := bstep (se 3 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 6645725 = 2492147) B2492147
theorem B1968119 : Blo 1311974 1968119 := bstep (se 1 (by rfl) ⟨1476089, by rfl⟩ : syracuseStep 1968119 = 2952179) B2952179
theorem B1312775 : Blo 1311974 1312775 := bstep (se 1 (by rfl) ⟨984581, by rfl⟩ : syracuseStep 1312775 = 1969163) B1969163
theorem B1968143 : Blo 1311974 1968143 := bstep (se 1 (by rfl) ⟨1476107, by rfl⟩ : syracuseStep 1968143 = 2952215) B2952215
theorem B2803727 : Blo 1311974 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B1312783 : Blo 1311974 1312783 := bstep (se 1 (by rfl) ⟨984587, by rfl⟩ : syracuseStep 1312783 = 1969175) B1969175
theorem B1968185 : Blo 1311974 1968185 := bstep (se 2 (by rfl) ⟨738069, by rfl⟩ : syracuseStep 1968185 = 1476139) B1476139
theorem B1312827 : Blo 1311974 1312827 := bstep (se 1 (by rfl) ⟨984620, by rfl⟩ : syracuseStep 1312827 = 1969241) B1969241
theorem B1968263 : Blo 1311974 1968263 := bstep (se 1 (by rfl) ⟨1476197, by rfl⟩ : syracuseStep 1968263 = 2952395) B2952395
theorem B1312903 : Blo 1311974 1312903 := bstep (se 1 (by rfl) ⟨984677, by rfl⟩ : syracuseStep 1312903 = 1969355) B1969355
theorem B1476751 : Blo 1311974 1476751 := bstep (se 1 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 1476751 = 2215127) B2215127
theorem B1312911 : Blo 1311974 1312911 := bstep (se 1 (by rfl) ⟨984683, by rfl⟩ : syracuseStep 1312911 = 1969367) B1969367
theorem B1968299 : Blo 1311974 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B1312955 : Blo 1311974 1312955 := bstep (se 1 (by rfl) ⟨984716, by rfl⟩ : syracuseStep 1312955 = 1969433) B1969433
theorem B1968329 : Blo 1311974 1968329 := bstep (se 2 (by rfl) ⟨738123, by rfl⟩ : syracuseStep 1968329 = 1476247) B1476247
theorem B1313031 : Blo 1311974 1313031 := bstep (se 1 (by rfl) ⟨984773, by rfl⟩ : syracuseStep 1313031 = 1969547) B1969547
theorem B2492687 : Blo 1311974 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B1313039 : Blo 1311974 1313039 := bstep (se 1 (by rfl) ⟨984779, by rfl⟩ : syracuseStep 1313039 = 1969559) B1969559
theorem B6646049 : Blo 1311974 6646049 := bstep (se 2 (by rfl) ⟨2492268, by rfl⟩ : syracuseStep 6646049 = 4984537) B4984537
theorem B4434209 : Blo 1311974 4434209 := bstep (se 2 (by rfl) ⟨1662828, by rfl⟩ : syracuseStep 4434209 = 3325657) B3325657
theorem B1968443 : Blo 1311974 1968443 := bstep (se 1 (by rfl) ⟨1476332, by rfl⟩ : syracuseStep 1968443 = 2952665) B2952665
theorem B1313083 : Blo 1311974 1313083 := bstep (se 1 (by rfl) ⟨984812, by rfl⟩ : syracuseStep 1313083 = 1969625) B1969625
theorem B2214263 : Blo 1311974 2214263 := bstep (se 1 (by rfl) ⟨1660697, by rfl⟩ : syracuseStep 2214263 = 3321395) B3321395
theorem B1968503 : Blo 1311974 1968503 := bstep (se 1 (by rfl) ⟨1476377, by rfl⟩ : syracuseStep 1968503 = 2952755) B2952755
theorem B1313159 : Blo 1311974 1313159 := bstep (se 1 (by rfl) ⟨984869, by rfl⟩ : syracuseStep 1313159 = 1969739) B1969739
theorem B1968527 : Blo 1311974 1968527 := bstep (se 1 (by rfl) ⟨1476395, by rfl⟩ : syracuseStep 1968527 = 2952791) B2952791
theorem B1313167 : Blo 1311974 1313167 := bstep (se 1 (by rfl) ⟨984875, by rfl⟩ : syracuseStep 1313167 = 1969751) B1969751
theorem B1968569 : Blo 1311974 1968569 := bstep (se 2 (by rfl) ⟨738213, by rfl⟩ : syracuseStep 1968569 = 1476427) B1476427
theorem B6834617 : Blo 1311974 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B1313211 : Blo 1311974 1313211 := bstep (se 1 (by rfl) ⟨984908, by rfl⟩ : syracuseStep 1313211 = 1969817) B1969817
theorem B7473617 : Blo 1311974 7473617 := bstep (se 2 (by rfl) ⟨2802606, by rfl⟩ : syracuseStep 7473617 = 5605213) B5605213
theorem B1968647 : Blo 1311974 1968647 := bstep (se 1 (by rfl) ⟨1476485, by rfl⟩ : syracuseStep 1968647 = 2952971) B2952971
theorem B1313287 : Blo 1311974 1313287 := bstep (se 1 (by rfl) ⟨984965, by rfl⟩ : syracuseStep 1313287 = 1969931) B1969931
theorem B1313295 : Blo 1311974 1313295 := bstep (se 1 (by rfl) ⟨984971, by rfl⟩ : syracuseStep 1313295 = 1969943) B1969943
theorem B4729373 : Blo 1311974 4729373 := bstep (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) B1773515
theorem B1968683 : Blo 1311974 1968683 := bstep (se 1 (by rfl) ⟨1476512, by rfl⟩ : syracuseStep 1968683 = 2953025) B2953025
theorem B1313339 : Blo 1311974 1313339 := bstep (se 1 (by rfl) ⟨985004, by rfl⟩ : syracuseStep 1313339 = 1970009) B1970009
theorem B5605949 : Blo 1311974 5605949 := bstep (se 3 (by rfl) ⟨1051115, by rfl⟩ : syracuseStep 5605949 = 2102231) B2102231
theorem B1968713 : Blo 1311974 1968713 := bstep (se 2 (by rfl) ⟨738267, by rfl⟩ : syracuseStep 1968713 = 1476535) B1476535
theorem B1870409 : Blo 1311974 1870409 := bstep (se 2 (by rfl) ⟨701403, by rfl⟩ : syracuseStep 1870409 = 1402807) B1402807
theorem B4983383 : Blo 1311974 4983383 := bstep (se 1 (by rfl) ⟨3737537, by rfl⟩ : syracuseStep 4983383 = 7475075) B7475075
theorem B6482551 : Blo 1311974 6482551 := bstep (se 1 (by rfl) ⟨4861913, by rfl⟩ : syracuseStep 6482551 = 9723827) B9723827
theorem B1477255 : Blo 1311974 1477255 := bstep (se 1 (by rfl) ⟨1107941, by rfl⟩ : syracuseStep 1477255 = 2215883) B2215883
theorem B1313415 : Blo 1311974 1313415 := bstep (se 1 (by rfl) ⟨985061, by rfl⟩ : syracuseStep 1313415 = 1970123) B1970123
theorem B1313423 : Blo 1311974 1313423 := bstep (se 1 (by rfl) ⟨985067, by rfl⟩ : syracuseStep 1313423 = 1970135) B1970135
theorem B1968827 : Blo 1311974 1968827 := bstep (se 1 (by rfl) ⟨1476620, by rfl⟩ : syracuseStep 1968827 = 2953241) B2953241
theorem B1313467 : Blo 1311974 1313467 := bstep (se 1 (by rfl) ⟨985100, by rfl⟩ : syracuseStep 1313467 = 1970201) B1970201
theorem B1968887 : Blo 1311974 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B1313543 : Blo 1311974 1313543 := bstep (se 1 (by rfl) ⟨985157, by rfl⟩ : syracuseStep 1313543 = 1970315) B1970315
theorem B1968911 : Blo 1311974 1968911 := bstep (se 1 (by rfl) ⟨1476683, by rfl⟩ : syracuseStep 1968911 = 2953367) B2953367
theorem B1313551 : Blo 1311974 1313551 := bstep (se 1 (by rfl) ⟨985163, by rfl⟩ : syracuseStep 1313551 = 1970327) B1970327
theorem B1968953 : Blo 1311974 1968953 := bstep (se 2 (by rfl) ⟨738357, by rfl⟩ : syracuseStep 1968953 = 1476715) B1476715
theorem B2214715 : Blo 1311974 2214715 := bstep (se 1 (by rfl) ⟨1661036, by rfl⟩ : syracuseStep 2214715 = 3322073) B3322073
theorem B1477435 : Blo 1311974 1477435 := bstep (se 1 (by rfl) ⟨1108076, by rfl⟩ : syracuseStep 1477435 = 2216153) B2216153
theorem B1313595 : Blo 1311974 1313595 := bstep (se 1 (by rfl) ⟨985196, by rfl⟩ : syracuseStep 1313595 = 1970393) B1970393
theorem B2952071 : Blo 1311974 2952071 := bstep (se 1 (by rfl) ⟨2214053, by rfl⟩ : syracuseStep 2952071 = 4428107) B4428107
theorem B1969031 : Blo 1311974 1969031 := bstep (se 1 (by rfl) ⟨1476773, by rfl⟩ : syracuseStep 1969031 = 2953547) B2953547
theorem B2804615 : Blo 1311974 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B1313671 : Blo 1311974 1313671 := bstep (se 1 (by rfl) ⟨985253, by rfl⟩ : syracuseStep 1313671 = 1970507) B1970507
theorem B1313679 : Blo 1311974 1313679 := bstep (se 1 (by rfl) ⟨985259, by rfl⟩ : syracuseStep 1313679 = 1970519) B1970519
theorem B1969067 : Blo 1311974 1969067 := bstep (se 1 (by rfl) ⟨1476800, by rfl⟩ : syracuseStep 1969067 = 2953601) B2953601
theorem B1313723 : Blo 1311974 1313723 := bstep (se 1 (by rfl) ⟨985292, by rfl⟩ : syracuseStep 1313723 = 1970585) B1970585
theorem B2214857 : Blo 1311974 2214857 := bstep (se 2 (by rfl) ⟨830571, by rfl⟩ : syracuseStep 2214857 = 1661143) B1661143
theorem B1969097 : Blo 1311974 1969097 := bstep (se 2 (by rfl) ⟨738411, by rfl⟩ : syracuseStep 1969097 = 1476823) B1476823
theorem B1313799 : Blo 1311974 1313799 := bstep (se 1 (by rfl) ⟨985349, by rfl⟩ : syracuseStep 1313799 = 1970699) B1970699
theorem B1313807 : Blo 1311974 1313807 := bstep (se 1 (by rfl) ⟨985355, by rfl⟩ : syracuseStep 1313807 = 1970711) B1970711
theorem B2952251 : Blo 1311974 2952251 := bstep (se 1 (by rfl) ⟨2214188, by rfl⟩ : syracuseStep 2952251 = 4428377) B4428377
theorem B1969211 : Blo 1311974 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B4983869 : Blo 1311974 4983869 := bstep (se 3 (by rfl) ⟨934475, by rfl⟩ : syracuseStep 4983869 = 1868951) B1868951
theorem B2493499 : Blo 1311974 2493499 := bstep (se 1 (by rfl) ⟨1870124, by rfl⟩ : syracuseStep 2493499 = 3740249) B3740249
theorem B1313851 : Blo 1311974 1313851 := bstep (se 1 (by rfl) ⟨985388, by rfl⟩ : syracuseStep 1313851 = 1970777) B1970777
theorem B1969271 : Blo 1311974 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B15969413 : Blo 1311974 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B2493575 : Blo 1311974 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B1313927 : Blo 1311974 1313927 := bstep (se 1 (by rfl) ⟨985445, by rfl⟩ : syracuseStep 1313927 = 1970891) B1970891
theorem B221367437 : Blo 1311974 221367437 := bstep (se 3 (by rfl) ⟨41506394, by rfl⟩ : syracuseStep 221367437 = 83012789) B83012789
theorem B1969295 : Blo 1311974 1969295 := bstep (se 1 (by rfl) ⟨1476971, by rfl⟩ : syracuseStep 1969295 = 2953943) B2953943
theorem B1313935 : Blo 1311974 1313935 := bstep (se 1 (by rfl) ⟨985451, by rfl⟩ : syracuseStep 1313935 = 1970903) B1970903
theorem B2952377 : Blo 1311974 2952377 := bstep (se 2 (by rfl) ⟨1107141, by rfl⟩ : syracuseStep 2952377 = 2214283) B2214283
theorem B1969337 : Blo 1311974 1969337 := bstep (se 2 (by rfl) ⟨738501, by rfl⟩ : syracuseStep 1969337 = 1477003) B1477003
theorem B60599501 : Blo 1311974 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B6647021 : Blo 1311974 6647021 := bstep (se 3 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 6647021 = 2492633) B2492633
theorem B1969415 : Blo 1311974 1969415 := bstep (se 1 (by rfl) ⟨1477061, by rfl⟩ : syracuseStep 1969415 = 2954123) B2954123
theorem B1477903 : Blo 1311974 1477903 := bstep (se 1 (by rfl) ⟨1108427, by rfl⟩ : syracuseStep 1477903 = 2216855) B2216855
theorem B3321121 : Blo 1311974 3321121 := bstep (se 2 (by rfl) ⟨1245420, by rfl⟩ : syracuseStep 3321121 = 2490841) B2490841
theorem B2805025 : Blo 1311974 2805025 := bstep (se 2 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 2805025 = 2103769) B2103769
theorem B1969451 : Blo 1311974 1969451 := bstep (se 1 (by rfl) ⟨1477088, by rfl⟩ : syracuseStep 1969451 = 2954177) B2954177
theorem B1969481 : Blo 1311974 1969481 := bstep (se 2 (by rfl) ⟨738555, by rfl⟩ : syracuseStep 1969481 = 1477111) B1477111
theorem B5049715 : Blo 1311974 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B4263283 : Blo 1311974 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B12610961 : Blo 1311974 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B1969595 : Blo 1311974 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B1969655 : Blo 1311974 1969655 := bstep (se 1 (by rfl) ⟨1477241, by rfl⟩ : syracuseStep 1969655 = 2954483) B2954483
theorem B2952719 : Blo 1311974 2952719 := bstep (se 1 (by rfl) ⟨2214539, by rfl⟩ : syracuseStep 2952719 = 4429079) B4429079
theorem B1969679 : Blo 1311974 1969679 := bstep (se 1 (by rfl) ⟨1477259, by rfl⟩ : syracuseStep 1969679 = 2954519) B2954519
theorem B2952737 : Blo 1311974 2952737 := bstep (se 2 (by rfl) ⟨1107276, by rfl⟩ : syracuseStep 2952737 = 2214553) B2214553
theorem B2493985 : Blo 1311974 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B9989675 : Blo 1311974 9989675 := bstep (se 1 (by rfl) ⟨7492256, by rfl⟩ : syracuseStep 9989675 = 14984513) B14984513
theorem B1969721 : Blo 1311974 1969721 := bstep (se 2 (by rfl) ⟨738645, by rfl⟩ : syracuseStep 1969721 = 1477291) B1477291
theorem B3739223 : Blo 1311974 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B2805367 : Blo 1311974 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B2215559 : Blo 1311974 2215559 := bstep (se 1 (by rfl) ⟨1661669, by rfl⟩ : syracuseStep 2215559 = 3323339) B3323339
theorem B1969799 : Blo 1311974 1969799 := bstep (se 1 (by rfl) ⟨1477349, by rfl⟩ : syracuseStep 1969799 = 2954699) B2954699
theorem B1969835 : Blo 1311974 1969835 := bstep (se 1 (by rfl) ⟨1477376, by rfl⟩ : syracuseStep 1969835 = 2954753) B2954753
theorem B1969865 : Blo 1311974 1969865 := bstep (se 2 (by rfl) ⟨738699, by rfl⟩ : syracuseStep 1969865 = 1477399) B1477399
theorem B95891201 : Blo 1311974 95891201 := bstep (se 2 (by rfl) ⟨35959200, by rfl⟩ : syracuseStep 95891201 = 71918401) B71918401
theorem B1969979 : Blo 1311974 1969979 := bstep (se 1 (by rfl) ⟨1477484, by rfl⟩ : syracuseStep 1969979 = 2954969) B2954969
theorem B8408947 : Blo 1311974 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B3321719 : Blo 1311974 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B2953079 : Blo 1311974 2953079 := bstep (se 1 (by rfl) ⟨2214809, by rfl⟩ : syracuseStep 2953079 = 4429619) B4429619
theorem B1970039 : Blo 1311974 1970039 := bstep (se 1 (by rfl) ⟨1477529, by rfl⟩ : syracuseStep 1970039 = 2955059) B2955059
theorem B2494327 : Blo 1311974 2494327 := bstep (se 1 (by rfl) ⟨1870745, by rfl⟩ : syracuseStep 2494327 = 3741491) B3741491
theorem B1970063 : Blo 1311974 1970063 := bstep (se 1 (by rfl) ⟨1477547, by rfl⟩ : syracuseStep 1970063 = 2955095) B2955095
theorem B22425497 : Blo 1311974 22425497 := bstep (se 2 (by rfl) ⟨8409561, by rfl⟩ : syracuseStep 22425497 = 16819123) B16819123
theorem B12627875 : Blo 1311974 12627875 := bstep (se 1 (by rfl) ⟨9470906, by rfl⟩ : syracuseStep 12627875 = 18941813) B18941813
theorem B1970105 : Blo 1311974 1970105 := bstep (se 2 (by rfl) ⟨738789, by rfl⟩ : syracuseStep 1970105 = 1477579) B1477579
theorem B1970183 : Blo 1311974 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B6647831 : Blo 1311974 6647831 := bstep (se 1 (by rfl) ⟨4985873, by rfl⟩ : syracuseStep 6647831 = 9971747) B9971747
theorem B2953259 : Blo 1311974 2953259 := bstep (se 1 (by rfl) ⟨2214944, by rfl⟩ : syracuseStep 2953259 = 4429889) B4429889
theorem B1970219 : Blo 1311974 1970219 := bstep (se 1 (by rfl) ⟨1477664, by rfl⟩ : syracuseStep 1970219 = 2955329) B2955329
theorem B1970249 : Blo 1311974 1970249 := bstep (se 2 (by rfl) ⟨738843, by rfl⟩ : syracuseStep 1970249 = 1477687) B1477687
theorem B27324533 : Blo 1311974 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1970363 : Blo 1311974 1970363 := bstep (se 1 (by rfl) ⟨1477772, by rfl⟩ : syracuseStep 1970363 = 2955545) B2955545
theorem B6394049 : Blo 1311974 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B46723313 : Blo 1311974 46723313 := bstep (se 2 (by rfl) ⟨17521242, by rfl⟩ : syracuseStep 46723313 = 35042485) B35042485
theorem B18919669 : Blo 1311974 18919669 := bstep (se 5 (by rfl) ⟨886859, by rfl⟩ : syracuseStep 18919669 = 1773719) B1773719
theorem B1970423 : Blo 1311974 1970423 := bstep (se 1 (by rfl) ⟨1477817, by rfl⟩ : syracuseStep 1970423 = 2955635) B2955635
theorem B2216207 : Blo 1311974 2216207 := bstep (se 1 (by rfl) ⟨1662155, by rfl⟩ : syracuseStep 2216207 = 3324311) B3324311
theorem B1970447 : Blo 1311974 1970447 := bstep (se 1 (by rfl) ⟨1477835, by rfl⟩ : syracuseStep 1970447 = 2955671) B2955671
theorem B1970489 : Blo 1311974 1970489 := bstep (se 2 (by rfl) ⟨738933, by rfl⟩ : syracuseStep 1970489 = 1477867) B1477867
theorem B15962503 : Blo 1311974 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B1577351 : Blo 1311974 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1970567 : Blo 1311974 1970567 := bstep (se 1 (by rfl) ⟨1477925, by rfl⟩ : syracuseStep 1970567 = 2955851) B2955851
theorem B2953619 : Blo 1311974 2953619 := bstep (se 1 (by rfl) ⟨2215214, by rfl⟩ : syracuseStep 2953619 = 4430429) B4430429
theorem B1970603 : Blo 1311974 1970603 := bstep (se 1 (by rfl) ⟨1477952, by rfl⟩ : syracuseStep 1970603 = 2955905) B2955905
theorem B3740089 : Blo 1311974 3740089 := bstep (se 2 (by rfl) ⟨1402533, by rfl⟩ : syracuseStep 3740089 = 2805067) B2805067
theorem B2953673 : Blo 1311974 2953673 := bstep (se 2 (by rfl) ⟨1107627, by rfl⟩ : syracuseStep 2953673 = 2215255) B2215255
theorem B1970633 : Blo 1311974 1970633 := bstep (se 2 (by rfl) ⟨738987, by rfl⟩ : syracuseStep 1970633 = 1477975) B1477975
theorem B4985297 : Blo 1311974 4985297 := bstep (se 2 (by rfl) ⟨1869486, by rfl⟩ : syracuseStep 4985297 = 3738973) B3738973
theorem B6312401 : Blo 1311974 6312401 := bstep (se 2 (by rfl) ⟨2367150, by rfl⟩ : syracuseStep 6312401 = 4734301) B4734301
theorem B21303773 : Blo 1311974 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B12800477 : Blo 1311974 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B5607947 : Blo 1311974 5607947 := bstep (se 1 (by rfl) ⟨4205960, by rfl⟩ : syracuseStep 5607947 = 8411921) B8411921
theorem B1970747 : Blo 1311974 1970747 := bstep (se 1 (by rfl) ⟨1478060, by rfl⟩ : syracuseStep 1970747 = 2956121) B2956121
theorem B1970807 : Blo 1311974 1970807 := bstep (se 1 (by rfl) ⟨1478105, by rfl⟩ : syracuseStep 1970807 = 2956211) B2956211
theorem B1970831 : Blo 1311974 1970831 := bstep (se 1 (by rfl) ⟨1478123, by rfl⟩ : syracuseStep 1970831 = 2956247) B2956247
theorem B1970873 : Blo 1311974 1970873 := bstep (se 2 (by rfl) ⟨739077, by rfl⟩ : syracuseStep 1970873 = 1478155) B1478155
theorem B1577659 : Blo 1311974 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B1970951 : Blo 1311974 1970951 := bstep (se 1 (by rfl) ⟨1478213, by rfl⟩ : syracuseStep 1970951 = 2956427) B2956427
theorem B3740431 : Blo 1311974 3740431 := bstep (se 1 (by rfl) ⟨2805323, by rfl⟩ : syracuseStep 3740431 = 5610647) B5610647
theorem B2216747 : Blo 1311974 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B4731763 : Blo 1311974 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B3740705 : Blo 1311974 3740705 := bstep (se 2 (by rfl) ⟨1402764, by rfl⟩ : syracuseStep 3740705 = 2805529) B2805529
theorem B14947415 : Blo 1311974 14947415 := bstep (se 1 (by rfl) ⟨11210561, by rfl⟩ : syracuseStep 14947415 = 22421123) B22421123
theorem B272667779 : Blo 1311974 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B3323015 : Blo 1311974 3323015 := bstep (se 1 (by rfl) ⟨2492261, by rfl⟩ : syracuseStep 3323015 = 4984523) B4984523
theorem B2954375 : Blo 1311974 2954375 := bstep (se 1 (by rfl) ⟨2215781, by rfl⟩ : syracuseStep 2954375 = 4431563) B4431563
theorem B3323065 : Blo 1311974 3323065 := bstep (se 2 (by rfl) ⟨1246149, by rfl⟩ : syracuseStep 3323065 = 2492299) B2492299
theorem B2217145 : Blo 1311974 2217145 := bstep (se 2 (by rfl) ⟨831429, by rfl⟩ : syracuseStep 2217145 = 1662859) B1662859
theorem B2954555 : Blo 1311974 2954555 := bstep (se 1 (by rfl) ⟨2215916, by rfl⟩ : syracuseStep 2954555 = 4431833) B4431833
theorem B2102647 : Blo 1311974 2102647 := bstep (se 1 (by rfl) ⟨1576985, by rfl⟩ : syracuseStep 2102647 = 3153971) B3153971
theorem B4429241 : Blo 1311974 4429241 := bstep (se 2 (by rfl) ⟨1660965, by rfl⟩ : syracuseStep 4429241 = 3321931) B3321931
theorem B2954681 : Blo 1311974 2954681 := bstep (se 2 (by rfl) ⟨1108005, by rfl⟩ : syracuseStep 2954681 = 2216011) B2216011
theorem B3741319 : Blo 1311974 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B3323663 : Blo 1311974 3323663 := bstep (se 1 (by rfl) ⟨2492747, by rfl⟩ : syracuseStep 3323663 = 4985495) B4985495
theorem B2955023 : Blo 1311974 2955023 := bstep (se 1 (by rfl) ⟨2216267, by rfl⟩ : syracuseStep 2955023 = 4432535) B4432535
theorem B2955041 : Blo 1311974 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B1775417 : Blo 1311974 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B4429835 : Blo 1311974 4429835 := bstep (se 1 (by rfl) ⟨3322376, by rfl⟩ : syracuseStep 4429835 = 6644753) B6644753
theorem B3741707 : Blo 1311974 3741707 := bstep (se 1 (by rfl) ⟨2806280, by rfl⟩ : syracuseStep 3741707 = 5612561) B5612561
theorem B21305389 : Blo 1311974 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B4986967 : Blo 1311974 4986967 := bstep (se 1 (by rfl) ⟨3740225, by rfl⟩ : syracuseStep 4986967 = 7480451) B7480451
theorem B4429943 : Blo 1311974 4429943 := bstep (se 1 (by rfl) ⟨3322457, by rfl⟩ : syracuseStep 4429943 = 6644915) B6644915
theorem B2955383 : Blo 1311974 2955383 := bstep (se 1 (by rfl) ⟨2216537, by rfl⟩ : syracuseStep 2955383 = 4433075) B4433075
theorem B2955563 : Blo 1311974 2955563 := bstep (se 1 (by rfl) ⟨2216672, by rfl⟩ : syracuseStep 2955563 = 4433345) B4433345
theorem B4987271 : Blo 1311974 4987271 := bstep (se 1 (by rfl) ⟨3740453, by rfl⟩ : syracuseStep 4987271 = 7480907) B7480907
theorem B3324361 : Blo 1311974 3324361 := bstep (se 2 (by rfl) ⟨1246635, by rfl⟩ : syracuseStep 3324361 = 2493271) B2493271
theorem B10648093 : Blo 1311974 10648093 := bstep (se 3 (by rfl) ⟨1996517, by rfl⟩ : syracuseStep 10648093 = 3993035) B3993035
theorem B4987453 : Blo 1311974 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B3324503 : Blo 1311974 3324503 := bstep (se 1 (by rfl) ⟨2493377, by rfl⟩ : syracuseStep 3324503 = 4986755) B4986755
theorem B2955923 : Blo 1311974 2955923 := bstep (se 1 (by rfl) ⟨2216942, by rfl⟩ : syracuseStep 2955923 = 4433885) B4433885
theorem B4430537 : Blo 1311974 4430537 := bstep (se 2 (by rfl) ⟨1661451, by rfl⟩ : syracuseStep 4430537 = 3322903) B3322903
theorem B2955977 : Blo 1311974 2955977 := bstep (se 2 (by rfl) ⟨1108491, by rfl⟩ : syracuseStep 2955977 = 2216983) B2216983
theorem B43170565 : Blo 1311974 43170565 := bstep (se 4 (by rfl) ⟨4047240, by rfl⟩ : syracuseStep 43170565 = 8094481) B8094481
theorem B4733711 : Blo 1311974 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B40410019 : Blo 1311974 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B6650909 : Blo 1311974 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B2841659 : Blo 1311974 2841659 := bstep (se 1 (by rfl) ⟨2131244, by rfl⟩ : syracuseStep 2841659 = 4262489) B4262489
theorem B25222535 : Blo 1311974 25222535 := bstep (se 1 (by rfl) ⟨18916901, by rfl⟩ : syracuseStep 25222535 = 37833803) B37833803
theorem B4431239 : Blo 1311974 4431239 := bstep (se 1 (by rfl) ⟨3323429, by rfl⟩ : syracuseStep 4431239 = 6646859) B6646859
theorem B7478675 : Blo 1311974 7478675 := bstep (se 1 (by rfl) ⟨5609006, by rfl⟩ : syracuseStep 7478675 = 11218013) B11218013
theorem B6651395 : Blo 1311974 6651395 := bstep (se 1 (by rfl) ⟨4988546, by rfl⟩ : syracuseStep 6651395 = 9977093) B9977093
theorem B3546683 : Blo 1311974 3546683 := bstep (se 1 (by rfl) ⟨2660012, by rfl⟩ : syracuseStep 3546683 = 5320025) B5320025
theorem B2367035 : Blo 1311974 2367035 := bstep (se 1 (by rfl) ⟨1775276, by rfl⟩ : syracuseStep 2367035 = 3550553) B3550553
theorem B7577317 : Blo 1311974 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B6643457 : Blo 1311974 6643457 := bstep (se 2 (by rfl) ⟨2491296, by rfl⟩ : syracuseStep 6643457 = 4982593) B4982593
theorem B4431617 : Blo 1311974 4431617 := bstep (se 2 (by rfl) ⟨1661856, by rfl⟩ : syracuseStep 4431617 = 3323713) B3323713
theorem B1662763 : Blo 1311974 1662763 := bstep (se 1 (by rfl) ⟨1247072, by rfl⟩ : syracuseStep 1662763 = 2494145) B2494145
theorem B37855025 : Blo 1311974 37855025 := bstep (se 2 (by rfl) ⟨14195634, by rfl⟩ : syracuseStep 37855025 = 28391269) B28391269
theorem B10649393 : Blo 1311974 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B26935091 : Blo 1311974 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B21307211 : Blo 1311974 21307211 := bstep (se 1 (by rfl) ⟨15980408, by rfl⟩ : syracuseStep 21307211 = 31960817) B31960817
theorem B7479175 : Blo 1311974 7479175 := bstep (se 1 (by rfl) ⟨5609381, by rfl⟩ : syracuseStep 7479175 = 11218763) B11218763
theorem B6307787 : Blo 1311974 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B4431887 : Blo 1311974 4431887 := bstep (se 1 (by rfl) ⟨3323915, by rfl⟩ : syracuseStep 4431887 = 6647831) B6647831
theorem B2490887 : Blo 1311974 2490887 := bstep (se 1 (by rfl) ⟨1868165, by rfl⟩ : syracuseStep 2490887 = 3736331) B3736331
theorem B21283337 : Blo 1311974 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B4432481 : Blo 1311974 4432481 := bstep (se 2 (by rfl) ⟨1662180, by rfl⟩ : syracuseStep 4432481 = 3324361) B3324361
theorem B4260487 : Blo 1311974 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B14197457 : Blo 1311974 14197457 := bstep (se 2 (by rfl) ⟨5324046, by rfl⟩ : syracuseStep 14197457 = 10648093) B10648093
theorem B8643401 : Blo 1311974 8643401 := bstep (se 2 (by rfl) ⟨3241275, by rfl⟩ : syracuseStep 8643401 = 6482551) B6482551
theorem B2802539 : Blo 1311974 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B2491411 : Blo 1311974 2491411 := bstep (se 1 (by rfl) ⟨1868558, by rfl⟩ : syracuseStep 2491411 = 3737117) B3737117
theorem B1868923 : Blo 1311974 1868923 := bstep (se 1 (by rfl) ⟨1401692, by rfl⟩ : syracuseStep 1868923 = 2803385) B2803385
theorem B6309017 : Blo 1311974 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B53880025 : Blo 1311974 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B1312039 : Blo 1311974 1312039 := bstep (se 1 (by rfl) ⟨984029, by rfl⟩ : syracuseStep 1312039 = 1968059) B1968059
theorem B1312079 : Blo 1311974 1312079 := bstep (se 1 (by rfl) ⟨984059, by rfl⟩ : syracuseStep 1312079 = 1968119) B1968119
theorem B1312095 : Blo 1311974 1312095 := bstep (se 1 (by rfl) ⟨984071, by rfl⟩ : syracuseStep 1312095 = 1968143) B1968143
theorem B1869151 : Blo 1311974 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B1312123 : Blo 1311974 1312123 := bstep (se 1 (by rfl) ⟨984092, by rfl⟩ : syracuseStep 1312123 = 1968185) B1968185
theorem B1312175 : Blo 1311974 1312175 := bstep (se 1 (by rfl) ⟨984131, by rfl⟩ : syracuseStep 1312175 = 1968263) B1968263
theorem B1312199 : Blo 1311974 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B1312219 : Blo 1311974 1312219 := bstep (se 1 (by rfl) ⟨984164, by rfl⟩ : syracuseStep 1312219 = 1968329) B1968329
theorem B1312295 : Blo 1311974 1312295 := bstep (se 1 (by rfl) ⟨984221, by rfl⟩ : syracuseStep 1312295 = 1968443) B1968443
theorem B9971261 : Blo 1311974 9971261 := bstep (se 3 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 9971261 = 3739223) B3739223
theorem B1476175 : Blo 1311974 1476175 := bstep (se 1 (by rfl) ⟨1107131, by rfl⟩ : syracuseStep 1476175 = 2214263) B2214263
theorem B1312335 : Blo 1311974 1312335 := bstep (se 1 (by rfl) ⟨984251, by rfl⟩ : syracuseStep 1312335 = 1968503) B1968503
theorem B1312351 : Blo 1311974 1312351 := bstep (se 1 (by rfl) ⟨984263, by rfl⟩ : syracuseStep 1312351 = 1968527) B1968527
theorem B1312379 : Blo 1311974 1312379 := bstep (se 1 (by rfl) ⟨984284, by rfl⟩ : syracuseStep 1312379 = 1968569) B1968569
theorem B4556411 : Blo 1311974 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B4982411 : Blo 1311974 4982411 := bstep (se 1 (by rfl) ⟨3736808, by rfl⟩ : syracuseStep 4982411 = 7473617) B7473617
theorem B1312431 : Blo 1311974 1312431 := bstep (se 1 (by rfl) ⟨984323, by rfl⟩ : syracuseStep 1312431 = 1968647) B1968647
theorem B1312455 : Blo 1311974 1312455 := bstep (se 1 (by rfl) ⟨984341, by rfl⟩ : syracuseStep 1312455 = 1968683) B1968683
theorem B3737299 : Blo 1311974 3737299 := bstep (se 1 (by rfl) ⟨2802974, by rfl⟩ : syracuseStep 3737299 = 5605949) B5605949
theorem B1312475 : Blo 1311974 1312475 := bstep (se 1 (by rfl) ⟨984356, by rfl⟩ : syracuseStep 1312475 = 1968713) B1968713
theorem B1312551 : Blo 1311974 1312551 := bstep (se 1 (by rfl) ⟨984413, by rfl⟩ : syracuseStep 1312551 = 1968827) B1968827
theorem B2803529 : Blo 1311974 2803529 := bstep (se 2 (by rfl) ⟨1051323, by rfl⟩ : syracuseStep 2803529 = 2102647) B2102647
theorem B1312591 : Blo 1311974 1312591 := bstep (se 1 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 1312591 = 1968887) B1968887
theorem B1312607 : Blo 1311974 1312607 := bstep (se 1 (by rfl) ⟨984455, by rfl⟩ : syracuseStep 1312607 = 1968911) B1968911
theorem B3155807 : Blo 1311974 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B1312635 : Blo 1311974 1312635 := bstep (se 1 (by rfl) ⟨984476, by rfl⟩ : syracuseStep 1312635 = 1968953) B1968953
theorem B1968047 : Blo 1311974 1968047 := bstep (se 1 (by rfl) ⟨1476035, by rfl⟩ : syracuseStep 1968047 = 2952071) B2952071
theorem B1312687 : Blo 1311974 1312687 := bstep (se 1 (by rfl) ⟨984515, by rfl⟩ : syracuseStep 1312687 = 1969031) B1969031
theorem B1869743 : Blo 1311974 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B1312711 : Blo 1311974 1312711 := bstep (se 1 (by rfl) ⟨984533, by rfl⟩ : syracuseStep 1312711 = 1969067) B1969067
theorem B1476571 : Blo 1311974 1476571 := bstep (se 1 (by rfl) ⟨1107428, by rfl⟩ : syracuseStep 1476571 = 2214857) B2214857
theorem B1312731 : Blo 1311974 1312731 := bstep (se 1 (by rfl) ⟨984548, by rfl⟩ : syracuseStep 1312731 = 1969097) B1969097
theorem B1968137 : Blo 1311974 1968137 := bstep (se 2 (by rfl) ⟨738051, by rfl⟩ : syracuseStep 1968137 = 1476103) B1476103
theorem B4433939 : Blo 1311974 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B1968167 : Blo 1311974 1968167 := bstep (se 1 (by rfl) ⟨1476125, by rfl⟩ : syracuseStep 1968167 = 2952251) B2952251
theorem B1894439 : Blo 1311974 1894439 := bstep (se 1 (by rfl) ⟨1420829, by rfl⟩ : syracuseStep 1894439 = 2841659) B2841659
theorem B1312807 : Blo 1311974 1312807 := bstep (se 1 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 1312807 = 1969211) B1969211
theorem B1312847 : Blo 1311974 1312847 := bstep (se 1 (by rfl) ⟨984635, by rfl⟩ : syracuseStep 1312847 = 1969271) B1969271
theorem B1312863 : Blo 1311974 1312863 := bstep (se 1 (by rfl) ⟨984647, by rfl⟩ : syracuseStep 1312863 = 1969295) B1969295
theorem B1968251 : Blo 1311974 1968251 := bstep (se 1 (by rfl) ⟨1476188, by rfl⟩ : syracuseStep 1968251 = 2952377) B2952377
theorem B1312891 : Blo 1311974 1312891 := bstep (se 1 (by rfl) ⟨984668, by rfl⟩ : syracuseStep 1312891 = 1969337) B1969337
theorem B1312943 : Blo 1311974 1312943 := bstep (se 1 (by rfl) ⟨984707, by rfl⟩ : syracuseStep 1312943 = 1969415) B1969415
theorem B1312967 : Blo 1311974 1312967 := bstep (se 1 (by rfl) ⟨984725, by rfl⟩ : syracuseStep 1312967 = 1969451) B1969451
theorem B1312987 : Blo 1311974 1312987 := bstep (se 1 (by rfl) ⟨984740, by rfl⟩ : syracuseStep 1312987 = 1969481) B1969481
theorem B1968377 : Blo 1311974 1968377 := bstep (se 2 (by rfl) ⟨738141, by rfl⟩ : syracuseStep 1968377 = 1476283) B1476283
theorem B8407307 : Blo 1311974 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B1313063 : Blo 1311974 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B10103089 : Blo 1311974 10103089 := bstep (se 2 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 10103089 = 7577317) B7577317
theorem B1313103 : Blo 1311974 1313103 := bstep (se 1 (by rfl) ⟨984827, by rfl⟩ : syracuseStep 1313103 = 1969655) B1969655
theorem B4434263 : Blo 1311974 4434263 := bstep (se 1 (by rfl) ⟨3325697, by rfl⟩ : syracuseStep 4434263 = 6651395) B6651395
theorem B1968479 : Blo 1311974 1968479 := bstep (se 1 (by rfl) ⟨1476359, by rfl⟩ : syracuseStep 1968479 = 2952719) B2952719
theorem B1313119 : Blo 1311974 1313119 := bstep (se 1 (by rfl) ⟨984839, by rfl⟩ : syracuseStep 1313119 = 1969679) B1969679
theorem B1968491 : Blo 1311974 1968491 := bstep (se 1 (by rfl) ⟨1476368, by rfl⟩ : syracuseStep 1968491 = 2952737) B2952737
theorem B1313147 : Blo 1311974 1313147 := bstep (se 1 (by rfl) ⟨984860, by rfl⟩ : syracuseStep 1313147 = 1969721) B1969721
theorem B1477039 : Blo 1311974 1477039 := bstep (se 1 (by rfl) ⟨1107779, by rfl⟩ : syracuseStep 1477039 = 2215559) B2215559
theorem B1313199 : Blo 1311974 1313199 := bstep (se 1 (by rfl) ⟨984899, by rfl⟩ : syracuseStep 1313199 = 1969799) B1969799
theorem B1313223 : Blo 1311974 1313223 := bstep (se 1 (by rfl) ⟨984917, by rfl⟩ : syracuseStep 1313223 = 1969835) B1969835
theorem B1313243 : Blo 1311974 1313243 := bstep (se 1 (by rfl) ⟨984932, by rfl⟩ : syracuseStep 1313243 = 1969865) B1969865
theorem B9972233 : Blo 1311974 9972233 := bstep (se 2 (by rfl) ⟨3739587, by rfl⟩ : syracuseStep 9972233 = 7479175) B7479175
theorem B1313319 : Blo 1311974 1313319 := bstep (se 1 (by rfl) ⟨984989, by rfl⟩ : syracuseStep 1313319 = 1969979) B1969979
theorem B2214479 : Blo 1311974 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B1968719 : Blo 1311974 1968719 := bstep (se 1 (by rfl) ⟨1476539, by rfl⟩ : syracuseStep 1968719 = 2953079) B2953079
theorem B1313359 : Blo 1311974 1313359 := bstep (se 1 (by rfl) ⟨985019, by rfl⟩ : syracuseStep 1313359 = 1970039) B1970039
theorem B1313375 : Blo 1311974 1313375 := bstep (se 1 (by rfl) ⟨985031, by rfl⟩ : syracuseStep 1313375 = 1970063) B1970063
theorem B1313403 : Blo 1311974 1313403 := bstep (se 1 (by rfl) ⟨985052, by rfl⟩ : syracuseStep 1313403 = 1970105) B1970105
theorem B4205191 : Blo 1311974 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B1313455 : Blo 1311974 1313455 := bstep (se 1 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 1313455 = 1970183) B1970183
theorem B1968839 : Blo 1311974 1968839 := bstep (se 1 (by rfl) ⟨1476629, by rfl⟩ : syracuseStep 1968839 = 2953259) B2953259
theorem B1313479 : Blo 1311974 1313479 := bstep (se 1 (by rfl) ⟨985109, by rfl⟩ : syracuseStep 1313479 = 1970219) B1970219
theorem B1313499 : Blo 1311974 1313499 := bstep (se 1 (by rfl) ⟨985124, by rfl⟩ : syracuseStep 1313499 = 1970249) B1970249
theorem B1313575 : Blo 1311974 1313575 := bstep (se 1 (by rfl) ⟨985181, by rfl⟩ : syracuseStep 1313575 = 1970363) B1970363
theorem B4262699 : Blo 1311974 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B31148875 : Blo 1311974 31148875 := bstep (se 1 (by rfl) ⟨23361656, by rfl⟩ : syracuseStep 31148875 = 46723313) B46723313
theorem B1313615 : Blo 1311974 1313615 := bstep (se 1 (by rfl) ⟨985211, by rfl⟩ : syracuseStep 1313615 = 1970423) B1970423
theorem B1477471 : Blo 1311974 1477471 := bstep (se 1 (by rfl) ⟨1108103, by rfl⟩ : syracuseStep 1477471 = 2216207) B2216207
theorem B1313631 : Blo 1311974 1313631 := bstep (se 1 (by rfl) ⟨985223, by rfl⟩ : syracuseStep 1313631 = 1970447) B1970447
theorem B1969001 : Blo 1311974 1969001 := bstep (se 2 (by rfl) ⟨738375, by rfl⟩ : syracuseStep 1969001 = 1476751) B1476751
theorem B1313659 : Blo 1311974 1313659 := bstep (se 1 (by rfl) ⟨985244, by rfl⟩ : syracuseStep 1313659 = 1970489) B1970489
theorem B1313711 : Blo 1311974 1313711 := bstep (se 1 (by rfl) ⟨985283, by rfl⟩ : syracuseStep 1313711 = 1970567) B1970567
theorem B1969079 : Blo 1311974 1969079 := bstep (se 1 (by rfl) ⟨1476809, by rfl⟩ : syracuseStep 1969079 = 2953619) B2953619
theorem B1895351 : Blo 1311974 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B1313735 : Blo 1311974 1313735 := bstep (se 1 (by rfl) ⟨985301, by rfl⟩ : syracuseStep 1313735 = 1970603) B1970603
theorem B1969115 : Blo 1311974 1969115 := bstep (se 1 (by rfl) ⟨1476836, by rfl⟩ : syracuseStep 1969115 = 2953673) B2953673
theorem B1313755 : Blo 1311974 1313755 := bstep (se 1 (by rfl) ⟨985316, by rfl⟩ : syracuseStep 1313755 = 1970633) B1970633
theorem B25226225 : Blo 1311974 25226225 := bstep (se 2 (by rfl) ⟨9459834, by rfl⟩ : syracuseStep 25226225 = 18919669) B18919669
theorem B3738631 : Blo 1311974 3738631 := bstep (se 1 (by rfl) ⟨2803973, by rfl⟩ : syracuseStep 3738631 = 5607947) B5607947
theorem B1313831 : Blo 1311974 1313831 := bstep (se 1 (by rfl) ⟨985373, by rfl⟩ : syracuseStep 1313831 = 1970747) B1970747
theorem B1313871 : Blo 1311974 1313871 := bstep (se 1 (by rfl) ⟨985403, by rfl⟩ : syracuseStep 1313871 = 1970807) B1970807
theorem B1313887 : Blo 1311974 1313887 := bstep (se 1 (by rfl) ⟨985415, by rfl⟩ : syracuseStep 1313887 = 1970831) B1970831
theorem B1313915 : Blo 1311974 1313915 := bstep (se 1 (by rfl) ⟨985436, by rfl⟩ : syracuseStep 1313915 = 1970873) B1970873
theorem B1313967 : Blo 1311974 1313967 := bstep (se 1 (by rfl) ⟨985475, by rfl⟩ : syracuseStep 1313967 = 1970951) B1970951
theorem B1477831 : Blo 1311974 1477831 := bstep (se 1 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 1477831 = 2216747) B2216747
theorem B2493803 : Blo 1311974 2493803 := bstep (se 1 (by rfl) ⟨1870352, by rfl⟩ : syracuseStep 2493803 = 3740705) B3740705
theorem B9964943 : Blo 1311974 9964943 := bstep (se 1 (by rfl) ⟨7473707, by rfl⟩ : syracuseStep 9964943 = 14947415) B14947415
theorem B6647183 : Blo 1311974 6647183 := bstep (se 1 (by rfl) ⟨4985387, by rfl⟩ : syracuseStep 6647183 = 9970775) B9970775
theorem B2215343 : Blo 1311974 2215343 := bstep (se 1 (by rfl) ⟨1661507, by rfl⟩ : syracuseStep 2215343 = 3323015) B3323015
theorem B1969583 : Blo 1311974 1969583 := bstep (se 1 (by rfl) ⟨1477187, by rfl⟩ : syracuseStep 1969583 = 2954375) B2954375
theorem B1969673 : Blo 1311974 1969673 := bstep (se 2 (by rfl) ⟨738627, by rfl⟩ : syracuseStep 1969673 = 1477255) B1477255
theorem B1969703 : Blo 1311974 1969703 := bstep (se 1 (by rfl) ⟨1477277, by rfl⟩ : syracuseStep 1969703 = 2954555) B2954555
theorem B2952827 : Blo 1311974 2952827 := bstep (se 1 (by rfl) ⟨2214620, by rfl⟩ : syracuseStep 2952827 = 4429241) B4429241
theorem B1969787 : Blo 1311974 1969787 := bstep (se 1 (by rfl) ⟨1477340, by rfl⟩ : syracuseStep 1969787 = 2954681) B2954681
theorem B57560753 : Blo 1311974 57560753 := bstep (se 2 (by rfl) ⟨21585282, by rfl⟩ : syracuseStep 57560753 = 43170565) B43170565
theorem B4206269 : Blo 1311974 4206269 := bstep (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) B1577351
theorem B2952953 : Blo 1311974 2952953 := bstep (se 2 (by rfl) ⟨1107357, by rfl⟩ : syracuseStep 2952953 = 2214715) B2214715
theorem B1969913 : Blo 1311974 1969913 := bstep (se 2 (by rfl) ⟨738717, by rfl⟩ : syracuseStep 1969913 = 1477435) B1477435
theorem B2215775 : Blo 1311974 2215775 := bstep (se 1 (by rfl) ⟨1661831, by rfl⟩ : syracuseStep 2215775 = 3323663) B3323663
theorem B1970015 : Blo 1311974 1970015 := bstep (se 1 (by rfl) ⟨1477511, by rfl⟩ : syracuseStep 1970015 = 2955023) B2955023
theorem B1970027 : Blo 1311974 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B9973691 : Blo 1311974 9973691 := bstep (se 1 (by rfl) ⟨7480268, by rfl⟩ : syracuseStep 9973691 = 14960537) B14960537
theorem B2953223 : Blo 1311974 2953223 := bstep (se 1 (by rfl) ⟨2214917, by rfl⟩ : syracuseStep 2953223 = 4429835) B4429835
theorem B2494471 : Blo 1311974 2494471 := bstep (se 1 (by rfl) ⟨1870853, by rfl⟩ : syracuseStep 2494471 = 3741707) B3741707
theorem B2953295 : Blo 1311974 2953295 := bstep (se 1 (by rfl) ⟨2214971, by rfl⟩ : syracuseStep 2953295 = 4429943) B4429943
theorem B1970255 : Blo 1311974 1970255 := bstep (se 1 (by rfl) ⟨1477691, by rfl⟩ : syracuseStep 1970255 = 2955383) B2955383
theorem B1970375 : Blo 1311974 1970375 := bstep (se 1 (by rfl) ⟨1477781, by rfl⟩ : syracuseStep 1970375 = 2955563) B2955563
theorem B1970537 : Blo 1311974 1970537 := bstep (se 2 (by rfl) ⟨738951, by rfl⟩ : syracuseStep 1970537 = 1477903) B1477903
theorem B4428161 : Blo 1311974 4428161 := bstep (se 2 (by rfl) ⟨1660560, by rfl⟩ : syracuseStep 4428161 = 3321121) B3321121
theorem B3740033 : Blo 1311974 3740033 := bstep (se 2 (by rfl) ⟨1402512, by rfl⟩ : syracuseStep 3740033 = 2805025) B2805025
theorem B3322255 : Blo 1311974 3322255 := bstep (se 1 (by rfl) ⟨2491691, by rfl⟩ : syracuseStep 3322255 = 4983383) B4983383
theorem B2216335 : Blo 1311974 2216335 := bstep (se 1 (by rfl) ⟨1662251, by rfl⟩ : syracuseStep 2216335 = 3324503) B3324503
theorem B1970615 : Blo 1311974 1970615 := bstep (se 1 (by rfl) ⟨1477961, by rfl⟩ : syracuseStep 1970615 = 2955923) B2955923
theorem B2953691 : Blo 1311974 2953691 := bstep (se 1 (by rfl) ⟨2215268, by rfl⟩ : syracuseStep 2953691 = 4430537) B4430537
theorem B1970651 : Blo 1311974 1970651 := bstep (se 1 (by rfl) ⟨1477988, by rfl⟩ : syracuseStep 1970651 = 2955977) B2955977
theorem B22737509 : Blo 1311974 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B3322579 : Blo 1311974 3322579 := bstep (se 1 (by rfl) ⟨2491934, by rfl⟩ : syracuseStep 3322579 = 4983869) B4983869
theorem B10646275 : Blo 1311974 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B40399667 : Blo 1311974 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B3740489 : Blo 1311974 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B16815023 : Blo 1311974 16815023 := bstep (se 1 (by rfl) ⟨12611267, by rfl⟩ : syracuseStep 16815023 = 25222535) B25222535
theorem B2954159 : Blo 1311974 2954159 := bstep (se 1 (by rfl) ⟨2215619, by rfl⟩ : syracuseStep 2954159 = 4431239) B4431239
theorem B4985783 : Blo 1311974 4985783 := bstep (se 1 (by rfl) ⟨3739337, by rfl⟩ : syracuseStep 4985783 = 7478675) B7478675
theorem B2364455 : Blo 1311974 2364455 := bstep (se 1 (by rfl) ⟨1773341, by rfl⟩ : syracuseStep 2364455 = 3546683) B3546683
theorem B1578023 : Blo 1311974 1578023 := bstep (se 1 (by rfl) ⟨1183517, by rfl⟩ : syracuseStep 1578023 = 2367035) B2367035
theorem B2217017 : Blo 1311974 2217017 := bstep (se 2 (by rfl) ⟨831381, by rfl⟩ : syracuseStep 2217017 = 1662763) B1662763
theorem B11211929 : Blo 1311974 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B4428971 : Blo 1311974 4428971 := bstep (se 1 (by rfl) ⟨3321728, by rfl⟩ : syracuseStep 4428971 = 6643457) B6643457
theorem B2954411 : Blo 1311974 2954411 := bstep (se 1 (by rfl) ⟨2215808, by rfl⟩ : syracuseStep 2954411 = 4431617) B4431617
theorem B63927467 : Blo 1311974 63927467 := bstep (se 1 (by rfl) ⟨47945600, by rfl⟩ : syracuseStep 63927467 = 95891201) B95891201
theorem B25236683 : Blo 1311974 25236683 := bstep (se 1 (by rfl) ⟨18927512, by rfl⟩ : syracuseStep 25236683 = 37855025) B37855025
theorem B7099595 : Blo 1311974 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B8418583 : Blo 1311974 8418583 := bstep (se 1 (by rfl) ⟨6313937, by rfl⟩ : syracuseStep 8418583 = 12627875) B12627875
theorem B28407185 : Blo 1311974 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B18216355 : Blo 1311974 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B6649289 : Blo 1311974 6649289 := bstep (se 2 (by rfl) ⟨2493483, by rfl⟩ : syracuseStep 6649289 = 4986967) B4986967
theorem B8099315 : Blo 1311974 8099315 := bstep (se 1 (by rfl) ⟨6074486, by rfl⟩ : syracuseStep 8099315 = 12148973) B12148973
theorem B6313459 : Blo 1311974 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B1660495 : Blo 1311974 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B3323531 : Blo 1311974 3323531 := bstep (se 1 (by rfl) ⟨2492648, by rfl⟩ : syracuseStep 3323531 = 4985297) B4985297
theorem B4208267 : Blo 1311974 4208267 := bstep (se 1 (by rfl) ⟨3156200, by rfl⟩ : syracuseStep 4208267 = 6312401) B6312401
theorem B14202515 : Blo 1311974 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B4429511 : Blo 1311974 4429511 := bstep (se 1 (by rfl) ⟨3322133, by rfl⟩ : syracuseStep 4429511 = 6644267) B6644267
theorem B2954951 : Blo 1311974 2954951 := bstep (se 1 (by rfl) ⟨2216213, by rfl⟩ : syracuseStep 2954951 = 4432427) B4432427
theorem B2840275 : Blo 1311974 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B3741547 : Blo 1311974 3741547 := bstep (se 1 (by rfl) ⟨2806160, by rfl⟩ : syracuseStep 3741547 = 5612321) B5612321
theorem B4986785 : Blo 1311974 4986785 := bstep (se 2 (by rfl) ⟨1870044, by rfl⟩ : syracuseStep 4986785 = 3740089) B3740089
theorem B9459665 : Blo 1311974 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6649937 : Blo 1311974 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B181778519 : Blo 1311974 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B5609587 : Blo 1311974 5609587 := bstep (se 1 (by rfl) ⟨4207190, by rfl⟩ : syracuseStep 5609587 = 8414381) B8414381
theorem B2103467 : Blo 1311974 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B2103545 : Blo 1311974 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B7100759 : Blo 1311974 7100759 := bstep (se 1 (by rfl) ⟨5325569, by rfl⟩ : syracuseStep 7100759 = 10651139) B10651139
theorem B4987241 : Blo 1311974 4987241 := bstep (se 2 (by rfl) ⟨1870215, by rfl⟩ : syracuseStep 4987241 = 3740431) B3740431
theorem B2660791 : Blo 1311974 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B4430375 : Blo 1311974 4430375 := bstep (se 1 (by rfl) ⟨3322781, by rfl⟩ : syracuseStep 4430375 = 6645563) B6645563
theorem B2955815 : Blo 1311974 2955815 := bstep (se 1 (by rfl) ⟨2216861, by rfl⟩ : syracuseStep 2955815 = 4433723) B4433723
theorem B34134605 : Blo 1311974 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B2660987 : Blo 1311974 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B1661563 : Blo 1311974 1661563 := bstep (se 1 (by rfl) ⟨1246172, by rfl⟩ : syracuseStep 1661563 = 2492345) B2492345
theorem B4430483 : Blo 1311974 4430483 := bstep (se 1 (by rfl) ⟨3322862, by rfl⟩ : syracuseStep 4430483 = 6645725) B6645725
theorem B3324665 : Blo 1311974 3324665 := bstep (se 2 (by rfl) ⟨1246749, by rfl⟩ : syracuseStep 3324665 = 2493499) B2493499
theorem B1661791 : Blo 1311974 1661791 := bstep (se 1 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 1661791 = 2492687) B2492687
theorem B4430699 : Blo 1311974 4430699 := bstep (se 1 (by rfl) ⟨3323024, by rfl⟩ : syracuseStep 4430699 = 6646049) B6646049
theorem B2956139 : Blo 1311974 2956139 := bstep (se 1 (by rfl) ⟨2217104, by rfl⟩ : syracuseStep 2956139 = 4434209) B4434209
theorem B4987757 : Blo 1311974 4987757 := bstep (se 3 (by rfl) ⟨935204, by rfl⟩ : syracuseStep 4987757 = 1870409) B1870409
theorem B4430753 : Blo 1311974 4430753 := bstep (se 2 (by rfl) ⟨1661532, by rfl⟩ : syracuseStep 4430753 = 3323065) B3323065
theorem B2956193 : Blo 1311974 2956193 := bstep (se 2 (by rfl) ⟨1108572, by rfl⟩ : syracuseStep 2956193 = 2217145) B2217145
theorem B3324847 : Blo 1311974 3324847 := bstep (se 1 (by rfl) ⟨2493635, by rfl⟩ : syracuseStep 3324847 = 4987271) B4987271
theorem B3152915 : Blo 1311974 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B6732953 : Blo 1311974 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B14204285 : Blo 1311974 14204285 := bstep (se 3 (by rfl) ⟨2663303, by rfl⟩ : syracuseStep 14204285 = 5326607) B5326607
theorem B3325313 : Blo 1311974 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1662383 : Blo 1311974 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B147578291 : Blo 1311974 147578291 := bstep (se 1 (by rfl) ⟨110683718, by rfl⟩ : syracuseStep 147578291 = 221367437) B221367437
theorem B4734445 : Blo 1311974 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B4431347 : Blo 1311974 4431347 := bstep (se 1 (by rfl) ⟨3323510, by rfl⟩ : syracuseStep 4431347 = 6647021) B6647021
theorem B4988425 : Blo 1311974 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B6659783 : Blo 1311974 6659783 := bstep (se 1 (by rfl) ⟨4994837, by rfl⟩ : syracuseStep 6659783 = 9989675) B9989675
theorem B3325769 : Blo 1311974 3325769 := bstep (se 2 (by rfl) ⟨1247163, by rfl⟩ : syracuseStep 3325769 = 2494327) B2494327
theorem B17956727 : Blo 1311974 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B14204807 : Blo 1311974 14204807 := bstep (se 1 (by rfl) ⟨10653605, by rfl⟩ : syracuseStep 14204807 = 21307211) B21307211
theorem B14950331 : Blo 1311974 14950331 := bstep (se 1 (by rfl) ⟨11212748, by rfl⟩ : syracuseStep 14950331 = 22425497) B22425497
theorem B3325961 : Blo 1311974 3325961 := bstep (se 2 (by rfl) ⟨1247235, by rfl⟩ : syracuseStep 3325961 = 2494471) B2494471
theorem B7479449 : Blo 1311974 7479449 := bstep (se 2 (by rfl) ⟨2804793, by rfl⟩ : syracuseStep 7479449 = 5609587) B5609587
theorem B14188891 : Blo 1311974 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B1868359 : Blo 1311974 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B3547721 : Blo 1311974 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B4432859 : Blo 1311974 4432859 := bstep (se 1 (by rfl) ⟨3324644, by rfl⟩ : syracuseStep 4432859 = 6649289) B6649289
theorem B5399543 : Blo 1311974 5399543 := bstep (se 1 (by rfl) ⟨4049657, by rfl⟩ : syracuseStep 5399543 = 8099315) B8099315
theorem B15148133 : Blo 1311974 15148133 := bstep (se 4 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 15148133 = 2840275) B2840275
theorem B4433021 : Blo 1311974 4433021 := bstep (se 3 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 4433021 = 1662383) B1662383
theorem B4433129 : Blo 1311974 4433129 := bstep (se 2 (by rfl) ⟨1662423, by rfl⟩ : syracuseStep 4433129 = 3324847) B3324847
theorem B1312031 : Blo 1311974 1312031 := bstep (se 1 (by rfl) ⟨984023, by rfl⟩ : syracuseStep 1312031 = 1968047) B1968047
theorem B1312091 : Blo 1311974 1312091 := bstep (se 1 (by rfl) ⟨984068, by rfl⟩ : syracuseStep 1312091 = 1968137) B1968137
theorem B1312111 : Blo 1311974 1312111 := bstep (se 1 (by rfl) ⟨984083, by rfl⟩ : syracuseStep 1312111 = 1968167) B1968167
theorem B4433291 : Blo 1311974 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B121185679 : Blo 1311974 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B1312167 : Blo 1311974 1312167 := bstep (se 1 (by rfl) ⟨984125, by rfl⟩ : syracuseStep 1312167 = 1968251) B1968251
theorem B2491897 : Blo 1311974 2491897 := bstep (se 2 (by rfl) ⟨934461, by rfl⟩ : syracuseStep 2491897 = 1868923) B1868923
theorem B1312251 : Blo 1311974 1312251 := bstep (se 1 (by rfl) ⟨984188, by rfl⟩ : syracuseStep 1312251 = 1968377) B1968377
theorem B1402363 : Blo 1311974 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B5604871 : Blo 1311974 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B1312319 : Blo 1311974 1312319 := bstep (se 1 (by rfl) ⟨984239, by rfl⟩ : syracuseStep 1312319 = 1968479) B1968479
theorem B1312327 : Blo 1311974 1312327 := bstep (se 1 (by rfl) ⟨984245, by rfl⟩ : syracuseStep 1312327 = 1968491) B1968491
theorem B11224777 : Blo 1311974 11224777 := bstep (se 2 (by rfl) ⟨4209291, by rfl⟩ : syracuseStep 11224777 = 8418583) B8418583
theorem B1476319 : Blo 1311974 1476319 := bstep (se 1 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 1476319 = 2214479) B2214479
theorem B1312479 : Blo 1311974 1312479 := bstep (se 1 (by rfl) ⟨984359, by rfl⟩ : syracuseStep 1312479 = 1968719) B1968719
theorem B166127333 : Blo 1311974 166127333 := bstep (se 4 (by rfl) ⟨15574437, by rfl⟩ : syracuseStep 166127333 = 31148875) B31148875
theorem B2492201 : Blo 1311974 2492201 := bstep (se 2 (by rfl) ⟨934575, by rfl⟩ : syracuseStep 2492201 = 1869151) B1869151
theorem B1312559 : Blo 1311974 1312559 := bstep (se 1 (by rfl) ⟨984419, by rfl⟩ : syracuseStep 1312559 = 1968839) B1968839
theorem B1312667 : Blo 1311974 1312667 := bstep (se 1 (by rfl) ⟨984500, by rfl⟩ : syracuseStep 1312667 = 1969001) B1969001
theorem B1312719 : Blo 1311974 1312719 := bstep (se 1 (by rfl) ⟨984539, by rfl⟩ : syracuseStep 1312719 = 1969079) B1969079
theorem B1312743 : Blo 1311974 1312743 := bstep (se 1 (by rfl) ⟨984557, by rfl⟩ : syracuseStep 1312743 = 1969115) B1969115
theorem B2213993 : Blo 1311974 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B1968233 : Blo 1311974 1968233 := bstep (se 2 (by rfl) ⟨738087, by rfl⟩ : syracuseStep 1968233 = 1476175) B1476175
theorem B8415485 : Blo 1311974 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B4983065 : Blo 1311974 4983065 := bstep (se 2 (by rfl) ⟨1868649, by rfl⟩ : syracuseStep 4983065 = 3737299) B3737299
theorem B1476895 : Blo 1311974 1476895 := bstep (se 1 (by rfl) ⟨1107671, by rfl⟩ : syracuseStep 1476895 = 2215343) B2215343
theorem B1313055 : Blo 1311974 1313055 := bstep (se 1 (by rfl) ⟨984791, by rfl⟩ : syracuseStep 1313055 = 1969583) B1969583
theorem B1313115 : Blo 1311974 1313115 := bstep (se 1 (by rfl) ⟨984836, by rfl⟩ : syracuseStep 1313115 = 1969673) B1969673
theorem B1313135 : Blo 1311974 1313135 := bstep (se 1 (by rfl) ⟨984851, by rfl⟩ : syracuseStep 1313135 = 1969703) B1969703
theorem B1968551 : Blo 1311974 1968551 := bstep (se 1 (by rfl) ⟨1476413, by rfl⟩ : syracuseStep 1968551 = 2952827) B2952827
theorem B1313191 : Blo 1311974 1313191 := bstep (se 1 (by rfl) ⟨984893, by rfl⟩ : syracuseStep 1313191 = 1969787) B1969787
theorem B38373835 : Blo 1311974 38373835 := bstep (se 1 (by rfl) ⟨28780376, by rfl⟩ : syracuseStep 38373835 = 57560753) B57560753
theorem B2804179 : Blo 1311974 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B1968635 : Blo 1311974 1968635 := bstep (se 1 (by rfl) ⟨1476476, by rfl⟩ : syracuseStep 1968635 = 2952953) B2952953
theorem B1313275 : Blo 1311974 1313275 := bstep (se 1 (by rfl) ⟨984956, by rfl⟩ : syracuseStep 1313275 = 1969913) B1969913
theorem B1477183 : Blo 1311974 1477183 := bstep (se 1 (by rfl) ⟨1107887, by rfl⟩ : syracuseStep 1477183 = 2215775) B2215775
theorem B1313343 : Blo 1311974 1313343 := bstep (se 1 (by rfl) ⟨985007, by rfl⟩ : syracuseStep 1313343 = 1970015) B1970015
theorem B1313351 : Blo 1311974 1313351 := bstep (se 1 (by rfl) ⟨985013, by rfl⟩ : syracuseStep 1313351 = 1970027) B1970027
theorem B11971151 : Blo 1311974 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B1968761 : Blo 1311974 1968761 := bstep (se 2 (by rfl) ⟨738285, by rfl⟩ : syracuseStep 1968761 = 1476571) B1476571
theorem B1968815 : Blo 1311974 1968815 := bstep (se 1 (by rfl) ⟨1476611, by rfl⟩ : syracuseStep 1968815 = 2953223) B2953223
theorem B1968863 : Blo 1311974 1968863 := bstep (se 1 (by rfl) ⟨1476647, by rfl⟩ : syracuseStep 1968863 = 2953295) B2953295
theorem B1313503 : Blo 1311974 1313503 := bstep (se 1 (by rfl) ⟨985127, by rfl⟩ : syracuseStep 1313503 = 1970255) B1970255
theorem B1313583 : Blo 1311974 1313583 := bstep (se 1 (by rfl) ⟨985187, by rfl⟩ : syracuseStep 1313583 = 1970375) B1970375
theorem B1313691 : Blo 1311974 1313691 := bstep (se 1 (by rfl) ⟨985268, by rfl⟩ : syracuseStep 1313691 = 1970537) B1970537
theorem B2952107 : Blo 1311974 2952107 := bstep (se 1 (by rfl) ⟨2214080, by rfl⟩ : syracuseStep 2952107 = 4428161) B4428161
theorem B2493355 : Blo 1311974 2493355 := bstep (se 1 (by rfl) ⟨1870016, by rfl⟩ : syracuseStep 2493355 = 3740033) B3740033
theorem B1313743 : Blo 1311974 1313743 := bstep (se 1 (by rfl) ⟨985307, by rfl⟩ : syracuseStep 1313743 = 1970615) B1970615
theorem B1969127 : Blo 1311974 1969127 := bstep (se 1 (by rfl) ⟨1476845, by rfl⟩ : syracuseStep 1969127 = 2953691) B2953691
theorem B1313767 : Blo 1311974 1313767 := bstep (se 1 (by rfl) ⟨985325, by rfl⟩ : syracuseStep 1313767 = 1970651) B1970651
theorem B13470785 : Blo 1311974 13470785 := bstep (se 2 (by rfl) ⟨5051544, by rfl⟩ : syracuseStep 13470785 = 10103089) B10103089
theorem B15158339 : Blo 1311974 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B9464971 : Blo 1311974 9464971 := bstep (se 1 (by rfl) ⟨7098728, by rfl⟩ : syracuseStep 9464971 = 14197457) B14197457
theorem B5762267 : Blo 1311974 5762267 := bstep (se 1 (by rfl) ⟨4321700, by rfl⟩ : syracuseStep 5762267 = 8643401) B8643401
theorem B2493659 : Blo 1311974 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B1969385 : Blo 1311974 1969385 := bstep (se 2 (by rfl) ⟨738519, by rfl⟩ : syracuseStep 1969385 = 1477039) B1477039
theorem B11210015 : Blo 1311974 11210015 := bstep (se 1 (by rfl) ⟨8407511, by rfl⟩ : syracuseStep 11210015 = 16815023) B16815023
theorem B1969439 : Blo 1311974 1969439 := bstep (se 1 (by rfl) ⟨1477079, by rfl⟩ : syracuseStep 1969439 = 2954159) B2954159
theorem B1576303 : Blo 1311974 1576303 := bstep (se 1 (by rfl) ⟨1182227, by rfl⟩ : syracuseStep 1576303 = 2364455) B2364455
theorem B1478011 : Blo 1311974 1478011 := bstep (se 1 (by rfl) ⟨1108508, by rfl⟩ : syracuseStep 1478011 = 2217017) B2217017
theorem B7474619 : Blo 1311974 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B4206011 : Blo 1311974 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B2952647 : Blo 1311974 2952647 := bstep (se 1 (by rfl) ⟨2214485, by rfl⟩ : syracuseStep 2952647 = 4428971) B4428971
theorem B1969607 : Blo 1311974 1969607 := bstep (se 1 (by rfl) ⟨1477205, by rfl⟩ : syracuseStep 1969607 = 2954411) B2954411
theorem B42618311 : Blo 1311974 42618311 := bstep (se 1 (by rfl) ⟨31963733, by rfl⟩ : syracuseStep 42618311 = 63927467) B63927467
theorem B2215417 : Blo 1311974 2215417 := bstep (se 2 (by rfl) ⟨830781, by rfl⟩ : syracuseStep 2215417 = 1661563) B1661563
theorem B5680649 : Blo 1311974 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B5606921 : Blo 1311974 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B6647507 : Blo 1311974 6647507 := bstep (se 1 (by rfl) ⟨4985630, by rfl⟩ : syracuseStep 6647507 = 9971261) B9971261
theorem B3321607 : Blo 1311974 3321607 := bstep (se 1 (by rfl) ⟨2491205, by rfl⟩ : syracuseStep 3321607 = 4982411) B4982411
theorem B2215687 : Blo 1311974 2215687 := bstep (se 1 (by rfl) ⟨1661765, by rfl⟩ : syracuseStep 2215687 = 3323531) B3323531
theorem B2805511 : Blo 1311974 2805511 := bstep (se 1 (by rfl) ⟨2104133, by rfl⟩ : syracuseStep 2805511 = 4208267) B4208267
theorem B2215721 : Blo 1311974 2215721 := bstep (se 2 (by rfl) ⟨830895, by rfl⟩ : syracuseStep 2215721 = 1661791) B1661791
theorem B1969961 : Blo 1311974 1969961 := bstep (se 2 (by rfl) ⟨738735, by rfl⟩ : syracuseStep 1969961 = 1477471) B1477471
theorem B2953007 : Blo 1311974 2953007 := bstep (se 1 (by rfl) ⟨2214755, by rfl⟩ : syracuseStep 2953007 = 4429511) B4429511
theorem B1969967 : Blo 1311974 1969967 := bstep (se 1 (by rfl) ⟨1477475, by rfl⟩ : syracuseStep 1969967 = 2954951) B2954951
theorem B4984841 : Blo 1311974 4984841 := bstep (se 2 (by rfl) ⟨1869315, by rfl⟩ : syracuseStep 4984841 = 3738631) B3738631
theorem B3321881 : Blo 1311974 3321881 := bstep (se 2 (by rfl) ⟨1245705, by rfl⟩ : syracuseStep 3321881 = 2491411) B2491411
theorem B1970441 : Blo 1311974 1970441 := bstep (se 2 (by rfl) ⟨738915, by rfl⟩ : syracuseStep 1970441 = 1477831) B1477831
theorem B71840033 : Blo 1311974 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B6648155 : Blo 1311974 6648155 := bstep (se 1 (by rfl) ⟨4986116, by rfl⟩ : syracuseStep 6648155 = 9972233) B9972233
theorem B2953583 : Blo 1311974 2953583 := bstep (se 1 (by rfl) ⟨2215187, by rfl⟩ : syracuseStep 2953583 = 4430375) B4430375
theorem B1970543 : Blo 1311974 1970543 := bstep (se 1 (by rfl) ⟨1477907, by rfl⟩ : syracuseStep 1970543 = 2955815) B2955815
theorem B1773991 : Blo 1311974 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B2953655 : Blo 1311974 2953655 := bstep (se 1 (by rfl) ⟨2215241, by rfl⟩ : syracuseStep 2953655 = 4430483) B4430483
theorem B2216443 : Blo 1311974 2216443 := bstep (se 1 (by rfl) ⟨1662332, by rfl⟩ : syracuseStep 2216443 = 3324665) B3324665
theorem B2953799 : Blo 1311974 2953799 := bstep (se 1 (by rfl) ⟨2215349, by rfl⟩ : syracuseStep 2953799 = 4430699) B4430699
theorem B1970759 : Blo 1311974 1970759 := bstep (se 1 (by rfl) ⟨1478069, by rfl⟩ : syracuseStep 1970759 = 2956139) B2956139
theorem B2953835 : Blo 1311974 2953835 := bstep (se 1 (by rfl) ⟨2215376, by rfl⟩ : syracuseStep 2953835 = 4430753) B4430753
theorem B1970795 : Blo 1311974 1970795 := bstep (se 1 (by rfl) ⟨1478096, by rfl⟩ : syracuseStep 1970795 = 2956193) B2956193
theorem B6312593 : Blo 1311974 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B8417945 : Blo 1311974 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B2101943 : Blo 1311974 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B7476077 : Blo 1311974 7476077 := bstep (se 3 (by rfl) ⟨1401764, by rfl⟩ : syracuseStep 7476077 = 2803529) B2803529
theorem B2216875 : Blo 1311974 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B2954231 : Blo 1311974 2954231 := bstep (se 1 (by rfl) ⟨2215673, by rfl⟩ : syracuseStep 2954231 = 4431347) B4431347
theorem B4985981 : Blo 1311974 4985981 := bstep (se 3 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 4985981 = 1869743) B1869743
theorem B2217179 : Blo 1311974 2217179 := bstep (se 1 (by rfl) ⟨1662884, by rfl⟩ : syracuseStep 2217179 = 3325769) B3325769
theorem B9966887 : Blo 1311974 9966887 := bstep (se 1 (by rfl) ⟨7475165, by rfl⟩ : syracuseStep 9966887 = 14950331) B14950331
theorem B6649127 : Blo 1311974 6649127 := bstep (se 1 (by rfl) ⟨4986845, by rfl⟩ : syracuseStep 6649127 = 9973691) B9973691
theorem B2954591 : Blo 1311974 2954591 := bstep (se 1 (by rfl) ⟨2215943, by rfl⟩ : syracuseStep 2954591 = 4431887) B4431887
theorem B5051837 : Blo 1311974 5051837 := bstep (se 3 (by rfl) ⟨947219, by rfl⟩ : syracuseStep 5051837 = 1894439) B1894439
theorem B1660591 : Blo 1311974 1660591 := bstep (se 1 (by rfl) ⟨1245443, by rfl⟩ : syracuseStep 1660591 = 2490887) B2490887
theorem B2954987 : Blo 1311974 2954987 := bstep (se 1 (by rfl) ⟨2216240, by rfl⟩ : syracuseStep 2954987 = 4432481) B4432481
theorem B16832245 : Blo 1311974 16832245 := bstep (se 5 (by rfl) ⟨789011, by rfl⟩ : syracuseStep 16832245 = 1578023) B1578023
theorem B5609245 : Blo 1311974 5609245 := bstep (se 3 (by rfl) ⟨1051733, by rfl⟩ : syracuseStep 5609245 = 2103467) B2103467
theorem B4429673 : Blo 1311974 4429673 := bstep (se 2 (by rfl) ⟨1661127, by rfl⟩ : syracuseStep 4429673 = 3322255) B3322255
theorem B2955113 : Blo 1311974 2955113 := bstep (se 2 (by rfl) ⟨1108167, by rfl⟩ : syracuseStep 2955113 = 2216335) B2216335
theorem B26933111 : Blo 1311974 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B3323855 : Blo 1311974 3323855 := bstep (se 1 (by rfl) ⟨2492891, by rfl⟩ : syracuseStep 3323855 = 4985783) B4985783
theorem B16824455 : Blo 1311974 16824455 := bstep (se 1 (by rfl) ⟨12618341, by rfl⟩ : syracuseStep 16824455 = 25236683) B25236683
theorem B4733063 : Blo 1311974 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B18938123 : Blo 1311974 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B4430105 : Blo 1311974 4430105 := bstep (se 2 (by rfl) ⟨1661289, by rfl⟩ : syracuseStep 4430105 = 3322579) B3322579
theorem B14195033 : Blo 1311974 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B3037607 : Blo 1311974 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B9468343 : Blo 1311974 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B3324523 : Blo 1311974 3324523 := bstep (se 1 (by rfl) ⟨2493392, by rfl⟩ : syracuseStep 3324523 = 4986785) B4986785
theorem B6306443 : Blo 1311974 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B2955959 : Blo 1311974 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B4733839 : Blo 1311974 4733839 := bstep (se 1 (by rfl) ⟨3550379, by rfl⟩ : syracuseStep 4733839 = 7100759) B7100759
theorem B2956175 : Blo 1311974 2956175 := bstep (se 1 (by rfl) ⟨2217131, by rfl⟩ : syracuseStep 2956175 = 4434263) B4434263
theorem B3324827 : Blo 1311974 3324827 := bstep (se 1 (by rfl) ⟨2493620, by rfl⟩ : syracuseStep 3324827 = 4987241) B4987241
theorem B22756403 : Blo 1311974 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B2841799 : Blo 1311974 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B24288473 : Blo 1311974 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B3325171 : Blo 1311974 3325171 := bstep (se 1 (by rfl) ⟨2493878, by rfl⟩ : syracuseStep 3325171 = 4987757) B4987757
theorem B20217077 : Blo 1311974 20217077 := bstep (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) B1895351
theorem B16817483 : Blo 1311974 16817483 := bstep (se 1 (by rfl) ⟨12613112, by rfl⟩ : syracuseStep 16817483 = 25226225) B25226225
theorem B6651233 : Blo 1311974 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B4488635 : Blo 1311974 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B1662535 : Blo 1311974 1662535 := bstep (se 1 (by rfl) ⟨1246901, by rfl⟩ : syracuseStep 1662535 = 2493803) B2493803
theorem B9469523 : Blo 1311974 9469523 := bstep (se 1 (by rfl) ⟨7102142, by rfl⟩ : syracuseStep 9469523 = 14204285) B14204285
theorem B6643295 : Blo 1311974 6643295 := bstep (se 1 (by rfl) ⟨4982471, by rfl⟩ : syracuseStep 6643295 = 9964943) B9964943
theorem B4431455 : Blo 1311974 4431455 := bstep (se 1 (by rfl) ⟨3323591, by rfl⟩ : syracuseStep 4431455 = 6647183) B6647183
theorem B98385527 : Blo 1311974 98385527 := bstep (se 1 (by rfl) ⟨73789145, by rfl⟩ : syracuseStep 98385527 = 147578291) B147578291
theorem B4439855 : Blo 1311974 4439855 := bstep (se 1 (by rfl) ⟨3329891, by rfl⟩ : syracuseStep 4439855 = 6659783) B6659783
theorem B4988729 : Blo 1311974 4988729 := bstep (se 2 (by rfl) ⟨1870773, by rfl⟩ : syracuseStep 4988729 = 3741547) B3741547
theorem B9469871 : Blo 1311974 9469871 := bstep (se 1 (by rfl) ⟨7102403, by rfl⟩ : syracuseStep 9469871 = 14204807) B14204807
theorem B4432103 : Blo 1311974 4432103 := bstep (se 1 (by rfl) ⟨3324077, by rfl⟩ : syracuseStep 4432103 = 6648155) B6648155
theorem B5611963 : Blo 1311974 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B1401295 : Blo 1311974 1401295 := bstep (se 1 (by rfl) ⟨1050971, by rfl⟩ : syracuseStep 1401295 = 2101943) B2101943
theorem B12624457 : Blo 1311974 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B2491145 : Blo 1311974 2491145 := bstep (se 2 (by rfl) ⟨934179, by rfl⟩ : syracuseStep 2491145 = 1868359) B1868359
theorem B4432697 : Blo 1311974 4432697 := bstep (se 2 (by rfl) ⟨1662261, by rfl⟩ : syracuseStep 4432697 = 3324523) B3324523
theorem B6644591 : Blo 1311974 6644591 := bstep (se 1 (by rfl) ⟨4983443, by rfl⟩ : syracuseStep 6644591 = 9966887) B9966887
theorem B4432751 : Blo 1311974 4432751 := bstep (se 1 (by rfl) ⟨3324563, by rfl⟩ : syracuseStep 4432751 = 6649127) B6649127
theorem B3367891 : Blo 1311974 3367891 := bstep (se 1 (by rfl) ⟨2525918, by rfl⟩ : syracuseStep 3367891 = 5051837) B5051837
theorem B11969693 : Blo 1311974 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B11216029 : Blo 1311974 11216029 := bstep (se 3 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 11216029 = 4206011) B4206011
theorem B15148397 : Blo 1311974 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B14951789 : Blo 1311974 14951789 := bstep (se 3 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 14951789 = 5606921) B5606921
theorem B1475995 : Blo 1311974 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B1312155 : Blo 1311974 1312155 := bstep (se 1 (by rfl) ⟨984116, by rfl⟩ : syracuseStep 1312155 = 1968233) B1968233
theorem B11216303 : Blo 1311974 11216303 := bstep (se 1 (by rfl) ⟨8412227, by rfl⟩ : syracuseStep 11216303 = 16824455) B16824455
theorem B3155375 : Blo 1311974 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B12625415 : Blo 1311974 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B9463355 : Blo 1311974 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B1312367 : Blo 1311974 1312367 := bstep (se 1 (by rfl) ⟨984275, by rfl⟩ : syracuseStep 1312367 = 1968551) B1968551
theorem B2025071 : Blo 1311974 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B4433561 : Blo 1311974 4433561 := bstep (se 2 (by rfl) ⟨1662585, by rfl⟩ : syracuseStep 4433561 = 3325171) B3325171
theorem B1312423 : Blo 1311974 1312423 := bstep (se 1 (by rfl) ⟨984317, by rfl⟩ : syracuseStep 1312423 = 1968635) B1968635
theorem B7980767 : Blo 1311974 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B1312507 : Blo 1311974 1312507 := bstep (se 1 (by rfl) ⟨984380, by rfl⟩ : syracuseStep 1312507 = 1968761) B1968761
theorem B4204295 : Blo 1311974 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B1312543 : Blo 1311974 1312543 := bstep (se 1 (by rfl) ⟨984407, by rfl⟩ : syracuseStep 1312543 = 1968815) B1968815
theorem B1312575 : Blo 1311974 1312575 := bstep (se 1 (by rfl) ⟨984431, by rfl⟩ : syracuseStep 1312575 = 1968863) B1968863
theorem B161580905 : Blo 1311974 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B8406949 : Blo 1311974 8406949 := bstep (se 4 (by rfl) ⟨788151, by rfl⟩ : syracuseStep 8406949 = 1576303) B1576303
theorem B1968071 : Blo 1311974 1968071 := bstep (se 1 (by rfl) ⟨1476053, by rfl⟩ : syracuseStep 1968071 = 2952107) B2952107
theorem B1312751 : Blo 1311974 1312751 := bstep (se 1 (by rfl) ⟨984563, by rfl⟩ : syracuseStep 1312751 = 1969127) B1969127
theorem B1869817 : Blo 1311974 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B7473161 : Blo 1311974 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B8980523 : Blo 1311974 8980523 := bstep (se 1 (by rfl) ⟨6735392, by rfl⟩ : syracuseStep 8980523 = 13470785) B13470785
theorem B11839613 : Blo 1311974 11839613 := bstep (se 3 (by rfl) ⟨2219927, by rfl⟩ : syracuseStep 11839613 = 4439855) B4439855
theorem B1312923 : Blo 1311974 1312923 := bstep (se 1 (by rfl) ⟨984692, by rfl⟩ : syracuseStep 1312923 = 1969385) B1969385
theorem B7473343 : Blo 1311974 7473343 := bstep (se 1 (by rfl) ⟨5605007, by rfl⟩ : syracuseStep 7473343 = 11210015) B11210015
theorem B1312959 : Blo 1311974 1312959 := bstep (se 1 (by rfl) ⟨984719, by rfl⟩ : syracuseStep 1312959 = 1969439) B1969439
theorem B2214121 : Blo 1311974 2214121 := bstep (se 2 (by rfl) ⟨830295, by rfl⟩ : syracuseStep 2214121 = 1660591) B1660591
theorem B4434155 : Blo 1311974 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B4983079 : Blo 1311974 4983079 := bstep (se 1 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 4983079 = 7474619) B7474619
theorem B1968425 : Blo 1311974 1968425 := bstep (se 2 (by rfl) ⟨738159, by rfl⟩ : syracuseStep 1968425 = 1476319) B1476319
theorem B1968431 : Blo 1311974 1968431 := bstep (se 1 (by rfl) ⟨1476323, by rfl⟩ : syracuseStep 1968431 = 2952647) B2952647
theorem B1313071 : Blo 1311974 1313071 := bstep (se 1 (by rfl) ⟨984803, by rfl⟩ : syracuseStep 1313071 = 1969607) B1969607
theorem B28412207 : Blo 1311974 28412207 := bstep (se 1 (by rfl) ⟨21309155, by rfl⟩ : syracuseStep 28412207 = 42618311) B42618311
theorem B1477147 : Blo 1311974 1477147 := bstep (se 1 (by rfl) ⟨1107860, by rfl⟩ : syracuseStep 1477147 = 2215721) B2215721
theorem B1313307 : Blo 1311974 1313307 := bstep (se 1 (by rfl) ⟨984980, by rfl⟩ : syracuseStep 1313307 = 1969961) B1969961
theorem B1968671 : Blo 1311974 1968671 := bstep (se 1 (by rfl) ⟨1476503, by rfl⟩ : syracuseStep 1968671 = 2953007) B2953007
theorem B1313311 : Blo 1311974 1313311 := bstep (se 1 (by rfl) ⟨984983, by rfl⟩ : syracuseStep 1313311 = 1969967) B1969967
theorem B2214587 : Blo 1311974 2214587 := bstep (se 1 (by rfl) ⟨1660940, by rfl⟩ : syracuseStep 2214587 = 3321881) B3321881
theorem B1313627 : Blo 1311974 1313627 := bstep (se 1 (by rfl) ⟨985220, by rfl⟩ : syracuseStep 1313627 = 1970441) B1970441
theorem B47893355 : Blo 1311974 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B1969055 : Blo 1311974 1969055 := bstep (se 1 (by rfl) ⟨1476791, by rfl⟩ : syracuseStep 1969055 = 2953583) B2953583
theorem B1313695 : Blo 1311974 1313695 := bstep (se 1 (by rfl) ⟨985271, by rfl⟩ : syracuseStep 1313695 = 1970543) B1970543
theorem B1969103 : Blo 1311974 1969103 := bstep (se 1 (by rfl) ⟨1476827, by rfl⟩ : syracuseStep 1969103 = 2953655) B2953655
theorem B1969193 : Blo 1311974 1969193 := bstep (se 2 (by rfl) ⟨738447, by rfl⟩ : syracuseStep 1969193 = 1476895) B1476895
theorem B1969199 : Blo 1311974 1969199 := bstep (se 1 (by rfl) ⟨1476899, by rfl⟩ : syracuseStep 1969199 = 2953799) B2953799
theorem B1313839 : Blo 1311974 1313839 := bstep (se 1 (by rfl) ⟨985379, by rfl⟩ : syracuseStep 1313839 = 1970759) B1970759
theorem B1969223 : Blo 1311974 1969223 := bstep (se 1 (by rfl) ⟨1476917, by rfl⟩ : syracuseStep 1969223 = 2953835) B2953835
theorem B1313863 : Blo 1311974 1313863 := bstep (se 1 (by rfl) ⟨985397, by rfl⟩ : syracuseStep 1313863 = 1970795) B1970795
theorem B18918521 : Blo 1311974 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B4984051 : Blo 1311974 4984051 := bstep (se 1 (by rfl) ⟨3738038, by rfl⟩ : syracuseStep 4984051 = 7476077) B7476077
theorem B3738905 : Blo 1311974 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B1969487 : Blo 1311974 1969487 := bstep (se 1 (by rfl) ⟨1477115, by rfl⟩ : syracuseStep 1969487 = 2954231) B2954231
theorem B3599695 : Blo 1311974 3599695 := bstep (se 1 (by rfl) ⟨2699771, by rfl⟩ : syracuseStep 3599695 = 5399543) B5399543
theorem B1969577 : Blo 1311974 1969577 := bstep (se 2 (by rfl) ⟨738591, by rfl⟩ : syracuseStep 1969577 = 1477183) B1477183
theorem B1478119 : Blo 1311974 1478119 := bstep (se 1 (by rfl) ⟨1108589, by rfl⟩ : syracuseStep 1478119 = 2217179) B2217179
theorem B1969727 : Blo 1311974 1969727 := bstep (se 1 (by rfl) ⟨1477295, by rfl⟩ : syracuseStep 1969727 = 2954591) B2954591
theorem B1969991 : Blo 1311974 1969991 := bstep (se 1 (by rfl) ⟨1477493, by rfl⟩ : syracuseStep 1969991 = 2954987) B2954987
theorem B6311785 : Blo 1311974 6311785 := bstep (se 2 (by rfl) ⟨2366919, by rfl⟩ : syracuseStep 6311785 = 4733839) B4733839
theorem B2953115 : Blo 1311974 2953115 := bstep (se 1 (by rfl) ⟨2214836, by rfl⟩ : syracuseStep 2953115 = 4429673) B4429673
theorem B1970075 : Blo 1311974 1970075 := bstep (se 1 (by rfl) ⟨1477556, by rfl⟩ : syracuseStep 1970075 = 2955113) B2955113
theorem B2215903 : Blo 1311974 2215903 := bstep (se 1 (by rfl) ⟨1661927, by rfl⟩ : syracuseStep 2215903 = 3323855) B3323855
theorem B12619961 : Blo 1311974 12619961 := bstep (se 2 (by rfl) ⟨4732485, by rfl⟩ : syracuseStep 12619961 = 9464971) B9464971
theorem B3322043 : Blo 1311974 3322043 := bstep (se 1 (by rfl) ⟨2491532, by rfl⟩ : syracuseStep 3322043 = 4983065) B4983065
theorem B2953403 : Blo 1311974 2953403 := bstep (se 1 (by rfl) ⟨2215052, by rfl⟩ : syracuseStep 2953403 = 4430105) B4430105
theorem B3789065 : Blo 1311974 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B262361405 : Blo 1311974 262361405 := bstep (se 3 (by rfl) ⟨49192763, by rfl⟩ : syracuseStep 262361405 = 98385527) B98385527
theorem B1970639 : Blo 1311974 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B1970681 : Blo 1311974 1970681 := bstep (se 2 (by rfl) ⟨739005, by rfl⟩ : syracuseStep 1970681 = 1478011) B1478011
theorem B1970783 : Blo 1311974 1970783 := bstep (se 1 (by rfl) ⟨1478087, by rfl⟩ : syracuseStep 1970783 = 2956175) B2956175
theorem B2216551 : Blo 1311974 2216551 := bstep (se 1 (by rfl) ⟨1662413, by rfl⟩ : syracuseStep 2216551 = 3324827) B3324827
theorem B3322529 : Blo 1311974 3322529 := bstep (se 2 (by rfl) ⟨1245948, by rfl⟩ : syracuseStep 3322529 = 2491897) B2491897
theorem B2953889 : Blo 1311974 2953889 := bstep (se 2 (by rfl) ⟨1107708, by rfl⟩ : syracuseStep 2953889 = 2215417) B2215417
theorem B10105559 : Blo 1311974 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B2216713 : Blo 1311974 2216713 := bstep (se 2 (by rfl) ⟨831267, by rfl⟩ : syracuseStep 2216713 = 1662535) B1662535
theorem B16192315 : Blo 1311974 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B11211655 : Blo 1311974 11211655 := bstep (se 1 (by rfl) ⟨8408741, by rfl⟩ : syracuseStep 11211655 = 16817483) B16817483
theorem B22442993 : Blo 1311974 22442993 := bstep (se 2 (by rfl) ⟨8416122, by rfl⟩ : syracuseStep 22442993 = 16832245) B16832245
theorem B4428809 : Blo 1311974 4428809 := bstep (se 2 (by rfl) ⟨1660803, by rfl⟩ : syracuseStep 4428809 = 3321607) B3321607
theorem B2954249 : Blo 1311974 2954249 := bstep (se 2 (by rfl) ⟨1107843, by rfl⟩ : syracuseStep 2954249 = 2215687) B2215687
theorem B3740681 : Blo 1311974 3740681 := bstep (se 2 (by rfl) ⟨1402755, by rfl⟩ : syracuseStep 3740681 = 2805511) B2805511
theorem B6313015 : Blo 1311974 6313015 := bstep (se 1 (by rfl) ⟨4734761, by rfl⟩ : syracuseStep 6313015 = 9469523) B9469523
theorem B4428863 : Blo 1311974 4428863 := bstep (se 1 (by rfl) ⟨3321647, by rfl⟩ : syracuseStep 4428863 = 6643295) B6643295
theorem B2954303 : Blo 1311974 2954303 := bstep (se 1 (by rfl) ⟨2215727, by rfl⟩ : syracuseStep 2954303 = 4431455) B4431455
theorem B6313247 : Blo 1311974 6313247 := bstep (se 1 (by rfl) ⟨4734935, by rfl⟩ : syracuseStep 6313247 = 9469871) B9469871
theorem B3323227 : Blo 1311974 3323227 := bstep (se 1 (by rfl) ⟨2492420, by rfl⟩ : syracuseStep 3323227 = 4984841) B4984841
theorem B2217307 : Blo 1311974 2217307 := bstep (se 1 (by rfl) ⟨1662980, by rfl⟩ : syracuseStep 2217307 = 3325961) B3325961
theorem B4986299 : Blo 1311974 4986299 := bstep (se 1 (by rfl) ⟨3739724, by rfl⟩ : syracuseStep 4986299 = 7479449) B7479449
theorem B2365147 : Blo 1311974 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B2365321 : Blo 1311974 2365321 := bstep (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) B1773991
theorem B51165113 : Blo 1311974 51165113 := bstep (se 2 (by rfl) ⟨19186917, by rfl⟩ : syracuseStep 51165113 = 38373835) B38373835
theorem B2955239 : Blo 1311974 2955239 := bstep (se 1 (by rfl) ⟨2216429, by rfl⟩ : syracuseStep 2955239 = 4432859) B4432859
theorem B2955257 : Blo 1311974 2955257 := bstep (se 2 (by rfl) ⟨1108221, by rfl⟩ : syracuseStep 2955257 = 2216443) B2216443
theorem B10098755 : Blo 1311974 10098755 := bstep (se 1 (by rfl) ⟨7574066, by rfl⟩ : syracuseStep 10098755 = 15148133) B15148133
theorem B3323987 : Blo 1311974 3323987 := bstep (se 1 (by rfl) ⟨2492990, by rfl⟩ : syracuseStep 3323987 = 4985981) B4985981
theorem B2955347 : Blo 1311974 2955347 := bstep (se 1 (by rfl) ⟨2216510, by rfl⟩ : syracuseStep 2955347 = 4433021) B4433021
theorem B13478051 : Blo 1311974 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B2955419 : Blo 1311974 2955419 := bstep (se 1 (by rfl) ⟨2216564, by rfl⟩ : syracuseStep 2955419 = 4433129) B4433129
theorem B2955527 : Blo 1311974 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B1661467 : Blo 1311974 1661467 := bstep (se 1 (by rfl) ⟨1246100, by rfl⟩ : syracuseStep 1661467 = 2492201) B2492201
theorem B3324473 : Blo 1311974 3324473 := bstep (se 2 (by rfl) ⟨1246677, by rfl⟩ : syracuseStep 3324473 = 2493355) B2493355
theorem B2955833 : Blo 1311974 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B17955407 : Blo 1311974 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B5610323 : Blo 1311974 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B16833581 : Blo 1311974 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B443006221 : Blo 1311974 443006221 := bstep (se 3 (by rfl) ⟨83063666, by rfl⟩ : syracuseStep 443006221 = 166127333) B166127333
theorem B15170935 : Blo 1311974 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B3841511 : Blo 1311974 3841511 := bstep (se 1 (by rfl) ⟨2881133, by rfl⟩ : syracuseStep 3841511 = 5762267) B5762267
theorem B1662439 : Blo 1311974 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B14966369 : Blo 1311974 14966369 := bstep (se 2 (by rfl) ⟨5612388, by rfl⟩ : syracuseStep 14966369 = 11224777) B11224777
theorem B7478993 : Blo 1311974 7478993 := bstep (se 2 (by rfl) ⟨2804622, by rfl⟩ : syracuseStep 7478993 = 5609245) B5609245
theorem B4431671 : Blo 1311974 4431671 := bstep (se 1 (by rfl) ⟨3323753, by rfl⟩ : syracuseStep 4431671 = 6647507) B6647507
theorem B3325819 : Blo 1311974 3325819 := bstep (se 1 (by rfl) ⟨2494364, by rfl⟩ : syracuseStep 3325819 = 4988729) B4988729
theorem B8413307 : Blo 1311974 8413307 := bstep (se 1 (by rfl) ⟨6309980, by rfl⟩ : syracuseStep 8413307 = 12619961) B12619961
theorem B174907603 : Blo 1311974 174907603 := bstep (se 1 (by rfl) ⟨131180702, by rfl⟩ : syracuseStep 174907603 = 262361405) B262361405
theorem B6644105 : Blo 1311974 6644105 := bstep (se 2 (by rfl) ⟨2491539, by rfl⟩ : syracuseStep 6644105 = 4983079) B4983079
theorem B1868393 : Blo 1311974 1868393 := bstep (se 2 (by rfl) ⟨700647, by rfl⟩ : syracuseStep 1868393 = 1401295) B1401295
theorem B7979795 : Blo 1311974 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B6308903 : Blo 1311974 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B2802863 : Blo 1311974 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B4490521 : Blo 1311974 4490521 := bstep (se 2 (by rfl) ⟨1683945, by rfl⟩ : syracuseStep 4490521 = 3367891) B3367891
theorem B1312047 : Blo 1311974 1312047 := bstep (se 1 (by rfl) ⟨984035, by rfl⟩ : syracuseStep 1312047 = 1968071) B1968071
theorem B126289205 : Blo 1311974 126289205 := bstep (se 5 (by rfl) ⟨5919806, by rfl⟩ : syracuseStep 126289205 = 11839613) B11839613
theorem B4982107 : Blo 1311974 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B1312283 : Blo 1311974 1312283 := bstep (se 1 (by rfl) ⟨984212, by rfl⟩ : syracuseStep 1312283 = 1968425) B1968425
theorem B1312287 : Blo 1311974 1312287 := bstep (se 1 (by rfl) ⟨984215, by rfl⟩ : syracuseStep 1312287 = 1968431) B1968431
theorem B18941471 : Blo 1311974 18941471 := bstep (se 1 (by rfl) ⟨14206103, by rfl⟩ : syracuseStep 18941471 = 28412207) B28412207
theorem B6645401 : Blo 1311974 6645401 := bstep (se 2 (by rfl) ⟨2492025, by rfl⟩ : syracuseStep 6645401 = 4984051) B4984051
theorem B1312447 : Blo 1311974 1312447 := bstep (se 1 (by rfl) ⟨984335, by rfl⟩ : syracuseStep 1312447 = 1968671) B1968671
theorem B11970271 : Blo 1311974 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B1476391 : Blo 1311974 1476391 := bstep (se 1 (by rfl) ⟨1107293, by rfl⟩ : syracuseStep 1476391 = 2214587) B2214587
theorem B20227913 : Blo 1311974 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B1967993 : Blo 1311974 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B1312703 : Blo 1311974 1312703 := bstep (se 1 (by rfl) ⟨984527, by rfl⟩ : syracuseStep 1312703 = 1969055) B1969055
theorem B1312735 : Blo 1311974 1312735 := bstep (se 1 (by rfl) ⟨984551, by rfl⟩ : syracuseStep 1312735 = 1969103) B1969103
theorem B1312795 : Blo 1311974 1312795 := bstep (se 1 (by rfl) ⟨984596, by rfl⟩ : syracuseStep 1312795 = 1969193) B1969193
theorem B1312799 : Blo 1311974 1312799 := bstep (se 1 (by rfl) ⟨984599, by rfl⟩ : syracuseStep 1312799 = 1969199) B1969199
theorem B1312815 : Blo 1311974 1312815 := bstep (se 1 (by rfl) ⟨984611, by rfl⟩ : syracuseStep 1312815 = 1969223) B1969223
theorem B2492603 : Blo 1311974 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B1312991 : Blo 1311974 1312991 := bstep (se 1 (by rfl) ⟨984743, by rfl⟩ : syracuseStep 1312991 = 1969487) B1969487
theorem B1313051 : Blo 1311974 1313051 := bstep (se 1 (by rfl) ⟨984788, by rfl⟩ : syracuseStep 1313051 = 1969577) B1969577
theorem B1313151 : Blo 1311974 1313151 := bstep (se 1 (by rfl) ⟨984863, by rfl⟩ : syracuseStep 1313151 = 1969727) B1969727
theorem B8415713 : Blo 1311974 8415713 := bstep (se 2 (by rfl) ⟨3155892, by rfl⟩ : syracuseStep 8415713 = 6311785) B6311785
theorem B136440301 : Blo 1311974 136440301 := bstep (se 3 (by rfl) ⟨25582556, by rfl⟩ : syracuseStep 136440301 = 51165113) B51165113
theorem B4434425 : Blo 1311974 4434425 := bstep (se 2 (by rfl) ⟨1662909, by rfl⟩ : syracuseStep 4434425 = 3325819) B3325819
theorem B1313327 : Blo 1311974 1313327 := bstep (se 1 (by rfl) ⟨984995, by rfl⟩ : syracuseStep 1313327 = 1969991) B1969991
theorem B11209265 : Blo 1311974 11209265 := bstep (se 2 (by rfl) ⟨4203474, by rfl⟩ : syracuseStep 11209265 = 8406949) B8406949
theorem B1968743 : Blo 1311974 1968743 := bstep (se 1 (by rfl) ⟨1476557, by rfl⟩ : syracuseStep 1968743 = 2953115) B2953115
theorem B1313383 : Blo 1311974 1313383 := bstep (se 1 (by rfl) ⟨985037, by rfl⟩ : syracuseStep 1313383 = 1970075) B1970075
theorem B2493089 : Blo 1311974 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B2214695 : Blo 1311974 2214695 := bstep (se 1 (by rfl) ⟨1661021, by rfl⟩ : syracuseStep 2214695 = 3322043) B3322043
theorem B1968935 : Blo 1311974 1968935 := bstep (se 1 (by rfl) ⟨1476701, by rfl⟩ : syracuseStep 1968935 = 2953403) B2953403
theorem B9964457 : Blo 1311974 9964457 := bstep (se 2 (by rfl) ⟨3736671, by rfl⟩ : syracuseStep 9964457 = 7473343) B7473343
theorem B1313759 : Blo 1311974 1313759 := bstep (se 1 (by rfl) ⟨985319, by rfl⟩ : syracuseStep 1313759 = 1970639) B1970639
theorem B2952161 : Blo 1311974 2952161 := bstep (se 2 (by rfl) ⟨1107060, by rfl⟩ : syracuseStep 2952161 = 2214121) B2214121
theorem B1313787 : Blo 1311974 1313787 := bstep (se 1 (by rfl) ⟨985340, by rfl⟩ : syracuseStep 1313787 = 1970681) B1970681
theorem B1313855 : Blo 1311974 1313855 := bstep (se 1 (by rfl) ⟨985391, by rfl⟩ : syracuseStep 1313855 = 1970783) B1970783
theorem B2215019 : Blo 1311974 2215019 := bstep (se 1 (by rfl) ⟨1661264, by rfl⟩ : syracuseStep 2215019 = 3322529) B3322529
theorem B1969259 : Blo 1311974 1969259 := bstep (se 1 (by rfl) ⟨1476944, by rfl⟩ : syracuseStep 1969259 = 2953889) B2953889
theorem B6737039 : Blo 1311974 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B7482617 : Blo 1311974 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B14961995 : Blo 1311974 14961995 := bstep (se 1 (by rfl) ⟨11221496, by rfl⟩ : syracuseStep 14961995 = 22442993) B22442993
theorem B2952539 : Blo 1311974 2952539 := bstep (se 1 (by rfl) ⟨2214404, by rfl⟩ : syracuseStep 2952539 = 4428809) B4428809
theorem B1969499 : Blo 1311974 1969499 := bstep (se 1 (by rfl) ⟨1477124, by rfl⟩ : syracuseStep 1969499 = 2954249) B2954249
theorem B10104173 : Blo 1311974 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B2215289 : Blo 1311974 2215289 := bstep (se 2 (by rfl) ⟨830733, by rfl⟩ : syracuseStep 2215289 = 1661467) B1661467
theorem B1969529 : Blo 1311974 1969529 := bstep (se 2 (by rfl) ⟨738573, by rfl⟩ : syracuseStep 1969529 = 1477147) B1477147
theorem B2952575 : Blo 1311974 2952575 := bstep (se 1 (by rfl) ⟨2214431, by rfl⟩ : syracuseStep 2952575 = 4428863) B4428863
theorem B1969535 : Blo 1311974 1969535 := bstep (se 1 (by rfl) ⟨1477151, by rfl⟩ : syracuseStep 1969535 = 2954303) B2954303
theorem B8416943 : Blo 1311974 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B21589753 : Blo 1311974 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B5320511 : Blo 1311974 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B107720603 : Blo 1311974 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B10244029 : Blo 1311974 10244029 := bstep (se 3 (by rfl) ⟨1920755, by rfl⟩ : syracuseStep 10244029 = 3841511) B3841511
theorem B1970159 : Blo 1311974 1970159 := bstep (se 1 (by rfl) ⟨1477619, by rfl⟩ : syracuseStep 1970159 = 2955239) B2955239
theorem B1970171 : Blo 1311974 1970171 := bstep (se 1 (by rfl) ⟨1477628, by rfl⟩ : syracuseStep 1970171 = 2955257) B2955257
theorem B2215991 : Blo 1311974 2215991 := bstep (se 1 (by rfl) ⟨1661993, by rfl⟩ : syracuseStep 2215991 = 3323987) B3323987
theorem B1970231 : Blo 1311974 1970231 := bstep (se 1 (by rfl) ⟨1477673, by rfl⟩ : syracuseStep 1970231 = 2955347) B2955347
theorem B8417353 : Blo 1311974 8417353 := bstep (se 2 (by rfl) ⟨3156507, by rfl⟩ : syracuseStep 8417353 = 6313015) B6313015
theorem B1970279 : Blo 1311974 1970279 := bstep (se 1 (by rfl) ⟨1477709, by rfl⟩ : syracuseStep 1970279 = 2955419) B2955419
theorem B1970351 : Blo 1311974 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B14954705 : Blo 1311974 14954705 := bstep (se 2 (by rfl) ⟨5608014, by rfl⟩ : syracuseStep 14954705 = 11216029) B11216029
theorem B2216315 : Blo 1311974 2216315 := bstep (se 1 (by rfl) ⟨1662236, by rfl⟩ : syracuseStep 2216315 = 3324473) B3324473
theorem B1970555 : Blo 1311974 1970555 := bstep (se 1 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 1970555 = 2955833) B2955833
theorem B3740215 : Blo 1311974 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B31928903 : Blo 1311974 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B2216585 : Blo 1311974 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B1970825 : Blo 1311974 1970825 := bstep (se 2 (by rfl) ⟨739059, by rfl⟩ : syracuseStep 1970825 = 1478119) B1478119
theorem B12612347 : Blo 1311974 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B4985995 : Blo 1311974 4985995 := bstep (se 1 (by rfl) ⟨3739496, by rfl⟩ : syracuseStep 4985995 = 7478993) B7478993
theorem B2954447 : Blo 1311974 2954447 := bstep (se 1 (by rfl) ⟨2215835, by rfl⟩ : syracuseStep 2954447 = 4431671) B4431671
theorem B2954537 : Blo 1311974 2954537 := bstep (se 2 (by rfl) ⟨1107951, by rfl⟩ : syracuseStep 2954537 = 2215903) B2215903
theorem B9975149 : Blo 1311974 9975149 := bstep (se 3 (by rfl) ⟨1870340, by rfl⟩ : syracuseStep 9975149 = 3740681) B3740681
theorem B2954735 : Blo 1311974 2954735 := bstep (se 1 (by rfl) ⟨2216051, by rfl⟩ : syracuseStep 2954735 = 4432103) B4432103
theorem B1660763 : Blo 1311974 1660763 := bstep (se 1 (by rfl) ⟨1245572, by rfl⟩ : syracuseStep 1660763 = 2491145) B2491145
theorem B2955131 : Blo 1311974 2955131 := bstep (se 1 (by rfl) ⟨2216348, by rfl⟩ : syracuseStep 2955131 = 4432697) B4432697
theorem B4429727 : Blo 1311974 4429727 := bstep (se 1 (by rfl) ⟨3322295, by rfl⟩ : syracuseStep 4429727 = 6644591) B6644591
theorem B2955167 : Blo 1311974 2955167 := bstep (se 1 (by rfl) ⟨2216375, by rfl⟩ : syracuseStep 2955167 = 4432751) B4432751
theorem B16832609 : Blo 1311974 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B2955401 : Blo 1311974 2955401 := bstep (se 2 (by rfl) ⟨1108275, by rfl⟩ : syracuseStep 2955401 = 2216551) B2216551
theorem B4208831 : Blo 1311974 4208831 := bstep (se 1 (by rfl) ⟨3156623, by rfl⟩ : syracuseStep 4208831 = 6313247) B6313247
theorem B10098931 : Blo 1311974 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B9967859 : Blo 1311974 9967859 := bstep (se 1 (by rfl) ⟨7475894, by rfl⟩ : syracuseStep 9967859 = 14951789) B14951789
theorem B7477535 : Blo 1311974 7477535 := bstep (se 1 (by rfl) ⟨5608151, by rfl⟩ : syracuseStep 7477535 = 11216303) B11216303
theorem B2103583 : Blo 1311974 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B3324199 : Blo 1311974 3324199 := bstep (se 1 (by rfl) ⟨2493149, by rfl⟩ : syracuseStep 3324199 = 4986299) B4986299
theorem B2955617 : Blo 1311974 2955617 := bstep (se 2 (by rfl) ⟨1108356, by rfl⟩ : syracuseStep 2955617 = 2216713) B2216713
theorem B1350047 : Blo 1311974 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B2955707 : Blo 1311974 2955707 := bstep (se 1 (by rfl) ⟨2216780, by rfl⟩ : syracuseStep 2955707 = 4433561) B4433561
theorem B14948873 : Blo 1311974 14948873 := bstep (se 2 (by rfl) ⟨5605827, by rfl⟩ : syracuseStep 14948873 = 11211655) B11211655
theorem B5987015 : Blo 1311974 5987015 := bstep (se 1 (by rfl) ⟨4490261, by rfl⟩ : syracuseStep 5987015 = 8980523) B8980523
theorem B6732503 : Blo 1311974 6732503 := bstep (se 1 (by rfl) ⟨5049377, by rfl⟩ : syracuseStep 6732503 = 10098755) B10098755
theorem B8985367 : Blo 1311974 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B2956103 : Blo 1311974 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B590674961 : Blo 1311974 590674961 := bstep (se 2 (by rfl) ⟨221503110, by rfl⟩ : syracuseStep 590674961 = 443006221) B443006221
theorem B4799593 : Blo 1311974 4799593 := bstep (se 2 (by rfl) ⟨1799847, by rfl⟩ : syracuseStep 4799593 = 3599695) B3599695
theorem B4430969 : Blo 1311974 4430969 := bstep (se 2 (by rfl) ⟨1661613, by rfl⟩ : syracuseStep 4430969 = 3323227) B3323227
theorem B2956409 : Blo 1311974 2956409 := bstep (se 2 (by rfl) ⟨1108653, by rfl⟩ : syracuseStep 2956409 = 2217307) B2217307
theorem B11222387 : Blo 1311974 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B3153529 : Blo 1311974 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B9977579 : Blo 1311974 9977579 := bstep (se 1 (by rfl) ⟨7483184, by rfl⟩ : syracuseStep 9977579 = 14966369) B14966369
theorem B3153761 : Blo 1311974 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B1575133229 : Blo 1311974 1575133229 := bstep (se 3 (by rfl) ⟨295337480, by rfl⟩ : syracuseStep 1575133229 = 590674961) B590674961
theorem B11223137 : Blo 1311974 11223137 := bstep (se 2 (by rfl) ⟨4208676, by rfl⟩ : syracuseStep 11223137 = 8417353) B8417353
theorem B9969803 : Blo 1311974 9969803 := bstep (se 1 (by rfl) ⟨7477352, by rfl⟩ : syracuseStep 9969803 = 14954705) B14954705
theorem B233210137 : Blo 1311974 233210137 := bstep (se 2 (by rfl) ⟨87453801, by rfl⟩ : syracuseStep 233210137 = 174907603) B174907603
theorem B4432265 : Blo 1311974 4432265 := bstep (se 2 (by rfl) ⟨1662099, by rfl⟩ : syracuseStep 4432265 = 3324199) B3324199
theorem B181920401 : Blo 1311974 181920401 := bstep (se 2 (by rfl) ⟨68220150, by rfl⟩ : syracuseStep 181920401 = 136440301) B136440301
theorem B13485275 : Blo 1311974 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B1311995 : Blo 1311974 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B6645239 : Blo 1311974 6645239 := bstep (se 1 (by rfl) ⟨4983929, by rfl⟩ : syracuseStep 6645239 = 9967859) B9967859
theorem B4982381 : Blo 1311974 4982381 := bstep (se 3 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 4982381 = 1868393) B1868393
theorem B7472843 : Blo 1311974 7472843 := bstep (se 1 (by rfl) ⟨5604632, by rfl⟩ : syracuseStep 7472843 = 11209265) B11209265
theorem B1312495 : Blo 1311974 1312495 := bstep (se 1 (by rfl) ⟨984371, by rfl⟩ : syracuseStep 1312495 = 1968743) B1968743
theorem B1476463 : Blo 1311974 1476463 := bstep (se 1 (by rfl) ⟨1107347, by rfl⟩ : syracuseStep 1476463 = 2214695) B2214695
theorem B1312623 : Blo 1311974 1312623 := bstep (se 1 (by rfl) ⟨984467, by rfl⟩ : syracuseStep 1312623 = 1968935) B1968935
theorem B1968107 : Blo 1311974 1968107 := bstep (se 1 (by rfl) ⟨1476080, by rfl⟩ : syracuseStep 1968107 = 2952161) B2952161
theorem B1476679 : Blo 1311974 1476679 := bstep (se 1 (by rfl) ⟨1107509, by rfl⟩ : syracuseStep 1476679 = 2215019) B2215019
theorem B1312839 : Blo 1311974 1312839 := bstep (se 1 (by rfl) ⟨984629, by rfl⟩ : syracuseStep 1312839 = 1969259) B1969259
theorem B4491359 : Blo 1311974 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B4204705 : Blo 1311974 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B1968359 : Blo 1311974 1968359 := bstep (se 1 (by rfl) ⟨1476269, by rfl⟩ : syracuseStep 1968359 = 2952539) B2952539
theorem B1312999 : Blo 1311974 1312999 := bstep (se 1 (by rfl) ⟨984749, by rfl⟩ : syracuseStep 1312999 = 1969499) B1969499
theorem B6736115 : Blo 1311974 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B7481591 : Blo 1311974 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B1476859 : Blo 1311974 1476859 := bstep (se 1 (by rfl) ⟨1107644, by rfl⟩ : syracuseStep 1476859 = 2215289) B2215289
theorem B1313019 : Blo 1311974 1313019 := bstep (se 1 (by rfl) ⟨984764, by rfl⟩ : syracuseStep 1313019 = 1969529) B1969529
theorem B1968383 : Blo 1311974 1968383 := bstep (se 1 (by rfl) ⟨1476287, by rfl⟩ : syracuseStep 1968383 = 2952575) B2952575
theorem B1313023 : Blo 1311974 1313023 := bstep (se 1 (by rfl) ⟨984767, by rfl⟩ : syracuseStep 1313023 = 1969535) B1969535
theorem B15960361 : Blo 1311974 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B1968521 : Blo 1311974 1968521 := bstep (se 2 (by rfl) ⟨738195, by rfl⟩ : syracuseStep 1968521 = 1476391) B1476391
theorem B13658705 : Blo 1311974 13658705 := bstep (se 2 (by rfl) ⟨5122014, by rfl⟩ : syracuseStep 13658705 = 10244029) B10244029
theorem B71813735 : Blo 1311974 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B1313439 : Blo 1311974 1313439 := bstep (se 1 (by rfl) ⟨985079, by rfl⟩ : syracuseStep 1313439 = 1970159) B1970159
theorem B1313447 : Blo 1311974 1313447 := bstep (se 1 (by rfl) ⟨985085, by rfl⟩ : syracuseStep 1313447 = 1970171) B1970171
theorem B1477327 : Blo 1311974 1477327 := bstep (se 1 (by rfl) ⟨1107995, by rfl⟩ : syracuseStep 1477327 = 2215991) B2215991
theorem B1313487 : Blo 1311974 1313487 := bstep (se 1 (by rfl) ⟨985115, by rfl⟩ : syracuseStep 1313487 = 1970231) B1970231
theorem B1313519 : Blo 1311974 1313519 := bstep (se 1 (by rfl) ⟨985139, by rfl⟩ : syracuseStep 1313519 = 1970279) B1970279
theorem B1313567 : Blo 1311974 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B1477543 : Blo 1311974 1477543 := bstep (se 1 (by rfl) ⟨1108157, by rfl⟩ : syracuseStep 1477543 = 2216315) B2216315
theorem B1313703 : Blo 1311974 1313703 := bstep (se 1 (by rfl) ⟨985277, by rfl⟩ : syracuseStep 1313703 = 1970555) B1970555
theorem B2804777 : Blo 1311974 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B21285935 : Blo 1311974 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B1477723 : Blo 1311974 1477723 := bstep (se 1 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 1477723 = 2216585) B2216585
theorem B1313883 : Blo 1311974 1313883 := bstep (se 1 (by rfl) ⟨985412, by rfl⟩ : syracuseStep 1313883 = 1970825) B1970825
theorem B7474301 : Blo 1311974 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B8408231 : Blo 1311974 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B5319863 : Blo 1311974 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B4205935 : Blo 1311974 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B1969631 : Blo 1311974 1969631 := bstep (se 1 (by rfl) ⟨1477223, by rfl⟩ : syracuseStep 1969631 = 2954447) B2954447
theorem B1969691 : Blo 1311974 1969691 := bstep (se 1 (by rfl) ⟨1477268, by rfl⟩ : syracuseStep 1969691 = 2954537) B2954537
theorem B84192803 : Blo 1311974 84192803 := bstep (se 1 (by rfl) ⟨63144602, by rfl⟩ : syracuseStep 84192803 = 126289205) B126289205
theorem B1969823 : Blo 1311974 1969823 := bstep (se 1 (by rfl) ⟨1477367, by rfl⟩ : syracuseStep 1969823 = 2954735) B2954735
theorem B12627647 : Blo 1311974 12627647 := bstep (se 1 (by rfl) ⟨9470735, by rfl⟩ : syracuseStep 12627647 = 18941471) B18941471
theorem B11980489 : Blo 1311974 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B3600125 : Blo 1311974 3600125 := bstep (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) B1350047
theorem B1970087 : Blo 1311974 1970087 := bstep (se 1 (by rfl) ⟨1477565, by rfl⟩ : syracuseStep 1970087 = 2955131) B2955131
theorem B2953151 : Blo 1311974 2953151 := bstep (se 1 (by rfl) ⟨2214863, by rfl⟩ : syracuseStep 2953151 = 4429727) B4429727
theorem B1970111 : Blo 1311974 1970111 := bstep (se 1 (by rfl) ⟨1477583, by rfl⟩ : syracuseStep 1970111 = 2955167) B2955167
theorem B1970267 : Blo 1311974 1970267 := bstep (se 1 (by rfl) ⟨1477700, by rfl⟩ : syracuseStep 1970267 = 2955401) B2955401
theorem B2805887 : Blo 1311974 2805887 := bstep (se 1 (by rfl) ⟨2104415, by rfl⟩ : syracuseStep 2805887 = 4208831) B4208831
theorem B23949445 : Blo 1311974 23949445 := bstep (se 4 (by rfl) ⟨2245260, by rfl⟩ : syracuseStep 23949445 = 4490521) B4490521
theorem B6647993 : Blo 1311974 6647993 := bstep (se 2 (by rfl) ⟨2492997, by rfl⟩ : syracuseStep 6647993 = 4985995) B4985995
theorem B4985023 : Blo 1311974 4985023 := bstep (se 1 (by rfl) ⟨3738767, by rfl⟩ : syracuseStep 4985023 = 7477535) B7477535
theorem B1970411 : Blo 1311974 1970411 := bstep (se 1 (by rfl) ⟨1477808, by rfl⟩ : syracuseStep 1970411 = 2955617) B2955617
theorem B1970471 : Blo 1311974 1970471 := bstep (se 1 (by rfl) ⟨1477853, by rfl⟩ : syracuseStep 1970471 = 2955707) B2955707
theorem B9965915 : Blo 1311974 9965915 := bstep (se 1 (by rfl) ⟨7474436, by rfl⟩ : syracuseStep 9965915 = 14948873) B14948873
theorem B1970735 : Blo 1311974 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B63861493 : Blo 1311974 63861493 := bstep (se 5 (by rfl) ⟨2993507, by rfl⟩ : syracuseStep 63861493 = 5987015) B5987015
theorem B2953979 : Blo 1311974 2953979 := bstep (se 1 (by rfl) ⟨2215484, by rfl⟩ : syracuseStep 2953979 = 4430969) B4430969
theorem B1970939 : Blo 1311974 1970939 := bstep (se 1 (by rfl) ⟨1478204, by rfl⟩ : syracuseStep 1970939 = 2956409) B2956409
theorem B9974663 : Blo 1311974 9974663 := bstep (se 1 (by rfl) ⟨7480997, by rfl⟩ : syracuseStep 9974663 = 14961995) B14961995
theorem B4428701 : Blo 1311974 4428701 := bstep (se 3 (by rfl) ⟨830381, by rfl⟩ : syracuseStep 4428701 = 1660763) B1660763
theorem B2102507 : Blo 1311974 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B5608871 : Blo 1311974 5608871 := bstep (se 1 (by rfl) ⟨4206653, by rfl⟩ : syracuseStep 5608871 = 8413307) B8413307
theorem B4429403 : Blo 1311974 4429403 := bstep (se 1 (by rfl) ⟨3322052, by rfl⟩ : syracuseStep 4429403 = 6644105) B6644105
theorem B13465241 : Blo 1311974 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B25597829 : Blo 1311974 25597829 := bstep (se 4 (by rfl) ⟨2399796, by rfl⟩ : syracuseStep 25597829 = 4799593) B4799593
theorem B4986953 : Blo 1311974 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B6650099 : Blo 1311974 6650099 := bstep (se 1 (by rfl) ⟨4987574, by rfl⟩ : syracuseStep 6650099 = 9975149) B9975149
theorem B4430267 : Blo 1311974 4430267 := bstep (se 1 (by rfl) ⟨3322700, by rfl⟩ : syracuseStep 4430267 = 6645401) B6645401
theorem B11221739 : Blo 1311974 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B1661735 : Blo 1311974 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B5610475 : Blo 1311974 5610475 := bstep (se 1 (by rfl) ⟨4207856, by rfl⟩ : syracuseStep 5610475 = 8415713) B8415713
theorem B2956283 : Blo 1311974 2956283 := bstep (se 1 (by rfl) ⟨2217212, by rfl⟩ : syracuseStep 2956283 = 4434425) B4434425
theorem B1662059 : Blo 1311974 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B6642809 : Blo 1311974 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B4488335 : Blo 1311974 4488335 := bstep (se 1 (by rfl) ⟨3366251, by rfl⟩ : syracuseStep 4488335 = 6732503) B6732503
theorem B6642971 : Blo 1311974 6642971 := bstep (se 1 (by rfl) ⟨4982228, by rfl⟩ : syracuseStep 6642971 = 9964457) B9964457
theorem B4988411 : Blo 1311974 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B28786337 : Blo 1311974 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B5611295 : Blo 1311974 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B6651719 : Blo 1311974 6651719 := bstep (se 1 (by rfl) ⟨4988789, by rfl⟩ : syracuseStep 6651719 = 9977579) B9977579
theorem B3547007 : Blo 1311974 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B4431995 : Blo 1311974 4431995 := bstep (se 1 (by rfl) ⟨3323996, by rfl⟩ : syracuseStep 4431995 = 6647993) B6647993
theorem B31932593 : Blo 1311974 31932593 := bstep (se 2 (by rfl) ⟨11974722, by rfl⟩ : syracuseStep 31932593 = 23949445) B23949445
theorem B6643943 : Blo 1311974 6643943 := bstep (se 1 (by rfl) ⟨4982957, by rfl⟩ : syracuseStep 6643943 = 9965915) B9965915
theorem B4432157 : Blo 1311974 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B1401671 : Blo 1311974 1401671 := bstep (se 1 (by rfl) ⟨1051253, by rfl⟩ : syracuseStep 1401671 = 2102507) B2102507
theorem B85148657 : Blo 1311974 85148657 := bstep (se 2 (by rfl) ⟨31930746, by rfl⟩ : syracuseStep 85148657 = 63861493) B63861493
theorem B4981895 : Blo 1311974 4981895 := bstep (se 1 (by rfl) ⟨3736421, by rfl⟩ : syracuseStep 4981895 = 7472843) B7472843
theorem B7480633 : Blo 1311974 7480633 := bstep (se 2 (by rfl) ⟨2805237, by rfl⟩ : syracuseStep 7480633 = 5610475) B5610475
theorem B1312071 : Blo 1311974 1312071 := bstep (se 1 (by rfl) ⟨984053, by rfl⟩ : syracuseStep 1312071 = 1968107) B1968107
theorem B1312239 : Blo 1311974 1312239 := bstep (se 1 (by rfl) ⟨984179, by rfl⟩ : syracuseStep 1312239 = 1968359) B1968359
theorem B4490743 : Blo 1311974 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B4433399 : Blo 1311974 4433399 := bstep (se 1 (by rfl) ⟨3325049, by rfl⟩ : syracuseStep 4433399 = 6650099) B6650099
theorem B1312255 : Blo 1311974 1312255 := bstep (se 1 (by rfl) ⟨984191, by rfl⟩ : syracuseStep 1312255 = 1968383) B1968383
theorem B1312347 : Blo 1311974 1312347 := bstep (se 1 (by rfl) ⟨984260, by rfl⟩ : syracuseStep 1312347 = 1968521) B1968521
theorem B47875823 : Blo 1311974 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B7481159 : Blo 1311974 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B1869851 : Blo 1311974 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B14190623 : Blo 1311974 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B4982867 : Blo 1311974 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B2992223 : Blo 1311974 2992223 := bstep (se 1 (by rfl) ⟨2244167, by rfl⟩ : syracuseStep 2992223 = 4488335) B4488335
theorem B5605487 : Blo 1311974 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B1313087 : Blo 1311974 1313087 := bstep (se 1 (by rfl) ⟨984815, by rfl⟩ : syracuseStep 1313087 = 1969631) B1969631
theorem B1313127 : Blo 1311974 1313127 := bstep (se 1 (by rfl) ⟨984845, by rfl⟩ : syracuseStep 1313127 = 1969691) B1969691
theorem B1313215 : Blo 1311974 1313215 := bstep (se 1 (by rfl) ⟨984911, by rfl⟩ : syracuseStep 1313215 = 1969823) B1969823
theorem B1968617 : Blo 1311974 1968617 := bstep (se 2 (by rfl) ⟨738231, by rfl⟩ : syracuseStep 1968617 = 1476463) B1476463
theorem B4434479 : Blo 1311974 4434479 := bstep (se 1 (by rfl) ⟨3325859, by rfl⟩ : syracuseStep 4434479 = 6651719) B6651719
theorem B1313391 : Blo 1311974 1313391 := bstep (se 1 (by rfl) ⟨985043, by rfl⟩ : syracuseStep 1313391 = 1970087) B1970087
theorem B1968767 : Blo 1311974 1968767 := bstep (se 1 (by rfl) ⟨1476575, by rfl⟩ : syracuseStep 1968767 = 2953151) B2953151
theorem B1313407 : Blo 1311974 1313407 := bstep (se 1 (by rfl) ⟨985055, by rfl⟩ : syracuseStep 1313407 = 1970111) B1970111
theorem B1313511 : Blo 1311974 1313511 := bstep (se 1 (by rfl) ⟨985133, by rfl⟩ : syracuseStep 1313511 = 1970267) B1970267
theorem B7482091 : Blo 1311974 7482091 := bstep (se 1 (by rfl) ⟨5611568, by rfl⟩ : syracuseStep 7482091 = 11223137) B11223137
theorem B6646535 : Blo 1311974 6646535 := bstep (se 1 (by rfl) ⟨4984901, by rfl⟩ : syracuseStep 6646535 = 9969803) B9969803
theorem B1968905 : Blo 1311974 1968905 := bstep (se 2 (by rfl) ⟨738339, by rfl⟩ : syracuseStep 1968905 = 1476679) B1476679
theorem B1313607 : Blo 1311974 1313607 := bstep (se 1 (by rfl) ⟨985205, by rfl⟩ : syracuseStep 1313607 = 1970411) B1970411
theorem B1313647 : Blo 1311974 1313647 := bstep (se 1 (by rfl) ⟨985235, by rfl⟩ : syracuseStep 1313647 = 1970471) B1970471
theorem B5606273 : Blo 1311974 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B6646697 : Blo 1311974 6646697 := bstep (se 2 (by rfl) ⟨2492511, by rfl⟩ : syracuseStep 6646697 = 4985023) B4985023
theorem B1969145 : Blo 1311974 1969145 := bstep (se 2 (by rfl) ⟨738429, by rfl⟩ : syracuseStep 1969145 = 1476859) B1476859
theorem B7482365 : Blo 1311974 7482365 := bstep (se 3 (by rfl) ⟨1402943, by rfl⟩ : syracuseStep 7482365 = 2805887) B2805887
theorem B1313823 : Blo 1311974 1313823 := bstep (se 1 (by rfl) ⟨985367, by rfl⟩ : syracuseStep 1313823 = 1970735) B1970735
theorem B310946849 : Blo 1311974 310946849 := bstep (se 2 (by rfl) ⟨116605068, by rfl⟩ : syracuseStep 310946849 = 233210137) B233210137
theorem B1969319 : Blo 1311974 1969319 := bstep (se 1 (by rfl) ⟨1476989, by rfl⟩ : syracuseStep 1969319 = 2953979) B2953979
theorem B1313959 : Blo 1311974 1313959 := bstep (se 1 (by rfl) ⟨985469, by rfl⟩ : syracuseStep 1313959 = 1970939) B1970939
theorem B2952467 : Blo 1311974 2952467 := bstep (se 1 (by rfl) ⟨2214350, by rfl⟩ : syracuseStep 2952467 = 4428701) B4428701
theorem B8990183 : Blo 1311974 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B1969769 : Blo 1311974 1969769 := bstep (se 2 (by rfl) ⟨738663, by rfl⟩ : syracuseStep 1969769 = 1477327) B1477327
theorem B3739247 : Blo 1311974 3739247 := bstep (se 1 (by rfl) ⟨2804435, by rfl⟩ : syracuseStep 3739247 = 5608871) B5608871
theorem B2952935 : Blo 1311974 2952935 := bstep (se 1 (by rfl) ⟨2214701, by rfl⟩ : syracuseStep 2952935 = 4429403) B4429403
theorem B3321587 : Blo 1311974 3321587 := bstep (se 1 (by rfl) ⟨2491190, by rfl⟩ : syracuseStep 3321587 = 4982381) B4982381
theorem B1970057 : Blo 1311974 1970057 := bstep (se 2 (by rfl) ⟨738771, by rfl⟩ : syracuseStep 1970057 = 1477543) B1477543
theorem B2994239 : Blo 1311974 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B1970297 : Blo 1311974 1970297 := bstep (se 2 (by rfl) ⟨738861, by rfl⟩ : syracuseStep 1970297 = 1477723) B1477723
theorem B2953511 : Blo 1311974 2953511 := bstep (se 1 (by rfl) ⟨2215133, by rfl⟩ : syracuseStep 2953511 = 4430267) B4430267
theorem B9105803 : Blo 1311974 9105803 := bstep (se 1 (by rfl) ⟨6829352, by rfl⟩ : syracuseStep 9105803 = 13658705) B13658705
theorem B5607913 : Blo 1311974 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B1970855 : Blo 1311974 1970855 := bstep (se 1 (by rfl) ⟨1478141, by rfl⟩ : syracuseStep 1970855 = 2956283) B2956283
theorem B4428539 : Blo 1311974 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B14963453 : Blo 1311974 14963453 := bstep (se 3 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 14963453 = 5611295) B5611295
theorem B4428647 : Blo 1311974 4428647 := bstep (se 1 (by rfl) ⟨3321485, by rfl⟩ : syracuseStep 4428647 = 6642971) B6642971
theorem B68260877 : Blo 1311974 68260877 := bstep (se 3 (by rfl) ⟨12798914, by rfl⟩ : syracuseStep 68260877 = 25597829) B25597829
theorem B56128535 : Blo 1311974 56128535 := bstep (se 1 (by rfl) ⟨42096401, by rfl⟩ : syracuseStep 56128535 = 84192803) B84192803
theorem B19190891 : Blo 1311974 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B8418431 : Blo 1311974 8418431 := bstep (se 1 (by rfl) ⟨6313823, by rfl⟩ : syracuseStep 8418431 = 12627647) B12627647
theorem B2364671 : Blo 1311974 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B4200355277 : Blo 1311974 4200355277 := bstep (se 3 (by rfl) ⟨787566614, by rfl⟩ : syracuseStep 4200355277 = 1575133229) B1575133229
theorem B2954843 : Blo 1311974 2954843 := bstep (se 1 (by rfl) ⟨2216132, by rfl⟩ : syracuseStep 2954843 = 4432265) B4432265
theorem B21280481 : Blo 1311974 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B121280267 : Blo 1311974 121280267 := bstep (se 1 (by rfl) ⟨90960200, by rfl⟩ : syracuseStep 121280267 = 181920401) B181920401
theorem B6649775 : Blo 1311974 6649775 := bstep (se 1 (by rfl) ⟨4987331, by rfl⟩ : syracuseStep 6649775 = 9974663) B9974663
theorem B4430159 : Blo 1311974 4430159 := bstep (se 1 (by rfl) ⟨3322619, by rfl⟩ : syracuseStep 4430159 = 6645239) B6645239
theorem B8976827 : Blo 1311974 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B3324635 : Blo 1311974 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B4987727 : Blo 1311974 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B4431293 : Blo 1311974 4431293 := bstep (se 3 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 4431293 = 1661735) B1661735
theorem B3546575 : Blo 1311974 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B15973985 : Blo 1311974 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B3325607 : Blo 1311974 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B2400083 : Blo 1311974 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B6070535 : Blo 1311974 6070535 := bstep (se 1 (by rfl) ⟨4552901, by rfl⟩ : syracuseStep 6070535 = 9105803) B9105803
theorem B51175709 : Blo 1311974 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B45507251 : Blo 1311974 45507251 := bstep (se 1 (by rfl) ⟨34130438, by rfl⟩ : syracuseStep 45507251 = 68260877) B68260877
theorem B5612287 : Blo 1311974 5612287 := bstep (se 1 (by rfl) ⟨4209215, by rfl⟩ : syracuseStep 5612287 = 8418431) B8418431
theorem B31917215 : Blo 1311974 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B4433183 : Blo 1311974 4433183 := bstep (se 1 (by rfl) ⟨3324887, by rfl⟩ : syracuseStep 4433183 = 6649775) B6649775
theorem B3736991 : Blo 1311974 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B1312411 : Blo 1311974 1312411 := bstep (se 1 (by rfl) ⟨984308, by rfl⟩ : syracuseStep 1312411 = 1968617) B1968617
theorem B1312511 : Blo 1311974 1312511 := bstep (se 1 (by rfl) ⟨984383, by rfl⟩ : syracuseStep 1312511 = 1968767) B1968767
theorem B1312603 : Blo 1311974 1312603 := bstep (se 1 (by rfl) ⟨984452, by rfl⟩ : syracuseStep 1312603 = 1968905) B1968905
theorem B3737515 : Blo 1311974 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B1312763 : Blo 1311974 1312763 := bstep (se 1 (by rfl) ⟨984572, by rfl⟩ : syracuseStep 1312763 = 1969145) B1969145
theorem B1312879 : Blo 1311974 1312879 := bstep (se 1 (by rfl) ⟨984659, by rfl⟩ : syracuseStep 1312879 = 1969319) B1969319
theorem B1968311 : Blo 1311974 1968311 := bstep (se 1 (by rfl) ⟨1476233, by rfl⟩ : syracuseStep 1968311 = 2952467) B2952467
theorem B3737789 : Blo 1311974 3737789 := bstep (se 3 (by rfl) ⟨700835, by rfl⟩ : syracuseStep 3737789 = 1401671) B1401671
theorem B1313179 : Blo 1311974 1313179 := bstep (se 1 (by rfl) ⟨984884, by rfl⟩ : syracuseStep 1313179 = 1969769) B1969769
theorem B2492831 : Blo 1311974 2492831 := bstep (se 1 (by rfl) ⟨1869623, by rfl⟩ : syracuseStep 2492831 = 3739247) B3739247
theorem B1968623 : Blo 1311974 1968623 := bstep (se 1 (by rfl) ⟨1476467, by rfl⟩ : syracuseStep 1968623 = 2952935) B2952935
theorem B2214391 : Blo 1311974 2214391 := bstep (se 1 (by rfl) ⟨1660793, by rfl⟩ : syracuseStep 2214391 = 3321587) B3321587
theorem B1313371 : Blo 1311974 1313371 := bstep (se 1 (by rfl) ⟨985028, by rfl⟩ : syracuseStep 1313371 = 1970057) B1970057
theorem B1313531 : Blo 1311974 1313531 := bstep (se 1 (by rfl) ⟨985148, by rfl⟩ : syracuseStep 1313531 = 1970297) B1970297
theorem B1969007 : Blo 1311974 1969007 := bstep (se 1 (by rfl) ⟨1476755, by rfl⟩ : syracuseStep 1969007 = 2953511) B2953511
theorem B1313903 : Blo 1311974 1313903 := bstep (se 1 (by rfl) ⟨985427, by rfl⟩ : syracuseStep 1313903 = 1970855) B1970855
theorem B2952359 : Blo 1311974 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B2952431 : Blo 1311974 2952431 := bstep (se 1 (by rfl) ⟨2214323, by rfl⟩ : syracuseStep 2952431 = 4428647) B4428647
theorem B56765771 : Blo 1311974 56765771 := bstep (se 1 (by rfl) ⟨42574328, by rfl⟩ : syracuseStep 56765771 = 85148657) B85148657
theorem B3321263 : Blo 1311974 3321263 := bstep (se 1 (by rfl) ⟨2490947, by rfl⟩ : syracuseStep 3321263 = 4981895) B4981895
theorem B102403541 : Blo 1311974 102403541 := bstep (se 7 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 102403541 = 2400083) B2400083
theorem B1969895 : Blo 1311974 1969895 := bstep (se 1 (by rfl) ⟨1477421, by rfl⟩ : syracuseStep 1969895 = 2954843) B2954843
theorem B3321911 : Blo 1311974 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B1994815 : Blo 1311974 1994815 := bstep (se 1 (by rfl) ⟨1496111, by rfl⟩ : syracuseStep 1994815 = 2992223) B2992223
theorem B2953439 : Blo 1311974 2953439 := bstep (se 1 (by rfl) ⟨2215079, by rfl⟩ : syracuseStep 2953439 = 4430159) B4430159
theorem B5984551 : Blo 1311974 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B9974177 : Blo 1311974 9974177 := bstep (se 2 (by rfl) ⟨3740316, by rfl⟩ : syracuseStep 9974177 = 7480633) B7480633
theorem B2216423 : Blo 1311974 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B2954195 : Blo 1311974 2954195 := bstep (se 1 (by rfl) ⟨2215646, by rfl⟩ : syracuseStep 2954195 = 4431293) B4431293
theorem B2364383 : Blo 1311974 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B5993455 : Blo 1311974 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B2217071 : Blo 1311974 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B1996159 : Blo 1311974 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B4986269 : Blo 1311974 4986269 := bstep (se 3 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 4986269 = 1869851) B1869851
theorem B2954663 : Blo 1311974 2954663 := bstep (se 1 (by rfl) ⟨2215997, by rfl⟩ : syracuseStep 2954663 = 4431995) B4431995
theorem B21288395 : Blo 1311974 21288395 := bstep (se 1 (by rfl) ⟨15966296, by rfl⟩ : syracuseStep 21288395 = 31932593) B31932593
theorem B4429295 : Blo 1311974 4429295 := bstep (se 1 (by rfl) ⟨3321971, by rfl⟩ : syracuseStep 4429295 = 6643943) B6643943
theorem B2954771 : Blo 1311974 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B9975635 : Blo 1311974 9975635 := bstep (se 1 (by rfl) ⟨7481726, by rfl⟩ : syracuseStep 9975635 = 14963453) B14963453
theorem B7477217 : Blo 1311974 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B6305789 : Blo 1311974 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B37419023 : Blo 1311974 37419023 := bstep (se 1 (by rfl) ⟨28064267, by rfl⟩ : syracuseStep 37419023 = 56128535) B56128535
theorem B2800236851 : Blo 1311974 2800236851 := bstep (se 1 (by rfl) ⟨2100177638, by rfl⟩ : syracuseStep 2800236851 = 4200355277) B4200355277
theorem B9976121 : Blo 1311974 9976121 := bstep (se 2 (by rfl) ⟨3741045, by rfl⟩ : syracuseStep 9976121 = 7482091) B7482091
theorem B2955599 : Blo 1311974 2955599 := bstep (se 1 (by rfl) ⟨2216699, by rfl⟩ : syracuseStep 2955599 = 4433399) B4433399
theorem B14186987 : Blo 1311974 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B80853511 : Blo 1311974 80853511 := bstep (se 1 (by rfl) ⟨60640133, by rfl⟩ : syracuseStep 80853511 = 121280267) B121280267
theorem B4987439 : Blo 1311974 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B9460415 : Blo 1311974 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B2956319 : Blo 1311974 2956319 := bstep (se 1 (by rfl) ⟨2217239, by rfl⟩ : syracuseStep 2956319 = 4434479) B4434479
theorem B4431023 : Blo 1311974 4431023 := bstep (se 1 (by rfl) ⟨3323267, by rfl⟩ : syracuseStep 4431023 = 6646535) B6646535
theorem B3325151 : Blo 1311974 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B4431131 : Blo 1311974 4431131 := bstep (se 1 (by rfl) ⟨3323348, by rfl⟩ : syracuseStep 4431131 = 6646697) B6646697
theorem B5987657 : Blo 1311974 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B4988243 : Blo 1311974 4988243 := bstep (se 1 (by rfl) ⟨3741182, by rfl⟩ : syracuseStep 4988243 = 7482365) B7482365
theorem B207297899 : Blo 1311974 207297899 := bstep (se 1 (by rfl) ⟨155473424, by rfl⟩ : syracuseStep 207297899 = 310946849) B310946849
theorem B10649323 : Blo 1311974 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B4047023 : Blo 1311974 4047023 := bstep (se 1 (by rfl) ⟨3035267, by rfl⟩ : syracuseStep 4047023 = 6070535) B6070535
theorem B7979401 : Blo 1311974 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B2491327 : Blo 1311974 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B4203859 : Blo 1311974 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B24946015 : Blo 1311974 24946015 := bstep (se 1 (by rfl) ⟨18709511, by rfl⟩ : syracuseStep 24946015 = 37419023) B37419023
theorem B1312207 : Blo 1311974 1312207 := bstep (se 1 (by rfl) ⟨984155, by rfl⟩ : syracuseStep 1312207 = 1968311) B1968311
theorem B2491859 : Blo 1311974 2491859 := bstep (se 1 (by rfl) ⟨1868894, by rfl⟩ : syracuseStep 2491859 = 3737789) B3737789
theorem B1312415 : Blo 1311974 1312415 := bstep (se 1 (by rfl) ⟨984311, by rfl⟩ : syracuseStep 1312415 = 1968623) B1968623
theorem B1312671 : Blo 1311974 1312671 := bstep (se 1 (by rfl) ⟨984503, by rfl⟩ : syracuseStep 1312671 = 1969007) B1969007
theorem B1968239 : Blo 1311974 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B1968287 : Blo 1311974 1968287 := bstep (se 1 (by rfl) ⟨1476215, by rfl⟩ : syracuseStep 1968287 = 2952431) B2952431
theorem B3991771 : Blo 1311974 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B2214175 : Blo 1311974 2214175 := bstep (se 1 (by rfl) ⟨1660631, by rfl⟩ : syracuseStep 2214175 = 3321263) B3321263
theorem B14199097 : Blo 1311974 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B1313263 : Blo 1311974 1313263 := bstep (se 1 (by rfl) ⟨984947, by rfl⟩ : syracuseStep 1313263 = 1969895) B1969895
theorem B4983353 : Blo 1311974 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B2214607 : Blo 1311974 2214607 := bstep (se 1 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 2214607 = 3321911) B3321911
theorem B1968959 : Blo 1311974 1968959 := bstep (se 1 (by rfl) ⟨1476719, by rfl⟩ : syracuseStep 1968959 = 2953439) B2953439
theorem B1477615 : Blo 1311974 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B30338167 : Blo 1311974 30338167 := bstep (se 1 (by rfl) ⟨22753625, by rfl⟩ : syracuseStep 30338167 = 45507251) B45507251
theorem B1969463 : Blo 1311974 1969463 := bstep (se 1 (by rfl) ⟨1477097, by rfl⟩ : syracuseStep 1969463 = 2954195) B2954195
theorem B1576255 : Blo 1311974 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B2952521 : Blo 1311974 2952521 := bstep (se 2 (by rfl) ⟨1107195, by rfl⟩ : syracuseStep 2952521 = 2214391) B2214391
theorem B1478047 : Blo 1311974 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B21278143 : Blo 1311974 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B1969775 : Blo 1311974 1969775 := bstep (se 1 (by rfl) ⟨1477331, by rfl⟩ : syracuseStep 1969775 = 2954663) B2954663
theorem B14192263 : Blo 1311974 14192263 := bstep (se 1 (by rfl) ⟨10644197, by rfl⟩ : syracuseStep 14192263 = 21288395) B21288395
theorem B2952863 : Blo 1311974 2952863 := bstep (se 1 (by rfl) ⟨2214647, by rfl⟩ : syracuseStep 2952863 = 4429295) B4429295
theorem B7483049 : Blo 1311974 7483049 := bstep (se 2 (by rfl) ⟨2806143, by rfl⟩ : syracuseStep 7483049 = 5612287) B5612287
theorem B1969847 : Blo 1311974 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B7991273 : Blo 1311974 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B4984811 : Blo 1311974 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B1970399 : Blo 1311974 1970399 := bstep (se 1 (by rfl) ⟨1477799, by rfl⟩ : syracuseStep 1970399 = 2955599) B2955599
theorem B9457991 : Blo 1311974 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B1970879 : Blo 1311974 1970879 := bstep (se 1 (by rfl) ⟨1478159, by rfl⟩ : syracuseStep 1970879 = 2956319) B2956319
theorem B2954015 : Blo 1311974 2954015 := bstep (se 1 (by rfl) ⟨2215511, by rfl⟩ : syracuseStep 2954015 = 4431023) B4431023
theorem B2216767 : Blo 1311974 2216767 := bstep (se 1 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 2216767 = 3325151) B3325151
theorem B2954087 : Blo 1311974 2954087 := bstep (se 1 (by rfl) ⟨2215565, by rfl⟩ : syracuseStep 2954087 = 4431131) B4431131
theorem B37843847 : Blo 1311974 37843847 := bstep (se 1 (by rfl) ⟨28382885, by rfl⟩ : syracuseStep 37843847 = 56765771) B56765771
theorem B68269027 : Blo 1311974 68269027 := bstep (se 1 (by rfl) ⟨51201770, by rfl⟩ : syracuseStep 68269027 = 102403541) B102403541
theorem B2659753 : Blo 1311974 2659753 := bstep (se 2 (by rfl) ⟨997407, by rfl⟩ : syracuseStep 2659753 = 1994815) B1994815
theorem B34117139 : Blo 1311974 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B6649451 : Blo 1311974 6649451 := bstep (se 1 (by rfl) ⟨4987088, by rfl⟩ : syracuseStep 6649451 = 9974177) B9974177
theorem B107804681 : Blo 1311974 107804681 := bstep (se 2 (by rfl) ⟨40426755, by rfl⟩ : syracuseStep 107804681 = 80853511) B80853511
theorem B2955455 : Blo 1311974 2955455 := bstep (se 1 (by rfl) ⟨2216591, by rfl⟩ : syracuseStep 2955455 = 4433183) B4433183
theorem B3324179 : Blo 1311974 3324179 := bstep (se 1 (by rfl) ⟨2493134, by rfl⟩ : syracuseStep 3324179 = 4986269) B4986269
theorem B6650423 : Blo 1311974 6650423 := bstep (se 1 (by rfl) ⟨4987817, by rfl⟩ : syracuseStep 6650423 = 9975635) B9975635
theorem B1866824567 : Blo 1311974 1866824567 := bstep (se 1 (by rfl) ⟨1400118425, by rfl⟩ : syracuseStep 1866824567 = 2800236851) B2800236851
theorem B6650747 : Blo 1311974 6650747 := bstep (se 1 (by rfl) ⟨4988060, by rfl⟩ : syracuseStep 6650747 = 9976121) B9976121
theorem B1661887 : Blo 1311974 1661887 := bstep (se 1 (by rfl) ⟨1246415, by rfl⟩ : syracuseStep 1661887 = 2492831) B2492831
theorem B3324959 : Blo 1311974 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B6306943 : Blo 1311974 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B2661545 : Blo 1311974 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B3325495 : Blo 1311974 3325495 := bstep (se 1 (by rfl) ⟨2494121, by rfl⟩ : syracuseStep 3325495 = 4988243) B4988243
theorem B138198599 : Blo 1311974 138198599 := bstep (se 1 (by rfl) ⟨103648949, by rfl⟩ : syracuseStep 138198599 = 207297899) B207297899
theorem B18932129 : Blo 1311974 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B4432967 : Blo 1311974 4432967 := bstep (se 1 (by rfl) ⟨3324725, by rfl⟩ : syracuseStep 4432967 = 6649451) B6649451
theorem B71869787 : Blo 1311974 71869787 := bstep (se 1 (by rfl) ⟨53902340, by rfl⟩ : syracuseStep 71869787 = 107804681) B107804681
theorem B1312159 : Blo 1311974 1312159 := bstep (se 1 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 1312159 = 1968239) B1968239
theorem B1312191 : Blo 1311974 1312191 := bstep (se 1 (by rfl) ⟨984143, by rfl⟩ : syracuseStep 1312191 = 1968287) B1968287
theorem B4433615 : Blo 1311974 4433615 := bstep (se 1 (by rfl) ⟨3325211, by rfl⟩ : syracuseStep 4433615 = 6650423) B6650423
theorem B5605145 : Blo 1311974 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B33261353 : Blo 1311974 33261353 := bstep (se 2 (by rfl) ⟨12473007, by rfl⟩ : syracuseStep 33261353 = 24946015) B24946015
theorem B1312639 : Blo 1311974 1312639 := bstep (se 1 (by rfl) ⟨984479, by rfl⟩ : syracuseStep 1312639 = 1968959) B1968959
theorem B4433831 : Blo 1311974 4433831 := bstep (se 1 (by rfl) ⟨3325373, by rfl⟩ : syracuseStep 4433831 = 6650747) B6650747
theorem B28370857 : Blo 1311974 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B4433993 : Blo 1311974 4433993 := bstep (se 2 (by rfl) ⟨1662747, by rfl⟩ : syracuseStep 4433993 = 3325495) B3325495
theorem B1312975 : Blo 1311974 1312975 := bstep (se 1 (by rfl) ⟨984731, by rfl⟩ : syracuseStep 1312975 = 1969463) B1969463
theorem B1968347 : Blo 1311974 1968347 := bstep (se 1 (by rfl) ⟨1476260, by rfl⟩ : syracuseStep 1968347 = 2952521) B2952521
theorem B1313183 : Blo 1311974 1313183 := bstep (se 1 (by rfl) ⟨984887, by rfl⟩ : syracuseStep 1313183 = 1969775) B1969775
theorem B1968575 : Blo 1311974 1968575 := bstep (se 1 (by rfl) ⟨1476431, by rfl⟩ : syracuseStep 1968575 = 2952863) B2952863
theorem B1313231 : Blo 1311974 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B1313599 : Blo 1311974 1313599 := bstep (se 1 (by rfl) ⟨985199, by rfl⟩ : syracuseStep 1313599 = 1970399) B1970399
theorem B2952233 : Blo 1311974 2952233 := bstep (se 2 (by rfl) ⟨1107087, by rfl⟩ : syracuseStep 2952233 = 2214175) B2214175
theorem B7097453 : Blo 1311974 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B10792061 : Blo 1311974 10792061 := bstep (se 3 (by rfl) ⟨2023511, by rfl⟩ : syracuseStep 10792061 = 4047023) B4047023
theorem B1313919 : Blo 1311974 1313919 := bstep (se 1 (by rfl) ⟨985439, by rfl⟩ : syracuseStep 1313919 = 1970879) B1970879
theorem B1969343 : Blo 1311974 1969343 := bstep (se 1 (by rfl) ⟨1477007, by rfl⟩ : syracuseStep 1969343 = 2954015) B2954015
theorem B1969391 : Blo 1311974 1969391 := bstep (se 1 (by rfl) ⟨1477043, by rfl⟩ : syracuseStep 1969391 = 2954087) B2954087
theorem B2952809 : Blo 1311974 2952809 := bstep (se 2 (by rfl) ⟨1107303, by rfl⟩ : syracuseStep 2952809 = 2214607) B2214607
theorem B22744759 : Blo 1311974 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B3321769 : Blo 1311974 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B2215849 : Blo 1311974 2215849 := bstep (se 2 (by rfl) ⟨830943, by rfl⟩ : syracuseStep 2215849 = 1661887) B1661887
theorem B91025369 : Blo 1311974 91025369 := bstep (se 2 (by rfl) ⟨34134513, by rfl⟩ : syracuseStep 91025369 = 68269027) B68269027
theorem B1970153 : Blo 1311974 1970153 := bstep (se 2 (by rfl) ⟨738807, by rfl⟩ : syracuseStep 1970153 = 1477615) B1477615
theorem B1970303 : Blo 1311974 1970303 := bstep (se 1 (by rfl) ⟨1477727, by rfl⟩ : syracuseStep 1970303 = 2955455) B2955455
theorem B8409257 : Blo 1311974 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B2216119 : Blo 1311974 2216119 := bstep (se 1 (by rfl) ⟨1662089, by rfl⟩ : syracuseStep 2216119 = 3324179) B3324179
theorem B3322235 : Blo 1311974 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B2101673 : Blo 1311974 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B1970729 : Blo 1311974 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B1244549711 : Blo 1311974 1244549711 := bstep (se 1 (by rfl) ⟨933412283, by rfl⟩ : syracuseStep 1244549711 = 1866824567) B1866824567
theorem B2216639 : Blo 1311974 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B92132399 : Blo 1311974 92132399 := bstep (se 1 (by rfl) ⟨69099299, by rfl⟩ : syracuseStep 92132399 = 138198599) B138198599
theorem B3323207 : Blo 1311974 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B6305327 : Blo 1311974 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B5322361 : Blo 1311974 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B10639201 : Blo 1311974 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B25229231 : Blo 1311974 25229231 := bstep (se 1 (by rfl) ⟨18921923, by rfl⟩ : syracuseStep 25229231 = 37843847) B37843847
theorem B1661239 : Blo 1311974 1661239 := bstep (se 1 (by rfl) ⟨1245929, by rfl⟩ : syracuseStep 1661239 = 2491859) B2491859
theorem B2955689 : Blo 1311974 2955689 := bstep (se 2 (by rfl) ⟨1108383, by rfl⟩ : syracuseStep 2955689 = 2216767) B2216767
theorem B40450889 : Blo 1311974 40450889 := bstep (se 2 (by rfl) ⟨15169083, by rfl⟩ : syracuseStep 40450889 = 30338167) B30338167
theorem B3546337 : Blo 1311974 3546337 := bstep (se 2 (by rfl) ⟨1329876, by rfl⟩ : syracuseStep 3546337 = 2659753) B2659753
theorem B18923017 : Blo 1311974 18923017 := bstep (se 2 (by rfl) ⟨7096131, by rfl⟩ : syracuseStep 18923017 = 14192263) B14192263
theorem B4988699 : Blo 1311974 4988699 := bstep (se 1 (by rfl) ⟨3741524, by rfl⟩ : syracuseStep 4988699 = 7483049) B7483049
theorem B5327515 : Blo 1311974 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B4203551 : Blo 1311974 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B5604461 : Blo 1311974 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B3736763 : Blo 1311974 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B16819487 : Blo 1311974 16819487 := bstep (se 1 (by rfl) ⟨12614615, by rfl⟩ : syracuseStep 16819487 = 25229231) B25229231
theorem B1312231 : Blo 1311974 1312231 := bstep (se 1 (by rfl) ⟨984173, by rfl⟩ : syracuseStep 1312231 = 1968347) B1968347
theorem B1312383 : Blo 1311974 1312383 := bstep (se 1 (by rfl) ⟨984287, by rfl⟩ : syracuseStep 1312383 = 1968575) B1968575
theorem B4728449 : Blo 1311974 4728449 := bstep (se 2 (by rfl) ⟨1773168, by rfl⟩ : syracuseStep 4728449 = 3546337) B3546337
theorem B1968155 : Blo 1311974 1968155 := bstep (se 1 (by rfl) ⟨1476116, by rfl⟩ : syracuseStep 1968155 = 2952233) B2952233
theorem B7194707 : Blo 1311974 7194707 := bstep (se 1 (by rfl) ⟨5396030, by rfl⟩ : syracuseStep 7194707 = 10792061) B10792061
theorem B1312895 : Blo 1311974 1312895 := bstep (se 1 (by rfl) ⟨984671, by rfl⟩ : syracuseStep 1312895 = 1969343) B1969343
theorem B7096481 : Blo 1311974 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B1312927 : Blo 1311974 1312927 := bstep (se 1 (by rfl) ⟨984695, by rfl⟩ : syracuseStep 1312927 = 1969391) B1969391
theorem B1968539 : Blo 1311974 1968539 := bstep (se 1 (by rfl) ⟨1476404, by rfl⟩ : syracuseStep 1968539 = 2952809) B2952809
theorem B1313435 : Blo 1311974 1313435 := bstep (se 1 (by rfl) ⟨985076, by rfl⟩ : syracuseStep 1313435 = 1970153) B1970153
theorem B1313535 : Blo 1311974 1313535 := bstep (se 1 (by rfl) ⟨985151, by rfl⟩ : syracuseStep 1313535 = 1970303) B1970303
theorem B5606171 : Blo 1311974 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B2214823 : Blo 1311974 2214823 := bstep (se 1 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 2214823 = 3322235) B3322235
theorem B1313819 : Blo 1311974 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B2214985 : Blo 1311974 2214985 := bstep (se 2 (by rfl) ⟨830619, by rfl⟩ : syracuseStep 2214985 = 1661239) B1661239
theorem B1477759 : Blo 1311974 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B28413413 : Blo 1311974 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B2215471 : Blo 1311974 2215471 := bstep (se 1 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 2215471 = 3323207) B3323207
theorem B1970459 : Blo 1311974 1970459 := bstep (se 1 (by rfl) ⟨1477844, by rfl⟩ : syracuseStep 1970459 = 2955689) B2955689
theorem B4731635 : Blo 1311974 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B14185601 : Blo 1311974 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B37827809 : Blo 1311974 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B4429025 : Blo 1311974 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B2954465 : Blo 1311974 2954465 := bstep (se 2 (by rfl) ⟨1107924, by rfl⟩ : syracuseStep 2954465 = 2215849) B2215849
theorem B60683579 : Blo 1311974 60683579 := bstep (se 1 (by rfl) ⟨45512684, by rfl⟩ : syracuseStep 60683579 = 91025369) B91025369
theorem B2954825 : Blo 1311974 2954825 := bstep (se 2 (by rfl) ⟨1108059, by rfl⟩ : syracuseStep 2954825 = 2216119) B2216119
theorem B12621419 : Blo 1311974 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B829699807 : Blo 1311974 829699807 := bstep (se 1 (by rfl) ⟨622274855, by rfl⟩ : syracuseStep 829699807 = 1244549711) B1244549711
theorem B61421599 : Blo 1311974 61421599 := bstep (se 1 (by rfl) ⟨46066199, by rfl⟩ : syracuseStep 61421599 = 92132399) B92132399
theorem B2955311 : Blo 1311974 2955311 := bstep (se 1 (by rfl) ⟨2216483, by rfl⟩ : syracuseStep 2955311 = 4432967) B4432967
theorem B47913191 : Blo 1311974 47913191 := bstep (se 1 (by rfl) ⟨35934893, by rfl⟩ : syracuseStep 47913191 = 71869787) B71869787
theorem B2955743 : Blo 1311974 2955743 := bstep (se 1 (by rfl) ⟨2216807, by rfl⟩ : syracuseStep 2955743 = 4433615) B4433615
theorem B22174235 : Blo 1311974 22174235 := bstep (se 1 (by rfl) ⟨16630676, by rfl⟩ : syracuseStep 22174235 = 33261353) B33261353
theorem B2955887 : Blo 1311974 2955887 := bstep (se 1 (by rfl) ⟨2216915, by rfl⟩ : syracuseStep 2955887 = 4433831) B4433831
theorem B2955995 : Blo 1311974 2955995 := bstep (se 1 (by rfl) ⟨2216996, by rfl⟩ : syracuseStep 2955995 = 4433993) B4433993
theorem B26967259 : Blo 1311974 26967259 := bstep (se 1 (by rfl) ⟨20225444, by rfl⟩ : syracuseStep 26967259 = 40450889) B40450889
theorem B25230689 : Blo 1311974 25230689 := bstep (se 2 (by rfl) ⟨9461508, by rfl⟩ : syracuseStep 25230689 = 18923017) B18923017
theorem B30326345 : Blo 1311974 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B3325799 : Blo 1311974 3325799 := bstep (se 1 (by rfl) ⟨2494349, by rfl⟩ : syracuseStep 3325799 = 4988699) B4988699
theorem B81895465 : Blo 1311974 81895465 := bstep (se 2 (by rfl) ⟨30710799, by rfl⟩ : syracuseStep 81895465 = 61421599) B61421599
theorem B2802367 : Blo 1311974 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B3736307 : Blo 1311974 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B2491175 : Blo 1311974 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B8414279 : Blo 1311974 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B1312103 : Blo 1311974 1312103 := bstep (se 1 (by rfl) ⟨984077, by rfl⟩ : syracuseStep 1312103 = 1968155) B1968155
theorem B31942127 : Blo 1311974 31942127 := bstep (se 1 (by rfl) ⟨23956595, by rfl⟩ : syracuseStep 31942127 = 47913191) B47913191
theorem B1312359 : Blo 1311974 1312359 := bstep (se 1 (by rfl) ⟨984269, by rfl⟩ : syracuseStep 1312359 = 1968539) B1968539
theorem B35956345 : Blo 1311974 35956345 := bstep (se 2 (by rfl) ⟨13483629, by rfl⟩ : syracuseStep 35956345 = 26967259) B26967259
theorem B3737447 : Blo 1311974 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B12617693 : Blo 1311974 12617693 := bstep (se 3 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 12617693 = 4731635) B4731635
theorem B16820459 : Blo 1311974 16820459 := bstep (se 1 (by rfl) ⟨12615344, by rfl⟩ : syracuseStep 16820459 = 25230689) B25230689
theorem B1106266409 : Blo 1311974 1106266409 := bstep (se 2 (by rfl) ⟨414849903, by rfl⟩ : syracuseStep 1106266409 = 829699807) B829699807
theorem B18942275 : Blo 1311974 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B1313639 : Blo 1311974 1313639 := bstep (se 1 (by rfl) ⟨985229, by rfl⟩ : syracuseStep 1313639 = 1970459) B1970459
theorem B9457067 : Blo 1311974 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B25218539 : Blo 1311974 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B2952683 : Blo 1311974 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B1969643 : Blo 1311974 1969643 := bstep (se 1 (by rfl) ⟨1477232, by rfl⟩ : syracuseStep 1969643 = 2954465) B2954465
theorem B40455719 : Blo 1311974 40455719 := bstep (se 1 (by rfl) ⟨30341789, by rfl⟩ : syracuseStep 40455719 = 60683579) B60683579
theorem B1969883 : Blo 1311974 1969883 := bstep (se 1 (by rfl) ⟨1477412, by rfl⟩ : syracuseStep 1969883 = 2954825) B2954825
theorem B2953097 : Blo 1311974 2953097 := bstep (se 2 (by rfl) ⟨1107411, by rfl⟩ : syracuseStep 2953097 = 2214823) B2214823
theorem B1970207 : Blo 1311974 1970207 := bstep (se 1 (by rfl) ⟨1477655, by rfl⟩ : syracuseStep 1970207 = 2955311) B2955311
theorem B4796471 : Blo 1311974 4796471 := bstep (se 1 (by rfl) ⟨3597353, by rfl⟩ : syracuseStep 4796471 = 7194707) B7194707
theorem B2953313 : Blo 1311974 2953313 := bstep (se 2 (by rfl) ⟨1107492, by rfl⟩ : syracuseStep 2953313 = 2214985) B2214985
theorem B4730987 : Blo 1311974 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B1970345 : Blo 1311974 1970345 := bstep (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) B1477759
theorem B1970495 : Blo 1311974 1970495 := bstep (se 1 (by rfl) ⟨1477871, by rfl⟩ : syracuseStep 1970495 = 2955743) B2955743
theorem B14782823 : Blo 1311974 14782823 := bstep (se 1 (by rfl) ⟨11087117, by rfl⟩ : syracuseStep 14782823 = 22174235) B22174235
theorem B1970591 : Blo 1311974 1970591 := bstep (se 1 (by rfl) ⟨1477943, by rfl⟩ : syracuseStep 1970591 = 2955887) B2955887
theorem B1970663 : Blo 1311974 1970663 := bstep (se 1 (by rfl) ⟨1477997, by rfl⟩ : syracuseStep 1970663 = 2955995) B2955995
theorem B2953961 : Blo 1311974 2953961 := bstep (se 2 (by rfl) ⟨1107735, by rfl⟩ : syracuseStep 2953961 = 2215471) B2215471
theorem B2217199 : Blo 1311974 2217199 := bstep (se 1 (by rfl) ⟨1662899, by rfl⟩ : syracuseStep 2217199 = 3325799) B3325799
theorem B11212991 : Blo 1311974 11212991 := bstep (se 1 (by rfl) ⟨8409743, by rfl⟩ : syracuseStep 11212991 = 16819487) B16819487
theorem B3152299 : Blo 1311974 3152299 := bstep (se 1 (by rfl) ⟨2364224, by rfl⟩ : syracuseStep 3152299 = 4728449) B4728449
theorem B20217563 : Blo 1311974 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B3153991 : Blo 1311974 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B9855215 : Blo 1311974 9855215 := bstep (se 1 (by rfl) ⟨7391411, by rfl⟩ : syracuseStep 9855215 = 14782823) B14782823
theorem B4203065 : Blo 1311974 4203065 := bstep (se 2 (by rfl) ⟨1576149, by rfl⟩ : syracuseStep 4203065 = 3152299) B3152299
theorem B2491631 : Blo 1311974 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B737510939 : Blo 1311974 737510939 := bstep (se 1 (by rfl) ⟨553133204, by rfl⟩ : syracuseStep 737510939 = 1106266409) B1106266409
theorem B47941793 : Blo 1311974 47941793 := bstep (se 2 (by rfl) ⟨17978172, by rfl⟩ : syracuseStep 47941793 = 35956345) B35956345
theorem B9963485 : Blo 1311974 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B16812359 : Blo 1311974 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B1968455 : Blo 1311974 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B1313095 : Blo 1311974 1313095 := bstep (se 1 (by rfl) ⟨984821, by rfl⟩ : syracuseStep 1313095 = 1969643) B1969643
theorem B26970479 : Blo 1311974 26970479 := bstep (se 1 (by rfl) ⟨20227859, by rfl⟩ : syracuseStep 26970479 = 40455719) B40455719
theorem B1313255 : Blo 1311974 1313255 := bstep (se 1 (by rfl) ⟨984941, by rfl⟩ : syracuseStep 1313255 = 1969883) B1969883
theorem B13478375 : Blo 1311974 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B1968731 : Blo 1311974 1968731 := bstep (se 1 (by rfl) ⟨1476548, by rfl⟩ : syracuseStep 1968731 = 2953097) B2953097
theorem B1313471 : Blo 1311974 1313471 := bstep (se 1 (by rfl) ⟨985103, by rfl⟩ : syracuseStep 1313471 = 1970207) B1970207
theorem B3197647 : Blo 1311974 3197647 := bstep (se 1 (by rfl) ⟨2398235, by rfl⟩ : syracuseStep 3197647 = 4796471) B4796471
theorem B109193953 : Blo 1311974 109193953 := bstep (se 2 (by rfl) ⟨40947732, by rfl⟩ : syracuseStep 109193953 = 81895465) B81895465
theorem B1968875 : Blo 1311974 1968875 := bstep (se 1 (by rfl) ⟨1476656, by rfl⟩ : syracuseStep 1968875 = 2953313) B2953313
theorem B1313563 : Blo 1311974 1313563 := bstep (se 1 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 1313563 = 1970345) B1970345
theorem B1313663 : Blo 1311974 1313663 := bstep (se 1 (by rfl) ⟨985247, by rfl⟩ : syracuseStep 1313663 = 1970495) B1970495
theorem B1313727 : Blo 1311974 1313727 := bstep (se 1 (by rfl) ⟨985295, by rfl⟩ : syracuseStep 1313727 = 1970591) B1970591
theorem B1313775 : Blo 1311974 1313775 := bstep (se 1 (by rfl) ⟨985331, by rfl⟩ : syracuseStep 1313775 = 1970663) B1970663
theorem B1969307 : Blo 1311974 1969307 := bstep (se 1 (by rfl) ⟨1476980, by rfl⟩ : syracuseStep 1969307 = 2953961) B2953961
theorem B21294751 : Blo 1311974 21294751 := bstep (se 1 (by rfl) ⟨15971063, by rfl⟩ : syracuseStep 21294751 = 31942127) B31942127
theorem B14945957 : Blo 1311974 14945957 := bstep (se 4 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 14945957 = 2802367) B2802367
theorem B7475327 : Blo 1311974 7475327 := bstep (se 1 (by rfl) ⟨5606495, by rfl⟩ : syracuseStep 7475327 = 11212991) B11212991
theorem B12628183 : Blo 1311974 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B6304711 : Blo 1311974 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B5609519 : Blo 1311974 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B8411795 : Blo 1311974 8411795 := bstep (se 1 (by rfl) ⟨6308846, by rfl⟩ : syracuseStep 8411795 = 12617693) B12617693
theorem B11213639 : Blo 1311974 11213639 := bstep (se 1 (by rfl) ⟨8410229, by rfl⟩ : syracuseStep 11213639 = 16820459) B16820459
theorem B2956265 : Blo 1311974 2956265 := bstep (se 2 (by rfl) ⟨1108599, by rfl⟩ : syracuseStep 2956265 = 2217199) B2217199
theorem B6643133 : Blo 1311974 6643133 := bstep (se 3 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 6643133 = 2491175) B2491175
theorem B6570143 : Blo 1311974 6570143 := bstep (se 1 (by rfl) ⟨4927607, by rfl⟩ : syracuseStep 6570143 = 9855215) B9855215
theorem B2802043 : Blo 1311974 2802043 := bstep (se 1 (by rfl) ⟨2101532, by rfl⟩ : syracuseStep 2802043 = 4203065) B4203065
theorem B8406281 : Blo 1311974 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B11208239 : Blo 1311974 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B1312303 : Blo 1311974 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B1312487 : Blo 1311974 1312487 := bstep (se 1 (by rfl) ⟨984365, by rfl⟩ : syracuseStep 1312487 = 1968731) B1968731
theorem B1312583 : Blo 1311974 1312583 := bstep (se 1 (by rfl) ⟨984437, by rfl⟩ : syracuseStep 1312583 = 1968875) B1968875
theorem B1312871 : Blo 1311974 1312871 := bstep (se 1 (by rfl) ⟨984653, by rfl⟩ : syracuseStep 1312871 = 1969307) B1969307
theorem B9963971 : Blo 1311974 9963971 := bstep (se 1 (by rfl) ⟨7472978, by rfl⟩ : syracuseStep 9963971 = 14945957) B14945957
theorem B4983551 : Blo 1311974 4983551 := bstep (se 1 (by rfl) ⟨3737663, by rfl⟩ : syracuseStep 4983551 = 7475327) B7475327
theorem B4205321 : Blo 1311974 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B16837577 : Blo 1311974 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B4263529 : Blo 1311974 4263529 := bstep (se 2 (by rfl) ⟨1598823, by rfl⟩ : syracuseStep 4263529 = 3197647) B3197647
theorem B145591937 : Blo 1311974 145591937 := bstep (se 2 (by rfl) ⟨54596976, by rfl⟩ : syracuseStep 145591937 = 109193953) B109193953
theorem B3739679 : Blo 1311974 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B31961195 : Blo 1311974 31961195 := bstep (se 1 (by rfl) ⟨23970896, by rfl⟩ : syracuseStep 31961195 = 47941793) B47941793
theorem B5607863 : Blo 1311974 5607863 := bstep (se 1 (by rfl) ⟨4205897, by rfl⟩ : syracuseStep 5607863 = 8411795) B8411795
theorem B7475759 : Blo 1311974 7475759 := bstep (se 1 (by rfl) ⟨5606819, by rfl⟩ : syracuseStep 7475759 = 11213639) B11213639
theorem B1970843 : Blo 1311974 1970843 := bstep (se 1 (by rfl) ⟨1478132, by rfl⟩ : syracuseStep 1970843 = 2956265) B2956265
theorem B4428755 : Blo 1311974 4428755 := bstep (se 1 (by rfl) ⟨3321566, by rfl⟩ : syracuseStep 4428755 = 6643133) B6643133
theorem B1661087 : Blo 1311974 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B491673959 : Blo 1311974 491673959 := bstep (se 1 (by rfl) ⟨368755469, by rfl⟩ : syracuseStep 491673959 = 737510939) B737510939
theorem B6642323 : Blo 1311974 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B17980319 : Blo 1311974 17980319 := bstep (se 1 (by rfl) ⟨13485239, by rfl⟩ : syracuseStep 17980319 = 26970479) B26970479
theorem B8985583 : Blo 1311974 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B28393001 : Blo 1311974 28393001 := bstep (se 2 (by rfl) ⟨10647375, by rfl⟩ : syracuseStep 28393001 = 21294751) B21294751
theorem B21307463 : Blo 1311974 21307463 := bstep (se 1 (by rfl) ⟨15980597, by rfl⟩ : syracuseStep 21307463 = 31961195) B31961195
theorem B11225051 : Blo 1311974 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B3736057 : Blo 1311974 3736057 := bstep (se 2 (by rfl) ⟨1401021, by rfl⟩ : syracuseStep 3736057 = 2802043) B2802043
theorem B7472159 : Blo 1311974 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B2803547 : Blo 1311974 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B11986879 : Blo 1311974 11986879 := bstep (se 1 (by rfl) ⟨8990159, by rfl⟩ : syracuseStep 11986879 = 17980319) B17980319
theorem B97061291 : Blo 1311974 97061291 := bstep (se 1 (by rfl) ⟨72795968, by rfl⟩ : syracuseStep 97061291 = 145591937) B145591937
theorem B2493119 : Blo 1311974 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B3738575 : Blo 1311974 3738575 := bstep (se 1 (by rfl) ⟨2803931, by rfl⟩ : syracuseStep 3738575 = 5607863) B5607863
theorem B4983839 : Blo 1311974 4983839 := bstep (se 1 (by rfl) ⟨3737879, by rfl⟩ : syracuseStep 4983839 = 7475759) B7475759
theorem B1313895 : Blo 1311974 1313895 := bstep (se 1 (by rfl) ⟨985421, by rfl⟩ : syracuseStep 1313895 = 1970843) B1970843
theorem B2952503 : Blo 1311974 2952503 := bstep (se 1 (by rfl) ⟨2214377, by rfl⟩ : syracuseStep 2952503 = 4428755) B4428755
theorem B22416749 : Blo 1311974 22416749 := bstep (se 3 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 22416749 = 8406281) B8406281
theorem B327782639 : Blo 1311974 327782639 := bstep (se 1 (by rfl) ⟨245836979, by rfl⟩ : syracuseStep 327782639 = 491673959) B491673959
theorem B4428215 : Blo 1311974 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B3322367 : Blo 1311974 3322367 := bstep (se 1 (by rfl) ⟨2491775, by rfl⟩ : syracuseStep 3322367 = 4983551) B4983551
theorem B18928667 : Blo 1311974 18928667 := bstep (se 1 (by rfl) ⟨14196500, by rfl⟩ : syracuseStep 18928667 = 28393001) B28393001
theorem B4380095 : Blo 1311974 4380095 := bstep (se 1 (by rfl) ⟨3285071, by rfl⟩ : syracuseStep 4380095 = 6570143) B6570143
theorem B4429565 : Blo 1311974 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B6642647 : Blo 1311974 6642647 := bstep (se 1 (by rfl) ⟨4981985, by rfl⟩ : syracuseStep 6642647 = 9963971) B9963971
theorem B5684705 : Blo 1311974 5684705 := bstep (se 2 (by rfl) ⟨2131764, by rfl⟩ : syracuseStep 5684705 = 4263529) B4263529
theorem B47923109 : Blo 1311974 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B14204975 : Blo 1311974 14204975 := bstep (se 1 (by rfl) ⟨10653731, by rfl⟩ : syracuseStep 14204975 = 21307463) B21307463
theorem B218521759 : Blo 1311974 218521759 := bstep (se 1 (by rfl) ⟨163891319, by rfl⟩ : syracuseStep 218521759 = 327782639) B327782639
theorem B4981409 : Blo 1311974 4981409 := bstep (se 2 (by rfl) ⟨1868028, by rfl⟩ : syracuseStep 4981409 = 3736057) B3736057
theorem B4981439 : Blo 1311974 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B1869031 : Blo 1311974 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B2492383 : Blo 1311974 2492383 := bstep (se 1 (by rfl) ⟨1869287, by rfl⟩ : syracuseStep 2492383 = 3738575) B3738575
theorem B1968335 : Blo 1311974 1968335 := bstep (se 1 (by rfl) ⟨1476251, by rfl⟩ : syracuseStep 1968335 = 2952503) B2952503
theorem B14944499 : Blo 1311974 14944499 := bstep (se 1 (by rfl) ⟨11208374, by rfl⟩ : syracuseStep 14944499 = 22416749) B22416749
theorem B2952143 : Blo 1311974 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B2214911 : Blo 1311974 2214911 := bstep (se 1 (by rfl) ⟨1661183, by rfl⟩ : syracuseStep 2214911 = 3322367) B3322367
theorem B12619111 : Blo 1311974 12619111 := bstep (se 1 (by rfl) ⟨9464333, by rfl⟩ : syracuseStep 12619111 = 18928667) B18928667
theorem B2953043 : Blo 1311974 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B7483367 : Blo 1311974 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B6648317 : Blo 1311974 6648317 := bstep (se 3 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 6648317 = 2493119) B2493119
theorem B4428431 : Blo 1311974 4428431 := bstep (se 1 (by rfl) ⟨3321323, by rfl⟩ : syracuseStep 4428431 = 6642647) B6642647
theorem B3322559 : Blo 1311974 3322559 := bstep (se 1 (by rfl) ⟨2491919, by rfl⟩ : syracuseStep 3322559 = 4983839) B4983839
theorem B3789803 : Blo 1311974 3789803 := bstep (se 1 (by rfl) ⟨2842352, by rfl⟩ : syracuseStep 3789803 = 5684705) B5684705
theorem B11680253 : Blo 1311974 11680253 := bstep (se 3 (by rfl) ⟨2190047, by rfl⟩ : syracuseStep 11680253 = 4380095) B4380095
theorem B64707527 : Blo 1311974 64707527 := bstep (se 1 (by rfl) ⟨48530645, by rfl⟩ : syracuseStep 64707527 = 97061291) B97061291
theorem B15982505 : Blo 1311974 15982505 := bstep (se 2 (by rfl) ⟨5993439, by rfl⟩ : syracuseStep 15982505 = 11986879) B11986879
theorem B31948739 : Blo 1311974 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B37879933 : Blo 1311974 37879933 := bstep (se 3 (by rfl) ⟨7102487, by rfl⟩ : syracuseStep 37879933 = 14204975) B14204975
theorem B4432211 : Blo 1311974 4432211 := bstep (se 1 (by rfl) ⟨3324158, by rfl⟩ : syracuseStep 4432211 = 6648317) B6648317
theorem B1312223 : Blo 1311974 1312223 := bstep (se 1 (by rfl) ⟨984167, by rfl⟩ : syracuseStep 1312223 = 1968335) B1968335
theorem B9962999 : Blo 1311974 9962999 := bstep (se 1 (by rfl) ⟨7472249, by rfl⟩ : syracuseStep 9962999 = 14944499) B14944499
theorem B2492041 : Blo 1311974 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B1968095 : Blo 1311974 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B1476607 : Blo 1311974 1476607 := bstep (se 1 (by rfl) ⟨1107455, by rfl⟩ : syracuseStep 1476607 = 2214911) B2214911
theorem B1968695 : Blo 1311974 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B2952287 : Blo 1311974 2952287 := bstep (se 1 (by rfl) ⟨2214215, by rfl⟩ : syracuseStep 2952287 = 4428431) B4428431
theorem B3320939 : Blo 1311974 3320939 := bstep (se 1 (by rfl) ⟨2490704, by rfl⟩ : syracuseStep 3320939 = 4981409) B4981409
theorem B3320959 : Blo 1311974 3320959 := bstep (se 1 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 3320959 = 4981439) B4981439
theorem B2215039 : Blo 1311974 2215039 := bstep (se 1 (by rfl) ⟨1661279, by rfl⟩ : syracuseStep 2215039 = 3322559) B3322559
theorem B2526535 : Blo 1311974 2526535 := bstep (se 1 (by rfl) ⟨1894901, by rfl⟩ : syracuseStep 2526535 = 3789803) B3789803
theorem B498357461 : Blo 1311974 498357461 := bstep (se 7 (by rfl) ⟨5840126, by rfl⟩ : syracuseStep 498357461 = 11680253) B11680253
theorem B10655003 : Blo 1311974 10655003 := bstep (se 1 (by rfl) ⟨7991252, by rfl⟩ : syracuseStep 10655003 = 15982505) B15982505
theorem B3323177 : Blo 1311974 3323177 := bstep (se 2 (by rfl) ⟨1246191, by rfl⟩ : syracuseStep 3323177 = 2492383) B2492383
theorem B291362345 : Blo 1311974 291362345 := bstep (se 2 (by rfl) ⟨109260879, by rfl⟩ : syracuseStep 291362345 = 218521759) B218521759
theorem B16825481 : Blo 1311974 16825481 := bstep (se 2 (by rfl) ⟨6309555, by rfl⟩ : syracuseStep 16825481 = 12619111) B12619111
theorem B43138351 : Blo 1311974 43138351 := bstep (se 1 (by rfl) ⟨32353763, by rfl⟩ : syracuseStep 43138351 = 64707527) B64707527
theorem B21299159 : Blo 1311974 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B4988911 : Blo 1311974 4988911 := bstep (se 1 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 4988911 = 7483367) B7483367
theorem B7103335 : Blo 1311974 7103335 := bstep (se 1 (by rfl) ⟨5327501, by rfl⟩ : syracuseStep 7103335 = 10655003) B10655003
theorem B194241563 : Blo 1311974 194241563 := bstep (se 1 (by rfl) ⟨145681172, by rfl⟩ : syracuseStep 194241563 = 291362345) B291362345
theorem B1312063 : Blo 1311974 1312063 := bstep (se 1 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 1312063 = 1968095) B1968095
theorem B1312463 : Blo 1311974 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B3368713 : Blo 1311974 3368713 := bstep (se 2 (by rfl) ⟨1263267, by rfl⟩ : syracuseStep 3368713 = 2526535) B2526535
theorem B1968191 : Blo 1311974 1968191 := bstep (se 1 (by rfl) ⟨1476143, by rfl⟩ : syracuseStep 1968191 = 2952287) B2952287
theorem B2213959 : Blo 1311974 2213959 := bstep (se 1 (by rfl) ⟨1660469, by rfl⟩ : syracuseStep 2213959 = 3320939) B3320939
theorem B11216987 : Blo 1311974 11216987 := bstep (se 1 (by rfl) ⟨8412740, by rfl⟩ : syracuseStep 11216987 = 16825481) B16825481
theorem B56797757 : Blo 1311974 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B1968809 : Blo 1311974 1968809 := bstep (se 2 (by rfl) ⟨738303, by rfl⟩ : syracuseStep 1968809 = 1476607) B1476607
theorem B50506577 : Blo 1311974 50506577 := bstep (se 2 (by rfl) ⟨18939966, by rfl⟩ : syracuseStep 50506577 = 37879933) B37879933
theorem B332238307 : Blo 1311974 332238307 := bstep (se 1 (by rfl) ⟨249178730, by rfl⟩ : syracuseStep 332238307 = 498357461) B498357461
theorem B2215451 : Blo 1311974 2215451 := bstep (se 1 (by rfl) ⟨1661588, by rfl⟩ : syracuseStep 2215451 = 3323177) B3323177
theorem B4427945 : Blo 1311974 4427945 := bstep (se 2 (by rfl) ⟨1660479, by rfl⟩ : syracuseStep 4427945 = 3320959) B3320959
theorem B2953385 : Blo 1311974 2953385 := bstep (se 2 (by rfl) ⟨1107519, by rfl⟩ : syracuseStep 2953385 = 2215039) B2215039
theorem B3322721 : Blo 1311974 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2954807 : Blo 1311974 2954807 := bstep (se 1 (by rfl) ⟨2216105, by rfl⟩ : syracuseStep 2954807 = 4432211) B4432211
theorem B6641999 : Blo 1311974 6641999 := bstep (se 1 (by rfl) ⟨4981499, by rfl⟩ : syracuseStep 6641999 = 9962999) B9962999
theorem B230071205 : Blo 1311974 230071205 := bstep (se 4 (by rfl) ⟨21569175, by rfl⟩ : syracuseStep 230071205 = 43138351) B43138351
theorem B6651881 : Blo 1311974 6651881 := bstep (se 2 (by rfl) ⟨2494455, by rfl⟩ : syracuseStep 6651881 = 4988911) B4988911
theorem B9471113 : Blo 1311974 9471113 := bstep (se 2 (by rfl) ⟨3551667, by rfl⟩ : syracuseStep 9471113 = 7103335) B7103335
theorem B1312127 : Blo 1311974 1312127 := bstep (se 1 (by rfl) ⟨984095, by rfl⟩ : syracuseStep 1312127 = 1968191) B1968191
theorem B37865171 : Blo 1311974 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B1312539 : Blo 1311974 1312539 := bstep (se 1 (by rfl) ⟨984404, by rfl⟩ : syracuseStep 1312539 = 1968809) B1968809
theorem B33671051 : Blo 1311974 33671051 := bstep (se 1 (by rfl) ⟨25253288, by rfl⟩ : syracuseStep 33671051 = 50506577) B50506577
theorem B153380803 : Blo 1311974 153380803 := bstep (se 1 (by rfl) ⟨115035602, by rfl⟩ : syracuseStep 153380803 = 230071205) B230071205
theorem B442984409 : Blo 1311974 442984409 := bstep (se 2 (by rfl) ⟨166119153, by rfl⟩ : syracuseStep 442984409 = 332238307) B332238307
theorem B4491617 : Blo 1311974 4491617 := bstep (se 2 (by rfl) ⟨1684356, by rfl⟩ : syracuseStep 4491617 = 3368713) B3368713
theorem B1476967 : Blo 1311974 1476967 := bstep (se 1 (by rfl) ⟨1107725, by rfl⟩ : syracuseStep 1476967 = 2215451) B2215451
theorem B4434587 : Blo 1311974 4434587 := bstep (se 1 (by rfl) ⟨3325940, by rfl⟩ : syracuseStep 4434587 = 6651881) B6651881
theorem B2951945 : Blo 1311974 2951945 := bstep (se 2 (by rfl) ⟨1106979, by rfl⟩ : syracuseStep 2951945 = 2213959) B2213959
theorem B2951963 : Blo 1311974 2951963 := bstep (se 1 (by rfl) ⟨2213972, by rfl⟩ : syracuseStep 2951963 = 4427945) B4427945
theorem B1968923 : Blo 1311974 1968923 := bstep (se 1 (by rfl) ⟨1476692, by rfl⟩ : syracuseStep 1968923 = 2953385) B2953385
theorem B2215147 : Blo 1311974 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B129494375 : Blo 1311974 129494375 := bstep (se 1 (by rfl) ⟨97120781, by rfl⟩ : syracuseStep 129494375 = 194241563) B194241563
theorem B1969871 : Blo 1311974 1969871 := bstep (se 1 (by rfl) ⟨1477403, by rfl⟩ : syracuseStep 1969871 = 2954807) B2954807
theorem B4427999 : Blo 1311974 4427999 := bstep (se 1 (by rfl) ⟨3320999, by rfl⟩ : syracuseStep 4427999 = 6641999) B6641999
theorem B7477991 : Blo 1311974 7477991 := bstep (se 1 (by rfl) ⟨5608493, by rfl⟩ : syracuseStep 7477991 = 11216987) B11216987
theorem B11977645 : Blo 1311974 11977645 := bstep (se 3 (by rfl) ⟨2245808, by rfl⟩ : syracuseStep 11977645 = 4491617) B4491617
theorem B22447367 : Blo 1311974 22447367 := bstep (se 1 (by rfl) ⟨16835525, by rfl⟩ : syracuseStep 22447367 = 33671051) B33671051
theorem B295322939 : Blo 1311974 295322939 := bstep (se 1 (by rfl) ⟨221492204, by rfl⟩ : syracuseStep 295322939 = 442984409) B442984409
theorem B1967963 : Blo 1311974 1967963 := bstep (se 1 (by rfl) ⟨1475972, by rfl⟩ : syracuseStep 1967963 = 2951945) B2951945
theorem B1967975 : Blo 1311974 1967975 := bstep (se 1 (by rfl) ⟨1475981, by rfl⟩ : syracuseStep 1967975 = 2951963) B2951963
theorem B1312615 : Blo 1311974 1312615 := bstep (se 1 (by rfl) ⟨984461, by rfl⟩ : syracuseStep 1312615 = 1968923) B1968923
theorem B86329583 : Blo 1311974 86329583 := bstep (se 1 (by rfl) ⟨64747187, by rfl⟩ : syracuseStep 86329583 = 129494375) B129494375
theorem B1313247 : Blo 1311974 1313247 := bstep (se 1 (by rfl) ⟨984935, by rfl⟩ : syracuseStep 1313247 = 1969871) B1969871
theorem B204507737 : Blo 1311974 204507737 := bstep (se 2 (by rfl) ⟨76690401, by rfl⟩ : syracuseStep 204507737 = 153380803) B153380803
theorem B2951999 : Blo 1311974 2951999 := bstep (se 1 (by rfl) ⟨2213999, by rfl⟩ : syracuseStep 2951999 = 4427999) B4427999
theorem B1969289 : Blo 1311974 1969289 := bstep (se 2 (by rfl) ⟨738483, by rfl⟩ : syracuseStep 1969289 = 1476967) B1476967
theorem B25243447 : Blo 1311974 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B2953529 : Blo 1311974 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B4985327 : Blo 1311974 4985327 := bstep (se 1 (by rfl) ⟨3738995, by rfl⟩ : syracuseStep 4985327 = 7477991) B7477991
theorem B6314075 : Blo 1311974 6314075 := bstep (se 1 (by rfl) ⟨4735556, by rfl⟩ : syracuseStep 6314075 = 9471113) B9471113
theorem B2956391 : Blo 1311974 2956391 := bstep (se 1 (by rfl) ⟨2217293, by rfl⟩ : syracuseStep 2956391 = 4434587) B4434587
theorem B1311975 : Blo 1311974 1311975 := bstep (se 1 (by rfl) ⟨983981, by rfl⟩ : syracuseStep 1311975 = 1967963) B1967963
theorem B1311983 : Blo 1311974 1311983 := bstep (se 1 (by rfl) ⟨983987, by rfl⟩ : syracuseStep 1311983 = 1967975) B1967975
theorem B1967999 : Blo 1311974 1967999 := bstep (se 1 (by rfl) ⟨1475999, by rfl⟩ : syracuseStep 1967999 = 2951999) B2951999
theorem B1312859 : Blo 1311974 1312859 := bstep (se 1 (by rfl) ⟨984644, by rfl⟩ : syracuseStep 1312859 = 1969289) B1969289
theorem B1969019 : Blo 1311974 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B196881959 : Blo 1311974 196881959 := bstep (se 1 (by rfl) ⟨147661469, by rfl⟩ : syracuseStep 196881959 = 295322939) B295322939
theorem B15970193 : Blo 1311974 15970193 := bstep (se 2 (by rfl) ⟨5988822, by rfl⟩ : syracuseStep 15970193 = 11977645) B11977645
theorem B57553055 : Blo 1311974 57553055 := bstep (se 1 (by rfl) ⟨43164791, by rfl⟩ : syracuseStep 57553055 = 86329583) B86329583
theorem B1970927 : Blo 1311974 1970927 := bstep (se 1 (by rfl) ⟨1478195, by rfl⟩ : syracuseStep 1970927 = 2956391) B2956391
theorem B33657929 : Blo 1311974 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B3323551 : Blo 1311974 3323551 := bstep (se 1 (by rfl) ⟨2492663, by rfl⟩ : syracuseStep 3323551 = 4985327) B4985327
theorem B14964911 : Blo 1311974 14964911 := bstep (se 1 (by rfl) ⟨11223683, by rfl⟩ : syracuseStep 14964911 = 22447367) B22447367
theorem B4209383 : Blo 1311974 4209383 := bstep (se 1 (by rfl) ⟨3157037, by rfl⟩ : syracuseStep 4209383 = 6314075) B6314075
theorem B136338491 : Blo 1311974 136338491 := bstep (se 1 (by rfl) ⟨102253868, by rfl⟩ : syracuseStep 136338491 = 204507737) B204507737
theorem B363569309 : Blo 1311974 363569309 := bstep (se 3 (by rfl) ⟨68169245, by rfl⟩ : syracuseStep 363569309 = 136338491) B136338491
theorem B22438619 : Blo 1311974 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B1311999 : Blo 1311974 1311999 := bstep (se 1 (by rfl) ⟨983999, by rfl⟩ : syracuseStep 1311999 = 1967999) B1967999
theorem B525018557 : Blo 1311974 525018557 := bstep (se 3 (by rfl) ⟨98440979, by rfl⟩ : syracuseStep 525018557 = 196881959) B196881959
theorem B1312679 : Blo 1311974 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B1313951 : Blo 1311974 1313951 := bstep (se 1 (by rfl) ⟨985463, by rfl⟩ : syracuseStep 1313951 = 1970927) B1970927
theorem B2806255 : Blo 1311974 2806255 := bstep (se 1 (by rfl) ⟨2104691, by rfl⟩ : syracuseStep 2806255 = 4209383) B4209383
theorem B10646795 : Blo 1311974 10646795 := bstep (se 1 (by rfl) ⟨7985096, by rfl⟩ : syracuseStep 10646795 = 15970193) B15970193
theorem B38368703 : Blo 1311974 38368703 := bstep (se 1 (by rfl) ⟨28776527, by rfl⟩ : syracuseStep 38368703 = 57553055) B57553055
theorem B9976607 : Blo 1311974 9976607 := bstep (se 1 (by rfl) ⟨7482455, by rfl⟩ : syracuseStep 9976607 = 14964911) B14964911
theorem B4431401 : Blo 1311974 4431401 := bstep (se 2 (by rfl) ⟨1661775, by rfl⟩ : syracuseStep 4431401 = 3323551) B3323551
theorem B14959079 : Blo 1311974 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B242379539 : Blo 1311974 242379539 := bstep (se 1 (by rfl) ⟨181784654, by rfl⟩ : syracuseStep 242379539 = 363569309) B363569309
theorem B7097863 : Blo 1311974 7097863 := bstep (se 1 (by rfl) ⟨5323397, by rfl⟩ : syracuseStep 7097863 = 10646795) B10646795
theorem B25579135 : Blo 1311974 25579135 := bstep (se 1 (by rfl) ⟨19184351, by rfl⟩ : syracuseStep 25579135 = 38368703) B38368703
theorem B1400049485 : Blo 1311974 1400049485 := bstep (se 3 (by rfl) ⟨262509278, by rfl⟩ : syracuseStep 1400049485 = 525018557) B525018557
theorem B2954267 : Blo 1311974 2954267 := bstep (se 1 (by rfl) ⟨2215700, by rfl⟩ : syracuseStep 2954267 = 4431401) B4431401
theorem B3741673 : Blo 1311974 3741673 := bstep (se 2 (by rfl) ⟨1403127, by rfl⟩ : syracuseStep 3741673 = 2806255) B2806255
theorem B6651071 : Blo 1311974 6651071 := bstep (se 1 (by rfl) ⟨4988303, by rfl⟩ : syracuseStep 6651071 = 9976607) B9976607
theorem B136422053 : Blo 1311974 136422053 := bstep (se 4 (by rfl) ⟨12789567, by rfl⟩ : syracuseStep 136422053 = 25579135) B25579135
theorem B9463817 : Blo 1311974 9463817 := bstep (se 2 (by rfl) ⟨3548931, by rfl⟩ : syracuseStep 9463817 = 7097863) B7097863
theorem B4434047 : Blo 1311974 4434047 := bstep (se 1 (by rfl) ⟨3325535, by rfl⟩ : syracuseStep 4434047 = 6651071) B6651071
theorem B933366323 : Blo 1311974 933366323 := bstep (se 1 (by rfl) ⟨700024742, by rfl⟩ : syracuseStep 933366323 = 1400049485) B1400049485
theorem B9972719 : Blo 1311974 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B1969511 : Blo 1311974 1969511 := bstep (se 1 (by rfl) ⟨1477133, by rfl⟩ : syracuseStep 1969511 = 2954267) B2954267
theorem B161586359 : Blo 1311974 161586359 := bstep (se 1 (by rfl) ⟨121189769, by rfl⟩ : syracuseStep 161586359 = 242379539) B242379539
theorem B4988897 : Blo 1311974 4988897 := bstep (se 2 (by rfl) ⟨1870836, by rfl⟩ : syracuseStep 4988897 = 3741673) B3741673
theorem B90948035 : Blo 1311974 90948035 := bstep (se 1 (by rfl) ⟨68211026, by rfl⟩ : syracuseStep 90948035 = 136422053) B136422053
theorem B6309211 : Blo 1311974 6309211 := bstep (se 1 (by rfl) ⟨4731908, by rfl⟩ : syracuseStep 6309211 = 9463817) B9463817
theorem B1313007 : Blo 1311974 1313007 := bstep (se 1 (by rfl) ⟨984755, by rfl⟩ : syracuseStep 1313007 = 1969511) B1969511
theorem B622244215 : Blo 1311974 622244215 := bstep (se 1 (by rfl) ⟨466683161, by rfl⟩ : syracuseStep 622244215 = 933366323) B933366323
theorem B6648479 : Blo 1311974 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B2956031 : Blo 1311974 2956031 := bstep (se 1 (by rfl) ⟨2217023, by rfl⟩ : syracuseStep 2956031 = 4434047) B4434047
theorem B107724239 : Blo 1311974 107724239 := bstep (se 1 (by rfl) ⟨80793179, by rfl⟩ : syracuseStep 107724239 = 161586359) B161586359
theorem B3325931 : Blo 1311974 3325931 := bstep (se 1 (by rfl) ⟨2494448, by rfl⟩ : syracuseStep 3325931 = 4988897) B4988897
theorem B4432319 : Blo 1311974 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B60632023 : Blo 1311974 60632023 := bstep (se 1 (by rfl) ⟨45474017, by rfl⟩ : syracuseStep 60632023 = 90948035) B90948035
theorem B1970687 : Blo 1311974 1970687 := bstep (se 1 (by rfl) ⟨1478015, by rfl⟩ : syracuseStep 1970687 = 2956031) B2956031
theorem B71816159 : Blo 1311974 71816159 := bstep (se 1 (by rfl) ⟨53862119, by rfl⟩ : syracuseStep 71816159 = 107724239) B107724239
theorem B2217287 : Blo 1311974 2217287 := bstep (se 1 (by rfl) ⟨1662965, by rfl⟩ : syracuseStep 2217287 = 3325931) B3325931
theorem B829658953 : Blo 1311974 829658953 := bstep (se 2 (by rfl) ⟨311122107, by rfl⟩ : syracuseStep 829658953 = 622244215) B622244215
theorem B8412281 : Blo 1311974 8412281 := bstep (se 2 (by rfl) ⟨3154605, by rfl⟩ : syracuseStep 8412281 = 6309211) B6309211
theorem B1313791 : Blo 1311974 1313791 := bstep (se 1 (by rfl) ⟨985343, by rfl⟩ : syracuseStep 1313791 = 1970687) B1970687
theorem B47877439 : Blo 1311974 47877439 := bstep (se 1 (by rfl) ⟨35908079, by rfl⟩ : syracuseStep 47877439 = 71816159) B71816159
theorem B1478191 : Blo 1311974 1478191 := bstep (se 1 (by rfl) ⟨1108643, by rfl⟩ : syracuseStep 1478191 = 2217287) B2217287
theorem B80842697 : Blo 1311974 80842697 := bstep (se 2 (by rfl) ⟨30316011, by rfl⟩ : syracuseStep 80842697 = 60632023) B60632023
theorem B5608187 : Blo 1311974 5608187 := bstep (se 1 (by rfl) ⟨4206140, by rfl⟩ : syracuseStep 5608187 = 8412281) B8412281
theorem B1106211937 : Blo 1311974 1106211937 := bstep (se 2 (by rfl) ⟨414829476, by rfl⟩ : syracuseStep 1106211937 = 829658953) B829658953
theorem B2954879 : Blo 1311974 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B3738791 : Blo 1311974 3738791 := bstep (se 1 (by rfl) ⟨2804093, by rfl⟩ : syracuseStep 3738791 = 5608187) B5608187
theorem B1969919 : Blo 1311974 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B1474949249 : Blo 1311974 1474949249 := bstep (se 2 (by rfl) ⟨553105968, by rfl⟩ : syracuseStep 1474949249 = 1106211937) B1106211937
theorem B63836585 : Blo 1311974 63836585 := bstep (se 2 (by rfl) ⟨23938719, by rfl⟩ : syracuseStep 63836585 = 47877439) B47877439
theorem B1970921 : Blo 1311974 1970921 := bstep (se 2 (by rfl) ⟨739095, by rfl⟩ : syracuseStep 1970921 = 1478191) B1478191
theorem B53895131 : Blo 1311974 53895131 := bstep (se 1 (by rfl) ⟨40421348, by rfl⟩ : syracuseStep 53895131 = 80842697) B80842697
theorem B42557723 : Blo 1311974 42557723 := bstep (se 1 (by rfl) ⟨31918292, by rfl⟩ : syracuseStep 42557723 = 63836585) B63836585
theorem B2492527 : Blo 1311974 2492527 := bstep (se 1 (by rfl) ⟨1869395, by rfl⟩ : syracuseStep 2492527 = 3738791) B3738791
theorem B1313279 : Blo 1311974 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B1313947 : Blo 1311974 1313947 := bstep (se 1 (by rfl) ⟨985460, by rfl⟩ : syracuseStep 1313947 = 1970921) B1970921
theorem B983299499 : Blo 1311974 983299499 := bstep (se 1 (by rfl) ⟨737474624, by rfl⟩ : syracuseStep 983299499 = 1474949249) B1474949249
theorem B35930087 : Blo 1311974 35930087 := bstep (se 1 (by rfl) ⟨26947565, by rfl⟩ : syracuseStep 35930087 = 53895131) B53895131
theorem B655532999 : Blo 1311974 655532999 := bstep (se 1 (by rfl) ⟨491649749, by rfl⟩ : syracuseStep 655532999 = 983299499) B983299499
theorem B28371815 : Blo 1311974 28371815 := bstep (se 1 (by rfl) ⟨21278861, by rfl⟩ : syracuseStep 28371815 = 42557723) B42557723
theorem B3323369 : Blo 1311974 3323369 := bstep (se 2 (by rfl) ⟨1246263, by rfl⟩ : syracuseStep 3323369 = 2492527) B2492527
theorem B23953391 : Blo 1311974 23953391 := bstep (se 1 (by rfl) ⟨17965043, by rfl⟩ : syracuseStep 23953391 = 35930087) B35930087
theorem B15968927 : Blo 1311974 15968927 := bstep (se 1 (by rfl) ⟨11976695, by rfl⟩ : syracuseStep 15968927 = 23953391) B23953391
theorem B437021999 : Blo 1311974 437021999 := bstep (se 1 (by rfl) ⟨327766499, by rfl⟩ : syracuseStep 437021999 = 655532999) B655532999
theorem B2215579 : Blo 1311974 2215579 := bstep (se 1 (by rfl) ⟨1661684, by rfl⟩ : syracuseStep 2215579 = 3323369) B3323369
theorem B18914543 : Blo 1311974 18914543 := bstep (se 1 (by rfl) ⟨14185907, by rfl⟩ : syracuseStep 18914543 = 28371815) B28371815
theorem B12609695 : Blo 1311974 12609695 := bstep (se 1 (by rfl) ⟨9457271, by rfl⟩ : syracuseStep 12609695 = 18914543) B18914543
theorem B10645951 : Blo 1311974 10645951 := bstep (se 1 (by rfl) ⟨7984463, by rfl⟩ : syracuseStep 10645951 = 15968927) B15968927
theorem B2954105 : Blo 1311974 2954105 := bstep (se 2 (by rfl) ⟨1107789, by rfl⟩ : syracuseStep 2954105 = 2215579) B2215579
theorem B291347999 : Blo 1311974 291347999 := bstep (se 1 (by rfl) ⟨218510999, by rfl⟩ : syracuseStep 291347999 = 437021999) B437021999
theorem B8406463 : Blo 1311974 8406463 := bstep (se 1 (by rfl) ⟨6304847, by rfl⟩ : syracuseStep 8406463 = 12609695) B12609695
theorem B1969403 : Blo 1311974 1969403 := bstep (se 1 (by rfl) ⟨1477052, by rfl⟩ : syracuseStep 1969403 = 2954105) B2954105
theorem B14194601 : Blo 1311974 14194601 := bstep (se 2 (by rfl) ⟨5322975, by rfl⟩ : syracuseStep 14194601 = 10645951) B10645951
theorem B194231999 : Blo 1311974 194231999 := bstep (se 1 (by rfl) ⟨145673999, by rfl⟩ : syracuseStep 194231999 = 291347999) B291347999
theorem B9463067 : Blo 1311974 9463067 := bstep (se 1 (by rfl) ⟨7097300, by rfl⟩ : syracuseStep 9463067 = 14194601) B14194601
theorem B11208617 : Blo 1311974 11208617 := bstep (se 2 (by rfl) ⟨4203231, by rfl⟩ : syracuseStep 11208617 = 8406463) B8406463
theorem B1312935 : Blo 1311974 1312935 := bstep (se 1 (by rfl) ⟨984701, by rfl⟩ : syracuseStep 1312935 = 1969403) B1969403
theorem B129487999 : Blo 1311974 129487999 := bstep (se 1 (by rfl) ⟨97115999, by rfl⟩ : syracuseStep 129487999 = 194231999) B194231999
theorem B6308711 : Blo 1311974 6308711 := bstep (se 1 (by rfl) ⟨4731533, by rfl⟩ : syracuseStep 6308711 = 9463067) B9463067
theorem B7472411 : Blo 1311974 7472411 := bstep (se 1 (by rfl) ⟨5604308, by rfl⟩ : syracuseStep 7472411 = 11208617) B11208617
theorem B172650665 : Blo 1311974 172650665 := bstep (se 2 (by rfl) ⟨64743999, by rfl⟩ : syracuseStep 172650665 = 129487999) B129487999
theorem B4981607 : Blo 1311974 4981607 := bstep (se 1 (by rfl) ⟨3736205, by rfl⟩ : syracuseStep 4981607 = 7472411) B7472411
theorem B115100443 : Blo 1311974 115100443 := bstep (se 1 (by rfl) ⟨86325332, by rfl⟩ : syracuseStep 115100443 = 172650665) B172650665
theorem B4205807 : Blo 1311974 4205807 := bstep (se 1 (by rfl) ⟨3154355, by rfl⟩ : syracuseStep 4205807 = 6308711) B6308711
theorem B613869029 : Blo 1311974 613869029 := bstep (se 4 (by rfl) ⟨57550221, by rfl⟩ : syracuseStep 613869029 = 115100443) B115100443
theorem B2803871 : Blo 1311974 2803871 := bstep (se 1 (by rfl) ⟨2102903, by rfl⟩ : syracuseStep 2803871 = 4205807) B4205807
theorem B3321071 : Blo 1311974 3321071 := bstep (se 1 (by rfl) ⟨2490803, by rfl⟩ : syracuseStep 3321071 = 4981607) B4981607
theorem B1869247 : Blo 1311974 1869247 := bstep (se 1 (by rfl) ⟨1401935, by rfl⟩ : syracuseStep 1869247 = 2803871) B2803871
theorem B2214047 : Blo 1311974 2214047 := bstep (se 1 (by rfl) ⟨1660535, by rfl⟩ : syracuseStep 2214047 = 3321071) B3321071
theorem B409246019 : Blo 1311974 409246019 := bstep (se 1 (by rfl) ⟨306934514, by rfl⟩ : syracuseStep 409246019 = 613869029) B613869029
theorem B1476031 : Blo 1311974 1476031 := bstep (se 1 (by rfl) ⟨1107023, by rfl⟩ : syracuseStep 1476031 = 2214047) B2214047
theorem B272830679 : Blo 1311974 272830679 := bstep (se 1 (by rfl) ⟨204623009, by rfl⟩ : syracuseStep 272830679 = 409246019) B409246019
theorem B9969317 : Blo 1311974 9969317 := bstep (se 4 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 9969317 = 1869247) B1869247
theorem B181887119 : Blo 1311974 181887119 := bstep (se 1 (by rfl) ⟨136415339, by rfl⟩ : syracuseStep 181887119 = 272830679) B272830679
theorem B1968041 : Blo 1311974 1968041 := bstep (se 2 (by rfl) ⟨738015, by rfl⟩ : syracuseStep 1968041 = 1476031) B1476031
theorem B6646211 : Blo 1311974 6646211 := bstep (se 1 (by rfl) ⟨4984658, by rfl⟩ : syracuseStep 6646211 = 9969317) B9969317
theorem B121258079 : Blo 1311974 121258079 := bstep (se 1 (by rfl) ⟨90943559, by rfl⟩ : syracuseStep 121258079 = 181887119) B181887119
theorem B1312027 : Blo 1311974 1312027 := bstep (se 1 (by rfl) ⟨984020, by rfl⟩ : syracuseStep 1312027 = 1968041) B1968041
theorem B4430807 : Blo 1311974 4430807 := bstep (se 1 (by rfl) ⟨3323105, by rfl⟩ : syracuseStep 4430807 = 6646211) B6646211
theorem B80838719 : Blo 1311974 80838719 := bstep (se 1 (by rfl) ⟨60629039, by rfl⟩ : syracuseStep 80838719 = 121258079) B121258079
theorem B2953871 : Blo 1311974 2953871 := bstep (se 1 (by rfl) ⟨2215403, by rfl⟩ : syracuseStep 2953871 = 4430807) B4430807
theorem B1969247 : Blo 1311974 1969247 := bstep (se 1 (by rfl) ⟨1476935, by rfl⟩ : syracuseStep 1969247 = 2953871) B2953871
theorem B53892479 : Blo 1311974 53892479 := bstep (se 1 (by rfl) ⟨40419359, by rfl⟩ : syracuseStep 53892479 = 80838719) B80838719
theorem B1312831 : Blo 1311974 1312831 := bstep (se 1 (by rfl) ⟨984623, by rfl⟩ : syracuseStep 1312831 = 1969247) B1969247
theorem B35928319 : Blo 1311974 35928319 := bstep (se 1 (by rfl) ⟨26946239, by rfl⟩ : syracuseStep 35928319 = 53892479) B53892479
theorem B47904425 : Blo 1311974 47904425 := bstep (se 2 (by rfl) ⟨17964159, by rfl⟩ : syracuseStep 47904425 = 35928319) B35928319
theorem B31936283 : Blo 1311974 31936283 := bstep (se 1 (by rfl) ⟨23952212, by rfl⟩ : syracuseStep 31936283 = 47904425) B47904425
theorem B21290855 : Blo 1311974 21290855 := bstep (se 1 (by rfl) ⟨15968141, by rfl⟩ : syracuseStep 21290855 = 31936283) B31936283
theorem B56775613 : Blo 1311974 56775613 := bstep (se 3 (by rfl) ⟨10645427, by rfl⟩ : syracuseStep 56775613 = 21290855) B21290855
theorem B75700817 : Blo 1311974 75700817 := bstep (se 2 (by rfl) ⟨28387806, by rfl⟩ : syracuseStep 75700817 = 56775613) B56775613
theorem B50467211 : Blo 1311974 50467211 := bstep (se 1 (by rfl) ⟨37850408, by rfl⟩ : syracuseStep 50467211 = 75700817) B75700817
theorem B33644807 : Blo 1311974 33644807 := bstep (se 1 (by rfl) ⟨25233605, by rfl⟩ : syracuseStep 33644807 = 50467211) B50467211
theorem B22429871 : Blo 1311974 22429871 := bstep (se 1 (by rfl) ⟨16822403, by rfl⟩ : syracuseStep 22429871 = 33644807) B33644807
theorem B14953247 : Blo 1311974 14953247 := bstep (se 1 (by rfl) ⟨11214935, by rfl⟩ : syracuseStep 14953247 = 22429871) B22429871
theorem B9968831 : Blo 1311974 9968831 := bstep (se 1 (by rfl) ⟨7476623, by rfl⟩ : syracuseStep 9968831 = 14953247) B14953247
theorem B6645887 : Blo 1311974 6645887 := bstep (se 1 (by rfl) ⟨4984415, by rfl⟩ : syracuseStep 6645887 = 9968831) B9968831
theorem B4430591 : Blo 1311974 4430591 := bstep (se 1 (by rfl) ⟨3322943, by rfl⟩ : syracuseStep 4430591 = 6645887) B6645887
theorem B2953727 : Blo 1311974 2953727 := bstep (se 1 (by rfl) ⟨2215295, by rfl⟩ : syracuseStep 2953727 = 4430591) B4430591
theorem B1969151 : Blo 1311974 1969151 := bstep (se 1 (by rfl) ⟨1476863, by rfl⟩ : syracuseStep 1969151 = 2953727) B2953727
theorem B1312767 : Blo 1311974 1312767 := bstep (se 1 (by rfl) ⟨984575, by rfl⟩ : syracuseStep 1312767 = 1969151) B1969151

theorem C0 (j : ℕ) (h1 : 327993 ≤ j) (h2 : j ≤ 328492) : Blo 1311974 (4 * j + 3) := by
  interval_cases j
  · exact B1311975
  · exact B1311979
  · exact B1311983
  · exact B1311987
  · exact B1311991
  · exact B1311995
  · exact B1311999
  · exact B1312003
  · exact B1312007
  · exact B1312011
  · exact B1312015
  · exact B1312019
  · exact B1312023
  · exact B1312027
  · exact B1312031
  · exact B1312035
  · exact B1312039
  · exact B1312043
  · exact B1312047
  · exact B1312051
  · exact B1312055
  · exact B1312059
  · exact B1312063
  · exact B1312067
  · exact B1312071
  · exact B1312075
  · exact B1312079
  · exact B1312083
  · exact B1312087
  · exact B1312091
  · exact B1312095
  · exact B1312099
  · exact B1312103
  · exact B1312107
  · exact B1312111
  · exact B1312115
  · exact B1312119
  · exact B1312123
  · exact B1312127
  · exact B1312131
  · exact B1312135
  · exact B1312139
  · exact B1312143
  · exact B1312147
  · exact B1312151
  · exact B1312155
  · exact B1312159
  · exact B1312163
  · exact B1312167
  · exact B1312171
  · exact B1312175
  · exact B1312179
  · exact B1312183
  · exact B1312187
  · exact B1312191
  · exact B1312195
  · exact B1312199
  · exact B1312203
  · exact B1312207
  · exact B1312211
  · exact B1312215
  · exact B1312219
  · exact B1312223
  · exact B1312227
  · exact B1312231
  · exact B1312235
  · exact B1312239
  · exact B1312243
  · exact B1312247
  · exact B1312251
  · exact B1312255
  · exact B1312259
  · exact B1312263
  · exact B1312267
  · exact B1312271
  · exact B1312275
  · exact B1312279
  · exact B1312283
  · exact B1312287
  · exact B1312291
  · exact B1312295
  · exact B1312299
  · exact B1312303
  · exact B1312307
  · exact B1312311
  · exact B1312315
  · exact B1312319
  · exact B1312323
  · exact B1312327
  · exact B1312331
  · exact B1312335
  · exact B1312339
  · exact B1312343
  · exact B1312347
  · exact B1312351
  · exact B1312355
  · exact B1312359
  · exact B1312363
  · exact B1312367
  · exact B1312371
  · exact B1312375
  · exact B1312379
  · exact B1312383
  · exact B1312387
  · exact B1312391
  · exact B1312395
  · exact B1312399
  · exact B1312403
  · exact B1312407
  · exact B1312411
  · exact B1312415
  · exact B1312419
  · exact B1312423
  · exact B1312427
  · exact B1312431
  · exact B1312435
  · exact B1312439
  · exact B1312443
  · exact B1312447
  · exact B1312451
  · exact B1312455
  · exact B1312459
  · exact B1312463
  · exact B1312467
  · exact B1312471
  · exact B1312475
  · exact B1312479
  · exact B1312483
  · exact B1312487
  · exact B1312491
  · exact B1312495
  · exact B1312499
  · exact B1312503
  · exact B1312507
  · exact B1312511
  · exact B1312515
  · exact B1312519
  · exact B1312523
  · exact B1312527
  · exact B1312531
  · exact B1312535
  · exact B1312539
  · exact B1312543
  · exact B1312547
  · exact B1312551
  · exact B1312555
  · exact B1312559
  · exact B1312563
  · exact B1312567
  · exact B1312571
  · exact B1312575
  · exact B1312579
  · exact B1312583
  · exact B1312587
  · exact B1312591
  · exact B1312595
  · exact B1312599
  · exact B1312603
  · exact B1312607
  · exact B1312611
  · exact B1312615
  · exact B1312619
  · exact B1312623
  · exact B1312627
  · exact B1312631
  · exact B1312635
  · exact B1312639
  · exact B1312643
  · exact B1312647
  · exact B1312651
  · exact B1312655
  · exact B1312659
  · exact B1312663
  · exact B1312667
  · exact B1312671
  · exact B1312675
  · exact B1312679
  · exact B1312683
  · exact B1312687
  · exact B1312691
  · exact B1312695
  · exact B1312699
  · exact B1312703
  · exact B1312707
  · exact B1312711
  · exact B1312715
  · exact B1312719
  · exact B1312723
  · exact B1312727
  · exact B1312731
  · exact B1312735
  · exact B1312739
  · exact B1312743
  · exact B1312747
  · exact B1312751
  · exact B1312755
  · exact B1312759
  · exact B1312763
  · exact B1312767
  · exact B1312771
  · exact B1312775
  · exact B1312779
  · exact B1312783
  · exact B1312787
  · exact B1312791
  · exact B1312795
  · exact B1312799
  · exact B1312803
  · exact B1312807
  · exact B1312811
  · exact B1312815
  · exact B1312819
  · exact B1312823
  · exact B1312827
  · exact B1312831
  · exact B1312835
  · exact B1312839
  · exact B1312843
  · exact B1312847
  · exact B1312851
  · exact B1312855
  · exact B1312859
  · exact B1312863
  · exact B1312867
  · exact B1312871
  · exact B1312875
  · exact B1312879
  · exact B1312883
  · exact B1312887
  · exact B1312891
  · exact B1312895
  · exact B1312899
  · exact B1312903
  · exact B1312907
  · exact B1312911
  · exact B1312915
  · exact B1312919
  · exact B1312923
  · exact B1312927
  · exact B1312931
  · exact B1312935
  · exact B1312939
  · exact B1312943
  · exact B1312947
  · exact B1312951
  · exact B1312955
  · exact B1312959
  · exact B1312963
  · exact B1312967
  · exact B1312971
  · exact B1312975
  · exact B1312979
  · exact B1312983
  · exact B1312987
  · exact B1312991
  · exact B1312995
  · exact B1312999
  · exact B1313003
  · exact B1313007
  · exact B1313011
  · exact B1313015
  · exact B1313019
  · exact B1313023
  · exact B1313027
  · exact B1313031
  · exact B1313035
  · exact B1313039
  · exact B1313043
  · exact B1313047
  · exact B1313051
  · exact B1313055
  · exact B1313059
  · exact B1313063
  · exact B1313067
  · exact B1313071
  · exact B1313075
  · exact B1313079
  · exact B1313083
  · exact B1313087
  · exact B1313091
  · exact B1313095
  · exact B1313099
  · exact B1313103
  · exact B1313107
  · exact B1313111
  · exact B1313115
  · exact B1313119
  · exact B1313123
  · exact B1313127
  · exact B1313131
  · exact B1313135
  · exact B1313139
  · exact B1313143
  · exact B1313147
  · exact B1313151
  · exact B1313155
  · exact B1313159
  · exact B1313163
  · exact B1313167
  · exact B1313171
  · exact B1313175
  · exact B1313179
  · exact B1313183
  · exact B1313187
  · exact B1313191
  · exact B1313195
  · exact B1313199
  · exact B1313203
  · exact B1313207
  · exact B1313211
  · exact B1313215
  · exact B1313219
  · exact B1313223
  · exact B1313227
  · exact B1313231
  · exact B1313235
  · exact B1313239
  · exact B1313243
  · exact B1313247
  · exact B1313251
  · exact B1313255
  · exact B1313259
  · exact B1313263
  · exact B1313267
  · exact B1313271
  · exact B1313275
  · exact B1313279
  · exact B1313283
  · exact B1313287
  · exact B1313291
  · exact B1313295
  · exact B1313299
  · exact B1313303
  · exact B1313307
  · exact B1313311
  · exact B1313315
  · exact B1313319
  · exact B1313323
  · exact B1313327
  · exact B1313331
  · exact B1313335
  · exact B1313339
  · exact B1313343
  · exact B1313347
  · exact B1313351
  · exact B1313355
  · exact B1313359
  · exact B1313363
  · exact B1313367
  · exact B1313371
  · exact B1313375
  · exact B1313379
  · exact B1313383
  · exact B1313387
  · exact B1313391
  · exact B1313395
  · exact B1313399
  · exact B1313403
  · exact B1313407
  · exact B1313411
  · exact B1313415
  · exact B1313419
  · exact B1313423
  · exact B1313427
  · exact B1313431
  · exact B1313435
  · exact B1313439
  · exact B1313443
  · exact B1313447
  · exact B1313451
  · exact B1313455
  · exact B1313459
  · exact B1313463
  · exact B1313467
  · exact B1313471
  · exact B1313475
  · exact B1313479
  · exact B1313483
  · exact B1313487
  · exact B1313491
  · exact B1313495
  · exact B1313499
  · exact B1313503
  · exact B1313507
  · exact B1313511
  · exact B1313515
  · exact B1313519
  · exact B1313523
  · exact B1313527
  · exact B1313531
  · exact B1313535
  · exact B1313539
  · exact B1313543
  · exact B1313547
  · exact B1313551
  · exact B1313555
  · exact B1313559
  · exact B1313563
  · exact B1313567
  · exact B1313571
  · exact B1313575
  · exact B1313579
  · exact B1313583
  · exact B1313587
  · exact B1313591
  · exact B1313595
  · exact B1313599
  · exact B1313603
  · exact B1313607
  · exact B1313611
  · exact B1313615
  · exact B1313619
  · exact B1313623
  · exact B1313627
  · exact B1313631
  · exact B1313635
  · exact B1313639
  · exact B1313643
  · exact B1313647
  · exact B1313651
  · exact B1313655
  · exact B1313659
  · exact B1313663
  · exact B1313667
  · exact B1313671
  · exact B1313675
  · exact B1313679
  · exact B1313683
  · exact B1313687
  · exact B1313691
  · exact B1313695
  · exact B1313699
  · exact B1313703
  · exact B1313707
  · exact B1313711
  · exact B1313715
  · exact B1313719
  · exact B1313723
  · exact B1313727
  · exact B1313731
  · exact B1313735
  · exact B1313739
  · exact B1313743
  · exact B1313747
  · exact B1313751
  · exact B1313755
  · exact B1313759
  · exact B1313763
  · exact B1313767
  · exact B1313771
  · exact B1313775
  · exact B1313779
  · exact B1313783
  · exact B1313787
  · exact B1313791
  · exact B1313795
  · exact B1313799
  · exact B1313803
  · exact B1313807
  · exact B1313811
  · exact B1313815
  · exact B1313819
  · exact B1313823
  · exact B1313827
  · exact B1313831
  · exact B1313835
  · exact B1313839
  · exact B1313843
  · exact B1313847
  · exact B1313851
  · exact B1313855
  · exact B1313859
  · exact B1313863
  · exact B1313867
  · exact B1313871
  · exact B1313875
  · exact B1313879
  · exact B1313883
  · exact B1313887
  · exact B1313891
  · exact B1313895
  · exact B1313899
  · exact B1313903
  · exact B1313907
  · exact B1313911
  · exact B1313915
  · exact B1313919
  · exact B1313923
  · exact B1313927
  · exact B1313931
  · exact B1313935
  · exact B1313939
  · exact B1313943
  · exact B1313947
  · exact B1313951
  · exact B1313955
  · exact B1313959
  · exact B1313963
  · exact B1313967
  · exact B1313971

theorem solution (m : ℕ) (hlo : 1311974 ≤ m) (hhi : m ≤ 1313974) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 327993 ≤ j := by omega
    have hj2 : j ≤ 328492 := by omega
    have hb : Blo 1311974 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
