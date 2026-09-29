-- Prove2me | solution 1 for syracuse_descends_range_151794_155794
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:40.098397+00:00
-- url     : https://prove2.me/submissions/13d441ee-533b-4a28-9be5-5a17631812e4

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


theorem B229397 : Blo 151794 229397 := bbase (se 6 (by rfl) ⟨5376, by rfl⟩ : syracuseStep 229397 = 10753) (by norm_num)
theorem B327701 : Blo 151794 327701 := bbase (se 6 (by rfl) ⟨7680, by rfl⟩ : syracuseStep 327701 = 15361) (by norm_num)
theorem B393245 : Blo 151794 393245 := bbase (se 3 (by rfl) ⟨73733, by rfl⟩ : syracuseStep 393245 = 147467) (by norm_num)
theorem B294941 : Blo 151794 294941 := bbase (se 3 (by rfl) ⟨55301, by rfl⟩ : syracuseStep 294941 = 110603) (by norm_num)
theorem B229421 : Blo 151794 229421 := bbase (se 3 (by rfl) ⟨43016, by rfl⟩ : syracuseStep 229421 = 86033) (by norm_num)
theorem B229445 : Blo 151794 229445 := bbase (se 4 (by rfl) ⟨21510, by rfl⟩ : syracuseStep 229445 = 43021) (by norm_num)
theorem B229469 : Blo 151794 229469 := bbase (se 3 (by rfl) ⟨43025, by rfl⟩ : syracuseStep 229469 = 86051) (by norm_num)
theorem B262237 : Blo 151794 262237 := bbase (se 3 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 262237 = 98339) (by norm_num)
theorem B229493 : Blo 151794 229493 := bbase (se 5 (by rfl) ⟨10757, by rfl⟩ : syracuseStep 229493 = 21515) (by norm_num)
theorem B229517 : Blo 151794 229517 := bbase (se 3 (by rfl) ⟨43034, by rfl⟩ : syracuseStep 229517 = 86069) (by norm_num)
theorem B196769 : Blo 151794 196769 := bbase (se 2 (by rfl) ⟨73788, by rfl⟩ : syracuseStep 196769 = 147577) (by norm_num)
theorem B229541 : Blo 151794 229541 := bbase (se 4 (by rfl) ⟨21519, by rfl⟩ : syracuseStep 229541 = 43039) (by norm_num)
theorem B327845 : Blo 151794 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B295093 : Blo 151794 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B262325 : Blo 151794 262325 := bbase (se 5 (by rfl) ⟨12296, by rfl⟩ : syracuseStep 262325 = 24593) (by norm_num)
theorem B229565 : Blo 151794 229565 := bbase (se 3 (by rfl) ⟨43043, by rfl⟩ : syracuseStep 229565 = 86087) (by norm_num)
theorem B229589 : Blo 151794 229589 := bbase (se 7 (by rfl) ⟨2690, by rfl⟩ : syracuseStep 229589 = 5381) (by norm_num)
theorem B524501 : Blo 151794 524501 := bbase (se 7 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 524501 = 12293) (by norm_num)
theorem B196825 : Blo 151794 196825 := bbase (se 2 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 196825 = 147619) (by norm_num)
theorem B393437 : Blo 151794 393437 := bbase (se 3 (by rfl) ⟨73769, by rfl⟩ : syracuseStep 393437 = 147539) (by norm_num)
theorem B229613 : Blo 151794 229613 := bbase (se 3 (by rfl) ⟨43052, by rfl⟩ : syracuseStep 229613 = 86105) (by norm_num)
theorem B229637 : Blo 151794 229637 := bbase (se 4 (by rfl) ⟨21528, by rfl⟩ : syracuseStep 229637 = 43057) (by norm_num)
theorem B229661 : Blo 151794 229661 := bbase (se 3 (by rfl) ⟨43061, by rfl⟩ : syracuseStep 229661 = 86123) (by norm_num)
theorem B229685 : Blo 151794 229685 := bbase (se 5 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 229685 = 21533) (by norm_num)
theorem B262453 : Blo 151794 262453 := bbase (se 5 (by rfl) ⟨12302, by rfl⟩ : syracuseStep 262453 = 24605) (by norm_num)
theorem B196921 : Blo 151794 196921 := bbase (se 2 (by rfl) ⟨73845, by rfl⟩ : syracuseStep 196921 = 147691) (by norm_num)
theorem B229709 : Blo 151794 229709 := bbase (se 3 (by rfl) ⟨43070, by rfl⟩ : syracuseStep 229709 = 86141) (by norm_num)
theorem B229733 : Blo 151794 229733 := bbase (se 4 (by rfl) ⟨21537, by rfl⟩ : syracuseStep 229733 = 43075) (by norm_num)
theorem B229757 : Blo 151794 229757 := bbase (se 3 (by rfl) ⟨43079, by rfl⟩ : syracuseStep 229757 = 86159) (by norm_num)
theorem B262541 : Blo 151794 262541 := bbase (se 3 (by rfl) ⟨49226, by rfl⟩ : syracuseStep 262541 = 98453) (by norm_num)
theorem B229781 : Blo 151794 229781 := bbase (se 6 (by rfl) ⟨5385, by rfl⟩ : syracuseStep 229781 = 10771) (by norm_num)
theorem B229805 : Blo 151794 229805 := bbase (se 3 (by rfl) ⟨43088, by rfl⟩ : syracuseStep 229805 = 86177) (by norm_num)
theorem B164273 : Blo 151794 164273 := bbase (se 2 (by rfl) ⟨61602, by rfl⟩ : syracuseStep 164273 = 123205) (by norm_num)
theorem B229829 : Blo 151794 229829 := bbase (se 4 (by rfl) ⟨21546, by rfl⟩ : syracuseStep 229829 = 43093) (by norm_num)
theorem B623045 : Blo 151794 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B229853 : Blo 151794 229853 := bbase (se 3 (by rfl) ⟨43097, by rfl⟩ : syracuseStep 229853 = 86195) (by norm_num)
theorem B295397 : Blo 151794 295397 := bbase (se 4 (by rfl) ⟨27693, by rfl⟩ : syracuseStep 295397 = 55387) (by norm_num)
theorem B197093 : Blo 151794 197093 := bbase (se 4 (by rfl) ⟨18477, by rfl⟩ : syracuseStep 197093 = 36955) (by norm_num)
theorem B229877 : Blo 151794 229877 := bbase (se 5 (by rfl) ⟨10775, by rfl⟩ : syracuseStep 229877 = 21551) (by norm_num)
theorem B229901 : Blo 151794 229901 := bbase (se 3 (by rfl) ⟨43106, by rfl⟩ : syracuseStep 229901 = 86213) (by norm_num)
theorem B328205 : Blo 151794 328205 := bbase (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) (by norm_num)
theorem B262669 : Blo 151794 262669 := bbase (se 3 (by rfl) ⟨49250, by rfl⟩ : syracuseStep 262669 = 98501) (by norm_num)
theorem B197149 : Blo 151794 197149 := bbase (se 3 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 197149 = 73931) (by norm_num)
theorem B229925 : Blo 151794 229925 := bbase (se 4 (by rfl) ⟨21555, by rfl⟩ : syracuseStep 229925 = 43111) (by norm_num)
theorem B393781 : Blo 151794 393781 := bbase (se 5 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 393781 = 36917) (by norm_num)
theorem B229949 : Blo 151794 229949 := bbase (se 3 (by rfl) ⟨43115, by rfl⟩ : syracuseStep 229949 = 86231) (by norm_num)
theorem B229973 : Blo 151794 229973 := bbase (se 8 (by rfl) ⟨1347, by rfl⟩ : syracuseStep 229973 = 2695) (by norm_num)
theorem B262757 : Blo 151794 262757 := bbase (se 4 (by rfl) ⟨24633, by rfl⟩ : syracuseStep 262757 = 49267) (by norm_num)
theorem B229997 : Blo 151794 229997 := bbase (se 3 (by rfl) ⟨43124, by rfl⟩ : syracuseStep 229997 = 86249) (by norm_num)
theorem B230021 : Blo 151794 230021 := bbase (se 4 (by rfl) ⟨21564, by rfl⟩ : syracuseStep 230021 = 43129) (by norm_num)
theorem B524933 : Blo 151794 524933 := bbase (se 4 (by rfl) ⟨49212, by rfl⟩ : syracuseStep 524933 = 98425) (by norm_num)
theorem B164497 : Blo 151794 164497 := bbase (se 2 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 164497 = 123373) (by norm_num)
theorem B230045 : Blo 151794 230045 := bbase (se 3 (by rfl) ⟨43133, by rfl⟩ : syracuseStep 230045 = 86267) (by norm_num)
theorem B393893 : Blo 151794 393893 := bbase (se 4 (by rfl) ⟨36927, by rfl⟩ : syracuseStep 393893 = 73855) (by norm_num)
theorem B164521 : Blo 151794 164521 := bbase (se 2 (by rfl) ⟨61695, by rfl⟩ : syracuseStep 164521 = 123391) (by norm_num)
theorem B230069 : Blo 151794 230069 := bbase (se 5 (by rfl) ⟨10784, by rfl⟩ : syracuseStep 230069 = 21569) (by norm_num)
theorem B230093 : Blo 151794 230093 := bbase (se 3 (by rfl) ⟨43142, by rfl⟩ : syracuseStep 230093 = 86285) (by norm_num)
theorem B787157 : Blo 151794 787157 := bbase (se 7 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 787157 = 18449) (by norm_num)
theorem B230117 : Blo 151794 230117 := bbase (se 4 (by rfl) ⟨21573, by rfl⟩ : syracuseStep 230117 = 43147) (by norm_num)
theorem B262885 : Blo 151794 262885 := bbase (se 4 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 262885 = 49291) (by norm_num)
theorem B230141 : Blo 151794 230141 := bbase (se 3 (by rfl) ⟨43151, by rfl⟩ : syracuseStep 230141 = 86303) (by norm_num)
theorem B590597 : Blo 151794 590597 := bbase (se 4 (by rfl) ⟨55368, by rfl⟩ : syracuseStep 590597 = 110737) (by norm_num)
theorem B230165 : Blo 151794 230165 := bbase (se 6 (by rfl) ⟨5394, by rfl⟩ : syracuseStep 230165 = 10789) (by norm_num)
theorem B230189 : Blo 151794 230189 := bbase (se 3 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 230189 = 86321) (by norm_num)
theorem B230213 : Blo 151794 230213 := bbase (se 4 (by rfl) ⟨21582, by rfl⟩ : syracuseStep 230213 = 43165) (by norm_num)
theorem B230237 : Blo 151794 230237 := bbase (se 3 (by rfl) ⟨43169, by rfl⟩ : syracuseStep 230237 = 86339) (by norm_num)
theorem B394085 : Blo 151794 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B230261 : Blo 151794 230261 := bbase (se 5 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 230261 = 21587) (by norm_num)
theorem B230285 : Blo 151794 230285 := bbase (se 3 (by rfl) ⟨43178, by rfl⟩ : syracuseStep 230285 = 86357) (by norm_num)
theorem B230309 : Blo 151794 230309 := bbase (se 4 (by rfl) ⟨21591, by rfl⟩ : syracuseStep 230309 = 43183) (by norm_num)
theorem B230333 : Blo 151794 230333 := bbase (se 3 (by rfl) ⟨43187, by rfl⟩ : syracuseStep 230333 = 86375) (by norm_num)
theorem B492485 : Blo 151794 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B230357 : Blo 151794 230357 := bbase (se 7 (by rfl) ⟨2699, by rfl⟩ : syracuseStep 230357 = 5399) (by norm_num)
theorem B230381 : Blo 151794 230381 := bbase (se 3 (by rfl) ⟨43196, by rfl⟩ : syracuseStep 230381 = 86393) (by norm_num)
theorem B230405 : Blo 151794 230405 := bbase (se 4 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 230405 = 43201) (by norm_num)
theorem B230429 : Blo 151794 230429 := bbase (se 3 (by rfl) ⟨43205, by rfl⟩ : syracuseStep 230429 = 86411) (by norm_num)
theorem B590885 : Blo 151794 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B230453 : Blo 151794 230453 := bbase (se 5 (by rfl) ⟨10802, by rfl⟩ : syracuseStep 230453 = 21605) (by norm_num)
theorem B525365 : Blo 151794 525365 := bbase (se 5 (by rfl) ⟨24626, by rfl⟩ : syracuseStep 525365 = 49253) (by norm_num)
theorem B230477 : Blo 151794 230477 := bbase (se 3 (by rfl) ⟨43214, by rfl⟩ : syracuseStep 230477 = 86429) (by norm_num)
theorem B230501 : Blo 151794 230501 := bbase (se 4 (by rfl) ⟨21609, by rfl⟩ : syracuseStep 230501 = 43219) (by norm_num)
theorem B164965 : Blo 151794 164965 := bbase (se 4 (by rfl) ⟨15465, by rfl⟩ : syracuseStep 164965 = 30931) (by norm_num)
theorem B230525 : Blo 151794 230525 := bbase (se 3 (by rfl) ⟨43223, by rfl⟩ : syracuseStep 230525 = 86447) (by norm_num)
theorem B230549 : Blo 151794 230549 := bbase (se 6 (by rfl) ⟨5403, by rfl⟩ : syracuseStep 230549 = 10807) (by norm_num)
theorem B165025 : Blo 151794 165025 := bbase (se 2 (by rfl) ⟨61884, by rfl⟩ : syracuseStep 165025 = 123769) (by norm_num)
theorem B230573 : Blo 151794 230573 := bbase (se 3 (by rfl) ⟨43232, by rfl⟩ : syracuseStep 230573 = 86465) (by norm_num)
theorem B230597 : Blo 151794 230597 := bbase (se 4 (by rfl) ⟨21618, by rfl⟩ : syracuseStep 230597 = 43237) (by norm_num)
theorem B230621 : Blo 151794 230621 := bbase (se 3 (by rfl) ⟨43241, by rfl⟩ : syracuseStep 230621 = 86483) (by norm_num)
theorem B230645 : Blo 151794 230645 := bbase (se 5 (by rfl) ⟨10811, by rfl⟩ : syracuseStep 230645 = 21623) (by norm_num)
theorem B230669 : Blo 151794 230669 := bbase (se 3 (by rfl) ⟨43250, by rfl⟩ : syracuseStep 230669 = 86501) (by norm_num)
theorem B230693 : Blo 151794 230693 := bbase (se 4 (by rfl) ⟨21627, by rfl⟩ : syracuseStep 230693 = 43255) (by norm_num)
theorem B558373 : Blo 151794 558373 := bbase (se 4 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 558373 = 104695) (by norm_num)
theorem B787765 : Blo 151794 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B230717 : Blo 151794 230717 := bbase (se 3 (by rfl) ⟨43259, by rfl⟩ : syracuseStep 230717 = 86519) (by norm_num)
theorem B230741 : Blo 151794 230741 := bbase (se 12 (by rfl) ⟨84, by rfl⟩ : syracuseStep 230741 = 169) (by norm_num)
theorem B230765 : Blo 151794 230765 := bbase (se 3 (by rfl) ⟨43268, by rfl⟩ : syracuseStep 230765 = 86537) (by norm_num)
theorem B230789 : Blo 151794 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B329093 : Blo 151794 329093 := bbase (se 4 (by rfl) ⟨30852, by rfl⟩ : syracuseStep 329093 = 61705) (by norm_num)
theorem B230813 : Blo 151794 230813 := bbase (se 3 (by rfl) ⟨43277, by rfl⟩ : syracuseStep 230813 = 86555) (by norm_num)
theorem B230837 : Blo 151794 230837 := bbase (se 5 (by rfl) ⟨10820, by rfl⟩ : syracuseStep 230837 = 21641) (by norm_num)
theorem B230861 : Blo 151794 230861 := bbase (se 3 (by rfl) ⟨43286, by rfl⟩ : syracuseStep 230861 = 86573) (by norm_num)
theorem B165341 : Blo 151794 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B230885 : Blo 151794 230885 := bbase (se 4 (by rfl) ⟨21645, by rfl⟩ : syracuseStep 230885 = 43291) (by norm_num)
theorem B525797 : Blo 151794 525797 := bbase (se 4 (by rfl) ⟨49293, by rfl⟩ : syracuseStep 525797 = 98587) (by norm_num)
theorem B230909 : Blo 151794 230909 := bbase (se 3 (by rfl) ⟨43295, by rfl⟩ : syracuseStep 230909 = 86591) (by norm_num)
theorem B230917 : Blo 151794 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B230933 : Blo 151794 230933 := bbase (se 6 (by rfl) ⟨5412, by rfl⟩ : syracuseStep 230933 = 10825) (by norm_num)
theorem B230957 : Blo 151794 230957 := bbase (se 3 (by rfl) ⟨43304, by rfl⟩ : syracuseStep 230957 = 86609) (by norm_num)
theorem B394813 : Blo 151794 394813 := bbase (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) (by norm_num)
theorem B230981 : Blo 151794 230981 := bbase (se 4 (by rfl) ⟨21654, by rfl⟩ : syracuseStep 230981 = 43309) (by norm_num)
theorem B231005 : Blo 151794 231005 := bbase (se 3 (by rfl) ⟨43313, by rfl⟩ : syracuseStep 231005 = 86627) (by norm_num)
theorem B231029 : Blo 151794 231029 := bbase (se 5 (by rfl) ⟨10829, by rfl⟩ : syracuseStep 231029 = 21659) (by norm_num)
theorem B1115765 : Blo 151794 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B329341 : Blo 151794 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B231053 : Blo 151794 231053 := bbase (se 3 (by rfl) ⟨43322, by rfl⟩ : syracuseStep 231053 = 86645) (by norm_num)
theorem B231077 : Blo 151794 231077 := bbase (se 4 (by rfl) ⟨21663, by rfl⟩ : syracuseStep 231077 = 43327) (by norm_num)
theorem B231101 : Blo 151794 231101 := bbase (se 3 (by rfl) ⟨43331, by rfl⟩ : syracuseStep 231101 = 86663) (by norm_num)
theorem B394949 : Blo 151794 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B231125 : Blo 151794 231125 := bbase (se 7 (by rfl) ⟨2708, by rfl⟩ : syracuseStep 231125 = 5417) (by norm_num)
theorem B231149 : Blo 151794 231149 := bbase (se 3 (by rfl) ⟨43340, by rfl⟩ : syracuseStep 231149 = 86681) (by norm_num)
theorem B231173 : Blo 151794 231173 := bbase (se 4 (by rfl) ⟨21672, by rfl⟩ : syracuseStep 231173 = 43345) (by norm_num)
theorem B231197 : Blo 151794 231197 := bbase (se 3 (by rfl) ⟨43349, by rfl⟩ : syracuseStep 231197 = 86699) (by norm_num)
theorem B231221 : Blo 151794 231221 := bbase (se 5 (by rfl) ⟨10838, by rfl⟩ : syracuseStep 231221 = 21677) (by norm_num)
theorem B231245 : Blo 151794 231245 := bbase (se 3 (by rfl) ⟨43358, by rfl⟩ : syracuseStep 231245 = 86717) (by norm_num)
theorem B493397 : Blo 151794 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B231269 : Blo 151794 231269 := bbase (se 4 (by rfl) ⟨21681, by rfl⟩ : syracuseStep 231269 = 43363) (by norm_num)
theorem B231293 : Blo 151794 231293 := bbase (se 3 (by rfl) ⟨43367, by rfl⟩ : syracuseStep 231293 = 86735) (by norm_num)
theorem B231317 : Blo 151794 231317 := bbase (se 6 (by rfl) ⟨5421, by rfl⟩ : syracuseStep 231317 = 10843) (by norm_num)
theorem B165785 : Blo 151794 165785 := bbase (se 2 (by rfl) ⟨62169, by rfl⟩ : syracuseStep 165785 = 124339) (by norm_num)
theorem B231341 : Blo 151794 231341 := bbase (se 3 (by rfl) ⟨43376, by rfl⟩ : syracuseStep 231341 = 86753) (by norm_num)
theorem B231365 : Blo 151794 231365 := bbase (se 4 (by rfl) ⟨21690, by rfl⟩ : syracuseStep 231365 = 43381) (by norm_num)
theorem B755669 : Blo 151794 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B165845 : Blo 151794 165845 := bbase (se 7 (by rfl) ⟨1943, by rfl⟩ : syracuseStep 165845 = 3887) (by norm_num)
theorem B231389 : Blo 151794 231389 := bbase (se 3 (by rfl) ⟨43385, by rfl⟩ : syracuseStep 231389 = 86771) (by norm_num)
theorem B788453 : Blo 151794 788453 := bbase (se 4 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 788453 = 147835) (by norm_num)
theorem B231413 : Blo 151794 231413 := bbase (se 5 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 231413 = 21695) (by norm_num)
theorem B231437 : Blo 151794 231437 := bbase (se 3 (by rfl) ⟨43394, by rfl⟩ : syracuseStep 231437 = 86789) (by norm_num)
theorem B231461 : Blo 151794 231461 := bbase (se 4 (by rfl) ⟨21699, by rfl⟩ : syracuseStep 231461 = 43399) (by norm_num)
theorem B231485 : Blo 151794 231485 := bbase (se 3 (by rfl) ⟨43403, by rfl⟩ : syracuseStep 231485 = 86807) (by norm_num)
theorem B231509 : Blo 151794 231509 := bbase (se 8 (by rfl) ⟨1356, by rfl⟩ : syracuseStep 231509 = 2713) (by norm_num)
theorem B165973 : Blo 151794 165973 := bbase (se 8 (by rfl) ⟨972, by rfl⟩ : syracuseStep 165973 = 1945) (by norm_num)
theorem B231533 : Blo 151794 231533 := bbase (se 3 (by rfl) ⟨43412, by rfl⟩ : syracuseStep 231533 = 86825) (by norm_num)
theorem B395381 : Blo 151794 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B329845 : Blo 151794 329845 := bbase (se 5 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 329845 = 30923) (by norm_num)
theorem B231557 : Blo 151794 231557 := bbase (se 4 (by rfl) ⟨21708, by rfl⟩ : syracuseStep 231557 = 43417) (by norm_num)
theorem B559237 : Blo 151794 559237 := bbase (se 4 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 559237 = 104857) (by norm_num)
theorem B231581 : Blo 151794 231581 := bbase (se 3 (by rfl) ⟨43421, by rfl⟩ : syracuseStep 231581 = 86843) (by norm_num)
theorem B231605 : Blo 151794 231605 := bbase (se 5 (by rfl) ⟨10856, by rfl⟩ : syracuseStep 231605 = 21713) (by norm_num)
theorem B231629 : Blo 151794 231629 := bbase (se 3 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 231629 = 86861) (by norm_num)
theorem B592085 : Blo 151794 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B231653 : Blo 151794 231653 := bbase (se 4 (by rfl) ⟨21717, by rfl⟩ : syracuseStep 231653 = 43435) (by norm_num)
theorem B231677 : Blo 151794 231677 := bbase (se 3 (by rfl) ⟨43439, by rfl⟩ : syracuseStep 231677 = 86879) (by norm_num)
theorem B231701 : Blo 151794 231701 := bbase (se 6 (by rfl) ⟨5430, by rfl⟩ : syracuseStep 231701 = 10861) (by norm_num)
theorem B264485 : Blo 151794 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B231725 : Blo 151794 231725 := bbase (se 3 (by rfl) ⟨43448, by rfl⟩ : syracuseStep 231725 = 86897) (by norm_num)
theorem B231749 : Blo 151794 231749 := bbase (se 4 (by rfl) ⟨21726, by rfl⟩ : syracuseStep 231749 = 43453) (by norm_num)
theorem B3705173 : Blo 151794 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B559445 : Blo 151794 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B231773 : Blo 151794 231773 := bbase (se 3 (by rfl) ⟨43457, by rfl⟩ : syracuseStep 231773 = 86915) (by norm_num)
theorem B231797 : Blo 151794 231797 := bbase (se 5 (by rfl) ⟨10865, by rfl⟩ : syracuseStep 231797 = 21731) (by norm_num)
theorem B231821 : Blo 151794 231821 := bbase (se 3 (by rfl) ⟨43466, by rfl⟩ : syracuseStep 231821 = 86933) (by norm_num)
theorem B231845 : Blo 151794 231845 := bbase (se 4 (by rfl) ⟨21735, by rfl⟩ : syracuseStep 231845 = 43471) (by norm_num)
theorem B231869 : Blo 151794 231869 := bbase (se 3 (by rfl) ⟨43475, by rfl⟩ : syracuseStep 231869 = 86951) (by norm_num)
theorem B657877 : Blo 151794 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B231893 : Blo 151794 231893 := bbase (se 7 (by rfl) ⟨2717, by rfl⟩ : syracuseStep 231893 = 5435) (by norm_num)
theorem B231917 : Blo 151794 231917 := bbase (se 3 (by rfl) ⟨43484, by rfl⟩ : syracuseStep 231917 = 86969) (by norm_num)
theorem B231941 : Blo 151794 231941 := bbase (se 4 (by rfl) ⟨21744, by rfl⟩ : syracuseStep 231941 = 43489) (by norm_num)
theorem B231965 : Blo 151794 231965 := bbase (se 3 (by rfl) ⟨43493, by rfl⟩ : syracuseStep 231965 = 86987) (by norm_num)
theorem B231989 : Blo 151794 231989 := bbase (se 5 (by rfl) ⟨10874, by rfl⟩ : syracuseStep 231989 = 21749) (by norm_num)
theorem B559685 : Blo 151794 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B232013 : Blo 151794 232013 := bbase (se 3 (by rfl) ⟨43502, by rfl⟩ : syracuseStep 232013 = 87005) (by norm_num)
theorem B232037 : Blo 151794 232037 := bbase (se 4 (by rfl) ⟨21753, by rfl⟩ : syracuseStep 232037 = 43507) (by norm_num)
theorem B232061 : Blo 151794 232061 := bbase (se 3 (by rfl) ⟨43511, by rfl⟩ : syracuseStep 232061 = 87023) (by norm_num)
theorem B232085 : Blo 151794 232085 := bbase (se 6 (by rfl) ⟨5439, by rfl⟩ : syracuseStep 232085 = 10879) (by norm_num)
theorem B232109 : Blo 151794 232109 := bbase (se 3 (by rfl) ⟨43520, by rfl⟩ : syracuseStep 232109 = 87041) (by norm_num)
theorem B232133 : Blo 151794 232133 := bbase (se 4 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 232133 = 43525) (by norm_num)
theorem B559813 : Blo 151794 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B232157 : Blo 151794 232157 := bbase (se 3 (by rfl) ⟨43529, by rfl⟩ : syracuseStep 232157 = 87059) (by norm_num)
theorem B232181 : Blo 151794 232181 := bbase (se 5 (by rfl) ⟨10883, by rfl⟩ : syracuseStep 232181 = 21767) (by norm_num)
theorem B232205 : Blo 151794 232205 := bbase (se 3 (by rfl) ⟨43538, by rfl⟩ : syracuseStep 232205 = 87077) (by norm_num)
theorem B232229 : Blo 151794 232229 := bbase (se 4 (by rfl) ⟨21771, by rfl⟩ : syracuseStep 232229 = 43543) (by norm_num)
theorem B232253 : Blo 151794 232253 := bbase (se 3 (by rfl) ⟨43547, by rfl⟩ : syracuseStep 232253 = 87095) (by norm_num)
theorem B265037 : Blo 151794 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B232277 : Blo 151794 232277 := bbase (se 9 (by rfl) ⟨680, by rfl⟩ : syracuseStep 232277 = 1361) (by norm_num)
theorem B232301 : Blo 151794 232301 := bbase (se 3 (by rfl) ⟨43556, by rfl⟩ : syracuseStep 232301 = 87113) (by norm_num)
theorem B232325 : Blo 151794 232325 := bbase (se 4 (by rfl) ⟨21780, by rfl⟩ : syracuseStep 232325 = 43561) (by norm_num)
theorem B232349 : Blo 151794 232349 := bbase (se 3 (by rfl) ⟨43565, by rfl⟩ : syracuseStep 232349 = 87131) (by norm_num)
theorem B232373 : Blo 151794 232373 := bbase (se 5 (by rfl) ⟨10892, by rfl⟩ : syracuseStep 232373 = 21785) (by norm_num)
theorem B232397 : Blo 151794 232397 := bbase (se 3 (by rfl) ⟨43574, by rfl⟩ : syracuseStep 232397 = 87149) (by norm_num)
theorem B232421 : Blo 151794 232421 := bbase (se 4 (by rfl) ⟨21789, by rfl⟩ : syracuseStep 232421 = 43579) (by norm_num)
theorem B330733 : Blo 151794 330733 := bbase (se 3 (by rfl) ⟨62012, by rfl⟩ : syracuseStep 330733 = 124025) (by norm_num)
theorem B232445 : Blo 151794 232445 := bbase (se 3 (by rfl) ⟨43583, by rfl⟩ : syracuseStep 232445 = 87167) (by norm_num)
theorem B232469 : Blo 151794 232469 := bbase (se 6 (by rfl) ⟨5448, by rfl⟩ : syracuseStep 232469 = 10897) (by norm_num)
theorem B232493 : Blo 151794 232493 := bbase (se 3 (by rfl) ⟨43592, by rfl⟩ : syracuseStep 232493 = 87185) (by norm_num)
theorem B232517 : Blo 151794 232517 := bbase (se 4 (by rfl) ⟨21798, by rfl⟩ : syracuseStep 232517 = 43597) (by norm_num)
theorem B2821205 : Blo 151794 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B232541 : Blo 151794 232541 := bbase (se 3 (by rfl) ⟨43601, by rfl⟩ : syracuseStep 232541 = 87203) (by norm_num)
theorem B232565 : Blo 151794 232565 := bbase (se 5 (by rfl) ⟨10901, by rfl⟩ : syracuseStep 232565 = 21803) (by norm_num)
theorem B232589 : Blo 151794 232589 := bbase (se 3 (by rfl) ⟨43610, by rfl⟩ : syracuseStep 232589 = 87221) (by norm_num)
theorem B494741 : Blo 151794 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B232613 : Blo 151794 232613 := bbase (se 4 (by rfl) ⟨21807, by rfl⟩ : syracuseStep 232613 = 43615) (by norm_num)
theorem B232637 : Blo 151794 232637 := bbase (se 3 (by rfl) ⟨43619, by rfl⟩ : syracuseStep 232637 = 87239) (by norm_num)
theorem B232661 : Blo 151794 232661 := bbase (se 7 (by rfl) ⟨2726, by rfl⟩ : syracuseStep 232661 = 5453) (by norm_num)
theorem B232685 : Blo 151794 232685 := bbase (se 3 (by rfl) ⟨43628, by rfl⟩ : syracuseStep 232685 = 87257) (by norm_num)
theorem B232709 : Blo 151794 232709 := bbase (se 4 (by rfl) ⟨21816, by rfl⟩ : syracuseStep 232709 = 43633) (by norm_num)
theorem B593173 : Blo 151794 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B232733 : Blo 151794 232733 := bbase (se 3 (by rfl) ⟨43637, by rfl⟩ : syracuseStep 232733 = 87275) (by norm_num)
theorem B232757 : Blo 151794 232757 := bbase (se 5 (by rfl) ⟨10910, by rfl⟩ : syracuseStep 232757 = 21821) (by norm_num)
theorem B232781 : Blo 151794 232781 := bbase (se 3 (by rfl) ⟨43646, by rfl⟩ : syracuseStep 232781 = 87293) (by norm_num)
theorem B232805 : Blo 151794 232805 := bbase (se 4 (by rfl) ⟨21825, by rfl⟩ : syracuseStep 232805 = 43651) (by norm_num)
theorem B232829 : Blo 151794 232829 := bbase (se 3 (by rfl) ⟨43655, by rfl⟩ : syracuseStep 232829 = 87311) (by norm_num)
theorem B232853 : Blo 151794 232853 := bbase (se 6 (by rfl) ⟨5457, by rfl⟩ : syracuseStep 232853 = 10915) (by norm_num)
theorem B232877 : Blo 151794 232877 := bbase (se 3 (by rfl) ⟨43664, by rfl⟩ : syracuseStep 232877 = 87329) (by norm_num)
theorem B232901 : Blo 151794 232901 := bbase (se 4 (by rfl) ⟨21834, by rfl⟩ : syracuseStep 232901 = 43669) (by norm_num)
theorem B331229 : Blo 151794 331229 := bbase (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) (by norm_num)
theorem B232925 : Blo 151794 232925 := bbase (se 3 (by rfl) ⟨43673, by rfl⟩ : syracuseStep 232925 = 87347) (by norm_num)
theorem B232949 : Blo 151794 232949 := bbase (se 5 (by rfl) ⟨10919, by rfl⟩ : syracuseStep 232949 = 21839) (by norm_num)
theorem B232973 : Blo 151794 232973 := bbase (se 3 (by rfl) ⟨43682, by rfl⟩ : syracuseStep 232973 = 87365) (by norm_num)
theorem B232997 : Blo 151794 232997 := bbase (se 4 (by rfl) ⟨21843, by rfl⟩ : syracuseStep 232997 = 43687) (by norm_num)
theorem B233021 : Blo 151794 233021 := bbase (se 3 (by rfl) ⟨43691, by rfl⟩ : syracuseStep 233021 = 87383) (by norm_num)
theorem B233045 : Blo 151794 233045 := bbase (se 8 (by rfl) ⟨1365, by rfl⟩ : syracuseStep 233045 = 2731) (by norm_num)
theorem B233069 : Blo 151794 233069 := bbase (se 3 (by rfl) ⟨43700, by rfl⟩ : syracuseStep 233069 = 87401) (by norm_num)
theorem B233093 : Blo 151794 233093 := bbase (se 4 (by rfl) ⟨21852, by rfl⟩ : syracuseStep 233093 = 43705) (by norm_num)
theorem B233117 : Blo 151794 233117 := bbase (se 3 (by rfl) ⟨43709, by rfl⟩ : syracuseStep 233117 = 87419) (by norm_num)
theorem B233141 : Blo 151794 233141 := bbase (se 5 (by rfl) ⟨10928, by rfl⟩ : syracuseStep 233141 = 21857) (by norm_num)
theorem B233165 : Blo 151794 233165 := bbase (se 3 (by rfl) ⟨43718, by rfl⟩ : syracuseStep 233165 = 87437) (by norm_num)
theorem B233189 : Blo 151794 233189 := bbase (se 4 (by rfl) ⟨21861, by rfl⟩ : syracuseStep 233189 = 43723) (by norm_num)
theorem B233213 : Blo 151794 233213 := bbase (se 3 (by rfl) ⟨43727, by rfl⟩ : syracuseStep 233213 = 87455) (by norm_num)
theorem B233237 : Blo 151794 233237 := bbase (se 6 (by rfl) ⟨5466, by rfl⟩ : syracuseStep 233237 = 10933) (by norm_num)
theorem B233261 : Blo 151794 233261 := bbase (se 3 (by rfl) ⟨43736, by rfl⟩ : syracuseStep 233261 = 87473) (by norm_num)
theorem B233285 : Blo 151794 233285 := bbase (se 4 (by rfl) ⟨21870, by rfl⟩ : syracuseStep 233285 = 43741) (by norm_num)
theorem B233309 : Blo 151794 233309 := bbase (se 3 (by rfl) ⟨43745, by rfl⟩ : syracuseStep 233309 = 87491) (by norm_num)
theorem B1118069 : Blo 151794 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B233333 : Blo 151794 233333 := bbase (se 5 (by rfl) ⟨10937, by rfl⟩ : syracuseStep 233333 = 21875) (by norm_num)
theorem B233357 : Blo 151794 233357 := bbase (se 3 (by rfl) ⟨43754, by rfl⟩ : syracuseStep 233357 = 87509) (by norm_num)
theorem B233381 : Blo 151794 233381 := bbase (se 4 (by rfl) ⟨21879, by rfl⟩ : syracuseStep 233381 = 43759) (by norm_num)
theorem B233405 : Blo 151794 233405 := bbase (se 3 (by rfl) ⟨43763, by rfl⟩ : syracuseStep 233405 = 87527) (by norm_num)
theorem B233429 : Blo 151794 233429 := bbase (se 7 (by rfl) ⟨2735, by rfl⟩ : syracuseStep 233429 = 5471) (by norm_num)
theorem B233453 : Blo 151794 233453 := bbase (se 3 (by rfl) ⟨43772, by rfl⟩ : syracuseStep 233453 = 87545) (by norm_num)
theorem B233477 : Blo 151794 233477 := bbase (se 4 (by rfl) ⟨21888, by rfl⟩ : syracuseStep 233477 = 43777) (by norm_num)
theorem B233501 : Blo 151794 233501 := bbase (se 3 (by rfl) ⟨43781, by rfl⟩ : syracuseStep 233501 = 87563) (by norm_num)
theorem B233525 : Blo 151794 233525 := bbase (se 5 (by rfl) ⟨10946, by rfl⟩ : syracuseStep 233525 = 21893) (by norm_num)
theorem B233549 : Blo 151794 233549 := bbase (se 3 (by rfl) ⟨43790, by rfl⟩ : syracuseStep 233549 = 87581) (by norm_num)
theorem B233573 : Blo 151794 233573 := bbase (se 4 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 233573 = 43795) (by norm_num)
theorem B233597 : Blo 151794 233597 := bbase (se 3 (by rfl) ⟨43799, by rfl⟩ : syracuseStep 233597 = 87599) (by norm_num)
theorem B233621 : Blo 151794 233621 := bbase (se 6 (by rfl) ⟨5475, by rfl⟩ : syracuseStep 233621 = 10951) (by norm_num)
theorem B233645 : Blo 151794 233645 := bbase (se 3 (by rfl) ⟨43808, by rfl⟩ : syracuseStep 233645 = 87617) (by norm_num)
theorem B233669 : Blo 151794 233669 := bbase (se 4 (by rfl) ⟨21906, by rfl⟩ : syracuseStep 233669 = 43813) (by norm_num)
theorem B332117 : Blo 151794 332117 := bbase (se 10 (by rfl) ⟨486, by rfl⟩ : syracuseStep 332117 = 973) (by norm_num)
theorem B364925 : Blo 151794 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B233861 : Blo 151794 233861 := bbase (se 4 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 233861 = 43849) (by norm_num)
theorem B1249717 : Blo 151794 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B233933 : Blo 151794 233933 := bbase (se 3 (by rfl) ⟨43862, by rfl⟩ : syracuseStep 233933 = 87725) (by norm_num)
theorem B332237 : Blo 151794 332237 := bbase (se 3 (by rfl) ⟨62294, by rfl⟩ : syracuseStep 332237 = 124589) (by norm_num)
theorem B496165 : Blo 151794 496165 := bbase (se 4 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 496165 = 93031) (by norm_num)
theorem B824021 : Blo 151794 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B168809 : Blo 151794 168809 := bbase (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) (by norm_num)
theorem B463973 : Blo 151794 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B791909 : Blo 151794 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B660869 : Blo 151794 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B988661 : Blo 151794 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B1316533 : Blo 151794 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B235229 : Blo 151794 235229 := bbase (se 3 (by rfl) ⟨44105, by rfl⟩ : syracuseStep 235229 = 88211) (by norm_num)
theorem B563221 : Blo 151794 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B497765 : Blo 151794 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B5445845 : Blo 151794 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B891157 : Blo 151794 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B661877 : Blo 151794 661877 := bbase (se 5 (by rfl) ⟨31025, by rfl⟩ : syracuseStep 661877 = 62051) (by norm_num)
theorem B498325 : Blo 151794 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B3185365 : Blo 151794 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B170797 : Blo 151794 170797 := bbase (se 3 (by rfl) ⟨32024, by rfl⟩ : syracuseStep 170797 = 64049) (by norm_num)
theorem B170833 : Blo 151794 170833 := bbase (se 2 (by rfl) ⟨64062, by rfl⟩ : syracuseStep 170833 = 128125) (by norm_num)
theorem B170869 : Blo 151794 170869 := bbase (se 5 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 170869 = 16019) (by norm_num)
theorem B170905 : Blo 151794 170905 := bbase (se 2 (by rfl) ⟨64089, by rfl⟩ : syracuseStep 170905 = 128179) (by norm_num)
theorem B170941 : Blo 151794 170941 := bbase (se 3 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 170941 = 64103) (by norm_num)
theorem B170977 : Blo 151794 170977 := bbase (se 2 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 170977 = 128233) (by norm_num)
theorem B171013 : Blo 151794 171013 := bbase (se 4 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 171013 = 32065) (by norm_num)
theorem B171049 : Blo 151794 171049 := bbase (se 2 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 171049 = 128287) (by norm_num)
theorem B1317941 : Blo 151794 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B171085 : Blo 151794 171085 := bbase (se 3 (by rfl) ⟨32078, by rfl⟩ : syracuseStep 171085 = 64157) (by norm_num)
theorem B171121 : Blo 151794 171121 := bbase (se 2 (by rfl) ⟨64170, by rfl⟩ : syracuseStep 171121 = 128341) (by norm_num)
theorem B171157 : Blo 151794 171157 := bbase (se 6 (by rfl) ⟨4011, by rfl⟩ : syracuseStep 171157 = 8023) (by norm_num)
theorem B236701 : Blo 151794 236701 := bbase (se 3 (by rfl) ⟨44381, by rfl⟩ : syracuseStep 236701 = 88763) (by norm_num)
theorem B335021 : Blo 151794 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B498869 : Blo 151794 498869 := bbase (se 5 (by rfl) ⟨23384, by rfl⟩ : syracuseStep 498869 = 46769) (by norm_num)
theorem B171193 : Blo 151794 171193 := bbase (se 2 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 171193 = 128395) (by norm_num)
theorem B171229 : Blo 151794 171229 := bbase (se 3 (by rfl) ⟨32105, by rfl⟩ : syracuseStep 171229 = 64211) (by norm_num)
theorem B466165 : Blo 151794 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B171265 : Blo 151794 171265 := bbase (se 2 (by rfl) ⟨64224, by rfl⟩ : syracuseStep 171265 = 128449) (by norm_num)
theorem B171301 : Blo 151794 171301 := bbase (se 4 (by rfl) ⟨16059, by rfl⟩ : syracuseStep 171301 = 32119) (by norm_num)
theorem B171337 : Blo 151794 171337 := bbase (se 2 (by rfl) ⟨64251, by rfl⟩ : syracuseStep 171337 = 128503) (by norm_num)
theorem B171373 : Blo 151794 171373 := bbase (se 3 (by rfl) ⟨32132, by rfl⟩ : syracuseStep 171373 = 64265) (by norm_num)
theorem B171409 : Blo 151794 171409 := bbase (se 2 (by rfl) ⟨64278, by rfl⟩ : syracuseStep 171409 = 128557) (by norm_num)
theorem B171433 : Blo 151794 171433 := bbase (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) (by norm_num)
theorem B171445 : Blo 151794 171445 := bbase (se 5 (by rfl) ⟨8036, by rfl⟩ : syracuseStep 171445 = 16073) (by norm_num)
theorem B368077 : Blo 151794 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B171481 : Blo 151794 171481 := bbase (se 2 (by rfl) ⟨64305, by rfl⟩ : syracuseStep 171481 = 128611) (by norm_num)
theorem B171517 : Blo 151794 171517 := bbase (se 3 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 171517 = 64319) (by norm_num)
theorem B171553 : Blo 151794 171553 := bbase (se 2 (by rfl) ⟨64332, by rfl⟩ : syracuseStep 171553 = 128665) (by norm_num)
theorem B171589 : Blo 151794 171589 := bbase (se 4 (by rfl) ⟨16086, by rfl⟩ : syracuseStep 171589 = 32173) (by norm_num)
theorem B171625 : Blo 151794 171625 := bbase (se 2 (by rfl) ⟨64359, by rfl⟩ : syracuseStep 171625 = 128719) (by norm_num)
theorem B171661 : Blo 151794 171661 := bbase (se 3 (by rfl) ⟨32186, by rfl⟩ : syracuseStep 171661 = 64373) (by norm_num)
theorem B171697 : Blo 151794 171697 := bbase (se 2 (by rfl) ⟨64386, by rfl⟩ : syracuseStep 171697 = 128773) (by norm_num)
theorem B171733 : Blo 151794 171733 := bbase (se 7 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 171733 = 4025) (by norm_num)
theorem B2989781 : Blo 151794 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B171769 : Blo 151794 171769 := bbase (se 2 (by rfl) ⟨64413, by rfl⟩ : syracuseStep 171769 = 128827) (by norm_num)
theorem B171805 : Blo 151794 171805 := bbase (se 3 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 171805 = 64427) (by norm_num)
theorem B171841 : Blo 151794 171841 := bbase (se 2 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 171841 = 128881) (by norm_num)
theorem B171877 : Blo 151794 171877 := bbase (se 4 (by rfl) ⟨16113, by rfl⟩ : syracuseStep 171877 = 32227) (by norm_num)
theorem B171913 : Blo 151794 171913 := bbase (se 2 (by rfl) ⟨64467, by rfl⟩ : syracuseStep 171913 = 128935) (by norm_num)
theorem B171949 : Blo 151794 171949 := bbase (se 3 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 171949 = 64481) (by norm_num)
theorem B171985 : Blo 151794 171985 := bbase (se 2 (by rfl) ⟨64494, by rfl⟩ : syracuseStep 171985 = 128989) (by norm_num)
theorem B172021 : Blo 151794 172021 := bbase (se 5 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 172021 = 16127) (by norm_num)
theorem B172057 : Blo 151794 172057 := bbase (se 2 (by rfl) ⟨64521, by rfl⟩ : syracuseStep 172057 = 129043) (by norm_num)
theorem B172093 : Blo 151794 172093 := bbase (se 3 (by rfl) ⟨32267, by rfl⟩ : syracuseStep 172093 = 64535) (by norm_num)
theorem B172129 : Blo 151794 172129 := bbase (se 2 (by rfl) ⟨64548, by rfl⟩ : syracuseStep 172129 = 129097) (by norm_num)
theorem B663653 : Blo 151794 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B368749 : Blo 151794 368749 := bbase (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) (by norm_num)
theorem B172165 : Blo 151794 172165 := bbase (se 4 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 172165 = 32281) (by norm_num)
theorem B1155221 : Blo 151794 1155221 := bbase (se 6 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 1155221 = 54151) (by norm_num)
theorem B172201 : Blo 151794 172201 := bbase (se 2 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 172201 = 129151) (by norm_num)
theorem B172237 : Blo 151794 172237 := bbase (se 3 (by rfl) ⟨32294, by rfl⟩ : syracuseStep 172237 = 64589) (by norm_num)
theorem B172273 : Blo 151794 172273 := bbase (se 2 (by rfl) ⟨64602, by rfl⟩ : syracuseStep 172273 = 129205) (by norm_num)
theorem B172309 : Blo 151794 172309 := bbase (se 6 (by rfl) ⟨4038, by rfl⟩ : syracuseStep 172309 = 8077) (by norm_num)
theorem B172345 : Blo 151794 172345 := bbase (se 2 (by rfl) ⟨64629, by rfl⟩ : syracuseStep 172345 = 129259) (by norm_num)
theorem B368981 : Blo 151794 368981 := bbase (se 10 (by rfl) ⟨540, by rfl⟩ : syracuseStep 368981 = 1081) (by norm_num)
theorem B172381 : Blo 151794 172381 := bbase (se 3 (by rfl) ⟨32321, by rfl⟩ : syracuseStep 172381 = 64643) (by norm_num)
theorem B827765 : Blo 151794 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B172417 : Blo 151794 172417 := bbase (se 2 (by rfl) ⟨64656, by rfl⟩ : syracuseStep 172417 = 129313) (by norm_num)
theorem B172453 : Blo 151794 172453 := bbase (se 4 (by rfl) ⟨16167, by rfl⟩ : syracuseStep 172453 = 32335) (by norm_num)
theorem B172489 : Blo 151794 172489 := bbase (se 2 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 172489 = 129367) (by norm_num)
theorem B369125 : Blo 151794 369125 := bbase (se 4 (by rfl) ⟨34605, by rfl⟩ : syracuseStep 369125 = 69211) (by norm_num)
theorem B172525 : Blo 151794 172525 := bbase (se 3 (by rfl) ⟨32348, by rfl⟩ : syracuseStep 172525 = 64697) (by norm_num)
theorem B172561 : Blo 151794 172561 := bbase (se 2 (by rfl) ⟨64710, by rfl⟩ : syracuseStep 172561 = 129421) (by norm_num)
theorem B369173 : Blo 151794 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B172597 : Blo 151794 172597 := bbase (se 5 (by rfl) ⟨8090, by rfl⟩ : syracuseStep 172597 = 16181) (by norm_num)
theorem B172633 : Blo 151794 172633 := bbase (se 2 (by rfl) ⟨64737, by rfl⟩ : syracuseStep 172633 = 129475) (by norm_num)
theorem B172669 : Blo 151794 172669 := bbase (se 3 (by rfl) ⟨32375, by rfl⟩ : syracuseStep 172669 = 64751) (by norm_num)
theorem B172705 : Blo 151794 172705 := bbase (se 2 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 172705 = 129529) (by norm_num)
theorem B172741 : Blo 151794 172741 := bbase (se 4 (by rfl) ⟨16194, by rfl⟩ : syracuseStep 172741 = 32389) (by norm_num)
theorem B172777 : Blo 151794 172777 := bbase (se 2 (by rfl) ⟨64791, by rfl⟩ : syracuseStep 172777 = 129583) (by norm_num)
theorem B172813 : Blo 151794 172813 := bbase (se 3 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 172813 = 64805) (by norm_num)
theorem B172849 : Blo 151794 172849 := bbase (se 2 (by rfl) ⟨64818, by rfl⟩ : syracuseStep 172849 = 129637) (by norm_num)
theorem B369461 : Blo 151794 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B172885 : Blo 151794 172885 := bbase (se 9 (by rfl) ⟨506, by rfl⟩ : syracuseStep 172885 = 1013) (by norm_num)
theorem B172921 : Blo 151794 172921 := bbase (se 2 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 172921 = 129691) (by norm_num)
theorem B435077 : Blo 151794 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B172957 : Blo 151794 172957 := bbase (se 3 (by rfl) ⟨32429, by rfl⟩ : syracuseStep 172957 = 64859) (by norm_num)
theorem B172993 : Blo 151794 172993 := bbase (se 2 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 172993 = 129745) (by norm_num)
theorem B173029 : Blo 151794 173029 := bbase (se 4 (by rfl) ⟨16221, by rfl⟩ : syracuseStep 173029 = 32443) (by norm_num)
theorem B173065 : Blo 151794 173065 := bbase (se 2 (by rfl) ⟨64899, by rfl⟩ : syracuseStep 173065 = 129799) (by norm_num)
theorem B173101 : Blo 151794 173101 := bbase (se 3 (by rfl) ⟨32456, by rfl⟩ : syracuseStep 173101 = 64913) (by norm_num)
theorem B173137 : Blo 151794 173137 := bbase (se 2 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 173137 = 129853) (by norm_num)
theorem B1647701 : Blo 151794 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B173173 : Blo 151794 173173 := bbase (se 5 (by rfl) ⟨8117, by rfl⟩ : syracuseStep 173173 = 16235) (by norm_num)
theorem B173209 : Blo 151794 173209 := bbase (se 2 (by rfl) ⟨64953, by rfl⟩ : syracuseStep 173209 = 129907) (by norm_num)
theorem B173245 : Blo 151794 173245 := bbase (se 3 (by rfl) ⟨32483, by rfl⟩ : syracuseStep 173245 = 64967) (by norm_num)
theorem B173281 : Blo 151794 173281 := bbase (se 2 (by rfl) ⟨64980, by rfl⟩ : syracuseStep 173281 = 129961) (by norm_num)
theorem B173317 : Blo 151794 173317 := bbase (se 4 (by rfl) ⟨16248, by rfl⟩ : syracuseStep 173317 = 32497) (by norm_num)
theorem B992533 : Blo 151794 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B173353 : Blo 151794 173353 := bbase (se 2 (by rfl) ⟨65007, by rfl⟩ : syracuseStep 173353 = 130015) (by norm_num)
theorem B173389 : Blo 151794 173389 := bbase (se 3 (by rfl) ⟨32510, by rfl⟩ : syracuseStep 173389 = 65021) (by norm_num)
theorem B173425 : Blo 151794 173425 := bbase (se 2 (by rfl) ⟨65034, by rfl⟩ : syracuseStep 173425 = 130069) (by norm_num)
theorem B173461 : Blo 151794 173461 := bbase (se 6 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 173461 = 8131) (by norm_num)
theorem B173497 : Blo 151794 173497 := bbase (se 2 (by rfl) ⟨65061, by rfl⟩ : syracuseStep 173497 = 130123) (by norm_num)
theorem B4793813 : Blo 151794 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B173533 : Blo 151794 173533 := bbase (se 3 (by rfl) ⟨32537, by rfl⟩ : syracuseStep 173533 = 65075) (by norm_num)
theorem B173569 : Blo 151794 173569 := bbase (se 2 (by rfl) ⟨65088, by rfl⟩ : syracuseStep 173569 = 130177) (by norm_num)
theorem B173605 : Blo 151794 173605 := bbase (se 4 (by rfl) ⟨16275, by rfl⟩ : syracuseStep 173605 = 32551) (by norm_num)
theorem B173641 : Blo 151794 173641 := bbase (se 2 (by rfl) ⟨65115, by rfl⟩ : syracuseStep 173641 = 130231) (by norm_num)
theorem B173677 : Blo 151794 173677 := bbase (se 3 (by rfl) ⟨32564, by rfl⟩ : syracuseStep 173677 = 65129) (by norm_num)
theorem B173713 : Blo 151794 173713 := bbase (se 2 (by rfl) ⟨65142, by rfl⟩ : syracuseStep 173713 = 130285) (by norm_num)
theorem B173749 : Blo 151794 173749 := bbase (se 5 (by rfl) ⟨8144, by rfl⟩ : syracuseStep 173749 = 16289) (by norm_num)
theorem B173785 : Blo 151794 173785 := bbase (se 2 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 173785 = 130339) (by norm_num)
theorem B173821 : Blo 151794 173821 := bbase (se 3 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 173821 = 65183) (by norm_num)
theorem B173857 : Blo 151794 173857 := bbase (se 2 (by rfl) ⟨65196, by rfl⟩ : syracuseStep 173857 = 130393) (by norm_num)
theorem B173893 : Blo 151794 173893 := bbase (se 4 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 173893 = 32605) (by norm_num)
theorem B173929 : Blo 151794 173929 := bbase (se 2 (by rfl) ⟨65223, by rfl⟩ : syracuseStep 173929 = 130447) (by norm_num)
theorem B173965 : Blo 151794 173965 := bbase (se 3 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 173965 = 65237) (by norm_num)
theorem B174001 : Blo 151794 174001 := bbase (se 2 (by rfl) ⟨65250, by rfl⟩ : syracuseStep 174001 = 130501) (by norm_num)
theorem B174037 : Blo 151794 174037 := bbase (se 7 (by rfl) ⟨2039, by rfl⟩ : syracuseStep 174037 = 4079) (by norm_num)
theorem B174073 : Blo 151794 174073 := bbase (se 2 (by rfl) ⟨65277, by rfl⟩ : syracuseStep 174073 = 130555) (by norm_num)
theorem B174109 : Blo 151794 174109 := bbase (se 3 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 174109 = 65291) (by norm_num)
theorem B436261 : Blo 151794 436261 := bbase (se 4 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 436261 = 81799) (by norm_num)
theorem B174145 : Blo 151794 174145 := bbase (se 2 (by rfl) ⟨65304, by rfl⟩ : syracuseStep 174145 = 130609) (by norm_num)
theorem B174181 : Blo 151794 174181 := bbase (se 4 (by rfl) ⟨16329, by rfl⟩ : syracuseStep 174181 = 32659) (by norm_num)
theorem B174217 : Blo 151794 174217 := bbase (se 2 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 174217 = 130663) (by norm_num)
theorem B469157 : Blo 151794 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B174253 : Blo 151794 174253 := bbase (se 3 (by rfl) ⟨32672, by rfl⟩ : syracuseStep 174253 = 65345) (by norm_num)
theorem B239789 : Blo 151794 239789 := bbase (se 3 (by rfl) ⟨44960, by rfl⟩ : syracuseStep 239789 = 89921) (by norm_num)
theorem B436421 : Blo 151794 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B174289 : Blo 151794 174289 := bbase (se 2 (by rfl) ⟨65358, by rfl⟩ : syracuseStep 174289 = 130717) (by norm_num)
theorem B174325 : Blo 151794 174325 := bbase (se 5 (by rfl) ⟨8171, by rfl⟩ : syracuseStep 174325 = 16343) (by norm_num)
theorem B174361 : Blo 151794 174361 := bbase (se 2 (by rfl) ⟨65385, by rfl⟩ : syracuseStep 174361 = 130771) (by norm_num)
theorem B174397 : Blo 151794 174397 := bbase (se 3 (by rfl) ⟨32699, by rfl⟩ : syracuseStep 174397 = 65399) (by norm_num)
theorem B174433 : Blo 151794 174433 := bbase (se 2 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 174433 = 130825) (by norm_num)
theorem B174469 : Blo 151794 174469 := bbase (se 4 (by rfl) ⟨16356, by rfl⟩ : syracuseStep 174469 = 32713) (by norm_num)
theorem B567685 : Blo 151794 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B174505 : Blo 151794 174505 := bbase (se 2 (by rfl) ⟨65439, by rfl⟩ : syracuseStep 174505 = 130879) (by norm_num)
theorem B436661 : Blo 151794 436661 := bbase (se 5 (by rfl) ⟨20468, by rfl⟩ : syracuseStep 436661 = 40937) (by norm_num)
theorem B502213 : Blo 151794 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B174541 : Blo 151794 174541 := bbase (se 3 (by rfl) ⟨32726, by rfl⟩ : syracuseStep 174541 = 65453) (by norm_num)
theorem B174577 : Blo 151794 174577 := bbase (se 2 (by rfl) ⟨65466, by rfl⟩ : syracuseStep 174577 = 130933) (by norm_num)
theorem B174613 : Blo 151794 174613 := bbase (se 6 (by rfl) ⟨4092, by rfl⟩ : syracuseStep 174613 = 8185) (by norm_num)
theorem B174649 : Blo 151794 174649 := bbase (se 2 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 174649 = 130987) (by norm_num)
theorem B174685 : Blo 151794 174685 := bbase (se 3 (by rfl) ⟨32753, by rfl⟩ : syracuseStep 174685 = 65507) (by norm_num)
theorem B436853 : Blo 151794 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B174721 : Blo 151794 174721 := bbase (se 2 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 174721 = 131041) (by norm_num)
theorem B174757 : Blo 151794 174757 := bbase (se 4 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 174757 = 32767) (by norm_num)
theorem B174793 : Blo 151794 174793 := bbase (se 2 (by rfl) ⟨65547, by rfl⟩ : syracuseStep 174793 = 131095) (by norm_num)
theorem B174829 : Blo 151794 174829 := bbase (se 3 (by rfl) ⟨32780, by rfl⟩ : syracuseStep 174829 = 65561) (by norm_num)
theorem B174865 : Blo 151794 174865 := bbase (se 2 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 174865 = 131149) (by norm_num)
theorem B469813 : Blo 151794 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B174901 : Blo 151794 174901 := bbase (se 5 (by rfl) ⟨8198, by rfl⟩ : syracuseStep 174901 = 16397) (by norm_num)
theorem B174937 : Blo 151794 174937 := bbase (se 2 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 174937 = 131203) (by norm_num)
theorem B174973 : Blo 151794 174973 := bbase (se 3 (by rfl) ⟨32807, by rfl⟩ : syracuseStep 174973 = 65615) (by norm_num)
theorem B175009 : Blo 151794 175009 := bbase (se 2 (by rfl) ⟨65628, by rfl⟩ : syracuseStep 175009 = 131257) (by norm_num)
theorem B175045 : Blo 151794 175045 := bbase (se 4 (by rfl) ⟨16410, by rfl⟩ : syracuseStep 175045 = 32821) (by norm_num)
theorem B175081 : Blo 151794 175081 := bbase (se 2 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 175081 = 131311) (by norm_num)
theorem B175117 : Blo 151794 175117 := bbase (se 3 (by rfl) ⟨32834, by rfl⟩ : syracuseStep 175117 = 65669) (by norm_num)
theorem B175153 : Blo 151794 175153 := bbase (se 2 (by rfl) ⟨65682, by rfl⟩ : syracuseStep 175153 = 131365) (by norm_num)
theorem B175189 : Blo 151794 175189 := bbase (se 8 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 175189 = 2053) (by norm_num)
theorem B207973 : Blo 151794 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B175225 : Blo 151794 175225 := bbase (se 2 (by rfl) ⟨65709, by rfl⟩ : syracuseStep 175225 = 131419) (by norm_num)
theorem B208013 : Blo 151794 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B175261 : Blo 151794 175261 := bbase (se 3 (by rfl) ⟨32861, by rfl⟩ : syracuseStep 175261 = 65723) (by norm_num)
theorem B371893 : Blo 151794 371893 := bbase (se 5 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 371893 = 34865) (by norm_num)
theorem B437845 : Blo 151794 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B372509 : Blo 151794 372509 := bbase (se 3 (by rfl) ⟨69845, by rfl⟩ : syracuseStep 372509 = 139691) (by norm_num)
theorem B372709 : Blo 151794 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B1323317 : Blo 151794 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B733637 : Blo 151794 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B1487413 : Blo 151794 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B275005 : Blo 151794 275005 := bbase (se 3 (by rfl) ⟨51563, by rfl⟩ : syracuseStep 275005 = 103127) (by norm_num)
theorem B438949 : Blo 151794 438949 := bbase (se 4 (by rfl) ⟨41151, by rfl⟩ : syracuseStep 438949 = 82303) (by norm_num)
theorem B373469 : Blo 151794 373469 := bbase (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) (by norm_num)
theorem B1487605 : Blo 151794 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B373517 : Blo 151794 373517 := bbase (se 3 (by rfl) ⟨70034, by rfl⟩ : syracuseStep 373517 = 140069) (by norm_num)
theorem B1979477 : Blo 151794 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B734309 : Blo 151794 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B537749 : Blo 151794 537749 := bbase (se 6 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 537749 = 25207) (by norm_num)
theorem B177385 : Blo 151794 177385 := bbase (se 2 (by rfl) ⟨66519, by rfl⟩ : syracuseStep 177385 = 133039) (by norm_num)
theorem B210157 : Blo 151794 210157 := bbase (se 3 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 210157 = 78809) (by norm_num)
theorem B177493 : Blo 151794 177493 := bbase (se 13 (by rfl) ⟨32, by rfl⟩ : syracuseStep 177493 = 65) (by norm_num)
theorem B275813 : Blo 151794 275813 := bbase (se 4 (by rfl) ⟨25857, by rfl⟩ : syracuseStep 275813 = 51715) (by norm_num)
theorem B308701 : Blo 151794 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B374285 : Blo 151794 374285 := bbase (se 3 (by rfl) ⟨70178, by rfl⟩ : syracuseStep 374285 = 140357) (by norm_num)
theorem B341549 : Blo 151794 341549 := bbase (se 3 (by rfl) ⟨64040, by rfl⟩ : syracuseStep 341549 = 128081) (by norm_num)
theorem B243245 : Blo 151794 243245 := bbase (se 3 (by rfl) ⟨45608, by rfl⟩ : syracuseStep 243245 = 91217) (by norm_num)
theorem B341621 : Blo 151794 341621 := bbase (se 5 (by rfl) ⟨16013, by rfl⟩ : syracuseStep 341621 = 32027) (by norm_num)
theorem B341693 : Blo 151794 341693 := bbase (se 3 (by rfl) ⟨64067, by rfl⟩ : syracuseStep 341693 = 128135) (by norm_num)
theorem B341765 : Blo 151794 341765 := bbase (se 4 (by rfl) ⟨32040, by rfl⟩ : syracuseStep 341765 = 64081) (by norm_num)
theorem B341837 : Blo 151794 341837 := bbase (se 3 (by rfl) ⟨64094, by rfl⟩ : syracuseStep 341837 = 128189) (by norm_num)
theorem B341909 : Blo 151794 341909 := bbase (se 6 (by rfl) ⟨8013, by rfl⟩ : syracuseStep 341909 = 16027) (by norm_num)
theorem B2537365 : Blo 151794 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B243629 : Blo 151794 243629 := bbase (se 3 (by rfl) ⟨45680, by rfl⟩ : syracuseStep 243629 = 91361) (by norm_num)
theorem B341981 : Blo 151794 341981 := bbase (se 3 (by rfl) ⟨64121, by rfl⟩ : syracuseStep 341981 = 128243) (by norm_num)
theorem B342053 : Blo 151794 342053 := bbase (se 4 (by rfl) ⟨32067, by rfl⟩ : syracuseStep 342053 = 64135) (by norm_num)
theorem B243757 : Blo 151794 243757 := bbase (se 3 (by rfl) ⟨45704, by rfl⟩ : syracuseStep 243757 = 91409) (by norm_num)
theorem B342125 : Blo 151794 342125 := bbase (se 3 (by rfl) ⟨64148, by rfl⟩ : syracuseStep 342125 = 128297) (by norm_num)
theorem B440453 : Blo 151794 440453 := bbase (se 4 (by rfl) ⟨41292, by rfl⟩ : syracuseStep 440453 = 82585) (by norm_num)
theorem B1947797 : Blo 151794 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B342197 : Blo 151794 342197 := bbase (se 5 (by rfl) ⟨16040, by rfl⟩ : syracuseStep 342197 = 32081) (by norm_num)
theorem B669941 : Blo 151794 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B342269 : Blo 151794 342269 := bbase (se 3 (by rfl) ⟨64175, by rfl⟩ : syracuseStep 342269 = 128351) (by norm_num)
theorem B899381 : Blo 151794 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B342341 : Blo 151794 342341 := bbase (se 4 (by rfl) ⟨32094, by rfl⟩ : syracuseStep 342341 = 64189) (by norm_num)
theorem B866645 : Blo 151794 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B342413 : Blo 151794 342413 := bbase (se 3 (by rfl) ⟨64202, by rfl⟩ : syracuseStep 342413 = 128405) (by norm_num)
theorem B342485 : Blo 151794 342485 := bbase (se 7 (by rfl) ⟨4013, by rfl⟩ : syracuseStep 342485 = 8027) (by norm_num)
theorem B342557 : Blo 151794 342557 := bbase (se 3 (by rfl) ⟨64229, by rfl⟩ : syracuseStep 342557 = 128459) (by norm_num)
theorem B342629 : Blo 151794 342629 := bbase (se 4 (by rfl) ⟨32121, by rfl⟩ : syracuseStep 342629 = 64243) (by norm_num)
theorem B342701 : Blo 151794 342701 := bbase (se 3 (by rfl) ⟨64256, by rfl⟩ : syracuseStep 342701 = 128513) (by norm_num)
theorem B342773 : Blo 151794 342773 := bbase (se 5 (by rfl) ⟨16067, by rfl⟩ : syracuseStep 342773 = 32135) (by norm_num)
theorem B342845 : Blo 151794 342845 := bbase (se 3 (by rfl) ⟨64283, by rfl⟩ : syracuseStep 342845 = 128567) (by norm_num)
theorem B342917 : Blo 151794 342917 := bbase (se 4 (by rfl) ⟨32148, by rfl⟩ : syracuseStep 342917 = 64297) (by norm_num)
theorem B342989 : Blo 151794 342989 := bbase (se 3 (by rfl) ⟨64310, by rfl⟩ : syracuseStep 342989 = 128621) (by norm_num)
theorem B769013 : Blo 151794 769013 := bbase (se 5 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 769013 = 72095) (by norm_num)
theorem B343061 : Blo 151794 343061 := bbase (se 6 (by rfl) ⟨8040, by rfl⟩ : syracuseStep 343061 = 16081) (by norm_num)
theorem B244757 : Blo 151794 244757 := bbase (se 6 (by rfl) ⟨5736, by rfl⟩ : syracuseStep 244757 = 11473) (by norm_num)
theorem B343133 : Blo 151794 343133 := bbase (se 3 (by rfl) ⟨64337, by rfl⟩ : syracuseStep 343133 = 128675) (by norm_num)
theorem B375925 : Blo 151794 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B244885 : Blo 151794 244885 := bbase (se 6 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 244885 = 11479) (by norm_num)
theorem B375965 : Blo 151794 375965 := bbase (se 3 (by rfl) ⟨70493, by rfl⟩ : syracuseStep 375965 = 140987) (by norm_num)
theorem B343205 : Blo 151794 343205 := bbase (se 4 (by rfl) ⟨32175, by rfl⟩ : syracuseStep 343205 = 64351) (by norm_num)
theorem B343277 : Blo 151794 343277 := bbase (se 3 (by rfl) ⟨64364, by rfl⟩ : syracuseStep 343277 = 128729) (by norm_num)
theorem B343349 : Blo 151794 343349 := bbase (se 5 (by rfl) ⟨16094, by rfl⟩ : syracuseStep 343349 = 32189) (by norm_num)
theorem B310613 : Blo 151794 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B343421 : Blo 151794 343421 := bbase (se 3 (by rfl) ⟨64391, by rfl⟩ : syracuseStep 343421 = 128783) (by norm_num)
theorem B343493 : Blo 151794 343493 := bbase (se 4 (by rfl) ⟨32202, by rfl⟩ : syracuseStep 343493 = 64405) (by norm_num)
theorem B277997 : Blo 151794 277997 := bbase (se 3 (by rfl) ⟨52124, by rfl⟩ : syracuseStep 277997 = 104249) (by norm_num)
theorem B343565 : Blo 151794 343565 := bbase (se 3 (by rfl) ⟨64418, by rfl⟩ : syracuseStep 343565 = 128837) (by norm_num)
theorem B245269 : Blo 151794 245269 := bbase (se 6 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 245269 = 11497) (by norm_num)
theorem B343637 : Blo 151794 343637 := bbase (se 8 (by rfl) ⟨2013, by rfl⟩ : syracuseStep 343637 = 4027) (by norm_num)
theorem B343709 : Blo 151794 343709 := bbase (se 3 (by rfl) ⟨64445, by rfl⟩ : syracuseStep 343709 = 128891) (by norm_num)
theorem B442037 : Blo 151794 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B343781 : Blo 151794 343781 := bbase (se 4 (by rfl) ⟨32229, by rfl⟩ : syracuseStep 343781 = 64459) (by norm_num)
theorem B1162997 : Blo 151794 1162997 := bbase (se 5 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 1162997 = 109031) (by norm_num)
theorem B245525 : Blo 151794 245525 := bbase (se 6 (by rfl) ⟨5754, by rfl⟩ : syracuseStep 245525 = 11509) (by norm_num)
theorem B343853 : Blo 151794 343853 := bbase (se 3 (by rfl) ⟨64472, by rfl⟩ : syracuseStep 343853 = 128945) (by norm_num)
theorem B343925 : Blo 151794 343925 := bbase (se 5 (by rfl) ⟨16121, by rfl⟩ : syracuseStep 343925 = 32243) (by norm_num)
theorem B343997 : Blo 151794 343997 := bbase (se 3 (by rfl) ⟨64499, by rfl⟩ : syracuseStep 343997 = 128999) (by norm_num)
theorem B344069 : Blo 151794 344069 := bbase (se 4 (by rfl) ⟨32256, by rfl⟩ : syracuseStep 344069 = 64513) (by norm_num)
theorem B278581 : Blo 151794 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B344141 : Blo 151794 344141 := bbase (se 3 (by rfl) ⟨64526, by rfl⟩ : syracuseStep 344141 = 129053) (by norm_num)
theorem B344213 : Blo 151794 344213 := bbase (se 6 (by rfl) ⟨8067, by rfl⟩ : syracuseStep 344213 = 16135) (by norm_num)
theorem B344285 : Blo 151794 344285 := bbase (se 3 (by rfl) ⟨64553, by rfl⟩ : syracuseStep 344285 = 129107) (by norm_num)
theorem B835829 : Blo 151794 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B770309 : Blo 151794 770309 := bbase (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) (by norm_num)
theorem B344357 : Blo 151794 344357 := bbase (se 4 (by rfl) ⟨32283, by rfl⟩ : syracuseStep 344357 = 64567) (by norm_num)
theorem B1589557 : Blo 151794 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442709 : Blo 151794 442709 := bbase (se 10 (by rfl) ⟨648, by rfl⟩ : syracuseStep 442709 = 1297) (by norm_num)
theorem B344429 : Blo 151794 344429 := bbase (se 3 (by rfl) ⟨64580, by rfl⟩ : syracuseStep 344429 = 129161) (by norm_num)
theorem B344501 : Blo 151794 344501 := bbase (se 5 (by rfl) ⟨16148, by rfl⟩ : syracuseStep 344501 = 32297) (by norm_num)
theorem B344573 : Blo 151794 344573 := bbase (se 3 (by rfl) ⟨64607, by rfl⟩ : syracuseStep 344573 = 129215) (by norm_num)
theorem B344645 : Blo 151794 344645 := bbase (se 4 (by rfl) ⟨32310, by rfl⟩ : syracuseStep 344645 = 64621) (by norm_num)
theorem B246397 : Blo 151794 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B344717 : Blo 151794 344717 := bbase (se 3 (by rfl) ⟨64634, by rfl⟩ : syracuseStep 344717 = 129269) (by norm_num)
theorem B344789 : Blo 151794 344789 := bbase (se 7 (by rfl) ⟨4040, by rfl⟩ : syracuseStep 344789 = 8081) (by norm_num)
theorem B246493 : Blo 151794 246493 := bbase (se 3 (by rfl) ⟨46217, by rfl⟩ : syracuseStep 246493 = 92435) (by norm_num)
theorem B443141 : Blo 151794 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B344861 : Blo 151794 344861 := bbase (se 3 (by rfl) ⟨64661, by rfl⟩ : syracuseStep 344861 = 129323) (by norm_num)
theorem B344933 : Blo 151794 344933 := bbase (se 4 (by rfl) ⟨32337, by rfl⟩ : syracuseStep 344933 = 64675) (by norm_num)
theorem B246653 : Blo 151794 246653 := bbase (se 3 (by rfl) ⟨46247, by rfl⟩ : syracuseStep 246653 = 92495) (by norm_num)
theorem B345005 : Blo 151794 345005 := bbase (se 3 (by rfl) ⟨64688, by rfl⟩ : syracuseStep 345005 = 129377) (by norm_num)
theorem B345077 : Blo 151794 345077 := bbase (se 5 (by rfl) ⟨16175, by rfl⟩ : syracuseStep 345077 = 32351) (by norm_num)
theorem B345149 : Blo 151794 345149 := bbase (se 3 (by rfl) ⟨64715, by rfl⟩ : syracuseStep 345149 = 129431) (by norm_num)
theorem B345221 : Blo 151794 345221 := bbase (se 4 (by rfl) ⟨32364, by rfl⟩ : syracuseStep 345221 = 64729) (by norm_num)
theorem B279749 : Blo 151794 279749 := bbase (se 4 (by rfl) ⟨26226, by rfl⟩ : syracuseStep 279749 = 52453) (by norm_num)
theorem B345293 : Blo 151794 345293 := bbase (se 3 (by rfl) ⟨64742, by rfl⟩ : syracuseStep 345293 = 129485) (by norm_num)
theorem B345365 : Blo 151794 345365 := bbase (se 6 (by rfl) ⟨8094, by rfl⟩ : syracuseStep 345365 = 16189) (by norm_num)
theorem B345437 : Blo 151794 345437 := bbase (se 3 (by rfl) ⟨64769, by rfl⟩ : syracuseStep 345437 = 129539) (by norm_num)
theorem B345509 : Blo 151794 345509 := bbase (se 4 (by rfl) ⟨32391, by rfl⟩ : syracuseStep 345509 = 64783) (by norm_num)
theorem B345581 : Blo 151794 345581 := bbase (se 3 (by rfl) ⟨64796, by rfl⟩ : syracuseStep 345581 = 129593) (by norm_num)
theorem B771605 : Blo 151794 771605 := bbase (se 6 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 771605 = 36169) (by norm_num)
theorem B345653 : Blo 151794 345653 := bbase (se 5 (by rfl) ⟨16202, by rfl⟩ : syracuseStep 345653 = 32405) (by norm_num)
theorem B345725 : Blo 151794 345725 := bbase (se 3 (by rfl) ⟨64823, by rfl⟩ : syracuseStep 345725 = 129647) (by norm_num)
theorem B280189 : Blo 151794 280189 := bbase (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) (by norm_num)
theorem B280253 : Blo 151794 280253 := bbase (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) (by norm_num)
theorem B345797 : Blo 151794 345797 := bbase (se 4 (by rfl) ⟨32418, by rfl⟩ : syracuseStep 345797 = 64837) (by norm_num)
theorem B345869 : Blo 151794 345869 := bbase (se 3 (by rfl) ⟨64850, by rfl⟩ : syracuseStep 345869 = 129701) (by norm_num)
theorem B345941 : Blo 151794 345941 := bbase (se 9 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 345941 = 2027) (by norm_num)
theorem B411493 : Blo 151794 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B346013 : Blo 151794 346013 := bbase (se 3 (by rfl) ⟨64877, by rfl⟩ : syracuseStep 346013 = 129755) (by norm_num)
theorem B280541 : Blo 151794 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B346085 : Blo 151794 346085 := bbase (se 4 (by rfl) ⟨32445, by rfl⟩ : syracuseStep 346085 = 64891) (by norm_num)
theorem B247781 : Blo 151794 247781 := bbase (se 4 (by rfl) ⟨23229, by rfl⟩ : syracuseStep 247781 = 46459) (by norm_num)
theorem B346157 : Blo 151794 346157 := bbase (se 3 (by rfl) ⟨64904, by rfl⟩ : syracuseStep 346157 = 129809) (by norm_num)
theorem B346229 : Blo 151794 346229 := bbase (se 5 (by rfl) ⟨16229, by rfl⟩ : syracuseStep 346229 = 32459) (by norm_num)
theorem B346301 : Blo 151794 346301 := bbase (se 3 (by rfl) ⟨64931, by rfl⟩ : syracuseStep 346301 = 129863) (by norm_num)
theorem B346373 : Blo 151794 346373 := bbase (se 4 (by rfl) ⟨32472, by rfl⟩ : syracuseStep 346373 = 64945) (by norm_num)
theorem B346445 : Blo 151794 346445 := bbase (se 3 (by rfl) ⟨64958, by rfl⟩ : syracuseStep 346445 = 129917) (by norm_num)
theorem B346517 : Blo 151794 346517 := bbase (se 6 (by rfl) ⟨8121, by rfl⟩ : syracuseStep 346517 = 16243) (by norm_num)
theorem B182741 : Blo 151794 182741 := bbase (se 7 (by rfl) ⟨2141, by rfl⟩ : syracuseStep 182741 = 4283) (by norm_num)
theorem B346589 : Blo 151794 346589 := bbase (se 3 (by rfl) ⟨64985, by rfl⟩ : syracuseStep 346589 = 129971) (by norm_num)
theorem B248293 : Blo 151794 248293 := bbase (se 4 (by rfl) ⟨23277, by rfl⟩ : syracuseStep 248293 = 46555) (by norm_num)
theorem B346661 : Blo 151794 346661 := bbase (se 4 (by rfl) ⟨32499, by rfl⟩ : syracuseStep 346661 = 64999) (by norm_num)
theorem B346733 : Blo 151794 346733 := bbase (se 3 (by rfl) ⟨65012, by rfl⟩ : syracuseStep 346733 = 130025) (by norm_num)
theorem B1493653 : Blo 151794 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B346805 : Blo 151794 346805 := bbase (se 5 (by rfl) ⟨16256, by rfl⟩ : syracuseStep 346805 = 32513) (by norm_num)
theorem B346877 : Blo 151794 346877 := bbase (se 3 (by rfl) ⟨65039, by rfl⟩ : syracuseStep 346877 = 130079) (by norm_num)
theorem B772901 : Blo 151794 772901 := bbase (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) (by norm_num)
theorem B281389 : Blo 151794 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B346949 : Blo 151794 346949 := bbase (se 4 (by rfl) ⟨32526, by rfl⟩ : syracuseStep 346949 = 65053) (by norm_num)
theorem B347021 : Blo 151794 347021 := bbase (se 3 (by rfl) ⟨65066, by rfl⟩ : syracuseStep 347021 = 130133) (by norm_num)
theorem B347093 : Blo 151794 347093 := bbase (se 7 (by rfl) ⟨4067, by rfl⟩ : syracuseStep 347093 = 8135) (by norm_num)
theorem B576517 : Blo 151794 576517 := bbase (se 4 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 576517 = 108097) (by norm_num)
theorem B347165 : Blo 151794 347165 := bbase (se 3 (by rfl) ⟨65093, by rfl⟩ : syracuseStep 347165 = 130187) (by norm_num)
theorem B347237 : Blo 151794 347237 := bbase (se 4 (by rfl) ⟨32553, by rfl⟩ : syracuseStep 347237 = 65107) (by norm_num)
theorem B183433 : Blo 151794 183433 := bbase (se 2 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 183433 = 137575) (by norm_num)
theorem B347309 : Blo 151794 347309 := bbase (se 3 (by rfl) ⟨65120, by rfl⟩ : syracuseStep 347309 = 130241) (by norm_num)
theorem B183529 : Blo 151794 183529 := bbase (se 2 (by rfl) ⟨68823, by rfl⟩ : syracuseStep 183529 = 137647) (by norm_num)
theorem B347381 : Blo 151794 347381 := bbase (se 5 (by rfl) ⟨16283, by rfl⟩ : syracuseStep 347381 = 32567) (by norm_num)
theorem B576821 : Blo 151794 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B347453 : Blo 151794 347453 := bbase (se 3 (by rfl) ⟨65147, by rfl⟩ : syracuseStep 347453 = 130295) (by norm_num)
theorem B1297781 : Blo 151794 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B216445 : Blo 151794 216445 := bbase (se 3 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 216445 = 81167) (by norm_num)
theorem B347525 : Blo 151794 347525 := bbase (se 4 (by rfl) ⟨32580, by rfl⟩ : syracuseStep 347525 = 65161) (by norm_num)
theorem B249293 : Blo 151794 249293 := bbase (se 3 (by rfl) ⟨46742, by rfl⟩ : syracuseStep 249293 = 93485) (by norm_num)
theorem B347597 : Blo 151794 347597 := bbase (se 3 (by rfl) ⟨65174, by rfl⟩ : syracuseStep 347597 = 130349) (by norm_num)
theorem B347669 : Blo 151794 347669 := bbase (se 6 (by rfl) ⟨8148, by rfl⟩ : syracuseStep 347669 = 16297) (by norm_num)
theorem B249421 : Blo 151794 249421 := bbase (se 3 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 249421 = 93533) (by norm_num)
theorem B347741 : Blo 151794 347741 := bbase (se 3 (by rfl) ⟨65201, by rfl⟩ : syracuseStep 347741 = 130403) (by norm_num)
theorem B183913 : Blo 151794 183913 := bbase (se 2 (by rfl) ⟨68967, by rfl⟩ : syracuseStep 183913 = 137935) (by norm_num)
theorem B249485 : Blo 151794 249485 := bbase (se 3 (by rfl) ⟨46778, by rfl⟩ : syracuseStep 249485 = 93557) (by norm_num)
theorem B347813 : Blo 151794 347813 := bbase (se 4 (by rfl) ⟨32607, by rfl⟩ : syracuseStep 347813 = 65215) (by norm_num)
theorem B249565 : Blo 151794 249565 := bbase (se 3 (by rfl) ⟨46793, by rfl⟩ : syracuseStep 249565 = 93587) (by norm_num)
theorem B347885 : Blo 151794 347885 := bbase (se 3 (by rfl) ⟨65228, by rfl⟩ : syracuseStep 347885 = 130457) (by norm_num)
theorem B347957 : Blo 151794 347957 := bbase (se 5 (by rfl) ⟨16310, by rfl⟩ : syracuseStep 347957 = 32621) (by norm_num)
theorem B348029 : Blo 151794 348029 := bbase (se 3 (by rfl) ⟨65255, by rfl⟩ : syracuseStep 348029 = 130511) (by norm_num)
theorem B348101 : Blo 151794 348101 := bbase (se 4 (by rfl) ⟨32634, by rfl⟩ : syracuseStep 348101 = 65269) (by norm_num)
theorem B217037 : Blo 151794 217037 := bbase (se 3 (by rfl) ⟨40694, by rfl⟩ : syracuseStep 217037 = 81389) (by norm_num)
theorem B937973 : Blo 151794 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B348173 : Blo 151794 348173 := bbase (se 3 (by rfl) ⟨65282, by rfl⟩ : syracuseStep 348173 = 130565) (by norm_num)
theorem B217117 : Blo 151794 217117 := bbase (se 3 (by rfl) ⟨40709, by rfl⟩ : syracuseStep 217117 = 81419) (by norm_num)
theorem B774197 : Blo 151794 774197 := bbase (se 5 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 774197 = 72581) (by norm_num)
theorem B348245 : Blo 151794 348245 := bbase (se 8 (by rfl) ⟨2040, by rfl⟩ : syracuseStep 348245 = 4081) (by norm_num)
theorem B217237 : Blo 151794 217237 := bbase (se 6 (by rfl) ⟨5091, by rfl⟩ : syracuseStep 217237 = 10183) (by norm_num)
theorem B348317 : Blo 151794 348317 := bbase (se 3 (by rfl) ⟨65309, by rfl⟩ : syracuseStep 348317 = 130619) (by norm_num)
theorem B315589 : Blo 151794 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B348389 : Blo 151794 348389 := bbase (se 4 (by rfl) ⟨32661, by rfl⟩ : syracuseStep 348389 = 65323) (by norm_num)
theorem B217333 : Blo 151794 217333 := bbase (se 5 (by rfl) ⟨10187, by rfl⟩ : syracuseStep 217333 = 20375) (by norm_num)
theorem B348461 : Blo 151794 348461 := bbase (se 3 (by rfl) ⟨65336, by rfl⟩ : syracuseStep 348461 = 130673) (by norm_num)
theorem B348533 : Blo 151794 348533 := bbase (se 5 (by rfl) ⟨16337, by rfl⟩ : syracuseStep 348533 = 32675) (by norm_num)
theorem B512405 : Blo 151794 512405 := bbase (se 6 (by rfl) ⟨12009, by rfl⟩ : syracuseStep 512405 = 24019) (by norm_num)
theorem B348565 : Blo 151794 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B348605 : Blo 151794 348605 := bbase (se 3 (by rfl) ⟨65363, by rfl⟩ : syracuseStep 348605 = 130727) (by norm_num)
theorem B348629 : Blo 151794 348629 := bbase (se 7 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 348629 = 8171) (by norm_num)
theorem B348677 : Blo 151794 348677 := bbase (se 4 (by rfl) ⟨32688, by rfl⟩ : syracuseStep 348677 = 65377) (by norm_num)
theorem B348749 : Blo 151794 348749 := bbase (se 3 (by rfl) ⟨65390, by rfl⟩ : syracuseStep 348749 = 130781) (by norm_num)
theorem B184961 : Blo 151794 184961 := bbase (se 2 (by rfl) ⟨69360, by rfl⟩ : syracuseStep 184961 = 138721) (by norm_num)
theorem B348821 : Blo 151794 348821 := bbase (se 6 (by rfl) ⟨8175, by rfl⟩ : syracuseStep 348821 = 16351) (by norm_num)
theorem B348893 : Blo 151794 348893 := bbase (se 3 (by rfl) ⟨65417, by rfl⟩ : syracuseStep 348893 = 130835) (by norm_num)
theorem B217829 : Blo 151794 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B348965 : Blo 151794 348965 := bbase (se 4 (by rfl) ⟨32715, by rfl⟩ : syracuseStep 348965 = 65431) (by norm_num)
theorem B512837 : Blo 151794 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B349037 : Blo 151794 349037 := bbase (se 3 (by rfl) ⟨65444, by rfl⟩ : syracuseStep 349037 = 130889) (by norm_num)
theorem B447365 : Blo 151794 447365 := bbase (se 4 (by rfl) ⟨41940, by rfl⟩ : syracuseStep 447365 = 83881) (by norm_num)
theorem B185269 : Blo 151794 185269 := bbase (se 5 (by rfl) ⟨8684, by rfl⟩ : syracuseStep 185269 = 17369) (by norm_num)
theorem B349109 : Blo 151794 349109 := bbase (se 5 (by rfl) ⟨16364, by rfl⟩ : syracuseStep 349109 = 32729) (by norm_num)
theorem B185297 : Blo 151794 185297 := bbase (se 2 (by rfl) ⟨69486, by rfl⟩ : syracuseStep 185297 = 138973) (by norm_num)
theorem B185333 : Blo 151794 185333 := bbase (se 5 (by rfl) ⟨8687, by rfl⟩ : syracuseStep 185333 = 17375) (by norm_num)
theorem B349181 : Blo 151794 349181 := bbase (se 3 (by rfl) ⟨65471, by rfl⟩ : syracuseStep 349181 = 130943) (by norm_num)
theorem B349253 : Blo 151794 349253 := bbase (se 4 (by rfl) ⟨32742, by rfl⟩ : syracuseStep 349253 = 65485) (by norm_num)
theorem B349325 : Blo 151794 349325 := bbase (se 3 (by rfl) ⟨65498, by rfl⟩ : syracuseStep 349325 = 130997) (by norm_num)
theorem B382133 : Blo 151794 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B349397 : Blo 151794 349397 := bbase (se 7 (by rfl) ⟨4094, by rfl⟩ : syracuseStep 349397 = 8189) (by norm_num)
theorem B513269 : Blo 151794 513269 := bbase (se 5 (by rfl) ⟨24059, by rfl⟩ : syracuseStep 513269 = 48119) (by norm_num)
theorem B218381 : Blo 151794 218381 := bbase (se 3 (by rfl) ⟨40946, by rfl⟩ : syracuseStep 218381 = 81893) (by norm_num)
theorem B349469 : Blo 151794 349469 := bbase (se 3 (by rfl) ⟨65525, by rfl⟩ : syracuseStep 349469 = 131051) (by norm_num)
theorem B775493 : Blo 151794 775493 := bbase (se 4 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 775493 = 145405) (by norm_num)
theorem B349541 : Blo 151794 349541 := bbase (se 4 (by rfl) ⟨32769, by rfl⟩ : syracuseStep 349541 = 65539) (by norm_num)
theorem B578933 : Blo 151794 578933 := bbase (se 5 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 578933 = 54275) (by norm_num)
theorem B349613 : Blo 151794 349613 := bbase (se 3 (by rfl) ⟨65552, by rfl⟩ : syracuseStep 349613 = 131105) (by norm_num)
theorem B185797 : Blo 151794 185797 := bbase (se 4 (by rfl) ⟨17418, by rfl⟩ : syracuseStep 185797 = 34837) (by norm_num)
theorem B349685 : Blo 151794 349685 := bbase (se 5 (by rfl) ⟨16391, by rfl⟩ : syracuseStep 349685 = 32783) (by norm_num)
theorem B153101 : Blo 151794 153101 := bbase (se 3 (by rfl) ⟨28706, by rfl⟩ : syracuseStep 153101 = 57413) (by norm_num)
theorem B349757 : Blo 151794 349757 := bbase (se 3 (by rfl) ⟨65579, by rfl⟩ : syracuseStep 349757 = 131159) (by norm_num)
theorem B349829 : Blo 151794 349829 := bbase (se 4 (by rfl) ⟨32796, by rfl⟩ : syracuseStep 349829 = 65593) (by norm_num)
theorem B579221 : Blo 151794 579221 := bbase (se 6 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 579221 = 27151) (by norm_num)
theorem B513701 : Blo 151794 513701 := bbase (se 4 (by rfl) ⟨48159, by rfl⟩ : syracuseStep 513701 = 96319) (by norm_num)
theorem B349901 : Blo 151794 349901 := bbase (se 3 (by rfl) ⟨65606, by rfl⟩ : syracuseStep 349901 = 131213) (by norm_num)
theorem B415493 : Blo 151794 415493 := bbase (se 4 (by rfl) ⟨38952, by rfl⟩ : syracuseStep 415493 = 77905) (by norm_num)
theorem B349973 : Blo 151794 349973 := bbase (se 6 (by rfl) ⟨8202, by rfl⟩ : syracuseStep 349973 = 16405) (by norm_num)
theorem B350045 : Blo 151794 350045 := bbase (se 3 (by rfl) ⟨65633, by rfl⟩ : syracuseStep 350045 = 131267) (by norm_num)
theorem B350117 : Blo 151794 350117 := bbase (se 4 (by rfl) ⟨32823, by rfl⟩ : syracuseStep 350117 = 65647) (by norm_num)
theorem B350189 : Blo 151794 350189 := bbase (se 3 (by rfl) ⟨65660, by rfl⟩ : syracuseStep 350189 = 131321) (by norm_num)
theorem B219133 : Blo 151794 219133 := bbase (se 3 (by rfl) ⟨41087, by rfl⟩ : syracuseStep 219133 = 82175) (by norm_num)
theorem B350261 : Blo 151794 350261 := bbase (se 5 (by rfl) ⟨16418, by rfl⟩ : syracuseStep 350261 = 32837) (by norm_num)
theorem B514133 : Blo 151794 514133 := bbase (se 8 (by rfl) ⟨3012, by rfl⟩ : syracuseStep 514133 = 6025) (by norm_num)
theorem B350333 : Blo 151794 350333 := bbase (se 3 (by rfl) ⟨65687, by rfl⟩ : syracuseStep 350333 = 131375) (by norm_num)
theorem B743573 : Blo 151794 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B350405 : Blo 151794 350405 := bbase (se 4 (by rfl) ⟨32850, by rfl⟩ : syracuseStep 350405 = 65701) (by norm_num)
theorem B874709 : Blo 151794 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B350477 : Blo 151794 350477 := bbase (se 3 (by rfl) ⟨65714, by rfl⟩ : syracuseStep 350477 = 131429) (by norm_num)
theorem B186769 : Blo 151794 186769 := bbase (se 2 (by rfl) ⟨70038, by rfl⟩ : syracuseStep 186769 = 140077) (by norm_num)
theorem B514565 : Blo 151794 514565 := bbase (se 4 (by rfl) ⟨48240, by rfl⟩ : syracuseStep 514565 = 96481) (by norm_num)
theorem B743957 : Blo 151794 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B776789 : Blo 151794 776789 := bbase (se 8 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 776789 = 9103) (by norm_num)
theorem B186985 : Blo 151794 186985 := bbase (se 2 (by rfl) ⟨70119, by rfl⟩ : syracuseStep 186985 = 140239) (by norm_num)
theorem B219925 : Blo 151794 219925 := bbase (se 6 (by rfl) ⟨5154, by rfl⟩ : syracuseStep 219925 = 10309) (by norm_num)
theorem B580405 : Blo 151794 580405 := bbase (se 5 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 580405 = 54413) (by norm_num)
theorem B187241 : Blo 151794 187241 := bbase (se 2 (by rfl) ⟨70215, by rfl⟩ : syracuseStep 187241 = 140431) (by norm_num)
theorem B514997 : Blo 151794 514997 := bbase (se 5 (by rfl) ⟨24140, by rfl⟩ : syracuseStep 514997 = 48281) (by norm_num)
theorem B580709 : Blo 151794 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B220261 : Blo 151794 220261 := bbase (se 4 (by rfl) ⟨20649, by rfl⟩ : syracuseStep 220261 = 41299) (by norm_num)
theorem B154829 : Blo 151794 154829 := bbase (se 3 (by rfl) ⟨29030, by rfl⟩ : syracuseStep 154829 = 58061) (by norm_num)
theorem B220477 : Blo 151794 220477 := bbase (se 3 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 220477 = 82679) (by norm_num)
theorem B1170773 : Blo 151794 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B515429 : Blo 151794 515429 := bbase (se 4 (by rfl) ⟨48321, by rfl⟩ : syracuseStep 515429 = 96643) (by norm_num)
theorem B384365 : Blo 151794 384365 := bbase (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) (by norm_num)
theorem B875893 : Blo 151794 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B155129 : Blo 151794 155129 := bbase (se 2 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 155129 = 116347) (by norm_num)
theorem B220853 : Blo 151794 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B384709 : Blo 151794 384709 := bbase (se 4 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 384709 = 72133) (by norm_num)
theorem B515861 : Blo 151794 515861 := bbase (se 6 (by rfl) ⟨12090, by rfl⟩ : syracuseStep 515861 = 24181) (by norm_num)
theorem B384821 : Blo 151794 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B778085 : Blo 151794 778085 := bbase (se 4 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 778085 = 145891) (by norm_num)
theorem B548741 : Blo 151794 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B385013 : Blo 151794 385013 := bbase (se 5 (by rfl) ⟨18047, by rfl⟩ : syracuseStep 385013 = 36095) (by norm_num)
theorem B155693 : Blo 151794 155693 := bbase (se 3 (by rfl) ⟨29192, by rfl⟩ : syracuseStep 155693 = 58385) (by norm_num)
theorem B155729 : Blo 151794 155729 := bbase (se 2 (by rfl) ⟨58398, by rfl⟩ : syracuseStep 155729 = 116797) (by norm_num)
theorem B516293 : Blo 151794 516293 := bbase (se 4 (by rfl) ⟨48402, by rfl⟩ : syracuseStep 516293 = 96805) (by norm_num)
theorem B385357 : Blo 151794 385357 := bbase (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) (by norm_num)
theorem B385469 : Blo 151794 385469 := bbase (se 3 (by rfl) ⟨72275, by rfl⟩ : syracuseStep 385469 = 144551) (by norm_num)
theorem B1237493 : Blo 151794 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B516725 : Blo 151794 516725 := bbase (se 5 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 516725 = 48443) (by norm_num)
theorem B385661 : Blo 151794 385661 := bbase (se 3 (by rfl) ⟨72311, by rfl⟩ : syracuseStep 385661 = 144623) (by norm_num)
theorem B189073 : Blo 151794 189073 := bbase (se 2 (by rfl) ⟨70902, by rfl⟩ : syracuseStep 189073 = 141805) (by norm_num)
theorem B189113 : Blo 151794 189113 := bbase (se 2 (by rfl) ⟨70917, by rfl⟩ : syracuseStep 189113 = 141835) (by norm_num)
theorem B975797 : Blo 151794 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B386005 : Blo 151794 386005 := bbase (se 7 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 386005 = 9047) (by norm_num)
theorem B517157 : Blo 151794 517157 := bbase (se 4 (by rfl) ⟨48483, by rfl⟩ : syracuseStep 517157 = 96967) (by norm_num)
theorem B386117 : Blo 151794 386117 := bbase (se 4 (by rfl) ⟨36198, by rfl⟩ : syracuseStep 386117 = 72397) (by norm_num)
theorem B779381 : Blo 151794 779381 := bbase (se 5 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 779381 = 73067) (by norm_num)
theorem B582821 : Blo 151794 582821 := bbase (se 4 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 582821 = 109279) (by norm_num)
theorem B189653 : Blo 151794 189653 := bbase (se 7 (by rfl) ⟨2222, by rfl⟩ : syracuseStep 189653 = 4445) (by norm_num)
theorem B386309 : Blo 151794 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B877877 : Blo 151794 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B386365 : Blo 151794 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B583109 : Blo 151794 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B517589 : Blo 151794 517589 := bbase (se 7 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 517589 = 12131) (by norm_num)
theorem B386653 : Blo 151794 386653 := bbase (se 3 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 386653 = 144995) (by norm_num)
theorem B288373 : Blo 151794 288373 := bbase (se 5 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 288373 = 27035) (by norm_num)
theorem B386765 : Blo 151794 386765 := bbase (se 3 (by rfl) ⟨72518, by rfl⟩ : syracuseStep 386765 = 145037) (by norm_num)
theorem B288517 : Blo 151794 288517 := bbase (se 4 (by rfl) ⟨27048, by rfl⟩ : syracuseStep 288517 = 54097) (by norm_num)
theorem B157541 : Blo 151794 157541 := bbase (se 4 (by rfl) ⟨14769, by rfl⟩ : syracuseStep 157541 = 29539) (by norm_num)
theorem B518021 : Blo 151794 518021 := bbase (se 4 (by rfl) ⟨48564, by rfl⟩ : syracuseStep 518021 = 97129) (by norm_num)
theorem B386957 : Blo 151794 386957 := bbase (se 3 (by rfl) ⟨72554, by rfl⟩ : syracuseStep 386957 = 145109) (by norm_num)
theorem B288677 : Blo 151794 288677 := bbase (se 4 (by rfl) ⟨27063, by rfl⟩ : syracuseStep 288677 = 54127) (by norm_num)
theorem B288821 : Blo 151794 288821 := bbase (se 5 (by rfl) ⟨13538, by rfl⟩ : syracuseStep 288821 = 27077) (by norm_num)
theorem B1730645 : Blo 151794 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B354397 : Blo 151794 354397 := bbase (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) (by norm_num)
theorem B911477 : Blo 151794 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B256189 : Blo 151794 256189 := bbase (se 3 (by rfl) ⟨48035, by rfl⟩ : syracuseStep 256189 = 96071) (by norm_num)
theorem B387301 : Blo 151794 387301 := bbase (se 4 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 387301 = 72619) (by norm_num)
theorem B256277 : Blo 151794 256277 := bbase (se 6 (by rfl) ⟨6006, by rfl⟩ : syracuseStep 256277 = 12013) (by norm_num)
theorem B518453 : Blo 151794 518453 := bbase (se 5 (by rfl) ⟨24302, by rfl⟩ : syracuseStep 518453 = 48605) (by norm_num)
theorem B289109 : Blo 151794 289109 := bbase (se 10 (by rfl) ⟨423, by rfl⟩ : syracuseStep 289109 = 847) (by norm_num)
theorem B387413 : Blo 151794 387413 := bbase (se 10 (by rfl) ⟨567, by rfl⟩ : syracuseStep 387413 = 1135) (by norm_num)
theorem B780677 : Blo 151794 780677 := bbase (se 4 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 780677 = 146377) (by norm_num)
theorem B256405 : Blo 151794 256405 := bbase (se 6 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 256405 = 12019) (by norm_num)
theorem B1173941 : Blo 151794 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B256493 : Blo 151794 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B289261 : Blo 151794 289261 := bbase (se 3 (by rfl) ⟨54236, by rfl⟩ : syracuseStep 289261 = 108473) (by norm_num)
theorem B387605 : Blo 151794 387605 := bbase (se 6 (by rfl) ⟨9084, by rfl⟩ : syracuseStep 387605 = 18169) (by norm_num)
theorem B584293 : Blo 151794 584293 := bbase (se 4 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 584293 = 109555) (by norm_num)
theorem B256621 : Blo 151794 256621 := bbase (se 3 (by rfl) ⟨48116, by rfl⟩ : syracuseStep 256621 = 96233) (by norm_num)
theorem B256709 : Blo 151794 256709 := bbase (se 4 (by rfl) ⟨24066, by rfl⟩ : syracuseStep 256709 = 48133) (by norm_num)
theorem B518885 : Blo 151794 518885 := bbase (se 4 (by rfl) ⟨48645, by rfl⟩ : syracuseStep 518885 = 97291) (by norm_num)
theorem B879349 : Blo 151794 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B289565 : Blo 151794 289565 := bbase (se 3 (by rfl) ⟨54293, by rfl⟩ : syracuseStep 289565 = 108587) (by norm_num)
theorem B256837 : Blo 151794 256837 := bbase (se 4 (by rfl) ⟨24078, by rfl⟩ : syracuseStep 256837 = 48157) (by norm_num)
theorem B387949 : Blo 151794 387949 := bbase (se 3 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 387949 = 145481) (by norm_num)
theorem B584597 : Blo 151794 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B256925 : Blo 151794 256925 := bbase (se 3 (by rfl) ⟨48173, by rfl⟩ : syracuseStep 256925 = 96347) (by norm_num)
theorem B388061 : Blo 151794 388061 := bbase (se 3 (by rfl) ⟨72761, by rfl⟩ : syracuseStep 388061 = 145523) (by norm_num)
theorem B257053 : Blo 151794 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B257141 : Blo 151794 257141 := bbase (se 5 (by rfl) ⟨12053, by rfl⟩ : syracuseStep 257141 = 24107) (by norm_num)
theorem B519317 : Blo 151794 519317 := bbase (se 6 (by rfl) ⟨12171, by rfl⟩ : syracuseStep 519317 = 24343) (by norm_num)
theorem B388253 : Blo 151794 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B257269 : Blo 151794 257269 := bbase (se 5 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 257269 = 24119) (by norm_num)
theorem B257357 : Blo 151794 257357 := bbase (se 3 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 257357 = 96509) (by norm_num)
theorem B585157 : Blo 151794 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B257485 : Blo 151794 257485 := bbase (se 3 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 257485 = 96557) (by norm_num)
theorem B880085 : Blo 151794 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B388597 : Blo 151794 388597 := bbase (se 5 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 388597 = 36431) (by norm_num)
theorem B290317 : Blo 151794 290317 := bbase (se 3 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 290317 = 108869) (by norm_num)
theorem B257573 : Blo 151794 257573 := bbase (se 4 (by rfl) ⟨24147, by rfl⟩ : syracuseStep 257573 = 48295) (by norm_num)
theorem B519749 : Blo 151794 519749 := bbase (se 4 (by rfl) ⟨48726, by rfl⟩ : syracuseStep 519749 = 97453) (by norm_num)
theorem B159301 : Blo 151794 159301 := bbase (se 4 (by rfl) ⟨14934, by rfl⟩ : syracuseStep 159301 = 29869) (by norm_num)
theorem B388709 : Blo 151794 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B781973 : Blo 151794 781973 := bbase (se 6 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 781973 = 36655) (by norm_num)
theorem B290461 : Blo 151794 290461 := bbase (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) (by norm_num)
theorem B257701 : Blo 151794 257701 := bbase (se 4 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 257701 = 48319) (by norm_num)
theorem B192233 : Blo 151794 192233 := bbase (se 2 (by rfl) ⟨72087, by rfl⟩ : syracuseStep 192233 = 144175) (by norm_num)
theorem B257789 : Blo 151794 257789 := bbase (se 3 (by rfl) ⟨48335, by rfl⟩ : syracuseStep 257789 = 96671) (by norm_num)
theorem B192289 : Blo 151794 192289 := bbase (se 2 (by rfl) ⟨72108, by rfl⟩ : syracuseStep 192289 = 144217) (by norm_num)
theorem B388901 : Blo 151794 388901 := bbase (se 4 (by rfl) ⟨36459, by rfl⟩ : syracuseStep 388901 = 72919) (by norm_num)
theorem B290621 : Blo 151794 290621 := bbase (se 3 (by rfl) ⟨54491, by rfl⟩ : syracuseStep 290621 = 108983) (by norm_num)
theorem B257917 : Blo 151794 257917 := bbase (se 3 (by rfl) ⟨48359, by rfl⟩ : syracuseStep 257917 = 96719) (by norm_num)
theorem B192385 : Blo 151794 192385 := bbase (se 2 (by rfl) ⟨72144, by rfl⟩ : syracuseStep 192385 = 144289) (by norm_num)
theorem B290765 : Blo 151794 290765 := bbase (se 3 (by rfl) ⟨54518, by rfl⟩ : syracuseStep 290765 = 109037) (by norm_num)
theorem B258005 : Blo 151794 258005 := bbase (se 7 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 258005 = 6047) (by norm_num)
theorem B520181 : Blo 151794 520181 := bbase (se 5 (by rfl) ⟨24383, by rfl⟩ : syracuseStep 520181 = 48767) (by norm_num)
theorem B192557 : Blo 151794 192557 := bbase (se 3 (by rfl) ⟨36104, by rfl⟩ : syracuseStep 192557 = 72209) (by norm_num)
theorem B2093141 : Blo 151794 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B258133 : Blo 151794 258133 := bbase (se 8 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 258133 = 3025) (by norm_num)
theorem B192613 : Blo 151794 192613 := bbase (se 4 (by rfl) ⟨18057, by rfl⟩ : syracuseStep 192613 = 36115) (by norm_num)
theorem B389245 : Blo 151794 389245 := bbase (se 3 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 389245 = 145967) (by norm_num)
theorem B258221 : Blo 151794 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B749749 : Blo 151794 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B192709 : Blo 151794 192709 := bbase (se 4 (by rfl) ⟨18066, by rfl⟩ : syracuseStep 192709 = 36133) (by norm_num)
theorem B291053 : Blo 151794 291053 := bbase (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) (by norm_num)
theorem B389357 : Blo 151794 389357 := bbase (se 3 (by rfl) ⟨73004, by rfl⟩ : syracuseStep 389357 = 146009) (by norm_num)
theorem B258349 : Blo 151794 258349 := bbase (se 3 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 258349 = 96881) (by norm_num)
theorem B192881 : Blo 151794 192881 := bbase (se 2 (by rfl) ⟨72330, by rfl⟩ : syracuseStep 192881 = 144661) (by norm_num)
theorem B258437 : Blo 151794 258437 := bbase (se 4 (by rfl) ⟨24228, by rfl⟩ : syracuseStep 258437 = 48457) (by norm_num)
theorem B291205 : Blo 151794 291205 := bbase (se 4 (by rfl) ⟨27300, by rfl⟩ : syracuseStep 291205 = 54601) (by norm_num)
theorem B520613 : Blo 151794 520613 := bbase (se 4 (by rfl) ⟨48807, by rfl⟩ : syracuseStep 520613 = 97615) (by norm_num)
theorem B192937 : Blo 151794 192937 := bbase (se 2 (by rfl) ⟨72351, by rfl⟩ : syracuseStep 192937 = 144703) (by norm_num)
theorem B389549 : Blo 151794 389549 := bbase (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) (by norm_num)
theorem B258565 : Blo 151794 258565 := bbase (se 4 (by rfl) ⟨24240, by rfl⟩ : syracuseStep 258565 = 48481) (by norm_num)
theorem B193033 : Blo 151794 193033 := bbase (se 2 (by rfl) ⟨72387, by rfl⟩ : syracuseStep 193033 = 144775) (by norm_num)
theorem B258653 : Blo 151794 258653 := bbase (se 3 (by rfl) ⟨48497, by rfl⟩ : syracuseStep 258653 = 96995) (by norm_num)
theorem B193205 : Blo 151794 193205 := bbase (se 5 (by rfl) ⟨9056, by rfl⟩ : syracuseStep 193205 = 18113) (by norm_num)
theorem B291509 : Blo 151794 291509 := bbase (se 5 (by rfl) ⟨13664, by rfl⟩ : syracuseStep 291509 = 27329) (by norm_num)
theorem B258781 : Blo 151794 258781 := bbase (se 3 (by rfl) ⟨48521, by rfl⟩ : syracuseStep 258781 = 97043) (by norm_num)
theorem B193261 : Blo 151794 193261 := bbase (se 3 (by rfl) ⟨36236, by rfl⟩ : syracuseStep 193261 = 72473) (by norm_num)
theorem B389893 : Blo 151794 389893 := bbase (se 4 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 389893 = 73105) (by norm_num)
theorem B258869 : Blo 151794 258869 := bbase (se 5 (by rfl) ⟨12134, by rfl⟩ : syracuseStep 258869 = 24269) (by norm_num)
theorem B193357 : Blo 151794 193357 := bbase (se 3 (by rfl) ⟨36254, by rfl⟩ : syracuseStep 193357 = 72509) (by norm_num)
theorem B521045 : Blo 151794 521045 := bbase (se 9 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 521045 = 3053) (by norm_num)
theorem B390005 : Blo 151794 390005 := bbase (se 5 (by rfl) ⟨18281, by rfl⟩ : syracuseStep 390005 = 36563) (by norm_num)
theorem B783269 : Blo 151794 783269 := bbase (se 4 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 783269 = 146863) (by norm_num)
theorem B258997 : Blo 151794 258997 := bbase (se 5 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 258997 = 24281) (by norm_num)
theorem B324557 : Blo 151794 324557 := bbase (se 3 (by rfl) ⟨60854, by rfl⟩ : syracuseStep 324557 = 121709) (by norm_num)
theorem B586709 : Blo 151794 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B193529 : Blo 151794 193529 := bbase (se 2 (by rfl) ⟨72573, by rfl⟩ : syracuseStep 193529 = 145147) (by norm_num)
theorem B259085 : Blo 151794 259085 := bbase (se 3 (by rfl) ⟨48578, by rfl⟩ : syracuseStep 259085 = 97157) (by norm_num)
theorem B193585 : Blo 151794 193585 := bbase (se 2 (by rfl) ⟨72594, by rfl⟩ : syracuseStep 193585 = 145189) (by norm_num)
theorem B390197 : Blo 151794 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B259213 : Blo 151794 259213 := bbase (se 3 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 259213 = 97205) (by norm_num)
theorem B193681 : Blo 151794 193681 := bbase (se 2 (by rfl) ⟨72630, by rfl⟩ : syracuseStep 193681 = 145261) (by norm_num)
theorem B259301 : Blo 151794 259301 := bbase (se 4 (by rfl) ⟨24309, by rfl⟩ : syracuseStep 259301 = 48619) (by norm_num)
theorem B488693 : Blo 151794 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B586997 : Blo 151794 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B521477 : Blo 151794 521477 := bbase (se 4 (by rfl) ⟨48888, by rfl⟩ : syracuseStep 521477 = 97777) (by norm_num)
theorem B193853 : Blo 151794 193853 := bbase (se 3 (by rfl) ⟨36347, by rfl⟩ : syracuseStep 193853 = 72695) (by norm_num)
theorem B259429 : Blo 151794 259429 := bbase (se 4 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 259429 = 48643) (by norm_num)
theorem B193909 : Blo 151794 193909 := bbase (se 5 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 193909 = 18179) (by norm_num)
theorem B390541 : Blo 151794 390541 := bbase (se 3 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 390541 = 146453) (by norm_num)
theorem B292261 : Blo 151794 292261 := bbase (se 4 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 292261 = 54799) (by norm_num)
theorem B259517 : Blo 151794 259517 := bbase (se 3 (by rfl) ⟨48659, by rfl⟩ : syracuseStep 259517 = 97319) (by norm_num)
theorem B194005 : Blo 151794 194005 := bbase (se 7 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 194005 = 4547) (by norm_num)
theorem B390653 : Blo 151794 390653 := bbase (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) (by norm_num)
theorem B652805 : Blo 151794 652805 := bbase (se 4 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 652805 = 122401) (by norm_num)
theorem B292405 : Blo 151794 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B259645 : Blo 151794 259645 := bbase (se 3 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 259645 = 97367) (by norm_num)
theorem B194177 : Blo 151794 194177 := bbase (se 2 (by rfl) ⟨72816, by rfl⟩ : syracuseStep 194177 = 145633) (by norm_num)
theorem B259733 : Blo 151794 259733 := bbase (se 6 (by rfl) ⟨6087, by rfl⟩ : syracuseStep 259733 = 12175) (by norm_num)
theorem B1111733 : Blo 151794 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B521909 : Blo 151794 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B194233 : Blo 151794 194233 := bbase (se 2 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 194233 = 145675) (by norm_num)
theorem B325309 : Blo 151794 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B390845 : Blo 151794 390845 := bbase (se 3 (by rfl) ⟨73283, by rfl⟩ : syracuseStep 390845 = 146567) (by norm_num)
theorem B292565 : Blo 151794 292565 := bbase (se 7 (by rfl) ⟨3428, by rfl⟩ : syracuseStep 292565 = 6857) (by norm_num)
theorem B259861 : Blo 151794 259861 := bbase (se 6 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 259861 = 12181) (by norm_num)
theorem B194329 : Blo 151794 194329 := bbase (se 2 (by rfl) ⟨72873, by rfl⟩ : syracuseStep 194329 = 145747) (by norm_num)
theorem B653093 : Blo 151794 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B161605 : Blo 151794 161605 := bbase (se 4 (by rfl) ⟨15150, by rfl⟩ : syracuseStep 161605 = 30301) (by norm_num)
theorem B325453 : Blo 151794 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B292709 : Blo 151794 292709 := bbase (se 4 (by rfl) ⟨27441, by rfl⟩ : syracuseStep 292709 = 54883) (by norm_num)
theorem B259949 : Blo 151794 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B194501 : Blo 151794 194501 := bbase (se 4 (by rfl) ⟨18234, by rfl⟩ : syracuseStep 194501 = 36469) (by norm_num)
theorem B260077 : Blo 151794 260077 := bbase (se 3 (by rfl) ⟨48764, by rfl⟩ : syracuseStep 260077 = 97529) (by norm_num)
theorem B194557 : Blo 151794 194557 := bbase (se 3 (by rfl) ⟨36479, by rfl⟩ : syracuseStep 194557 = 72959) (by norm_num)
theorem B391189 : Blo 151794 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B292925 : Blo 151794 292925 := bbase (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) (by norm_num)
theorem B292933 : Blo 151794 292933 := bbase (se 4 (by rfl) ⟨27462, by rfl⟩ : syracuseStep 292933 = 54925) (by norm_num)
theorem B260165 : Blo 151794 260165 := bbase (se 4 (by rfl) ⟨24390, by rfl⟩ : syracuseStep 260165 = 48781) (by norm_num)
theorem B194653 : Blo 151794 194653 := bbase (se 3 (by rfl) ⟨36497, by rfl⟩ : syracuseStep 194653 = 72995) (by norm_num)
theorem B522341 : Blo 151794 522341 := bbase (se 4 (by rfl) ⟨48969, by rfl⟩ : syracuseStep 522341 = 97939) (by norm_num)
theorem B292997 : Blo 151794 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B391301 : Blo 151794 391301 := bbase (se 4 (by rfl) ⟨36684, by rfl⟩ : syracuseStep 391301 = 73369) (by norm_num)
theorem B784565 : Blo 151794 784565 := bbase (se 5 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 784565 = 73553) (by norm_num)
theorem B325829 : Blo 151794 325829 := bbase (se 4 (by rfl) ⟨30546, by rfl⟩ : syracuseStep 325829 = 61093) (by norm_num)
theorem B260293 : Blo 151794 260293 := bbase (se 4 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 260293 = 48805) (by norm_num)
theorem B194825 : Blo 151794 194825 := bbase (se 2 (by rfl) ⟨73059, by rfl⟩ : syracuseStep 194825 = 146119) (by norm_num)
theorem B260381 : Blo 151794 260381 := bbase (se 3 (by rfl) ⟨48821, by rfl⟩ : syracuseStep 260381 = 97643) (by norm_num)
theorem B293149 : Blo 151794 293149 := bbase (se 3 (by rfl) ⟨54965, by rfl⟩ : syracuseStep 293149 = 109931) (by norm_num)
theorem B194881 : Blo 151794 194881 := bbase (se 2 (by rfl) ⟨73080, by rfl⟩ : syracuseStep 194881 = 146161) (by norm_num)
theorem B391493 : Blo 151794 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B227693 : Blo 151794 227693 := bbase (se 3 (by rfl) ⟨42692, by rfl⟩ : syracuseStep 227693 = 85385) (by norm_num)
theorem B227717 : Blo 151794 227717 := bbase (se 4 (by rfl) ⟨21348, by rfl⟩ : syracuseStep 227717 = 42697) (by norm_num)
theorem B588181 : Blo 151794 588181 := bbase (se 6 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 588181 = 27571) (by norm_num)
theorem B227741 : Blo 151794 227741 := bbase (se 3 (by rfl) ⟨42701, by rfl⟩ : syracuseStep 227741 = 85403) (by norm_num)
theorem B260509 : Blo 151794 260509 := bbase (se 3 (by rfl) ⟨48845, by rfl⟩ : syracuseStep 260509 = 97691) (by norm_num)
theorem B194977 : Blo 151794 194977 := bbase (se 2 (by rfl) ⟨73116, by rfl⟩ : syracuseStep 194977 = 146233) (by norm_num)
theorem B227765 : Blo 151794 227765 := bbase (se 5 (by rfl) ⟨10676, by rfl⟩ : syracuseStep 227765 = 21353) (by norm_num)
theorem B227789 : Blo 151794 227789 := bbase (se 3 (by rfl) ⟨42710, by rfl⟩ : syracuseStep 227789 = 85421) (by norm_num)
theorem B227813 : Blo 151794 227813 := bbase (se 4 (by rfl) ⟨21357, by rfl⟩ : syracuseStep 227813 = 42715) (by norm_num)
theorem B260597 : Blo 151794 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B227837 : Blo 151794 227837 := bbase (se 3 (by rfl) ⟨42719, by rfl⟩ : syracuseStep 227837 = 85439) (by norm_num)
theorem B227861 : Blo 151794 227861 := bbase (se 6 (by rfl) ⟨5340, by rfl⟩ : syracuseStep 227861 = 10681) (by norm_num)
theorem B653845 : Blo 151794 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B522773 : Blo 151794 522773 := bbase (se 6 (by rfl) ⟨12252, by rfl⟩ : syracuseStep 522773 = 24505) (by norm_num)
theorem B227885 : Blo 151794 227885 := bbase (se 3 (by rfl) ⟨42728, by rfl⟩ : syracuseStep 227885 = 85457) (by norm_num)
theorem B326197 : Blo 151794 326197 := bbase (se 5 (by rfl) ⟨15290, by rfl⟩ : syracuseStep 326197 = 30581) (by norm_num)
theorem B227909 : Blo 151794 227909 := bbase (se 4 (by rfl) ⟨21366, by rfl⟩ : syracuseStep 227909 = 42733) (by norm_num)
theorem B195149 : Blo 151794 195149 := bbase (se 3 (by rfl) ⟨36590, by rfl⟩ : syracuseStep 195149 = 73181) (by norm_num)
theorem B293453 : Blo 151794 293453 := bbase (se 3 (by rfl) ⟨55022, by rfl⟩ : syracuseStep 293453 = 110045) (by norm_num)
theorem B555605 : Blo 151794 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B227933 : Blo 151794 227933 := bbase (se 3 (by rfl) ⟨42737, by rfl⟩ : syracuseStep 227933 = 85475) (by norm_num)
theorem B227957 : Blo 151794 227957 := bbase (se 5 (by rfl) ⟨10685, by rfl⟩ : syracuseStep 227957 = 21371) (by norm_num)
theorem B260725 : Blo 151794 260725 := bbase (se 5 (by rfl) ⟨12221, by rfl⟩ : syracuseStep 260725 = 24443) (by norm_num)
theorem B195205 : Blo 151794 195205 := bbase (se 4 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 195205 = 36601) (by norm_num)
theorem B227981 : Blo 151794 227981 := bbase (se 3 (by rfl) ⟨42746, by rfl⟩ : syracuseStep 227981 = 85493) (by norm_num)
theorem B391837 : Blo 151794 391837 := bbase (se 3 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 391837 = 146939) (by norm_num)
theorem B228005 : Blo 151794 228005 := bbase (se 4 (by rfl) ⟨21375, by rfl⟩ : syracuseStep 228005 = 42751) (by norm_num)
theorem B228029 : Blo 151794 228029 := bbase (se 3 (by rfl) ⟨42755, by rfl⟩ : syracuseStep 228029 = 85511) (by norm_num)
theorem B588485 : Blo 151794 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B260813 : Blo 151794 260813 := bbase (se 3 (by rfl) ⟨48902, by rfl⟩ : syracuseStep 260813 = 97805) (by norm_num)
theorem B228053 : Blo 151794 228053 := bbase (se 7 (by rfl) ⟨2672, by rfl⟩ : syracuseStep 228053 = 5345) (by norm_num)
theorem B195301 : Blo 151794 195301 := bbase (se 4 (by rfl) ⟨18309, by rfl⟩ : syracuseStep 195301 = 36619) (by norm_num)
theorem B228077 : Blo 151794 228077 := bbase (se 3 (by rfl) ⟨42764, by rfl⟩ : syracuseStep 228077 = 85529) (by norm_num)
theorem B228101 : Blo 151794 228101 := bbase (se 4 (by rfl) ⟨21384, by rfl⟩ : syracuseStep 228101 = 42769) (by norm_num)
theorem B391949 : Blo 151794 391949 := bbase (se 3 (by rfl) ⟨73490, by rfl⟩ : syracuseStep 391949 = 146981) (by norm_num)
theorem B228125 : Blo 151794 228125 := bbase (se 3 (by rfl) ⟨42773, by rfl⟩ : syracuseStep 228125 = 85547) (by norm_num)
theorem B228149 : Blo 151794 228149 := bbase (se 5 (by rfl) ⟨10694, by rfl⟩ : syracuseStep 228149 = 21389) (by norm_num)
theorem B260941 : Blo 151794 260941 := bbase (se 3 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 260941 = 97853) (by norm_num)
theorem B228173 : Blo 151794 228173 := bbase (se 3 (by rfl) ⟨42782, by rfl⟩ : syracuseStep 228173 = 85565) (by norm_num)
theorem B228197 : Blo 151794 228197 := bbase (se 4 (by rfl) ⟨21393, by rfl⟩ : syracuseStep 228197 = 42787) (by norm_num)
theorem B228221 : Blo 151794 228221 := bbase (se 3 (by rfl) ⟨42791, by rfl⟩ : syracuseStep 228221 = 85583) (by norm_num)
theorem B195473 : Blo 151794 195473 := bbase (se 2 (by rfl) ⟨73302, by rfl⟩ : syracuseStep 195473 = 146605) (by norm_num)
theorem B228245 : Blo 151794 228245 := bbase (se 6 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 228245 = 10699) (by norm_num)
theorem B261029 : Blo 151794 261029 := bbase (se 4 (by rfl) ⟨24471, by rfl⟩ : syracuseStep 261029 = 48943) (by norm_num)
theorem B228269 : Blo 151794 228269 := bbase (se 3 (by rfl) ⟨42800, by rfl⟩ : syracuseStep 228269 = 85601) (by norm_num)
theorem B1178549 : Blo 151794 1178549 := bbase (se 5 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 1178549 = 110489) (by norm_num)
theorem B228293 : Blo 151794 228293 := bbase (se 4 (by rfl) ⟨21402, by rfl⟩ : syracuseStep 228293 = 42805) (by norm_num)
theorem B162757 : Blo 151794 162757 := bbase (se 4 (by rfl) ⟨15258, by rfl⟩ : syracuseStep 162757 = 30517) (by norm_num)
theorem B523205 : Blo 151794 523205 := bbase (se 4 (by rfl) ⟨49050, by rfl⟩ : syracuseStep 523205 = 98101) (by norm_num)
theorem B195529 : Blo 151794 195529 := bbase (se 2 (by rfl) ⟨73323, by rfl⟩ : syracuseStep 195529 = 146647) (by norm_num)
theorem B392141 : Blo 151794 392141 := bbase (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) (by norm_num)
theorem B228317 : Blo 151794 228317 := bbase (se 3 (by rfl) ⟨42809, by rfl⟩ : syracuseStep 228317 = 85619) (by norm_num)
theorem B228341 : Blo 151794 228341 := bbase (se 5 (by rfl) ⟨10703, by rfl⟩ : syracuseStep 228341 = 21407) (by norm_num)
theorem B228365 : Blo 151794 228365 := bbase (se 3 (by rfl) ⟨42818, by rfl⟩ : syracuseStep 228365 = 85637) (by norm_num)
theorem B162829 : Blo 151794 162829 := bbase (se 3 (by rfl) ⟨30530, by rfl⟩ : syracuseStep 162829 = 61061) (by norm_num)
theorem B293917 : Blo 151794 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B228389 : Blo 151794 228389 := bbase (se 4 (by rfl) ⟨21411, by rfl⟩ : syracuseStep 228389 = 42823) (by norm_num)
theorem B261157 : Blo 151794 261157 := bbase (se 4 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 261157 = 48967) (by norm_num)
theorem B195625 : Blo 151794 195625 := bbase (se 2 (by rfl) ⟨73359, by rfl⟩ : syracuseStep 195625 = 146719) (by norm_num)
theorem B228413 : Blo 151794 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B228437 : Blo 151794 228437 := bbase (se 8 (by rfl) ⟨1338, by rfl⟩ : syracuseStep 228437 = 2677) (by norm_num)
theorem B228461 : Blo 151794 228461 := bbase (se 3 (by rfl) ⟨42836, by rfl⟩ : syracuseStep 228461 = 85673) (by norm_num)
theorem B261245 : Blo 151794 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B228485 : Blo 151794 228485 := bbase (se 4 (by rfl) ⟨21420, by rfl⟩ : syracuseStep 228485 = 42841) (by norm_num)
theorem B228509 : Blo 151794 228509 := bbase (se 3 (by rfl) ⟨42845, by rfl⟩ : syracuseStep 228509 = 85691) (by norm_num)
theorem B228533 : Blo 151794 228533 := bbase (se 5 (by rfl) ⟨10712, by rfl⟩ : syracuseStep 228533 = 21425) (by norm_num)
theorem B1309877 : Blo 151794 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B163009 : Blo 151794 163009 := bbase (se 2 (by rfl) ⟨61128, by rfl⟩ : syracuseStep 163009 = 122257) (by norm_num)
theorem B228557 : Blo 151794 228557 := bbase (se 3 (by rfl) ⟨42854, by rfl⟩ : syracuseStep 228557 = 85709) (by norm_num)
theorem B195797 : Blo 151794 195797 := bbase (se 7 (by rfl) ⟨2294, by rfl⟩ : syracuseStep 195797 = 4589) (by norm_num)
theorem B228581 : Blo 151794 228581 := bbase (se 4 (by rfl) ⟨21429, by rfl⟩ : syracuseStep 228581 = 42859) (by norm_num)
theorem B654581 : Blo 151794 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B228605 : Blo 151794 228605 := bbase (se 3 (by rfl) ⟨42863, by rfl⟩ : syracuseStep 228605 = 85727) (by norm_num)
theorem B261373 : Blo 151794 261373 := bbase (se 3 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 261373 = 98015) (by norm_num)
theorem B195853 : Blo 151794 195853 := bbase (se 3 (by rfl) ⟨36722, by rfl⟩ : syracuseStep 195853 = 73445) (by norm_num)
theorem B228629 : Blo 151794 228629 := bbase (se 6 (by rfl) ⟨5358, by rfl⟩ : syracuseStep 228629 = 10717) (by norm_num)
theorem B392485 : Blo 151794 392485 := bbase (se 4 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 392485 = 73591) (by norm_num)
theorem B228653 : Blo 151794 228653 := bbase (se 3 (by rfl) ⟨42872, by rfl⟩ : syracuseStep 228653 = 85745) (by norm_num)
theorem B294205 : Blo 151794 294205 := bbase (se 3 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 294205 = 110327) (by norm_num)
theorem B228677 : Blo 151794 228677 := bbase (se 4 (by rfl) ⟨21438, by rfl⟩ : syracuseStep 228677 = 42877) (by norm_num)
theorem B261461 : Blo 151794 261461 := bbase (se 11 (by rfl) ⟨191, by rfl⟩ : syracuseStep 261461 = 383) (by norm_num)
theorem B228701 : Blo 151794 228701 := bbase (se 3 (by rfl) ⟨42881, by rfl⟩ : syracuseStep 228701 = 85763) (by norm_num)
theorem B195949 : Blo 151794 195949 := bbase (se 3 (by rfl) ⟨36740, by rfl⟩ : syracuseStep 195949 = 73481) (by norm_num)
theorem B228725 : Blo 151794 228725 := bbase (se 5 (by rfl) ⟨10721, by rfl⟩ : syracuseStep 228725 = 21443) (by norm_num)
theorem B523637 : Blo 151794 523637 := bbase (se 5 (by rfl) ⟨24545, by rfl⟩ : syracuseStep 523637 = 49091) (by norm_num)
theorem B228749 : Blo 151794 228749 := bbase (se 3 (by rfl) ⟨42890, by rfl⟩ : syracuseStep 228749 = 85781) (by norm_num)
theorem B392597 : Blo 151794 392597 := bbase (se 6 (by rfl) ⟨9201, by rfl⟩ : syracuseStep 392597 = 18403) (by norm_num)
theorem B228773 : Blo 151794 228773 := bbase (se 4 (by rfl) ⟨21447, by rfl⟩ : syracuseStep 228773 = 42895) (by norm_num)
theorem B228797 : Blo 151794 228797 := bbase (se 3 (by rfl) ⟨42899, by rfl⟩ : syracuseStep 228797 = 85799) (by norm_num)
theorem B785861 : Blo 151794 785861 := bbase (se 4 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 785861 = 147349) (by norm_num)
theorem B294349 : Blo 151794 294349 := bbase (se 3 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 294349 = 110381) (by norm_num)
theorem B228821 : Blo 151794 228821 := bbase (se 7 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 228821 = 5363) (by norm_num)
theorem B261589 : Blo 151794 261589 := bbase (se 7 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 261589 = 6131) (by norm_num)
theorem B228845 : Blo 151794 228845 := bbase (se 3 (by rfl) ⟨42908, by rfl⟩ : syracuseStep 228845 = 85817) (by norm_num)
theorem B228869 : Blo 151794 228869 := bbase (se 4 (by rfl) ⟨21456, by rfl⟩ : syracuseStep 228869 = 42913) (by norm_num)
theorem B2227733 : Blo 151794 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B196121 : Blo 151794 196121 := bbase (se 2 (by rfl) ⟨73545, by rfl⟩ : syracuseStep 196121 = 147091) (by norm_num)
theorem B228893 : Blo 151794 228893 := bbase (se 3 (by rfl) ⟨42917, by rfl⟩ : syracuseStep 228893 = 85835) (by norm_num)
theorem B261677 : Blo 151794 261677 := bbase (se 3 (by rfl) ⟨49064, by rfl⟩ : syracuseStep 261677 = 98129) (by norm_num)
theorem B228917 : Blo 151794 228917 := bbase (se 5 (by rfl) ⟨10730, by rfl⟩ : syracuseStep 228917 = 21461) (by norm_num)
theorem B1408565 : Blo 151794 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B228941 : Blo 151794 228941 := bbase (se 3 (by rfl) ⟨42926, by rfl⟩ : syracuseStep 228941 = 85853) (by norm_num)
theorem B196177 : Blo 151794 196177 := bbase (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) (by norm_num)
theorem B392789 : Blo 151794 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B228965 : Blo 151794 228965 := bbase (se 4 (by rfl) ⟨21465, by rfl⟩ : syracuseStep 228965 = 42931) (by norm_num)
theorem B294509 : Blo 151794 294509 := bbase (se 3 (by rfl) ⟨55220, by rfl⟩ : syracuseStep 294509 = 110441) (by norm_num)
theorem B228989 : Blo 151794 228989 := bbase (se 3 (by rfl) ⟨42935, by rfl⟩ : syracuseStep 228989 = 85871) (by norm_num)
theorem B163453 : Blo 151794 163453 := bbase (se 3 (by rfl) ⟨30647, by rfl⟩ : syracuseStep 163453 = 61295) (by norm_num)
theorem B229013 : Blo 151794 229013 := bbase (se 6 (by rfl) ⟨5367, by rfl⟩ : syracuseStep 229013 = 10735) (by norm_num)
theorem B229037 : Blo 151794 229037 := bbase (se 3 (by rfl) ⟨42944, by rfl⟩ : syracuseStep 229037 = 85889) (by norm_num)
theorem B261805 : Blo 151794 261805 := bbase (se 3 (by rfl) ⟨49088, by rfl⟩ : syracuseStep 261805 = 98177) (by norm_num)
theorem B196273 : Blo 151794 196273 := bbase (se 2 (by rfl) ⟨73602, by rfl⟩ : syracuseStep 196273 = 147205) (by norm_num)
theorem B229061 : Blo 151794 229061 := bbase (se 4 (by rfl) ⟨21474, by rfl⟩ : syracuseStep 229061 = 42949) (by norm_num)
theorem B229085 : Blo 151794 229085 := bbase (se 3 (by rfl) ⟨42953, by rfl⟩ : syracuseStep 229085 = 85907) (by norm_num)
theorem B229109 : Blo 151794 229109 := bbase (se 5 (by rfl) ⟨10739, by rfl⟩ : syracuseStep 229109 = 21479) (by norm_num)
theorem B163577 : Blo 151794 163577 := bbase (se 2 (by rfl) ⟨61341, by rfl⟩ : syracuseStep 163577 = 122683) (by norm_num)
theorem B294653 : Blo 151794 294653 := bbase (se 3 (by rfl) ⟨55247, by rfl⟩ : syracuseStep 294653 = 110495) (by norm_num)
theorem B261893 : Blo 151794 261893 := bbase (se 4 (by rfl) ⟨24552, by rfl⟩ : syracuseStep 261893 = 49105) (by norm_num)
theorem B229133 : Blo 151794 229133 := bbase (se 3 (by rfl) ⟨42962, by rfl⟩ : syracuseStep 229133 = 85925) (by norm_num)
theorem B229157 : Blo 151794 229157 := bbase (se 4 (by rfl) ⟨21483, by rfl⟩ : syracuseStep 229157 = 42967) (by norm_num)
theorem B524069 : Blo 151794 524069 := bbase (se 4 (by rfl) ⟨49131, by rfl⟩ : syracuseStep 524069 = 98263) (by norm_num)
theorem B229181 : Blo 151794 229181 := bbase (se 3 (by rfl) ⟨42971, by rfl⟩ : syracuseStep 229181 = 85943) (by norm_num)
theorem B1408853 : Blo 151794 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B229205 : Blo 151794 229205 := bbase (se 9 (by rfl) ⟨671, by rfl⟩ : syracuseStep 229205 = 1343) (by norm_num)
theorem B196445 : Blo 151794 196445 := bbase (se 3 (by rfl) ⟨36833, by rfl⟩ : syracuseStep 196445 = 73667) (by norm_num)
theorem B229229 : Blo 151794 229229 := bbase (se 3 (by rfl) ⟨42980, by rfl⟩ : syracuseStep 229229 = 85961) (by norm_num)
theorem B229253 : Blo 151794 229253 := bbase (se 4 (by rfl) ⟨21492, by rfl⟩ : syracuseStep 229253 = 42985) (by norm_num)
theorem B262021 : Blo 151794 262021 := bbase (se 4 (by rfl) ⟨24564, by rfl⟩ : syracuseStep 262021 = 49129) (by norm_num)
theorem B196501 : Blo 151794 196501 := bbase (se 6 (by rfl) ⟨4605, by rfl⟩ : syracuseStep 196501 = 9211) (by norm_num)
theorem B229277 : Blo 151794 229277 := bbase (se 3 (by rfl) ⟨42989, by rfl⟩ : syracuseStep 229277 = 85979) (by norm_num)
theorem B393133 : Blo 151794 393133 := bbase (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) (by norm_num)
theorem B229301 : Blo 151794 229301 := bbase (se 5 (by rfl) ⟨10748, by rfl⟩ : syracuseStep 229301 = 21497) (by norm_num)
theorem B229325 : Blo 151794 229325 := bbase (se 3 (by rfl) ⟨42998, by rfl⟩ : syracuseStep 229325 = 85997) (by norm_num)
theorem B262109 : Blo 151794 262109 := bbase (se 3 (by rfl) ⟨49145, by rfl⟩ : syracuseStep 262109 = 98291) (by norm_num)
theorem B229349 : Blo 151794 229349 := bbase (se 4 (by rfl) ⟨21501, by rfl⟩ : syracuseStep 229349 = 43003) (by norm_num)
theorem B163829 : Blo 151794 163829 := bbase (se 5 (by rfl) ⟨7679, by rfl⟩ : syracuseStep 163829 = 15359) (by norm_num)
theorem B557045 : Blo 151794 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B196597 : Blo 151794 196597 := bbase (se 5 (by rfl) ⟨9215, by rfl⟩ : syracuseStep 196597 = 18431) (by norm_num)
theorem B229373 : Blo 151794 229373 := bbase (se 3 (by rfl) ⟨43007, by rfl⟩ : syracuseStep 229373 = 86015) (by norm_num)
theorem B229379 : Blo 151794 229379 := bstep (se 1 (by rfl) ⟨172034, by rfl⟩ : syracuseStep 229379 = 344069) B344069
theorem B262163 : Blo 151794 262163 := bstep (se 1 (by rfl) ⟨196622, by rfl⟩ : syracuseStep 262163 = 393245) B393245
theorem B229409 : Blo 151794 229409 := bstep (se 2 (by rfl) ⟨86028, by rfl⟩ : syracuseStep 229409 = 172057) B172057
theorem B229427 : Blo 151794 229427 := bstep (se 1 (by rfl) ⟨172070, by rfl⟩ : syracuseStep 229427 = 344141) B344141
theorem B786509 : Blo 151794 786509 := bstep (se 3 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 786509 = 294941) B294941
theorem B229457 : Blo 151794 229457 := bstep (se 2 (by rfl) ⟨86046, by rfl⟩ : syracuseStep 229457 = 172093) B172093
theorem B229475 : Blo 151794 229475 := bstep (se 1 (by rfl) ⟨172106, by rfl⟩ : syracuseStep 229475 = 344213) B344213
theorem B229505 : Blo 151794 229505 := bstep (se 2 (by rfl) ⟨86064, by rfl⟩ : syracuseStep 229505 = 172129) B172129
theorem B491665 : Blo 151794 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B229523 : Blo 151794 229523 := bstep (se 1 (by rfl) ⟨172142, by rfl⟩ : syracuseStep 229523 = 344285) B344285
theorem B262291 : Blo 151794 262291 := bstep (se 1 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 262291 = 393437) B393437
theorem B557219 : Blo 151794 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B229553 : Blo 151794 229553 := bstep (se 2 (by rfl) ⟨86082, by rfl⟩ : syracuseStep 229553 = 172165) B172165
theorem B229571 : Blo 151794 229571 := bstep (se 1 (by rfl) ⟨172178, by rfl⟩ : syracuseStep 229571 = 344357) B344357
theorem B229601 : Blo 151794 229601 := bstep (se 2 (by rfl) ⟨86100, by rfl⟩ : syracuseStep 229601 = 172201) B172201
theorem B295139 : Blo 151794 295139 := bstep (se 1 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 295139 = 442709) B442709
theorem B393457 : Blo 151794 393457 := bstep (se 2 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 393457 = 295093) B295093
theorem B229619 : Blo 151794 229619 := bstep (se 1 (by rfl) ⟨172214, by rfl⟩ : syracuseStep 229619 = 344429) B344429
theorem B229649 : Blo 151794 229649 := bstep (se 2 (by rfl) ⟨86118, by rfl⟩ : syracuseStep 229649 = 172237) B172237
theorem B262433 : Blo 151794 262433 := bstep (se 2 (by rfl) ⟨98412, by rfl⟩ : syracuseStep 262433 = 196825) B196825
theorem B229667 : Blo 151794 229667 := bstep (se 1 (by rfl) ⟨172250, by rfl⟩ : syracuseStep 229667 = 344501) B344501
theorem B229697 : Blo 151794 229697 := bstep (se 2 (by rfl) ⟨86136, by rfl⟩ : syracuseStep 229697 = 172273) B172273
theorem B196931 : Blo 151794 196931 := bstep (se 1 (by rfl) ⟨147698, by rfl⟩ : syracuseStep 196931 = 295397) B295397
theorem B229715 : Blo 151794 229715 := bstep (se 1 (by rfl) ⟨172286, by rfl⟩ : syracuseStep 229715 = 344573) B344573
theorem B229745 : Blo 151794 229745 := bstep (se 2 (by rfl) ⟨86154, by rfl⟩ : syracuseStep 229745 = 172309) B172309
theorem B229763 : Blo 151794 229763 := bstep (se 1 (by rfl) ⟨172322, by rfl⟩ : syracuseStep 229763 = 344645) B344645
theorem B229793 : Blo 151794 229793 := bstep (se 2 (by rfl) ⟨86172, by rfl⟩ : syracuseStep 229793 = 172345) B172345
theorem B262561 : Blo 151794 262561 := bstep (se 2 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 262561 = 196921) B196921
theorem B524717 : Blo 151794 524717 := bstep (se 3 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 524717 = 196769) B196769
theorem B229811 : Blo 151794 229811 := bstep (se 1 (by rfl) ⟨172358, by rfl⟩ : syracuseStep 229811 = 344717) B344717
theorem B262595 : Blo 151794 262595 := bstep (se 1 (by rfl) ⟨196946, by rfl⟩ : syracuseStep 262595 = 393893) B393893
theorem B229841 : Blo 151794 229841 := bstep (se 2 (by rfl) ⟨86190, by rfl⟩ : syracuseStep 229841 = 172381) B172381
theorem B229859 : Blo 151794 229859 := bstep (se 1 (by rfl) ⟨172394, by rfl⟩ : syracuseStep 229859 = 344789) B344789
theorem B524771 : Blo 151794 524771 := bstep (se 1 (by rfl) ⟨393578, by rfl⟩ : syracuseStep 524771 = 787157) B787157
theorem B229889 : Blo 151794 229889 := bstep (se 2 (by rfl) ⟨86208, by rfl⟩ : syracuseStep 229889 = 172417) B172417
theorem B393731 : Blo 151794 393731 := bstep (se 1 (by rfl) ⟨295298, by rfl⟩ : syracuseStep 393731 = 590597) B590597
theorem B295427 : Blo 151794 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B229907 : Blo 151794 229907 := bstep (se 1 (by rfl) ⟨172430, by rfl⟩ : syracuseStep 229907 = 344861) B344861
theorem B229937 : Blo 151794 229937 := bstep (se 2 (by rfl) ⟨86226, by rfl⟩ : syracuseStep 229937 = 172453) B172453
theorem B229955 : Blo 151794 229955 := bstep (se 1 (by rfl) ⟨172466, by rfl⟩ : syracuseStep 229955 = 344933) B344933
theorem B262723 : Blo 151794 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B164435 : Blo 151794 164435 := bstep (se 1 (by rfl) ⟨123326, by rfl⟩ : syracuseStep 164435 = 246653) B246653
theorem B229985 : Blo 151794 229985 := bstep (se 2 (by rfl) ⟨86244, by rfl⟩ : syracuseStep 229985 = 172489) B172489
theorem B230003 : Blo 151794 230003 := bstep (se 1 (by rfl) ⟨172502, by rfl⟩ : syracuseStep 230003 = 345005) B345005
theorem B230033 : Blo 151794 230033 := bstep (se 2 (by rfl) ⟨86262, by rfl⟩ : syracuseStep 230033 = 172525) B172525
theorem B230051 : Blo 151794 230051 := bstep (se 1 (by rfl) ⟨172538, by rfl⟩ : syracuseStep 230051 = 345077) B345077
theorem B230081 : Blo 151794 230081 := bstep (se 2 (by rfl) ⟨86280, by rfl⟩ : syracuseStep 230081 = 172561) B172561
theorem B393923 : Blo 151794 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B262865 : Blo 151794 262865 := bstep (se 2 (by rfl) ⟨98574, by rfl⟩ : syracuseStep 262865 = 197149) B197149
theorem B230099 : Blo 151794 230099 := bstep (se 1 (by rfl) ⟨172574, by rfl⟩ : syracuseStep 230099 = 345149) B345149
theorem B230129 : Blo 151794 230129 := bstep (se 2 (by rfl) ⟨86298, by rfl⟩ : syracuseStep 230129 = 172597) B172597
theorem B525041 : Blo 151794 525041 := bstep (se 2 (by rfl) ⟨196890, by rfl⟩ : syracuseStep 525041 = 393781) B393781
theorem B230147 : Blo 151794 230147 := bstep (se 1 (by rfl) ⟨172610, by rfl⟩ : syracuseStep 230147 = 345221) B345221
theorem B230177 : Blo 151794 230177 := bstep (se 2 (by rfl) ⟨86316, by rfl⟩ : syracuseStep 230177 = 172633) B172633
theorem B230195 : Blo 151794 230195 := bstep (se 1 (by rfl) ⟨172646, by rfl⟩ : syracuseStep 230195 = 345293) B345293
theorem B230225 : Blo 151794 230225 := bstep (se 2 (by rfl) ⟨86334, by rfl⟩ : syracuseStep 230225 = 172669) B172669
theorem B328529 : Blo 151794 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B230243 : Blo 151794 230243 := bstep (se 1 (by rfl) ⟨172682, by rfl⟩ : syracuseStep 230243 = 345365) B345365
theorem B230273 : Blo 151794 230273 := bstep (se 2 (by rfl) ⟨86352, by rfl⟩ : syracuseStep 230273 = 172705) B172705
theorem B230291 : Blo 151794 230291 := bstep (se 1 (by rfl) ⟨172718, by rfl⟩ : syracuseStep 230291 = 345437) B345437
theorem B230321 : Blo 151794 230321 := bstep (se 2 (by rfl) ⟨86370, by rfl⟩ : syracuseStep 230321 = 172741) B172741
theorem B230339 : Blo 151794 230339 := bstep (se 1 (by rfl) ⟨172754, by rfl⟩ : syracuseStep 230339 = 345509) B345509
theorem B230369 : Blo 151794 230369 := bstep (se 2 (by rfl) ⟨86388, by rfl⟩ : syracuseStep 230369 = 172777) B172777
theorem B230387 : Blo 151794 230387 := bstep (se 1 (by rfl) ⟨172790, by rfl⟩ : syracuseStep 230387 = 345581) B345581
theorem B623629 : Blo 151794 623629 := bstep (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) B233861
theorem B230417 : Blo 151794 230417 := bstep (se 2 (by rfl) ⟨86406, by rfl⟩ : syracuseStep 230417 = 172813) B172813
theorem B230435 : Blo 151794 230435 := bstep (se 1 (by rfl) ⟨172826, by rfl⟩ : syracuseStep 230435 = 345653) B345653
theorem B4949045 : Blo 151794 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B230465 : Blo 151794 230465 := bstep (se 2 (by rfl) ⟨86424, by rfl⟩ : syracuseStep 230465 = 172849) B172849
theorem B230483 : Blo 151794 230483 := bstep (se 1 (by rfl) ⟨172862, by rfl⟩ : syracuseStep 230483 = 345725) B345725
theorem B230513 : Blo 151794 230513 := bstep (se 2 (by rfl) ⟨86442, by rfl⟩ : syracuseStep 230513 = 172885) B172885
theorem B230531 : Blo 151794 230531 := bstep (se 1 (by rfl) ⟨172898, by rfl⟩ : syracuseStep 230531 = 345797) B345797
theorem B263299 : Blo 151794 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B230561 : Blo 151794 230561 := bstep (se 2 (by rfl) ⟨86460, by rfl⟩ : syracuseStep 230561 = 172921) B172921
theorem B230579 : Blo 151794 230579 := bstep (se 1 (by rfl) ⟨172934, by rfl⟩ : syracuseStep 230579 = 345869) B345869
theorem B230609 : Blo 151794 230609 := bstep (se 2 (by rfl) ⟨86478, by rfl⟩ : syracuseStep 230609 = 172957) B172957
theorem B230627 : Blo 151794 230627 := bstep (se 1 (by rfl) ⟨172970, by rfl⟩ : syracuseStep 230627 = 345941) B345941
theorem B328931 : Blo 151794 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B230657 : Blo 151794 230657 := bstep (se 2 (by rfl) ⟨86496, by rfl⟩ : syracuseStep 230657 = 172993) B172993
theorem B525581 : Blo 151794 525581 := bstep (se 3 (by rfl) ⟨98546, by rfl⟩ : syracuseStep 525581 = 197093) B197093
theorem B230675 : Blo 151794 230675 := bstep (se 1 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 230675 = 346013) B346013
theorem B230705 : Blo 151794 230705 := bstep (se 2 (by rfl) ⟨86514, by rfl⟩ : syracuseStep 230705 = 173029) B173029
theorem B230723 : Blo 151794 230723 := bstep (se 1 (by rfl) ⟨173042, by rfl⟩ : syracuseStep 230723 = 346085) B346085
theorem B165187 : Blo 151794 165187 := bstep (se 1 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 165187 = 247781) B247781
theorem B525635 : Blo 151794 525635 := bstep (se 1 (by rfl) ⟨394226, by rfl⟩ : syracuseStep 525635 = 788453) B788453
theorem B230753 : Blo 151794 230753 := bstep (se 2 (by rfl) ⟨86532, by rfl⟩ : syracuseStep 230753 = 173065) B173065
theorem B230771 : Blo 151794 230771 := bstep (se 1 (by rfl) ⟨173078, by rfl⟩ : syracuseStep 230771 = 346157) B346157
theorem B230801 : Blo 151794 230801 := bstep (se 2 (by rfl) ⟨86550, by rfl⟩ : syracuseStep 230801 = 173101) B173101
theorem B230819 : Blo 151794 230819 := bstep (se 1 (by rfl) ⟨173114, by rfl⟩ : syracuseStep 230819 = 346229) B346229
theorem B263587 : Blo 151794 263587 := bstep (se 1 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 263587 = 395381) B395381
theorem B230849 : Blo 151794 230849 := bstep (se 2 (by rfl) ⟨86568, by rfl⟩ : syracuseStep 230849 = 173137) B173137
theorem B230867 : Blo 151794 230867 := bstep (se 1 (by rfl) ⟨173150, by rfl⟩ : syracuseStep 230867 = 346301) B346301
theorem B394723 : Blo 151794 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B230897 : Blo 151794 230897 := bstep (se 2 (by rfl) ⟨86586, by rfl⟩ : syracuseStep 230897 = 173173) B173173
theorem B230915 : Blo 151794 230915 := bstep (se 1 (by rfl) ⟨173186, by rfl⟩ : syracuseStep 230915 = 346373) B346373
theorem B230945 : Blo 151794 230945 := bstep (se 2 (by rfl) ⟨86604, by rfl⟩ : syracuseStep 230945 = 173209) B173209
theorem B230963 : Blo 151794 230963 := bstep (se 1 (by rfl) ⟨173222, by rfl⟩ : syracuseStep 230963 = 346445) B346445
theorem B230993 : Blo 151794 230993 := bstep (se 2 (by rfl) ⟨86622, by rfl⟩ : syracuseStep 230993 = 173245) B173245
theorem B231011 : Blo 151794 231011 := bstep (se 1 (by rfl) ⟨173258, by rfl⟩ : syracuseStep 231011 = 346517) B346517
theorem B231041 : Blo 151794 231041 := bstep (se 2 (by rfl) ⟨86640, by rfl⟩ : syracuseStep 231041 = 173281) B173281
theorem B231059 : Blo 151794 231059 := bstep (se 1 (by rfl) ⟨173294, by rfl⟩ : syracuseStep 231059 = 346589) B346589
theorem B493229 : Blo 151794 493229 := bstep (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) B184961
theorem B231089 : Blo 151794 231089 := bstep (se 2 (by rfl) ⟨86658, by rfl⟩ : syracuseStep 231089 = 173317) B173317
theorem B231107 : Blo 151794 231107 := bstep (se 1 (by rfl) ⟨173330, by rfl⟩ : syracuseStep 231107 = 346661) B346661
theorem B231137 : Blo 151794 231137 := bstep (se 2 (by rfl) ⟨86676, by rfl⟩ : syracuseStep 231137 = 173353) B173353
theorem B1050353 : Blo 151794 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B231155 : Blo 151794 231155 := bstep (se 1 (by rfl) ⟨173366, by rfl⟩ : syracuseStep 231155 = 346733) B346733
theorem B231185 : Blo 151794 231185 := bstep (se 2 (by rfl) ⟨86694, by rfl⟩ : syracuseStep 231185 = 173389) B173389
theorem B231203 : Blo 151794 231203 := bstep (se 1 (by rfl) ⟨173402, by rfl⟩ : syracuseStep 231203 = 346805) B346805
theorem B3573557 : Blo 151794 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B231233 : Blo 151794 231233 := bstep (se 2 (by rfl) ⟨86712, by rfl⟩ : syracuseStep 231233 = 173425) B173425
theorem B231251 : Blo 151794 231251 := bstep (se 1 (by rfl) ⟨173438, by rfl⟩ : syracuseStep 231251 = 346877) B346877
theorem B231281 : Blo 151794 231281 := bstep (se 2 (by rfl) ⟨86730, by rfl⟩ : syracuseStep 231281 = 173461) B173461
theorem B231299 : Blo 151794 231299 := bstep (se 1 (by rfl) ⟨173474, by rfl⟩ : syracuseStep 231299 = 346949) B346949
theorem B231329 : Blo 151794 231329 := bstep (se 2 (by rfl) ⟨86748, by rfl⟩ : syracuseStep 231329 = 173497) B173497
theorem B231347 : Blo 151794 231347 := bstep (se 1 (by rfl) ⟨173510, by rfl⟩ : syracuseStep 231347 = 347021) B347021
theorem B231377 : Blo 151794 231377 := bstep (se 2 (by rfl) ⟨86766, by rfl⟩ : syracuseStep 231377 = 173533) B173533
theorem B231395 : Blo 151794 231395 := bstep (se 1 (by rfl) ⟨173546, by rfl⟩ : syracuseStep 231395 = 347093) B347093
theorem B231425 : Blo 151794 231425 := bstep (se 2 (by rfl) ⟨86784, by rfl⟩ : syracuseStep 231425 = 173569) B173569
theorem B231443 : Blo 151794 231443 := bstep (se 1 (by rfl) ⟨173582, by rfl⟩ : syracuseStep 231443 = 347165) B347165
theorem B231473 : Blo 151794 231473 := bstep (se 2 (by rfl) ⟨86802, by rfl⟩ : syracuseStep 231473 = 173605) B173605
theorem B231491 : Blo 151794 231491 := bstep (se 1 (by rfl) ⟨173618, by rfl⟩ : syracuseStep 231491 = 347237) B347237
theorem B526417 : Blo 151794 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B231521 : Blo 151794 231521 := bstep (se 2 (by rfl) ⟨86820, by rfl⟩ : syracuseStep 231521 = 173641) B173641
theorem B329827 : Blo 151794 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B231539 : Blo 151794 231539 := bstep (se 1 (by rfl) ⟨173654, by rfl⟩ : syracuseStep 231539 = 347309) B347309
theorem B985229 : Blo 151794 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B231569 : Blo 151794 231569 := bstep (se 2 (by rfl) ⟨86838, by rfl⟩ : syracuseStep 231569 = 173677) B173677
theorem B231587 : Blo 151794 231587 := bstep (se 1 (by rfl) ⟨173690, by rfl⟩ : syracuseStep 231587 = 347381) B347381
theorem B231617 : Blo 151794 231617 := bstep (se 2 (by rfl) ⟨86856, by rfl⟩ : syracuseStep 231617 = 173713) B173713
theorem B231635 : Blo 151794 231635 := bstep (se 1 (by rfl) ⟨173726, by rfl⟩ : syracuseStep 231635 = 347453) B347453
theorem B231665 : Blo 151794 231665 := bstep (se 2 (by rfl) ⟨86874, by rfl⟩ : syracuseStep 231665 = 173749) B173749
theorem B231683 : Blo 151794 231683 := bstep (se 1 (by rfl) ⟨173762, by rfl⟩ : syracuseStep 231683 = 347525) B347525
theorem B231713 : Blo 151794 231713 := bstep (se 2 (by rfl) ⟨86892, by rfl⟩ : syracuseStep 231713 = 173785) B173785
theorem B166195 : Blo 151794 166195 := bstep (se 1 (by rfl) ⟨124646, by rfl⟩ : syracuseStep 166195 = 249293) B249293
theorem B231731 : Blo 151794 231731 := bstep (se 1 (by rfl) ⟨173798, by rfl⟩ : syracuseStep 231731 = 347597) B347597
theorem B231761 : Blo 151794 231761 := bstep (se 2 (by rfl) ⟨86910, by rfl⟩ : syracuseStep 231761 = 173821) B173821
theorem B231779 : Blo 151794 231779 := bstep (se 1 (by rfl) ⟨173834, by rfl⟩ : syracuseStep 231779 = 347669) B347669
theorem B231809 : Blo 151794 231809 := bstep (se 2 (by rfl) ⟨86928, by rfl⟩ : syracuseStep 231809 = 173857) B173857
theorem B231827 : Blo 151794 231827 := bstep (se 1 (by rfl) ⟨173870, by rfl⟩ : syracuseStep 231827 = 347741) B347741
theorem B231857 : Blo 151794 231857 := bstep (se 2 (by rfl) ⟨86946, by rfl⟩ : syracuseStep 231857 = 173893) B173893
theorem B231875 : Blo 151794 231875 := bstep (se 1 (by rfl) ⟨173906, by rfl⟩ : syracuseStep 231875 = 347813) B347813
theorem B231905 : Blo 151794 231905 := bstep (se 2 (by rfl) ⟨86964, by rfl⟩ : syracuseStep 231905 = 173929) B173929
theorem B231923 : Blo 151794 231923 := bstep (se 1 (by rfl) ⟨173942, by rfl⟩ : syracuseStep 231923 = 347885) B347885
theorem B1313293 : Blo 151794 1313293 := bstep (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) B492485
theorem B231953 : Blo 151794 231953 := bstep (se 2 (by rfl) ⟨86982, by rfl⟩ : syracuseStep 231953 = 173965) B173965
theorem B231971 : Blo 151794 231971 := bstep (se 1 (by rfl) ⟨173978, by rfl⟩ : syracuseStep 231971 = 347957) B347957
theorem B232001 : Blo 151794 232001 := bstep (se 2 (by rfl) ⟨87000, by rfl⟩ : syracuseStep 232001 = 174001) B174001
theorem B232019 : Blo 151794 232019 := bstep (se 1 (by rfl) ⟨174014, by rfl⟩ : syracuseStep 232019 = 348029) B348029
theorem B232049 : Blo 151794 232049 := bstep (se 2 (by rfl) ⟨87018, by rfl⟩ : syracuseStep 232049 = 174037) B174037
theorem B232067 : Blo 151794 232067 := bstep (se 1 (by rfl) ⟨174050, by rfl⟩ : syracuseStep 232067 = 348101) B348101
theorem B494221 : Blo 151794 494221 := bstep (se 3 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 494221 = 185333) B185333
theorem B232097 : Blo 151794 232097 := bstep (se 2 (by rfl) ⟨87036, by rfl⟩ : syracuseStep 232097 = 174073) B174073
theorem B625315 : Blo 151794 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B232115 : Blo 151794 232115 := bstep (se 1 (by rfl) ⟨174086, by rfl⟩ : syracuseStep 232115 = 348173) B348173
theorem B232145 : Blo 151794 232145 := bstep (se 2 (by rfl) ⟨87054, by rfl⟩ : syracuseStep 232145 = 174109) B174109
theorem B232163 : Blo 151794 232163 := bstep (se 1 (by rfl) ⟨174122, by rfl⟩ : syracuseStep 232163 = 348245) B348245
theorem B232193 : Blo 151794 232193 := bstep (se 2 (by rfl) ⟨87072, by rfl⟩ : syracuseStep 232193 = 174145) B174145
theorem B232211 : Blo 151794 232211 := bstep (se 1 (by rfl) ⟨174158, by rfl⟩ : syracuseStep 232211 = 348317) B348317
theorem B232241 : Blo 151794 232241 := bstep (se 2 (by rfl) ⟨87090, by rfl⟩ : syracuseStep 232241 = 174181) B174181
theorem B232259 : Blo 151794 232259 := bstep (se 1 (by rfl) ⟨174194, by rfl⟩ : syracuseStep 232259 = 348389) B348389
theorem B232289 : Blo 151794 232289 := bstep (se 2 (by rfl) ⟨87108, by rfl⟩ : syracuseStep 232289 = 174217) B174217
theorem B232307 : Blo 151794 232307 := bstep (se 1 (by rfl) ⟨174230, by rfl⟩ : syracuseStep 232307 = 348461) B348461
theorem B232337 : Blo 151794 232337 := bstep (se 2 (by rfl) ⟨87126, by rfl⟩ : syracuseStep 232337 = 174253) B174253
theorem B232355 : Blo 151794 232355 := bstep (se 1 (by rfl) ⟨174266, by rfl⟩ : syracuseStep 232355 = 348533) B348533
theorem B232385 : Blo 151794 232385 := bstep (se 2 (by rfl) ⟨87144, by rfl⟩ : syracuseStep 232385 = 174289) B174289
theorem B232403 : Blo 151794 232403 := bstep (se 1 (by rfl) ⟨174302, by rfl⟩ : syracuseStep 232403 = 348605) B348605
theorem B232433 : Blo 151794 232433 := bstep (se 2 (by rfl) ⟨87162, by rfl⟩ : syracuseStep 232433 = 174325) B174325
theorem B232451 : Blo 151794 232451 := bstep (se 1 (by rfl) ⟨174338, by rfl⟩ : syracuseStep 232451 = 348677) B348677
theorem B232481 : Blo 151794 232481 := bstep (se 2 (by rfl) ⟨87180, by rfl⟩ : syracuseStep 232481 = 174361) B174361
theorem B232499 : Blo 151794 232499 := bstep (se 1 (by rfl) ⟨174374, by rfl⟩ : syracuseStep 232499 = 348749) B348749
theorem B232529 : Blo 151794 232529 := bstep (se 2 (by rfl) ⟨87198, by rfl⟩ : syracuseStep 232529 = 174397) B174397
theorem B232547 : Blo 151794 232547 := bstep (se 1 (by rfl) ⟨174410, by rfl⟩ : syracuseStep 232547 = 348821) B348821
theorem B232577 : Blo 151794 232577 := bstep (se 2 (by rfl) ⟨87216, by rfl⟩ : syracuseStep 232577 = 174433) B174433
theorem B232595 : Blo 151794 232595 := bstep (se 1 (by rfl) ⟨174446, by rfl⟩ : syracuseStep 232595 = 348893) B348893
theorem B232625 : Blo 151794 232625 := bstep (se 2 (by rfl) ⟨87234, by rfl⟩ : syracuseStep 232625 = 174469) B174469
theorem B756913 : Blo 151794 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B232643 : Blo 151794 232643 := bstep (se 1 (by rfl) ⟨174482, by rfl⟩ : syracuseStep 232643 = 348965) B348965
theorem B232673 : Blo 151794 232673 := bstep (se 2 (by rfl) ⟨87252, by rfl⟩ : syracuseStep 232673 = 174505) B174505
theorem B232691 : Blo 151794 232691 := bstep (se 1 (by rfl) ⟨174518, by rfl⟩ : syracuseStep 232691 = 349037) B349037
theorem B298243 : Blo 151794 298243 := bstep (se 1 (by rfl) ⟨223682, by rfl⟩ : syracuseStep 298243 = 447365) B447365
theorem B232721 : Blo 151794 232721 := bstep (se 2 (by rfl) ⟨87270, by rfl⟩ : syracuseStep 232721 = 174541) B174541
theorem B232739 : Blo 151794 232739 := bstep (se 1 (by rfl) ⟨174554, by rfl⟩ : syracuseStep 232739 = 349109) B349109
theorem B331057 : Blo 151794 331057 := bstep (se 2 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 331057 = 248293) B248293
theorem B232769 : Blo 151794 232769 := bstep (se 2 (by rfl) ⟨87288, by rfl⟩ : syracuseStep 232769 = 174577) B174577
theorem B232787 : Blo 151794 232787 := bstep (se 1 (by rfl) ⟨174590, by rfl⟩ : syracuseStep 232787 = 349181) B349181
theorem B232817 : Blo 151794 232817 := bstep (se 2 (by rfl) ⟨87306, by rfl⟩ : syracuseStep 232817 = 174613) B174613
theorem B232835 : Blo 151794 232835 := bstep (se 1 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 232835 = 349253) B349253
theorem B232865 : Blo 151794 232865 := bstep (se 2 (by rfl) ⟨87324, by rfl⟩ : syracuseStep 232865 = 174649) B174649
theorem B232883 : Blo 151794 232883 := bstep (se 1 (by rfl) ⟨174662, by rfl⟩ : syracuseStep 232883 = 349325) B349325
theorem B232913 : Blo 151794 232913 := bstep (se 2 (by rfl) ⟨87342, by rfl⟩ : syracuseStep 232913 = 174685) B174685
theorem B232931 : Blo 151794 232931 := bstep (se 1 (by rfl) ⟨174698, by rfl⟩ : syracuseStep 232931 = 349397) B349397
theorem B232961 : Blo 151794 232961 := bstep (se 2 (by rfl) ⟨87360, by rfl⟩ : syracuseStep 232961 = 174721) B174721
theorem B232979 : Blo 151794 232979 := bstep (se 1 (by rfl) ⟨174734, by rfl⟩ : syracuseStep 232979 = 349469) B349469
theorem B233009 : Blo 151794 233009 := bstep (se 2 (by rfl) ⟨87378, by rfl⟩ : syracuseStep 233009 = 174757) B174757
theorem B527939 : Blo 151794 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B233027 : Blo 151794 233027 := bstep (se 1 (by rfl) ⟨174770, by rfl⟩ : syracuseStep 233027 = 349541) B349541
theorem B233057 : Blo 151794 233057 := bstep (se 2 (by rfl) ⟨87396, by rfl⟩ : syracuseStep 233057 = 174793) B174793
theorem B233075 : Blo 151794 233075 := bstep (se 1 (by rfl) ⟨174806, by rfl⟩ : syracuseStep 233075 = 349613) B349613
theorem B233105 : Blo 151794 233105 := bstep (se 2 (by rfl) ⟨87414, by rfl⟩ : syracuseStep 233105 = 174829) B174829
theorem B659107 : Blo 151794 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B233123 : Blo 151794 233123 := bstep (se 1 (by rfl) ⟨174842, by rfl⟩ : syracuseStep 233123 = 349685) B349685
theorem B233153 : Blo 151794 233153 := bstep (se 2 (by rfl) ⟨87432, by rfl⟩ : syracuseStep 233153 = 174865) B174865
theorem B233171 : Blo 151794 233171 := bstep (se 1 (by rfl) ⟨174878, by rfl⟩ : syracuseStep 233171 = 349757) B349757
theorem B626417 : Blo 151794 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B233201 : Blo 151794 233201 := bstep (se 2 (by rfl) ⟨87450, by rfl⟩ : syracuseStep 233201 = 174901) B174901
theorem B233219 : Blo 151794 233219 := bstep (se 1 (by rfl) ⟨174914, by rfl⟩ : syracuseStep 233219 = 349829) B349829
theorem B233249 : Blo 151794 233249 := bstep (se 2 (by rfl) ⟨87468, by rfl⟩ : syracuseStep 233249 = 174937) B174937
theorem B233267 : Blo 151794 233267 := bstep (se 1 (by rfl) ⟨174950, by rfl⟩ : syracuseStep 233267 = 349901) B349901
theorem B1314629 : Blo 151794 1314629 := bstep (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) B246493
theorem B233297 : Blo 151794 233297 := bstep (se 2 (by rfl) ⟨87486, by rfl⟩ : syracuseStep 233297 = 174973) B174973
theorem B233315 : Blo 151794 233315 := bstep (se 1 (by rfl) ⟨174986, by rfl⟩ : syracuseStep 233315 = 349973) B349973
theorem B233345 : Blo 151794 233345 := bstep (se 2 (by rfl) ⟨87504, by rfl⟩ : syracuseStep 233345 = 175009) B175009
theorem B233363 : Blo 151794 233363 := bstep (se 1 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 233363 = 350045) B350045
theorem B233393 : Blo 151794 233393 := bstep (se 2 (by rfl) ⟨87522, by rfl⟩ : syracuseStep 233393 = 175045) B175045
theorem B233411 : Blo 151794 233411 := bstep (se 1 (by rfl) ⟨175058, by rfl⟩ : syracuseStep 233411 = 350117) B350117
theorem B233441 : Blo 151794 233441 := bstep (se 2 (by rfl) ⟨87540, by rfl⟩ : syracuseStep 233441 = 175081) B175081
theorem B233459 : Blo 151794 233459 := bstep (se 1 (by rfl) ⟨175094, by rfl⟩ : syracuseStep 233459 = 350189) B350189
theorem B233489 : Blo 151794 233489 := bstep (se 2 (by rfl) ⟨87558, by rfl⟩ : syracuseStep 233489 = 175117) B175117
theorem B233507 : Blo 151794 233507 := bstep (se 1 (by rfl) ⟨175130, by rfl⟩ : syracuseStep 233507 = 350261) B350261
theorem B233537 : Blo 151794 233537 := bstep (se 2 (by rfl) ⟨87576, by rfl⟩ : syracuseStep 233537 = 175153) B175153
theorem B233555 : Blo 151794 233555 := bstep (se 1 (by rfl) ⟨175166, by rfl⟩ : syracuseStep 233555 = 350333) B350333
theorem B495715 : Blo 151794 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B233585 : Blo 151794 233585 := bstep (se 2 (by rfl) ⟨87594, by rfl⟩ : syracuseStep 233585 = 175189) B175189
theorem B233603 : Blo 151794 233603 := bstep (se 1 (by rfl) ⟨175202, by rfl⟩ : syracuseStep 233603 = 350405) B350405
theorem B233633 : Blo 151794 233633 := bstep (se 2 (by rfl) ⟨87612, by rfl⟩ : syracuseStep 233633 = 175225) B175225
theorem B233651 : Blo 151794 233651 := bstep (se 1 (by rfl) ⟨175238, by rfl⟩ : syracuseStep 233651 = 350477) B350477
theorem B233681 : Blo 151794 233681 := bstep (se 2 (by rfl) ⟨87630, by rfl⟩ : syracuseStep 233681 = 175261) B175261
theorem B495857 : Blo 151794 495857 := bstep (se 2 (by rfl) ⟨185946, by rfl⟩ : syracuseStep 495857 = 371893) B371893
theorem B495971 : Blo 151794 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B790897 : Blo 151794 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B627277 : Blo 151794 627277 := bstep (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) B235229
theorem B332561 : Blo 151794 332561 := bstep (se 2 (by rfl) ⟨124710, by rfl⟩ : syracuseStep 332561 = 249421) B249421
theorem B332579 : Blo 151794 332579 := bstep (se 1 (by rfl) ⟨249434, by rfl⟩ : syracuseStep 332579 = 498869) B498869
theorem B2495285 : Blo 151794 2495285 := bstep (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) B233933
theorem B332753 : Blo 151794 332753 := bstep (se 2 (by rfl) ⟨124782, by rfl⟩ : syracuseStep 332753 = 249565) B249565
theorem B496945 : Blo 151794 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B824995 : Blo 151794 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B1251085 : Blo 151794 1251085 := bstep (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) B469157
theorem B464753 : Blo 151794 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B661553 : Blo 151794 661553 := bstep (se 2 (by rfl) ⟨248082, by rfl⟩ : syracuseStep 661553 = 496165) B496165
theorem B2398349 : Blo 151794 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B694925 : Blo 151794 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B1153763 : Blo 151794 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B170851 : Blo 151794 170851 := bstep (se 1 (by rfl) ⟨128138, by rfl⟩ : syracuseStep 170851 = 256277) B256277
theorem B236513 : Blo 151794 236513 := bstep (se 2 (by rfl) ⟨88692, by rfl⟩ : syracuseStep 236513 = 177385) B177385
theorem B170995 : Blo 151794 170995 := bstep (se 1 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 170995 = 256493) B256493
theorem B171139 : Blo 151794 171139 := bstep (se 1 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 171139 = 256709) B256709
theorem B171283 : Blo 151794 171283 := bstep (se 1 (by rfl) ⟨128462, by rfl⟩ : syracuseStep 171283 = 256925) B256925
theorem B171427 : Blo 151794 171427 := bstep (se 1 (by rfl) ⟨128570, by rfl⟩ : syracuseStep 171427 = 257141) B257141
theorem B171571 : Blo 151794 171571 := bstep (se 1 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 171571 = 257357) B257357
theorem B433745 : Blo 151794 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B171715 : Blo 151794 171715 := bstep (se 1 (by rfl) ⟨128786, by rfl⟩ : syracuseStep 171715 = 257573) B257573
theorem B990917 : Blo 151794 990917 := bstep (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) B185797
theorem B433937 : Blo 151794 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B171859 : Blo 151794 171859 := bstep (se 1 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 171859 = 257789) B257789
theorem B3383153 : Blo 151794 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B172003 : Blo 151794 172003 := bstep (se 1 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 172003 = 258005) B258005
theorem B172147 : Blo 151794 172147 := bstep (se 1 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 172147 = 258221) B258221
theorem B172291 : Blo 151794 172291 := bstep (se 1 (by rfl) ⟨129218, by rfl⟩ : syracuseStep 172291 = 258437) B258437
theorem B1188209 : Blo 151794 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B172435 : Blo 151794 172435 := bstep (se 1 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 172435 = 258653) B258653
theorem B172579 : Blo 151794 172579 := bstep (se 1 (by rfl) ⟨129434, by rfl⟩ : syracuseStep 172579 = 258869) B258869
theorem B172723 : Blo 151794 172723 := bstep (se 1 (by rfl) ⟨129542, by rfl⟩ : syracuseStep 172723 = 259085) B259085
theorem B1319651 : Blo 151794 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B434929 : Blo 151794 434929 := bstep (se 2 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 434929 = 326197) B326197
theorem B172867 : Blo 151794 172867 := bstep (se 1 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 172867 = 259301) B259301
theorem B664433 : Blo 151794 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B828301 : Blo 151794 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B173011 : Blo 151794 173011 := bstep (se 1 (by rfl) ⟨129758, by rfl⟩ : syracuseStep 173011 = 259517) B259517
theorem B435203 : Blo 151794 435203 := bstep (se 1 (by rfl) ⟨326402, by rfl⟩ : syracuseStep 435203 = 652805) B652805
theorem B173155 : Blo 151794 173155 := bstep (se 1 (by rfl) ⟨129866, by rfl⟩ : syracuseStep 173155 = 259733) B259733
theorem B435395 : Blo 151794 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B173299 : Blo 151794 173299 := bstep (se 1 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 173299 = 259949) B259949
theorem B173443 : Blo 151794 173443 := bstep (se 1 (by rfl) ⟨130082, by rfl⟩ : syracuseStep 173443 = 260165) B260165
theorem B501233 : Blo 151794 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B173587 : Blo 151794 173587 := bstep (se 1 (by rfl) ⟨130190, by rfl⟩ : syracuseStep 173587 = 260381) B260381
theorem B173731 : Blo 151794 173731 := bstep (se 1 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 173731 = 260597) B260597
theorem B665293 : Blo 151794 665293 := bstep (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) B249485
theorem B370403 : Blo 151794 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B173875 : Blo 151794 173875 := bstep (se 1 (by rfl) ⟨130406, by rfl⟩ : syracuseStep 173875 = 260813) B260813
theorem B174019 : Blo 151794 174019 := bstep (se 1 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 174019 = 261029) B261029
theorem B436205 : Blo 151794 436205 := bstep (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) B163577
theorem B174163 : Blo 151794 174163 := bstep (se 1 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 174163 = 261245) B261245
theorem B436387 : Blo 151794 436387 := bstep (se 1 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 436387 = 654581) B654581
theorem B1976501 : Blo 151794 1976501 := bstep (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) B185297
theorem B174307 : Blo 151794 174307 := bstep (se 1 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 174307 = 261461) B261461
theorem B1485155 : Blo 151794 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B174451 : Blo 151794 174451 := bstep (se 1 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 174451 = 261677) B261677
theorem B174595 : Blo 151794 174595 := bstep (se 1 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 174595 = 261893) B261893
theorem B436877 : Blo 151794 436877 := bstep (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) B163829
theorem B174739 : Blo 151794 174739 := bstep (se 1 (by rfl) ⟨131054, by rfl⟩ : syracuseStep 174739 = 262109) B262109
theorem B371363 : Blo 151794 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B371441 : Blo 151794 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B174883 : Blo 151794 174883 := bstep (se 1 (by rfl) ⟨131162, by rfl⟩ : syracuseStep 174883 = 262325) B262325
theorem B175027 : Blo 151794 175027 := bstep (se 1 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 175027 = 262541) B262541
theorem B175171 : Blo 151794 175171 := bstep (se 1 (by rfl) ⟨131378, by rfl⟩ : syracuseStep 175171 = 262757) B262757
theorem B438061 : Blo 151794 438061 := bstep (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) B164273
theorem B929677 : Blo 151794 929677 := bstep (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) B348629
theorem B1159109 : Blo 151794 1159109 := bstep (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) B217333
theorem B2470115 : Blo 151794 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B1323377 : Blo 151794 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B373123 : Blo 151794 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B504301 : Blo 151794 504301 := bstep (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) B189113
theorem B995917 : Blo 151794 995917 := bstep (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) B373469
theorem B307889 : Blo 151794 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B1880803 : Blo 151794 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B996101 : Blo 151794 996101 := bstep (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) B186769
theorem B439121 : Blo 151794 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B373585 : Blo 151794 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B865187 : Blo 151794 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B472529 : Blo 151794 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B439793 : Blo 151794 439793 := bstep (se 2 (by rfl) ⟨164922, by rfl⟩ : syracuseStep 439793 = 329845) B329845
theorem B341585 : Blo 151794 341585 := bstep (se 2 (by rfl) ⟨128094, by rfl⟩ : syracuseStep 341585 = 256189) B256189
theorem B341603 : Blo 151794 341603 := bstep (se 1 (by rfl) ⟨256202, by rfl⟩ : syracuseStep 341603 = 512405) B512405
theorem B341873 : Blo 151794 341873 := bstep (se 2 (by rfl) ⟨128202, by rfl⟩ : syracuseStep 341873 = 256405) B256405
theorem B341891 : Blo 151794 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B669617 : Blo 151794 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B342161 : Blo 151794 342161 := bstep (se 2 (by rfl) ⟨128310, by rfl⟩ : syracuseStep 342161 = 256621) B256621
theorem B342179 : Blo 151794 342179 := bstep (se 1 (by rfl) ⟨256634, by rfl⟩ : syracuseStep 342179 = 513269) B513269
theorem B440579 : Blo 151794 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B375185 : Blo 151794 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B342449 : Blo 151794 342449 := bstep (se 2 (by rfl) ⟨128418, by rfl⟩ : syracuseStep 342449 = 256837) B256837
theorem B342467 : Blo 151794 342467 := bstep (se 1 (by rfl) ⟨256850, by rfl⟩ : syracuseStep 342467 = 513701) B513701
theorem B276995 : Blo 151794 276995 := bstep (se 1 (by rfl) ⟨207746, by rfl⟩ : syracuseStep 276995 = 415493) B415493
theorem B440909 : Blo 151794 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B440977 : Blo 151794 440977 := bstep (se 2 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 440977 = 330733) B330733
theorem B768689 : Blo 151794 768689 := bstep (se 2 (by rfl) ⟨288258, by rfl⟩ : syracuseStep 768689 = 576517) B576517
theorem B408269 : Blo 151794 408269 := bstep (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) B153101
theorem B342737 : Blo 151794 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B342755 : Blo 151794 342755 := bstep (se 1 (by rfl) ⟨257066, by rfl⟩ : syracuseStep 342755 = 514133) B514133
theorem B244577 : Blo 151794 244577 := bstep (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) B183433
theorem B441251 : Blo 151794 441251 := bstep (se 1 (by rfl) ⟨330938, by rfl⟩ : syracuseStep 441251 = 661877) B661877
theorem B244705 : Blo 151794 244705 := bstep (se 2 (by rfl) ⟨91764, by rfl⟩ : syracuseStep 244705 = 183529) B183529
theorem B343025 : Blo 151794 343025 := bstep (se 2 (by rfl) ⟨128634, by rfl⟩ : syracuseStep 343025 = 257269) B257269
theorem B343043 : Blo 151794 343043 := bstep (se 1 (by rfl) ⟨257282, by rfl⟩ : syracuseStep 343043 = 514565) B514565
theorem B343313 : Blo 151794 343313 := bstep (se 2 (by rfl) ⟨128742, by rfl⟩ : syracuseStep 343313 = 257485) B257485
theorem B343331 : Blo 151794 343331 := bstep (se 1 (by rfl) ⟨257498, by rfl⟩ : syracuseStep 343331 = 514997) B514997
theorem B212401 : Blo 151794 212401 := bstep (se 2 (by rfl) ⟨79650, by rfl⟩ : syracuseStep 212401 = 159301) B159301
theorem B343601 : Blo 151794 343601 := bstep (se 2 (by rfl) ⟨128850, by rfl⟩ : syracuseStep 343601 = 257701) B257701
theorem B343619 : Blo 151794 343619 := bstep (se 1 (by rfl) ⟨257714, by rfl⟩ : syracuseStep 343619 = 515429) B515429
theorem B442093 : Blo 151794 442093 := bstep (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) B165785
theorem B343889 : Blo 151794 343889 := bstep (se 2 (by rfl) ⟨128958, by rfl⟩ : syracuseStep 343889 = 257917) B257917
theorem B343907 : Blo 151794 343907 := bstep (se 1 (by rfl) ⟨257930, by rfl⟩ : syracuseStep 343907 = 515861) B515861
theorem B2015117 : Blo 151794 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B442253 : Blo 151794 442253 := bstep (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) B165845
theorem B442435 : Blo 151794 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B868421 : Blo 151794 868421 := bstep (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) B162829
theorem B770147 : Blo 151794 770147 := bstep (se 1 (by rfl) ⟨577610, by rfl⟩ : syracuseStep 770147 = 1155221) B1155221
theorem B344177 : Blo 151794 344177 := bstep (se 2 (by rfl) ⟨129066, by rfl⟩ : syracuseStep 344177 = 258133) B258133
theorem B344195 : Blo 151794 344195 := bstep (se 1 (by rfl) ⟨258146, by rfl⟩ : syracuseStep 344195 = 516293) B516293
theorem B245987 : Blo 151794 245987 := bstep (se 1 (by rfl) ⟨184490, by rfl⟩ : syracuseStep 245987 = 368981) B368981
theorem B999665 : Blo 151794 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B1327373 : Blo 151794 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B246083 : Blo 151794 246083 := bstep (se 1 (by rfl) ⟨184562, by rfl⟩ : syracuseStep 246083 = 369125) B369125
theorem B246115 : Blo 151794 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B344465 : Blo 151794 344465 := bstep (se 2 (by rfl) ⟨129174, by rfl⟩ : syracuseStep 344465 = 258349) B258349
theorem B344483 : Blo 151794 344483 := bstep (se 1 (by rfl) ⟨258362, by rfl⟩ : syracuseStep 344483 = 516725) B516725
theorem B868877 : Blo 151794 868877 := bstep (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) B325829
theorem B344753 : Blo 151794 344753 := bstep (se 2 (by rfl) ⟨129282, by rfl⟩ : syracuseStep 344753 = 258565) B258565
theorem B344771 : Blo 151794 344771 := bstep (se 1 (by rfl) ⟨258578, by rfl⟩ : syracuseStep 344771 = 517157) B517157
theorem B1098467 : Blo 151794 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1983217 : Blo 151794 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B705293 : Blo 151794 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B1262405 : Blo 151794 1262405 := bstep (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) B236701
theorem B770957 : Blo 151794 770957 := bstep (se 3 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 770957 = 289109) B289109
theorem B1491853 : Blo 151794 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B345041 : Blo 151794 345041 := bstep (se 2 (by rfl) ⟨129390, by rfl⟩ : syracuseStep 345041 = 258781) B258781
theorem B345059 : Blo 151794 345059 := bstep (se 1 (by rfl) ⟨258794, by rfl⟩ : syracuseStep 345059 = 517589) B517589
theorem B3195875 : Blo 151794 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1983473 : Blo 151794 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B345329 : Blo 151794 345329 := bstep (se 2 (by rfl) ⟨129498, by rfl⟩ : syracuseStep 345329 = 258997) B258997
theorem B247025 : Blo 151794 247025 := bstep (se 2 (by rfl) ⟨92634, by rfl⟩ : syracuseStep 247025 = 185269) B185269
theorem B345347 : Blo 151794 345347 := bstep (se 1 (by rfl) ⟨259010, by rfl⟩ : syracuseStep 345347 = 518021) B518021
theorem B607651 : Blo 151794 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B345617 : Blo 151794 345617 := bstep (se 2 (by rfl) ⟨129606, by rfl⟩ : syracuseStep 345617 = 259213) B259213
theorem B345635 : Blo 151794 345635 := bstep (se 1 (by rfl) ⟨259226, by rfl⟩ : syracuseStep 345635 = 518453) B518453
theorem B1164941 : Blo 151794 1164941 := bstep (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) B436853
theorem B3786517 : Blo 151794 3786517 := bstep (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) B177493
theorem B345905 : Blo 151794 345905 := bstep (se 2 (by rfl) ⟨129714, by rfl⟩ : syracuseStep 345905 = 259429) B259429
theorem B345923 : Blo 151794 345923 := bstep (se 1 (by rfl) ⟨259442, by rfl⟩ : syracuseStep 345923 = 518885) B518885
theorem B411601 : Blo 151794 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B346193 : Blo 151794 346193 := bstep (se 2 (by rfl) ⟨129822, by rfl⟩ : syracuseStep 346193 = 259645) B259645
theorem B346211 : Blo 151794 346211 := bstep (se 1 (by rfl) ⟨259658, by rfl⟩ : syracuseStep 346211 = 519317) B519317
theorem B706765 : Blo 151794 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B1755377 : Blo 151794 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B346481 : Blo 151794 346481 := bstep (se 2 (by rfl) ⟨129930, by rfl⟩ : syracuseStep 346481 = 259861) B259861
theorem B346499 : Blo 151794 346499 := bstep (se 1 (by rfl) ⟨259874, by rfl⟩ : syracuseStep 346499 = 519749) B519749
theorem B215473 : Blo 151794 215473 := bstep (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) B161605
theorem B248339 : Blo 151794 248339 := bstep (se 1 (by rfl) ⟨186254, by rfl⟩ : syracuseStep 248339 = 372509) B372509
theorem B346769 : Blo 151794 346769 := bstep (se 2 (by rfl) ⟨130038, by rfl⟩ : syracuseStep 346769 = 260077) B260077
theorem B346787 : Blo 151794 346787 := bstep (se 1 (by rfl) ⟨260090, by rfl⟩ : syracuseStep 346787 = 520181) B520181
theorem B1395427 : Blo 151794 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B347057 : Blo 151794 347057 := bstep (se 2 (by rfl) ⟨130146, by rfl⟩ : syracuseStep 347057 = 260293) B260293
theorem B347075 : Blo 151794 347075 := bstep (se 1 (by rfl) ⟨260306, by rfl⟩ : syracuseStep 347075 = 520613) B520613
theorem B249011 : Blo 151794 249011 := bstep (se 1 (by rfl) ⟨186758, by rfl⟩ : syracuseStep 249011 = 373517) B373517
theorem B412877 : Blo 151794 412877 := bstep (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) B154829
theorem B347345 : Blo 151794 347345 := bstep (se 2 (by rfl) ⟨130254, by rfl⟩ : syracuseStep 347345 = 260509) B260509
theorem B347363 : Blo 151794 347363 := bstep (se 1 (by rfl) ⟨260522, by rfl⟩ : syracuseStep 347363 = 521045) B521045
theorem B216371 : Blo 151794 216371 := bstep (se 1 (by rfl) ⟨162278, by rfl⟩ : syracuseStep 216371 = 324557) B324557
theorem B871793 : Blo 151794 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B249313 : Blo 151794 249313 := bstep (se 2 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 249313 = 186985) B186985
theorem B347633 : Blo 151794 347633 := bstep (se 2 (by rfl) ⟨130362, by rfl⟩ : syracuseStep 347633 = 260725) B260725
theorem B347651 : Blo 151794 347651 := bstep (se 1 (by rfl) ⟨260738, by rfl⟩ : syracuseStep 347651 = 521477) B521477
theorem B183875 : Blo 151794 183875 := bstep (se 1 (by rfl) ⟨137906, by rfl⟩ : syracuseStep 183875 = 275813) B275813
theorem B4247153 : Blo 151794 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B249523 : Blo 151794 249523 := bstep (se 1 (by rfl) ⟨187142, by rfl⟩ : syracuseStep 249523 = 374285) B374285
theorem B773873 : Blo 151794 773873 := bstep (se 2 (by rfl) ⟨290202, by rfl⟩ : syracuseStep 773873 = 580405) B580405
theorem B347921 : Blo 151794 347921 := bstep (se 2 (by rfl) ⟨130470, by rfl⟩ : syracuseStep 347921 = 260941) B260941
theorem B741155 : Blo 151794 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B347939 : Blo 151794 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B217009 : Blo 151794 217009 := bstep (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) B162757
theorem B741325 : Blo 151794 741325 := bstep (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) B277997
theorem B413677 : Blo 151794 413677 := bstep (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) B155129
theorem B348209 : Blo 151794 348209 := bstep (se 2 (by rfl) ⟨130578, by rfl⟩ : syracuseStep 348209 = 261157) B261157
theorem B348227 : Blo 151794 348227 := bstep (se 1 (by rfl) ⟨261170, by rfl⟩ : syracuseStep 348227 = 522341) B522341
theorem B1298531 : Blo 151794 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B446627 : Blo 151794 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B577763 : Blo 151794 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B151795 : Blo 151794 151795 := bstep (se 1 (by rfl) ⟨113846, by rfl⟩ : syracuseStep 151795 = 227693) B227693
theorem B217345 : Blo 151794 217345 := bstep (se 2 (by rfl) ⟨81504, by rfl⟩ : syracuseStep 217345 = 163009) B163009
theorem B151811 : Blo 151794 151811 := bstep (se 1 (by rfl) ⟨113858, by rfl⟩ : syracuseStep 151811 = 227717) B227717
theorem B151827 : Blo 151794 151827 := bstep (se 1 (by rfl) ⟨113870, by rfl⟩ : syracuseStep 151827 = 227741) B227741
theorem B151843 : Blo 151794 151843 := bstep (se 1 (by rfl) ⟨113882, by rfl⟩ : syracuseStep 151843 = 227765) B227765
theorem B151859 : Blo 151794 151859 := bstep (se 1 (by rfl) ⟨113894, by rfl⟩ : syracuseStep 151859 = 227789) B227789
theorem B151875 : Blo 151794 151875 := bstep (se 1 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 151875 = 227813) B227813
theorem B348497 : Blo 151794 348497 := bstep (se 2 (by rfl) ⟨130686, by rfl⟩ : syracuseStep 348497 = 261373) B261373
theorem B151891 : Blo 151794 151891 := bstep (se 1 (by rfl) ⟨113918, by rfl⟩ : syracuseStep 151891 = 227837) B227837
theorem B151907 : Blo 151794 151907 := bstep (se 1 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 151907 = 227861) B227861
theorem B348515 : Blo 151794 348515 := bstep (se 1 (by rfl) ⟨261386, by rfl⟩ : syracuseStep 348515 = 522773) B522773
theorem B151923 : Blo 151794 151923 := bstep (se 1 (by rfl) ⟨113942, by rfl⟩ : syracuseStep 151923 = 227885) B227885
theorem B151939 : Blo 151794 151939 := bstep (se 1 (by rfl) ⟨113954, by rfl⟩ : syracuseStep 151939 = 227909) B227909
theorem B151955 : Blo 151794 151955 := bstep (se 1 (by rfl) ⟨113966, by rfl⟩ : syracuseStep 151955 = 227933) B227933
theorem B151971 : Blo 151794 151971 := bstep (se 1 (by rfl) ⟨113978, by rfl⟩ : syracuseStep 151971 = 227957) B227957
theorem B151987 : Blo 151794 151987 := bstep (se 1 (by rfl) ⟨113990, by rfl⟩ : syracuseStep 151987 = 227981) B227981
theorem B152003 : Blo 151794 152003 := bstep (se 1 (by rfl) ⟨114002, by rfl⟩ : syracuseStep 152003 = 228005) B228005
theorem B152019 : Blo 151794 152019 := bstep (se 1 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 152019 = 228029) B228029
theorem B152035 : Blo 151794 152035 := bstep (se 1 (by rfl) ⟨114026, by rfl⟩ : syracuseStep 152035 = 228053) B228053
theorem B1167857 : Blo 151794 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B152051 : Blo 151794 152051 := bstep (se 1 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 152051 = 228077) B228077
theorem B152067 : Blo 151794 152067 := bstep (se 1 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 152067 = 228101) B228101
theorem B152083 : Blo 151794 152083 := bstep (se 1 (by rfl) ⟨114062, by rfl⟩ : syracuseStep 152083 = 228125) B228125
theorem B152099 : Blo 151794 152099 := bstep (se 1 (by rfl) ⟨114074, by rfl⟩ : syracuseStep 152099 = 228149) B228149
theorem B152115 : Blo 151794 152115 := bstep (se 1 (by rfl) ⟨114086, by rfl⟩ : syracuseStep 152115 = 228173) B228173
theorem B152131 : Blo 151794 152131 := bstep (se 1 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 152131 = 228197) B228197
theorem B152147 : Blo 151794 152147 := bstep (se 1 (by rfl) ⟨114110, by rfl⟩ : syracuseStep 152147 = 228221) B228221
theorem B152163 : Blo 151794 152163 := bstep (se 1 (by rfl) ⟨114122, by rfl⟩ : syracuseStep 152163 = 228245) B228245
theorem B512621 : Blo 151794 512621 := bstep (se 3 (by rfl) ⟨96116, by rfl⟩ : syracuseStep 512621 = 192233) B192233
theorem B348785 : Blo 151794 348785 := bstep (se 2 (by rfl) ⟨130794, by rfl⟩ : syracuseStep 348785 = 261589) B261589
theorem B152179 : Blo 151794 152179 := bstep (se 1 (by rfl) ⟨114134, by rfl⟩ : syracuseStep 152179 = 228269) B228269
theorem B152195 : Blo 151794 152195 := bstep (se 1 (by rfl) ⟨114146, by rfl⟩ : syracuseStep 152195 = 228293) B228293
theorem B348803 : Blo 151794 348803 := bstep (se 1 (by rfl) ⟨261602, by rfl⟩ : syracuseStep 348803 = 523205) B523205
theorem B152211 : Blo 151794 152211 := bstep (se 1 (by rfl) ⟨114158, by rfl⟩ : syracuseStep 152211 = 228317) B228317
theorem B512675 : Blo 151794 512675 := bstep (se 1 (by rfl) ⟨384506, by rfl⟩ : syracuseStep 512675 = 769013) B769013
theorem B152227 : Blo 151794 152227 := bstep (se 1 (by rfl) ⟨114170, by rfl⟩ : syracuseStep 152227 = 228341) B228341
theorem B152243 : Blo 151794 152243 := bstep (se 1 (by rfl) ⟨114182, by rfl⟩ : syracuseStep 152243 = 228365) B228365
theorem B152259 : Blo 151794 152259 := bstep (se 1 (by rfl) ⟨114194, by rfl⟩ : syracuseStep 152259 = 228389) B228389
theorem B152275 : Blo 151794 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B152291 : Blo 151794 152291 := bstep (se 1 (by rfl) ⟨114218, by rfl⟩ : syracuseStep 152291 = 228437) B228437
theorem B152307 : Blo 151794 152307 := bstep (se 1 (by rfl) ⟨114230, by rfl⟩ : syracuseStep 152307 = 228461) B228461
theorem B152323 : Blo 151794 152323 := bstep (se 1 (by rfl) ⟨114242, by rfl⟩ : syracuseStep 152323 = 228485) B228485
theorem B152339 : Blo 151794 152339 := bstep (se 1 (by rfl) ⟨114254, by rfl⟩ : syracuseStep 152339 = 228509) B228509
theorem B250643 : Blo 151794 250643 := bstep (se 1 (by rfl) ⟨187982, by rfl⟩ : syracuseStep 250643 = 375965) B375965
theorem B152355 : Blo 151794 152355 := bstep (se 1 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 152355 = 228533) B228533
theorem B873251 : Blo 151794 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B152371 : Blo 151794 152371 := bstep (se 1 (by rfl) ⟨114278, by rfl⟩ : syracuseStep 152371 = 228557) B228557
theorem B152387 : Blo 151794 152387 := bstep (se 1 (by rfl) ⟨114290, by rfl⟩ : syracuseStep 152387 = 228581) B228581
theorem B217937 : Blo 151794 217937 := bstep (se 2 (by rfl) ⟨81726, by rfl⟩ : syracuseStep 217937 = 163453) B163453
theorem B152403 : Blo 151794 152403 := bstep (se 1 (by rfl) ⟨114302, by rfl⟩ : syracuseStep 152403 = 228605) B228605
theorem B152419 : Blo 151794 152419 := bstep (se 1 (by rfl) ⟨114314, by rfl⟩ : syracuseStep 152419 = 228629) B228629
theorem B152435 : Blo 151794 152435 := bstep (se 1 (by rfl) ⟨114326, by rfl⟩ : syracuseStep 152435 = 228653) B228653
theorem B152451 : Blo 151794 152451 := bstep (se 1 (by rfl) ⟨114338, by rfl⟩ : syracuseStep 152451 = 228677) B228677
theorem B349073 : Blo 151794 349073 := bstep (se 2 (by rfl) ⟨130902, by rfl⟩ : syracuseStep 349073 = 261805) B261805
theorem B152467 : Blo 151794 152467 := bstep (se 1 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 152467 = 228701) B228701
theorem B152483 : Blo 151794 152483 := bstep (se 1 (by rfl) ⟨114362, by rfl⟩ : syracuseStep 152483 = 228725) B228725
theorem B349091 : Blo 151794 349091 := bstep (se 1 (by rfl) ⟨261818, by rfl⟩ : syracuseStep 349091 = 523637) B523637
theorem B512945 : Blo 151794 512945 := bstep (se 2 (by rfl) ⟨192354, by rfl⟩ : syracuseStep 512945 = 384709) B384709
theorem B152499 : Blo 151794 152499 := bstep (se 1 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 152499 = 228749) B228749
theorem B152515 : Blo 151794 152515 := bstep (se 1 (by rfl) ⟨114386, by rfl⟩ : syracuseStep 152515 = 228773) B228773
theorem B152531 : Blo 151794 152531 := bstep (se 1 (by rfl) ⟨114398, by rfl⟩ : syracuseStep 152531 = 228797) B228797
theorem B152547 : Blo 151794 152547 := bstep (se 1 (by rfl) ⟨114410, by rfl⟩ : syracuseStep 152547 = 228821) B228821
theorem B152563 : Blo 151794 152563 := bstep (se 1 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 152563 = 228845) B228845
theorem B152579 : Blo 151794 152579 := bstep (se 1 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 152579 = 228869) B228869
theorem B1463309 : Blo 151794 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B152595 : Blo 151794 152595 := bstep (se 1 (by rfl) ⟨114446, by rfl⟩ : syracuseStep 152595 = 228893) B228893
theorem B152611 : Blo 151794 152611 := bstep (se 1 (by rfl) ⟨114458, by rfl⟩ : syracuseStep 152611 = 228917) B228917
theorem B939043 : Blo 151794 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B152627 : Blo 151794 152627 := bstep (se 1 (by rfl) ⟨114470, by rfl⟩ : syracuseStep 152627 = 228941) B228941
theorem B152643 : Blo 151794 152643 := bstep (se 1 (by rfl) ⟨114482, by rfl⟩ : syracuseStep 152643 = 228965) B228965
theorem B152659 : Blo 151794 152659 := bstep (se 1 (by rfl) ⟨114494, by rfl⟩ : syracuseStep 152659 = 228989) B228989
theorem B152675 : Blo 151794 152675 := bstep (se 1 (by rfl) ⟨114506, by rfl⟩ : syracuseStep 152675 = 229013) B229013
theorem B152691 : Blo 151794 152691 := bstep (se 1 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 152691 = 229037) B229037
theorem B152707 : Blo 151794 152707 := bstep (se 1 (by rfl) ⟨114530, by rfl⟩ : syracuseStep 152707 = 229061) B229061
theorem B152723 : Blo 151794 152723 := bstep (se 1 (by rfl) ⟨114542, by rfl⟩ : syracuseStep 152723 = 229085) B229085
theorem B152739 : Blo 151794 152739 := bstep (se 1 (by rfl) ⟨114554, by rfl⟩ : syracuseStep 152739 = 229109) B229109
theorem B775331 : Blo 151794 775331 := bstep (se 1 (by rfl) ⟨581498, by rfl⟩ : syracuseStep 775331 = 1162997) B1162997
theorem B349361 : Blo 151794 349361 := bstep (se 2 (by rfl) ⟨131010, by rfl⟩ : syracuseStep 349361 = 262021) B262021
theorem B152755 : Blo 151794 152755 := bstep (se 1 (by rfl) ⟨114566, by rfl⟩ : syracuseStep 152755 = 229133) B229133
theorem B152771 : Blo 151794 152771 := bstep (se 1 (by rfl) ⟨114578, by rfl⟩ : syracuseStep 152771 = 229157) B229157
theorem B349379 : Blo 151794 349379 := bstep (se 1 (by rfl) ⟨262034, by rfl⟩ : syracuseStep 349379 = 524069) B524069
theorem B578765 : Blo 151794 578765 := bstep (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) B217037
theorem B152787 : Blo 151794 152787 := bstep (se 1 (by rfl) ⟨114590, by rfl⟩ : syracuseStep 152787 = 229181) B229181
theorem B939235 : Blo 151794 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B152803 : Blo 151794 152803 := bstep (se 1 (by rfl) ⟨114602, by rfl⟩ : syracuseStep 152803 = 229205) B229205
theorem B152819 : Blo 151794 152819 := bstep (se 1 (by rfl) ⟨114614, by rfl⟩ : syracuseStep 152819 = 229229) B229229
theorem B152835 : Blo 151794 152835 := bstep (se 1 (by rfl) ⟨114626, by rfl⟩ : syracuseStep 152835 = 229253) B229253
theorem B152851 : Blo 151794 152851 := bstep (se 1 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 152851 = 229277) B229277
theorem B152867 : Blo 151794 152867 := bstep (se 1 (by rfl) ⟨114650, by rfl⟩ : syracuseStep 152867 = 229301) B229301
theorem B152883 : Blo 151794 152883 := bstep (se 1 (by rfl) ⟨114662, by rfl⟩ : syracuseStep 152883 = 229325) B229325
theorem B152899 : Blo 151794 152899 := bstep (se 1 (by rfl) ⟨114674, by rfl⟩ : syracuseStep 152899 = 229349) B229349
theorem B152915 : Blo 151794 152915 := bstep (se 1 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 152915 = 229373) B229373
theorem B152931 : Blo 151794 152931 := bstep (se 1 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 152931 = 229397) B229397
theorem B218467 : Blo 151794 218467 := bstep (se 1 (by rfl) ⟨163850, by rfl⟩ : syracuseStep 218467 = 327701) B327701
theorem B152947 : Blo 151794 152947 := bstep (se 1 (by rfl) ⟨114710, by rfl⟩ : syracuseStep 152947 = 229421) B229421
theorem B152963 : Blo 151794 152963 := bstep (se 1 (by rfl) ⟨114722, by rfl⟩ : syracuseStep 152963 = 229445) B229445
theorem B152979 : Blo 151794 152979 := bstep (se 1 (by rfl) ⟨114734, by rfl⟩ : syracuseStep 152979 = 229469) B229469
theorem B152995 : Blo 151794 152995 := bstep (se 1 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 152995 = 229493) B229493
theorem B153011 : Blo 151794 153011 := bstep (se 1 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 153011 = 229517) B229517
theorem B153027 : Blo 151794 153027 := bstep (se 1 (by rfl) ⟨114770, by rfl⟩ : syracuseStep 153027 = 229541) B229541
theorem B513485 : Blo 151794 513485 := bstep (se 3 (by rfl) ⟨96278, by rfl⟩ : syracuseStep 513485 = 192557) B192557
theorem B415181 : Blo 151794 415181 := bstep (se 3 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 415181 = 155693) B155693
theorem B349649 : Blo 151794 349649 := bstep (se 2 (by rfl) ⟨131118, by rfl⟩ : syracuseStep 349649 = 262237) B262237
theorem B153043 : Blo 151794 153043 := bstep (se 1 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 153043 = 229565) B229565
theorem B153059 : Blo 151794 153059 := bstep (se 1 (by rfl) ⟨114794, by rfl⟩ : syracuseStep 153059 = 229589) B229589
theorem B349667 : Blo 151794 349667 := bstep (se 1 (by rfl) ⟨262250, by rfl⟩ : syracuseStep 349667 = 524501) B524501
theorem B153075 : Blo 151794 153075 := bstep (se 1 (by rfl) ⟨114806, by rfl⟩ : syracuseStep 153075 = 229613) B229613
theorem B513539 : Blo 151794 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B153091 : Blo 151794 153091 := bstep (se 1 (by rfl) ⟨114818, by rfl⟩ : syracuseStep 153091 = 229637) B229637
theorem B153107 : Blo 151794 153107 := bstep (se 1 (by rfl) ⟨114830, by rfl⟩ : syracuseStep 153107 = 229661) B229661
theorem B153123 : Blo 151794 153123 := bstep (se 1 (by rfl) ⟨114842, by rfl⟩ : syracuseStep 153123 = 229685) B229685
theorem B415277 : Blo 151794 415277 := bstep (se 3 (by rfl) ⟨77864, by rfl⟩ : syracuseStep 415277 = 155729) B155729
theorem B153139 : Blo 151794 153139 := bstep (se 1 (by rfl) ⟨114854, by rfl⟩ : syracuseStep 153139 = 229709) B229709
theorem B153155 : Blo 151794 153155 := bstep (se 1 (by rfl) ⟨114866, by rfl⟩ : syracuseStep 153155 = 229733) B229733
theorem B153171 : Blo 151794 153171 := bstep (se 1 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 153171 = 229757) B229757
theorem B153187 : Blo 151794 153187 := bstep (se 1 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 153187 = 229781) B229781
theorem B153203 : Blo 151794 153203 := bstep (se 1 (by rfl) ⟨114902, by rfl⟩ : syracuseStep 153203 = 229805) B229805
theorem B153219 : Blo 151794 153219 := bstep (se 1 (by rfl) ⟨114914, by rfl⟩ : syracuseStep 153219 = 229829) B229829
theorem B415363 : Blo 151794 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B153235 : Blo 151794 153235 := bstep (se 1 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 153235 = 229853) B229853
theorem B153251 : Blo 151794 153251 := bstep (se 1 (by rfl) ⟨114938, by rfl⟩ : syracuseStep 153251 = 229877) B229877
theorem B153267 : Blo 151794 153267 := bstep (se 1 (by rfl) ⟨114950, by rfl⟩ : syracuseStep 153267 = 229901) B229901
theorem B218803 : Blo 151794 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B153283 : Blo 151794 153283 := bstep (se 1 (by rfl) ⟨114962, by rfl⟩ : syracuseStep 153283 = 229925) B229925
theorem B153299 : Blo 151794 153299 := bstep (se 1 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 153299 = 229949) B229949
theorem B153315 : Blo 151794 153315 := bstep (se 1 (by rfl) ⟨114986, by rfl⟩ : syracuseStep 153315 = 229973) B229973
theorem B2119409 : Blo 151794 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B349937 : Blo 151794 349937 := bstep (se 2 (by rfl) ⟨131226, by rfl⟩ : syracuseStep 349937 = 262453) B262453
theorem B153331 : Blo 151794 153331 := bstep (se 1 (by rfl) ⟨114998, by rfl⟩ : syracuseStep 153331 = 229997) B229997
theorem B153347 : Blo 151794 153347 := bstep (se 1 (by rfl) ⟨115010, by rfl⟩ : syracuseStep 153347 = 230021) B230021
theorem B349955 : Blo 151794 349955 := bstep (se 1 (by rfl) ⟨262466, by rfl⟩ : syracuseStep 349955 = 524933) B524933
theorem B874253 : Blo 151794 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B513809 : Blo 151794 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B153363 : Blo 151794 153363 := bstep (se 1 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 153363 = 230045) B230045
theorem B153379 : Blo 151794 153379 := bstep (se 1 (by rfl) ⟨115034, by rfl⟩ : syracuseStep 153379 = 230069) B230069
theorem B153395 : Blo 151794 153395 := bstep (se 1 (by rfl) ⟨115046, by rfl⟩ : syracuseStep 153395 = 230093) B230093
theorem B153411 : Blo 151794 153411 := bstep (se 1 (by rfl) ⟨115058, by rfl⟩ : syracuseStep 153411 = 230117) B230117
theorem B153427 : Blo 151794 153427 := bstep (se 1 (by rfl) ⟨115070, by rfl⟩ : syracuseStep 153427 = 230141) B230141
theorem B153443 : Blo 151794 153443 := bstep (se 1 (by rfl) ⟨115082, by rfl⟩ : syracuseStep 153443 = 230165) B230165
theorem B153459 : Blo 151794 153459 := bstep (se 1 (by rfl) ⟨115094, by rfl⟩ : syracuseStep 153459 = 230189) B230189
theorem B153475 : Blo 151794 153475 := bstep (se 1 (by rfl) ⟨115106, by rfl⟩ : syracuseStep 153475 = 230213) B230213
theorem B153491 : Blo 151794 153491 := bstep (se 1 (by rfl) ⟨115118, by rfl⟩ : syracuseStep 153491 = 230237) B230237
theorem B153507 : Blo 151794 153507 := bstep (se 1 (by rfl) ⟨115130, by rfl⟩ : syracuseStep 153507 = 230261) B230261
theorem B153523 : Blo 151794 153523 := bstep (se 1 (by rfl) ⟨115142, by rfl⟩ : syracuseStep 153523 = 230285) B230285
theorem B153539 : Blo 151794 153539 := bstep (se 1 (by rfl) ⟨115154, by rfl⟩ : syracuseStep 153539 = 230309) B230309
theorem B776141 : Blo 151794 776141 := bstep (se 3 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 776141 = 291053) B291053
theorem B153555 : Blo 151794 153555 := bstep (se 1 (by rfl) ⟨115166, by rfl⟩ : syracuseStep 153555 = 230333) B230333
theorem B153571 : Blo 151794 153571 := bstep (se 1 (by rfl) ⟨115178, by rfl⟩ : syracuseStep 153571 = 230357) B230357
theorem B153587 : Blo 151794 153587 := bstep (se 1 (by rfl) ⟨115190, by rfl⟩ : syracuseStep 153587 = 230381) B230381
theorem B153603 : Blo 151794 153603 := bstep (se 1 (by rfl) ⟨115202, by rfl⟩ : syracuseStep 153603 = 230405) B230405
theorem B350225 : Blo 151794 350225 := bstep (se 2 (by rfl) ⟨131334, by rfl⟩ : syracuseStep 350225 = 262669) B262669
theorem B153619 : Blo 151794 153619 := bstep (se 1 (by rfl) ⟨115214, by rfl⟩ : syracuseStep 153619 = 230429) B230429
theorem B153635 : Blo 151794 153635 := bstep (se 1 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 153635 = 230453) B230453
theorem B350243 : Blo 151794 350243 := bstep (se 1 (by rfl) ⟨262682, by rfl⟩ : syracuseStep 350243 = 525365) B525365
theorem B153651 : Blo 151794 153651 := bstep (se 1 (by rfl) ⟨115238, by rfl⟩ : syracuseStep 153651 = 230477) B230477
theorem B153667 : Blo 151794 153667 := bstep (se 1 (by rfl) ⟨115250, by rfl⟩ : syracuseStep 153667 = 230501) B230501
theorem B153683 : Blo 151794 153683 := bstep (se 1 (by rfl) ⟨115262, by rfl⟩ : syracuseStep 153683 = 230525) B230525
theorem B153699 : Blo 151794 153699 := bstep (se 1 (by rfl) ⟨115274, by rfl⟩ : syracuseStep 153699 = 230549) B230549
theorem B153715 : Blo 151794 153715 := bstep (se 1 (by rfl) ⟨115286, by rfl⟩ : syracuseStep 153715 = 230573) B230573
theorem B153731 : Blo 151794 153731 := bstep (se 1 (by rfl) ⟨115298, by rfl⟩ : syracuseStep 153731 = 230597) B230597
theorem B186499 : Blo 151794 186499 := bstep (se 1 (by rfl) ⟨139874, by rfl⟩ : syracuseStep 186499 = 279749) B279749
theorem B3528845 : Blo 151794 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B153747 : Blo 151794 153747 := bstep (se 1 (by rfl) ⟨115310, by rfl⟩ : syracuseStep 153747 = 230621) B230621
theorem B153763 : Blo 151794 153763 := bstep (se 1 (by rfl) ⟨115322, by rfl⟩ : syracuseStep 153763 = 230645) B230645
theorem B153779 : Blo 151794 153779 := bstep (se 1 (by rfl) ⟨115334, by rfl⟩ : syracuseStep 153779 = 230669) B230669
theorem B219329 : Blo 151794 219329 := bstep (se 2 (by rfl) ⟨82248, by rfl⟩ : syracuseStep 219329 = 164497) B164497
theorem B153795 : Blo 151794 153795 := bstep (se 1 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 153795 = 230693) B230693
theorem B153811 : Blo 151794 153811 := bstep (se 1 (by rfl) ⟨115358, by rfl⟩ : syracuseStep 153811 = 230717) B230717
theorem B219361 : Blo 151794 219361 := bstep (se 2 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 219361 = 164521) B164521
theorem B153827 : Blo 151794 153827 := bstep (se 1 (by rfl) ⟨115370, by rfl⟩ : syracuseStep 153827 = 230741) B230741
theorem B153843 : Blo 151794 153843 := bstep (se 1 (by rfl) ⟨115382, by rfl⟩ : syracuseStep 153843 = 230765) B230765
theorem B153859 : Blo 151794 153859 := bstep (se 1 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 153859 = 230789) B230789
theorem B219395 : Blo 151794 219395 := bstep (se 1 (by rfl) ⟨164546, by rfl⟩ : syracuseStep 219395 = 329093) B329093
theorem B153875 : Blo 151794 153875 := bstep (se 1 (by rfl) ⟨115406, by rfl⟩ : syracuseStep 153875 = 230813) B230813
theorem B153891 : Blo 151794 153891 := bstep (se 1 (by rfl) ⟨115418, by rfl⟩ : syracuseStep 153891 = 230837) B230837
theorem B514349 : Blo 151794 514349 := bstep (se 3 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 514349 = 192881) B192881
theorem B350513 : Blo 151794 350513 := bstep (se 2 (by rfl) ⟨131442, by rfl⟩ : syracuseStep 350513 = 262885) B262885
theorem B153907 : Blo 151794 153907 := bstep (se 1 (by rfl) ⟨115430, by rfl⟩ : syracuseStep 153907 = 230861) B230861
theorem B153923 : Blo 151794 153923 := bstep (se 1 (by rfl) ⟨115442, by rfl⟩ : syracuseStep 153923 = 230885) B230885
theorem B350531 : Blo 151794 350531 := bstep (se 1 (by rfl) ⟨262898, by rfl⟩ : syracuseStep 350531 = 525797) B525797
theorem B973133 : Blo 151794 973133 := bstep (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) B364925
theorem B153939 : Blo 151794 153939 := bstep (se 1 (by rfl) ⟨115454, by rfl⟩ : syracuseStep 153939 = 230909) B230909
theorem B514403 : Blo 151794 514403 := bstep (se 1 (by rfl) ⟨385802, by rfl⟩ : syracuseStep 514403 = 771605) B771605
theorem B153955 : Blo 151794 153955 := bstep (se 1 (by rfl) ⟨115466, by rfl⟩ : syracuseStep 153955 = 230933) B230933
theorem B153971 : Blo 151794 153971 := bstep (se 1 (by rfl) ⟨115478, by rfl⟩ : syracuseStep 153971 = 230957) B230957
theorem B153987 : Blo 151794 153987 := bstep (se 1 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 153987 = 230981) B230981
theorem B154003 : Blo 151794 154003 := bstep (se 1 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 154003 = 231005) B231005
theorem B154019 : Blo 151794 154019 := bstep (se 1 (by rfl) ⟨115514, by rfl⟩ : syracuseStep 154019 = 231029) B231029
theorem B743843 : Blo 151794 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B154035 : Blo 151794 154035 := bstep (se 1 (by rfl) ⟨115526, by rfl⟩ : syracuseStep 154035 = 231053) B231053
theorem B154051 : Blo 151794 154051 := bstep (se 1 (by rfl) ⟨115538, by rfl⟩ : syracuseStep 154051 = 231077) B231077
theorem B154067 : Blo 151794 154067 := bstep (se 1 (by rfl) ⟨115550, by rfl⟩ : syracuseStep 154067 = 231101) B231101
theorem B186835 : Blo 151794 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B154083 : Blo 151794 154083 := bstep (se 1 (by rfl) ⟨115562, by rfl⟩ : syracuseStep 154083 = 231125) B231125
theorem B154099 : Blo 151794 154099 := bstep (se 1 (by rfl) ⟨115574, by rfl⟩ : syracuseStep 154099 = 231149) B231149
theorem B154115 : Blo 151794 154115 := bstep (se 1 (by rfl) ⟨115586, by rfl⟩ : syracuseStep 154115 = 231173) B231173
theorem B154131 : Blo 151794 154131 := bstep (se 1 (by rfl) ⟨115598, by rfl⟩ : syracuseStep 154131 = 231197) B231197
theorem B154147 : Blo 151794 154147 := bstep (se 1 (by rfl) ⟨115610, by rfl⟩ : syracuseStep 154147 = 231221) B231221
theorem B154163 : Blo 151794 154163 := bstep (se 1 (by rfl) ⟨115622, by rfl⟩ : syracuseStep 154163 = 231245) B231245
theorem B154179 : Blo 151794 154179 := bstep (se 1 (by rfl) ⟨115634, by rfl⟩ : syracuseStep 154179 = 231269) B231269
theorem B154195 : Blo 151794 154195 := bstep (se 1 (by rfl) ⟨115646, by rfl⟩ : syracuseStep 154195 = 231293) B231293
theorem B154211 : Blo 151794 154211 := bstep (se 1 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 154211 = 231317) B231317
theorem B514673 : Blo 151794 514673 := bstep (se 2 (by rfl) ⟨193002, by rfl⟩ : syracuseStep 514673 = 386005) B386005
theorem B154227 : Blo 151794 154227 := bstep (se 1 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 154227 = 231341) B231341
theorem B154243 : Blo 151794 154243 := bstep (se 1 (by rfl) ⟨115682, by rfl⟩ : syracuseStep 154243 = 231365) B231365
theorem B154259 : Blo 151794 154259 := bstep (se 1 (by rfl) ⟨115694, by rfl⟩ : syracuseStep 154259 = 231389) B231389
theorem B154275 : Blo 151794 154275 := bstep (se 1 (by rfl) ⟨115706, by rfl⟩ : syracuseStep 154275 = 231413) B231413
theorem B154291 : Blo 151794 154291 := bstep (se 1 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 154291 = 231437) B231437
theorem B154307 : Blo 151794 154307 := bstep (se 1 (by rfl) ⟨115730, by rfl⟩ : syracuseStep 154307 = 231461) B231461
theorem B154323 : Blo 151794 154323 := bstep (se 1 (by rfl) ⟨115742, by rfl⟩ : syracuseStep 154323 = 231485) B231485
theorem B154339 : Blo 151794 154339 := bstep (se 1 (by rfl) ⟨115754, by rfl⟩ : syracuseStep 154339 = 231509) B231509
theorem B154355 : Blo 151794 154355 := bstep (se 1 (by rfl) ⟨115766, by rfl⟩ : syracuseStep 154355 = 231533) B231533
theorem B154371 : Blo 151794 154371 := bstep (se 1 (by rfl) ⟨115778, by rfl⟩ : syracuseStep 154371 = 231557) B231557
theorem B154387 : Blo 151794 154387 := bstep (se 1 (by rfl) ⟨115790, by rfl⟩ : syracuseStep 154387 = 231581) B231581
theorem B154403 : Blo 151794 154403 := bstep (se 1 (by rfl) ⟨115802, by rfl⟩ : syracuseStep 154403 = 231605) B231605
theorem B219953 : Blo 151794 219953 := bstep (se 2 (by rfl) ⟨82482, by rfl⟩ : syracuseStep 219953 = 164965) B164965
theorem B154419 : Blo 151794 154419 := bstep (se 1 (by rfl) ⟨115814, by rfl⟩ : syracuseStep 154419 = 231629) B231629
theorem B154435 : Blo 151794 154435 := bstep (se 1 (by rfl) ⟨115826, by rfl⟩ : syracuseStep 154435 = 231653) B231653
theorem B154451 : Blo 151794 154451 := bstep (se 1 (by rfl) ⟨115838, by rfl⟩ : syracuseStep 154451 = 231677) B231677
theorem B154467 : Blo 151794 154467 := bstep (se 1 (by rfl) ⟨115850, by rfl⟩ : syracuseStep 154467 = 231701) B231701
theorem B154483 : Blo 151794 154483 := bstep (se 1 (by rfl) ⟨115862, by rfl⟩ : syracuseStep 154483 = 231725) B231725
theorem B220033 : Blo 151794 220033 := bstep (se 2 (by rfl) ⟨82512, by rfl⟩ : syracuseStep 220033 = 165025) B165025
theorem B154499 : Blo 151794 154499 := bstep (se 1 (by rfl) ⟨115874, by rfl⟩ : syracuseStep 154499 = 231749) B231749
theorem B154515 : Blo 151794 154515 := bstep (se 1 (by rfl) ⟨115886, by rfl⟩ : syracuseStep 154515 = 231773) B231773
theorem B154531 : Blo 151794 154531 := bstep (se 1 (by rfl) ⟨115898, by rfl⟩ : syracuseStep 154531 = 231797) B231797
theorem B154547 : Blo 151794 154547 := bstep (se 1 (by rfl) ⟨115910, by rfl⟩ : syracuseStep 154547 = 231821) B231821
theorem B154563 : Blo 151794 154563 := bstep (se 1 (by rfl) ⟨115922, by rfl⟩ : syracuseStep 154563 = 231845) B231845
theorem B154579 : Blo 151794 154579 := bstep (se 1 (by rfl) ⟨115934, by rfl⟩ : syracuseStep 154579 = 231869) B231869
theorem B154595 : Blo 151794 154595 := bstep (se 1 (by rfl) ⟨115946, by rfl⟩ : syracuseStep 154595 = 231893) B231893
theorem B154611 : Blo 151794 154611 := bstep (se 1 (by rfl) ⟨115958, by rfl⟩ : syracuseStep 154611 = 231917) B231917
theorem B154627 : Blo 151794 154627 := bstep (se 1 (by rfl) ⟨115970, by rfl⟩ : syracuseStep 154627 = 231941) B231941
theorem B154643 : Blo 151794 154643 := bstep (se 1 (by rfl) ⟨115982, by rfl⟩ : syracuseStep 154643 = 231965) B231965
theorem B154659 : Blo 151794 154659 := bstep (se 1 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 154659 = 231989) B231989
theorem B744497 : Blo 151794 744497 := bstep (se 2 (by rfl) ⟨279186, by rfl⟩ : syracuseStep 744497 = 558373) B558373
theorem B154675 : Blo 151794 154675 := bstep (se 1 (by rfl) ⟨116006, by rfl⟩ : syracuseStep 154675 = 232013) B232013
theorem B154691 : Blo 151794 154691 := bstep (se 1 (by rfl) ⟨116018, by rfl⟩ : syracuseStep 154691 = 232037) B232037
theorem B515153 : Blo 151794 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B154707 : Blo 151794 154707 := bstep (se 1 (by rfl) ⟨116030, by rfl⟩ : syracuseStep 154707 = 232061) B232061
theorem B154723 : Blo 151794 154723 := bstep (se 1 (by rfl) ⟨116042, by rfl⟩ : syracuseStep 154723 = 232085) B232085
theorem B154739 : Blo 151794 154739 := bstep (se 1 (by rfl) ⟨116054, by rfl⟩ : syracuseStep 154739 = 232109) B232109
theorem B154755 : Blo 151794 154755 := bstep (se 1 (by rfl) ⟨116066, by rfl⟩ : syracuseStep 154755 = 232133) B232133
theorem B515213 : Blo 151794 515213 := bstep (se 3 (by rfl) ⟨96602, by rfl⟩ : syracuseStep 515213 = 193205) B193205
theorem B154771 : Blo 151794 154771 := bstep (se 1 (by rfl) ⟨116078, by rfl⟩ : syracuseStep 154771 = 232157) B232157
theorem B154787 : Blo 151794 154787 := bstep (se 1 (by rfl) ⟨116090, by rfl⟩ : syracuseStep 154787 = 232181) B232181
theorem B154803 : Blo 151794 154803 := bstep (se 1 (by rfl) ⟨116102, by rfl⟩ : syracuseStep 154803 = 232205) B232205
theorem B515267 : Blo 151794 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B154819 : Blo 151794 154819 := bstep (se 1 (by rfl) ⟨116114, by rfl⟩ : syracuseStep 154819 = 232229) B232229
theorem B154835 : Blo 151794 154835 := bstep (se 1 (by rfl) ⟨116126, by rfl⟩ : syracuseStep 154835 = 232253) B232253
theorem B154851 : Blo 151794 154851 := bstep (se 1 (by rfl) ⟨116138, by rfl⟩ : syracuseStep 154851 = 232277) B232277
theorem B154867 : Blo 151794 154867 := bstep (se 1 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 154867 = 232301) B232301
theorem B154883 : Blo 151794 154883 := bstep (se 1 (by rfl) ⟨116162, by rfl⟩ : syracuseStep 154883 = 232325) B232325
theorem B580877 : Blo 151794 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B154899 : Blo 151794 154899 := bstep (se 1 (by rfl) ⟨116174, by rfl⟩ : syracuseStep 154899 = 232349) B232349
theorem B154915 : Blo 151794 154915 := bstep (se 1 (by rfl) ⟨116186, by rfl⟩ : syracuseStep 154915 = 232373) B232373
theorem B154931 : Blo 151794 154931 := bstep (se 1 (by rfl) ⟨116198, by rfl⟩ : syracuseStep 154931 = 232397) B232397
theorem B154947 : Blo 151794 154947 := bstep (se 1 (by rfl) ⟨116210, by rfl⟩ : syracuseStep 154947 = 232421) B232421
theorem B154963 : Blo 151794 154963 := bstep (se 1 (by rfl) ⟨116222, by rfl⟩ : syracuseStep 154963 = 232445) B232445
theorem B154979 : Blo 151794 154979 := bstep (se 1 (by rfl) ⟨116234, by rfl⟩ : syracuseStep 154979 = 232469) B232469
theorem B154995 : Blo 151794 154995 := bstep (se 1 (by rfl) ⟨116246, by rfl⟩ : syracuseStep 154995 = 232493) B232493
theorem B155011 : Blo 151794 155011 := bstep (se 1 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 155011 = 232517) B232517
theorem B155027 : Blo 151794 155027 := bstep (se 1 (by rfl) ⟨116270, by rfl⟩ : syracuseStep 155027 = 232541) B232541
theorem B155043 : Blo 151794 155043 := bstep (se 1 (by rfl) ⟨116282, by rfl⟩ : syracuseStep 155043 = 232565) B232565
theorem B155059 : Blo 151794 155059 := bstep (se 1 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 155059 = 232589) B232589
theorem B155075 : Blo 151794 155075 := bstep (se 1 (by rfl) ⟨116306, by rfl⟩ : syracuseStep 155075 = 232613) B232613
theorem B515537 : Blo 151794 515537 := bstep (se 2 (by rfl) ⟨193326, by rfl⟩ : syracuseStep 515537 = 386653) B386653
theorem B155091 : Blo 151794 155091 := bstep (se 1 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 155091 = 232637) B232637
theorem B155107 : Blo 151794 155107 := bstep (se 1 (by rfl) ⟨116330, by rfl⟩ : syracuseStep 155107 = 232661) B232661
theorem B384497 : Blo 151794 384497 := bstep (se 2 (by rfl) ⟨144186, by rfl⟩ : syracuseStep 384497 = 288373) B288373
theorem B155123 : Blo 151794 155123 := bstep (se 1 (by rfl) ⟨116342, by rfl⟩ : syracuseStep 155123 = 232685) B232685
theorem B155139 : Blo 151794 155139 := bstep (se 1 (by rfl) ⟨116354, by rfl⟩ : syracuseStep 155139 = 232709) B232709
theorem B155155 : Blo 151794 155155 := bstep (se 1 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 155155 = 232733) B232733
theorem B3923477 : Blo 151794 3923477 := bstep (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) B183913
theorem B384547 : Blo 151794 384547 := bstep (se 1 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 384547 = 576821) B576821
theorem B155171 : Blo 151794 155171 := bstep (se 1 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 155171 = 232757) B232757
theorem B155187 : Blo 151794 155187 := bstep (se 1 (by rfl) ⟨116390, by rfl⟩ : syracuseStep 155187 = 232781) B232781
theorem B2022965 : Blo 151794 2022965 := bstep (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) B189653
theorem B155203 : Blo 151794 155203 := bstep (se 1 (by rfl) ⟨116402, by rfl⟩ : syracuseStep 155203 = 232805) B232805
theorem B155219 : Blo 151794 155219 := bstep (se 1 (by rfl) ⟨116414, by rfl⟩ : syracuseStep 155219 = 232829) B232829
theorem B155235 : Blo 151794 155235 := bstep (se 1 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 155235 = 232853) B232853
theorem B155251 : Blo 151794 155251 := bstep (se 1 (by rfl) ⟨116438, by rfl⟩ : syracuseStep 155251 = 232877) B232877
theorem B155267 : Blo 151794 155267 := bstep (se 1 (by rfl) ⟨116450, by rfl⟩ : syracuseStep 155267 = 232901) B232901
theorem B220819 : Blo 151794 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B155283 : Blo 151794 155283 := bstep (se 1 (by rfl) ⟨116462, by rfl⟩ : syracuseStep 155283 = 232925) B232925
theorem B155299 : Blo 151794 155299 := bstep (se 1 (by rfl) ⟨116474, by rfl⟩ : syracuseStep 155299 = 232949) B232949
theorem B384689 : Blo 151794 384689 := bstep (se 2 (by rfl) ⟨144258, by rfl⟩ : syracuseStep 384689 = 288517) B288517
theorem B155315 : Blo 151794 155315 := bstep (se 1 (by rfl) ⟨116486, by rfl⟩ : syracuseStep 155315 = 232973) B232973
theorem B155331 : Blo 151794 155331 := bstep (se 1 (by rfl) ⟨116498, by rfl⟩ : syracuseStep 155331 = 232997) B232997
theorem B155347 : Blo 151794 155347 := bstep (se 1 (by rfl) ⟨116510, by rfl⟩ : syracuseStep 155347 = 233021) B233021
theorem B155363 : Blo 151794 155363 := bstep (se 1 (by rfl) ⟨116522, by rfl⟩ : syracuseStep 155363 = 233045) B233045
theorem B155379 : Blo 151794 155379 := bstep (se 1 (by rfl) ⟨116534, by rfl⟩ : syracuseStep 155379 = 233069) B233069
theorem B155395 : Blo 151794 155395 := bstep (se 1 (by rfl) ⟨116546, by rfl⟩ : syracuseStep 155395 = 233093) B233093
theorem B155411 : Blo 151794 155411 := bstep (se 1 (by rfl) ⟨116558, by rfl⟩ : syracuseStep 155411 = 233117) B233117
theorem B155427 : Blo 151794 155427 := bstep (se 1 (by rfl) ⟨116570, by rfl⟩ : syracuseStep 155427 = 233141) B233141
theorem B548657 : Blo 151794 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B155443 : Blo 151794 155443 := bstep (se 1 (by rfl) ⟨116582, by rfl⟩ : syracuseStep 155443 = 233165) B233165
theorem B155459 : Blo 151794 155459 := bstep (se 1 (by rfl) ⟨116594, by rfl⟩ : syracuseStep 155459 = 233189) B233189
theorem B155475 : Blo 151794 155475 := bstep (se 1 (by rfl) ⟨116606, by rfl⟩ : syracuseStep 155475 = 233213) B233213
theorem B155491 : Blo 151794 155491 := bstep (se 1 (by rfl) ⟨116618, by rfl⟩ : syracuseStep 155491 = 233237) B233237
theorem B155507 : Blo 151794 155507 := bstep (se 1 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 155507 = 233261) B233261
theorem B155523 : Blo 151794 155523 := bstep (se 1 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 155523 = 233285) B233285
theorem B155539 : Blo 151794 155539 := bstep (se 1 (by rfl) ⟨116654, by rfl⟩ : syracuseStep 155539 = 233309) B233309
theorem B745379 : Blo 151794 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B155555 : Blo 151794 155555 := bstep (se 1 (by rfl) ⟨116666, by rfl⟩ : syracuseStep 155555 = 233333) B233333
theorem B155571 : Blo 151794 155571 := bstep (se 1 (by rfl) ⟨116678, by rfl⟩ : syracuseStep 155571 = 233357) B233357
theorem B155587 : Blo 151794 155587 := bstep (se 1 (by rfl) ⟨116690, by rfl⟩ : syracuseStep 155587 = 233381) B233381
theorem B155603 : Blo 151794 155603 := bstep (se 1 (by rfl) ⟨116702, by rfl⟩ : syracuseStep 155603 = 233405) B233405
theorem B155619 : Blo 151794 155619 := bstep (se 1 (by rfl) ⟨116714, by rfl⟩ : syracuseStep 155619 = 233429) B233429
theorem B516077 : Blo 151794 516077 := bstep (se 3 (by rfl) ⟨96764, by rfl⟩ : syracuseStep 516077 = 193529) B193529
theorem B155635 : Blo 151794 155635 := bstep (se 1 (by rfl) ⟨116726, by rfl⟩ : syracuseStep 155635 = 233453) B233453
theorem B155651 : Blo 151794 155651 := bstep (se 1 (by rfl) ⟨116738, by rfl⟩ : syracuseStep 155651 = 233477) B233477
theorem B155667 : Blo 151794 155667 := bstep (se 1 (by rfl) ⟨116750, by rfl⟩ : syracuseStep 155667 = 233501) B233501
theorem B516131 : Blo 151794 516131 := bstep (se 1 (by rfl) ⟨387098, by rfl⟩ : syracuseStep 516131 = 774197) B774197
theorem B155683 : Blo 151794 155683 := bstep (se 1 (by rfl) ⟨116762, by rfl⟩ : syracuseStep 155683 = 233525) B233525
theorem B581681 : Blo 151794 581681 := bstep (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) B436261
theorem B155699 : Blo 151794 155699 := bstep (se 1 (by rfl) ⟨116774, by rfl⟩ : syracuseStep 155699 = 233549) B233549
theorem B155715 : Blo 151794 155715 := bstep (se 1 (by rfl) ⟨116786, by rfl⟩ : syracuseStep 155715 = 233573) B233573
theorem B155731 : Blo 151794 155731 := bstep (se 1 (by rfl) ⟨116798, by rfl⟩ : syracuseStep 155731 = 233597) B233597
theorem B155747 : Blo 151794 155747 := bstep (se 1 (by rfl) ⟨116810, by rfl⟩ : syracuseStep 155747 = 233621) B233621
theorem B221297 : Blo 151794 221297 := bstep (se 2 (by rfl) ⟨82986, by rfl⟩ : syracuseStep 221297 = 165973) B165973
theorem B155763 : Blo 151794 155763 := bstep (se 1 (by rfl) ⟨116822, by rfl⟩ : syracuseStep 155763 = 233645) B233645
theorem B155779 : Blo 151794 155779 := bstep (se 1 (by rfl) ⟨116834, by rfl⟩ : syracuseStep 155779 = 233669) B233669
theorem B745649 : Blo 151794 745649 := bstep (se 2 (by rfl) ⟨279618, by rfl⟩ : syracuseStep 745649 = 559237) B559237
theorem B221411 : Blo 151794 221411 := bstep (se 1 (by rfl) ⟨166058, by rfl⟩ : syracuseStep 221411 = 332117) B332117
theorem B516401 : Blo 151794 516401 := bstep (se 2 (by rfl) ⟨193650, by rfl⟩ : syracuseStep 516401 = 387301) B387301
theorem B221491 : Blo 151794 221491 := bstep (se 1 (by rfl) ⟨166118, by rfl⟩ : syracuseStep 221491 = 332237) B332237
theorem B1466693 : Blo 151794 1466693 := bstep (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) B275005
theorem B549347 : Blo 151794 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B877169 : Blo 151794 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B385681 : Blo 151794 385681 := bstep (se 2 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 385681 = 289261) B289261
theorem B582349 : Blo 151794 582349 := bstep (se 3 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 582349 = 218381) B218381
theorem B1008389 : Blo 151794 1008389 := bstep (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) B189073
theorem B254755 : Blo 151794 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B779057 : Blo 151794 779057 := bstep (se 2 (by rfl) ⟨292146, by rfl⟩ : syracuseStep 779057 = 584293) B584293
theorem B516941 : Blo 151794 516941 := bstep (se 3 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 516941 = 193853) B193853
theorem B1991537 : Blo 151794 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B516995 : Blo 151794 516995 := bstep (se 1 (by rfl) ⟨387746, by rfl⟩ : syracuseStep 516995 = 775493) B775493
theorem B385955 : Blo 151794 385955 := bstep (se 1 (by rfl) ⟨289466, by rfl⟩ : syracuseStep 385955 = 578933) B578933
theorem B746417 : Blo 151794 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B1172465 : Blo 151794 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B386147 : Blo 151794 386147 := bstep (se 1 (by rfl) ⟨289610, by rfl⟩ : syracuseStep 386147 = 579221) B579221
theorem B517265 : Blo 151794 517265 := bstep (se 2 (by rfl) ⟨193974, by rfl⟩ : syracuseStep 517265 = 387949) B387949
theorem B583139 : Blo 151794 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B3630563 : Blo 151794 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B517805 : Blo 151794 517805 := bstep (se 3 (by rfl) ⟨97088, by rfl⟩ : syracuseStep 517805 = 194177) B194177
theorem B517859 : Blo 151794 517859 := bstep (se 1 (by rfl) ⟨388394, by rfl⟩ : syracuseStep 517859 = 776789) B776789
theorem B288593 : Blo 151794 288593 := bstep (se 2 (by rfl) ⟨108222, by rfl⟩ : syracuseStep 288593 = 216445) B216445
theorem B780209 : Blo 151794 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B518129 : Blo 151794 518129 := bstep (se 2 (by rfl) ⟨194298, by rfl⟩ : syracuseStep 518129 = 388597) B388597
theorem B387089 : Blo 151794 387089 := bstep (se 2 (by rfl) ⟨145158, by rfl⟩ : syracuseStep 387089 = 290317) B290317
theorem B878627 : Blo 151794 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B387139 : Blo 151794 387139 := bstep (se 1 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 387139 = 580709) B580709
theorem B583793 : Blo 151794 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B387281 : Blo 151794 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B780515 : Blo 151794 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B256243 : Blo 151794 256243 := bstep (se 1 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 256243 = 384365) B384365
theorem B420109 : Blo 151794 420109 := bstep (se 3 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 420109 = 157541) B157541
theorem B4483349 : Blo 151794 4483349 := bstep (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) B210157
theorem B256385 : Blo 151794 256385 := bstep (se 2 (by rfl) ⟨96144, by rfl⟩ : syracuseStep 256385 = 192289) B192289
theorem B1993187 : Blo 151794 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B256513 : Blo 151794 256513 := bstep (se 2 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 256513 = 192385) B192385
theorem B518669 : Blo 151794 518669 := bstep (se 3 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 518669 = 194501) B194501
theorem B256547 : Blo 151794 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B518723 : Blo 151794 518723 := bstep (se 1 (by rfl) ⟨389042, by rfl⟩ : syracuseStep 518723 = 778085) B778085
theorem B748109 : Blo 151794 748109 := bstep (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) B280541
theorem B256675 : Blo 151794 256675 := bstep (se 1 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 256675 = 385013) B385013
theorem B289489 : Blo 151794 289489 := bstep (se 2 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 289489 = 217117) B217117
theorem B256817 : Blo 151794 256817 := bstep (se 2 (by rfl) ⟨96306, by rfl⟩ : syracuseStep 256817 = 192613) B192613
theorem B518993 : Blo 151794 518993 := bstep (se 2 (by rfl) ⟨194622, by rfl⟩ : syracuseStep 518993 = 389245) B389245
theorem B289649 : Blo 151794 289649 := bstep (se 2 (by rfl) ⟨108618, by rfl⟩ : syracuseStep 289649 = 217237) B217237
theorem B551843 : Blo 151794 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B256945 : Blo 151794 256945 := bstep (se 2 (by rfl) ⟨96354, by rfl⟩ : syracuseStep 256945 = 192709) B192709
theorem B420785 : Blo 151794 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B256979 : Blo 151794 256979 := bstep (se 1 (by rfl) ⟨192734, by rfl⟩ : syracuseStep 256979 = 385469) B385469
theorem B781325 : Blo 151794 781325 := bstep (se 3 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 781325 = 292997) B292997
theorem B257107 : Blo 151794 257107 := bstep (se 1 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 257107 = 385661) B385661
theorem B388273 : Blo 151794 388273 := bstep (se 2 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 388273 = 291205) B291205
theorem B1109189 : Blo 151794 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B257249 : Blo 151794 257249 := bstep (se 2 (by rfl) ⟨96468, by rfl⟩ : syracuseStep 257249 = 192937) B192937
theorem B1666289 : Blo 151794 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B290051 : Blo 151794 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B650531 : Blo 151794 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B257377 : Blo 151794 257377 := bstep (se 2 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 257377 = 193033) B193033
theorem B519533 : Blo 151794 519533 := bstep (se 3 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 519533 = 194825) B194825
theorem B257411 : Blo 151794 257411 := bstep (se 1 (by rfl) ⟨193058, by rfl⟩ : syracuseStep 257411 = 386117) B386117
theorem B519587 : Blo 151794 519587 := bstep (se 1 (by rfl) ⟨389690, by rfl⟩ : syracuseStep 519587 = 779381) B779381
theorem B388547 : Blo 151794 388547 := bstep (se 1 (by rfl) ⟨291410, by rfl⟩ : syracuseStep 388547 = 582821) B582821
theorem B257539 : Blo 151794 257539 := bstep (se 1 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 257539 = 386309) B386309
theorem B585251 : Blo 151794 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B585265 : Blo 151794 585265 := bstep (se 2 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 585265 = 438949) B438949
theorem B388739 : Blo 151794 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B257681 : Blo 151794 257681 := bstep (se 2 (by rfl) ⟨96630, by rfl⟩ : syracuseStep 257681 = 193261) B193261
theorem B519857 : Blo 151794 519857 := bstep (se 2 (by rfl) ⟨194946, by rfl⟩ : syracuseStep 519857 = 389893) B389893
theorem B257809 : Blo 151794 257809 := bstep (se 2 (by rfl) ⟨96678, by rfl⟩ : syracuseStep 257809 = 193357) B193357
theorem B257843 : Blo 151794 257843 := bstep (se 1 (by rfl) ⟨193382, by rfl⟩ : syracuseStep 257843 = 386765) B386765
theorem B487309 : Blo 151794 487309 := bstep (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) B182741
theorem B257971 : Blo 151794 257971 := bstep (se 1 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 257971 = 386957) B386957
theorem B192451 : Blo 151794 192451 := bstep (se 1 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 192451 = 288677) B288677
theorem B192547 : Blo 151794 192547 := bstep (se 1 (by rfl) ⟨144410, by rfl⟩ : syracuseStep 192547 = 288821) B288821
theorem B258113 : Blo 151794 258113 := bstep (se 2 (by rfl) ⟨96792, by rfl⟩ : syracuseStep 258113 = 193585) B193585
theorem B159859 : Blo 151794 159859 := bstep (se 1 (by rfl) ⟨119894, by rfl⟩ : syracuseStep 159859 = 239789) B239789
theorem B290947 : Blo 151794 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B258241 : Blo 151794 258241 := bstep (se 2 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 258241 = 193681) B193681
theorem B520397 : Blo 151794 520397 := bstep (se 3 (by rfl) ⟨97574, by rfl⟩ : syracuseStep 520397 = 195149) B195149
theorem B258275 : Blo 151794 258275 := bstep (se 1 (by rfl) ⟨193706, by rfl⟩ : syracuseStep 258275 = 387413) B387413
theorem B520451 : Blo 151794 520451 := bstep (se 1 (by rfl) ⟨390338, by rfl⟩ : syracuseStep 520451 = 780677) B780677
theorem B782627 : Blo 151794 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B291107 : Blo 151794 291107 := bstep (se 1 (by rfl) ⟨218330, by rfl⟩ : syracuseStep 291107 = 436661) B436661
theorem B258403 : Blo 151794 258403 := bstep (se 1 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 258403 = 387605) B387605
theorem B258545 : Blo 151794 258545 := bstep (se 2 (by rfl) ⟨96954, by rfl⟩ : syracuseStep 258545 = 193909) B193909
theorem B520721 : Blo 151794 520721 := bstep (se 2 (by rfl) ⟨195270, by rfl⟩ : syracuseStep 520721 = 390541) B390541
theorem B193043 : Blo 151794 193043 := bstep (se 1 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 193043 = 289565) B289565
theorem B389681 : Blo 151794 389681 := bstep (se 2 (by rfl) ⟨146130, by rfl⟩ : syracuseStep 389681 = 292261) B292261
theorem B389731 : Blo 151794 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B258673 : Blo 151794 258673 := bstep (se 2 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 258673 = 194005) B194005
theorem B258707 : Blo 151794 258707 := bstep (se 1 (by rfl) ⟨194030, by rfl⟩ : syracuseStep 258707 = 388061) B388061
theorem B389873 : Blo 151794 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B258835 : Blo 151794 258835 := bstep (se 1 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 258835 = 388253) B388253
theorem B258977 : Blo 151794 258977 := bstep (se 2 (by rfl) ⟨97116, by rfl⟩ : syracuseStep 258977 = 194233) B194233
theorem B586723 : Blo 151794 586723 := bstep (se 1 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 586723 = 880085) B880085
theorem B259105 : Blo 151794 259105 := bstep (se 2 (by rfl) ⟨97164, by rfl⟩ : syracuseStep 259105 = 194329) B194329
theorem B521261 : Blo 151794 521261 := bstep (se 3 (by rfl) ⟨97736, by rfl⟩ : syracuseStep 521261 = 195473) B195473
theorem B259139 : Blo 151794 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B521315 : Blo 151794 521315 := bstep (se 1 (by rfl) ⟨390986, by rfl⟩ : syracuseStep 521315 = 781973) B781973
theorem B259267 : Blo 151794 259267 := bstep (se 1 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 259267 = 388901) B388901
theorem B193747 : Blo 151794 193747 := bstep (se 1 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 193747 = 290621) B290621
theorem B193843 : Blo 151794 193843 := bstep (se 1 (by rfl) ⟨145382, by rfl⟩ : syracuseStep 193843 = 290765) B290765
theorem B259409 : Blo 151794 259409 := bstep (se 2 (by rfl) ⟨97278, by rfl⟩ : syracuseStep 259409 = 194557) B194557
theorem B292177 : Blo 151794 292177 := bstep (se 2 (by rfl) ⟨109566, by rfl⟩ : syracuseStep 292177 = 219133) B219133
theorem B750961 : Blo 151794 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B521585 : Blo 151794 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B325009 : Blo 151794 325009 := bstep (se 2 (by rfl) ⟨121878, by rfl⟩ : syracuseStep 325009 = 243757) B243757
theorem B390577 : Blo 151794 390577 := bstep (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) B292933
theorem B259537 : Blo 151794 259537 := bstep (se 2 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 259537 = 194653) B194653
theorem B259571 : Blo 151794 259571 := bstep (se 1 (by rfl) ⟨194678, by rfl⟩ : syracuseStep 259571 = 389357) B389357
theorem B259699 : Blo 151794 259699 := bstep (se 1 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 259699 = 389549) B389549
theorem B489091 : Blo 151794 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B554701 : Blo 151794 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B390865 : Blo 151794 390865 := bstep (se 2 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 390865 = 293149) B293149
theorem B259841 : Blo 151794 259841 := bstep (se 2 (by rfl) ⟨97440, by rfl⟩ : syracuseStep 259841 = 194881) B194881
theorem B194339 : Blo 151794 194339 := bstep (se 1 (by rfl) ⟨145754, by rfl⟩ : syracuseStep 194339 = 291509) B291509
theorem B784241 : Blo 151794 784241 := bstep (se 2 (by rfl) ⟨294090, by rfl⟩ : syracuseStep 784241 = 588181) B588181
theorem B259969 : Blo 151794 259969 := bstep (se 2 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 259969 = 194977) B194977
theorem B522125 : Blo 151794 522125 := bstep (se 3 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 522125 = 195797) B195797
theorem B260003 : Blo 151794 260003 := bstep (se 1 (by rfl) ⟨195002, by rfl⟩ : syracuseStep 260003 = 390005) B390005
theorem B522179 : Blo 151794 522179 := bstep (se 1 (by rfl) ⟨391634, by rfl⟩ : syracuseStep 522179 = 783269) B783269
theorem B391139 : Blo 151794 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B260131 : Blo 151794 260131 := bstep (se 1 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 260131 = 390197) B390197
theorem B489539 : Blo 151794 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B358499 : Blo 151794 358499 := bstep (se 1 (by rfl) ⟨268874, by rfl⟩ : syracuseStep 358499 = 537749) B537749
theorem B325795 : Blo 151794 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B391331 : Blo 151794 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B260273 : Blo 151794 260273 := bstep (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) B195205
theorem B522449 : Blo 151794 522449 := bstep (se 2 (by rfl) ⟨195918, by rfl⟩ : syracuseStep 522449 = 391837) B391837
theorem B260401 : Blo 151794 260401 := bstep (se 2 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 260401 = 195301) B195301
theorem B260435 : Blo 151794 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B293233 : Blo 151794 293233 := bstep (se 2 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 293233 = 219925) B219925
theorem B227699 : Blo 151794 227699 := bstep (se 1 (by rfl) ⟨170774, by rfl⟩ : syracuseStep 227699 = 341549) B341549
theorem B162163 : Blo 151794 162163 := bstep (se 1 (by rfl) ⟨121622, by rfl⟩ : syracuseStep 162163 = 243245) B243245
theorem B227729 : Blo 151794 227729 := bstep (se 2 (by rfl) ⟨85398, by rfl⟩ : syracuseStep 227729 = 170797) B170797
theorem B227747 : Blo 151794 227747 := bstep (se 1 (by rfl) ⟨170810, by rfl⟩ : syracuseStep 227747 = 341621) B341621
theorem B1997237 : Blo 151794 1997237 := bstep (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) B187241
theorem B1800629 : Blo 151794 1800629 := bstep (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) B168809
theorem B227777 : Blo 151794 227777 := bstep (se 2 (by rfl) ⟨85416, by rfl⟩ : syracuseStep 227777 = 170833) B170833
theorem B227795 : Blo 151794 227795 := bstep (se 1 (by rfl) ⟨170846, by rfl⟩ : syracuseStep 227795 = 341693) B341693
theorem B260563 : Blo 151794 260563 := bstep (se 1 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 260563 = 390845) B390845
theorem B195043 : Blo 151794 195043 := bstep (se 1 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 195043 = 292565) B292565
theorem B227825 : Blo 151794 227825 := bstep (se 2 (by rfl) ⟨85434, by rfl⟩ : syracuseStep 227825 = 170869) B170869
theorem B227843 : Blo 151794 227843 := bstep (se 1 (by rfl) ⟨170882, by rfl⟩ : syracuseStep 227843 = 341765) B341765
theorem B227873 : Blo 151794 227873 := bstep (se 2 (by rfl) ⟨85452, by rfl⟩ : syracuseStep 227873 = 170905) B170905
theorem B227891 : Blo 151794 227891 := bstep (se 1 (by rfl) ⟨170918, by rfl⟩ : syracuseStep 227891 = 341837) B341837
theorem B195139 : Blo 151794 195139 := bstep (se 1 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 195139 = 292709) B292709
theorem B227921 : Blo 151794 227921 := bstep (se 2 (by rfl) ⟨85470, by rfl⟩ : syracuseStep 227921 = 170941) B170941
theorem B260705 : Blo 151794 260705 := bstep (se 2 (by rfl) ⟨97764, by rfl⟩ : syracuseStep 260705 = 195529) B195529
theorem B227939 : Blo 151794 227939 := bstep (se 1 (by rfl) ⟨170954, by rfl⟩ : syracuseStep 227939 = 341909) B341909
theorem B162419 : Blo 151794 162419 := bstep (se 1 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 162419 = 243629) B243629
theorem B227969 : Blo 151794 227969 := bstep (se 2 (by rfl) ⟨85488, by rfl⟩ : syracuseStep 227969 = 170977) B170977
theorem B227987 : Blo 151794 227987 := bstep (se 1 (by rfl) ⟨170990, by rfl⟩ : syracuseStep 227987 = 341981) B341981
theorem B228017 : Blo 151794 228017 := bstep (se 2 (by rfl) ⟨85506, by rfl⟩ : syracuseStep 228017 = 171013) B171013
theorem B228035 : Blo 151794 228035 := bstep (se 1 (by rfl) ⟨171026, by rfl⟩ : syracuseStep 228035 = 342053) B342053
theorem B391889 : Blo 151794 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B195283 : Blo 151794 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B228065 : Blo 151794 228065 := bstep (se 2 (by rfl) ⟨85524, by rfl⟩ : syracuseStep 228065 = 171049) B171049
theorem B260833 : Blo 151794 260833 := bstep (se 2 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 260833 = 195625) B195625
theorem B522989 : Blo 151794 522989 := bstep (se 3 (by rfl) ⟨98060, by rfl⟩ : syracuseStep 522989 = 196121) B196121
theorem B228083 : Blo 151794 228083 := bstep (se 1 (by rfl) ⟨171062, by rfl⟩ : syracuseStep 228083 = 342125) B342125
theorem B260867 : Blo 151794 260867 := bstep (se 1 (by rfl) ⟨195650, by rfl⟩ : syracuseStep 260867 = 391301) B391301
theorem B293635 : Blo 151794 293635 := bstep (se 1 (by rfl) ⟨220226, by rfl⟩ : syracuseStep 293635 = 440453) B440453
theorem B228113 : Blo 151794 228113 := bstep (se 2 (by rfl) ⟨85542, by rfl⟩ : syracuseStep 228113 = 171085) B171085
theorem B523043 : Blo 151794 523043 := bstep (se 1 (by rfl) ⟨392282, by rfl⟩ : syracuseStep 523043 = 784565) B784565
theorem B228131 : Blo 151794 228131 := bstep (se 1 (by rfl) ⟨171098, by rfl⟩ : syracuseStep 228131 = 342197) B342197
theorem B293681 : Blo 151794 293681 := bstep (se 2 (by rfl) ⟨110130, by rfl⟩ : syracuseStep 293681 = 220261) B220261
theorem B228161 : Blo 151794 228161 := bstep (se 2 (by rfl) ⟨85560, by rfl⟩ : syracuseStep 228161 = 171121) B171121
theorem B228179 : Blo 151794 228179 := bstep (se 1 (by rfl) ⟨171134, by rfl⟩ : syracuseStep 228179 = 342269) B342269
theorem B228209 : Blo 151794 228209 := bstep (se 2 (by rfl) ⟨85578, by rfl⟩ : syracuseStep 228209 = 171157) B171157
theorem B326513 : Blo 151794 326513 := bstep (se 2 (by rfl) ⟨122442, by rfl⟩ : syracuseStep 326513 = 244885) B244885
theorem B228227 : Blo 151794 228227 := bstep (se 1 (by rfl) ⟨171170, by rfl⟩ : syracuseStep 228227 = 342341) B342341
theorem B260995 : Blo 151794 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B228257 : Blo 151794 228257 := bstep (se 2 (by rfl) ⟨85596, by rfl⟩ : syracuseStep 228257 = 171193) B171193
theorem B228275 : Blo 151794 228275 := bstep (se 1 (by rfl) ⟨171206, by rfl⟩ : syracuseStep 228275 = 342413) B342413
theorem B228305 : Blo 151794 228305 := bstep (se 2 (by rfl) ⟨85614, by rfl⟩ : syracuseStep 228305 = 171229) B171229
theorem B228323 : Blo 151794 228323 := bstep (se 1 (by rfl) ⟨171242, by rfl⟩ : syracuseStep 228323 = 342485) B342485
theorem B621553 : Blo 151794 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B228353 : Blo 151794 228353 := bstep (se 2 (by rfl) ⟨85632, by rfl⟩ : syracuseStep 228353 = 171265) B171265
theorem B261137 : Blo 151794 261137 := bstep (se 2 (by rfl) ⟨97926, by rfl⟩ : syracuseStep 261137 = 195853) B195853
theorem B228371 : Blo 151794 228371 := bstep (se 1 (by rfl) ⟨171278, by rfl⟩ : syracuseStep 228371 = 342557) B342557
theorem B228401 : Blo 151794 228401 := bstep (se 2 (by rfl) ⟨85650, by rfl⟩ : syracuseStep 228401 = 171301) B171301
theorem B523313 : Blo 151794 523313 := bstep (se 2 (by rfl) ⟨196242, by rfl⟩ : syracuseStep 523313 = 392485) B392485
theorem B195635 : Blo 151794 195635 := bstep (se 1 (by rfl) ⟨146726, by rfl⟩ : syracuseStep 195635 = 293453) B293453
theorem B228419 : Blo 151794 228419 := bstep (se 1 (by rfl) ⟨171314, by rfl⟩ : syracuseStep 228419 = 342629) B342629
theorem B293969 : Blo 151794 293969 := bstep (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) B220477
theorem B392273 : Blo 151794 392273 := bstep (se 2 (by rfl) ⟨147102, by rfl⟩ : syracuseStep 392273 = 294205) B294205
theorem B228449 : Blo 151794 228449 := bstep (se 2 (by rfl) ⟨85668, by rfl⟩ : syracuseStep 228449 = 171337) B171337
theorem B228467 : Blo 151794 228467 := bstep (se 1 (by rfl) ⟨171350, by rfl⟩ : syracuseStep 228467 = 342701) B342701
theorem B392323 : Blo 151794 392323 := bstep (se 1 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 392323 = 588485) B588485
theorem B588941 : Blo 151794 588941 := bstep (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) B220853
theorem B228497 : Blo 151794 228497 := bstep (se 2 (by rfl) ⟨85686, by rfl⟩ : syracuseStep 228497 = 171373) B171373
theorem B261265 : Blo 151794 261265 := bstep (se 2 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 261265 = 195949) B195949
theorem B228515 : Blo 151794 228515 := bstep (se 1 (by rfl) ⟨171386, by rfl⟩ : syracuseStep 228515 = 342773) B342773
theorem B261299 : Blo 151794 261299 := bstep (se 1 (by rfl) ⟨195974, by rfl⟩ : syracuseStep 261299 = 391949) B391949
theorem B228545 : Blo 151794 228545 := bstep (se 2 (by rfl) ⟨85704, by rfl⟩ : syracuseStep 228545 = 171409) B171409
theorem B228563 : Blo 151794 228563 := bstep (se 1 (by rfl) ⟨171422, by rfl⟩ : syracuseStep 228563 = 342845) B342845
theorem B228577 : Blo 151794 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B228593 : Blo 151794 228593 := bstep (se 2 (by rfl) ⟨85722, by rfl⟩ : syracuseStep 228593 = 171445) B171445
theorem B228611 : Blo 151794 228611 := bstep (se 1 (by rfl) ⟨171458, by rfl⟩ : syracuseStep 228611 = 342917) B342917
theorem B392465 : Blo 151794 392465 := bstep (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) B294349
theorem B490769 : Blo 151794 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B228641 : Blo 151794 228641 := bstep (se 2 (by rfl) ⟨85740, by rfl⟩ : syracuseStep 228641 = 171481) B171481
theorem B785699 : Blo 151794 785699 := bstep (se 1 (by rfl) ⟨589274, by rfl⟩ : syracuseStep 785699 = 1178549) B1178549
theorem B228659 : Blo 151794 228659 := bstep (se 1 (by rfl) ⟨171494, by rfl⟩ : syracuseStep 228659 = 342989) B342989
theorem B261427 : Blo 151794 261427 := bstep (se 1 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 261427 = 392141) B392141
theorem B228689 : Blo 151794 228689 := bstep (se 2 (by rfl) ⟨85758, by rfl⟩ : syracuseStep 228689 = 171517) B171517
theorem B228707 : Blo 151794 228707 := bstep (se 1 (by rfl) ⟨171530, by rfl⟩ : syracuseStep 228707 = 343061) B343061
theorem B163171 : Blo 151794 163171 := bstep (se 1 (by rfl) ⟨122378, by rfl⟩ : syracuseStep 163171 = 244757) B244757
theorem B327025 : Blo 151794 327025 := bstep (se 2 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 327025 = 245269) B245269
theorem B228737 : Blo 151794 228737 := bstep (se 2 (by rfl) ⟨85776, by rfl⟩ : syracuseStep 228737 = 171553) B171553
theorem B654733 : Blo 151794 654733 := bstep (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) B245525
theorem B228755 : Blo 151794 228755 := bstep (se 1 (by rfl) ⟨171566, by rfl⟩ : syracuseStep 228755 = 343133) B343133
theorem B228785 : Blo 151794 228785 := bstep (se 2 (by rfl) ⟨85794, by rfl⟩ : syracuseStep 228785 = 171589) B171589
theorem B261569 : Blo 151794 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B228803 : Blo 151794 228803 := bstep (se 1 (by rfl) ⟨171602, by rfl⟩ : syracuseStep 228803 = 343205) B343205
theorem B228833 : Blo 151794 228833 := bstep (se 2 (by rfl) ⟨85812, by rfl⟩ : syracuseStep 228833 = 171625) B171625
theorem B228851 : Blo 151794 228851 := bstep (se 1 (by rfl) ⟨171638, by rfl⟩ : syracuseStep 228851 = 343277) B343277
theorem B228881 : Blo 151794 228881 := bstep (se 2 (by rfl) ⟨85830, by rfl⟩ : syracuseStep 228881 = 171661) B171661
theorem B228899 : Blo 151794 228899 := bstep (se 1 (by rfl) ⟨171674, by rfl⟩ : syracuseStep 228899 = 343349) B343349
theorem B228929 : Blo 151794 228929 := bstep (se 2 (by rfl) ⟨85848, by rfl⟩ : syracuseStep 228929 = 171697) B171697
theorem B261697 : Blo 151794 261697 := bstep (se 2 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 261697 = 196273) B196273
theorem B523853 : Blo 151794 523853 := bstep (se 3 (by rfl) ⟨98222, by rfl⟩ : syracuseStep 523853 = 196445) B196445
theorem B228947 : Blo 151794 228947 := bstep (se 1 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 228947 = 343421) B343421
theorem B261731 : Blo 151794 261731 := bstep (se 1 (by rfl) ⟨196298, by rfl⟩ : syracuseStep 261731 = 392597) B392597
theorem B228977 : Blo 151794 228977 := bstep (se 2 (by rfl) ⟨85866, by rfl⟩ : syracuseStep 228977 = 171733) B171733
theorem B228995 : Blo 151794 228995 := bstep (se 1 (by rfl) ⟨171746, by rfl⟩ : syracuseStep 228995 = 343493) B343493
theorem B523907 : Blo 151794 523907 := bstep (se 1 (by rfl) ⟨392930, by rfl⟩ : syracuseStep 523907 = 785861) B785861
theorem B229025 : Blo 151794 229025 := bstep (se 2 (by rfl) ⟨85884, by rfl⟩ : syracuseStep 229025 = 171769) B171769
theorem B229043 : Blo 151794 229043 := bstep (se 1 (by rfl) ⟨171782, by rfl⟩ : syracuseStep 229043 = 343565) B343565
theorem B229073 : Blo 151794 229073 := bstep (se 2 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 229073 = 171805) B171805
theorem B229091 : Blo 151794 229091 := bstep (se 1 (by rfl) ⟨171818, by rfl⟩ : syracuseStep 229091 = 343637) B343637
theorem B261859 : Blo 151794 261859 := bstep (se 1 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 261859 = 392789) B392789
theorem B196339 : Blo 151794 196339 := bstep (se 1 (by rfl) ⟨147254, by rfl⟩ : syracuseStep 196339 = 294509) B294509
theorem B229121 : Blo 151794 229121 := bstep (se 2 (by rfl) ⟨85920, by rfl⟩ : syracuseStep 229121 = 171841) B171841
theorem B229139 : Blo 151794 229139 := bstep (se 1 (by rfl) ⟨171854, by rfl⟩ : syracuseStep 229139 = 343709) B343709
theorem B294691 : Blo 151794 294691 := bstep (se 1 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 294691 = 442037) B442037
theorem B229169 : Blo 151794 229169 := bstep (se 2 (by rfl) ⟨85938, by rfl⟩ : syracuseStep 229169 = 171877) B171877
theorem B229187 : Blo 151794 229187 := bstep (se 1 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 229187 = 343781) B343781
theorem B196435 : Blo 151794 196435 := bstep (se 1 (by rfl) ⟨147326, by rfl⟩ : syracuseStep 196435 = 294653) B294653
theorem B229217 : Blo 151794 229217 := bstep (se 2 (by rfl) ⟨85956, by rfl⟩ : syracuseStep 229217 = 171913) B171913
theorem B262001 : Blo 151794 262001 := bstep (se 2 (by rfl) ⟨98250, by rfl⟩ : syracuseStep 262001 = 196501) B196501
theorem B229235 : Blo 151794 229235 := bstep (se 1 (by rfl) ⟨171926, by rfl⟩ : syracuseStep 229235 = 343853) B343853
theorem B229265 : Blo 151794 229265 := bstep (se 2 (by rfl) ⟨85974, by rfl⟩ : syracuseStep 229265 = 171949) B171949
theorem B524177 : Blo 151794 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B229283 : Blo 151794 229283 := bstep (se 1 (by rfl) ⟨171962, by rfl⟩ : syracuseStep 229283 = 343925) B343925
theorem B229313 : Blo 151794 229313 := bstep (se 2 (by rfl) ⟨85992, by rfl⟩ : syracuseStep 229313 = 171985) B171985
theorem B229331 : Blo 151794 229331 := bstep (se 1 (by rfl) ⟨171998, by rfl⟩ : syracuseStep 229331 = 343997) B343997
theorem B229361 : Blo 151794 229361 := bstep (se 2 (by rfl) ⟨86010, by rfl⟩ : syracuseStep 229361 = 172021) B172021
theorem B262129 : Blo 151794 262129 := bstep (se 2 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 262129 = 196597) B196597
theorem B524339 : Blo 151794 524339 := bstep (se 1 (by rfl) ⟨393254, by rfl⟩ : syracuseStep 524339 = 786509) B786509
theorem B229451 : Blo 151794 229451 := bstep (se 1 (by rfl) ⟨172088, by rfl⟩ : syracuseStep 229451 = 344177) B344177
theorem B229463 : Blo 151794 229463 := bstep (se 1 (by rfl) ⟨172097, by rfl⟩ : syracuseStep 229463 = 344195) B344195
theorem B589913 : Blo 151794 589913 := bstep (se 2 (by rfl) ⟨221217, by rfl⟩ : syracuseStep 589913 = 442435) B442435
theorem B163991 : Blo 151794 163991 := bstep (se 1 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 163991 = 245987) B245987
theorem B196759 : Blo 151794 196759 := bstep (se 1 (by rfl) ⟨147569, by rfl⟩ : syracuseStep 196759 = 295139) B295139
theorem B229529 : Blo 151794 229529 := bstep (se 2 (by rfl) ⟨86073, by rfl⟩ : syracuseStep 229529 = 172147) B172147
theorem B884915 : Blo 151794 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B655553 : Blo 151794 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B229643 : Blo 151794 229643 := bstep (se 1 (by rfl) ⟨172232, by rfl⟩ : syracuseStep 229643 = 344465) B344465
theorem B229655 : Blo 151794 229655 := bstep (se 1 (by rfl) ⟨172241, by rfl⟩ : syracuseStep 229655 = 344483) B344483
theorem B590125 : Blo 151794 590125 := bstep (se 3 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 590125 = 221297) B221297
theorem B524609 : Blo 151794 524609 := bstep (se 2 (by rfl) ⟨196728, by rfl⟩ : syracuseStep 524609 = 393457) B393457
theorem B262487 : Blo 151794 262487 := bstep (se 1 (by rfl) ⟨196865, by rfl⟩ : syracuseStep 262487 = 393731) B393731
theorem B229721 : Blo 151794 229721 := bstep (se 2 (by rfl) ⟨86145, by rfl⟩ : syracuseStep 229721 = 172291) B172291
theorem B295321 : Blo 151794 295321 := bstep (se 2 (by rfl) ⟨110745, by rfl⟩ : syracuseStep 295321 = 221491) B221491
theorem B229835 : Blo 151794 229835 := bstep (se 1 (by rfl) ⟨172376, by rfl⟩ : syracuseStep 229835 = 344753) B344753
theorem B229847 : Blo 151794 229847 := bstep (se 1 (by rfl) ⟨172385, by rfl⟩ : syracuseStep 229847 = 344771) B344771
theorem B262615 : Blo 151794 262615 := bstep (se 1 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 262615 = 393923) B393923
theorem B328153 : Blo 151794 328153 := bstep (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) B246115
theorem B229913 : Blo 151794 229913 := bstep (se 2 (by rfl) ⟨86217, by rfl⟩ : syracuseStep 229913 = 172435) B172435
theorem B590429 : Blo 151794 590429 := bstep (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) B221411
theorem B230027 : Blo 151794 230027 := bstep (se 1 (by rfl) ⟨172520, by rfl⟩ : syracuseStep 230027 = 345041) B345041
theorem B230039 : Blo 151794 230039 := bstep (se 1 (by rfl) ⟨172529, by rfl⟩ : syracuseStep 230039 = 345059) B345059
theorem B2130583 : Blo 151794 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B230105 : Blo 151794 230105 := bstep (se 2 (by rfl) ⟨86289, by rfl⟩ : syracuseStep 230105 = 172579) B172579
theorem B230219 : Blo 151794 230219 := bstep (se 1 (by rfl) ⟨172664, by rfl⟩ : syracuseStep 230219 = 345329) B345329
theorem B164683 : Blo 151794 164683 := bstep (se 1 (by rfl) ⟨123512, by rfl⟩ : syracuseStep 164683 = 247025) B247025
theorem B230231 : Blo 151794 230231 := bstep (se 1 (by rfl) ⟨172673, by rfl⟩ : syracuseStep 230231 = 345347) B345347
theorem B656221 : Blo 151794 656221 := bstep (se 3 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 656221 = 246083) B246083
theorem B525149 : Blo 151794 525149 := bstep (se 3 (by rfl) ⟨98465, by rfl⟩ : syracuseStep 525149 = 196931) B196931
theorem B230297 : Blo 151794 230297 := bstep (se 2 (by rfl) ⟨86361, by rfl⟩ : syracuseStep 230297 = 172723) B172723
theorem B230411 : Blo 151794 230411 := bstep (se 1 (by rfl) ⟨172808, by rfl⟩ : syracuseStep 230411 = 345617) B345617
theorem B230423 : Blo 151794 230423 := bstep (se 1 (by rfl) ⟨172817, by rfl⟩ : syracuseStep 230423 = 345635) B345635
theorem B230489 : Blo 151794 230489 := bstep (se 2 (by rfl) ⟨86433, by rfl⟩ : syracuseStep 230489 = 172867) B172867
theorem B230603 : Blo 151794 230603 := bstep (se 1 (by rfl) ⟨172952, by rfl⟩ : syracuseStep 230603 = 345905) B345905
theorem B230615 : Blo 151794 230615 := bstep (se 1 (by rfl) ⟨172961, by rfl⟩ : syracuseStep 230615 = 345923) B345923
theorem B230681 : Blo 151794 230681 := bstep (se 2 (by rfl) ⟨86505, by rfl⟩ : syracuseStep 230681 = 173011) B173011
theorem B787805 : Blo 151794 787805 := bstep (se 3 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 787805 = 295427) B295427
theorem B230795 : Blo 151794 230795 := bstep (se 1 (by rfl) ⟨173096, by rfl⟩ : syracuseStep 230795 = 346193) B346193
theorem B230807 : Blo 151794 230807 := bstep (se 1 (by rfl) ⟨173105, by rfl⟩ : syracuseStep 230807 = 346211) B346211
theorem B656819 : Blo 151794 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B230873 : Blo 151794 230873 := bstep (se 2 (by rfl) ⟨86577, by rfl⟩ : syracuseStep 230873 = 173155) B173155
theorem B230987 : Blo 151794 230987 := bstep (se 1 (by rfl) ⟨173240, by rfl⟩ : syracuseStep 230987 = 346481) B346481
theorem B230999 : Blo 151794 230999 := bstep (se 1 (by rfl) ⟨173249, by rfl⟩ : syracuseStep 230999 = 346499) B346499
theorem B886373 : Blo 151794 886373 := bstep (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) B166195
theorem B231065 : Blo 151794 231065 := bstep (se 2 (by rfl) ⟨86649, by rfl⟩ : syracuseStep 231065 = 173299) B173299
theorem B165559 : Blo 151794 165559 := bstep (se 1 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 165559 = 248339) B248339
theorem B231179 : Blo 151794 231179 := bstep (se 1 (by rfl) ⟨173384, by rfl⟩ : syracuseStep 231179 = 346769) B346769
theorem B231191 : Blo 151794 231191 := bstep (se 1 (by rfl) ⟨173393, by rfl⟩ : syracuseStep 231191 = 346787) B346787
theorem B231257 : Blo 151794 231257 := bstep (se 2 (by rfl) ⟨86721, by rfl⟩ : syracuseStep 231257 = 173443) B173443
theorem B231371 : Blo 151794 231371 := bstep (se 1 (by rfl) ⟨173528, by rfl⟩ : syracuseStep 231371 = 347057) B347057
theorem B231383 : Blo 151794 231383 := bstep (se 1 (by rfl) ⟨173537, by rfl⟩ : syracuseStep 231383 = 347075) B347075
theorem B526297 : Blo 151794 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B231449 : Blo 151794 231449 := bstep (se 2 (by rfl) ⟨86793, by rfl⟩ : syracuseStep 231449 = 173587) B173587
theorem B166007 : Blo 151794 166007 := bstep (se 1 (by rfl) ⟨124505, by rfl⟩ : syracuseStep 166007 = 249011) B249011
theorem B231563 : Blo 151794 231563 := bstep (se 1 (by rfl) ⟨173672, by rfl⟩ : syracuseStep 231563 = 347345) B347345
theorem B231575 : Blo 151794 231575 := bstep (se 1 (by rfl) ⟨173681, by rfl⟩ : syracuseStep 231575 = 347363) B347363
theorem B231641 : Blo 151794 231641 := bstep (se 2 (by rfl) ⟨86865, by rfl⟩ : syracuseStep 231641 = 173731) B173731
theorem B887057 : Blo 151794 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B231755 : Blo 151794 231755 := bstep (se 1 (by rfl) ⟨173816, by rfl⟩ : syracuseStep 231755 = 347633) B347633
theorem B231767 : Blo 151794 231767 := bstep (se 1 (by rfl) ⟨173825, by rfl⟩ : syracuseStep 231767 = 347651) B347651
theorem B231833 : Blo 151794 231833 := bstep (se 2 (by rfl) ⟨86937, by rfl⟩ : syracuseStep 231833 = 173875) B173875
theorem B231947 : Blo 151794 231947 := bstep (se 1 (by rfl) ⟨173960, by rfl⟩ : syracuseStep 231947 = 347921) B347921
theorem B231959 : Blo 151794 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B232025 : Blo 151794 232025 := bstep (se 2 (by rfl) ⟨87009, by rfl⟩ : syracuseStep 232025 = 174019) B174019
theorem B232139 : Blo 151794 232139 := bstep (se 1 (by rfl) ⟨174104, by rfl⟩ : syracuseStep 232139 = 348209) B348209
theorem B232151 : Blo 151794 232151 := bstep (se 1 (by rfl) ⟨174113, by rfl⟩ : syracuseStep 232151 = 348227) B348227
theorem B297751 : Blo 151794 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B232217 : Blo 151794 232217 := bstep (se 2 (by rfl) ⟨87081, by rfl⟩ : syracuseStep 232217 = 174163) B174163
theorem B330571 : Blo 151794 330571 := bstep (se 1 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 330571 = 495857) B495857
theorem B232331 : Blo 151794 232331 := bstep (se 1 (by rfl) ⟨174248, by rfl⟩ : syracuseStep 232331 = 348497) B348497
theorem B330647 : Blo 151794 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B232343 : Blo 151794 232343 := bstep (se 1 (by rfl) ⟨174257, by rfl⟩ : syracuseStep 232343 = 348515) B348515
theorem B232409 : Blo 151794 232409 := bstep (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) B174307
theorem B232523 : Blo 151794 232523 := bstep (se 1 (by rfl) ⟨174392, by rfl⟩ : syracuseStep 232523 = 348785) B348785
theorem B232535 : Blo 151794 232535 := bstep (se 1 (by rfl) ⟨174401, by rfl⟩ : syracuseStep 232535 = 348803) B348803
theorem B232601 : Blo 151794 232601 := bstep (se 2 (by rfl) ⟨87225, by rfl⟩ : syracuseStep 232601 = 174451) B174451
theorem B167095 : Blo 151794 167095 := bstep (se 1 (by rfl) ⟨125321, by rfl⟩ : syracuseStep 167095 = 250643) B250643
theorem B232715 : Blo 151794 232715 := bstep (se 1 (by rfl) ⟨174536, by rfl⟩ : syracuseStep 232715 = 349073) B349073
theorem B232727 : Blo 151794 232727 := bstep (se 1 (by rfl) ⟨174545, by rfl⟩ : syracuseStep 232727 = 349091) B349091
theorem B232793 : Blo 151794 232793 := bstep (se 2 (by rfl) ⟨87297, by rfl⟩ : syracuseStep 232793 = 174595) B174595
theorem B232907 : Blo 151794 232907 := bstep (se 1 (by rfl) ⟨174680, by rfl⟩ : syracuseStep 232907 = 349361) B349361
theorem B232919 : Blo 151794 232919 := bstep (se 1 (by rfl) ⟨174689, by rfl⟩ : syracuseStep 232919 = 349379) B349379
theorem B658961 : Blo 151794 658961 := bstep (se 2 (by rfl) ⟨247110, by rfl⟩ : syracuseStep 658961 = 494221) B494221
theorem B232985 : Blo 151794 232985 := bstep (se 2 (by rfl) ⟨87369, by rfl⟩ : syracuseStep 232985 = 174739) B174739
theorem B233099 : Blo 151794 233099 := bstep (se 1 (by rfl) ⟨174824, by rfl⟩ : syracuseStep 233099 = 349649) B349649
theorem B233111 : Blo 151794 233111 := bstep (se 1 (by rfl) ⟨174833, by rfl⟩ : syracuseStep 233111 = 349667) B349667
theorem B233177 : Blo 151794 233177 := bstep (se 2 (by rfl) ⟨87441, by rfl⟩ : syracuseStep 233177 = 174883) B174883
theorem B1412939 : Blo 151794 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B233291 : Blo 151794 233291 := bstep (se 1 (by rfl) ⟨174968, by rfl⟩ : syracuseStep 233291 = 349937) B349937
theorem B233303 : Blo 151794 233303 := bstep (se 1 (by rfl) ⟨174977, by rfl⟩ : syracuseStep 233303 = 349955) B349955
theorem B10030949 : Blo 151794 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B233369 : Blo 151794 233369 := bstep (se 2 (by rfl) ⟨87513, by rfl⟩ : syracuseStep 233369 = 175027) B175027
theorem B233483 : Blo 151794 233483 := bstep (se 1 (by rfl) ⟨175112, by rfl⟩ : syracuseStep 233483 = 350225) B350225
theorem B233495 : Blo 151794 233495 := bstep (se 1 (by rfl) ⟨175121, by rfl⟩ : syracuseStep 233495 = 350243) B350243
theorem B233561 : Blo 151794 233561 := bstep (se 2 (by rfl) ⟨87585, by rfl⟩ : syracuseStep 233561 = 175171) B175171
theorem B233675 : Blo 151794 233675 := bstep (se 1 (by rfl) ⟨175256, by rfl⟩ : syracuseStep 233675 = 350513) B350513
theorem B233687 : Blo 151794 233687 := bstep (se 1 (by rfl) ⟨175265, by rfl⟩ : syracuseStep 233687 = 350531) B350531
theorem B495895 : Blo 151794 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B397657 : Blo 151794 397657 := bstep (se 2 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 397657 = 298243) B298243
theorem B463283 : Blo 151794 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B1315277 : Blo 151794 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B332417 : Blo 151794 332417 := bstep (se 2 (by rfl) ⟨124656, by rfl⟩ : syracuseStep 332417 = 249313) B249313
theorem B496331 : Blo 151794 496331 := bstep (se 1 (by rfl) ⟨372248, by rfl⟩ : syracuseStep 496331 = 744497) B744497
theorem B1348643 : Blo 151794 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B660611 : Blo 151794 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B365771 : Blo 151794 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B988433 : Blo 151794 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B496919 : Blo 151794 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B497099 : Blo 151794 497099 := bstep (se 1 (by rfl) ⟨372824, by rfl⟩ : syracuseStep 497099 = 745649) B745649
theorem B660953 : Blo 151794 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B792139 : Blo 151794 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B1054529 : Blo 151794 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B497497 : Blo 151794 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B497611 : Blo 151794 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B498113 : Blo 151794 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B1252057 : Blo 151794 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B1317667 : Blo 151794 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B2988899 : Blo 151794 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B990103 : Blo 151794 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B170923 : Blo 151794 170923 := bstep (se 1 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 170923 = 256385) B256385
theorem B1252313 : Blo 151794 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B433117 : Blo 151794 433117 := bstep (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) B162419
theorem B171031 : Blo 151794 171031 := bstep (se 1 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 171031 = 256547) B256547
theorem B498739 : Blo 151794 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B662593 : Blo 151794 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B990301 : Blo 151794 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B433345 : Blo 151794 433345 := bstep (se 2 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 433345 = 325009) B325009
theorem B171211 : Blo 151794 171211 := bstep (se 1 (by rfl) ⟨128408, by rfl⟩ : syracuseStep 171211 = 256817) B256817
theorem B367895 : Blo 151794 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B171319 : Blo 151794 171319 := bstep (se 1 (by rfl) ⟨128489, by rfl⟩ : syracuseStep 171319 = 256979) B256979
theorem B171499 : Blo 151794 171499 := bstep (se 1 (by rfl) ⟨128624, by rfl⟩ : syracuseStep 171499 = 257249) B257249
theorem B433687 : Blo 151794 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B171607 : Blo 151794 171607 := bstep (se 1 (by rfl) ⟨128705, by rfl⟩ : syracuseStep 171607 = 257411) B257411
theorem B171787 : Blo 151794 171787 := bstep (se 1 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 171787 = 257681) B257681
theorem B171895 : Blo 151794 171895 := bstep (se 1 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 171895 = 257843) B257843
theorem B172075 : Blo 151794 172075 := bstep (se 1 (by rfl) ⟨129056, by rfl⟩ : syracuseStep 172075 = 258113) B258113
theorem B1646743 : Blo 151794 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B172183 : Blo 151794 172183 := bstep (se 1 (by rfl) ⟨129137, by rfl⟩ : syracuseStep 172183 = 258275) B258275
theorem B434393 : Blo 151794 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B172363 : Blo 151794 172363 := bstep (se 1 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 172363 = 258545) B258545
theorem B172471 : Blo 151794 172471 := bstep (se 1 (by rfl) ⟨129353, by rfl⟩ : syracuseStep 172471 = 258707) B258707
theorem B205259 : Blo 151794 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B664067 : Blo 151794 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B172651 : Blo 151794 172651 := bstep (se 1 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 172651 = 258977) B258977
theorem B172759 : Blo 151794 172759 := bstep (se 1 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 172759 = 259139) B259139
theorem B172939 : Blo 151794 172939 := bstep (se 1 (by rfl) ⟨129704, by rfl⟩ : syracuseStep 172939 = 259409) B259409
theorem B173047 : Blo 151794 173047 := bstep (se 1 (by rfl) ⟨129785, by rfl⟩ : syracuseStep 173047 = 259571) B259571
theorem B173227 : Blo 151794 173227 := bstep (se 1 (by rfl) ⟨129920, by rfl⟩ : syracuseStep 173227 = 259841) B259841
theorem B173335 : Blo 151794 173335 := bstep (se 1 (by rfl) ⟨130001, by rfl⟩ : syracuseStep 173335 = 260003) B260003
theorem B828737 : Blo 151794 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B238999 : Blo 151794 238999 := bstep (se 1 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 238999 = 358499) B358499
theorem B20194757 : Blo 151794 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B173515 : Blo 151794 173515 := bstep (se 1 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 173515 = 260273) B260273
theorem B173623 : Blo 151794 173623 := bstep (se 1 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 173623 = 260435) B260435
theorem B304769 : Blo 151794 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B173803 : Blo 151794 173803 := bstep (se 1 (by rfl) ⟨130352, by rfl⟩ : syracuseStep 173803 = 260705) B260705
theorem B272179 : Blo 151794 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B436033 : Blo 151794 436033 := bstep (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) B327025
theorem B173911 : Blo 151794 173911 := bstep (se 1 (by rfl) ⟨130433, by rfl⟩ : syracuseStep 173911 = 260867) B260867
theorem B174091 : Blo 151794 174091 := bstep (se 1 (by rfl) ⟨130568, by rfl⟩ : syracuseStep 174091 = 261137) B261137
theorem B1157165 : Blo 151794 1157165 := bstep (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) B433937
theorem B1976413 : Blo 151794 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B174199 : Blo 151794 174199 := bstep (se 1 (by rfl) ⟨130649, by rfl⟩ : syracuseStep 174199 = 261299) B261299
theorem B3549365 : Blo 151794 3549365 := bstep (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) B332753
theorem B174379 : Blo 151794 174379 := bstep (se 1 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 174379 = 261569) B261569
theorem B174487 : Blo 151794 174487 := bstep (se 1 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 174487 = 261731) B261731
theorem B174667 : Blo 151794 174667 := bstep (se 1 (by rfl) ⟨131000, by rfl⟩ : syracuseStep 174667 = 262001) B262001
theorem B174775 : Blo 151794 174775 := bstep (se 1 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 174775 = 262163) B262163
theorem B371479 : Blo 151794 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B666443 : Blo 151794 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B174955 : Blo 151794 174955 := bstep (se 1 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 174955 = 262433) B262433
theorem B175063 : Blo 151794 175063 := bstep (se 1 (by rfl) ⟨131297, by rfl⟩ : syracuseStep 175063 = 262595) B262595
theorem B175243 : Blo 151794 175243 := bstep (se 1 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 175243 = 262865) B262865
theorem B732311 : Blo 151794 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B470195 : Blo 151794 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B1322315 : Blo 151794 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B700235 : Blo 151794 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B831505 : Blo 151794 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B2240581 : Blo 151794 2240581 := bstep (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) B420109
theorem B275251 : Blo 151794 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B2831435 : Blo 151794 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B865687 : Blo 151794 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B439769 : Blo 151794 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B341657 : Blo 151794 341657 := bstep (se 2 (by rfl) ⟨128121, by rfl⟩ : syracuseStep 341657 = 256243) B256243
theorem B341747 : Blo 151794 341747 := bstep (se 1 (by rfl) ⟨256310, by rfl⟩ : syracuseStep 341747 = 512621) B512621
theorem B341783 : Blo 151794 341783 := bstep (se 1 (by rfl) ⟨256337, by rfl⟩ : syracuseStep 341783 = 512675) B512675
theorem B1161053 : Blo 151794 1161053 := bstep (se 3 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 1161053 = 435395) B435395
theorem B341963 : Blo 151794 341963 := bstep (se 1 (by rfl) ⟨256472, by rfl⟩ : syracuseStep 341963 = 512945) B512945
theorem B342017 : Blo 151794 342017 := bstep (se 2 (by rfl) ⟨128256, by rfl⟩ : syracuseStep 342017 = 256513) B256513
theorem B1751057 : Blo 151794 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B342233 : Blo 151794 342233 := bstep (se 2 (by rfl) ⟨128337, by rfl⟩ : syracuseStep 342233 = 256675) B256675
theorem B833753 : Blo 151794 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B342323 : Blo 151794 342323 := bstep (se 1 (by rfl) ⟨256742, by rfl⟩ : syracuseStep 342323 = 513485) B513485
theorem B276787 : Blo 151794 276787 := bstep (se 1 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 276787 = 415181) B415181
theorem B342359 : Blo 151794 342359 := bstep (se 1 (by rfl) ⟨256769, by rfl⟩ : syracuseStep 342359 = 513539) B513539
theorem B276851 : Blo 151794 276851 := bstep (se 1 (by rfl) ⟨207638, by rfl⟩ : syracuseStep 276851 = 415277) B415277
theorem B342539 : Blo 151794 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B342593 : Blo 151794 342593 := bstep (se 2 (by rfl) ⟨128472, by rfl⟩ : syracuseStep 342593 = 256945) B256945
theorem B309835 : Blo 151794 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B441035 : Blo 151794 441035 := bstep (se 1 (by rfl) ⟨330776, by rfl⟩ : syracuseStep 441035 = 661553) B661553
theorem B342809 : Blo 151794 342809 := bstep (se 2 (by rfl) ⟨128553, by rfl⟩ : syracuseStep 342809 = 257107) B257107
theorem B1358693 : Blo 151794 1358693 := bstep (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) B254755
theorem B342899 : Blo 151794 342899 := bstep (se 1 (by rfl) ⟨257174, by rfl⟩ : syracuseStep 342899 = 514349) B514349
theorem B342935 : Blo 151794 342935 := bstep (se 1 (by rfl) ⟨257201, by rfl⟩ : syracuseStep 342935 = 514403) B514403
theorem B343115 : Blo 151794 343115 := bstep (se 1 (by rfl) ⟨257336, by rfl⟩ : syracuseStep 343115 = 514673) B514673
theorem B343169 : Blo 151794 343169 := bstep (se 2 (by rfl) ⟨128688, by rfl⟩ : syracuseStep 343169 = 257377) B257377
theorem B769175 : Blo 151794 769175 := bstep (se 1 (by rfl) ⟨576881, by rfl⟩ : syracuseStep 769175 = 1153763) B1153763
theorem B343385 : Blo 151794 343385 := bstep (se 2 (by rfl) ⟨128769, by rfl⟩ : syracuseStep 343385 = 257539) B257539
theorem B343435 : Blo 151794 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B343475 : Blo 151794 343475 := bstep (se 1 (by rfl) ⟨257606, by rfl⟩ : syracuseStep 343475 = 515213) B515213
theorem B343511 : Blo 151794 343511 := bstep (se 1 (by rfl) ⟨257633, by rfl⟩ : syracuseStep 343511 = 515267) B515267
theorem B343691 : Blo 151794 343691 := bstep (se 1 (by rfl) ⟨257768, by rfl⟩ : syracuseStep 343691 = 515537) B515537
theorem B343745 : Blo 151794 343745 := bstep (se 2 (by rfl) ⟨128904, by rfl⟩ : syracuseStep 343745 = 257809) B257809
theorem B343961 : Blo 151794 343961 := bstep (se 2 (by rfl) ⟨128985, by rfl⟩ : syracuseStep 343961 = 257971) B257971
theorem B344051 : Blo 151794 344051 := bstep (se 1 (by rfl) ⟨258038, by rfl⟩ : syracuseStep 344051 = 516077) B516077
theorem B344087 : Blo 151794 344087 := bstep (se 1 (by rfl) ⟨258065, by rfl⟩ : syracuseStep 344087 = 516131) B516131
theorem B213145 : Blo 151794 213145 := bstep (se 2 (by rfl) ⟨79929, by rfl⟩ : syracuseStep 213145 = 159859) B159859
theorem B344267 : Blo 151794 344267 := bstep (se 1 (by rfl) ⟨258200, by rfl⟩ : syracuseStep 344267 = 516401) B516401
theorem B344321 : Blo 151794 344321 := bstep (se 2 (by rfl) ⟨129120, by rfl⟩ : syracuseStep 344321 = 258241) B258241
theorem B344537 : Blo 151794 344537 := bstep (se 2 (by rfl) ⟨129201, by rfl⟩ : syracuseStep 344537 = 258403) B258403
theorem B672259 : Blo 151794 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B344627 : Blo 151794 344627 := bstep (se 1 (by rfl) ⟨258470, by rfl⟩ : syracuseStep 344627 = 516941) B516941
theorem B1327691 : Blo 151794 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B442955 : Blo 151794 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B344663 : Blo 151794 344663 := bstep (se 1 (by rfl) ⟨258497, by rfl⟩ : syracuseStep 344663 = 516995) B516995
theorem B672401 : Blo 151794 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B344843 : Blo 151794 344843 := bstep (se 1 (by rfl) ⟨258632, by rfl⟩ : syracuseStep 344843 = 517265) B517265
theorem B836369 : Blo 151794 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B1327889 : Blo 151794 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B344897 : Blo 151794 344897 := bstep (se 2 (by rfl) ⟨129336, by rfl⟩ : syracuseStep 344897 = 258673) B258673
theorem B1753973 : Blo 151794 1753973 := bstep (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) B164435
theorem B345113 : Blo 151794 345113 := bstep (se 2 (by rfl) ⟨129417, by rfl⟩ : syracuseStep 345113 = 258835) B258835
theorem B345203 : Blo 151794 345203 := bstep (se 1 (by rfl) ⟨258902, by rfl⟩ : syracuseStep 345203 = 517805) B517805
theorem B345239 : Blo 151794 345239 := bstep (se 1 (by rfl) ⟨258929, by rfl⟩ : syracuseStep 345239 = 517859) B517859
theorem B246935 : Blo 151794 246935 := bstep (se 1 (by rfl) ⟨185201, by rfl⟩ : syracuseStep 246935 = 370403) B370403
theorem B345419 : Blo 151794 345419 := bstep (se 1 (by rfl) ⟨259064, by rfl⟩ : syracuseStep 345419 = 518129) B518129
theorem B345473 : Blo 151794 345473 := bstep (se 2 (by rfl) ⟨129552, by rfl⟩ : syracuseStep 345473 = 259105) B259105
theorem B345689 : Blo 151794 345689 := bstep (se 2 (by rfl) ⟨129633, by rfl⟩ : syracuseStep 345689 = 259267) B259267
theorem B1328791 : Blo 151794 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B345779 : Blo 151794 345779 := bstep (se 1 (by rfl) ⟨259334, by rfl⟩ : syracuseStep 345779 = 518669) B518669
theorem B345815 : Blo 151794 345815 := bstep (se 1 (by rfl) ⟨259361, by rfl⟩ : syracuseStep 345815 = 518723) B518723
theorem B1001281 : Blo 151794 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B247627 : Blo 151794 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B345995 : Blo 151794 345995 := bstep (se 1 (by rfl) ⟨259496, by rfl⟩ : syracuseStep 345995 = 518993) B518993
theorem B346049 : Blo 151794 346049 := bstep (se 2 (by rfl) ⟨129768, by rfl⟩ : syracuseStep 346049 = 259537) B259537
theorem B280523 : Blo 151794 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B739459 : Blo 151794 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B346265 : Blo 151794 346265 := bstep (se 2 (by rfl) ⟨129849, by rfl⟩ : syracuseStep 346265 = 259699) B259699
theorem B1099993 : Blo 151794 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B346355 : Blo 151794 346355 := bstep (se 1 (by rfl) ⟨259766, by rfl⟩ : syracuseStep 346355 = 519533) B519533
theorem B1132805 : Blo 151794 1132805 := bstep (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) B212401
theorem B739601 : Blo 151794 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B346391 : Blo 151794 346391 := bstep (se 1 (by rfl) ⟨259793, by rfl⟩ : syracuseStep 346391 = 519587) B519587
theorem B346571 : Blo 151794 346571 := bstep (se 1 (by rfl) ⟨259928, by rfl⟩ : syracuseStep 346571 = 519857) B519857
theorem B346625 : Blo 151794 346625 := bstep (se 2 (by rfl) ⟨129984, by rfl⟩ : syracuseStep 346625 = 259969) B259969
theorem B772739 : Blo 151794 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B9358037 : Blo 151794 9358037 := bstep (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) B219329
theorem B346841 : Blo 151794 346841 := bstep (se 2 (by rfl) ⟨130065, by rfl⟩ : syracuseStep 346841 = 260131) B260131
theorem B346931 : Blo 151794 346931 := bstep (se 1 (by rfl) ⟨260198, by rfl⟩ : syracuseStep 346931 = 520397) B520397
theorem B346967 : Blo 151794 346967 := bstep (se 1 (by rfl) ⟨260225, by rfl⟩ : syracuseStep 346967 = 520451) B520451
theorem B248665 : Blo 151794 248665 := bstep (se 2 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 248665 = 186499) B186499
theorem B347147 : Blo 151794 347147 := bstep (se 1 (by rfl) ⟨260360, by rfl⟩ : syracuseStep 347147 = 520721) B520721
theorem B347201 : Blo 151794 347201 := bstep (se 2 (by rfl) ⟨130200, by rfl⟩ : syracuseStep 347201 = 260401) B260401
theorem B216217 : Blo 151794 216217 := bstep (se 2 (by rfl) ⟨81081, by rfl⟩ : syracuseStep 216217 = 162163) B162163
theorem B576791 : Blo 151794 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B347417 : Blo 151794 347417 := bstep (se 2 (by rfl) ⟨130281, by rfl⟩ : syracuseStep 347417 = 260563) B260563
theorem B249113 : Blo 151794 249113 := bstep (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) B186835
theorem B4443437 : Blo 151794 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B347507 : Blo 151794 347507 := bstep (se 1 (by rfl) ⟨260630, by rfl⟩ : syracuseStep 347507 = 521261) B521261
theorem B347543 : Blo 151794 347543 := bstep (se 1 (by rfl) ⟨260657, by rfl⟩ : syracuseStep 347543 = 521315) B521315
theorem B576989 : Blo 151794 576989 := bstep (se 3 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 576989 = 216371) B216371
theorem B347723 : Blo 151794 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B1330789 : Blo 151794 1330789 := bstep (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) B249523
theorem B347777 : Blo 151794 347777 := bstep (se 2 (by rfl) ⟨130416, by rfl⟩ : syracuseStep 347777 = 260833) B260833
theorem B315019 : Blo 151794 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B347993 : Blo 151794 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B348083 : Blo 151794 348083 := bstep (se 1 (by rfl) ⟨261062, by rfl⟩ : syracuseStep 348083 = 522125) B522125
theorem B446411 : Blo 151794 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B348119 : Blo 151794 348119 := bstep (se 1 (by rfl) ⟨261089, by rfl⟩ : syracuseStep 348119 = 522179) B522179
theorem B348299 : Blo 151794 348299 := bstep (se 1 (by rfl) ⟨261224, by rfl⟩ : syracuseStep 348299 = 522449) B522449
theorem B348353 : Blo 151794 348353 := bstep (se 2 (by rfl) ⟨130632, by rfl⟩ : syracuseStep 348353 = 261265) B261265
theorem B151799 : Blo 151794 151799 := bstep (se 1 (by rfl) ⟨113849, by rfl⟩ : syracuseStep 151799 = 227699) B227699
theorem B151819 : Blo 151794 151819 := bstep (se 1 (by rfl) ⟨113864, by rfl⟩ : syracuseStep 151819 = 227729) B227729
theorem B250123 : Blo 151794 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B151831 : Blo 151794 151831 := bstep (se 1 (by rfl) ⟨113873, by rfl⟩ : syracuseStep 151831 = 227747) B227747
theorem B1331491 : Blo 151794 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1200419 : Blo 151794 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B151851 : Blo 151794 151851 := bstep (se 1 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 151851 = 227777) B227777
theorem B151863 : Blo 151794 151863 := bstep (se 1 (by rfl) ⟨113897, by rfl⟩ : syracuseStep 151863 = 227795) B227795
theorem B151883 : Blo 151794 151883 := bstep (se 1 (by rfl) ⟨113912, by rfl⟩ : syracuseStep 151883 = 227825) B227825
theorem B151895 : Blo 151794 151895 := bstep (se 1 (by rfl) ⟨113921, by rfl⟩ : syracuseStep 151895 = 227843) B227843
theorem B184663 : Blo 151794 184663 := bstep (se 1 (by rfl) ⟨138497, by rfl⟩ : syracuseStep 184663 = 276995) B276995
theorem B151915 : Blo 151794 151915 := bstep (se 1 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 151915 = 227873) B227873
theorem B151927 : Blo 151794 151927 := bstep (se 1 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 151927 = 227891) B227891
theorem B151947 : Blo 151794 151947 := bstep (se 1 (by rfl) ⟨113960, by rfl⟩ : syracuseStep 151947 = 227921) B227921
theorem B151959 : Blo 151794 151959 := bstep (se 1 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 151959 = 227939) B227939
theorem B348569 : Blo 151794 348569 := bstep (se 2 (by rfl) ⟨130713, by rfl⟩ : syracuseStep 348569 = 261427) B261427
theorem B151979 : Blo 151794 151979 := bstep (se 1 (by rfl) ⟨113984, by rfl⟩ : syracuseStep 151979 = 227969) B227969
theorem B151991 : Blo 151794 151991 := bstep (se 1 (by rfl) ⟨113993, by rfl⟩ : syracuseStep 151991 = 227987) B227987
theorem B512459 : Blo 151794 512459 := bstep (se 1 (by rfl) ⟨384344, by rfl⟩ : syracuseStep 512459 = 768689) B768689
theorem B152011 : Blo 151794 152011 := bstep (se 1 (by rfl) ⟨114008, by rfl⟩ : syracuseStep 152011 = 228017) B228017
theorem B152023 : Blo 151794 152023 := bstep (se 1 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 152023 = 228035) B228035
theorem B217561 : Blo 151794 217561 := bstep (se 2 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 217561 = 163171) B163171
theorem B152043 : Blo 151794 152043 := bstep (se 1 (by rfl) ⟨114032, by rfl⟩ : syracuseStep 152043 = 228065) B228065
theorem B348659 : Blo 151794 348659 := bstep (se 1 (by rfl) ⟨261494, by rfl⟩ : syracuseStep 348659 = 522989) B522989
theorem B152055 : Blo 151794 152055 := bstep (se 1 (by rfl) ⟨114041, by rfl⟩ : syracuseStep 152055 = 228083) B228083
theorem B152075 : Blo 151794 152075 := bstep (se 1 (by rfl) ⟨114056, by rfl⟩ : syracuseStep 152075 = 228113) B228113
theorem B872977 : Blo 151794 872977 := bstep (se 2 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 872977 = 654733) B654733
theorem B152087 : Blo 151794 152087 := bstep (se 1 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 152087 = 228131) B228131
theorem B348695 : Blo 151794 348695 := bstep (se 1 (by rfl) ⟨261521, by rfl⟩ : syracuseStep 348695 = 523043) B523043
theorem B152107 : Blo 151794 152107 := bstep (se 1 (by rfl) ⟨114080, by rfl⟩ : syracuseStep 152107 = 228161) B228161
theorem B152119 : Blo 151794 152119 := bstep (se 1 (by rfl) ⟨114089, by rfl⟩ : syracuseStep 152119 = 228179) B228179
theorem B152139 : Blo 151794 152139 := bstep (se 1 (by rfl) ⟨114104, by rfl⟩ : syracuseStep 152139 = 228209) B228209
theorem B217675 : Blo 151794 217675 := bstep (se 1 (by rfl) ⟨163256, by rfl⟩ : syracuseStep 217675 = 326513) B326513
theorem B152151 : Blo 151794 152151 := bstep (se 1 (by rfl) ⟨114113, by rfl⟩ : syracuseStep 152151 = 228227) B228227
theorem B152171 : Blo 151794 152171 := bstep (se 1 (by rfl) ⟨114128, by rfl⟩ : syracuseStep 152171 = 228257) B228257
theorem B152183 : Blo 151794 152183 := bstep (se 1 (by rfl) ⟨114137, by rfl⟩ : syracuseStep 152183 = 228275) B228275
theorem B152203 : Blo 151794 152203 := bstep (se 1 (by rfl) ⟨114152, by rfl⟩ : syracuseStep 152203 = 228305) B228305
theorem B152215 : Blo 151794 152215 := bstep (se 1 (by rfl) ⟨114161, by rfl⟩ : syracuseStep 152215 = 228323) B228323
theorem B152235 : Blo 151794 152235 := bstep (se 1 (by rfl) ⟨114176, by rfl⟩ : syracuseStep 152235 = 228353) B228353
theorem B152247 : Blo 151794 152247 := bstep (se 1 (by rfl) ⟨114185, by rfl⟩ : syracuseStep 152247 = 228371) B228371
theorem B152267 : Blo 151794 152267 := bstep (se 1 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 152267 = 228401) B228401
theorem B348875 : Blo 151794 348875 := bstep (se 1 (by rfl) ⟨261656, by rfl⟩ : syracuseStep 348875 = 523313) B523313
theorem B152279 : Blo 151794 152279 := bstep (se 1 (by rfl) ⟨114209, by rfl⟩ : syracuseStep 152279 = 228419) B228419
theorem B512729 : Blo 151794 512729 := bstep (se 2 (by rfl) ⟨192273, by rfl⟩ : syracuseStep 512729 = 384547) B384547
theorem B152299 : Blo 151794 152299 := bstep (se 1 (by rfl) ⟨114224, by rfl⟩ : syracuseStep 152299 = 228449) B228449
theorem B152311 : Blo 151794 152311 := bstep (se 1 (by rfl) ⟨114233, by rfl⟩ : syracuseStep 152311 = 228467) B228467
theorem B348929 : Blo 151794 348929 := bstep (se 2 (by rfl) ⟨130848, by rfl⟩ : syracuseStep 348929 = 261697) B261697
theorem B152331 : Blo 151794 152331 := bstep (se 1 (by rfl) ⟨114248, by rfl⟩ : syracuseStep 152331 = 228497) B228497
theorem B152343 : Blo 151794 152343 := bstep (se 1 (by rfl) ⟨114257, by rfl⟩ : syracuseStep 152343 = 228515) B228515
theorem B152363 : Blo 151794 152363 := bstep (se 1 (by rfl) ⟨114272, by rfl⟩ : syracuseStep 152363 = 228545) B228545
theorem B152375 : Blo 151794 152375 := bstep (se 1 (by rfl) ⟨114281, by rfl⟩ : syracuseStep 152375 = 228563) B228563
theorem B152395 : Blo 151794 152395 := bstep (se 1 (by rfl) ⟨114296, by rfl⟩ : syracuseStep 152395 = 228593) B228593
theorem B152407 : Blo 151794 152407 := bstep (se 1 (by rfl) ⟨114305, by rfl⟩ : syracuseStep 152407 = 228611) B228611
theorem B152427 : Blo 151794 152427 := bstep (se 1 (by rfl) ⟨114320, by rfl⟩ : syracuseStep 152427 = 228641) B228641
theorem B152439 : Blo 151794 152439 := bstep (se 1 (by rfl) ⟨114329, by rfl⟩ : syracuseStep 152439 = 228659) B228659
theorem B152459 : Blo 151794 152459 := bstep (se 1 (by rfl) ⟨114344, by rfl⟩ : syracuseStep 152459 = 228689) B228689
theorem B152471 : Blo 151794 152471 := bstep (se 1 (by rfl) ⟨114353, by rfl⟩ : syracuseStep 152471 = 228707) B228707
theorem B152491 : Blo 151794 152491 := bstep (se 1 (by rfl) ⟨114368, by rfl⟩ : syracuseStep 152491 = 228737) B228737
theorem B152503 : Blo 151794 152503 := bstep (se 1 (by rfl) ⟨114377, by rfl⟩ : syracuseStep 152503 = 228755) B228755
theorem B152523 : Blo 151794 152523 := bstep (se 1 (by rfl) ⟨114392, by rfl⟩ : syracuseStep 152523 = 228785) B228785
theorem B152535 : Blo 151794 152535 := bstep (se 1 (by rfl) ⟨114401, by rfl⟩ : syracuseStep 152535 = 228803) B228803
theorem B349145 : Blo 151794 349145 := bstep (se 2 (by rfl) ⟨130929, by rfl⟩ : syracuseStep 349145 = 261859) B261859
theorem B152555 : Blo 151794 152555 := bstep (se 1 (by rfl) ⟨114416, by rfl⟩ : syracuseStep 152555 = 228833) B228833
theorem B152567 : Blo 151794 152567 := bstep (se 1 (by rfl) ⟨114425, by rfl⟩ : syracuseStep 152567 = 228851) B228851
theorem B152587 : Blo 151794 152587 := bstep (se 1 (by rfl) ⟨114440, by rfl⟩ : syracuseStep 152587 = 228881) B228881
theorem B152599 : Blo 151794 152599 := bstep (se 1 (by rfl) ⟨114449, by rfl⟩ : syracuseStep 152599 = 228899) B228899
theorem B152619 : Blo 151794 152619 := bstep (se 1 (by rfl) ⟨114464, by rfl⟩ : syracuseStep 152619 = 228929) B228929
theorem B349235 : Blo 151794 349235 := bstep (se 1 (by rfl) ⟨261926, by rfl⟩ : syracuseStep 349235 = 523853) B523853
theorem B152631 : Blo 151794 152631 := bstep (se 1 (by rfl) ⟨114473, by rfl⟩ : syracuseStep 152631 = 228947) B228947
theorem B152651 : Blo 151794 152651 := bstep (se 1 (by rfl) ⟨114488, by rfl⟩ : syracuseStep 152651 = 228977) B228977
theorem B152663 : Blo 151794 152663 := bstep (se 1 (by rfl) ⟨114497, by rfl⟩ : syracuseStep 152663 = 228995) B228995
theorem B349271 : Blo 151794 349271 := bstep (se 1 (by rfl) ⟨261953, by rfl⟩ : syracuseStep 349271 = 523907) B523907
theorem B152683 : Blo 151794 152683 := bstep (se 1 (by rfl) ⟨114512, by rfl⟩ : syracuseStep 152683 = 229025) B229025
theorem B152695 : Blo 151794 152695 := bstep (se 1 (by rfl) ⟨114521, by rfl⟩ : syracuseStep 152695 = 229043) B229043
theorem B152715 : Blo 151794 152715 := bstep (se 1 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 152715 = 229073) B229073
theorem B152727 : Blo 151794 152727 := bstep (se 1 (by rfl) ⟨114545, by rfl⟩ : syracuseStep 152727 = 229091) B229091
theorem B152747 : Blo 151794 152747 := bstep (se 1 (by rfl) ⟨114560, by rfl⟩ : syracuseStep 152747 = 229121) B229121
theorem B152759 : Blo 151794 152759 := bstep (se 1 (by rfl) ⟨114569, by rfl⟩ : syracuseStep 152759 = 229139) B229139
theorem B152779 : Blo 151794 152779 := bstep (se 1 (by rfl) ⟨114584, by rfl⟩ : syracuseStep 152779 = 229169) B229169
theorem B152791 : Blo 151794 152791 := bstep (se 1 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 152791 = 229187) B229187
theorem B152811 : Blo 151794 152811 := bstep (se 1 (by rfl) ⟨114608, by rfl⟩ : syracuseStep 152811 = 229217) B229217
theorem B152823 : Blo 151794 152823 := bstep (se 1 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 152823 = 229235) B229235
theorem B152843 : Blo 151794 152843 := bstep (se 1 (by rfl) ⟨114632, by rfl⟩ : syracuseStep 152843 = 229265) B229265
theorem B349451 : Blo 151794 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B152855 : Blo 151794 152855 := bstep (se 1 (by rfl) ⟨114641, by rfl⟩ : syracuseStep 152855 = 229283) B229283
theorem B152875 : Blo 151794 152875 := bstep (se 1 (by rfl) ⟨114656, by rfl⟩ : syracuseStep 152875 = 229313) B229313
theorem B152887 : Blo 151794 152887 := bstep (se 1 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 152887 = 229331) B229331
theorem B349505 : Blo 151794 349505 := bstep (se 2 (by rfl) ⟨131064, by rfl⟩ : syracuseStep 349505 = 262129) B262129
theorem B152907 : Blo 151794 152907 := bstep (se 1 (by rfl) ⟨114680, by rfl⟩ : syracuseStep 152907 = 229361) B229361
theorem B152919 : Blo 151794 152919 := bstep (se 1 (by rfl) ⟨114689, by rfl⟩ : syracuseStep 152919 = 229379) B229379
theorem B152939 : Blo 151794 152939 := bstep (se 1 (by rfl) ⟨114704, by rfl⟩ : syracuseStep 152939 = 229409) B229409
theorem B152951 : Blo 151794 152951 := bstep (se 1 (by rfl) ⟨114713, by rfl⟩ : syracuseStep 152951 = 229427) B229427
theorem B578947 : Blo 151794 578947 := bstep (se 1 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 578947 = 868421) B868421
theorem B152971 : Blo 151794 152971 := bstep (se 1 (by rfl) ⟨114728, by rfl⟩ : syracuseStep 152971 = 229457) B229457
theorem B513431 : Blo 151794 513431 := bstep (se 1 (by rfl) ⟨385073, by rfl⟩ : syracuseStep 513431 = 770147) B770147
theorem B152983 : Blo 151794 152983 := bstep (se 1 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 152983 = 229475) B229475
theorem B153003 : Blo 151794 153003 := bstep (se 1 (by rfl) ⟨114752, by rfl⟩ : syracuseStep 153003 = 229505) B229505
theorem B153015 : Blo 151794 153015 := bstep (se 1 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 153015 = 229523) B229523
theorem B153035 : Blo 151794 153035 := bstep (se 1 (by rfl) ⟨114776, by rfl⟩ : syracuseStep 153035 = 229553) B229553
theorem B153047 : Blo 151794 153047 := bstep (se 1 (by rfl) ⟨114785, by rfl⟩ : syracuseStep 153047 = 229571) B229571
theorem B153067 : Blo 151794 153067 := bstep (se 1 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 153067 = 229601) B229601
theorem B153079 : Blo 151794 153079 := bstep (se 1 (by rfl) ⟨114809, by rfl⟩ : syracuseStep 153079 = 229619) B229619
theorem B153099 : Blo 151794 153099 := bstep (se 1 (by rfl) ⟨114824, by rfl⟩ : syracuseStep 153099 = 229649) B229649
theorem B153111 : Blo 151794 153111 := bstep (se 1 (by rfl) ⟨114833, by rfl⟩ : syracuseStep 153111 = 229667) B229667
theorem B349721 : Blo 151794 349721 := bstep (se 2 (by rfl) ⟨131145, by rfl⟩ : syracuseStep 349721 = 262291) B262291
theorem B153131 : Blo 151794 153131 := bstep (se 1 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 153131 = 229697) B229697
theorem B153143 : Blo 151794 153143 := bstep (se 1 (by rfl) ⟨114857, by rfl⟩ : syracuseStep 153143 = 229715) B229715
theorem B153163 : Blo 151794 153163 := bstep (se 1 (by rfl) ⟨114872, by rfl⟩ : syracuseStep 153163 = 229745) B229745
theorem B153175 : Blo 151794 153175 := bstep (se 1 (by rfl) ⟨114881, by rfl⟩ : syracuseStep 153175 = 229763) B229763
theorem B153195 : Blo 151794 153195 := bstep (se 1 (by rfl) ⟨114896, by rfl⟩ : syracuseStep 153195 = 229793) B229793
theorem B349811 : Blo 151794 349811 := bstep (se 1 (by rfl) ⟨262358, by rfl⟩ : syracuseStep 349811 = 524717) B524717
theorem B153207 : Blo 151794 153207 := bstep (se 1 (by rfl) ⟨114905, by rfl⟩ : syracuseStep 153207 = 229811) B229811
theorem B153227 : Blo 151794 153227 := bstep (se 1 (by rfl) ⟨114920, by rfl⟩ : syracuseStep 153227 = 229841) B229841
theorem B153239 : Blo 151794 153239 := bstep (se 1 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 153239 = 229859) B229859
theorem B349847 : Blo 151794 349847 := bstep (se 1 (by rfl) ⟨262385, by rfl⟩ : syracuseStep 349847 = 524771) B524771
theorem B153259 : Blo 151794 153259 := bstep (se 1 (by rfl) ⟨114944, by rfl⟩ : syracuseStep 153259 = 229889) B229889
theorem B579251 : Blo 151794 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B153271 : Blo 151794 153271 := bstep (se 1 (by rfl) ⟨114953, by rfl⟩ : syracuseStep 153271 = 229907) B229907
theorem B153291 : Blo 151794 153291 := bstep (se 1 (by rfl) ⟨114968, by rfl⟩ : syracuseStep 153291 = 229937) B229937
theorem B153303 : Blo 151794 153303 := bstep (se 1 (by rfl) ⟨114977, by rfl⟩ : syracuseStep 153303 = 229955) B229955
theorem B153323 : Blo 151794 153323 := bstep (se 1 (by rfl) ⟨114992, by rfl⟩ : syracuseStep 153323 = 229985) B229985
theorem B153335 : Blo 151794 153335 := bstep (se 1 (by rfl) ⟨115001, by rfl⟩ : syracuseStep 153335 = 230003) B230003
theorem B2807557 : Blo 151794 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B153355 : Blo 151794 153355 := bstep (se 1 (by rfl) ⟨115016, by rfl⟩ : syracuseStep 153355 = 230033) B230033
theorem B153367 : Blo 151794 153367 := bstep (se 1 (by rfl) ⟨115025, by rfl⟩ : syracuseStep 153367 = 230051) B230051
theorem B153387 : Blo 151794 153387 := bstep (se 1 (by rfl) ⟨115040, by rfl⟩ : syracuseStep 153387 = 230081) B230081
theorem B153399 : Blo 151794 153399 := bstep (se 1 (by rfl) ⟨115049, by rfl⟩ : syracuseStep 153399 = 230099) B230099
theorem B153419 : Blo 151794 153419 := bstep (se 1 (by rfl) ⟨115064, by rfl⟩ : syracuseStep 153419 = 230129) B230129
theorem B350027 : Blo 151794 350027 := bstep (se 1 (by rfl) ⟨262520, by rfl⟩ : syracuseStep 350027 = 525041) B525041
theorem B153431 : Blo 151794 153431 := bstep (se 1 (by rfl) ⟨115073, by rfl⟩ : syracuseStep 153431 = 230147) B230147
theorem B153451 : Blo 151794 153451 := bstep (se 1 (by rfl) ⟨115088, by rfl⟩ : syracuseStep 153451 = 230177) B230177
theorem B153463 : Blo 151794 153463 := bstep (se 1 (by rfl) ⟨115097, by rfl⟩ : syracuseStep 153463 = 230195) B230195
theorem B350081 : Blo 151794 350081 := bstep (se 2 (by rfl) ⟨131280, by rfl⟩ : syracuseStep 350081 = 262561) B262561
theorem B841603 : Blo 151794 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B153483 : Blo 151794 153483 := bstep (se 1 (by rfl) ⟨115112, by rfl⟩ : syracuseStep 153483 = 230225) B230225
theorem B219019 : Blo 151794 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B153495 : Blo 151794 153495 := bstep (se 1 (by rfl) ⟨115121, by rfl⟩ : syracuseStep 153495 = 230243) B230243
theorem B153515 : Blo 151794 153515 := bstep (se 1 (by rfl) ⟨115136, by rfl⟩ : syracuseStep 153515 = 230273) B230273
theorem B513971 : Blo 151794 513971 := bstep (se 1 (by rfl) ⟨385478, by rfl⟩ : syracuseStep 513971 = 770957) B770957
theorem B153527 : Blo 151794 153527 := bstep (se 1 (by rfl) ⟨115145, by rfl⟩ : syracuseStep 153527 = 230291) B230291
theorem B153547 : Blo 151794 153547 := bstep (se 1 (by rfl) ⟨115160, by rfl⟩ : syracuseStep 153547 = 230321) B230321
theorem B153559 : Blo 151794 153559 := bstep (se 1 (by rfl) ⟨115169, by rfl⟩ : syracuseStep 153559 = 230339) B230339
theorem B153579 : Blo 151794 153579 := bstep (se 1 (by rfl) ⟨115184, by rfl⟩ : syracuseStep 153579 = 230369) B230369
theorem B153591 : Blo 151794 153591 := bstep (se 1 (by rfl) ⟨115193, by rfl⟩ : syracuseStep 153591 = 230387) B230387
theorem B153611 : Blo 151794 153611 := bstep (se 1 (by rfl) ⟨115208, by rfl⟩ : syracuseStep 153611 = 230417) B230417
theorem B153623 : Blo 151794 153623 := bstep (se 1 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 153623 = 230435) B230435
theorem B3299363 : Blo 151794 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B153643 : Blo 151794 153643 := bstep (se 1 (by rfl) ⟨115232, by rfl⟩ : syracuseStep 153643 = 230465) B230465
theorem B153655 : Blo 151794 153655 := bstep (se 1 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 153655 = 230483) B230483
theorem B153675 : Blo 151794 153675 := bstep (se 1 (by rfl) ⟨115256, by rfl⟩ : syracuseStep 153675 = 230513) B230513
theorem B153687 : Blo 151794 153687 := bstep (se 1 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 153687 = 230531) B230531
theorem B350297 : Blo 151794 350297 := bstep (se 2 (by rfl) ⟨131361, by rfl⟩ : syracuseStep 350297 = 262723) B262723
theorem B153707 : Blo 151794 153707 := bstep (se 1 (by rfl) ⟨115280, by rfl⟩ : syracuseStep 153707 = 230561) B230561
theorem B153719 : Blo 151794 153719 := bstep (se 1 (by rfl) ⟨115289, by rfl⟩ : syracuseStep 153719 = 230579) B230579
theorem B153739 : Blo 151794 153739 := bstep (se 1 (by rfl) ⟨115304, by rfl⟩ : syracuseStep 153739 = 230609) B230609
theorem B153751 : Blo 151794 153751 := bstep (se 1 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 153751 = 230627) B230627
theorem B219287 : Blo 151794 219287 := bstep (se 1 (by rfl) ⟨164465, by rfl⟩ : syracuseStep 219287 = 328931) B328931
theorem B153771 : Blo 151794 153771 := bstep (se 1 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 153771 = 230657) B230657
theorem B350387 : Blo 151794 350387 := bstep (se 1 (by rfl) ⟨262790, by rfl⟩ : syracuseStep 350387 = 525581) B525581
theorem B153783 : Blo 151794 153783 := bstep (se 1 (by rfl) ⟨115337, by rfl⟩ : syracuseStep 153783 = 230675) B230675
theorem B514241 : Blo 151794 514241 := bstep (se 2 (by rfl) ⟨192840, by rfl⟩ : syracuseStep 514241 = 385681) B385681
theorem B153803 : Blo 151794 153803 := bstep (se 1 (by rfl) ⟨115352, by rfl⟩ : syracuseStep 153803 = 230705) B230705
theorem B153815 : Blo 151794 153815 := bstep (se 1 (by rfl) ⟨115361, by rfl⟩ : syracuseStep 153815 = 230723) B230723
theorem B350423 : Blo 151794 350423 := bstep (se 1 (by rfl) ⟨262817, by rfl⟩ : syracuseStep 350423 = 525635) B525635
theorem B153835 : Blo 151794 153835 := bstep (se 1 (by rfl) ⟨115376, by rfl⟩ : syracuseStep 153835 = 230753) B230753
theorem B153847 : Blo 151794 153847 := bstep (se 1 (by rfl) ⟨115385, by rfl⟩ : syracuseStep 153847 = 230771) B230771
theorem B153867 : Blo 151794 153867 := bstep (se 1 (by rfl) ⟨115400, by rfl⟩ : syracuseStep 153867 = 230801) B230801
theorem B776465 : Blo 151794 776465 := bstep (se 2 (by rfl) ⟨291174, by rfl⟩ : syracuseStep 776465 = 582349) B582349
theorem B153879 : Blo 151794 153879 := bstep (se 1 (by rfl) ⟨115409, by rfl⟩ : syracuseStep 153879 = 230819) B230819
theorem B153899 : Blo 151794 153899 := bstep (se 1 (by rfl) ⟨115424, by rfl⟩ : syracuseStep 153899 = 230849) B230849
theorem B153911 : Blo 151794 153911 := bstep (se 1 (by rfl) ⟨115433, by rfl⟩ : syracuseStep 153911 = 230867) B230867
theorem B2644289 : Blo 151794 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B579905 : Blo 151794 579905 := bstep (se 2 (by rfl) ⟨217464, by rfl⟩ : syracuseStep 579905 = 434929) B434929
theorem B153931 : Blo 151794 153931 := bstep (se 1 (by rfl) ⟨115448, by rfl⟩ : syracuseStep 153931 = 230897) B230897
theorem B153943 : Blo 151794 153943 := bstep (se 1 (by rfl) ⟨115457, by rfl⟩ : syracuseStep 153943 = 230915) B230915
theorem B153963 : Blo 151794 153963 := bstep (se 1 (by rfl) ⟨115472, by rfl⟩ : syracuseStep 153963 = 230945) B230945
theorem B153975 : Blo 151794 153975 := bstep (se 1 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 153975 = 230963) B230963
theorem B153995 : Blo 151794 153995 := bstep (se 1 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 153995 = 230993) B230993
theorem B154007 : Blo 151794 154007 := bstep (se 1 (by rfl) ⟨115505, by rfl⟩ : syracuseStep 154007 = 231011) B231011
theorem B154027 : Blo 151794 154027 := bstep (se 1 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 154027 = 231041) B231041
theorem B776627 : Blo 151794 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B154039 : Blo 151794 154039 := bstep (se 1 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 154039 = 231059) B231059
theorem B154059 : Blo 151794 154059 := bstep (se 1 (by rfl) ⟨115544, by rfl⟩ : syracuseStep 154059 = 231089) B231089
theorem B154071 : Blo 151794 154071 := bstep (se 1 (by rfl) ⟨115553, by rfl⟩ : syracuseStep 154071 = 231107) B231107
theorem B154091 : Blo 151794 154091 := bstep (se 1 (by rfl) ⟨115568, by rfl⟩ : syracuseStep 154091 = 231137) B231137
theorem B154103 : Blo 151794 154103 := bstep (se 1 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 154103 = 231155) B231155
theorem B154123 : Blo 151794 154123 := bstep (se 1 (by rfl) ⟨115592, by rfl⟩ : syracuseStep 154123 = 231185) B231185
theorem B1989137 : Blo 151794 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1104401 : Blo 151794 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B154135 : Blo 151794 154135 := bstep (se 1 (by rfl) ⟨115601, by rfl⟩ : syracuseStep 154135 = 231203) B231203
theorem B2382371 : Blo 151794 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B154155 : Blo 151794 154155 := bstep (se 1 (by rfl) ⟨115616, by rfl⟩ : syracuseStep 154155 = 231233) B231233
theorem B154167 : Blo 151794 154167 := bstep (se 1 (by rfl) ⟨115625, by rfl⟩ : syracuseStep 154167 = 231251) B231251
theorem B154187 : Blo 151794 154187 := bstep (se 1 (by rfl) ⟨115640, by rfl⟩ : syracuseStep 154187 = 231281) B231281
theorem B154199 : Blo 151794 154199 := bstep (se 1 (by rfl) ⟨115649, by rfl⟩ : syracuseStep 154199 = 231299) B231299
theorem B1464925 : Blo 151794 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B154219 : Blo 151794 154219 := bstep (se 1 (by rfl) ⟨115664, by rfl⟩ : syracuseStep 154219 = 231329) B231329
theorem B154231 : Blo 151794 154231 := bstep (se 1 (by rfl) ⟨115673, by rfl⟩ : syracuseStep 154231 = 231347) B231347
theorem B154251 : Blo 151794 154251 := bstep (se 1 (by rfl) ⟨115688, by rfl⟩ : syracuseStep 154251 = 231377) B231377
theorem B154263 : Blo 151794 154263 := bstep (se 1 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 154263 = 231395) B231395
theorem B154283 : Blo 151794 154283 := bstep (se 1 (by rfl) ⟨115712, by rfl⟩ : syracuseStep 154283 = 231425) B231425
theorem B154295 : Blo 151794 154295 := bstep (se 1 (by rfl) ⟨115721, by rfl⟩ : syracuseStep 154295 = 231443) B231443
theorem B154315 : Blo 151794 154315 := bstep (se 1 (by rfl) ⟨115736, by rfl⟩ : syracuseStep 154315 = 231473) B231473
theorem B154327 : Blo 151794 154327 := bstep (se 1 (by rfl) ⟨115745, by rfl⟩ : syracuseStep 154327 = 231491) B231491
theorem B514781 : Blo 151794 514781 := bstep (se 3 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 514781 = 193043) B193043
theorem B154347 : Blo 151794 154347 := bstep (se 1 (by rfl) ⟨115760, by rfl⟩ : syracuseStep 154347 = 231521) B231521
theorem B154359 : Blo 151794 154359 := bstep (se 1 (by rfl) ⟨115769, by rfl⟩ : syracuseStep 154359 = 231539) B231539
theorem B154379 : Blo 151794 154379 := bstep (se 1 (by rfl) ⟨115784, by rfl⟩ : syracuseStep 154379 = 231569) B231569
theorem B154391 : Blo 151794 154391 := bstep (se 1 (by rfl) ⟨115793, by rfl⟩ : syracuseStep 154391 = 231587) B231587
theorem B154411 : Blo 151794 154411 := bstep (se 1 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 154411 = 231617) B231617
theorem B154423 : Blo 151794 154423 := bstep (se 1 (by rfl) ⟨115817, by rfl⟩ : syracuseStep 154423 = 231635) B231635
theorem B1170251 : Blo 151794 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B154443 : Blo 151794 154443 := bstep (se 1 (by rfl) ⟨115832, by rfl⟩ : syracuseStep 154443 = 231665) B231665
theorem B154455 : Blo 151794 154455 := bstep (se 1 (by rfl) ⟨115841, by rfl⟩ : syracuseStep 154455 = 231683) B231683
theorem B351065 : Blo 151794 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B154475 : Blo 151794 154475 := bstep (se 1 (by rfl) ⟨115856, by rfl⟩ : syracuseStep 154475 = 231713) B231713
theorem B154487 : Blo 151794 154487 := bstep (se 1 (by rfl) ⟨115865, by rfl⟩ : syracuseStep 154487 = 231731) B231731
theorem B154507 : Blo 151794 154507 := bstep (se 1 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 154507 = 231761) B231761
theorem B154519 : Blo 151794 154519 := bstep (se 1 (by rfl) ⟨115889, by rfl⟩ : syracuseStep 154519 = 231779) B231779
theorem B154539 : Blo 151794 154539 := bstep (se 1 (by rfl) ⟨115904, by rfl⟩ : syracuseStep 154539 = 231809) B231809
theorem B154551 : Blo 151794 154551 := bstep (se 1 (by rfl) ⟨115913, by rfl⟩ : syracuseStep 154551 = 231827) B231827
theorem B154571 : Blo 151794 154571 := bstep (se 1 (by rfl) ⟨115928, by rfl⟩ : syracuseStep 154571 = 231857) B231857
theorem B154583 : Blo 151794 154583 := bstep (se 1 (by rfl) ⟨115937, by rfl⟩ : syracuseStep 154583 = 231875) B231875
theorem B154603 : Blo 151794 154603 := bstep (se 1 (by rfl) ⟨115952, by rfl⟩ : syracuseStep 154603 = 231905) B231905
theorem B154615 : Blo 151794 154615 := bstep (se 1 (by rfl) ⟨115961, by rfl⟩ : syracuseStep 154615 = 231923) B231923
theorem B154635 : Blo 151794 154635 := bstep (se 1 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 154635 = 231953) B231953
theorem B154647 : Blo 151794 154647 := bstep (se 1 (by rfl) ⟨115985, by rfl⟩ : syracuseStep 154647 = 231971) B231971
theorem B154667 : Blo 151794 154667 := bstep (se 1 (by rfl) ⟨116000, by rfl⟩ : syracuseStep 154667 = 232001) B232001
theorem B154679 : Blo 151794 154679 := bstep (se 1 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 154679 = 232019) B232019
theorem B154699 : Blo 151794 154699 := bstep (se 1 (by rfl) ⟨116024, by rfl⟩ : syracuseStep 154699 = 232049) B232049
theorem B154711 : Blo 151794 154711 := bstep (se 1 (by rfl) ⟨116033, by rfl⟩ : syracuseStep 154711 = 232067) B232067
theorem B220249 : Blo 151794 220249 := bstep (se 2 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 220249 = 165187) B165187
theorem B154731 : Blo 151794 154731 := bstep (se 1 (by rfl) ⟨116048, by rfl⟩ : syracuseStep 154731 = 232097) B232097
theorem B154743 : Blo 151794 154743 := bstep (se 1 (by rfl) ⟨116057, by rfl⟩ : syracuseStep 154743 = 232115) B232115
theorem B154763 : Blo 151794 154763 := bstep (se 1 (by rfl) ⟨116072, by rfl⟩ : syracuseStep 154763 = 232145) B232145
theorem B154775 : Blo 151794 154775 := bstep (se 1 (by rfl) ⟨116081, by rfl⟩ : syracuseStep 154775 = 232163) B232163
theorem B154795 : Blo 151794 154795 := bstep (se 1 (by rfl) ⟨116096, by rfl⟩ : syracuseStep 154795 = 232193) B232193
theorem B154807 : Blo 151794 154807 := bstep (se 1 (by rfl) ⟨116105, by rfl⟩ : syracuseStep 154807 = 232211) B232211
theorem B154827 : Blo 151794 154827 := bstep (se 1 (by rfl) ⟨116120, by rfl⟩ : syracuseStep 154827 = 232241) B232241
theorem B154839 : Blo 151794 154839 := bstep (se 1 (by rfl) ⟨116129, by rfl⟩ : syracuseStep 154839 = 232259) B232259
theorem B351449 : Blo 151794 351449 := bstep (se 2 (by rfl) ⟨131793, by rfl⟩ : syracuseStep 351449 = 263587) B263587
theorem B154859 : Blo 151794 154859 := bstep (se 1 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 154859 = 232289) B232289
theorem B154871 : Blo 151794 154871 := bstep (se 1 (by rfl) ⟨116153, by rfl⟩ : syracuseStep 154871 = 232307) B232307
theorem B154891 : Blo 151794 154891 := bstep (se 1 (by rfl) ⟨116168, by rfl⟩ : syracuseStep 154891 = 232337) B232337
theorem B154903 : Blo 151794 154903 := bstep (se 1 (by rfl) ⟨116177, by rfl⟩ : syracuseStep 154903 = 232355) B232355
theorem B154923 : Blo 151794 154923 := bstep (se 1 (by rfl) ⟨116192, by rfl⟩ : syracuseStep 154923 = 232385) B232385
theorem B154935 : Blo 151794 154935 := bstep (se 1 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 154935 = 232403) B232403
theorem B154955 : Blo 151794 154955 := bstep (se 1 (by rfl) ⟨116216, by rfl⟩ : syracuseStep 154955 = 232433) B232433
theorem B154967 : Blo 151794 154967 := bstep (se 1 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 154967 = 232451) B232451
theorem B154987 : Blo 151794 154987 := bstep (se 1 (by rfl) ⟨116240, by rfl⟩ : syracuseStep 154987 = 232481) B232481
theorem B154999 : Blo 151794 154999 := bstep (se 1 (by rfl) ⟨116249, by rfl⟩ : syracuseStep 154999 = 232499) B232499
theorem B155019 : Blo 151794 155019 := bstep (se 1 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 155019 = 232529) B232529
theorem B155031 : Blo 151794 155031 := bstep (se 1 (by rfl) ⟨116273, by rfl⟩ : syracuseStep 155031 = 232547) B232547
theorem B155051 : Blo 151794 155051 := bstep (se 1 (by rfl) ⟨116288, by rfl⟩ : syracuseStep 155051 = 232577) B232577
theorem B155063 : Blo 151794 155063 := bstep (se 1 (by rfl) ⟨116297, by rfl⟩ : syracuseStep 155063 = 232595) B232595
theorem B155083 : Blo 151794 155083 := bstep (se 1 (by rfl) ⟨116312, by rfl⟩ : syracuseStep 155083 = 232625) B232625
theorem B155095 : Blo 151794 155095 := bstep (se 1 (by rfl) ⟨116321, by rfl⟩ : syracuseStep 155095 = 232643) B232643
theorem B155115 : Blo 151794 155115 := bstep (se 1 (by rfl) ⟨116336, by rfl⟩ : syracuseStep 155115 = 232673) B232673
theorem B155127 : Blo 151794 155127 := bstep (se 1 (by rfl) ⟨116345, by rfl⟩ : syracuseStep 155127 = 232691) B232691
theorem B155147 : Blo 151794 155147 := bstep (se 1 (by rfl) ⟨116360, by rfl⟩ : syracuseStep 155147 = 232721) B232721
theorem B155159 : Blo 151794 155159 := bstep (se 1 (by rfl) ⟨116369, by rfl⟩ : syracuseStep 155159 = 232739) B232739
theorem B155179 : Blo 151794 155179 := bstep (se 1 (by rfl) ⟨116384, by rfl⟩ : syracuseStep 155179 = 232769) B232769
theorem B581165 : Blo 151794 581165 := bstep (se 3 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 581165 = 217937) B217937
theorem B155191 : Blo 151794 155191 := bstep (se 1 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 155191 = 232787) B232787
theorem B581195 : Blo 151794 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B155211 : Blo 151794 155211 := bstep (se 1 (by rfl) ⟨116408, by rfl⟩ : syracuseStep 155211 = 232817) B232817
theorem B155223 : Blo 151794 155223 := bstep (se 1 (by rfl) ⟨116417, by rfl⟩ : syracuseStep 155223 = 232835) B232835
theorem B155243 : Blo 151794 155243 := bstep (se 1 (by rfl) ⟨116432, by rfl⟩ : syracuseStep 155243 = 232865) B232865
theorem B155255 : Blo 151794 155255 := bstep (se 1 (by rfl) ⟨116441, by rfl⟩ : syracuseStep 155255 = 232883) B232883
theorem B155275 : Blo 151794 155275 := bstep (se 1 (by rfl) ⟨116456, by rfl⟩ : syracuseStep 155275 = 232913) B232913
theorem B155287 : Blo 151794 155287 := bstep (se 1 (by rfl) ⟨116465, by rfl⟩ : syracuseStep 155287 = 232931) B232931
theorem B155307 : Blo 151794 155307 := bstep (se 1 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 155307 = 232961) B232961
theorem B155319 : Blo 151794 155319 := bstep (se 1 (by rfl) ⟨116489, by rfl⟩ : syracuseStep 155319 = 232979) B232979
theorem B155339 : Blo 151794 155339 := bstep (se 1 (by rfl) ⟨116504, by rfl⟩ : syracuseStep 155339 = 233009) B233009
theorem B351959 : Blo 151794 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B155351 : Blo 151794 155351 := bstep (se 1 (by rfl) ⟨116513, by rfl⟩ : syracuseStep 155351 = 233027) B233027
theorem B155371 : Blo 151794 155371 := bstep (se 1 (by rfl) ⟨116528, by rfl⟩ : syracuseStep 155371 = 233057) B233057
theorem B155383 : Blo 151794 155383 := bstep (se 1 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 155383 = 233075) B233075
theorem B155403 : Blo 151794 155403 := bstep (se 1 (by rfl) ⟨116552, by rfl⟩ : syracuseStep 155403 = 233105) B233105
theorem B155415 : Blo 151794 155415 := bstep (se 1 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 155415 = 233123) B233123
theorem B155435 : Blo 151794 155435 := bstep (se 1 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 155435 = 233153) B233153
theorem B155447 : Blo 151794 155447 := bstep (se 1 (by rfl) ⟨116585, by rfl⟩ : syracuseStep 155447 = 233171) B233171
theorem B515915 : Blo 151794 515915 := bstep (se 1 (by rfl) ⟨386936, by rfl⟩ : syracuseStep 515915 = 773873) B773873
theorem B417611 : Blo 151794 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B155467 : Blo 151794 155467 := bstep (se 1 (by rfl) ⟨116600, by rfl⟩ : syracuseStep 155467 = 233201) B233201
theorem B155479 : Blo 151794 155479 := bstep (se 1 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 155479 = 233219) B233219
theorem B155499 : Blo 151794 155499 := bstep (se 1 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 155499 = 233249) B233249
theorem B155511 : Blo 151794 155511 := bstep (se 1 (by rfl) ⟨116633, by rfl⟩ : syracuseStep 155511 = 233267) B233267
theorem B876419 : Blo 151794 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B155531 : Blo 151794 155531 := bstep (se 1 (by rfl) ⟨116648, by rfl⟩ : syracuseStep 155531 = 233297) B233297
theorem B155543 : Blo 151794 155543 := bstep (se 1 (by rfl) ⟨116657, by rfl⟩ : syracuseStep 155543 = 233315) B233315
theorem B155563 : Blo 151794 155563 := bstep (se 1 (by rfl) ⟨116672, by rfl⟩ : syracuseStep 155563 = 233345) B233345
theorem B155575 : Blo 151794 155575 := bstep (se 1 (by rfl) ⟨116681, by rfl⟩ : syracuseStep 155575 = 233363) B233363
theorem B548801 : Blo 151794 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B155595 : Blo 151794 155595 := bstep (se 1 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 155595 = 233393) B233393
theorem B155607 : Blo 151794 155607 := bstep (se 1 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 155607 = 233411) B233411
theorem B155627 : Blo 151794 155627 := bstep (se 1 (by rfl) ⟨116720, by rfl⟩ : syracuseStep 155627 = 233441) B233441
theorem B155639 : Blo 151794 155639 := bstep (se 1 (by rfl) ⟨116729, by rfl⟩ : syracuseStep 155639 = 233459) B233459
theorem B155659 : Blo 151794 155659 := bstep (se 1 (by rfl) ⟨116744, by rfl⟩ : syracuseStep 155659 = 233489) B233489
theorem B155671 : Blo 151794 155671 := bstep (se 1 (by rfl) ⟨116753, by rfl⟩ : syracuseStep 155671 = 233507) B233507
theorem B155691 : Blo 151794 155691 := bstep (se 1 (by rfl) ⟨116768, by rfl⟩ : syracuseStep 155691 = 233537) B233537
theorem B155703 : Blo 151794 155703 := bstep (se 1 (by rfl) ⟨116777, by rfl⟩ : syracuseStep 155703 = 233555) B233555
theorem B155723 : Blo 151794 155723 := bstep (se 1 (by rfl) ⟨116792, by rfl⟩ : syracuseStep 155723 = 233585) B233585
theorem B155735 : Blo 151794 155735 := bstep (se 1 (by rfl) ⟨116801, by rfl⟩ : syracuseStep 155735 = 233603) B233603
theorem B516185 : Blo 151794 516185 := bstep (se 2 (by rfl) ⟨193569, by rfl⟩ : syracuseStep 516185 = 387139) B387139
theorem B155755 : Blo 151794 155755 := bstep (se 1 (by rfl) ⟨116816, by rfl⟩ : syracuseStep 155755 = 233633) B233633
theorem B155767 : Blo 151794 155767 := bstep (se 1 (by rfl) ⟨116825, by rfl⟩ : syracuseStep 155767 = 233651) B233651
theorem B155787 : Blo 151794 155787 := bstep (se 1 (by rfl) ⟨116840, by rfl⟩ : syracuseStep 155787 = 233681) B233681
theorem B385175 : Blo 151794 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B581849 : Blo 151794 581849 := bstep (se 2 (by rfl) ⟨218193, by rfl⟩ : syracuseStep 581849 = 436387) B436387
theorem B942353 : Blo 151794 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B778571 : Blo 151794 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B8348021 : Blo 151794 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B221707 : Blo 151794 221707 := bstep (se 1 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 221707 = 332561) B332561
theorem B582167 : Blo 151794 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B221719 : Blo 151794 221719 := bstep (se 1 (by rfl) ⟨166289, by rfl⟩ : syracuseStep 221719 = 332579) B332579
theorem B1663523 : Blo 151794 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B287297 : Blo 151794 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B975539 : Blo 151794 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B516887 : Blo 151794 516887 := bstep (se 1 (by rfl) ⟨387665, by rfl⟩ : syracuseStep 516887 = 775331) B775331
theorem B385843 : Blo 151794 385843 := bstep (se 1 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 385843 = 578765) B578765
theorem B385985 : Blo 151794 385985 := bstep (se 2 (by rfl) ⟨144744, by rfl⟩ : syracuseStep 385985 = 289489) B289489
theorem B1860569 : Blo 151794 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B582835 : Blo 151794 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B1336621 : Blo 151794 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B517427 : Blo 151794 517427 := bstep (se 1 (by rfl) ⟨388070, by rfl⟩ : syracuseStep 517427 = 776141) B776141
theorem B2352563 : Blo 151794 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B1598899 : Blo 151794 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B648755 : Blo 151794 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B517697 : Blo 151794 517697 := bstep (se 2 (by rfl) ⟨194136, by rfl⟩ : syracuseStep 517697 = 388273) B388273
theorem B1009217 : Blo 151794 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B157675 : Blo 151794 157675 := bstep (se 1 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 157675 = 236513) B236513
theorem B780353 : Blo 151794 780353 := bstep (se 2 (by rfl) ⟨292632, by rfl⟩ : syracuseStep 780353 = 585265) B585265
theorem B518237 : Blo 151794 518237 := bstep (se 3 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 518237 = 194339) B194339
theorem B387251 : Blo 151794 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B878809 : Blo 151794 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B256331 : Blo 151794 256331 := bstep (se 1 (by rfl) ⟨192248, by rfl⟩ : syracuseStep 256331 = 384497) B384497
theorem B2615651 : Blo 151794 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B289163 : Blo 151794 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B584081 : Blo 151794 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B256459 : Blo 151794 256459 := bstep (se 1 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 256459 = 384689) B384689
theorem B649745 : Blo 151794 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B1239569 : Blo 151794 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B289345 : Blo 151794 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B2255435 : Blo 151794 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B256601 : Blo 151794 256601 := bstep (se 2 (by rfl) ⟨96225, by rfl⟩ : syracuseStep 256601 = 192451) B192451
theorem B551569 : Blo 151794 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B387787 : Blo 151794 387787 := bstep (se 1 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 387787 = 581681) B581681
theorem B256729 : Blo 151794 256729 := bstep (se 2 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 256729 = 192547) B192547
theorem B387929 : Blo 151794 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B977795 : Blo 151794 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B289793 : Blo 151794 289793 := bstep (se 2 (by rfl) ⟨108672, by rfl⟩ : syracuseStep 289793 = 217345) B217345
theorem B584779 : Blo 151794 584779 := bstep (se 1 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 584779 = 877169) B877169
theorem B879767 : Blo 151794 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B519371 : Blo 151794 519371 := bstep (se 1 (by rfl) ⟨389528, by rfl⟩ : syracuseStep 519371 = 779057) B779057
theorem B257303 : Blo 151794 257303 := bstep (se 1 (by rfl) ⟨192977, by rfl⟩ : syracuseStep 257303 = 385955) B385955
theorem B781643 : Blo 151794 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B290135 : Blo 151794 290135 := bstep (se 1 (by rfl) ⟨217601, by rfl⟩ : syracuseStep 290135 = 435203) B435203
theorem B585053 : Blo 151794 585053 := bstep (se 3 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 585053 = 219395) B219395
theorem B257431 : Blo 151794 257431 := bstep (se 1 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 257431 = 386147) B386147
theorem B519641 : Blo 151794 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B388759 : Blo 151794 388759 := bstep (se 1 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 388759 = 583139) B583139
theorem B2420375 : Blo 151794 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B192395 : Blo 151794 192395 := bstep (se 1 (by rfl) ⟨144296, by rfl⟩ : syracuseStep 192395 = 288593) B288593
theorem B520139 : Blo 151794 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B782297 : Blo 151794 782297 := bstep (se 2 (by rfl) ⟨293361, by rfl⟩ : syracuseStep 782297 = 586723) B586723
theorem B290803 : Blo 151794 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B258059 : Blo 151794 258059 := bstep (se 1 (by rfl) ⟨193544, by rfl⟩ : syracuseStep 258059 = 387089) B387089
theorem B585751 : Blo 151794 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B389195 : Blo 151794 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B258187 : Blo 151794 258187 := bstep (se 1 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 258187 = 387281) B387281
theorem B520343 : Blo 151794 520343 := bstep (se 1 (by rfl) ⟨390257, by rfl⟩ : syracuseStep 520343 = 780515) B780515
theorem B1765637 : Blo 151794 1765637 := bstep (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) B331057
theorem B258329 : Blo 151794 258329 := bstep (se 2 (by rfl) ⟨96873, by rfl⟩ : syracuseStep 258329 = 193747) B193747
theorem B258457 : Blo 151794 258457 := bstep (se 2 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 258457 = 193843) B193843
theorem B291251 : Blo 151794 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B389569 : Blo 151794 389569 := bstep (se 2 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 389569 = 292177) B292177
theorem B291289 : Blo 151794 291289 := bstep (se 2 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 291289 = 218467) B218467
theorem B1045037 : Blo 151794 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B520769 : Blo 151794 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B193099 : Blo 151794 193099 := bstep (se 1 (by rfl) ⟨144824, by rfl⟩ : syracuseStep 193099 = 289649) B289649
theorem B520883 : Blo 151794 520883 := bstep (se 1 (by rfl) ⟨390662, by rfl⟩ : syracuseStep 520883 = 781325) B781325
theorem B586541 : Blo 151794 586541 := bstep (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) B219953
theorem B193367 : Blo 151794 193367 := bstep (se 1 (by rfl) ⟨145025, by rfl⟩ : syracuseStep 193367 = 290051) B290051
theorem B652121 : Blo 151794 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B553817 : Blo 151794 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B3240805 : Blo 151794 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B291737 : Blo 151794 291737 := bstep (se 2 (by rfl) ⟨109401, by rfl⟩ : syracuseStep 291737 = 218803) B218803
theorem B652205 : Blo 151794 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B521153 : Blo 151794 521153 := bstep (se 2 (by rfl) ⟨195432, by rfl⟩ : syracuseStep 521153 = 390865) B390865
theorem B259031 : Blo 151794 259031 := bstep (se 1 (by rfl) ⟨194273, by rfl⟩ : syracuseStep 259031 = 388547) B388547
theorem B1668113 : Blo 151794 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B390167 : Blo 151794 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B259159 : Blo 151794 259159 := bstep (se 1 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 259159 = 388739) B388739
theorem B521693 : Blo 151794 521693 := bstep (se 3 (by rfl) ⟨97817, by rfl⟩ : syracuseStep 521693 = 195635) B195635
theorem B194071 : Blo 151794 194071 := bstep (se 1 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 194071 = 291107) B291107
theorem B783917 : Blo 151794 783917 := bstep (se 3 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 783917 = 293969) B293969
theorem B882251 : Blo 151794 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B292481 : Blo 151794 292481 := bstep (se 2 (by rfl) ⟨109680, by rfl⟩ : syracuseStep 292481 = 219361) B219361
theorem B259787 : Blo 151794 259787 := bstep (se 1 (by rfl) ⟨194840, by rfl⟩ : syracuseStep 259787 = 389681) B389681
theorem B390977 : Blo 151794 390977 := bstep (se 2 (by rfl) ⟨146616, by rfl⟩ : syracuseStep 390977 = 293233) B293233
theorem B259915 : Blo 151794 259915 := bstep (se 1 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 259915 = 389873) B389873
theorem B292747 : Blo 151794 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B260057 : Blo 151794 260057 := bstep (se 2 (by rfl) ⟨97521, by rfl⟩ : syracuseStep 260057 = 195043) B195043
theorem B260185 : Blo 151794 260185 := bstep (se 2 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 260185 = 195139) B195139
theorem B587969 : Blo 151794 587969 := bstep (se 2 (by rfl) ⟨220488, by rfl⟩ : syracuseStep 587969 = 440977) B440977
theorem B260377 : Blo 151794 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B293195 : Blo 151794 293195 := bstep (se 1 (by rfl) ⟨219896, by rfl⟩ : syracuseStep 293195 = 439793) B439793
theorem B391513 : Blo 151794 391513 := bstep (se 2 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 391513 = 293635) B293635
theorem B227723 : Blo 151794 227723 := bstep (se 1 (by rfl) ⟨170792, by rfl⟩ : syracuseStep 227723 = 341585) B341585
theorem B227735 : Blo 151794 227735 := bstep (se 1 (by rfl) ⟨170801, by rfl⟩ : syracuseStep 227735 = 341603) B341603
theorem B227801 : Blo 151794 227801 := bstep (se 2 (by rfl) ⟨85425, by rfl⟩ : syracuseStep 227801 = 170851) B170851
theorem B293377 : Blo 151794 293377 := bstep (se 2 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 293377 = 220033) B220033
theorem B522827 : Blo 151794 522827 := bstep (se 1 (by rfl) ⟨392120, by rfl⟩ : syracuseStep 522827 = 784241) B784241
theorem B227915 : Blo 151794 227915 := bstep (se 1 (by rfl) ⟨170936, by rfl⟩ : syracuseStep 227915 = 341873) B341873
theorem B227927 : Blo 151794 227927 := bstep (se 1 (by rfl) ⟨170945, by rfl⟩ : syracuseStep 227927 = 341891) B341891
theorem B326273 : Blo 151794 326273 := bstep (se 2 (by rfl) ⟨122352, by rfl⟩ : syracuseStep 326273 = 244705) B244705
theorem B260759 : Blo 151794 260759 := bstep (se 1 (by rfl) ⟨195569, by rfl⟩ : syracuseStep 260759 = 391139) B391139
theorem B227993 : Blo 151794 227993 := bstep (se 2 (by rfl) ⟨85497, by rfl⟩ : syracuseStep 227993 = 170995) B170995
theorem B326359 : Blo 151794 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B228107 : Blo 151794 228107 := bstep (se 1 (by rfl) ⟨171080, by rfl⟩ : syracuseStep 228107 = 342161) B342161
theorem B228119 : Blo 151794 228119 := bstep (se 1 (by rfl) ⟨171089, by rfl⟩ : syracuseStep 228119 = 342179) B342179
theorem B260887 : Blo 151794 260887 := bstep (se 1 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 260887 = 391331) B391331
theorem B293719 : Blo 151794 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B228185 : Blo 151794 228185 := bstep (se 2 (by rfl) ⟨85569, by rfl⟩ : syracuseStep 228185 = 171139) B171139
theorem B523097 : Blo 151794 523097 := bstep (se 2 (by rfl) ⟨196161, by rfl⟩ : syracuseStep 523097 = 392323) B392323
theorem B490333 : Blo 151794 490333 := bstep (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) B183875
theorem B228299 : Blo 151794 228299 := bstep (se 1 (by rfl) ⟨171224, by rfl⟩ : syracuseStep 228299 = 342449) B342449
theorem B228311 : Blo 151794 228311 := bstep (se 1 (by rfl) ⟨171233, by rfl⟩ : syracuseStep 228311 = 342467) B342467
theorem B228377 : Blo 151794 228377 := bstep (se 2 (by rfl) ⟨85641, by rfl⟩ : syracuseStep 228377 = 171283) B171283
theorem B293939 : Blo 151794 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B228491 : Blo 151794 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B228503 : Blo 151794 228503 := bstep (se 1 (by rfl) ⟨171377, by rfl⟩ : syracuseStep 228503 = 342755) B342755
theorem B195787 : Blo 151794 195787 := bstep (se 1 (by rfl) ⟨146840, by rfl⟩ : syracuseStep 195787 = 293681) B293681
theorem B228569 : Blo 151794 228569 := bstep (se 2 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 228569 = 171427) B171427
theorem B294167 : Blo 151794 294167 := bstep (se 1 (by rfl) ⟨220625, by rfl⟩ : syracuseStep 294167 = 441251) B441251
theorem B228683 : Blo 151794 228683 := bstep (se 1 (by rfl) ⟨171512, by rfl⟩ : syracuseStep 228683 = 343025) B343025
theorem B228695 : Blo 151794 228695 := bstep (se 1 (by rfl) ⟨171521, by rfl⟩ : syracuseStep 228695 = 343043) B343043
theorem B261515 : Blo 151794 261515 := bstep (se 1 (by rfl) ⟨196136, by rfl⟩ : syracuseStep 261515 = 392273) B392273
theorem B228761 : Blo 151794 228761 := bstep (se 2 (by rfl) ⟨85785, by rfl⟩ : syracuseStep 228761 = 171571) B171571
theorem B392627 : Blo 151794 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B228875 : Blo 151794 228875 := bstep (se 1 (by rfl) ⟨171656, by rfl⟩ : syracuseStep 228875 = 343313) B343313
theorem B327179 : Blo 151794 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B261643 : Blo 151794 261643 := bstep (se 1 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 261643 = 392465) B392465
theorem B228887 : Blo 151794 228887 := bstep (se 1 (by rfl) ⟨171665, by rfl⟩ : syracuseStep 228887 = 343331) B343331
theorem B523799 : Blo 151794 523799 := bstep (se 1 (by rfl) ⟨392849, by rfl⟩ : syracuseStep 523799 = 785699) B785699
theorem B294425 : Blo 151794 294425 := bstep (se 2 (by rfl) ⟨110409, by rfl⟩ : syracuseStep 294425 = 220819) B220819
theorem B228953 : Blo 151794 228953 := bstep (se 2 (by rfl) ⟨85857, by rfl⟩ : syracuseStep 228953 = 171715) B171715
theorem B589457 : Blo 151794 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B261785 : Blo 151794 261785 := bstep (se 2 (by rfl) ⟨98169, by rfl⟩ : syracuseStep 261785 = 196339) B196339
theorem B229067 : Blo 151794 229067 := bstep (se 1 (by rfl) ⟨171800, by rfl⟩ : syracuseStep 229067 = 343601) B343601
theorem B229079 : Blo 151794 229079 := bstep (se 1 (by rfl) ⟨171809, by rfl⟩ : syracuseStep 229079 = 343619) B343619
theorem B392921 : Blo 151794 392921 := bstep (se 2 (by rfl) ⟨147345, by rfl⟩ : syracuseStep 392921 = 294691) B294691
theorem B229145 : Blo 151794 229145 := bstep (se 2 (by rfl) ⟨85929, by rfl⟩ : syracuseStep 229145 = 171859) B171859
theorem B261913 : Blo 151794 261913 := bstep (se 2 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 261913 = 196435) B196435
theorem B229259 : Blo 151794 229259 := bstep (se 1 (by rfl) ⟨171944, by rfl⟩ : syracuseStep 229259 = 343889) B343889
theorem B229271 : Blo 151794 229271 := bstep (se 1 (by rfl) ⟨171953, by rfl⟩ : syracuseStep 229271 = 343907) B343907
theorem B1343411 : Blo 151794 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B294835 : Blo 151794 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B229337 : Blo 151794 229337 := bstep (se 2 (by rfl) ⟨86001, by rfl⟩ : syracuseStep 229337 = 172003) B172003
theorem B229391 : Blo 151794 229391 := bstep (se 1 (by rfl) ⟨172043, by rfl⟩ : syracuseStep 229391 = 344087) B344087
theorem B229433 : Blo 151794 229433 := bstep (se 2 (by rfl) ⟨86037, by rfl⟩ : syracuseStep 229433 = 172075) B172075
theorem B393275 : Blo 151794 393275 := bstep (se 1 (by rfl) ⟨294956, by rfl⟩ : syracuseStep 393275 = 589913) B589913
theorem B589943 : Blo 151794 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B229511 : Blo 151794 229511 := bstep (se 1 (by rfl) ⟨172133, by rfl⟩ : syracuseStep 229511 = 344267) B344267
theorem B229547 : Blo 151794 229547 := bstep (se 1 (by rfl) ⟨172160, by rfl⟩ : syracuseStep 229547 = 344321) B344321
theorem B2195657 : Blo 151794 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B229577 : Blo 151794 229577 := bstep (se 2 (by rfl) ⟨86091, by rfl⟩ : syracuseStep 229577 = 172183) B172183
theorem B262345 : Blo 151794 262345 := bstep (se 2 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 262345 = 196759) B196759
theorem B229691 : Blo 151794 229691 := bstep (se 1 (by rfl) ⟨172268, by rfl⟩ : syracuseStep 229691 = 344537) B344537
theorem B229751 : Blo 151794 229751 := bstep (se 1 (by rfl) ⟨172313, by rfl⟩ : syracuseStep 229751 = 344627) B344627
theorem B885127 : Blo 151794 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B229775 : Blo 151794 229775 := bstep (se 1 (by rfl) ⟨172331, by rfl⟩ : syracuseStep 229775 = 344663) B344663
theorem B786833 : Blo 151794 786833 := bstep (se 2 (by rfl) ⟨295062, by rfl⟩ : syracuseStep 786833 = 590125) B590125
theorem B393619 : Blo 151794 393619 := bstep (se 1 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 393619 = 590429) B590429
theorem B229817 : Blo 151794 229817 := bstep (se 2 (by rfl) ⟨86181, by rfl⟩ : syracuseStep 229817 = 172363) B172363
theorem B229895 : Blo 151794 229895 := bstep (se 1 (by rfl) ⟨172421, by rfl⟩ : syracuseStep 229895 = 344843) B344843
theorem B557579 : Blo 151794 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B885259 : Blo 151794 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B393761 : Blo 151794 393761 := bstep (se 2 (by rfl) ⟨147660, by rfl⟩ : syracuseStep 393761 = 295321) B295321
theorem B229931 : Blo 151794 229931 := bstep (se 1 (by rfl) ⟨172448, by rfl⟩ : syracuseStep 229931 = 344897) B344897
theorem B229961 : Blo 151794 229961 := bstep (se 2 (by rfl) ⟨86235, by rfl⟩ : syracuseStep 229961 = 172471) B172471
theorem B230075 : Blo 151794 230075 := bstep (se 1 (by rfl) ⟨172556, by rfl⟩ : syracuseStep 230075 = 345113) B345113
theorem B295625 : Blo 151794 295625 := bstep (se 2 (by rfl) ⟨110859, by rfl⟩ : syracuseStep 295625 = 221719) B221719
theorem B230135 : Blo 151794 230135 := bstep (se 1 (by rfl) ⟨172601, by rfl⟩ : syracuseStep 230135 = 345203) B345203
theorem B230159 : Blo 151794 230159 := bstep (se 1 (by rfl) ⟨172619, by rfl⟩ : syracuseStep 230159 = 345239) B345239
theorem B230201 : Blo 151794 230201 := bstep (se 2 (by rfl) ⟨86325, by rfl⟩ : syracuseStep 230201 = 172651) B172651
theorem B230279 : Blo 151794 230279 := bstep (se 1 (by rfl) ⟨172709, by rfl⟩ : syracuseStep 230279 = 345419) B345419
theorem B525203 : Blo 151794 525203 := bstep (se 1 (by rfl) ⟨393902, by rfl⟩ : syracuseStep 525203 = 787805) B787805
theorem B230315 : Blo 151794 230315 := bstep (se 1 (by rfl) ⟨172736, by rfl⟩ : syracuseStep 230315 = 345473) B345473
theorem B230345 : Blo 151794 230345 := bstep (se 2 (by rfl) ⟨86379, by rfl⟩ : syracuseStep 230345 = 172759) B172759
theorem B230459 : Blo 151794 230459 := bstep (se 1 (by rfl) ⟨172844, by rfl⟩ : syracuseStep 230459 = 345689) B345689
theorem B590915 : Blo 151794 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B230519 : Blo 151794 230519 := bstep (se 1 (by rfl) ⟨172889, by rfl⟩ : syracuseStep 230519 = 345779) B345779
theorem B230543 : Blo 151794 230543 := bstep (se 1 (by rfl) ⟨172907, by rfl⟩ : syracuseStep 230543 = 345815) B345815
theorem B230585 : Blo 151794 230585 := bstep (se 2 (by rfl) ⟨86469, by rfl⟩ : syracuseStep 230585 = 172939) B172939
theorem B230663 : Blo 151794 230663 := bstep (se 1 (by rfl) ⟨172997, by rfl⟩ : syracuseStep 230663 = 345995) B345995
theorem B230699 : Blo 151794 230699 := bstep (se 1 (by rfl) ⟨173024, by rfl⟩ : syracuseStep 230699 = 346049) B346049
theorem B230729 : Blo 151794 230729 := bstep (se 2 (by rfl) ⟨86523, by rfl⟩ : syracuseStep 230729 = 173047) B173047
theorem B230843 : Blo 151794 230843 := bstep (se 1 (by rfl) ⟨173132, by rfl⟩ : syracuseStep 230843 = 346265) B346265
theorem B230903 : Blo 151794 230903 := bstep (se 1 (by rfl) ⟨173177, by rfl⟩ : syracuseStep 230903 = 346355) B346355
theorem B755203 : Blo 151794 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B493067 : Blo 151794 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B591371 : Blo 151794 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B230927 : Blo 151794 230927 := bstep (se 1 (by rfl) ⟨173195, by rfl⟩ : syracuseStep 230927 = 346391) B346391
theorem B1181213 : Blo 151794 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B230969 : Blo 151794 230969 := bstep (se 2 (by rfl) ⟨86613, by rfl⟩ : syracuseStep 230969 = 173227) B173227
theorem B231047 : Blo 151794 231047 := bstep (se 1 (by rfl) ⟨173285, by rfl⟩ : syracuseStep 231047 = 346571) B346571
theorem B231083 : Blo 151794 231083 := bstep (se 1 (by rfl) ⟨173312, by rfl⟩ : syracuseStep 231083 = 346625) B346625
theorem B231113 : Blo 151794 231113 := bstep (se 2 (by rfl) ⟨86667, by rfl⟩ : syracuseStep 231113 = 173335) B173335
theorem B984869 : Blo 151794 984869 := bstep (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) B184663
theorem B231227 : Blo 151794 231227 := bstep (se 1 (by rfl) ⟨173420, by rfl⟩ : syracuseStep 231227 = 346841) B346841
theorem B231287 : Blo 151794 231287 := bstep (se 1 (by rfl) ⟨173465, by rfl⟩ : syracuseStep 231287 = 346931) B346931
theorem B231311 : Blo 151794 231311 := bstep (se 1 (by rfl) ⟨173483, by rfl⟩ : syracuseStep 231311 = 346967) B346967
theorem B2131865 : Blo 151794 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B231353 : Blo 151794 231353 := bstep (se 2 (by rfl) ⟨86757, by rfl⟩ : syracuseStep 231353 = 173515) B173515
theorem B231431 : Blo 151794 231431 := bstep (se 1 (by rfl) ⟨173573, by rfl⟩ : syracuseStep 231431 = 347147) B347147
theorem B231467 : Blo 151794 231467 := bstep (se 1 (by rfl) ⟨173600, by rfl⟩ : syracuseStep 231467 = 347201) B347201
theorem B231497 : Blo 151794 231497 := bstep (se 2 (by rfl) ⟨86811, by rfl⟩ : syracuseStep 231497 = 173623) B173623
theorem B231611 : Blo 151794 231611 := bstep (se 1 (by rfl) ⟨173708, by rfl⟩ : syracuseStep 231611 = 347417) B347417
theorem B1771721 : Blo 151794 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B231671 : Blo 151794 231671 := bstep (se 1 (by rfl) ⟨173753, by rfl⟩ : syracuseStep 231671 = 347507) B347507
theorem B231695 : Blo 151794 231695 := bstep (se 1 (by rfl) ⟨173771, by rfl⟩ : syracuseStep 231695 = 347543) B347543
theorem B231737 : Blo 151794 231737 := bstep (se 2 (by rfl) ⟨86901, by rfl⟩ : syracuseStep 231737 = 173803) B173803
theorem B231815 : Blo 151794 231815 := bstep (se 1 (by rfl) ⟨173861, by rfl⟩ : syracuseStep 231815 = 347723) B347723
theorem B231851 : Blo 151794 231851 := bstep (se 1 (by rfl) ⟨173888, by rfl⟩ : syracuseStep 231851 = 347777) B347777
theorem B330169 : Blo 151794 330169 := bstep (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) B247627
theorem B231881 : Blo 151794 231881 := bstep (se 2 (by rfl) ⟨86955, by rfl⟩ : syracuseStep 231881 = 173911) B173911
theorem B231995 : Blo 151794 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B6687299 : Blo 151794 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B232055 : Blo 151794 232055 := bstep (se 1 (by rfl) ⟨174041, by rfl⟩ : syracuseStep 232055 = 348083) B348083
theorem B297607 : Blo 151794 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B232079 : Blo 151794 232079 := bstep (se 1 (by rfl) ⟨174059, by rfl⟩ : syracuseStep 232079 = 348119) B348119
theorem B232121 : Blo 151794 232121 := bstep (se 2 (by rfl) ⟨87045, by rfl⟩ : syracuseStep 232121 = 174091) B174091
theorem B1182437 : Blo 151794 1182437 := bstep (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) B221707
theorem B232199 : Blo 151794 232199 := bstep (se 1 (by rfl) ⟨174149, by rfl⟩ : syracuseStep 232199 = 348299) B348299
theorem B232235 : Blo 151794 232235 := bstep (se 1 (by rfl) ⟨174176, by rfl⟩ : syracuseStep 232235 = 348353) B348353
theorem B232265 : Blo 151794 232265 := bstep (se 2 (by rfl) ⟨87099, by rfl⟩ : syracuseStep 232265 = 174199) B174199
theorem B985945 : Blo 151794 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B232379 : Blo 151794 232379 := bstep (se 1 (by rfl) ⟨174284, by rfl⟩ : syracuseStep 232379 = 348569) B348569
theorem B232439 : Blo 151794 232439 := bstep (se 1 (by rfl) ⟨174329, by rfl⟩ : syracuseStep 232439 = 348659) B348659
theorem B232463 : Blo 151794 232463 := bstep (se 1 (by rfl) ⟨174347, by rfl⟩ : syracuseStep 232463 = 348695) B348695
theorem B232505 : Blo 151794 232505 := bstep (se 2 (by rfl) ⟨87189, by rfl⟩ : syracuseStep 232505 = 174379) B174379
theorem B658493 : Blo 151794 658493 := bstep (se 3 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 658493 = 246935) B246935
theorem B330887 : Blo 151794 330887 := bstep (se 1 (by rfl) ⟨248165, by rfl⟩ : syracuseStep 330887 = 496331) B496331
theorem B232583 : Blo 151794 232583 := bstep (se 1 (by rfl) ⟨174437, by rfl⟩ : syracuseStep 232583 = 348875) B348875
theorem B232619 : Blo 151794 232619 := bstep (se 1 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 232619 = 348929) B348929
theorem B232649 : Blo 151794 232649 := bstep (se 2 (by rfl) ⟨87243, by rfl⟩ : syracuseStep 232649 = 174487) B174487
theorem B232763 : Blo 151794 232763 := bstep (se 1 (by rfl) ⟨174572, by rfl⟩ : syracuseStep 232763 = 349145) B349145
theorem B232823 : Blo 151794 232823 := bstep (se 1 (by rfl) ⟨174617, by rfl⟩ : syracuseStep 232823 = 349235) B349235
theorem B232847 : Blo 151794 232847 := bstep (se 1 (by rfl) ⟨174635, by rfl⟩ : syracuseStep 232847 = 349271) B349271
theorem B232889 : Blo 151794 232889 := bstep (se 2 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 232889 = 174667) B174667
theorem B232967 : Blo 151794 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B658955 : Blo 151794 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B233003 : Blo 151794 233003 := bstep (se 1 (by rfl) ⟨174752, by rfl⟩ : syracuseStep 233003 = 349505) B349505
theorem B233033 : Blo 151794 233033 := bstep (se 2 (by rfl) ⟨87387, by rfl⟩ : syracuseStep 233033 = 174775) B174775
theorem B331399 : Blo 151794 331399 := bstep (se 1 (by rfl) ⟨248549, by rfl⟩ : syracuseStep 331399 = 497099) B497099
theorem B233147 : Blo 151794 233147 := bstep (se 1 (by rfl) ⟨174860, by rfl⟩ : syracuseStep 233147 = 349721) B349721
theorem B495305 : Blo 151794 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B397001 : Blo 151794 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B233207 : Blo 151794 233207 := bstep (se 1 (by rfl) ⟨174905, by rfl⟩ : syracuseStep 233207 = 349811) B349811
theorem B233231 : Blo 151794 233231 := bstep (se 1 (by rfl) ⟨174923, by rfl⟩ : syracuseStep 233231 = 349847) B349847
theorem B331553 : Blo 151794 331553 := bstep (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) B248665
theorem B233273 : Blo 151794 233273 := bstep (se 2 (by rfl) ⟨87477, by rfl⟩ : syracuseStep 233273 = 174955) B174955
theorem B233351 : Blo 151794 233351 := bstep (se 1 (by rfl) ⟨175013, by rfl⟩ : syracuseStep 233351 = 350027) B350027
theorem B233387 : Blo 151794 233387 := bstep (se 1 (by rfl) ⟨175040, by rfl⟩ : syracuseStep 233387 = 350081) B350081
theorem B233417 : Blo 151794 233417 := bstep (se 2 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 233417 = 175063) B175063
theorem B2199575 : Blo 151794 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B233531 : Blo 151794 233531 := bstep (se 1 (by rfl) ⟨175148, by rfl⟩ : syracuseStep 233531 = 350297) B350297
theorem B233591 : Blo 151794 233591 := bstep (se 1 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 233591 = 350387) B350387
theorem B233615 : Blo 151794 233615 := bstep (se 1 (by rfl) ⟨175211, by rfl⟩ : syracuseStep 233615 = 350423) B350423
theorem B2691245 : Blo 151794 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B233657 : Blo 151794 233657 := bstep (se 2 (by rfl) ⟨87621, by rfl⟩ : syracuseStep 233657 = 175243) B175243
theorem B332075 : Blo 151794 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B1774385 : Blo 151794 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B234299 : Blo 151794 234299 := bstep (se 1 (by rfl) ⟨175724, by rfl⟩ : syracuseStep 234299 = 351449) B351449
theorem B365867 : Blo 151794 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B2987441 : Blo 151794 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B628235 : Blo 151794 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B333497 : Blo 151794 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B661193 : Blo 151794 661193 := bstep (se 2 (by rfl) ⟨247947, by rfl⟩ : syracuseStep 661193 = 495895) B495895
theorem B1775321 : Blo 151794 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B530209 : Blo 151794 530209 := bstep (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) B397657
theorem B432503 : Blo 151794 432503 := bstep (se 1 (by rfl) ⟨324377, by rfl⟩ : syracuseStep 432503 = 648755) B648755
theorem B367001 : Blo 151794 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B2366243 : Blo 151794 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B170887 : Blo 151794 170887 := bstep (se 1 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 170887 = 256331) B256331
theorem B1743767 : Blo 151794 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B433163 : Blo 151794 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B826379 : Blo 151794 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B171067 : Blo 151794 171067 := bstep (se 1 (by rfl) ⟨128300, by rfl⟩ : syracuseStep 171067 = 256601) B256601
theorem B1154249 : Blo 151794 1154249 := bstep (se 2 (by rfl) ⟨432843, by rfl⟩ : syracuseStep 1154249 = 865687) B865687
theorem B1056185 : Blo 151794 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B171535 : Blo 151794 171535 := bstep (se 1 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 171535 = 257303) B257303
theorem B663329 : Blo 151794 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B1122137 : Blo 151794 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B466823 : Blo 151794 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B663481 : Blo 151794 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B172039 : Blo 151794 172039 := bstep (se 1 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 172039 = 258059) B258059
theorem B172219 : Blo 151794 172219 := bstep (se 1 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 172219 = 258329) B258329
theorem B696691 : Blo 151794 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B369049 : Blo 151794 369049 := bstep (se 2 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 369049 = 276787) B276787
theorem B434747 : Blo 151794 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B369211 : Blo 151794 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B434803 : Blo 151794 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B172687 : Blo 151794 172687 := bstep (se 1 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 172687 = 259031) B259031
theorem B664301 : Blo 151794 664301 := bstep (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) B249113
theorem B435145 : Blo 151794 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B173191 : Blo 151794 173191 := bstep (se 1 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 173191 = 259787) B259787
theorem B1320137 : Blo 151794 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B173371 : Blo 151794 173371 := bstep (se 1 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 173371 = 260057) B260057
theorem B664985 : Blo 151794 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B1320401 : Blo 151794 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B1451621 : Blo 151794 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B173839 : Blo 151794 173839 := bstep (se 1 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 173839 = 260759) B260759
theorem B174343 : Blo 151794 174343 := bstep (se 1 (by rfl) ⟨130757, by rfl⟩ : syracuseStep 174343 = 261515) B261515
theorem B174523 : Blo 151794 174523 := bstep (se 1 (by rfl) ⟨130892, by rfl⟩ : syracuseStep 174523 = 261785) B261785
theorem B1387037 : Blo 151794 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B895607 : Blo 151794 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B174991 : Blo 151794 174991 := bstep (se 1 (by rfl) ⟨131243, by rfl⟩ : syracuseStep 174991 = 262487) B262487
theorem B437309 : Blo 151794 437309 := bstep (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) B163991
theorem B1748141 : Blo 151794 1748141 := bstep (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) B655553
theorem B437537 : Blo 151794 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B896345 : Blo 151794 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B437879 : Blo 151794 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B1388677 : Blo 151794 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B1782161 : Blo 151794 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B6238691 : Blo 151794 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B2962291 : Blo 151794 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B439307 : Blo 151794 439307 := bstep (se 1 (by rfl) ⟨329480, by rfl⟩ : syracuseStep 439307 = 658961) B658961
theorem B701729 : Blo 151794 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B210233 : Blo 151794 210233 := bstep (se 2 (by rfl) ⟨78837, by rfl⟩ : syracuseStep 210233 = 157675) B157675
theorem B2635217 : Blo 151794 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B800279 : Blo 151794 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B308855 : Blo 151794 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B341639 : Blo 151794 341639 := bstep (se 1 (by rfl) ⟨256229, by rfl⟩ : syracuseStep 341639 = 512459) B512459
theorem B341819 : Blo 151794 341819 := bstep (se 1 (by rfl) ⟨256364, by rfl⟩ : syracuseStep 341819 = 512729) B512729
theorem B341945 : Blo 151794 341945 := bstep (se 2 (by rfl) ⟨128229, by rfl⟩ : syracuseStep 341945 = 256459) B256459
theorem B899095 : Blo 151794 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B1325117 : Blo 151794 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B440407 : Blo 151794 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B243847 : Blo 151794 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B735425 : Blo 151794 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B342287 : Blo 151794 342287 := bstep (se 1 (by rfl) ⟨256715, by rfl⟩ : syracuseStep 342287 = 513431) B513431
theorem B342305 : Blo 151794 342305 := bstep (se 2 (by rfl) ⟨128364, by rfl⟩ : syracuseStep 342305 = 256729) B256729
theorem B440635 : Blo 151794 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B440761 : Blo 151794 440761 := bstep (se 2 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 440761 = 330571) B330571
theorem B703019 : Blo 151794 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B342647 : Blo 151794 342647 := bstep (se 1 (by rfl) ⟨256985, by rfl⟩ : syracuseStep 342647 = 513971) B513971
theorem B342827 : Blo 151794 342827 := bstep (se 1 (by rfl) ⟨257120, by rfl⟩ : syracuseStep 342827 = 514241) B514241
theorem B1588247 : Blo 151794 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B343187 : Blo 151794 343187 := bstep (se 1 (by rfl) ⟨257390, by rfl⟩ : syracuseStep 343187 = 514781) B514781
theorem B343241 : Blo 151794 343241 := bstep (se 2 (by rfl) ⟨128715, by rfl⟩ : syracuseStep 343241 = 257431) B257431
theorem B834875 : Blo 151794 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B245263 : Blo 151794 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B343943 : Blo 151794 343943 := bstep (se 1 (by rfl) ⟨257957, by rfl⟩ : syracuseStep 343943 = 515915) B515915
theorem B278407 : Blo 151794 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B344123 : Blo 151794 344123 := bstep (se 1 (by rfl) ⟨258092, by rfl⟩ : syracuseStep 344123 = 516185) B516185
theorem B344249 : Blo 151794 344249 := bstep (se 2 (by rfl) ⟨129093, by rfl⟩ : syracuseStep 344249 = 258187) B258187
theorem B442685 : Blo 151794 442685 := bstep (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) B166007
theorem B442711 : Blo 151794 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B344591 : Blo 151794 344591 := bstep (se 1 (by rfl) ⟨258443, by rfl⟩ : syracuseStep 344591 = 516887) B516887
theorem B344609 : Blo 151794 344609 := bstep (se 2 (by rfl) ⟨129228, by rfl⟩ : syracuseStep 344609 = 258457) B258457
theorem B1163969 : Blo 151794 1163969 := bstep (se 2 (by rfl) ⟨436488, by rfl⟩ : syracuseStep 1163969 = 872977) B872977
theorem B344951 : Blo 151794 344951 := bstep (se 1 (by rfl) ⟨258713, by rfl⟩ : syracuseStep 344951 = 517427) B517427
theorem B345131 : Blo 151794 345131 := bstep (se 1 (by rfl) ⟨258848, by rfl⟩ : syracuseStep 345131 = 517697) B517697
theorem B771443 : Blo 151794 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B345491 : Blo 151794 345491 := bstep (se 1 (by rfl) ⟨259118, by rfl⟩ : syracuseStep 345491 = 518237) B518237
theorem B345545 : Blo 151794 345545 := bstep (se 2 (by rfl) ⟨129579, by rfl⟩ : syracuseStep 345545 = 259159) B259159
theorem B870061 : Blo 151794 870061 := bstep (se 3 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 870061 = 326273) B326273
theorem B771929 : Blo 151794 771929 := bstep (se 2 (by rfl) ⟨289473, by rfl⟩ : syracuseStep 771929 = 578947) B578947
theorem B444295 : Blo 151794 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B1656949 : Blo 151794 1656949 := bstep (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) B155339
theorem B313463 : Blo 151794 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B346247 : Blo 151794 346247 := bstep (se 1 (by rfl) ⟨259685, by rfl⟩ : syracuseStep 346247 = 519371) B519371
theorem B936173 : Blo 151794 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B346427 : Blo 151794 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B346553 : Blo 151794 346553 := bstep (se 2 (by rfl) ⟨129957, by rfl⟩ : syracuseStep 346553 = 259915) B259915
theorem B3721909 : Blo 151794 3721909 := bstep (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) B348929
theorem B346895 : Blo 151794 346895 := bstep (se 1 (by rfl) ⟨260171, by rfl⟩ : syracuseStep 346895 = 520343) B520343
theorem B346913 : Blo 151794 346913 := bstep (se 2 (by rfl) ⟨130092, by rfl⟩ : syracuseStep 346913 = 260185) B260185
theorem B347179 : Blo 151794 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B347255 : Blo 151794 347255 := bstep (se 1 (by rfl) ⟨260441, by rfl⟩ : syracuseStep 347255 = 520883) B520883
theorem B347435 : Blo 151794 347435 := bstep (se 1 (by rfl) ⟨260576, by rfl⟩ : syracuseStep 347435 = 521153) B521153
theorem B1887623 : Blo 151794 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B413113 : Blo 151794 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B1953233 : Blo 151794 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B347795 : Blo 151794 347795 := bstep (se 1 (by rfl) ⟨260846, by rfl⟩ : syracuseStep 347795 = 521693) B521693
theorem B347849 : Blo 151794 347849 := bstep (se 2 (by rfl) ⟨130443, by rfl⟩ : syracuseStep 347849 = 260887) B260887
theorem B1756889 : Blo 151794 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B774035 : Blo 151794 774035 := bstep (se 1 (by rfl) ⟨580526, by rfl⟩ : syracuseStep 774035 = 1161053) B1161053
theorem B577489 : Blo 151794 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B1167371 : Blo 151794 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B872477 : Blo 151794 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B184567 : Blo 151794 184567 := bstep (se 1 (by rfl) ⟨138425, by rfl⟩ : syracuseStep 184567 = 276851) B276851
theorem B577793 : Blo 151794 577793 := bstep (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) B433345
theorem B151815 : Blo 151794 151815 := bstep (se 1 (by rfl) ⟨113861, by rfl⟩ : syracuseStep 151815 = 227723) B227723
theorem B151823 : Blo 151794 151823 := bstep (se 1 (by rfl) ⟨113867, by rfl⟩ : syracuseStep 151823 = 227735) B227735
theorem B151867 : Blo 151794 151867 := bstep (se 1 (by rfl) ⟨113900, by rfl⟩ : syracuseStep 151867 = 227801) B227801
theorem B151943 : Blo 151794 151943 := bstep (se 1 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 151943 = 227915) B227915
theorem B348551 : Blo 151794 348551 := bstep (se 1 (by rfl) ⟨261413, by rfl⟩ : syracuseStep 348551 = 522827) B522827
theorem B151951 : Blo 151794 151951 := bstep (se 1 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 151951 = 227927) B227927
theorem B151995 : Blo 151794 151995 := bstep (se 1 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 151995 = 227993) B227993
theorem B152071 : Blo 151794 152071 := bstep (se 1 (by rfl) ⟨114053, by rfl⟩ : syracuseStep 152071 = 228107) B228107
theorem B152079 : Blo 151794 152079 := bstep (se 1 (by rfl) ⟨114059, by rfl⟩ : syracuseStep 152079 = 228119) B228119
theorem B152123 : Blo 151794 152123 := bstep (se 1 (by rfl) ⟨114092, by rfl⟩ : syracuseStep 152123 = 228185) B228185
theorem B348731 : Blo 151794 348731 := bstep (se 1 (by rfl) ⟨261548, by rfl⟩ : syracuseStep 348731 = 523097) B523097
theorem B938557 : Blo 151794 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B905795 : Blo 151794 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B152199 : Blo 151794 152199 := bstep (se 1 (by rfl) ⟨114149, by rfl⟩ : syracuseStep 152199 = 228299) B228299
theorem B152207 : Blo 151794 152207 := bstep (se 1 (by rfl) ⟨114155, by rfl⟩ : syracuseStep 152207 = 228311) B228311
theorem B348857 : Blo 151794 348857 := bstep (se 2 (by rfl) ⟨130821, by rfl⟩ : syracuseStep 348857 = 261643) B261643
theorem B152251 : Blo 151794 152251 := bstep (se 1 (by rfl) ⟨114188, by rfl⟩ : syracuseStep 152251 = 228377) B228377
theorem B578249 : Blo 151794 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B152327 : Blo 151794 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B512783 : Blo 151794 512783 := bstep (se 1 (by rfl) ⟨384587, by rfl⟩ : syracuseStep 512783 = 769175) B769175
theorem B152335 : Blo 151794 152335 := bstep (se 1 (by rfl) ⟨114251, by rfl⟩ : syracuseStep 152335 = 228503) B228503
theorem B152379 : Blo 151794 152379 := bstep (se 1 (by rfl) ⟨114284, by rfl⟩ : syracuseStep 152379 = 228569) B228569
theorem B152455 : Blo 151794 152455 := bstep (se 1 (by rfl) ⟨114341, by rfl⟩ : syracuseStep 152455 = 228683) B228683
theorem B152463 : Blo 151794 152463 := bstep (se 1 (by rfl) ⟨114347, by rfl⟩ : syracuseStep 152463 = 228695) B228695
theorem B152507 : Blo 151794 152507 := bstep (se 1 (by rfl) ⟨114380, by rfl⟩ : syracuseStep 152507 = 228761) B228761
theorem B152583 : Blo 151794 152583 := bstep (se 1 (by rfl) ⟨114437, by rfl⟩ : syracuseStep 152583 = 228875) B228875
theorem B152591 : Blo 151794 152591 := bstep (se 1 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 152591 = 228887) B228887
theorem B349199 : Blo 151794 349199 := bstep (se 1 (by rfl) ⟨261899, by rfl⟩ : syracuseStep 349199 = 523799) B523799
theorem B513053 : Blo 151794 513053 := bstep (se 3 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 513053 = 192395) B192395
theorem B349217 : Blo 151794 349217 := bstep (se 2 (by rfl) ⟨130956, by rfl⟩ : syracuseStep 349217 = 261913) B261913
theorem B152635 : Blo 151794 152635 := bstep (se 1 (by rfl) ⟨114476, by rfl⟩ : syracuseStep 152635 = 228953) B228953
theorem B152711 : Blo 151794 152711 := bstep (se 1 (by rfl) ⟨114533, by rfl⟩ : syracuseStep 152711 = 229067) B229067
theorem B152719 : Blo 151794 152719 := bstep (se 1 (by rfl) ⟨114539, by rfl⟩ : syracuseStep 152719 = 229079) B229079
theorem B152763 : Blo 151794 152763 := bstep (se 1 (by rfl) ⟨114572, by rfl⟩ : syracuseStep 152763 = 229145) B229145
theorem B152839 : Blo 151794 152839 := bstep (se 1 (by rfl) ⟨114629, by rfl⟩ : syracuseStep 152839 = 229259) B229259
theorem B152847 : Blo 151794 152847 := bstep (se 1 (by rfl) ⟨114635, by rfl⟩ : syracuseStep 152847 = 229271) B229271
theorem B152891 : Blo 151794 152891 := bstep (se 1 (by rfl) ⟨114668, by rfl⟩ : syracuseStep 152891 = 229337) B229337
theorem B349559 : Blo 151794 349559 := bstep (se 1 (by rfl) ⟨262169, by rfl⟩ : syracuseStep 349559 = 524339) B524339
theorem B152967 : Blo 151794 152967 := bstep (se 1 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 152967 = 229451) B229451
theorem B152975 : Blo 151794 152975 := bstep (se 1 (by rfl) ⟨114731, by rfl⟩ : syracuseStep 152975 = 229463) B229463
theorem B153019 : Blo 151794 153019 := bstep (se 1 (by rfl) ⟨114764, by rfl⟩ : syracuseStep 153019 = 229529) B229529
theorem B153095 : Blo 151794 153095 := bstep (se 1 (by rfl) ⟨114821, by rfl⟩ : syracuseStep 153095 = 229643) B229643
theorem B153103 : Blo 151794 153103 := bstep (se 1 (by rfl) ⟨114827, by rfl⟩ : syracuseStep 153103 = 229655) B229655
theorem B349739 : Blo 151794 349739 := bstep (se 1 (by rfl) ⟨262304, by rfl⟩ : syracuseStep 349739 = 524609) B524609
theorem B153147 : Blo 151794 153147 := bstep (se 1 (by rfl) ⟨114860, by rfl⟩ : syracuseStep 153147 = 229721) B229721
theorem B153223 : Blo 151794 153223 := bstep (se 1 (by rfl) ⟨114917, by rfl⟩ : syracuseStep 153223 = 229835) B229835
theorem B153231 : Blo 151794 153231 := bstep (se 1 (by rfl) ⟨114923, by rfl⟩ : syracuseStep 153231 = 229847) B229847
theorem B153275 : Blo 151794 153275 := bstep (se 1 (by rfl) ⟨114956, by rfl⟩ : syracuseStep 153275 = 229913) B229913
theorem B153351 : Blo 151794 153351 := bstep (se 1 (by rfl) ⟨115013, by rfl⟩ : syracuseStep 153351 = 230027) B230027
theorem B448267 : Blo 151794 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B153359 : Blo 151794 153359 := bstep (se 1 (by rfl) ⟨115019, by rfl⟩ : syracuseStep 153359 = 230039) B230039
theorem B153403 : Blo 151794 153403 := bstep (se 1 (by rfl) ⟨115052, by rfl⟩ : syracuseStep 153403 = 230105) B230105
theorem B153479 : Blo 151794 153479 := bstep (se 1 (by rfl) ⟨115109, by rfl⟩ : syracuseStep 153479 = 230219) B230219
theorem B153487 : Blo 151794 153487 := bstep (se 1 (by rfl) ⟨115115, by rfl⟩ : syracuseStep 153487 = 230231) B230231
theorem B350099 : Blo 151794 350099 := bstep (se 1 (by rfl) ⟨262574, by rfl⟩ : syracuseStep 350099 = 525149) B525149
theorem B1169315 : Blo 151794 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B153531 : Blo 151794 153531 := bstep (se 1 (by rfl) ⟨115148, by rfl⟩ : syracuseStep 153531 = 230297) B230297
theorem B350153 : Blo 151794 350153 := bstep (se 2 (by rfl) ⟨131307, by rfl⟩ : syracuseStep 350153 = 262615) B262615
theorem B153607 : Blo 151794 153607 := bstep (se 1 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 153607 = 230411) B230411
theorem B153615 : Blo 151794 153615 := bstep (se 1 (by rfl) ⟨115211, by rfl⟩ : syracuseStep 153615 = 230423) B230423
theorem B153659 : Blo 151794 153659 := bstep (se 1 (by rfl) ⟨115244, by rfl⟩ : syracuseStep 153659 = 230489) B230489
theorem B1136773 : Blo 151794 1136773 := bstep (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) B213145
theorem B153735 : Blo 151794 153735 := bstep (se 1 (by rfl) ⟨115301, by rfl⟩ : syracuseStep 153735 = 230603) B230603
theorem B153743 : Blo 151794 153743 := bstep (se 1 (by rfl) ⟨115307, by rfl⟩ : syracuseStep 153743 = 230615) B230615
theorem B153787 : Blo 151794 153787 := bstep (se 1 (by rfl) ⟨115340, by rfl⟩ : syracuseStep 153787 = 230681) B230681
theorem B2840777 : Blo 151794 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B153863 : Blo 151794 153863 := bstep (se 1 (by rfl) ⟨115397, by rfl⟩ : syracuseStep 153863 = 230795) B230795
theorem B153871 : Blo 151794 153871 := bstep (se 1 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 153871 = 230807) B230807
theorem B153915 : Blo 151794 153915 := bstep (se 1 (by rfl) ⟨115436, by rfl⟩ : syracuseStep 153915 = 230873) B230873
theorem B153991 : Blo 151794 153991 := bstep (se 1 (by rfl) ⟨115493, by rfl⟩ : syracuseStep 153991 = 230987) B230987
theorem B153999 : Blo 151794 153999 := bstep (se 1 (by rfl) ⟨115499, by rfl⟩ : syracuseStep 153999 = 230999) B230999
theorem B514457 : Blo 151794 514457 := bstep (se 2 (by rfl) ⟨192921, by rfl⟩ : syracuseStep 514457 = 385843) B385843
theorem B154043 : Blo 151794 154043 := bstep (se 1 (by rfl) ⟨115532, by rfl⟩ : syracuseStep 154043 = 231065) B231065
theorem B874961 : Blo 151794 874961 := bstep (se 2 (by rfl) ⟨328110, by rfl⟩ : syracuseStep 874961 = 656221) B656221
theorem B154119 : Blo 151794 154119 := bstep (se 1 (by rfl) ⟨115589, by rfl⟩ : syracuseStep 154119 = 231179) B231179
theorem B154127 : Blo 151794 154127 := bstep (se 1 (by rfl) ⟨115595, by rfl⟩ : syracuseStep 154127 = 231191) B231191
theorem B154171 : Blo 151794 154171 := bstep (se 1 (by rfl) ⟨115628, by rfl⟩ : syracuseStep 154171 = 231257) B231257
theorem B154247 : Blo 151794 154247 := bstep (se 1 (by rfl) ⟨115685, by rfl⟩ : syracuseStep 154247 = 231371) B231371
theorem B154255 : Blo 151794 154255 := bstep (se 1 (by rfl) ⟨115691, by rfl⟩ : syracuseStep 154255 = 231383) B231383
theorem B154299 : Blo 151794 154299 := bstep (se 1 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 154299 = 231449) B231449
theorem B154375 : Blo 151794 154375 := bstep (se 1 (by rfl) ⟨115781, by rfl⟩ : syracuseStep 154375 = 231563) B231563
theorem B154383 : Blo 151794 154383 := bstep (se 1 (by rfl) ⟨115787, by rfl⟩ : syracuseStep 154383 = 231575) B231575
theorem B154427 : Blo 151794 154427 := bstep (se 1 (by rfl) ⟨115820, by rfl⟩ : syracuseStep 154427 = 231641) B231641
theorem B154503 : Blo 151794 154503 := bstep (se 1 (by rfl) ⟨115877, by rfl⟩ : syracuseStep 154503 = 231755) B231755
theorem B154511 : Blo 151794 154511 := bstep (se 1 (by rfl) ⟨115883, by rfl⟩ : syracuseStep 154511 = 231767) B231767
theorem B777113 : Blo 151794 777113 := bstep (se 2 (by rfl) ⟨291417, by rfl⟩ : syracuseStep 777113 = 582835) B582835
theorem B154555 : Blo 151794 154555 := bstep (se 1 (by rfl) ⟨115916, by rfl⟩ : syracuseStep 154555 = 231833) B231833
theorem B154631 : Blo 151794 154631 := bstep (se 1 (by rfl) ⟨115973, by rfl⟩ : syracuseStep 154631 = 231947) B231947
theorem B154639 : Blo 151794 154639 := bstep (se 1 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 154639 = 231959) B231959
theorem B154683 : Blo 151794 154683 := bstep (se 1 (by rfl) ⟨116012, by rfl⟩ : syracuseStep 154683 = 232025) B232025
theorem B515159 : Blo 151794 515159 := bstep (se 1 (by rfl) ⟨386369, by rfl⟩ : syracuseStep 515159 = 772739) B772739
theorem B154759 : Blo 151794 154759 := bstep (se 1 (by rfl) ⟨116069, by rfl⟩ : syracuseStep 154759 = 232139) B232139
theorem B154767 : Blo 151794 154767 := bstep (se 1 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 154767 = 232151) B232151
theorem B154811 : Blo 151794 154811 := bstep (se 1 (by rfl) ⟨116108, by rfl⟩ : syracuseStep 154811 = 232217) B232217
theorem B318665 : Blo 151794 318665 := bstep (se 2 (by rfl) ⟨119499, by rfl⟩ : syracuseStep 318665 = 238999) B238999
theorem B154887 : Blo 151794 154887 := bstep (se 1 (by rfl) ⟨116165, by rfl⟩ : syracuseStep 154887 = 232331) B232331
theorem B154895 : Blo 151794 154895 := bstep (se 1 (by rfl) ⟨116171, by rfl⟩ : syracuseStep 154895 = 232343) B232343
theorem B154939 : Blo 151794 154939 := bstep (se 1 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 154939 = 232409) B232409
theorem B155015 : Blo 151794 155015 := bstep (se 1 (by rfl) ⟨116261, by rfl⟩ : syracuseStep 155015 = 232523) B232523
theorem B155023 : Blo 151794 155023 := bstep (se 1 (by rfl) ⟨116267, by rfl⟩ : syracuseStep 155023 = 232535) B232535
theorem B155067 : Blo 151794 155067 := bstep (se 1 (by rfl) ⟨116300, by rfl⟩ : syracuseStep 155067 = 232601) B232601
theorem B155143 : Blo 151794 155143 := bstep (se 1 (by rfl) ⟨116357, by rfl⟩ : syracuseStep 155143 = 232715) B232715
theorem B384527 : Blo 151794 384527 := bstep (se 1 (by rfl) ⟨288395, by rfl⟩ : syracuseStep 384527 = 576791) B576791
theorem B155151 : Blo 151794 155151 := bstep (se 1 (by rfl) ⟨116363, by rfl⟩ : syracuseStep 155151 = 232727) B232727
theorem B155195 : Blo 151794 155195 := bstep (se 1 (by rfl) ⟨116396, by rfl⟩ : syracuseStep 155195 = 232793) B232793
theorem B515645 : Blo 151794 515645 := bstep (se 3 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 515645 = 193367) B193367
theorem B220745 : Blo 151794 220745 := bstep (se 2 (by rfl) ⟨82779, by rfl⟩ : syracuseStep 220745 = 165559) B165559
theorem B155271 : Blo 151794 155271 := bstep (se 1 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 155271 = 232907) B232907
theorem B155279 : Blo 151794 155279 := bstep (se 1 (by rfl) ⟨116459, by rfl⟩ : syracuseStep 155279 = 232919) B232919
theorem B384659 : Blo 151794 384659 := bstep (se 1 (by rfl) ⟨288494, by rfl⟩ : syracuseStep 384659 = 576989) B576989
theorem B155323 : Blo 151794 155323 := bstep (se 1 (by rfl) ⟨116492, by rfl⟩ : syracuseStep 155323 = 232985) B232985
theorem B1335041 : Blo 151794 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B581377 : Blo 151794 581377 := bstep (se 2 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 581377 = 436033) B436033
theorem B155399 : Blo 151794 155399 := bstep (se 1 (by rfl) ⟨116549, by rfl⟩ : syracuseStep 155399 = 233099) B233099
theorem B155407 : Blo 151794 155407 := bstep (se 1 (by rfl) ⟨116555, by rfl⟩ : syracuseStep 155407 = 233111) B233111
theorem B155451 : Blo 151794 155451 := bstep (se 1 (by rfl) ⟨116588, by rfl⟩ : syracuseStep 155451 = 233177) B233177
theorem B941959 : Blo 151794 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B155527 : Blo 151794 155527 := bstep (se 1 (by rfl) ⟨116645, by rfl⟩ : syracuseStep 155527 = 233291) B233291
theorem B155535 : Blo 151794 155535 := bstep (se 1 (by rfl) ⟨116651, by rfl⟩ : syracuseStep 155535 = 233303) B233303
theorem B155579 : Blo 151794 155579 := bstep (se 1 (by rfl) ⟨116684, by rfl⟩ : syracuseStep 155579 = 233369) B233369
theorem B155655 : Blo 151794 155655 := bstep (se 1 (by rfl) ⟨116741, by rfl⟩ : syracuseStep 155655 = 233483) B233483
theorem B155663 : Blo 151794 155663 := bstep (se 1 (by rfl) ⟨116747, by rfl⟩ : syracuseStep 155663 = 233495) B233495
theorem B155707 : Blo 151794 155707 := bstep (se 1 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 155707 = 233561) B233561
theorem B155783 : Blo 151794 155783 := bstep (se 1 (by rfl) ⟨116837, by rfl⟩ : syracuseStep 155783 = 233675) B233675
theorem B155791 : Blo 151794 155791 := bstep (se 1 (by rfl) ⟨116843, by rfl⟩ : syracuseStep 155791 = 233687) B233687
theorem B1466657 : Blo 151794 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B1171745 : Blo 151794 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B876851 : Blo 151794 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B221611 : Blo 151794 221611 := bstep (se 1 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 221611 = 332417) B332417
theorem B385793 : Blo 151794 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B517049 : Blo 151794 517049 := bstep (se 2 (by rfl) ⟨193893, by rfl⟩ : syracuseStep 517049 = 387787) B387787
theorem B386167 : Blo 151794 386167 := bstep (se 1 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 386167 = 579251) B579251
theorem B1172717 : Blo 151794 1172717 := bstep (se 3 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 1172717 = 439769) B439769
theorem B779705 : Blo 151794 779705 := bstep (se 2 (by rfl) ⟨292389, by rfl⟩ : syracuseStep 779705 = 584779) B584779
theorem B517643 : Blo 151794 517643 := bstep (se 1 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 517643 = 776465) B776465
theorem B288289 : Blo 151794 288289 := bstep (se 2 (by rfl) ⟨108108, by rfl⟩ : syracuseStep 288289 = 216217) B216217
theorem B1762859 : Blo 151794 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B386603 : Blo 151794 386603 := bstep (se 1 (by rfl) ⟨289952, by rfl⟩ : syracuseStep 386603 = 579905) B579905
theorem B222793 : Blo 151794 222793 := bstep (se 2 (by rfl) ⟨83547, by rfl⟩ : syracuseStep 222793 = 167095) B167095
theorem B517751 : Blo 151794 517751 := bstep (se 1 (by rfl) ⟨388313, by rfl⟩ : syracuseStep 517751 = 776627) B776627
theorem B812717 : Blo 151794 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B878309 : Blo 151794 878309 := bstep (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) B164683
theorem B780167 : Blo 151794 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B1992599 : Blo 151794 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B2189429 : Blo 151794 2189429 := bstep (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) B205259
theorem B420025 : Blo 151794 420025 := bstep (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) B315019
theorem B518345 : Blo 151794 518345 := bstep (se 2 (by rfl) ⟨194379, by rfl⟩ : syracuseStep 518345 = 388759) B388759
theorem B387443 : Blo 151794 387443 := bstep (se 1 (by rfl) ⟨290582, by rfl⟩ : syracuseStep 387443 = 581165) B581165
theorem B387463 : Blo 151794 387463 := bstep (se 1 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 387463 = 581195) B581195
theorem B748061 : Blo 151794 748061 := bstep (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) B280523
theorem B584279 : Blo 151794 584279 := bstep (se 1 (by rfl) ⟨438209, by rfl⟩ : syracuseStep 584279 = 876419) B876419
theorem B387737 : Blo 151794 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B1108673 : Blo 151794 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B781001 : Blo 151794 781001 := bstep (se 2 (by rfl) ⟨292875, by rfl⟩ : syracuseStep 781001 = 585751) B585751
theorem B256783 : Blo 151794 256783 := bstep (se 1 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 256783 = 385175) B385175
theorem B59894549 : Blo 151794 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B289595 : Blo 151794 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B387899 : Blo 151794 387899 := bstep (se 1 (by rfl) ⟨290924, by rfl⟩ : syracuseStep 387899 = 581849) B581849
theorem B519047 : Blo 151794 519047 := bstep (se 1 (by rfl) ⟨389285, by rfl⟩ : syracuseStep 519047 = 778571) B778571
theorem B5565347 : Blo 151794 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B388111 : Blo 151794 388111 := bstep (se 1 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 388111 = 582167) B582167
theorem B1109015 : Blo 151794 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B191531 : Blo 151794 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B584765 : Blo 151794 584765 := bstep (se 3 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 584765 = 219287) B219287
theorem B650359 : Blo 151794 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B1174661 : Blo 151794 1174661 := bstep (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) B220249
theorem B519425 : Blo 151794 519425 := bstep (se 2 (by rfl) ⟨194784, by rfl⟩ : syracuseStep 519425 = 389569) B389569
theorem B290081 : Blo 151794 290081 := bstep (se 2 (by rfl) ⟨108780, by rfl⟩ : syracuseStep 290081 = 217561) B217561
theorem B388385 : Blo 151794 388385 := bstep (se 2 (by rfl) ⟨145644, by rfl⟩ : syracuseStep 388385 = 291289) B291289
theorem B257323 : Blo 151794 257323 := bstep (se 1 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 257323 = 385985) B385985
theorem B1240379 : Blo 151794 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B257465 : Blo 151794 257465 := bstep (se 2 (by rfl) ⟨96549, by rfl⟩ : syracuseStep 257465 = 193099) B193099
theorem B290233 : Blo 151794 290233 := bstep (se 2 (by rfl) ⟨108837, by rfl⟩ : syracuseStep 290233 = 217675) B217675
theorem B552491 : Blo 151794 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B1568375 : Blo 151794 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B13463171 : Blo 151794 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B4321073 : Blo 151794 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B520235 : Blo 151794 520235 := bstep (se 1 (by rfl) ⟨390176, by rfl⟩ : syracuseStep 520235 = 780353) B780353
theorem B5304365 : Blo 151794 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B2945069 : Blo 151794 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B258167 : Blo 151794 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B192775 : Blo 151794 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B389387 : Blo 151794 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B1503623 : Blo 151794 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B258619 : Blo 151794 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B651863 : Blo 151794 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B193195 : Blo 151794 193195 := bstep (se 1 (by rfl) ⟨144896, by rfl⟩ : syracuseStep 193195 = 289793) B289793
theorem B258761 : Blo 151794 258761 := bstep (se 2 (by rfl) ⟨97035, by rfl⟩ : syracuseStep 258761 = 194071) B194071
theorem B488207 : Blo 151794 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B586511 : Blo 151794 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B521095 : Blo 151794 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B881543 : Blo 151794 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B193423 : Blo 151794 193423 := bstep (se 1 (by rfl) ⟨145067, by rfl⟩ : syracuseStep 193423 = 290135) B290135
theorem B390035 : Blo 151794 390035 := bstep (se 1 (by rfl) ⟨292526, by rfl⟩ : syracuseStep 390035 = 585053) B585053
theorem B881725 : Blo 151794 881725 := bstep (se 3 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 881725 = 330647) B330647
theorem B292025 : Blo 151794 292025 := bstep (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) B219019
theorem B390329 : Blo 151794 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B521531 : Blo 151794 521531 := bstep (se 1 (by rfl) ⟨391148, by rfl⟩ : syracuseStep 521531 = 782297) B782297
theorem B259463 : Blo 151794 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B1177091 : Blo 151794 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B194167 : Blo 151794 194167 := bstep (se 1 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 194167 = 291251) B291251
theorem B522017 : Blo 151794 522017 := bstep (se 2 (by rfl) ⟨195756, by rfl⟩ : syracuseStep 522017 = 391513) B391513
theorem B391027 : Blo 151794 391027 := bstep (se 1 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 391027 = 586541) B586541
theorem B194491 : Blo 151794 194491 := bstep (se 1 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 194491 = 291737) B291737
theorem B391169 : Blo 151794 391169 := bstep (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) B293377
theorem B1112075 : Blo 151794 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B260111 : Blo 151794 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B1669409 : Blo 151794 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B522611 : Blo 151794 522611 := bstep (se 1 (by rfl) ⟨391958, by rfl⟩ : syracuseStep 522611 = 783917) B783917
theorem B588167 : Blo 151794 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B194987 : Blo 151794 194987 := bstep (se 1 (by rfl) ⟨146240, by rfl⟩ : syracuseStep 194987 = 292481) B292481
theorem B227771 : Blo 151794 227771 := bstep (se 1 (by rfl) ⟨170828, by rfl⟩ : syracuseStep 227771 = 341657) B341657
theorem B391625 : Blo 151794 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B653777 : Blo 151794 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B227831 : Blo 151794 227831 := bstep (se 1 (by rfl) ⟨170873, by rfl⟩ : syracuseStep 227831 = 341747) B341747
theorem B227855 : Blo 151794 227855 := bstep (se 1 (by rfl) ⟨170891, by rfl⟩ : syracuseStep 227855 = 341783) B341783
theorem B260651 : Blo 151794 260651 := bstep (se 1 (by rfl) ⟨195488, by rfl⟩ : syracuseStep 260651 = 390977) B390977
theorem B227897 : Blo 151794 227897 := bstep (se 2 (by rfl) ⟨85461, by rfl⟩ : syracuseStep 227897 = 170923) B170923
theorem B227975 : Blo 151794 227975 := bstep (se 1 (by rfl) ⟨170981, by rfl⟩ : syracuseStep 227975 = 341963) B341963
theorem B228011 : Blo 151794 228011 := bstep (se 1 (by rfl) ⟨171008, by rfl⟩ : syracuseStep 228011 = 342017) B342017
theorem B228041 : Blo 151794 228041 := bstep (se 2 (by rfl) ⟨85515, by rfl⟩ : syracuseStep 228041 = 171031) B171031
theorem B883457 : Blo 151794 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B391979 : Blo 151794 391979 := bstep (se 1 (by rfl) ⟨293984, by rfl⟩ : syracuseStep 391979 = 587969) B587969
theorem B228155 : Blo 151794 228155 := bstep (se 1 (by rfl) ⟨171116, by rfl⟩ : syracuseStep 228155 = 342233) B342233
theorem B555835 : Blo 151794 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B228215 : Blo 151794 228215 := bstep (se 1 (by rfl) ⟨171161, by rfl⟩ : syracuseStep 228215 = 342323) B342323
theorem B195463 : Blo 151794 195463 := bstep (se 1 (by rfl) ⟨146597, by rfl⟩ : syracuseStep 195463 = 293195) B293195
theorem B228239 : Blo 151794 228239 := bstep (se 1 (by rfl) ⟨171179, by rfl⟩ : syracuseStep 228239 = 342359) B342359
theorem B228281 : Blo 151794 228281 := bstep (se 2 (by rfl) ⟨85605, by rfl⟩ : syracuseStep 228281 = 171211) B171211
theorem B261049 : Blo 151794 261049 := bstep (se 2 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 261049 = 195787) B195787
theorem B228359 : Blo 151794 228359 := bstep (se 1 (by rfl) ⟨171269, by rfl⟩ : syracuseStep 228359 = 342539) B342539
theorem B228395 : Blo 151794 228395 := bstep (se 1 (by rfl) ⟨171296, by rfl⟩ : syracuseStep 228395 = 342593) B342593
theorem B6454333 : Blo 151794 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B228425 : Blo 151794 228425 := bstep (se 2 (by rfl) ⟨85659, by rfl⟩ : syracuseStep 228425 = 171319) B171319
theorem B294023 : Blo 151794 294023 := bstep (se 1 (by rfl) ⟨220517, by rfl⟩ : syracuseStep 294023 = 441035) B441035
theorem B457913 : Blo 151794 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B228539 : Blo 151794 228539 := bstep (se 1 (by rfl) ⟨171404, by rfl⟩ : syracuseStep 228539 = 342809) B342809
theorem B228599 : Blo 151794 228599 := bstep (se 1 (by rfl) ⟨171449, by rfl⟩ : syracuseStep 228599 = 342899) B342899
theorem B228623 : Blo 151794 228623 := bstep (se 1 (by rfl) ⟨171467, by rfl⟩ : syracuseStep 228623 = 342935) B342935
theorem B228665 : Blo 151794 228665 := bstep (se 2 (by rfl) ⟨85749, by rfl⟩ : syracuseStep 228665 = 171499) B171499
theorem B195959 : Blo 151794 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B228743 : Blo 151794 228743 := bstep (se 1 (by rfl) ⟨171557, by rfl⟩ : syracuseStep 228743 = 343115) B343115
theorem B228779 : Blo 151794 228779 := bstep (se 1 (by rfl) ⟨171584, by rfl⟩ : syracuseStep 228779 = 343169) B343169
theorem B228809 : Blo 151794 228809 := bstep (se 2 (by rfl) ⟨85803, by rfl⟩ : syracuseStep 228809 = 171607) B171607
theorem B196111 : Blo 151794 196111 := bstep (se 1 (by rfl) ⟨147083, by rfl⟩ : syracuseStep 196111 = 294167) B294167
theorem B228923 : Blo 151794 228923 := bstep (se 1 (by rfl) ⟨171692, by rfl⟩ : syracuseStep 228923 = 343385) B343385
theorem B228983 : Blo 151794 228983 := bstep (se 1 (by rfl) ⟨171737, by rfl⟩ : syracuseStep 228983 = 343475) B343475
theorem B261751 : Blo 151794 261751 := bstep (se 1 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 261751 = 392627) B392627
theorem B229007 : Blo 151794 229007 := bstep (se 1 (by rfl) ⟨171755, by rfl⟩ : syracuseStep 229007 = 343511) B343511
theorem B229049 : Blo 151794 229049 := bstep (se 2 (by rfl) ⟨85893, by rfl⟩ : syracuseStep 229049 = 171787) B171787
theorem B196283 : Blo 151794 196283 := bstep (se 1 (by rfl) ⟨147212, by rfl⟩ : syracuseStep 196283 = 294425) B294425
theorem B229127 : Blo 151794 229127 := bstep (se 1 (by rfl) ⟨171845, by rfl⟩ : syracuseStep 229127 = 343691) B343691
theorem B392971 : Blo 151794 392971 := bstep (se 1 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 392971 = 589457) B589457
theorem B229163 : Blo 151794 229163 := bstep (se 1 (by rfl) ⟨171872, by rfl⟩ : syracuseStep 229163 = 343745) B343745
theorem B261947 : Blo 151794 261947 := bstep (se 1 (by rfl) ⟨196460, by rfl⟩ : syracuseStep 261947 = 392921) B392921
theorem B229193 : Blo 151794 229193 := bstep (se 2 (by rfl) ⟨85947, by rfl⟩ : syracuseStep 229193 = 171895) B171895
theorem B393113 : Blo 151794 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B229307 : Blo 151794 229307 := bstep (se 1 (by rfl) ⟨171980, by rfl⟩ : syracuseStep 229307 = 343961) B343961
theorem B229367 : Blo 151794 229367 := bstep (se 1 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 229367 = 344051) B344051
theorem B229385 : Blo 151794 229385 := bstep (se 2 (by rfl) ⟨86019, by rfl⟩ : syracuseStep 229385 = 172039) B172039
theorem B229415 : Blo 151794 229415 := bstep (se 1 (by rfl) ⟨172061, by rfl⟩ : syracuseStep 229415 = 344123) B344123
theorem B262183 : Blo 151794 262183 := bstep (se 1 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 262183 = 393275) B393275
theorem B5865533 : Blo 151794 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B393295 : Blo 151794 393295 := bstep (se 1 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 393295 = 589943) B589943
theorem B229499 : Blo 151794 229499 := bstep (se 1 (by rfl) ⟨172124, by rfl⟩ : syracuseStep 229499 = 344249) B344249
theorem B229625 : Blo 151794 229625 := bstep (se 2 (by rfl) ⟨86109, by rfl⟩ : syracuseStep 229625 = 172219) B172219
theorem B524555 : Blo 151794 524555 := bstep (se 1 (by rfl) ⟨393416, by rfl⟩ : syracuseStep 524555 = 786833) B786833
theorem B229727 : Blo 151794 229727 := bstep (se 1 (by rfl) ⟨172295, by rfl⟩ : syracuseStep 229727 = 344591) B344591
theorem B229739 : Blo 151794 229739 := bstep (se 1 (by rfl) ⟨172304, by rfl⟩ : syracuseStep 229739 = 344609) B344609
theorem B262507 : Blo 151794 262507 := bstep (se 1 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 262507 = 393761) B393761
theorem B197083 : Blo 151794 197083 := bstep (se 1 (by rfl) ⟨147812, by rfl⟩ : syracuseStep 197083 = 295625) B295625
theorem B1180169 : Blo 151794 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B524825 : Blo 151794 524825 := bstep (se 2 (by rfl) ⟨196809, by rfl⟩ : syracuseStep 524825 = 393619) B393619
theorem B492065 : Blo 151794 492065 := bstep (se 2 (by rfl) ⟨184524, by rfl⟩ : syracuseStep 492065 = 369049) B369049
theorem B295481 : Blo 151794 295481 := bstep (se 2 (by rfl) ⟨110805, by rfl⟩ : syracuseStep 295481 = 221611) B221611
theorem B229967 : Blo 151794 229967 := bstep (se 1 (by rfl) ⟨172475, by rfl⟩ : syracuseStep 229967 = 344951) B344951
theorem B1180345 : Blo 151794 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B6062789 : Blo 151794 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B230087 : Blo 151794 230087 := bstep (se 1 (by rfl) ⟨172565, by rfl⟩ : syracuseStep 230087 = 345131) B345131
theorem B393943 : Blo 151794 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B492281 : Blo 151794 492281 := bstep (se 2 (by rfl) ⟨184605, by rfl⟩ : syracuseStep 492281 = 369211) B369211
theorem B1180493 : Blo 151794 1180493 := bstep (se 3 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 1180493 = 442685) B442685
theorem B230249 : Blo 151794 230249 := bstep (se 2 (by rfl) ⟨86343, by rfl⟩ : syracuseStep 230249 = 172687) B172687
theorem B230327 : Blo 151794 230327 := bstep (se 1 (by rfl) ⟨172745, by rfl⟩ : syracuseStep 230327 = 345491) B345491
theorem B230363 : Blo 151794 230363 := bstep (se 1 (by rfl) ⟨172772, by rfl⟩ : syracuseStep 230363 = 345545) B345545
theorem B328711 : Blo 151794 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B394247 : Blo 151794 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B787475 : Blo 151794 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B656579 : Blo 151794 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B230831 : Blo 151794 230831 := bstep (se 1 (by rfl) ⟨173123, by rfl⟩ : syracuseStep 230831 = 346247) B346247
theorem B1181147 : Blo 151794 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B624115 : Blo 151794 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B230921 : Blo 151794 230921 := bstep (se 2 (by rfl) ⟨86595, by rfl⟩ : syracuseStep 230921 = 173191) B173191
theorem B230951 : Blo 151794 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B231035 : Blo 151794 231035 := bstep (se 1 (by rfl) ⟨173276, by rfl⟩ : syracuseStep 231035 = 346553) B346553
theorem B4458199 : Blo 151794 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B231161 : Blo 151794 231161 := bstep (se 2 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 231161 = 173371) B173371
theorem B2361125 : Blo 151794 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B788291 : Blo 151794 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B231263 : Blo 151794 231263 := bstep (se 1 (by rfl) ⟨173447, by rfl⟩ : syracuseStep 231263 = 346895) B346895
theorem B231275 : Blo 151794 231275 := bstep (se 1 (by rfl) ⟨173456, by rfl⟩ : syracuseStep 231275 = 346913) B346913
theorem B1771469 : Blo 151794 1771469 := bstep (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) B664301
theorem B231503 : Blo 151794 231503 := bstep (se 1 (by rfl) ⟨173627, by rfl⟩ : syracuseStep 231503 = 347255) B347255
theorem B231623 : Blo 151794 231623 := bstep (se 1 (by rfl) ⟨173717, by rfl⟩ : syracuseStep 231623 = 347435) B347435
theorem B231785 : Blo 151794 231785 := bstep (se 2 (by rfl) ⟨86919, by rfl⟩ : syracuseStep 231785 = 173839) B173839
theorem B231863 : Blo 151794 231863 := bstep (se 1 (by rfl) ⟨173897, by rfl⟩ : syracuseStep 231863 = 347795) B347795
theorem B231899 : Blo 151794 231899 := bstep (se 1 (by rfl) ⟨173924, by rfl⟩ : syracuseStep 231899 = 347849) B347849
theorem B330203 : Blo 151794 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B592393 : Blo 151794 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B560033 : Blo 151794 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B232367 : Blo 151794 232367 := bstep (se 1 (by rfl) ⟨174275, by rfl⟩ : syracuseStep 232367 = 348551) B348551
theorem B232457 : Blo 151794 232457 := bstep (se 2 (by rfl) ⟨87171, by rfl⟩ : syracuseStep 232457 = 174343) B174343
theorem B232487 : Blo 151794 232487 := bstep (se 1 (by rfl) ⟨174365, by rfl⟩ : syracuseStep 232487 = 348731) B348731
theorem B232571 : Blo 151794 232571 := bstep (se 1 (by rfl) ⟨174428, by rfl⟩ : syracuseStep 232571 = 348857) B348857
theorem B1182923 : Blo 151794 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B232697 : Blo 151794 232697 := bstep (se 2 (by rfl) ⟨87261, by rfl⟩ : syracuseStep 232697 = 174523) B174523
theorem B232799 : Blo 151794 232799 := bstep (se 1 (by rfl) ⟨174599, by rfl⟩ : syracuseStep 232799 = 349199) B349199
theorem B232811 : Blo 151794 232811 := bstep (se 1 (by rfl) ⟨174608, by rfl⟩ : syracuseStep 232811 = 349217) B349217
theorem B560621 : Blo 151794 560621 := bstep (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) B210233
theorem B396809 : Blo 151794 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B233039 : Blo 151794 233039 := bstep (se 1 (by rfl) ⟨174779, by rfl⟩ : syracuseStep 233039 = 349559) B349559
theorem B233159 : Blo 151794 233159 := bstep (se 1 (by rfl) ⟨174869, by rfl⟩ : syracuseStep 233159 = 349739) B349739
theorem B1314593 : Blo 151794 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B1183547 : Blo 151794 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B233321 : Blo 151794 233321 := bstep (se 2 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 233321 = 174991) B174991
theorem B233399 : Blo 151794 233399 := bstep (se 1 (by rfl) ⟨175049, by rfl⟩ : syracuseStep 233399 = 350099) B350099
theorem B233435 : Blo 151794 233435 := bstep (se 1 (by rfl) ⟨175076, by rfl⟩ : syracuseStep 233435 = 350153) B350153
theorem B462905 : Blo 151794 462905 := bstep (se 2 (by rfl) ⟨173589, by rfl⟩ : syracuseStep 462905 = 347179) B347179
theorem B3870989 : Blo 151794 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B1577495 : Blo 151794 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B890027 : Blo 151794 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B1251409 : Blo 151794 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B694793 : Blo 151794 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B924691 : Blo 151794 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B498707 : Blo 151794 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B597071 : Blo 151794 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B3710231 : Blo 151794 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B826789 : Blo 151794 826789 := bstep (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) B155023
theorem B826919 : Blo 151794 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B597563 : Blo 151794 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B171643 : Blo 151794 171643 := bstep (se 1 (by rfl) ⟨128732, by rfl⟩ : syracuseStep 171643 = 257465) B257465
theorem B597689 : Blo 151794 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B368327 : Blo 151794 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B172111 : Blo 151794 172111 := bstep (se 1 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 172111 = 258167) B258167
theorem B1188107 : Blo 151794 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B1188229 : Blo 151794 1188229 := bstep (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) B222793
theorem B434575 : Blo 151794 434575 := bstep (se 1 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 434575 = 651863) B651863
theorem B172507 : Blo 151794 172507 := bstep (se 1 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 172507 = 258761) B258761
theorem B467819 : Blo 151794 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B172975 : Blo 151794 172975 := bstep (se 1 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 172975 = 259463) B259463
theorem B533519 : Blo 151794 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B205903 : Blo 151794 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B173407 : Blo 151794 173407 := bstep (se 1 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 173407 = 260111) B260111
theorem B2827781 : Blo 151794 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B435851 : Blo 151794 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B468679 : Blo 151794 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B173767 : Blo 151794 173767 := bstep (se 1 (by rfl) ⟨130325, by rfl⟩ : syracuseStep 173767 = 260651) B260651
theorem B1058669 : Blo 151794 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B1058831 : Blo 151794 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B1484837 : Blo 151794 1484837 := bstep (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) B278407
theorem B5023781 : Blo 151794 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B305275 : Blo 151794 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B174631 : Blo 151794 174631 := bstep (se 1 (by rfl) ⟨130973, by rfl⟩ : syracuseStep 174631 = 261947) B261947
theorem B371719 : Blo 151794 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B928921 : Blo 151794 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B4009661 : Blo 151794 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B1421243 : Blo 151794 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B208975 : Blo 151794 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B406205 : Blo 151794 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B438995 : Blo 151794 438995 := bstep (se 1 (by rfl) ⟨329246, by rfl⟩ : syracuseStep 438995 = 658493) B658493
theorem B1160081 : Blo 151794 1160081 := bstep (se 2 (by rfl) ⟨435030, by rfl⟩ : syracuseStep 1160081 = 870061) B870061
theorem B1258415 : Blo 151794 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B439303 : Blo 151794 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B2209265 : Blo 151794 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B603863 : Blo 151794 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B341855 : Blo 151794 341855 := bstep (se 1 (by rfl) ⟨256391, by rfl⟩ : syracuseStep 341855 = 512783) B512783
theorem B440225 : Blo 151794 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B342035 : Blo 151794 342035 := bstep (se 1 (by rfl) ⟨256526, by rfl⟩ : syracuseStep 342035 = 513053) B513053
theorem B243911 : Blo 151794 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B4962545 : Blo 151794 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B342377 : Blo 151794 342377 := bstep (se 2 (by rfl) ⟨128391, by rfl⟩ : syracuseStep 342377 = 256783) B256783
theorem B440795 : Blo 151794 440795 := bstep (se 1 (by rfl) ⟨330596, by rfl⟩ : syracuseStep 440795 = 661193) B661193
theorem B867145 : Blo 151794 867145 := bstep (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) B650359
theorem B342971 : Blo 151794 342971 := bstep (se 1 (by rfl) ⟨257228, by rfl⟩ : syracuseStep 342971 = 514457) B514457
theorem B244667 : Blo 151794 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B343097 : Blo 151794 343097 := bstep (se 2 (by rfl) ⟨128661, by rfl⟩ : syracuseStep 343097 = 257323) B257323
theorem B1162511 : Blo 151794 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B343439 : Blo 151794 343439 := bstep (se 1 (by rfl) ⟨257579, by rfl⟩ : syracuseStep 343439 = 515159) B515159
theorem B769499 : Blo 151794 769499 := bstep (se 1 (by rfl) ⟨577124, by rfl⟩ : syracuseStep 769499 = 1154249) B1154249
theorem B441865 : Blo 151794 441865 := bstep (se 2 (by rfl) ⟨165699, by rfl⟩ : syracuseStep 441865 = 331399) B331399
theorem B704123 : Blo 151794 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B343763 : Blo 151794 343763 := bstep (se 1 (by rfl) ⟨257822, by rfl⟩ : syracuseStep 343763 = 515645) B515645
theorem B442219 : Blo 151794 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B311215 : Blo 151794 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B769985 : Blo 151794 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B1851569 : Blo 151794 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B246089 : Blo 151794 246089 := bstep (se 2 (by rfl) ⟨92283, by rfl⟩ : syracuseStep 246089 = 184567) B184567
theorem B344699 : Blo 151794 344699 := bstep (se 1 (by rfl) ⟨258524, by rfl⟩ : syracuseStep 344699 = 517049) B517049
theorem B344825 : Blo 151794 344825 := bstep (se 2 (by rfl) ⟨129309, by rfl⟩ : syracuseStep 344825 = 258619) B258619
theorem B443323 : Blo 151794 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B345095 : Blo 151794 345095 := bstep (se 1 (by rfl) ⟨258821, by rfl⟩ : syracuseStep 345095 = 517643) B517643
theorem B345167 : Blo 151794 345167 := bstep (se 1 (by rfl) ⟨258875, by rfl⟩ : syracuseStep 345167 = 517751) B517751
theorem B541811 : Blo 151794 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B3949721 : Blo 151794 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B1328399 : Blo 151794 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B1459619 : Blo 151794 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B345563 : Blo 151794 345563 := bstep (se 1 (by rfl) ⟨259172, by rfl⟩ : syracuseStep 345563 = 518345) B518345
theorem B739115 : Blo 151794 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B39929699 : Blo 151794 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B346031 : Blo 151794 346031 := bstep (se 1 (by rfl) ⟨259523, by rfl⟩ : syracuseStep 346031 = 519047) B519047
theorem B739343 : Blo 151794 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B1165427 : Blo 151794 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B772253 : Blo 151794 772253 := bstep (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) B289595
theorem B346283 : Blo 151794 346283 := bstep (se 1 (by rfl) ⟨259712, by rfl⟩ : syracuseStep 346283 = 519425) B519425
theorem B346823 : Blo 151794 346823 := bstep (se 1 (by rfl) ⟨260117, by rfl⟩ : syracuseStep 346823 = 520235) B520235
theorem B1198793 : Blo 151794 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B510749 : Blo 151794 510749 := bstep (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) B191531
theorem B773549 : Blo 151794 773549 := bstep (se 3 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 773549 = 290081) B290081
theorem B347687 : Blo 151794 347687 := bstep (se 1 (by rfl) ⟨260765, by rfl⟩ : syracuseStep 347687 = 521531) B521531
theorem B1756811 : Blo 151794 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B741113 : Blo 151794 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B348011 : Blo 151794 348011 := bstep (se 1 (by rfl) ⟨261008, by rfl⟩ : syracuseStep 348011 = 522017) B522017
theorem B348065 : Blo 151794 348065 := bstep (se 2 (by rfl) ⟨130524, by rfl⟩ : syracuseStep 348065 = 261049) B261049
theorem B741383 : Blo 151794 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B8605777 : Blo 151794 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B348407 : Blo 151794 348407 := bstep (se 1 (by rfl) ⟨261305, by rfl⟩ : syracuseStep 348407 = 522611) B522611
theorem B151847 : Blo 151794 151847 := bstep (se 1 (by rfl) ⟨113885, by rfl⟩ : syracuseStep 151847 = 227771) B227771
theorem B151887 : Blo 151794 151887 := bstep (se 1 (by rfl) ⟨113915, by rfl⟩ : syracuseStep 151887 = 227831) B227831
theorem B151903 : Blo 151794 151903 := bstep (se 1 (by rfl) ⟨113927, by rfl⟩ : syracuseStep 151903 = 227855) B227855
theorem B151931 : Blo 151794 151931 := bstep (se 1 (by rfl) ⟨113948, by rfl⟩ : syracuseStep 151931 = 227897) B227897
theorem B151983 : Blo 151794 151983 := bstep (se 1 (by rfl) ⟨113987, by rfl⟩ : syracuseStep 151983 = 227975) B227975
theorem B152007 : Blo 151794 152007 := bstep (se 1 (by rfl) ⟨114005, by rfl⟩ : syracuseStep 152007 = 228011) B228011
theorem B152027 : Blo 151794 152027 := bstep (se 1 (by rfl) ⟨114020, by rfl⟩ : syracuseStep 152027 = 228041) B228041
theorem B152103 : Blo 151794 152103 := bstep (se 1 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 152103 = 228155) B228155
theorem B152143 : Blo 151794 152143 := bstep (se 1 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 152143 = 228215) B228215
theorem B152159 : Blo 151794 152159 := bstep (se 1 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 152159 = 228239) B228239
theorem B152187 : Blo 151794 152187 := bstep (se 1 (by rfl) ⟨114140, by rfl⟩ : syracuseStep 152187 = 228281) B228281
theorem B152239 : Blo 151794 152239 := bstep (se 1 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 152239 = 228359) B228359
theorem B152263 : Blo 151794 152263 := bstep (se 1 (by rfl) ⟨114197, by rfl⟩ : syracuseStep 152263 = 228395) B228395
theorem B152283 : Blo 151794 152283 := bstep (se 1 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 152283 = 228425) B228425
theorem B152359 : Blo 151794 152359 := bstep (se 1 (by rfl) ⟨114269, by rfl⟩ : syracuseStep 152359 = 228539) B228539
theorem B349001 : Blo 151794 349001 := bstep (se 2 (by rfl) ⟨130875, by rfl⟩ : syracuseStep 349001 = 261751) B261751
theorem B152399 : Blo 151794 152399 := bstep (se 1 (by rfl) ⟨114299, by rfl⟩ : syracuseStep 152399 = 228599) B228599
theorem B152415 : Blo 151794 152415 := bstep (se 1 (by rfl) ⟨114311, by rfl⟩ : syracuseStep 152415 = 228623) B228623
theorem B152443 : Blo 151794 152443 := bstep (se 1 (by rfl) ⟨114332, by rfl⟩ : syracuseStep 152443 = 228665) B228665
theorem B152495 : Blo 151794 152495 := bstep (se 1 (by rfl) ⟨114371, by rfl⟩ : syracuseStep 152495 = 228743) B228743
theorem B152519 : Blo 151794 152519 := bstep (se 1 (by rfl) ⟨114389, by rfl⟩ : syracuseStep 152519 = 228779) B228779
theorem B152539 : Blo 151794 152539 := bstep (se 1 (by rfl) ⟨114404, by rfl⟩ : syracuseStep 152539 = 228809) B228809
theorem B775169 : Blo 151794 775169 := bstep (se 2 (by rfl) ⟨290688, by rfl⟩ : syracuseStep 775169 = 581377) B581377
theorem B152615 : Blo 151794 152615 := bstep (se 1 (by rfl) ⟨114461, by rfl⟩ : syracuseStep 152615 = 228923) B228923
theorem B152655 : Blo 151794 152655 := bstep (se 1 (by rfl) ⟨114491, by rfl⟩ : syracuseStep 152655 = 228983) B228983
theorem B152671 : Blo 151794 152671 := bstep (se 1 (by rfl) ⟨114503, by rfl⟩ : syracuseStep 152671 = 229007) B229007
theorem B152699 : Blo 151794 152699 := bstep (se 1 (by rfl) ⟨114524, by rfl⟩ : syracuseStep 152699 = 229049) B229049
theorem B152751 : Blo 151794 152751 := bstep (se 1 (by rfl) ⟨114563, by rfl⟩ : syracuseStep 152751 = 229127) B229127
theorem B152775 : Blo 151794 152775 := bstep (se 1 (by rfl) ⟨114581, by rfl⟩ : syracuseStep 152775 = 229163) B229163
theorem B152795 : Blo 151794 152795 := bstep (se 1 (by rfl) ⟨114596, by rfl⟩ : syracuseStep 152795 = 229193) B229193
theorem B152871 : Blo 151794 152871 := bstep (se 1 (by rfl) ⟨114653, by rfl⟩ : syracuseStep 152871 = 229307) B229307
theorem B152911 : Blo 151794 152911 := bstep (se 1 (by rfl) ⟨114683, by rfl⟩ : syracuseStep 152911 = 229367) B229367
theorem B152927 : Blo 151794 152927 := bstep (se 1 (by rfl) ⟨114695, by rfl⟩ : syracuseStep 152927 = 229391) B229391
theorem B152955 : Blo 151794 152955 := bstep (se 1 (by rfl) ⟨114716, by rfl⟩ : syracuseStep 152955 = 229433) B229433
theorem B153007 : Blo 151794 153007 := bstep (se 1 (by rfl) ⟨114755, by rfl⟩ : syracuseStep 153007 = 229511) B229511
theorem B153031 : Blo 151794 153031 := bstep (se 1 (by rfl) ⟨114773, by rfl⟩ : syracuseStep 153031 = 229547) B229547
theorem B1463771 : Blo 151794 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B153051 : Blo 151794 153051 := bstep (se 1 (by rfl) ⟨114788, by rfl⟩ : syracuseStep 153051 = 229577) B229577
theorem B153127 : Blo 151794 153127 := bstep (se 1 (by rfl) ⟨114845, by rfl⟩ : syracuseStep 153127 = 229691) B229691
theorem B153167 : Blo 151794 153167 := bstep (se 1 (by rfl) ⟨114875, by rfl⟩ : syracuseStep 153167 = 229751) B229751
theorem B153183 : Blo 151794 153183 := bstep (se 1 (by rfl) ⟨114887, by rfl⟩ : syracuseStep 153183 = 229775) B229775
theorem B349793 : Blo 151794 349793 := bstep (se 2 (by rfl) ⟨131172, by rfl⟩ : syracuseStep 349793 = 262345) B262345
theorem B153211 : Blo 151794 153211 := bstep (se 1 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 153211 = 229817) B229817
theorem B153263 : Blo 151794 153263 := bstep (se 1 (by rfl) ⟨114947, by rfl⟩ : syracuseStep 153263 = 229895) B229895
theorem B153287 : Blo 151794 153287 := bstep (se 1 (by rfl) ⟨114965, by rfl⟩ : syracuseStep 153287 = 229931) B229931
theorem B153307 : Blo 151794 153307 := bstep (se 1 (by rfl) ⟨114980, by rfl⟩ : syracuseStep 153307 = 229961) B229961
theorem B153383 : Blo 151794 153383 := bstep (se 1 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 153383 = 230075) B230075
theorem B775979 : Blo 151794 775979 := bstep (se 1 (by rfl) ⟨581984, by rfl⟩ : syracuseStep 775979 = 1163969) B1163969
theorem B153423 : Blo 151794 153423 := bstep (se 1 (by rfl) ⟨115067, by rfl⟩ : syracuseStep 153423 = 230135) B230135
theorem B153439 : Blo 151794 153439 := bstep (se 1 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 153439 = 230159) B230159
theorem B153467 : Blo 151794 153467 := bstep (se 1 (by rfl) ⟨115100, by rfl⟩ : syracuseStep 153467 = 230201) B230201
theorem B153519 : Blo 151794 153519 := bstep (se 1 (by rfl) ⟨115139, by rfl⟩ : syracuseStep 153519 = 230279) B230279
theorem B350135 : Blo 151794 350135 := bstep (se 1 (by rfl) ⟨262601, by rfl⟩ : syracuseStep 350135 = 525203) B525203
theorem B153543 : Blo 151794 153543 := bstep (se 1 (by rfl) ⟨115157, by rfl⟩ : syracuseStep 153543 = 230315) B230315
theorem B153563 : Blo 151794 153563 := bstep (se 1 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 153563 = 230345) B230345
theorem B153639 : Blo 151794 153639 := bstep (se 1 (by rfl) ⟨115229, by rfl⟩ : syracuseStep 153639 = 230459) B230459
theorem B153679 : Blo 151794 153679 := bstep (se 1 (by rfl) ⟨115259, by rfl⟩ : syracuseStep 153679 = 230519) B230519
theorem B153695 : Blo 151794 153695 := bstep (se 1 (by rfl) ⟨115271, by rfl⟩ : syracuseStep 153695 = 230543) B230543
theorem B153723 : Blo 151794 153723 := bstep (se 1 (by rfl) ⟨115292, by rfl⟩ : syracuseStep 153723 = 230585) B230585
theorem B579737 : Blo 151794 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B153775 : Blo 151794 153775 := bstep (se 1 (by rfl) ⟨115331, by rfl⟩ : syracuseStep 153775 = 230663) B230663
theorem B153799 : Blo 151794 153799 := bstep (se 1 (by rfl) ⟨115349, by rfl⟩ : syracuseStep 153799 = 230699) B230699
theorem B153819 : Blo 151794 153819 := bstep (se 1 (by rfl) ⟨115364, by rfl⟩ : syracuseStep 153819 = 230729) B230729
theorem B514295 : Blo 151794 514295 := bstep (se 1 (by rfl) ⟨385721, by rfl⟩ : syracuseStep 514295 = 771443) B771443
theorem B153895 : Blo 151794 153895 := bstep (se 1 (by rfl) ⟨115421, by rfl⟩ : syracuseStep 153895 = 230843) B230843
theorem B153935 : Blo 151794 153935 := bstep (se 1 (by rfl) ⟨115451, by rfl⟩ : syracuseStep 153935 = 230903) B230903
theorem B153951 : Blo 151794 153951 := bstep (se 1 (by rfl) ⟨115463, by rfl⟩ : syracuseStep 153951 = 230927) B230927
theorem B153979 : Blo 151794 153979 := bstep (se 1 (by rfl) ⟨115484, by rfl⟩ : syracuseStep 153979 = 230969) B230969
theorem B154031 : Blo 151794 154031 := bstep (se 1 (by rfl) ⟨115523, by rfl⟩ : syracuseStep 154031 = 231047) B231047
theorem B154055 : Blo 151794 154055 := bstep (se 1 (by rfl) ⟨115541, by rfl⟩ : syracuseStep 154055 = 231083) B231083
theorem B154075 : Blo 151794 154075 := bstep (se 1 (by rfl) ⟨115556, by rfl⟩ : syracuseStep 154075 = 231113) B231113
theorem B154151 : Blo 151794 154151 := bstep (se 1 (by rfl) ⟨115613, by rfl⟩ : syracuseStep 154151 = 231227) B231227
theorem B514619 : Blo 151794 514619 := bstep (se 1 (by rfl) ⟨385964, by rfl⟩ : syracuseStep 514619 = 771929) B771929
theorem B154191 : Blo 151794 154191 := bstep (se 1 (by rfl) ⟨115643, by rfl⟩ : syracuseStep 154191 = 231287) B231287
theorem B154207 : Blo 151794 154207 := bstep (se 1 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 154207 = 231311) B231311
theorem B580193 : Blo 151794 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B154235 : Blo 151794 154235 := bstep (se 1 (by rfl) ⟨115676, by rfl⟩ : syracuseStep 154235 = 231353) B231353
theorem B154287 : Blo 151794 154287 := bstep (se 1 (by rfl) ⟨115715, by rfl⟩ : syracuseStep 154287 = 231431) B231431
theorem B154311 : Blo 151794 154311 := bstep (se 1 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 154311 = 231467) B231467
theorem B154331 : Blo 151794 154331 := bstep (se 1 (by rfl) ⟨115748, by rfl⟩ : syracuseStep 154331 = 231497) B231497
theorem B154407 : Blo 151794 154407 := bstep (se 1 (by rfl) ⟨115805, by rfl⟩ : syracuseStep 154407 = 231611) B231611
theorem B514889 : Blo 151794 514889 := bstep (se 2 (by rfl) ⟨193083, by rfl⟩ : syracuseStep 514889 = 386167) B386167
theorem B154447 : Blo 151794 154447 := bstep (se 1 (by rfl) ⟨115835, by rfl⟩ : syracuseStep 154447 = 231671) B231671
theorem B154463 : Blo 151794 154463 := bstep (se 1 (by rfl) ⟨115847, by rfl⟩ : syracuseStep 154463 = 231695) B231695
theorem B154491 : Blo 151794 154491 := bstep (se 1 (by rfl) ⟨115868, by rfl⟩ : syracuseStep 154491 = 231737) B231737
theorem B154543 : Blo 151794 154543 := bstep (se 1 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 154543 = 231815) B231815
theorem B154567 : Blo 151794 154567 := bstep (se 1 (by rfl) ⟨115925, by rfl⟩ : syracuseStep 154567 = 231851) B231851
theorem B154587 : Blo 151794 154587 := bstep (se 1 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 154587 = 231881) B231881
theorem B154663 : Blo 151794 154663 := bstep (se 1 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 154663 = 231995) B231995
theorem B154703 : Blo 151794 154703 := bstep (se 1 (by rfl) ⟨116027, by rfl⟩ : syracuseStep 154703 = 232055) B232055
theorem B154719 : Blo 151794 154719 := bstep (se 1 (by rfl) ⟨116039, by rfl⟩ : syracuseStep 154719 = 232079) B232079
theorem B154747 : Blo 151794 154747 := bstep (se 1 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 154747 = 232121) B232121
theorem B154799 : Blo 151794 154799 := bstep (se 1 (by rfl) ⟨116099, by rfl⟩ : syracuseStep 154799 = 232199) B232199
theorem B154823 : Blo 151794 154823 := bstep (se 1 (by rfl) ⟨116117, by rfl⟩ : syracuseStep 154823 = 232235) B232235
theorem B154843 : Blo 151794 154843 := bstep (se 1 (by rfl) ⟨116132, by rfl⟩ : syracuseStep 154843 = 232265) B232265
theorem B154919 : Blo 151794 154919 := bstep (se 1 (by rfl) ⟨116189, by rfl⟩ : syracuseStep 154919 = 232379) B232379
theorem B154959 : Blo 151794 154959 := bstep (se 1 (by rfl) ⟨116219, by rfl⟩ : syracuseStep 154959 = 232439) B232439
theorem B1006937 : Blo 151794 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B154975 : Blo 151794 154975 := bstep (se 1 (by rfl) ⟨116231, by rfl⟩ : syracuseStep 154975 = 232463) B232463
theorem B155003 : Blo 151794 155003 := bstep (se 1 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 155003 = 232505) B232505
theorem B384385 : Blo 151794 384385 := bstep (se 2 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 384385 = 288289) B288289
theorem B220591 : Blo 151794 220591 := bstep (se 1 (by rfl) ⟨165443, by rfl⟩ : syracuseStep 220591 = 330887) B330887
theorem B155055 : Blo 151794 155055 := bstep (se 1 (by rfl) ⟨116291, by rfl⟩ : syracuseStep 155055 = 232583) B232583
theorem B155079 : Blo 151794 155079 := bstep (se 1 (by rfl) ⟨116309, by rfl⟩ : syracuseStep 155079 = 232619) B232619
theorem B155099 : Blo 151794 155099 := bstep (se 1 (by rfl) ⟨116324, by rfl⟩ : syracuseStep 155099 = 232649) B232649
theorem B155175 : Blo 151794 155175 := bstep (se 1 (by rfl) ⟨116381, by rfl⟩ : syracuseStep 155175 = 232763) B232763
theorem B155215 : Blo 151794 155215 := bstep (se 1 (by rfl) ⟨116411, by rfl⟩ : syracuseStep 155215 = 232823) B232823
theorem B155231 : Blo 151794 155231 := bstep (se 1 (by rfl) ⟨116423, by rfl⟩ : syracuseStep 155231 = 232847) B232847
theorem B155259 : Blo 151794 155259 := bstep (se 1 (by rfl) ⟨116444, by rfl⟩ : syracuseStep 155259 = 232889) B232889
theorem B1302155 : Blo 151794 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B155311 : Blo 151794 155311 := bstep (se 1 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 155311 = 232967) B232967
theorem B155335 : Blo 151794 155335 := bstep (se 1 (by rfl) ⟨116501, by rfl⟩ : syracuseStep 155335 = 233003) B233003
theorem B155355 : Blo 151794 155355 := bstep (se 1 (by rfl) ⟨116516, by rfl⟩ : syracuseStep 155355 = 233033) B233033
theorem B155431 : Blo 151794 155431 := bstep (se 1 (by rfl) ⟨116573, by rfl⟩ : syracuseStep 155431 = 233147) B233147
theorem B1171259 : Blo 151794 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B155471 : Blo 151794 155471 := bstep (se 1 (by rfl) ⟨116603, by rfl⟩ : syracuseStep 155471 = 233207) B233207
theorem B155487 : Blo 151794 155487 := bstep (se 1 (by rfl) ⟨116615, by rfl⟩ : syracuseStep 155487 = 233231) B233231
theorem B155515 : Blo 151794 155515 := bstep (se 1 (by rfl) ⟨116636, by rfl⟩ : syracuseStep 155515 = 233273) B233273
theorem B155567 : Blo 151794 155567 := bstep (se 1 (by rfl) ⟨116675, by rfl⟩ : syracuseStep 155567 = 233351) B233351
theorem B516023 : Blo 151794 516023 := bstep (se 1 (by rfl) ⟨387017, by rfl⟩ : syracuseStep 516023 = 774035) B774035
theorem B155591 : Blo 151794 155591 := bstep (se 1 (by rfl) ⟨116693, by rfl⟩ : syracuseStep 155591 = 233387) B233387
theorem B155611 : Blo 151794 155611 := bstep (se 1 (by rfl) ⟨116708, by rfl⟩ : syracuseStep 155611 = 233417) B233417
theorem B778247 : Blo 151794 778247 := bstep (se 1 (by rfl) ⟨583685, by rfl⟩ : syracuseStep 778247 = 1167371) B1167371
theorem B581651 : Blo 151794 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B155687 : Blo 151794 155687 := bstep (se 1 (by rfl) ⟨116765, by rfl⟩ : syracuseStep 155687 = 233531) B233531
theorem B155727 : Blo 151794 155727 := bstep (se 1 (by rfl) ⟨116795, by rfl⟩ : syracuseStep 155727 = 233591) B233591
theorem B155743 : Blo 151794 155743 := bstep (se 1 (by rfl) ⟨116807, by rfl⟩ : syracuseStep 155743 = 233615) B233615
theorem B1794163 : Blo 151794 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B155771 : Blo 151794 155771 := bstep (se 1 (by rfl) ⟨116828, by rfl⟩ : syracuseStep 155771 = 233657) B233657
theorem B385195 : Blo 151794 385195 := bstep (se 1 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 385195 = 577793) B577793
theorem B221383 : Blo 151794 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B385499 : Blo 151794 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B778733 : Blo 151794 778733 := bstep (se 3 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 778733 = 292025) B292025
theorem B516617 : Blo 151794 516617 := bstep (se 2 (by rfl) ⟨193731, by rfl⟩ : syracuseStep 516617 = 387463) B387463
theorem B156199 : Blo 151794 156199 := bstep (se 1 (by rfl) ⟨117149, by rfl⟩ : syracuseStep 156199 = 234299) B234299
theorem B1991627 : Blo 151794 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B418823 : Blo 151794 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B222331 : Blo 151794 222331 := bstep (se 1 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 222331 = 333497) B333497
theorem B779543 : Blo 151794 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B517481 : Blo 151794 517481 := bstep (se 2 (by rfl) ⟨194055, by rfl⟩ : syracuseStep 517481 = 388111) B388111
theorem B1893851 : Blo 151794 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B288335 : Blo 151794 288335 := bstep (se 1 (by rfl) ⟨216251, by rfl⟩ : syracuseStep 288335 = 432503) B432503
theorem B583307 : Blo 151794 583307 := bstep (se 1 (by rfl) ⟨437480, by rfl⟩ : syracuseStep 583307 = 874961) B874961
theorem B550817 : Blo 151794 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B386977 : Blo 151794 386977 := bstep (se 2 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 386977 = 290233) B290233
theorem B518075 : Blo 151794 518075 := bstep (se 1 (by rfl) ⟨388556, by rfl⟩ : syracuseStep 518075 = 777113) B777113
theorem B288775 : Blo 151794 288775 := bstep (se 1 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 288775 = 433163) B433163
theorem B550919 : Blo 151794 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B256351 : Blo 151794 256351 := bstep (se 1 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 256351 = 384527) B384527
theorem B256439 : Blo 151794 256439 := bstep (se 1 (by rfl) ⟨192329, by rfl⟩ : syracuseStep 256439 = 384659) B384659
theorem B748091 : Blo 151794 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B3533645 : Blo 151794 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B977771 : Blo 151794 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B781163 : Blo 151794 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B584567 : Blo 151794 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B257033 : Blo 151794 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B289831 : Blo 151794 289831 := bstep (se 1 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 289831 = 434747) B434747
theorem B257195 : Blo 151794 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B880091 : Blo 151794 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B781811 : Blo 151794 781811 := bstep (se 1 (by rfl) ⟨586358, by rfl⟩ : syracuseStep 781811 = 1172717) B1172717
theorem B257593 : Blo 151794 257593 := bstep (se 2 (by rfl) ⟨96597, by rfl⟩ : syracuseStep 257593 = 193195) B193195
theorem B519803 : Blo 151794 519803 := bstep (se 1 (by rfl) ⟨389852, by rfl⟩ : syracuseStep 519803 = 779705) B779705
theorem B880267 : Blo 151794 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B1175239 : Blo 151794 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B257735 : Blo 151794 257735 := bstep (se 1 (by rfl) ⟨193301, by rfl⟩ : syracuseStep 257735 = 386603) B386603
theorem B519965 : Blo 151794 519965 := bstep (se 3 (by rfl) ⟨97493, by rfl⟩ : syracuseStep 519965 = 194987) B194987
theorem B585539 : Blo 151794 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B257897 : Blo 151794 257897 := bstep (se 2 (by rfl) ⟨96711, by rfl⟩ : syracuseStep 257897 = 193423) B193423
theorem B520111 : Blo 151794 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B1175633 : Blo 151794 1175633 := bstep (se 2 (by rfl) ⟨440862, by rfl⟩ : syracuseStep 1175633 = 881725) B881725
theorem B258295 : Blo 151794 258295 := bstep (se 1 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 258295 = 387443) B387443
theorem B389519 : Blo 151794 389519 := bstep (se 1 (by rfl) ⟨292139, by rfl⟩ : syracuseStep 389519 = 584279) B584279
theorem B258491 : Blo 151794 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B520667 : Blo 151794 520667 := bstep (se 1 (by rfl) ⟨390500, by rfl⟩ : syracuseStep 520667 = 781001) B781001
theorem B258599 : Blo 151794 258599 := bstep (se 1 (by rfl) ⟨193949, by rfl⟩ : syracuseStep 258599 = 387899) B387899
theorem B291539 : Blo 151794 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B389843 : Blo 151794 389843 := bstep (se 1 (by rfl) ⟨292382, by rfl⟩ : syracuseStep 389843 = 584765) B584765
theorem B783107 : Blo 151794 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B258889 : Blo 151794 258889 := bstep (se 2 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 258889 = 194167) B194167
theorem B258923 : Blo 151794 258923 := bstep (se 1 (by rfl) ⟨194192, by rfl⟩ : syracuseStep 258923 = 388385) B388385
theorem B291691 : Blo 151794 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B1045583 : Blo 151794 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B291919 : Blo 151794 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B8975447 : Blo 151794 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B521369 : Blo 151794 521369 := bstep (se 2 (by rfl) ⟨195513, by rfl⟩ : syracuseStep 521369 = 391027) B391027
theorem B2880715 : Blo 151794 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B259321 : Blo 151794 259321 := bstep (se 2 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 259321 = 194491) B194491
theorem B3536243 : Blo 151794 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1963379 : Blo 151794 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B587209 : Blo 151794 587209 := bstep (se 2 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 587209 = 440407) B440407
theorem B259591 : Blo 151794 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B325129 : Blo 151794 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B4159127 : Blo 151794 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B587513 : Blo 151794 587513 := bstep (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) B440635
theorem B325471 : Blo 151794 325471 := bstep (se 1 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 325471 = 488207) B488207
theorem B391007 : Blo 151794 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B849773 : Blo 151794 849773 := bstep (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) B318665
theorem B587681 : Blo 151794 587681 := bstep (se 2 (by rfl) ⟨220380, by rfl⟩ : syracuseStep 587681 = 440761) B440761
theorem B587695 : Blo 151794 587695 := bstep (se 1 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 587695 = 881543) B881543
theorem B260023 : Blo 151794 260023 := bstep (se 1 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 260023 = 390035) B390035
theorem B292871 : Blo 151794 292871 := bstep (se 1 (by rfl) ⟨219653, by rfl⟩ : syracuseStep 292871 = 439307) B439307
theorem B260219 : Blo 151794 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B522557 : Blo 151794 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B784727 : Blo 151794 784727 := bstep (se 1 (by rfl) ⟨588545, by rfl⟩ : syracuseStep 784727 = 1177091) B1177091
theorem B227759 : Blo 151794 227759 := bstep (se 1 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 227759 = 341639) B341639
theorem B227849 : Blo 151794 227849 := bstep (se 2 (by rfl) ⟨85443, by rfl⟩ : syracuseStep 227849 = 170887) B170887
theorem B260617 : Blo 151794 260617 := bstep (se 2 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 260617 = 195463) B195463
theorem B227879 : Blo 151794 227879 := bstep (se 1 (by rfl) ⟨170909, by rfl⟩ : syracuseStep 227879 = 341819) B341819
theorem B227963 : Blo 151794 227963 := bstep (se 1 (by rfl) ⟨170972, by rfl⟩ : syracuseStep 227963 = 341945) B341945
theorem B260779 : Blo 151794 260779 := bstep (se 1 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 260779 = 391169) B391169
theorem B228089 : Blo 151794 228089 := bstep (se 2 (by rfl) ⟨85533, by rfl⟩ : syracuseStep 228089 = 171067) B171067
theorem B490283 : Blo 151794 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B228191 : Blo 151794 228191 := bstep (se 1 (by rfl) ⟨171143, by rfl⟩ : syracuseStep 228191 = 342287) B342287
theorem B228203 : Blo 151794 228203 := bstep (se 1 (by rfl) ⟨171152, by rfl⟩ : syracuseStep 228203 = 342305) B342305
theorem B1112939 : Blo 151794 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B588653 : Blo 151794 588653 := bstep (se 3 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 588653 = 220745) B220745
theorem B392111 : Blo 151794 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B261083 : Blo 151794 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B228431 : Blo 151794 228431 := bstep (se 1 (by rfl) ⟨171323, by rfl⟩ : syracuseStep 228431 = 342647) B342647
theorem B523421 : Blo 151794 523421 := bstep (se 3 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 523421 = 196283) B196283
theorem B588971 : Blo 151794 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B261319 : Blo 151794 261319 := bstep (se 1 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 261319 = 391979) B391979
theorem B228551 : Blo 151794 228551 := bstep (se 1 (by rfl) ⟨171413, by rfl⟩ : syracuseStep 228551 = 342827) B342827
theorem B228713 : Blo 151794 228713 := bstep (se 2 (by rfl) ⟨85767, by rfl⟩ : syracuseStep 228713 = 171535) B171535
theorem B327017 : Blo 151794 327017 := bstep (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) B245263
theorem B261481 : Blo 151794 261481 := bstep (se 2 (by rfl) ⟨98055, by rfl⟩ : syracuseStep 261481 = 196111) B196111
theorem B884141 : Blo 151794 884141 := bstep (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) B331553
theorem B196015 : Blo 151794 196015 := bstep (se 1 (by rfl) ⟨147011, by rfl⟩ : syracuseStep 196015 = 294023) B294023
theorem B228791 : Blo 151794 228791 := bstep (se 1 (by rfl) ⟨171593, by rfl⟩ : syracuseStep 228791 = 343187) B343187
theorem B228827 : Blo 151794 228827 := bstep (se 1 (by rfl) ⟨171620, by rfl⟩ : syracuseStep 228827 = 343241) B343241
theorem B556583 : Blo 151794 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B523961 : Blo 151794 523961 := bstep (se 2 (by rfl) ⟨196485, by rfl⟩ : syracuseStep 523961 = 392971) B392971
theorem B884641 : Blo 151794 884641 := bstep (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) B663481
theorem B229295 : Blo 151794 229295 := bstep (se 1 (by rfl) ⟨171971, by rfl⟩ : syracuseStep 229295 = 343943) B343943
theorem B262075 : Blo 151794 262075 := bstep (se 1 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 262075 = 393113) B393113
theorem B229481 : Blo 151794 229481 := bstep (se 2 (by rfl) ⟨86055, by rfl⟩ : syracuseStep 229481 = 172111) B172111
theorem B524393 : Blo 151794 524393 := bstep (se 2 (by rfl) ⟨196647, by rfl⟩ : syracuseStep 524393 = 393295) B393295
theorem B2392217 : Blo 151794 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B295177 : Blo 151794 295177 := bstep (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) B221383
theorem B786779 : Blo 151794 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B328043 : Blo 151794 328043 := bstep (se 1 (by rfl) ⟨246032, by rfl⟩ : syracuseStep 328043 = 492065) B492065
theorem B196987 : Blo 151794 196987 := bstep (se 1 (by rfl) ⟨147740, by rfl⟩ : syracuseStep 196987 = 295481) B295481
theorem B229799 : Blo 151794 229799 := bstep (se 1 (by rfl) ⟨172349, by rfl⟩ : syracuseStep 229799 = 344699) B344699
theorem B229883 : Blo 151794 229883 := bstep (se 1 (by rfl) ⟨172412, by rfl⟩ : syracuseStep 229883 = 344825) B344825
theorem B328187 : Blo 151794 328187 := bstep (se 1 (by rfl) ⟨246140, by rfl⟩ : syracuseStep 328187 = 492281) B492281
theorem B786995 : Blo 151794 786995 := bstep (se 1 (by rfl) ⟨590246, by rfl⟩ : syracuseStep 786995 = 1180493) B1180493
theorem B230009 : Blo 151794 230009 := bstep (se 2 (by rfl) ⟨86253, by rfl⟩ : syracuseStep 230009 = 172507) B172507
theorem B262777 : Blo 151794 262777 := bstep (se 2 (by rfl) ⟨98541, by rfl⟩ : syracuseStep 262777 = 197083) B197083
theorem B230063 : Blo 151794 230063 := bstep (se 1 (by rfl) ⟨172547, by rfl⟩ : syracuseStep 230063 = 345095) B345095
theorem B262831 : Blo 151794 262831 := bstep (se 1 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 262831 = 394247) B394247
theorem B524983 : Blo 151794 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B230111 : Blo 151794 230111 := bstep (se 1 (by rfl) ⟨172583, by rfl⟩ : syracuseStep 230111 = 345167) B345167
theorem B361207 : Blo 151794 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B885599 : Blo 151794 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B656237 : Blo 151794 656237 := bstep (se 3 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 656237 = 246089) B246089
theorem B1573793 : Blo 151794 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B525257 : Blo 151794 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B230375 : Blo 151794 230375 := bstep (se 1 (by rfl) ⟨172781, by rfl⟩ : syracuseStep 230375 = 345563) B345563
theorem B1574083 : Blo 151794 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B492743 : Blo 151794 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B525527 : Blo 151794 525527 := bstep (se 1 (by rfl) ⟨394145, by rfl⟩ : syracuseStep 525527 = 788291) B788291
theorem B230633 : Blo 151794 230633 := bstep (se 2 (by rfl) ⟨86487, by rfl⟩ : syracuseStep 230633 = 172975) B172975
theorem B591097 : Blo 151794 591097 := bstep (se 2 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 591097 = 443323) B443323
theorem B230687 : Blo 151794 230687 := bstep (se 1 (by rfl) ⟨173015, by rfl⟩ : syracuseStep 230687 = 346031) B346031
theorem B1180979 : Blo 151794 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B492895 : Blo 151794 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B230855 : Blo 151794 230855 := bstep (se 1 (by rfl) ⟨173141, by rfl⟩ : syracuseStep 230855 = 346283) B346283
theorem B296441 : Blo 151794 296441 := bstep (se 2 (by rfl) ⟨111165, by rfl⟩ : syracuseStep 296441 = 222331) B222331
theorem B231209 : Blo 151794 231209 := bstep (se 2 (by rfl) ⟨86703, by rfl⟩ : syracuseStep 231209 = 173407) B173407
theorem B231215 : Blo 151794 231215 := bstep (se 1 (by rfl) ⟨173411, by rfl⟩ : syracuseStep 231215 = 346823) B346823
theorem B788615 : Blo 151794 788615 := bstep (se 1 (by rfl) ⟨591461, by rfl⟩ : syracuseStep 788615 = 1182923) B1182923
theorem B624905 : Blo 151794 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B231689 : Blo 151794 231689 := bstep (se 2 (by rfl) ⟨86883, by rfl⟩ : syracuseStep 231689 = 173767) B173767
theorem B264539 : Blo 151794 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B231791 : Blo 151794 231791 := bstep (se 1 (by rfl) ⟨173843, by rfl⟩ : syracuseStep 231791 = 347687) B347687
theorem B494075 : Blo 151794 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B789031 : Blo 151794 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B232007 : Blo 151794 232007 := bstep (se 1 (by rfl) ⟨174005, by rfl⟩ : syracuseStep 232007 = 348011) B348011
theorem B232043 : Blo 151794 232043 := bstep (se 1 (by rfl) ⟨174032, by rfl⟩ : syracuseStep 232043 = 348065) B348065
theorem B494255 : Blo 151794 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B232271 : Blo 151794 232271 := bstep (se 1 (by rfl) ⟨174203, by rfl⟩ : syracuseStep 232271 = 348407) B348407
theorem B1051663 : Blo 151794 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B232667 : Blo 151794 232667 := bstep (se 1 (by rfl) ⟨174500, by rfl⟩ : syracuseStep 232667 = 349001) B349001
theorem B789857 : Blo 151794 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B232841 : Blo 151794 232841 := bstep (se 2 (by rfl) ⟨87315, by rfl⟩ : syracuseStep 232841 = 174631) B174631
theorem B593351 : Blo 151794 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B233195 : Blo 151794 233195 := bstep (se 1 (by rfl) ⟨174896, by rfl⟩ : syracuseStep 233195 = 349793) B349793
theorem B3149725 : Blo 151794 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B233423 : Blo 151794 233423 := bstep (se 1 (by rfl) ⟨175067, by rfl⟩ : syracuseStep 233423 = 350135) B350135
theorem B463195 : Blo 151794 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B332471 : Blo 151794 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B398047 : Blo 151794 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B2266061 : Blo 151794 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B398375 : Blo 151794 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B398459 : Blo 151794 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B693481 : Blo 151794 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B11474369 : Blo 151794 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B792071 : Blo 151794 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B5936885 : Blo 151794 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B367211 : Blo 151794 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B989891 : Blo 151794 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B3349187 : Blo 151794 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B3840953 : Blo 151794 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B170959 : Blo 151794 170959 := bstep (se 1 (by rfl) ⟨128219, by rfl⟩ : syracuseStep 170959 = 256439) B256439
theorem B498727 : Blo 151794 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B171355 : Blo 151794 171355 := bstep (se 1 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 171355 = 257033) B257033
theorem B433505 : Blo 151794 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B171463 : Blo 151794 171463 := bstep (se 1 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 171463 = 257195) B257195
theorem B433961 : Blo 151794 433961 := bstep (se 2 (by rfl) ⟨162735, by rfl⟩ : syracuseStep 433961 = 325471) B325471
theorem B171823 : Blo 151794 171823 := bstep (se 1 (by rfl) ⟨128867, by rfl⟩ : syracuseStep 171823 = 257735) B257735
theorem B171931 : Blo 151794 171931 := bstep (se 1 (by rfl) ⟨128948, by rfl⟩ : syracuseStep 171931 = 257897) B257897
theorem B172327 : Blo 151794 172327 := bstep (se 1 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 172327 = 258491) B258491
theorem B172399 : Blo 151794 172399 := bstep (se 1 (by rfl) ⟨129299, by rfl⟩ : syracuseStep 172399 = 258599) B258599
theorem B270803 : Blo 151794 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B172615 : Blo 151794 172615 := bstep (se 1 (by rfl) ⟨129461, by rfl⟩ : syracuseStep 172615 = 258923) B258923
theorem B697055 : Blo 151794 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B1156193 : Blo 151794 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B402575 : Blo 151794 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B173479 : Blo 151794 173479 := bstep (se 1 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 173479 = 260219) B260219
theorem B174055 : Blo 151794 174055 := bstep (se 1 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 174055 = 261083) B261083
theorem B469415 : Blo 151794 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B3910355 : Blo 151794 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B4041859 : Blo 151794 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B1584305 : Blo 151794 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B208265 : Blo 151794 208265 := bstep (se 2 (by rfl) ⟨78099, by rfl⟩ : syracuseStep 208265 = 156199) B156199
theorem B2633147 : Blo 151794 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B437719 : Blo 151794 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B26619799 : Blo 151794 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B438281 : Blo 151794 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B274537 : Blo 151794 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B799195 : Blo 151794 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B340499 : Blo 151794 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B373355 : Blo 151794 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B5944265 : Blo 151794 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B373747 : Blo 151794 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B308603 : Blo 151794 308603 := bstep (se 1 (by rfl) ⟨231452, by rfl⟩ : syracuseStep 308603 = 462905) B462905
theorem B407033 : Blo 151794 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B341801 : Blo 151794 341801 := bstep (se 2 (by rfl) ⟨128175, by rfl⟩ : syracuseStep 341801 = 256351) B256351
theorem B342863 : Blo 151794 342863 := bstep (se 1 (by rfl) ⟨257147, by rfl⟩ : syracuseStep 342863 = 514295) B514295
theorem B343079 : Blo 151794 343079 := bstep (se 1 (by rfl) ⟨257309, by rfl⟩ : syracuseStep 343079 = 514619) B514619
theorem B343259 : Blo 151794 343259 := bstep (se 1 (by rfl) ⟨257444, by rfl⟩ : syracuseStep 343259 = 514889) B514889
theorem B343457 : Blo 151794 343457 := bstep (se 2 (by rfl) ⟨128796, by rfl⟩ : syracuseStep 343457 = 257593) B257593
theorem B2473487 : Blo 151794 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B671291 : Blo 151794 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B868103 : Blo 151794 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B344015 : Blo 151794 344015 := bstep (se 1 (by rfl) ⟨258011, by rfl⟩ : syracuseStep 344015 = 516023) B516023
theorem B1982501 : Blo 151794 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B278633 : Blo 151794 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B344393 : Blo 151794 344393 := bstep (se 2 (by rfl) ⟨129147, by rfl⟩ : syracuseStep 344393 = 258295) B258295
theorem B344411 : Blo 151794 344411 := bstep (se 1 (by rfl) ⟨258308, by rfl⟩ : syracuseStep 344411 = 516617) B516617
theorem B311879 : Blo 151794 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B1327751 : Blo 151794 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B279215 : Blo 151794 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B344987 : Blo 151794 344987 := bstep (se 1 (by rfl) ⟨258740, by rfl⟩ : syracuseStep 344987 = 517481) B517481
theorem B1262567 : Blo 151794 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B1885187 : Blo 151794 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B345185 : Blo 151794 345185 := bstep (se 2 (by rfl) ⟨129444, by rfl⟩ : syracuseStep 345185 = 258889) B258889
theorem B705779 : Blo 151794 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B345383 : Blo 151794 345383 := bstep (se 1 (by rfl) ⟨259037, by rfl⟩ : syracuseStep 345383 = 518075) B518075
theorem B705887 : Blo 151794 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B345761 : Blo 151794 345761 := bstep (se 2 (by rfl) ⟨129660, by rfl⟩ : syracuseStep 345761 = 259321) B259321
theorem B346121 : Blo 151794 346121 := bstep (se 2 (by rfl) ⟨129795, by rfl⟩ : syracuseStep 346121 = 259591) B259591
theorem B9423053 : Blo 151794 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B346535 : Blo 151794 346535 := bstep (se 1 (by rfl) ⟨259901, by rfl⟩ : syracuseStep 346535 = 519803) B519803
theorem B2673107 : Blo 151794 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B346643 : Blo 151794 346643 := bstep (se 1 (by rfl) ⟨259982, by rfl⟩ : syracuseStep 346643 = 519965) B519965
theorem B346697 : Blo 151794 346697 := bstep (se 2 (by rfl) ⟨130011, by rfl⟩ : syracuseStep 346697 = 260023) B260023
theorem B3328613 : Blo 151794 3328613 := bstep (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) B624115
theorem B347111 : Blo 151794 347111 := bstep (se 1 (by rfl) ⟨260333, by rfl⟩ : syracuseStep 347111 = 520667) B520667
theorem B773387 : Blo 151794 773387 := bstep (se 1 (by rfl) ⟨580040, by rfl⟩ : syracuseStep 773387 = 1160081) B1160081
theorem B838943 : Blo 151794 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B347489 : Blo 151794 347489 := bstep (se 2 (by rfl) ⟨130308, by rfl⟩ : syracuseStep 347489 = 260617) B260617
theorem B5983631 : Blo 151794 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B347579 : Blo 151794 347579 := bstep (se 1 (by rfl) ⟨260684, by rfl⟩ : syracuseStep 347579 = 521369) B521369
theorem B347705 : Blo 151794 347705 := bstep (se 2 (by rfl) ⟨130389, by rfl⟩ : syracuseStep 347705 = 260779) B260779
theorem B872045 : Blo 151794 872045 := bstep (se 3 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 872045 = 327017) B327017
theorem B2772751 : Blo 151794 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B1232921 : Blo 151794 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B348371 : Blo 151794 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B348425 : Blo 151794 348425 := bstep (se 2 (by rfl) ⟨130659, by rfl⟩ : syracuseStep 348425 = 261319) B261319
theorem B151839 : Blo 151794 151839 := bstep (se 1 (by rfl) ⟨113879, by rfl⟩ : syracuseStep 151839 = 227759) B227759
theorem B151899 : Blo 151794 151899 := bstep (se 1 (by rfl) ⟨113924, by rfl⟩ : syracuseStep 151899 = 227849) B227849
theorem B151919 : Blo 151794 151919 := bstep (se 1 (by rfl) ⟨113939, by rfl⟩ : syracuseStep 151919 = 227879) B227879
theorem B151975 : Blo 151794 151975 := bstep (se 1 (by rfl) ⟨113981, by rfl⟩ : syracuseStep 151975 = 227963) B227963
theorem B348641 : Blo 151794 348641 := bstep (se 2 (by rfl) ⟨130740, by rfl⟩ : syracuseStep 348641 = 261481) B261481
theorem B152059 : Blo 151794 152059 := bstep (se 1 (by rfl) ⟨114044, by rfl⟩ : syracuseStep 152059 = 228089) B228089
theorem B512513 : Blo 151794 512513 := bstep (se 2 (by rfl) ⟨192192, by rfl⟩ : syracuseStep 512513 = 384385) B384385
theorem B1102385 : Blo 151794 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B152127 : Blo 151794 152127 := bstep (se 1 (by rfl) ⟨114095, by rfl⟩ : syracuseStep 152127 = 228191) B228191
theorem B152135 : Blo 151794 152135 := bstep (se 1 (by rfl) ⟨114101, by rfl⟩ : syracuseStep 152135 = 228203) B228203
theorem B741959 : Blo 151794 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B152287 : Blo 151794 152287 := bstep (se 1 (by rfl) ⟨114215, by rfl⟩ : syracuseStep 152287 = 228431) B228431
theorem B348947 : Blo 151794 348947 := bstep (se 1 (by rfl) ⟨261710, by rfl⟩ : syracuseStep 348947 = 523421) B523421
theorem B152367 : Blo 151794 152367 := bstep (se 1 (by rfl) ⟨114275, by rfl⟩ : syracuseStep 152367 = 228551) B228551
theorem B775007 : Blo 151794 775007 := bstep (se 1 (by rfl) ⟨581255, by rfl⟩ : syracuseStep 775007 = 1162511) B1162511
theorem B152475 : Blo 151794 152475 := bstep (se 1 (by rfl) ⟨114356, by rfl⟩ : syracuseStep 152475 = 228713) B228713
theorem B152527 : Blo 151794 152527 := bstep (se 1 (by rfl) ⟨114395, by rfl⟩ : syracuseStep 152527 = 228791) B228791
theorem B512999 : Blo 151794 512999 := bstep (se 1 (by rfl) ⟨384749, by rfl⟩ : syracuseStep 512999 = 769499) B769499
theorem B152551 : Blo 151794 152551 := bstep (se 1 (by rfl) ⟨114413, by rfl⟩ : syracuseStep 152551 = 228827) B228827
theorem B349307 : Blo 151794 349307 := bstep (se 1 (by rfl) ⟨261980, by rfl⟩ : syracuseStep 349307 = 523961) B523961
theorem B414953 : Blo 151794 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B349433 : Blo 151794 349433 := bstep (se 2 (by rfl) ⟨131037, by rfl⟩ : syracuseStep 349433 = 262075) B262075
theorem B152863 : Blo 151794 152863 := bstep (se 1 (by rfl) ⟨114647, by rfl⟩ : syracuseStep 152863 = 229295) B229295
theorem B513323 : Blo 151794 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B152923 : Blo 151794 152923 := bstep (se 1 (by rfl) ⟨114692, by rfl⟩ : syracuseStep 152923 = 229385) B229385
theorem B152943 : Blo 151794 152943 := bstep (se 1 (by rfl) ⟨114707, by rfl⟩ : syracuseStep 152943 = 229415) B229415
theorem B349577 : Blo 151794 349577 := bstep (se 2 (by rfl) ⟨131091, by rfl⟩ : syracuseStep 349577 = 262183) B262183
theorem B152999 : Blo 151794 152999 := bstep (se 1 (by rfl) ⟨114749, by rfl⟩ : syracuseStep 152999 = 229499) B229499
theorem B1234379 : Blo 151794 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B153083 : Blo 151794 153083 := bstep (se 1 (by rfl) ⟨114812, by rfl⟩ : syracuseStep 153083 = 229625) B229625
theorem B349703 : Blo 151794 349703 := bstep (se 1 (by rfl) ⟨262277, by rfl⟩ : syracuseStep 349703 = 524555) B524555
theorem B513593 : Blo 151794 513593 := bstep (se 2 (by rfl) ⟨192597, by rfl⟩ : syracuseStep 513593 = 385195) B385195
theorem B153151 : Blo 151794 153151 := bstep (se 1 (by rfl) ⟨114863, by rfl⟩ : syracuseStep 153151 = 229727) B229727
theorem B153159 : Blo 151794 153159 := bstep (se 1 (by rfl) ⟨114869, by rfl⟩ : syracuseStep 153159 = 229739) B229739
theorem B349883 : Blo 151794 349883 := bstep (se 1 (by rfl) ⟨262412, by rfl⟩ : syracuseStep 349883 = 524825) B524825
theorem B153311 : Blo 151794 153311 := bstep (se 1 (by rfl) ⟨114983, by rfl⟩ : syracuseStep 153311 = 229967) B229967
theorem B153391 : Blo 151794 153391 := bstep (se 1 (by rfl) ⟨115043, by rfl⟩ : syracuseStep 153391 = 230087) B230087
theorem B350009 : Blo 151794 350009 := bstep (se 2 (by rfl) ⟨131253, by rfl⟩ : syracuseStep 350009 = 262507) B262507
theorem B579433 : Blo 151794 579433 := bstep (se 2 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 579433 = 434575) B434575
theorem B153499 : Blo 151794 153499 := bstep (se 1 (by rfl) ⟨115124, by rfl⟩ : syracuseStep 153499 = 230249) B230249
theorem B153551 : Blo 151794 153551 := bstep (se 1 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 153551 = 230327) B230327
theorem B22763477 : Blo 151794 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B153575 : Blo 151794 153575 := bstep (se 1 (by rfl) ⟨115181, by rfl⟩ : syracuseStep 153575 = 230363) B230363
theorem B973079 : Blo 151794 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B153887 : Blo 151794 153887 := bstep (se 1 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 153887 = 230831) B230831
theorem B153947 : Blo 151794 153947 := bstep (se 1 (by rfl) ⟨115460, by rfl⟩ : syracuseStep 153947 = 230921) B230921
theorem B153967 : Blo 151794 153967 := bstep (se 1 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 153967 = 230951) B230951
theorem B154023 : Blo 151794 154023 := bstep (se 1 (by rfl) ⟨115517, by rfl⟩ : syracuseStep 154023 = 231035) B231035
theorem B154107 : Blo 151794 154107 := bstep (se 1 (by rfl) ⟨115580, by rfl⟩ : syracuseStep 154107 = 231161) B231161
theorem B154175 : Blo 151794 154175 := bstep (se 1 (by rfl) ⟨115631, by rfl⟩ : syracuseStep 154175 = 231263) B231263
theorem B154183 : Blo 151794 154183 := bstep (se 1 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 154183 = 231275) B231275
theorem B154335 : Blo 151794 154335 := bstep (se 1 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 154335 = 231503) B231503
theorem B776951 : Blo 151794 776951 := bstep (se 1 (by rfl) ⟨582713, by rfl⟩ : syracuseStep 776951 = 1165427) B1165427
theorem B514835 : Blo 151794 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B154415 : Blo 151794 154415 := bstep (se 1 (by rfl) ⟨115811, by rfl⟩ : syracuseStep 154415 = 231623) B231623
theorem B154523 : Blo 151794 154523 := bstep (se 1 (by rfl) ⟨115892, by rfl⟩ : syracuseStep 154523 = 231785) B231785
theorem B154575 : Blo 151794 154575 := bstep (se 1 (by rfl) ⟨115931, by rfl⟩ : syracuseStep 154575 = 231863) B231863
theorem B154599 : Blo 151794 154599 := bstep (se 1 (by rfl) ⟨115949, by rfl⟩ : syracuseStep 154599 = 231899) B231899
theorem B777437 : Blo 151794 777437 := bstep (se 3 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 777437 = 291539) B291539
theorem B154911 : Blo 151794 154911 := bstep (se 1 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 154911 = 232367) B232367
theorem B154971 : Blo 151794 154971 := bstep (se 1 (by rfl) ⟨116228, by rfl⟩ : syracuseStep 154971 = 232457) B232457
theorem B154991 : Blo 151794 154991 := bstep (se 1 (by rfl) ⟨116243, by rfl⟩ : syracuseStep 154991 = 232487) B232487
theorem B155047 : Blo 151794 155047 := bstep (se 1 (by rfl) ⟨116285, by rfl⟩ : syracuseStep 155047 = 232571) B232571
theorem B155131 : Blo 151794 155131 := bstep (se 1 (by rfl) ⟨116348, by rfl⟩ : syracuseStep 155131 = 232697) B232697
theorem B155199 : Blo 151794 155199 := bstep (se 1 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 155199 = 232799) B232799
theorem B155207 : Blo 151794 155207 := bstep (se 1 (by rfl) ⟨116405, by rfl⟩ : syracuseStep 155207 = 232811) B232811
theorem B515699 : Blo 151794 515699 := bstep (se 1 (by rfl) ⟨386774, by rfl⟩ : syracuseStep 515699 = 773549) B773549
theorem B155359 : Blo 151794 155359 := bstep (se 1 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 155359 = 233039) B233039
theorem B1171207 : Blo 151794 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B155439 : Blo 151794 155439 := bstep (se 1 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 155439 = 233159) B233159
theorem B876395 : Blo 151794 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B515969 : Blo 151794 515969 := bstep (se 2 (by rfl) ⟨193488, by rfl⟩ : syracuseStep 515969 = 386977) B386977
theorem B155547 : Blo 151794 155547 := bstep (se 1 (by rfl) ⟨116660, by rfl⟩ : syracuseStep 155547 = 233321) B233321
theorem B155599 : Blo 151794 155599 := bstep (se 1 (by rfl) ⟨116699, by rfl⟩ : syracuseStep 155599 = 233399) B233399
theorem B155623 : Blo 151794 155623 := bstep (se 1 (by rfl) ⟨116717, by rfl⟩ : syracuseStep 155623 = 233435) B233435
theorem B385033 : Blo 151794 385033 := bstep (se 2 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 385033 = 288775) B288775
theorem B2580659 : Blo 151794 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B516779 : Blo 151794 516779 := bstep (se 1 (by rfl) ⟨387584, by rfl⟩ : syracuseStep 516779 = 775169) B775169
theorem B975847 : Blo 151794 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B517319 : Blo 151794 517319 := bstep (se 1 (by rfl) ⟨387989, by rfl⟩ : syracuseStep 517319 = 775979) B775979
theorem B386441 : Blo 151794 386441 := bstep (se 2 (by rfl) ⟨144915, by rfl⟩ : syracuseStep 386441 = 289831) B289831
theorem B386491 : Blo 151794 386491 := bstep (se 1 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 386491 = 579737) B579737
theorem B1238561 : Blo 151794 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B386795 : Blo 151794 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B1173689 : Blo 151794 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B1566985 : Blo 151794 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B551279 : Blo 151794 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B780839 : Blo 151794 780839 := bstep (se 1 (by rfl) ⟨585629, by rfl⟩ : syracuseStep 780839 = 1171259) B1171259
theorem B518831 : Blo 151794 518831 := bstep (se 1 (by rfl) ⟨389123, by rfl⟩ : syracuseStep 518831 = 778247) B778247
theorem B387767 : Blo 151794 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B1469117 : Blo 151794 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B256999 : Blo 151794 256999 := bstep (se 1 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 256999 = 385499) B385499
theorem B519155 : Blo 151794 519155 := bstep (se 1 (by rfl) ⟨389366, by rfl⟩ : syracuseStep 519155 = 778733) B778733
theorem B650429 : Blo 151794 650429 := bstep (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) B243911
theorem B519695 : Blo 151794 519695 := bstep (se 1 (by rfl) ⟨389771, by rfl⟩ : syracuseStep 519695 = 779543) B779543
theorem B192223 : Blo 151794 192223 := bstep (se 1 (by rfl) ⟨144167, by rfl⟩ : syracuseStep 192223 = 288335) B288335
theorem B290567 : Blo 151794 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B388871 : Blo 151794 388871 := bstep (se 1 (by rfl) ⟨291653, by rfl⟩ : syracuseStep 388871 = 583307) B583307
theorem B388921 : Blo 151794 388921 := bstep (se 2 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 388921 = 291691) B291691
theorem B880541 : Blo 151794 880541 := bstep (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) B330203
theorem B585737 : Blo 151794 585737 := bstep (se 2 (by rfl) ⟨219651, by rfl⟩ : syracuseStep 585737 = 439303) B439303
theorem B389225 : Blo 151794 389225 := bstep (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) B291919
theorem B651847 : Blo 151794 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B520775 : Blo 151794 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B389711 : Blo 151794 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B782945 : Blo 151794 782945 := bstep (se 2 (by rfl) ⟨293604, by rfl⟩ : syracuseStep 782945 = 587209) B587209
theorem B586727 : Blo 151794 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B521207 : Blo 151794 521207 := bstep (se 1 (by rfl) ⟨390905, by rfl⟩ : syracuseStep 521207 = 781811) B781811
theorem B652445 : Blo 151794 652445 := bstep (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) B244667
theorem B390359 : Blo 151794 390359 := bstep (se 1 (by rfl) ⟨292769, by rfl⟩ : syracuseStep 390359 = 585539) B585539
theorem B783593 : Blo 151794 783593 := bstep (se 2 (by rfl) ⟨293847, by rfl⟩ : syracuseStep 783593 = 587695) B587695
theorem B947495 : Blo 151794 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B783755 : Blo 151794 783755 := bstep (se 1 (by rfl) ⟨587816, by rfl⟩ : syracuseStep 783755 = 1175633) B1175633
theorem B1668545 : Blo 151794 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B259679 : Blo 151794 259679 := bstep (se 1 (by rfl) ⟨194759, by rfl⟩ : syracuseStep 259679 = 389519) B389519
theorem B259895 : Blo 151794 259895 := bstep (se 1 (by rfl) ⟨194921, by rfl⟩ : syracuseStep 259895 = 389843) B389843
theorem B292663 : Blo 151794 292663 := bstep (se 1 (by rfl) ⟨219497, by rfl⟩ : syracuseStep 292663 = 438995) B438995
theorem B522071 : Blo 151794 522071 := bstep (se 1 (by rfl) ⟨391553, by rfl⟩ : syracuseStep 522071 = 783107) B783107
theorem B2357495 : Blo 151794 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1308919 : Blo 151794 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B1472843 : Blo 151794 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B391675 : Blo 151794 391675 := bstep (se 1 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 391675 = 587513) B587513
theorem B227903 : Blo 151794 227903 := bstep (se 1 (by rfl) ⟨170927, by rfl⟩ : syracuseStep 227903 = 341855) B341855
theorem B260671 : Blo 151794 260671 := bstep (se 1 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 260671 = 391007) B391007
theorem B293483 : Blo 151794 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B391787 : Blo 151794 391787 := bstep (se 1 (by rfl) ⟨293840, by rfl⟩ : syracuseStep 391787 = 587681) B587681
theorem B195247 : Blo 151794 195247 := bstep (se 1 (by rfl) ⟨146435, by rfl⟩ : syracuseStep 195247 = 292871) B292871
theorem B228023 : Blo 151794 228023 := bstep (se 1 (by rfl) ⟨171017, by rfl⟩ : syracuseStep 228023 = 342035) B342035
theorem B3308363 : Blo 151794 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B523151 : Blo 151794 523151 := bstep (se 1 (by rfl) ⟨392363, by rfl⟩ : syracuseStep 523151 = 784727) B784727
theorem B228251 : Blo 151794 228251 := bstep (se 1 (by rfl) ⟨171188, by rfl⟩ : syracuseStep 228251 = 342377) B342377
theorem B293863 : Blo 151794 293863 := bstep (se 1 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 293863 = 440795) B440795
theorem B982205 : Blo 151794 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B326855 : Blo 151794 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B261353 : Blo 151794 261353 := bstep (se 2 (by rfl) ⟨98007, by rfl⟩ : syracuseStep 261353 = 196015) B196015
theorem B294121 : Blo 151794 294121 := bstep (se 2 (by rfl) ⟨110295, by rfl⟩ : syracuseStep 294121 = 220591) B220591
theorem B392435 : Blo 151794 392435 := bstep (se 1 (by rfl) ⟨294326, by rfl⟩ : syracuseStep 392435 = 588653) B588653
theorem B261407 : Blo 151794 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B228647 : Blo 151794 228647 := bstep (se 1 (by rfl) ⟨171485, by rfl⟩ : syracuseStep 228647 = 342971) B342971
theorem B589153 : Blo 151794 589153 := bstep (se 2 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 589153 = 441865) B441865
theorem B228731 : Blo 151794 228731 := bstep (se 1 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 228731 = 343097) B343097
theorem B392647 : Blo 151794 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B228857 : Blo 151794 228857 := bstep (se 2 (by rfl) ⟨85821, by rfl⟩ : syracuseStep 228857 = 171643) B171643
theorem B228959 : Blo 151794 228959 := bstep (se 1 (by rfl) ⟨171719, by rfl⟩ : syracuseStep 228959 = 343439) B343439
theorem B589427 : Blo 151794 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B229175 : Blo 151794 229175 := bstep (se 1 (by rfl) ⟨171881, by rfl⟩ : syracuseStep 229175 = 343763) B343763
theorem B589625 : Blo 151794 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B1179521 : Blo 151794 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B229595 : Blo 151794 229595 := bstep (se 1 (by rfl) ⟨172196, by rfl⟩ : syracuseStep 229595 = 344393) B344393
theorem B229607 : Blo 151794 229607 := bstep (se 1 (by rfl) ⟨172205, by rfl⟩ : syracuseStep 229607 = 344411) B344411
theorem B524519 : Blo 151794 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B393569 : Blo 151794 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B524663 : Blo 151794 524663 := bstep (se 1 (by rfl) ⟨393497, by rfl⟩ : syracuseStep 524663 = 786995) B786995
theorem B229769 : Blo 151794 229769 := bstep (se 2 (by rfl) ⟨86163, by rfl⟩ : syracuseStep 229769 = 172327) B172327
theorem B885167 : Blo 151794 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B229865 : Blo 151794 229865 := bstep (se 2 (by rfl) ⟨86199, by rfl⟩ : syracuseStep 229865 = 172399) B172399
theorem B262649 : Blo 151794 262649 := bstep (se 2 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 262649 = 196987) B196987
theorem B590399 : Blo 151794 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B229991 : Blo 151794 229991 := bstep (se 1 (by rfl) ⟨172493, by rfl⟩ : syracuseStep 229991 = 344987) B344987
theorem B1049195 : Blo 151794 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B230123 : Blo 151794 230123 := bstep (se 1 (by rfl) ⟨172592, by rfl⟩ : syracuseStep 230123 = 345185) B345185
theorem B230153 : Blo 151794 230153 := bstep (se 2 (by rfl) ⟨86307, by rfl⟩ : syracuseStep 230153 = 172615) B172615
theorem B328495 : Blo 151794 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B230255 : Blo 151794 230255 := bstep (se 1 (by rfl) ⟨172691, by rfl⟩ : syracuseStep 230255 = 345383) B345383
theorem B787319 : Blo 151794 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B230507 : Blo 151794 230507 := bstep (se 1 (by rfl) ⟨172880, by rfl⟩ : syracuseStep 230507 = 345761) B345761
theorem B230747 : Blo 151794 230747 := bstep (se 1 (by rfl) ⟨173060, by rfl⟩ : syracuseStep 230747 = 346121) B346121
theorem B525743 : Blo 151794 525743 := bstep (se 1 (by rfl) ⟨394307, by rfl⟩ : syracuseStep 525743 = 788615) B788615
theorem B231023 : Blo 151794 231023 := bstep (se 1 (by rfl) ⟨173267, by rfl⟩ : syracuseStep 231023 = 346535) B346535
theorem B788129 : Blo 151794 788129 := bstep (se 2 (by rfl) ⟨295548, by rfl⟩ : syracuseStep 788129 = 591097) B591097
theorem B329383 : Blo 151794 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B231095 : Blo 151794 231095 := bstep (se 1 (by rfl) ⟨173321, by rfl⟩ : syracuseStep 231095 = 346643) B346643
theorem B231131 : Blo 151794 231131 := bstep (se 1 (by rfl) ⟨173348, by rfl⟩ : syracuseStep 231131 = 346697) B346697
theorem B329503 : Blo 151794 329503 := bstep (se 1 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 329503 = 494255) B494255
theorem B231305 : Blo 151794 231305 := bstep (se 2 (by rfl) ⟨86739, by rfl⟩ : syracuseStep 231305 = 173479) B173479
theorem B231407 : Blo 151794 231407 := bstep (se 1 (by rfl) ⟨173555, by rfl⟩ : syracuseStep 231407 = 347111) B347111
theorem B559295 : Blo 151794 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B526571 : Blo 151794 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B231659 : Blo 151794 231659 := bstep (se 1 (by rfl) ⟨173744, by rfl⟩ : syracuseStep 231659 = 347489) B347489
theorem B231719 : Blo 151794 231719 := bstep (se 1 (by rfl) ⟨173789, by rfl⟩ : syracuseStep 231719 = 347579) B347579
theorem B395567 : Blo 151794 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B231803 : Blo 151794 231803 := bstep (se 1 (by rfl) ⟨173852, by rfl⟩ : syracuseStep 231803 = 347705) B347705
theorem B232073 : Blo 151794 232073 := bstep (se 2 (by rfl) ⟨87027, by rfl⟩ : syracuseStep 232073 = 174055) B174055
theorem B821947 : Blo 151794 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B232247 : Blo 151794 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B232283 : Blo 151794 232283 := bstep (se 1 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 232283 = 348425) B348425
theorem B232427 : Blo 151794 232427 := bstep (se 1 (by rfl) ⟨174320, by rfl⟩ : syracuseStep 232427 = 348641) B348641
theorem B494639 : Blo 151794 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B232631 : Blo 151794 232631 := bstep (se 1 (by rfl) ⟨174473, by rfl⟩ : syracuseStep 232631 = 348947) B348947
theorem B265583 : Blo 151794 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B232871 : Blo 151794 232871 := bstep (se 1 (by rfl) ⟨174653, by rfl⟩ : syracuseStep 232871 = 349307) B349307
theorem B265639 : Blo 151794 265639 := bstep (se 1 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 265639 = 398459) B398459
theorem B2526653 : Blo 151794 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B232955 : Blo 151794 232955 := bstep (se 1 (by rfl) ⟨174716, by rfl⟩ : syracuseStep 232955 = 349433) B349433
theorem B233051 : Blo 151794 233051 := bstep (se 1 (by rfl) ⟨174788, by rfl⟩ : syracuseStep 233051 = 349577) B349577
theorem B528047 : Blo 151794 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B233135 : Blo 151794 233135 := bstep (se 1 (by rfl) ⟨174851, by rfl⟩ : syracuseStep 233135 = 349703) B349703
theorem B233255 : Blo 151794 233255 := bstep (se 1 (by rfl) ⟨174941, by rfl⟩ : syracuseStep 233255 = 349883) B349883
theorem B233339 : Blo 151794 233339 := bstep (se 1 (by rfl) ⟨175004, by rfl⟩ : syracuseStep 233339 = 350009) B350009
theorem B659927 : Blo 151794 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B2232791 : Blo 151794 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B35493065 : Blo 151794 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B4199633 : Blo 151794 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B366049 : Blo 151794 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B530729 : Blo 151794 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B8395109 : Blo 151794 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B825707 : Blo 151794 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B498329 : Blo 151794 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B367519 : Blo 151794 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B924641 : Blo 151794 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B2628773 : Blo 151794 2628773 := bstep (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) B492895
theorem B1056203 : Blo 151794 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B433619 : Blo 151794 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B1745225 : Blo 151794 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B434963 : Blo 151794 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B205735 : Blo 151794 205735 := bstep (se 1 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 205735 = 308603) B308603
theorem B271355 : Blo 151794 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B173119 : Blo 151794 173119 := bstep (se 1 (by rfl) ⟨129839, by rfl⟩ : syracuseStep 173119 = 259679) B259679
theorem B173263 : Blo 151794 173263 := bstep (se 1 (by rfl) ⟨129947, by rfl⟩ : syracuseStep 173263 = 259895) B259895
theorem B664969 : Blo 151794 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B2205575 : Blo 151794 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B174235 : Blo 151794 174235 := bstep (se 1 (by rfl) ⟨130676, by rfl⟩ : syracuseStep 174235 = 261353) B261353
theorem B174271 : Blo 151794 174271 := bstep (se 1 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 174271 = 261407) B261407
theorem B1648991 : Blo 151794 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B1321667 : Blo 151794 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B207919 : Blo 151794 207919 := bstep (se 1 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 207919 = 311879) B311879
theorem B437491 : Blo 151794 437491 := bstep (se 1 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 437491 = 656237) B656237
theorem B1256791 : Blo 151794 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B470519 : Blo 151794 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B470591 : Blo 151794 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B699977 : Blo 151794 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B176359 : Blo 151794 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B1782071 : Blo 151794 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B4208165 : Blo 151794 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B341675 : Blo 151794 341675 := bstep (se 1 (by rfl) ⟨256256, by rfl⟩ : syracuseStep 341675 = 512513) B512513
theorem B734923 : Blo 151794 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B341999 : Blo 151794 341999 := bstep (se 1 (by rfl) ⟨256499, by rfl⟩ : syracuseStep 341999 = 512999) B512999
theorem B276635 : Blo 151794 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B342215 : Blo 151794 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B7649579 : Blo 151794 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B342395 : Blo 151794 342395 := bstep (se 1 (by rfl) ⟨256796, by rfl⟩ : syracuseStep 342395 = 513593) B513593
theorem B3291677 : Blo 151794 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B342665 : Blo 151794 342665 := bstep (se 2 (by rfl) ⟨128499, by rfl⟩ : syracuseStep 342665 = 256999) B256999
theorem B5389145 : Blo 151794 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B343223 : Blo 151794 343223 := bstep (se 1 (by rfl) ⟨257417, by rfl⟩ : syracuseStep 343223 = 514835) B514835
theorem B343799 : Blo 151794 343799 := bstep (se 1 (by rfl) ⟨257849, by rfl⟩ : syracuseStep 343799 = 515699) B515699
theorem B60702605 : Blo 151794 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B343979 : Blo 151794 343979 := bstep (se 1 (by rfl) ⟨257984, by rfl⟩ : syracuseStep 343979 = 515969) B515969
theorem B3162037 : Blo 151794 3162037 := bstep (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) B296441
theorem B1720439 : Blo 151794 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B180535 : Blo 151794 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B344519 : Blo 151794 344519 := bstep (se 1 (by rfl) ⟨258389, by rfl⟩ : syracuseStep 344519 = 516779) B516779
theorem B1065593 : Blo 151794 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B770795 : Blo 151794 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B869129 : Blo 151794 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B344879 : Blo 151794 344879 := bstep (se 1 (by rfl) ⟨258659, by rfl⟩ : syracuseStep 344879 = 517319) B517319
theorem B312943 : Blo 151794 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B345887 : Blo 151794 345887 := bstep (se 1 (by rfl) ⟨259415, by rfl⟩ : syracuseStep 345887 = 518831) B518831
theorem B2606903 : Blo 151794 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B346103 : Blo 151794 346103 := bstep (se 1 (by rfl) ⟨259577, by rfl⟩ : syracuseStep 346103 = 519155) B519155
theorem B1755431 : Blo 151794 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B346463 : Blo 151794 346463 := bstep (se 1 (by rfl) ⟨259847, by rfl⟩ : syracuseStep 346463 = 519695) B519695
theorem B772577 : Blo 151794 772577 := bstep (se 2 (by rfl) ⟨289716, by rfl⟩ : syracuseStep 772577 = 579433) B579433
theorem B10242541 : Blo 151794 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B347183 : Blo 151794 347183 := bstep (se 1 (by rfl) ⟨260387, by rfl⟩ : syracuseStep 347183 = 520775) B520775
theorem B248903 : Blo 151794 248903 := bstep (se 1 (by rfl) ⟨186677, by rfl⟩ : syracuseStep 248903 = 373355) B373355
theorem B347471 : Blo 151794 347471 := bstep (se 1 (by rfl) ⟨260603, by rfl⟩ : syracuseStep 347471 = 521207) B521207
theorem B347561 : Blo 151794 347561 := bstep (se 2 (by rfl) ⟨130335, by rfl⟩ : syracuseStep 347561 = 260671) B260671
theorem B413309 : Blo 151794 413309 := bstep (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) B154991
theorem B348047 : Blo 151794 348047 := bstep (se 1 (by rfl) ⟨261035, by rfl⟩ : syracuseStep 348047 = 522071) B522071
theorem B151935 : Blo 151794 151935 := bstep (se 1 (by rfl) ⟨113951, by rfl⟩ : syracuseStep 151935 = 227903) B227903
theorem B152015 : Blo 151794 152015 := bstep (se 1 (by rfl) ⟨114011, by rfl⟩ : syracuseStep 152015 = 228023) B228023
theorem B348767 : Blo 151794 348767 := bstep (se 1 (by rfl) ⟨261575, by rfl⟩ : syracuseStep 348767 = 523151) B523151
theorem B152167 : Blo 151794 152167 := bstep (se 1 (by rfl) ⟨114125, by rfl⟩ : syracuseStep 152167 = 228251) B228251
theorem B774845 : Blo 151794 774845 := bstep (se 3 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 774845 = 290567) B290567
theorem B217903 : Blo 151794 217903 := bstep (se 1 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 217903 = 326855) B326855
theorem B24171317 : Blo 151794 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B152431 : Blo 151794 152431 := bstep (se 1 (by rfl) ⟨114323, by rfl⟩ : syracuseStep 152431 = 228647) B228647
theorem B152487 : Blo 151794 152487 := bstep (se 1 (by rfl) ⟨114365, by rfl⟩ : syracuseStep 152487 = 228731) B228731
theorem B152571 : Blo 151794 152571 := bstep (se 1 (by rfl) ⟨114428, by rfl⟩ : syracuseStep 152571 = 228857) B228857
theorem B1561609 : Blo 151794 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B447527 : Blo 151794 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B152639 : Blo 151794 152639 := bstep (se 1 (by rfl) ⟨114479, by rfl⟩ : syracuseStep 152639 = 228959) B228959
theorem B578735 : Blo 151794 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B152783 : Blo 151794 152783 := bstep (se 1 (by rfl) ⟨114587, by rfl⟩ : syracuseStep 152783 = 229175) B229175
theorem B513377 : Blo 151794 513377 := bstep (se 2 (by rfl) ⟨192516, by rfl⟩ : syracuseStep 513377 = 385033) B385033
theorem B152987 : Blo 151794 152987 := bstep (se 1 (by rfl) ⟨114740, by rfl⟩ : syracuseStep 152987 = 229481) B229481
theorem B185755 : Blo 151794 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B349595 : Blo 151794 349595 := bstep (se 1 (by rfl) ⟨262196, by rfl⟩ : syracuseStep 349595 = 524393) B524393
theorem B1594811 : Blo 151794 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B218695 : Blo 151794 218695 := bstep (se 1 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 218695 = 328043) B328043
theorem B153199 : Blo 151794 153199 := bstep (se 1 (by rfl) ⟨114899, by rfl⟩ : syracuseStep 153199 = 229799) B229799
theorem B153255 : Blo 151794 153255 := bstep (se 1 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 153255 = 229883) B229883
theorem B218791 : Blo 151794 218791 := bstep (se 1 (by rfl) ⟨164093, by rfl⟩ : syracuseStep 218791 = 328187) B328187
theorem B153339 : Blo 151794 153339 := bstep (se 1 (by rfl) ⟨115004, by rfl⟩ : syracuseStep 153339 = 230009) B230009
theorem B153375 : Blo 151794 153375 := bstep (se 1 (by rfl) ⟨115031, by rfl⟩ : syracuseStep 153375 = 230063) B230063
theorem B186143 : Blo 151794 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B153407 : Blo 151794 153407 := bstep (se 1 (by rfl) ⟨115055, by rfl⟩ : syracuseStep 153407 = 230111) B230111
theorem B350171 : Blo 151794 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B153583 : Blo 151794 153583 := bstep (se 1 (by rfl) ⟨115187, by rfl⟩ : syracuseStep 153583 = 230375) B230375
theorem B841711 : Blo 151794 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B350351 : Blo 151794 350351 := bstep (se 1 (by rfl) ⟨262763, by rfl⟩ : syracuseStep 350351 = 525527) B525527
theorem B153755 : Blo 151794 153755 := bstep (se 1 (by rfl) ⟨115316, by rfl⟩ : syracuseStep 153755 = 230633) B230633
theorem B350369 : Blo 151794 350369 := bstep (se 2 (by rfl) ⟨131388, by rfl⟩ : syracuseStep 350369 = 262777) B262777
theorem B153791 : Blo 151794 153791 := bstep (se 1 (by rfl) ⟨115343, by rfl⟩ : syracuseStep 153791 = 230687) B230687
theorem B350441 : Blo 151794 350441 := bstep (se 2 (by rfl) ⟨131415, by rfl⟩ : syracuseStep 350441 = 262831) B262831
theorem B153903 : Blo 151794 153903 := bstep (se 1 (by rfl) ⟨115427, by rfl⟩ : syracuseStep 153903 = 230855) B230855
theorem B481609 : Blo 151794 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B154139 : Blo 151794 154139 := bstep (se 1 (by rfl) ⟨115604, by rfl⟩ : syracuseStep 154139 = 231209) B231209
theorem B154143 : Blo 151794 154143 := bstep (se 1 (by rfl) ⟨115607, by rfl⟩ : syracuseStep 154143 = 231215) B231215
theorem B1301129 : Blo 151794 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B6282035 : Blo 151794 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B416603 : Blo 151794 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B154459 : Blo 151794 154459 := bstep (se 1 (by rfl) ⟨115844, by rfl⟩ : syracuseStep 154459 = 231689) B231689
theorem B154527 : Blo 151794 154527 := bstep (se 1 (by rfl) ⟨115895, by rfl⟩ : syracuseStep 154527 = 231791) B231791
theorem B154671 : Blo 151794 154671 := bstep (se 1 (by rfl) ⟨116003, by rfl⟩ : syracuseStep 154671 = 232007) B232007
theorem B2219075 : Blo 151794 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B154695 : Blo 151794 154695 := bstep (se 1 (by rfl) ⟨116021, by rfl⟩ : syracuseStep 154695 = 232043) B232043
theorem B154847 : Blo 151794 154847 := bstep (se 1 (by rfl) ⟨116135, by rfl⟩ : syracuseStep 154847 = 232271) B232271
theorem B515321 : Blo 151794 515321 := bstep (se 2 (by rfl) ⟨193245, by rfl⟩ : syracuseStep 515321 = 386491) B386491
theorem B155111 : Blo 151794 155111 := bstep (se 1 (by rfl) ⟨116333, by rfl⟩ : syracuseStep 155111 = 232667) B232667
theorem B515591 : Blo 151794 515591 := bstep (se 1 (by rfl) ⟨386693, by rfl⟩ : syracuseStep 515591 = 773387) B773387
theorem B155227 : Blo 151794 155227 := bstep (se 1 (by rfl) ⟨116420, by rfl⟩ : syracuseStep 155227 = 232841) B232841
theorem B3989087 : Blo 151794 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B581363 : Blo 151794 581363 := bstep (se 1 (by rfl) ⟨436022, by rfl⟩ : syracuseStep 581363 = 872045) B872045
theorem B155463 : Blo 151794 155463 := bstep (se 1 (by rfl) ⟨116597, by rfl⟩ : syracuseStep 155463 = 233195) B233195
theorem B155615 : Blo 151794 155615 := bstep (se 1 (by rfl) ⟨116711, by rfl⟩ : syracuseStep 155615 = 233423) B233423
theorem B2089313 : Blo 151794 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B1073533 : Blo 151794 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B221647 : Blo 151794 221647 := bstep (se 1 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 221647 = 332471) B332471
theorem B516671 : Blo 151794 516671 := bstep (se 1 (by rfl) ⟨387503, by rfl⟩ : syracuseStep 516671 = 775007) B775007
theorem B3957923 : Blo 151794 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1402217 : Blo 151794 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B648719 : Blo 151794 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B517967 : Blo 151794 517967 := bstep (se 1 (by rfl) ⟨388475, by rfl⟩ : syracuseStep 517967 = 776951) B776951
theorem B583625 : Blo 151794 583625 := bstep (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) B437719
theorem B518291 : Blo 151794 518291 := bstep (se 1 (by rfl) ⟨388718, by rfl⟩ : syracuseStep 518291 = 777437) B777437
theorem B289003 : Blo 151794 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B256297 : Blo 151794 256297 := bstep (se 2 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 256297 = 192223) B192223
theorem B3697001 : Blo 151794 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B518561 : Blo 151794 518561 := bstep (se 2 (by rfl) ⟨194460, by rfl⟩ : syracuseStep 518561 = 388921) B388921
theorem B289307 : Blo 151794 289307 := bstep (se 1 (by rfl) ⟨216980, by rfl⟩ : syracuseStep 289307 = 433961) B433961
theorem B584263 : Blo 151794 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B617593 : Blo 151794 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B257627 : Blo 151794 257627 := bstep (se 1 (by rfl) ⟨193220, by rfl⟩ : syracuseStep 257627 = 386441) B386441
theorem B257863 : Blo 151794 257863 := bstep (se 1 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 257863 = 386795) B386795
theorem B782459 : Blo 151794 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B979229 : Blo 151794 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B782621 : Blo 151794 782621 := bstep (se 3 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 782621 = 293483) B293483
theorem B520559 : Blo 151794 520559 := bstep (se 1 (by rfl) ⟨390419, by rfl⟩ : syracuseStep 520559 = 780839) B780839
theorem B258511 : Blo 151794 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B979411 : Blo 151794 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B7435253 : Blo 151794 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B390217 : Blo 151794 390217 := bstep (se 2 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 390217 = 292663) B292663
theorem B259247 : Blo 151794 259247 := bstep (se 1 (by rfl) ⟨194435, by rfl⟩ : syracuseStep 259247 = 388871) B388871
theorem B587027 : Blo 151794 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B292187 : Blo 151794 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B390491 : Blo 151794 390491 := bstep (se 1 (by rfl) ⟨292868, by rfl⟩ : syracuseStep 390491 = 585737) B585737
theorem B259483 : Blo 151794 259483 := bstep (se 1 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 259483 = 389225) B389225
theorem B226999 : Blo 151794 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B259807 : Blo 151794 259807 := bstep (se 1 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 259807 = 389711) B389711
theorem B521963 : Blo 151794 521963 := bstep (se 1 (by rfl) ⟨391472, by rfl⟩ : syracuseStep 521963 = 782945) B782945
theorem B3962843 : Blo 151794 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B391151 : Blo 151794 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B522233 : Blo 151794 522233 := bstep (se 2 (by rfl) ⟨195837, by rfl⟩ : syracuseStep 522233 = 391675) B391675
theorem B260239 : Blo 151794 260239 := bstep (se 1 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 260239 = 390359) B390359
theorem B522395 : Blo 151794 522395 := bstep (se 1 (by rfl) ⟨391796, by rfl⟩ : syracuseStep 522395 = 783593) B783593
theorem B260329 : Blo 151794 260329 := bstep (se 2 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 260329 = 195247) B195247
theorem B522503 : Blo 151794 522503 := bstep (se 1 (by rfl) ⟨391877, by rfl⟩ : syracuseStep 522503 = 783755) B783755
theorem B1112363 : Blo 151794 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B555373 : Blo 151794 555373 := bstep (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) B208265
theorem B227867 : Blo 151794 227867 := bstep (se 1 (by rfl) ⟨170900, by rfl⟩ : syracuseStep 227867 = 341801) B341801
theorem B227945 : Blo 151794 227945 := bstep (se 2 (by rfl) ⟨85479, by rfl⟩ : syracuseStep 227945 = 170959) B170959
theorem B391817 : Blo 151794 391817 := bstep (se 2 (by rfl) ⟨146931, by rfl⟩ : syracuseStep 391817 = 293863) B293863
theorem B1571663 : Blo 151794 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B981895 : Blo 151794 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B392161 : Blo 151794 392161 := bstep (se 2 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 392161 = 294121) B294121
theorem B261191 : Blo 151794 261191 := bstep (se 1 (by rfl) ⟨195893, by rfl⟩ : syracuseStep 261191 = 391787) B391787
theorem B228473 : Blo 151794 228473 := bstep (se 2 (by rfl) ⟨85677, by rfl⟩ : syracuseStep 228473 = 171355) B171355
theorem B785537 : Blo 151794 785537 := bstep (se 2 (by rfl) ⟨294576, by rfl⟩ : syracuseStep 785537 = 589153) B589153
theorem B228575 : Blo 151794 228575 := bstep (se 1 (by rfl) ⟨171431, by rfl⟩ : syracuseStep 228575 = 342863) B342863
theorem B228617 : Blo 151794 228617 := bstep (se 2 (by rfl) ⟨85731, by rfl⟩ : syracuseStep 228617 = 171463) B171463
theorem B523529 : Blo 151794 523529 := bstep (se 2 (by rfl) ⟨196323, by rfl⟩ : syracuseStep 523529 = 392647) B392647
theorem B228719 : Blo 151794 228719 := bstep (se 1 (by rfl) ⟨171539, by rfl⟩ : syracuseStep 228719 = 343079) B343079
theorem B654803 : Blo 151794 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B228839 : Blo 151794 228839 := bstep (se 1 (by rfl) ⟨171629, by rfl⟩ : syracuseStep 228839 = 343259) B343259
theorem B261623 : Blo 151794 261623 := bstep (se 1 (by rfl) ⟨196217, by rfl⟩ : syracuseStep 261623 = 392435) B392435
theorem B228971 : Blo 151794 228971 := bstep (se 1 (by rfl) ⟨171728, by rfl⟩ : syracuseStep 228971 = 343457) B343457
theorem B229097 : Blo 151794 229097 := bstep (se 2 (by rfl) ⟨85911, by rfl⟩ : syracuseStep 229097 = 171823) B171823
theorem B392951 : Blo 151794 392951 := bstep (se 1 (by rfl) ⟨294713, by rfl⟩ : syracuseStep 392951 = 589427) B589427
theorem B229241 : Blo 151794 229241 := bstep (se 2 (by rfl) ⟨85965, by rfl⟩ : syracuseStep 229241 = 171931) B171931
theorem B393083 : Blo 151794 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B786347 : Blo 151794 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B229343 : Blo 151794 229343 := bstep (se 1 (by rfl) ⟨172007, by rfl⟩ : syracuseStep 229343 = 344015) B344015
theorem B1146959 : Blo 151794 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B262379 : Blo 151794 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B590111 : Blo 151794 590111 := bstep (se 1 (by rfl) ⟨442583, by rfl⟩ : syracuseStep 590111 = 885167) B885167
theorem B229679 : Blo 151794 229679 := bstep (se 1 (by rfl) ⟨172259, by rfl⟩ : syracuseStep 229679 = 344519) B344519
theorem B393599 : Blo 151794 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B229919 : Blo 151794 229919 := bstep (se 1 (by rfl) ⟨172439, by rfl⟩ : syracuseStep 229919 = 344879) B344879
theorem B524879 : Blo 151794 524879 := bstep (se 1 (by rfl) ⟨393659, by rfl⟩ : syracuseStep 524879 = 787319) B787319
theorem B295529 : Blo 151794 295529 := bstep (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) B221647
theorem B525419 : Blo 151794 525419 := bstep (se 1 (by rfl) ⟨394064, by rfl⟩ : syracuseStep 525419 = 788129) B788129
theorem B230591 : Blo 151794 230591 := bstep (se 1 (by rfl) ⟨172943, by rfl⟩ : syracuseStep 230591 = 345887) B345887
theorem B1737935 : Blo 151794 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B230735 : Blo 151794 230735 := bstep (se 1 (by rfl) ⟨173051, by rfl⟩ : syracuseStep 230735 = 346103) B346103
theorem B230825 : Blo 151794 230825 := bstep (se 2 (by rfl) ⟨86559, by rfl⟩ : syracuseStep 230825 = 173119) B173119
theorem B263711 : Blo 151794 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B230975 : Blo 151794 230975 := bstep (se 1 (by rfl) ⟨173231, by rfl⟩ : syracuseStep 230975 = 346463) B346463
theorem B231017 : Blo 151794 231017 := bstep (se 2 (by rfl) ⟨86631, by rfl⟩ : syracuseStep 231017 = 173263) B173263
theorem B886625 : Blo 151794 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B231455 : Blo 151794 231455 := bstep (se 1 (by rfl) ⟨173591, by rfl⟩ : syracuseStep 231455 = 347183) B347183
theorem B329759 : Blo 151794 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B165935 : Blo 151794 165935 := bstep (se 1 (by rfl) ⟨124451, by rfl⟩ : syracuseStep 165935 = 248903) B248903
theorem B231647 : Blo 151794 231647 := bstep (se 1 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 231647 = 347471) B347471
theorem B231707 : Blo 151794 231707 := bstep (se 1 (by rfl) ⟨173780, by rfl⟩ : syracuseStep 231707 = 347561) B347561
theorem B232031 : Blo 151794 232031 := bstep (se 1 (by rfl) ⟨174023, by rfl⟩ : syracuseStep 232031 = 348047) B348047
theorem B232313 : Blo 151794 232313 := bstep (se 2 (by rfl) ⟨87117, by rfl⟩ : syracuseStep 232313 = 174235) B174235
theorem B232361 : Blo 151794 232361 := bstep (se 2 (by rfl) ⟨87135, by rfl⟩ : syracuseStep 232361 = 174271) B174271
theorem B232511 : Blo 151794 232511 := bstep (se 1 (by rfl) ⟨174383, by rfl⟩ : syracuseStep 232511 = 348767) B348767
theorem B298351 : Blo 151794 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B23662043 : Blo 151794 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B233063 : Blo 151794 233063 := bstep (se 1 (by rfl) ⟨174797, by rfl⟩ : syracuseStep 233063 = 349595) B349595
theorem B233447 : Blo 151794 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B233567 : Blo 151794 233567 := bstep (se 1 (by rfl) ⟨175175, by rfl⟩ : syracuseStep 233567 = 350351) B350351
theorem B233579 : Blo 151794 233579 := bstep (se 1 (by rfl) ⟨175184, by rfl⟩ : syracuseStep 233579 = 350369) B350369
theorem B233627 : Blo 151794 233627 := bstep (se 1 (by rfl) ⟨175220, by rfl⟩ : syracuseStep 233627 = 350441) B350441
theorem B823457 : Blo 151794 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B332219 : Blo 151794 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B1675721 : Blo 151794 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B1479383 : Blo 151794 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B496381 : Blo 151794 496381 := bstep (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) B186143
theorem B2659391 : Blo 151794 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B235145 : Blo 151794 235145 := bstep (se 2 (by rfl) ⟨88179, by rfl⟩ : syracuseStep 235145 = 176359) B176359
theorem B432479 : Blo 151794 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B2464667 : Blo 151794 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B302665 : Blo 151794 302665 := bstep (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) B226999
theorem B466651 : Blo 151794 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B171751 : Blo 151794 171751 := bstep (se 1 (by rfl) ⟨128813, by rfl⟩ : syracuseStep 171751 = 257627) B257627
theorem B1122281 : Blo 151794 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B1188047 : Blo 151794 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B4956835 : Blo 151794 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B172831 : Blo 151794 172831 := bstep (se 1 (by rfl) ⟨129623, by rfl⟩ : syracuseStep 172831 = 259247) B259247
theorem B174127 : Blo 151794 174127 := bstep (se 1 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 174127 = 261191) B261191
theorem B436535 : Blo 151794 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B174415 : Blo 151794 174415 := bstep (se 1 (by rfl) ⟨130811, by rfl⟩ : syracuseStep 174415 = 261623) B261623
theorem B2894453 : Blo 151794 2894453 := bstep (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) B271355
theorem B175099 : Blo 151794 175099 := bstep (se 1 (by rfl) ⟨131324, by rfl⟩ : syracuseStep 175099 = 262649) B262649
theorem B699463 : Blo 151794 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B240713 : Blo 151794 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B437993 : Blo 151794 437993 := bstep (se 2 (by rfl) ⟨164247, by rfl⟩ : syracuseStep 437993 = 328495) B328495
theorem B274313 : Blo 151794 274313 := bstep (se 2 (by rfl) ⟨102867, by rfl⟩ : syracuseStep 274313 = 205735) B205735
theorem B372863 : Blo 151794 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B2568581 : Blo 151794 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B439177 : Blo 151794 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B1684435 : Blo 151794 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B439337 : Blo 151794 439337 := bstep (se 2 (by rfl) ⟨164751, by rfl⟩ : syracuseStep 439337 = 329503) B329503
theorem B1488527 : Blo 151794 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B341729 : Blo 151794 341729 := bstep (se 2 (by rfl) ⟨128148, by rfl⟩ : syracuseStep 341729 = 256297) B256297
theorem B2799755 : Blo 151794 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B342251 : Blo 151794 342251 := bstep (se 1 (by rfl) ⟨256688, by rfl⟩ : syracuseStep 342251 = 513377) B513377
theorem B1095929 : Blo 151794 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B1063207 : Blo 151794 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B277225 : Blo 151794 277225 := bstep (se 2 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 277225 = 207919) B207919
theorem B867419 : Blo 151794 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B1752515 : Blo 151794 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B343547 : Blo 151794 343547 := bstep (se 1 (by rfl) ⟨257660, by rfl⟩ : syracuseStep 343547 = 515321) B515321
theorem B704135 : Blo 151794 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B343727 : Blo 151794 343727 := bstep (se 1 (by rfl) ⟨257795, by rfl⟩ : syracuseStep 343727 = 515591) B515591
theorem B343817 : Blo 151794 343817 := bstep (se 2 (by rfl) ⟨128931, by rfl⟩ : syracuseStep 343817 = 257863) B257863
theorem B1163483 : Blo 151794 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B1392875 : Blo 151794 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B344447 : Blo 151794 344447 := bstep (se 1 (by rfl) ⟨258335, by rfl⟩ : syracuseStep 344447 = 516671) B516671
theorem B737693 : Blo 151794 737693 := bstep (se 3 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 737693 = 276635) B276635
theorem B344681 : Blo 151794 344681 := bstep (se 2 (by rfl) ⟨129255, by rfl⟩ : syracuseStep 344681 = 258511) B258511
theorem B2638615 : Blo 151794 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B934811 : Blo 151794 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B345311 : Blo 151794 345311 := bstep (se 1 (by rfl) ⟨258983, by rfl⟩ : syracuseStep 345311 = 517967) B517967
theorem B2082145 : Blo 151794 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B345527 : Blo 151794 345527 := bstep (se 1 (by rfl) ⟨259145, by rfl⟩ : syracuseStep 345527 = 518291) B518291
theorem B1099327 : Blo 151794 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B345707 : Blo 151794 345707 := bstep (se 1 (by rfl) ⟨259280, by rfl⟩ : syracuseStep 345707 = 518561) B518561
theorem B345977 : Blo 151794 345977 := bstep (se 2 (by rfl) ⟨129741, by rfl⟩ : syracuseStep 345977 = 259483) B259483
theorem B247673 : Blo 151794 247673 := bstep (se 2 (by rfl) ⟨92877, by rfl⟩ : syracuseStep 247673 = 185755) B185755
theorem B346409 : Blo 151794 346409 := bstep (se 2 (by rfl) ⟨129903, by rfl⟩ : syracuseStep 346409 = 259807) B259807
theorem B313679 : Blo 151794 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B313727 : Blo 151794 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B1952261 : Blo 151794 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B346985 : Blo 151794 346985 := bstep (se 2 (by rfl) ⟨130119, by rfl⟩ : syracuseStep 346985 = 260239) B260239
theorem B347039 : Blo 151794 347039 := bstep (se 1 (by rfl) ⟨260279, by rfl⟩ : syracuseStep 347039 = 520559) B520559
theorem B347105 : Blo 151794 347105 := bstep (se 2 (by rfl) ⟨130164, by rfl⟩ : syracuseStep 347105 = 260329) B260329
theorem B740497 : Blo 151794 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B1166885 : Blo 151794 1166885 := bstep (se 4 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 1166885 = 218791) B218791
theorem B708221 : Blo 151794 708221 := bstep (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) B265583
theorem B2805443 : Blo 151794 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B347975 : Blo 151794 347975 := bstep (se 1 (by rfl) ⟨260981, by rfl⟩ : syracuseStep 347975 = 521963) B521963
theorem B2641895 : Blo 151794 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B348155 : Blo 151794 348155 := bstep (se 1 (by rfl) ⟨261116, by rfl⟩ : syracuseStep 348155 = 522233) B522233
theorem B348263 : Blo 151794 348263 := bstep (se 1 (by rfl) ⟨261197, by rfl⟩ : syracuseStep 348263 = 522395) B522395
theorem B348335 : Blo 151794 348335 := bstep (se 1 (by rfl) ⟨261251, by rfl⟩ : syracuseStep 348335 = 522503) B522503
theorem B741575 : Blo 151794 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B5099719 : Blo 151794 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1102157 : Blo 151794 1102157 := bstep (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) B413309
theorem B151911 : Blo 151794 151911 := bstep (se 1 (by rfl) ⟨113933, by rfl⟩ : syracuseStep 151911 = 227867) B227867
theorem B151963 : Blo 151794 151963 := bstep (se 1 (by rfl) ⟨113972, by rfl⟩ : syracuseStep 151963 = 227945) B227945
theorem B3592763 : Blo 151794 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B152315 : Blo 151794 152315 := bstep (se 1 (by rfl) ⟨114236, by rfl⟩ : syracuseStep 152315 = 228473) B228473
theorem B152383 : Blo 151794 152383 := bstep (se 1 (by rfl) ⟨114287, by rfl⟩ : syracuseStep 152383 = 228575) B228575
theorem B152411 : Blo 151794 152411 := bstep (se 1 (by rfl) ⟨114308, by rfl⟩ : syracuseStep 152411 = 228617) B228617
theorem B349019 : Blo 151794 349019 := bstep (se 1 (by rfl) ⟨261764, by rfl⟩ : syracuseStep 349019 = 523529) B523529
theorem B152479 : Blo 151794 152479 := bstep (se 1 (by rfl) ⟨114359, by rfl⟩ : syracuseStep 152479 = 228719) B228719
theorem B152559 : Blo 151794 152559 := bstep (se 1 (by rfl) ⟨114419, by rfl⟩ : syracuseStep 152559 = 228839) B228839
theorem B152647 : Blo 151794 152647 := bstep (se 1 (by rfl) ⟨114485, by rfl⟩ : syracuseStep 152647 = 228971) B228971
theorem B152731 : Blo 151794 152731 := bstep (se 1 (by rfl) ⟨114548, by rfl⟩ : syracuseStep 152731 = 229097) B229097
theorem B4216049 : Blo 151794 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B152827 : Blo 151794 152827 := bstep (se 1 (by rfl) ⟨114620, by rfl⟩ : syracuseStep 152827 = 229241) B229241
theorem B152895 : Blo 151794 152895 := bstep (se 1 (by rfl) ⟨114671, by rfl⟩ : syracuseStep 152895 = 229343) B229343
theorem B153063 : Blo 151794 153063 := bstep (se 1 (by rfl) ⟨114797, by rfl⟩ : syracuseStep 153063 = 229595) B229595
theorem B153071 : Blo 151794 153071 := bstep (se 1 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 153071 = 229607) B229607
theorem B349679 : Blo 151794 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B349775 : Blo 151794 349775 := bstep (se 1 (by rfl) ⟨262331, by rfl⟩ : syracuseStep 349775 = 524663) B524663
theorem B153179 : Blo 151794 153179 := bstep (se 1 (by rfl) ⟨114884, by rfl⟩ : syracuseStep 153179 = 229769) B229769
theorem B153243 : Blo 151794 153243 := bstep (se 1 (by rfl) ⟨114932, by rfl⟩ : syracuseStep 153243 = 229865) B229865
theorem B153327 : Blo 151794 153327 := bstep (se 1 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 153327 = 229991) B229991
theorem B513863 : Blo 151794 513863 := bstep (se 1 (by rfl) ⟨385397, by rfl⟩ : syracuseStep 513863 = 770795) B770795
theorem B153415 : Blo 151794 153415 := bstep (se 1 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 153415 = 230123) B230123
theorem B1431377 : Blo 151794 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B579419 : Blo 151794 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B153435 : Blo 151794 153435 := bstep (se 1 (by rfl) ⟨115076, by rfl⟩ : syracuseStep 153435 = 230153) B230153
theorem B153503 : Blo 151794 153503 := bstep (se 1 (by rfl) ⟨115127, by rfl⟩ : syracuseStep 153503 = 230255) B230255
theorem B153671 : Blo 151794 153671 := bstep (se 1 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 153671 = 230507) B230507
theorem B2611277 : Blo 151794 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B153831 : Blo 151794 153831 := bstep (se 1 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 153831 = 230747) B230747
theorem B350495 : Blo 151794 350495 := bstep (se 1 (by rfl) ⟨262871, by rfl⟩ : syracuseStep 350495 = 525743) B525743
theorem B154015 : Blo 151794 154015 := bstep (se 1 (by rfl) ⟨115511, by rfl⟩ : syracuseStep 154015 = 231023) B231023
theorem B154063 : Blo 151794 154063 := bstep (se 1 (by rfl) ⟨115547, by rfl⟩ : syracuseStep 154063 = 231095) B231095
theorem B154087 : Blo 151794 154087 := bstep (se 1 (by rfl) ⟨115565, by rfl⟩ : syracuseStep 154087 = 231131) B231131
theorem B1759805 : Blo 151794 1759805 := bstep (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) B659927
theorem B154203 : Blo 151794 154203 := bstep (se 1 (by rfl) ⟨115652, by rfl⟩ : syracuseStep 154203 = 231305) B231305
theorem B154271 : Blo 151794 154271 := bstep (se 1 (by rfl) ⟨115703, by rfl⟩ : syracuseStep 154271 = 231407) B231407
theorem B351047 : Blo 151794 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B154439 : Blo 151794 154439 := bstep (se 1 (by rfl) ⟨115829, by rfl⟩ : syracuseStep 154439 = 231659) B231659
theorem B1170287 : Blo 151794 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B154479 : Blo 151794 154479 := bstep (se 1 (by rfl) ⟨115859, by rfl⟩ : syracuseStep 154479 = 231719) B231719
theorem B154535 : Blo 151794 154535 := bstep (se 1 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 154535 = 231803) B231803
theorem B515051 : Blo 151794 515051 := bstep (se 1 (by rfl) ⟨386288, by rfl⟩ : syracuseStep 515051 = 772577) B772577
theorem B2841581 : Blo 151794 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B154715 : Blo 151794 154715 := bstep (se 1 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 154715 = 232073) B232073
theorem B154831 : Blo 151794 154831 := bstep (se 1 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 154831 = 232247) B232247
theorem B154855 : Blo 151794 154855 := bstep (se 1 (by rfl) ⟨116141, by rfl⟩ : syracuseStep 154855 = 232283) B232283
theorem B154951 : Blo 151794 154951 := bstep (se 1 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 154951 = 232427) B232427
theorem B155087 : Blo 151794 155087 := bstep (se 1 (by rfl) ⟨116315, by rfl⟩ : syracuseStep 155087 = 232631) B232631
theorem B417257 : Blo 151794 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B155247 : Blo 151794 155247 := bstep (se 1 (by rfl) ⟨116435, by rfl⟩ : syracuseStep 155247 = 232871) B232871
theorem B155303 : Blo 151794 155303 := bstep (se 1 (by rfl) ⟨116477, by rfl⟩ : syracuseStep 155303 = 232955) B232955
theorem B155367 : Blo 151794 155367 := bstep (se 1 (by rfl) ⟨116525, by rfl⟩ : syracuseStep 155367 = 233051) B233051
theorem B352031 : Blo 151794 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B155423 : Blo 151794 155423 := bstep (se 1 (by rfl) ⟨116567, by rfl⟩ : syracuseStep 155423 = 233135) B233135
theorem B155503 : Blo 151794 155503 := bstep (se 1 (by rfl) ⟨116627, by rfl⟩ : syracuseStep 155503 = 233255) B233255
theorem B155559 : Blo 151794 155559 := bstep (se 1 (by rfl) ⟨116669, by rfl⟩ : syracuseStep 155559 = 233339) B233339
theorem B385337 : Blo 151794 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B516563 : Blo 151794 516563 := bstep (se 1 (by rfl) ⟨387422, by rfl⟩ : syracuseStep 516563 = 774845) B774845
theorem B16114211 : Blo 151794 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B13656721 : Blo 151794 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B779017 : Blo 151794 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B385823 : Blo 151794 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B779165 : Blo 151794 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B353819 : Blo 151794 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B5596739 : Blo 151794 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B550471 : Blo 151794 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B583321 : Blo 151794 583321 := bstep (se 2 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 583321 = 437491) B437491
theorem B4188023 : Blo 151794 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B354185 : Blo 151794 354185 := bstep (se 2 (by rfl) ⟨132819, by rfl⟩ : syracuseStep 354185 = 265639) B265639
theorem B616427 : Blo 151794 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B289079 : Blo 151794 289079 := bstep (se 1 (by rfl) ⟨216809, by rfl⟩ : syracuseStep 289079 = 433619) B433619
theorem B387575 : Blo 151794 387575 := bstep (se 1 (by rfl) ⟨290681, by rfl⟩ : syracuseStep 387575 = 581363) B581363
theorem B289975 : Blo 151794 289975 := bstep (se 1 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 289975 = 434963) B434963
theorem B1305881 : Blo 151794 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B290537 : Blo 151794 290537 := bstep (se 2 (by rfl) ⟨108951, by rfl⟩ : syracuseStep 290537 = 217903) B217903
theorem B1470383 : Blo 151794 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B389083 : Blo 151794 389083 := bstep (se 1 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 389083 = 583625) B583625
theorem B520289 : Blo 151794 520289 := bstep (se 2 (by rfl) ⟨195108, by rfl⟩ : syracuseStep 520289 = 390217) B390217
theorem B192871 : Blo 151794 192871 := bstep (se 1 (by rfl) ⟨144653, by rfl⟩ : syracuseStep 192871 = 289307) B289307
theorem B881111 : Blo 151794 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B291593 : Blo 151794 291593 := bstep (se 2 (by rfl) ⟨109347, by rfl⟩ : syracuseStep 291593 = 218695) B218695
theorem B1110941 : Blo 151794 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B979897 : Blo 151794 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B521639 : Blo 151794 521639 := bstep (se 1 (by rfl) ⟨391229, by rfl⟩ : syracuseStep 521639 = 782459) B782459
theorem B521747 : Blo 151794 521747 := bstep (se 1 (by rfl) ⟨391310, by rfl⟩ : syracuseStep 521747 = 782621) B782621
theorem B391351 : Blo 151794 391351 := bstep (se 1 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 391351 = 587027) B587027
theorem B260327 : Blo 151794 260327 := bstep (se 1 (by rfl) ⟨195245, by rfl⟩ : syracuseStep 260327 = 390491) B390491
theorem B227783 : Blo 151794 227783 := bstep (se 1 (by rfl) ⟨170837, by rfl⟩ : syracuseStep 227783 = 341675) B341675
theorem B1309193 : Blo 151794 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B490025 : Blo 151794 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B522881 : Blo 151794 522881 := bstep (se 2 (by rfl) ⟨196080, by rfl⟩ : syracuseStep 522881 = 392161) B392161
theorem B227999 : Blo 151794 227999 := bstep (se 1 (by rfl) ⟨170999, by rfl⟩ : syracuseStep 227999 = 341999) B341999
theorem B260767 : Blo 151794 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B228143 : Blo 151794 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B228263 : Blo 151794 228263 := bstep (se 1 (by rfl) ⟨171197, by rfl⟩ : syracuseStep 228263 = 342395) B342395
theorem B2194451 : Blo 151794 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B228443 : Blo 151794 228443 := bstep (se 1 (by rfl) ⟨171332, by rfl⟩ : syracuseStep 228443 = 342665) B342665
theorem B261211 : Blo 151794 261211 := bstep (se 1 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 261211 = 391817) B391817
theorem B1047775 : Blo 151794 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B523691 : Blo 151794 523691 := bstep (se 1 (by rfl) ⟨392768, by rfl⟩ : syracuseStep 523691 = 785537) B785537
theorem B228815 : Blo 151794 228815 := bstep (se 1 (by rfl) ⟨171611, by rfl⟩ : syracuseStep 228815 = 343223) B343223
theorem B229199 : Blo 151794 229199 := bstep (se 1 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 229199 = 343799) B343799
theorem B261967 : Blo 151794 261967 := bstep (se 1 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 261967 = 392951) B392951
theorem B262055 : Blo 151794 262055 := bstep (se 1 (by rfl) ⟨196541, by rfl⟩ : syracuseStep 262055 = 393083) B393083
theorem B40468403 : Blo 151794 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B229319 : Blo 151794 229319 := bstep (se 1 (by rfl) ⟨171989, by rfl⟩ : syracuseStep 229319 = 343979) B343979
theorem B524231 : Blo 151794 524231 := bstep (se 1 (by rfl) ⟨393173, by rfl⟩ : syracuseStep 524231 = 786347) B786347
theorem B393407 : Blo 151794 393407 := bstep (se 1 (by rfl) ⟨295055, by rfl⟩ : syracuseStep 393407 = 590111) B590111
theorem B229631 : Blo 151794 229631 := bstep (se 1 (by rfl) ⟨172223, by rfl⟩ : syracuseStep 229631 = 344447) B344447
theorem B262399 : Blo 151794 262399 := bstep (se 1 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 262399 = 393599) B393599
theorem B491795 : Blo 151794 491795 := bstep (se 1 (by rfl) ⟨368846, by rfl⟩ : syracuseStep 491795 = 737693) B737693
theorem B229787 : Blo 151794 229787 := bstep (se 1 (by rfl) ⟨172340, by rfl⟩ : syracuseStep 229787 = 344681) B344681
theorem B2195885 : Blo 151794 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B623207 : Blo 151794 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B230207 : Blo 151794 230207 := bstep (se 1 (by rfl) ⟨172655, by rfl⟩ : syracuseStep 230207 = 345311) B345311
theorem B230351 : Blo 151794 230351 := bstep (se 1 (by rfl) ⟨172763, by rfl⟩ : syracuseStep 230351 = 345527) B345527
theorem B230441 : Blo 151794 230441 := bstep (se 2 (by rfl) ⟨86415, by rfl⟩ : syracuseStep 230441 = 172831) B172831
theorem B230471 : Blo 151794 230471 := bstep (se 1 (by rfl) ⟨172853, by rfl⟩ : syracuseStep 230471 = 345707) B345707
theorem B885917 : Blo 151794 885917 := bstep (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) B332219
theorem B591083 : Blo 151794 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B230651 : Blo 151794 230651 := bstep (se 1 (by rfl) ⟨172988, by rfl⟩ : syracuseStep 230651 = 345977) B345977
theorem B165115 : Blo 151794 165115 := bstep (se 1 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 165115 = 247673) B247673
theorem B230939 : Blo 151794 230939 := bstep (se 1 (by rfl) ⟨173204, by rfl⟩ : syracuseStep 230939 = 346409) B346409
theorem B788077 : Blo 151794 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B231323 : Blo 151794 231323 := bstep (se 1 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 231323 = 346985) B346985
theorem B231359 : Blo 151794 231359 := bstep (se 1 (by rfl) ⟨173519, by rfl⟩ : syracuseStep 231359 = 347039) B347039
theorem B1870295 : Blo 151794 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B231983 : Blo 151794 231983 := bstep (se 1 (by rfl) ⟨173987, by rfl⟩ : syracuseStep 231983 = 347975) B347975
theorem B232103 : Blo 151794 232103 := bstep (se 1 (by rfl) ⟨174077, by rfl⟩ : syracuseStep 232103 = 348155) B348155
theorem B232169 : Blo 151794 232169 := bstep (se 2 (by rfl) ⟨87063, by rfl⟩ : syracuseStep 232169 = 174127) B174127
theorem B232175 : Blo 151794 232175 := bstep (se 1 (by rfl) ⟨174131, by rfl⟩ : syracuseStep 232175 = 348263) B348263
theorem B232223 : Blo 151794 232223 := bstep (se 1 (by rfl) ⟨174167, by rfl⟩ : syracuseStep 232223 = 348335) B348335
theorem B494383 : Blo 151794 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B1117147 : Blo 151794 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B2395175 : Blo 151794 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B232553 : Blo 151794 232553 := bstep (se 2 (by rfl) ⟨87207, by rfl⟩ : syracuseStep 232553 = 174415) B174415
theorem B986255 : Blo 151794 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B232679 : Blo 151794 232679 := bstep (se 1 (by rfl) ⟨174509, by rfl⟩ : syracuseStep 232679 = 349019) B349019
theorem B1772927 : Blo 151794 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B233119 : Blo 151794 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B233183 : Blo 151794 233183 := bstep (se 1 (by rfl) ⟨174887, by rfl⟩ : syracuseStep 233183 = 349775) B349775
theorem B1478533 : Blo 151794 1478533 := bstep (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) B277225
theorem B954251 : Blo 151794 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B233465 : Blo 151794 233465 := bstep (se 2 (by rfl) ⟨87549, by rfl⟩ : syracuseStep 233465 = 175099) B175099
theorem B1740851 : Blo 151794 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B233663 : Blo 151794 233663 := bstep (se 1 (by rfl) ⟨175247, by rfl⟩ : syracuseStep 233663 = 350495) B350495
theorem B987329 : Blo 151794 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B397801 : Blo 151794 397801 := bstep (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) B298351
theorem B234031 : Blo 151794 234031 := bstep (se 1 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 234031 = 351047) B351047
theorem B1643111 : Blo 151794 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B792031 : Blo 151794 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B1153277 : Blo 151794 1153277 := bstep (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) B432479
theorem B661841 : Blo 151794 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B235879 : Blo 151794 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B2792015 : Blo 151794 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B236123 : Blo 151794 236123 := bstep (se 1 (by rfl) ⟨177092, by rfl⟩ : syracuseStep 236123 = 354185) B354185
theorem B925613 : Blo 151794 925613 := bstep (se 3 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 925613 = 347105) B347105
theorem B1712387 : Blo 151794 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B1417609 : Blo 151794 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B992351 : Blo 151794 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B173551 : Blo 151794 173551 := bstep (se 1 (by rfl) ⟨130163, by rfl⟩ : syracuseStep 173551 = 260327) B260327
theorem B730619 : Blo 151794 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B403553 : Blo 151794 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B731501 : Blo 151794 731501 := bstep (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) B274313
theorem B469423 : Blo 151794 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B174703 : Blo 151794 174703 := bstep (se 1 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 174703 = 262055) B262055
theorem B26978935 : Blo 151794 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B764639 : Blo 151794 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B928583 : Blo 151794 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B174919 : Blo 151794 174919 := bstep (se 1 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 174919 = 262379) B262379
theorem B994301 : Blo 151794 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B1158623 : Blo 151794 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B175807 : Blo 151794 175807 := bstep (se 1 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 175807 = 263711) B263711
theorem B3518153 : Blo 151794 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B733961 : Blo 151794 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B15774695 : Blo 151794 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B734771 : Blo 151794 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B342575 : Blo 151794 342575 := bstep (se 1 (by rfl) ⟨256931, by rfl⟩ : syracuseStep 342575 = 513863) B513863
theorem B932617 : Blo 151794 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B343367 : Blo 151794 343367 := bstep (se 1 (by rfl) ⟨257525, by rfl⟩ : syracuseStep 343367 = 515051) B515051
theorem B278171 : Blo 151794 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B442493 : Blo 151794 442493 := bstep (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) B165935
theorem B6799625 : Blo 151794 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B344375 : Blo 151794 344375 := bstep (se 1 (by rfl) ⟨258281, by rfl⟩ : syracuseStep 344375 = 516563) B516563
theorem B836477 : Blo 151794 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B836605 : Blo 151794 836605 := bstep (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) B313727
theorem B2245913 : Blo 151794 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B410951 : Blo 151794 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B870587 : Blo 151794 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B346859 : Blo 151794 346859 := bstep (se 1 (by rfl) ⟨260144, by rfl⟩ : syracuseStep 346859 = 520289) B520289
theorem B3754997 : Blo 151794 3754997 := bstep (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) B352031
theorem B740627 : Blo 151794 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B347689 : Blo 151794 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B347759 : Blo 151794 347759 := bstep (se 1 (by rfl) ⟨260819, by rfl⟩ : syracuseStep 347759 = 521639) B521639
theorem B347831 : Blo 151794 347831 := bstep (se 1 (by rfl) ⟨260873, by rfl⟩ : syracuseStep 347831 = 521747) B521747
theorem B348281 : Blo 151794 348281 := bstep (se 2 (by rfl) ⟨130605, by rfl⟩ : syracuseStep 348281 = 261211) B261211
theorem B1397033 : Blo 151794 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B151855 : Blo 151794 151855 := bstep (se 1 (by rfl) ⟨113891, by rfl⟩ : syracuseStep 151855 = 227783) B227783
theorem B1888589 : Blo 151794 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B872795 : Blo 151794 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B348587 : Blo 151794 348587 := bstep (se 1 (by rfl) ⟨261440, by rfl⟩ : syracuseStep 348587 = 522881) B522881
theorem B151999 : Blo 151794 151999 := bstep (se 1 (by rfl) ⟨113999, by rfl⟩ : syracuseStep 151999 = 227999) B227999
theorem B152095 : Blo 151794 152095 := bstep (se 1 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 152095 = 228143) B228143
theorem B152175 : Blo 151794 152175 := bstep (se 1 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 152175 = 228263) B228263
theorem B1462967 : Blo 151794 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B152295 : Blo 151794 152295 := bstep (se 1 (by rfl) ⟨114221, by rfl⟩ : syracuseStep 152295 = 228443) B228443
theorem B578279 : Blo 151794 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B349127 : Blo 151794 349127 := bstep (se 1 (by rfl) ⟨261845, by rfl⟩ : syracuseStep 349127 = 523691) B523691
theorem B1168343 : Blo 151794 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B152543 : Blo 151794 152543 := bstep (se 1 (by rfl) ⟨114407, by rfl⟩ : syracuseStep 152543 = 228815) B228815
theorem B349289 : Blo 151794 349289 := bstep (se 2 (by rfl) ⟨130983, by rfl⟩ : syracuseStep 349289 = 261967) B261967
theorem B152799 : Blo 151794 152799 := bstep (se 1 (by rfl) ⟨114599, by rfl⟩ : syracuseStep 152799 = 229199) B229199
theorem B152879 : Blo 151794 152879 := bstep (se 1 (by rfl) ⟨114659, by rfl⟩ : syracuseStep 152879 = 229319) B229319
theorem B349487 : Blo 151794 349487 := bstep (se 1 (by rfl) ⟨262115, by rfl⟩ : syracuseStep 349487 = 524231) B524231
theorem B775655 : Blo 151794 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B153119 : Blo 151794 153119 := bstep (se 1 (by rfl) ⟨114839, by rfl⟩ : syracuseStep 153119 = 229679) B229679
theorem B153279 : Blo 151794 153279 := bstep (se 1 (by rfl) ⟨114959, by rfl⟩ : syracuseStep 153279 = 229919) B229919
theorem B349919 : Blo 151794 349919 := bstep (se 1 (by rfl) ⟨262439, by rfl⟩ : syracuseStep 349919 = 524879) B524879
theorem B350279 : Blo 151794 350279 := bstep (se 1 (by rfl) ⟨262709, by rfl⟩ : syracuseStep 350279 = 525419) B525419
theorem B153727 : Blo 151794 153727 := bstep (se 1 (by rfl) ⟨115295, by rfl⟩ : syracuseStep 153727 = 230591) B230591
theorem B18208961 : Blo 151794 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B6609113 : Blo 151794 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B153823 : Blo 151794 153823 := bstep (se 1 (by rfl) ⟨115367, by rfl⟩ : syracuseStep 153823 = 230735) B230735
theorem B153883 : Blo 151794 153883 := bstep (se 1 (by rfl) ⟨115412, by rfl⟩ : syracuseStep 153883 = 230825) B230825
theorem B1038689 : Blo 151794 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B153983 : Blo 151794 153983 := bstep (se 1 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 153983 = 230975) B230975
theorem B154011 : Blo 151794 154011 := bstep (se 1 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 154011 = 231017) B231017
theorem B154303 : Blo 151794 154303 := bstep (se 1 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 154303 = 231455) B231455
theorem B219839 : Blo 151794 219839 := bstep (se 1 (by rfl) ⟨164879, by rfl⟩ : syracuseStep 219839 = 329759) B329759
theorem B154431 : Blo 151794 154431 := bstep (se 1 (by rfl) ⟨115823, by rfl⟩ : syracuseStep 154431 = 231647) B231647
theorem B154471 : Blo 151794 154471 := bstep (se 1 (by rfl) ⟨115853, by rfl⟩ : syracuseStep 154471 = 231707) B231707
theorem B1301507 : Blo 151794 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B154687 : Blo 151794 154687 := bstep (se 1 (by rfl) ⟨116015, by rfl⟩ : syracuseStep 154687 = 232031) B232031
theorem B2776193 : Blo 151794 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B154875 : Blo 151794 154875 := bstep (se 1 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 154875 = 232313) B232313
theorem B154907 : Blo 151794 154907 := bstep (se 1 (by rfl) ⟨116180, by rfl⟩ : syracuseStep 154907 = 232361) B232361
theorem B155007 : Blo 151794 155007 := bstep (se 1 (by rfl) ⟨116255, by rfl⟩ : syracuseStep 155007 = 232511) B232511
theorem B1465769 : Blo 151794 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B777761 : Blo 151794 777761 := bstep (se 2 (by rfl) ⟨291660, by rfl⟩ : syracuseStep 777761 = 583321) B583321
theorem B777923 : Blo 151794 777923 := bstep (se 1 (by rfl) ⟨583442, by rfl⟩ : syracuseStep 777923 = 1166885) B1166885
theorem B155375 : Blo 151794 155375 := bstep (se 1 (by rfl) ⟨116531, by rfl⟩ : syracuseStep 155375 = 233063) B233063
theorem B1761263 : Blo 151794 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B155631 : Blo 151794 155631 := bstep (se 1 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 155631 = 233447) B233447
theorem B155711 : Blo 151794 155711 := bstep (se 1 (by rfl) ⟨116783, by rfl⟩ : syracuseStep 155711 = 233567) B233567
theorem B155719 : Blo 151794 155719 := bstep (se 1 (by rfl) ⟨116789, by rfl⟩ : syracuseStep 155719 = 233579) B233579
theorem B155751 : Blo 151794 155751 := bstep (se 1 (by rfl) ⟨116813, by rfl⟩ : syracuseStep 155751 = 233627) B233627
theorem B2810699 : Blo 151794 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B156763 : Blo 151794 156763 := bstep (se 1 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 156763 = 235145) B235145
theorem B386279 : Blo 151794 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B386633 : Blo 151794 386633 := bstep (se 2 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 386633 = 289975) B289975
theorem B1173203 : Blo 151794 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B780191 : Blo 151794 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B1894387 : Blo 151794 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B518777 : Blo 151794 518777 := bstep (se 2 (by rfl) ⟨194541, by rfl⟩ : syracuseStep 518777 = 389083) B389083
theorem B748187 : Blo 151794 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B256891 : Blo 151794 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B10742807 : Blo 151794 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B257161 : Blo 151794 257161 := bstep (se 2 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 257161 = 192871) B192871
theorem B257215 : Blo 151794 257215 := bstep (se 1 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 257215 = 385823) B385823
theorem B519443 : Blo 151794 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B3731159 : Blo 151794 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B585569 : Blo 151794 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B1306529 : Blo 151794 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B192719 : Blo 151794 192719 := bstep (se 1 (by rfl) ⟨144539, by rfl⟩ : syracuseStep 192719 = 289079) B289079
theorem B291023 : Blo 151794 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B258383 : Blo 151794 258383 := bstep (se 1 (by rfl) ⟨193787, by rfl⟩ : syracuseStep 258383 = 387575) B387575
theorem B1929635 : Blo 151794 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B160475 : Blo 151794 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B193691 : Blo 151794 193691 := bstep (se 1 (by rfl) ⟨145268, by rfl⟩ : syracuseStep 193691 = 290537) B290537
theorem B291995 : Blo 151794 291995 := bstep (se 1 (by rfl) ⟨218996, by rfl⟩ : syracuseStep 291995 = 437993) B437993
theorem B980255 : Blo 151794 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B521801 : Blo 151794 521801 := bstep (se 2 (by rfl) ⟨195675, by rfl⟩ : syracuseStep 521801 = 391351) B391351
theorem B587407 : Blo 151794 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B194395 : Blo 151794 194395 := bstep (se 1 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 194395 = 291593) B291593
theorem B292891 : Blo 151794 292891 := bstep (se 1 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 292891 = 439337) B439337
theorem B2488805 : Blo 151794 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B227819 : Blo 151794 227819 := bstep (se 1 (by rfl) ⟨170864, by rfl⟩ : syracuseStep 227819 = 341729) B341729
theorem B1866503 : Blo 151794 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B228167 : Blo 151794 228167 := bstep (se 1 (by rfl) ⟨171125, by rfl⟩ : syracuseStep 228167 = 342251) B342251
theorem B326683 : Blo 151794 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B229001 : Blo 151794 229001 := bstep (se 2 (by rfl) ⟨85875, by rfl⟩ : syracuseStep 229001 = 171751) B171751
theorem B229031 : Blo 151794 229031 := bstep (se 1 (by rfl) ⟨171773, by rfl⟩ : syracuseStep 229031 = 343547) B343547
theorem B229151 : Blo 151794 229151 := bstep (se 1 (by rfl) ⟨171863, by rfl⟩ : syracuseStep 229151 = 343727) B343727
theorem B229211 : Blo 151794 229211 := bstep (se 1 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 229211 = 343817) B343817
theorem B622525 : Blo 151794 622525 := bstep (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) B233447
theorem B294995 : Blo 151794 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B262271 : Blo 151794 262271 := bstep (se 1 (by rfl) ⟨196703, by rfl⟩ : syracuseStep 262271 = 393407) B393407
theorem B327863 : Blo 151794 327863 := bstep (se 1 (by rfl) ⟨245897, by rfl⟩ : syracuseStep 327863 = 491795) B491795
theorem B229583 : Blo 151794 229583 := bstep (se 1 (by rfl) ⟨172187, by rfl⟩ : syracuseStep 229583 = 344375) B344375
theorem B557651 : Blo 151794 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B590611 : Blo 151794 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B394055 : Blo 151794 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B1115473 : Blo 151794 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B231239 : Blo 151794 231239 := bstep (se 1 (by rfl) ⟨173429, by rfl⟩ : syracuseStep 231239 = 346859) B346859
theorem B427933 : Blo 151794 427933 := bstep (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) B160475
theorem B231401 : Blo 151794 231401 := bstep (se 2 (by rfl) ⟨86775, by rfl⟩ : syracuseStep 231401 = 173551) B173551
theorem B657503 : Blo 151794 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B1050769 : Blo 151794 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B493751 : Blo 151794 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B1181951 : Blo 151794 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B231839 : Blo 151794 231839 := bstep (se 1 (by rfl) ⟨173879, by rfl⟩ : syracuseStep 231839 = 347759) B347759
theorem B231887 : Blo 151794 231887 := bstep (se 1 (by rfl) ⟨173915, by rfl⟩ : syracuseStep 231887 = 347831) B347831
theorem B2525849 : Blo 151794 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B232187 : Blo 151794 232187 := bstep (se 1 (by rfl) ⟨174140, by rfl⟩ : syracuseStep 232187 = 348281) B348281
theorem B658219 : Blo 151794 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B232391 : Blo 151794 232391 := bstep (se 1 (by rfl) ⟨174293, by rfl⟩ : syracuseStep 232391 = 348587) B348587
theorem B625897 : Blo 151794 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B232751 : Blo 151794 232751 := bstep (se 1 (by rfl) ⟨174563, by rfl⟩ : syracuseStep 232751 = 349127) B349127
theorem B232859 : Blo 151794 232859 := bstep (se 1 (by rfl) ⟨174644, by rfl⟩ : syracuseStep 232859 = 349289) B349289
theorem B232937 : Blo 151794 232937 := bstep (se 2 (by rfl) ⟨87351, by rfl⟩ : syracuseStep 232937 = 174703) B174703
theorem B232991 : Blo 151794 232991 := bstep (se 1 (by rfl) ⟨174743, by rfl⟩ : syracuseStep 232991 = 349487) B349487
theorem B659177 : Blo 151794 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B233225 : Blo 151794 233225 := bstep (se 2 (by rfl) ⟨87459, by rfl⟩ : syracuseStep 233225 = 174919) B174919
theorem B233279 : Blo 151794 233279 := bstep (se 1 (by rfl) ⟨174959, by rfl⟩ : syracuseStep 233279 = 349919) B349919
theorem B233519 : Blo 151794 233519 := bstep (se 1 (by rfl) ⟨175139, by rfl⟩ : syracuseStep 233519 = 350279) B350279
theorem B692459 : Blo 151794 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B463585 : Blo 151794 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B234409 : Blo 151794 234409 := bstep (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) B175807
theorem B1971377 : Blo 151794 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B1742309 : Blo 151794 1742309 := bstep (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) B326683
theorem B1873799 : Blo 151794 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B530401 : Blo 151794 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B4987453 : Blo 151794 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B498791 : Blo 151794 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B1056041 : Blo 151794 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B662867 : Blo 151794 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B172255 : Blo 151794 172255 := bstep (se 1 (by rfl) ⟨129191, by rfl⟩ : syracuseStep 172255 = 258383) B258383
theorem B1286423 : Blo 151794 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B830033 : Blo 151794 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B4533083 : Blo 151794 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B4566365 : Blo 151794 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B209017 : Blo 151794 209017 := bstep (se 2 (by rfl) ⟨78381, by rfl⟩ : syracuseStep 209017 = 156763) B156763
theorem B1258021 : Blo 151794 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B2503331 : Blo 151794 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B636167 : Blo 151794 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B1160567 : Blo 151794 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B931355 : Blo 151794 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B1259059 : Blo 151794 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B1095407 : Blo 151794 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B1095869 : Blo 151794 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B342521 : Blo 151794 342521 := bstep (se 2 (by rfl) ⟨128445, by rfl⟩ : syracuseStep 342521 = 256891) B256891
theorem B1489529 : Blo 151794 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B12139307 : Blo 151794 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B4406075 : Blo 151794 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B768851 : Blo 151794 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B342881 : Blo 151794 342881 := bstep (se 2 (by rfl) ⟨128580, by rfl⟩ : syracuseStep 342881 = 257161) B257161
theorem B441227 : Blo 151794 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B342953 : Blo 151794 342953 := bstep (se 2 (by rfl) ⟨128607, by rfl⟩ : syracuseStep 342953 = 257215) B257215
theorem B867671 : Blo 151794 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B1850795 : Blo 151794 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B310825 : Blo 151794 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B312041 : Blo 151794 312041 := bstep (se 2 (by rfl) ⟨117015, by rfl⟩ : syracuseStep 312041 = 234031) B234031
theorem B345851 : Blo 151794 345851 := bstep (se 1 (by rfl) ⟨259388, by rfl⟩ : syracuseStep 345851 = 518777) B518777
theorem B509759 : Blo 151794 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B7161871 : Blo 151794 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B346295 : Blo 151794 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B772415 : Blo 151794 772415 := bstep (se 1 (by rfl) ⟨579311, by rfl⟩ : syracuseStep 772415 = 1158623) B1158623
theorem B2345435 : Blo 151794 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B871019 : Blo 151794 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B347867 : Blo 151794 347867 := bstep (se 1 (by rfl) ⟨260900, by rfl⟩ : syracuseStep 347867 = 521801) B521801
theorem B1659203 : Blo 151794 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B151879 : Blo 151794 151879 := bstep (se 1 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 151879 = 227819) B227819
theorem B152111 : Blo 151794 152111 := bstep (se 1 (by rfl) ⟨114083, by rfl⟩ : syracuseStep 152111 = 228167) B228167
theorem B152667 : Blo 151794 152667 := bstep (se 1 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 152667 = 229001) B229001
theorem B185447 : Blo 151794 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B152687 : Blo 151794 152687 := bstep (se 1 (by rfl) ⟨114515, by rfl⟩ : syracuseStep 152687 = 229031) B229031
theorem B152767 : Blo 151794 152767 := bstep (se 1 (by rfl) ⟨114575, by rfl⟩ : syracuseStep 152767 = 229151) B229151
theorem B152807 : Blo 151794 152807 := bstep (se 1 (by rfl) ⟨114605, by rfl⟩ : syracuseStep 152807 = 229211) B229211
theorem B153087 : Blo 151794 153087 := bstep (se 1 (by rfl) ⟨114815, by rfl⟩ : syracuseStep 153087 = 229631) B229631
theorem B153191 : Blo 151794 153191 := bstep (se 1 (by rfl) ⟨114893, by rfl⟩ : syracuseStep 153191 = 229787) B229787
theorem B1463923 : Blo 151794 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B349865 : Blo 151794 349865 := bstep (se 2 (by rfl) ⟨131199, by rfl⟩ : syracuseStep 349865 = 262399) B262399
theorem B415471 : Blo 151794 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B1890145 : Blo 151794 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B513917 : Blo 151794 513917 := bstep (se 3 (by rfl) ⟨96359, by rfl⟩ : syracuseStep 513917 = 192719) B192719
theorem B153471 : Blo 151794 153471 := bstep (se 1 (by rfl) ⟨115103, by rfl⟩ : syracuseStep 153471 = 230207) B230207
theorem B153567 : Blo 151794 153567 := bstep (se 1 (by rfl) ⟨115175, by rfl⟩ : syracuseStep 153567 = 230351) B230351
theorem B153627 : Blo 151794 153627 := bstep (se 1 (by rfl) ⟨115220, by rfl⟩ : syracuseStep 153627 = 230441) B230441
theorem B153647 : Blo 151794 153647 := bstep (se 1 (by rfl) ⟨115235, by rfl⟩ : syracuseStep 153647 = 230471) B230471
theorem B153767 : Blo 151794 153767 := bstep (se 1 (by rfl) ⟨115325, by rfl⟩ : syracuseStep 153767 = 230651) B230651
theorem B1497275 : Blo 151794 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B153959 : Blo 151794 153959 := bstep (se 1 (by rfl) ⟨115469, by rfl⟩ : syracuseStep 153959 = 230939) B230939
theorem B154215 : Blo 151794 154215 := bstep (se 1 (by rfl) ⟨115661, by rfl⟩ : syracuseStep 154215 = 231323) B231323
theorem B154239 : Blo 151794 154239 := bstep (se 1 (by rfl) ⟨115679, by rfl⟩ : syracuseStep 154239 = 231359) B231359
theorem B580391 : Blo 151794 580391 := bstep (se 1 (by rfl) ⟨435293, by rfl⟩ : syracuseStep 580391 = 870587) B870587
theorem B220153 : Blo 151794 220153 := bstep (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) B165115
theorem B154655 : Blo 151794 154655 := bstep (se 1 (by rfl) ⟨115991, by rfl⟩ : syracuseStep 154655 = 231983) B231983
theorem B154735 : Blo 151794 154735 := bstep (se 1 (by rfl) ⟨116051, by rfl⟩ : syracuseStep 154735 = 232103) B232103
theorem B154779 : Blo 151794 154779 := bstep (se 1 (by rfl) ⟨116084, by rfl⟩ : syracuseStep 154779 = 232169) B232169
theorem B154783 : Blo 151794 154783 := bstep (se 1 (by rfl) ⟨116087, by rfl⟩ : syracuseStep 154783 = 232175) B232175
theorem B154815 : Blo 151794 154815 := bstep (se 1 (by rfl) ⟨116111, by rfl⟩ : syracuseStep 154815 = 232223) B232223
theorem B1957229 : Blo 151794 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B155035 : Blo 151794 155035 := bstep (se 1 (by rfl) ⟨116276, by rfl⟩ : syracuseStep 155035 = 232553) B232553
theorem B155119 : Blo 151794 155119 := bstep (se 1 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 155119 = 232679) B232679
theorem B155455 : Blo 151794 155455 := bstep (se 1 (by rfl) ⟨116591, by rfl⟩ : syracuseStep 155455 = 233183) B233183
theorem B155643 : Blo 151794 155643 := bstep (se 1 (by rfl) ⟨116732, by rfl⟩ : syracuseStep 155643 = 233465) B233465
theorem B155775 : Blo 151794 155775 := bstep (se 1 (by rfl) ⟨116831, by rfl⟩ : syracuseStep 155775 = 233663) B233663
theorem B581863 : Blo 151794 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B2646269 : Blo 151794 2646269 := bstep (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) B992351
theorem B516509 : Blo 151794 516509 := bstep (se 3 (by rfl) ⟨96845, by rfl⟩ : syracuseStep 516509 = 193691) B193691
theorem B975311 : Blo 151794 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B385519 : Blo 151794 385519 := bstep (se 1 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 385519 = 578279) B578279
theorem B778895 : Blo 151794 778895 := bstep (se 1 (by rfl) ⟨584171, by rfl⟩ : syracuseStep 778895 = 1168343) B1168343
theorem B35971913 : Blo 151794 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B517103 : Blo 151794 517103 := bstep (se 1 (by rfl) ⟨387827, by rfl⟩ : syracuseStep 517103 = 775655) B775655
theorem B4973957 : Blo 151794 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B1861343 : Blo 151794 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B157415 : Blo 151794 157415 := bstep (se 1 (by rfl) ⟨118061, by rfl⟩ : syracuseStep 157415 = 236123) B236123
theorem B977179 : Blo 151794 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B518507 : Blo 151794 518507 := bstep (se 1 (by rfl) ⟨388880, by rfl⟩ : syracuseStep 518507 = 777761) B777761
theorem B518615 : Blo 151794 518615 := bstep (se 1 (by rfl) ⟨388961, by rfl⟩ : syracuseStep 518615 = 777923) B777923
theorem B617075 : Blo 151794 617075 := bstep (se 1 (by rfl) ⟨462806, by rfl⟩ : syracuseStep 617075 = 925613) B925613
theorem B1174175 : Blo 151794 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B1076141 : Blo 151794 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B257519 : Blo 151794 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B487079 : Blo 151794 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B257755 : Blo 151794 257755 := bstep (se 1 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 257755 = 386633) B386633
theorem B782135 : Blo 151794 782135 := bstep (se 1 (by rfl) ⟨586601, by rfl⟩ : syracuseStep 782135 = 1173203) B1173203
theorem B520127 : Blo 151794 520127 := bstep (se 1 (by rfl) ⟨390095, by rfl⟩ : syracuseStep 520127 = 780191) B780191
theorem B487667 : Blo 151794 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B586237 : Blo 151794 586237 := bstep (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) B219839
theorem B619055 : Blo 151794 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B783209 : Blo 151794 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B259193 : Blo 151794 259193 := bstep (se 2 (by rfl) ⟨97197, by rfl⟩ : syracuseStep 259193 = 194395) B194395
theorem B2487439 : Blo 151794 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B390379 : Blo 151794 390379 := bstep (se 1 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 390379 = 585569) B585569
theorem B390521 : Blo 151794 390521 := bstep (se 2 (by rfl) ⟨146445, by rfl⟩ : syracuseStep 390521 = 292891) B292891
theorem B6387133 : Blo 151794 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B194015 : Blo 151794 194015 := bstep (se 1 (by rfl) ⟨145511, by rfl⟩ : syracuseStep 194015 = 291023) B291023
theorem B10516463 : Blo 151794 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B194663 : Blo 151794 194663 := bstep (se 1 (by rfl) ⟨145997, by rfl⟩ : syracuseStep 194663 = 291995) B291995
theorem B653503 : Blo 151794 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B489847 : Blo 151794 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B228383 : Blo 151794 228383 := bstep (se 1 (by rfl) ⟨171287, by rfl⟩ : syracuseStep 228383 = 342575) B342575
theorem B1244335 : Blo 151794 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B228911 : Blo 151794 228911 := bstep (se 1 (by rfl) ⟨171683, by rfl⟩ : syracuseStep 228911 = 343367) B343367
theorem B196663 : Blo 151794 196663 := bstep (se 1 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 196663 = 294995) B294995
theorem B229673 : Blo 151794 229673 := bstep (se 2 (by rfl) ⟨86127, by rfl⟩ : syracuseStep 229673 = 172255) B172255
theorem B262703 : Blo 151794 262703 := bstep (se 1 (by rfl) ⟨197027, by rfl⟩ : syracuseStep 262703 = 394055) B394055
theorem B54887381 : Blo 151794 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B787481 : Blo 151794 787481 := bstep (se 2 (by rfl) ⟨295305, by rfl⟩ : syracuseStep 787481 = 590611) B590611
theorem B230567 : Blo 151794 230567 := bstep (se 1 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 230567 = 345851) B345851
theorem B230863 : Blo 151794 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B329167 : Blo 151794 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B787967 : Blo 151794 787967 := bstep (se 1 (by rfl) ⟨590975, by rfl⟩ : syracuseStep 787967 = 1181951) B1181951
theorem B231911 : Blo 151794 231911 := bstep (se 1 (by rfl) ⟨173933, by rfl⟩ : syracuseStep 231911 = 347867) B347867
theorem B461639 : Blo 151794 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B494525 : Blo 151794 494525 := bstep (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) B185447
theorem B1314251 : Blo 151794 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B233243 : Blo 151794 233243 := bstep (se 1 (by rfl) ⟨174932, by rfl⟩ : syracuseStep 233243 = 349865) B349865
theorem B1249199 : Blo 151794 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B332527 : Blo 151794 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B1677361 : Blo 151794 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B3315971 : Blo 151794 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B3316585 : Blo 151794 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B3022055 : Blo 151794 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B1678745 : Blo 151794 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B171679 : Blo 151794 171679 := bstep (se 1 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 171679 = 257519) B257519
theorem B1679093 : Blo 151794 1679093 := bstep (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) B157415
theorem B172795 : Blo 151794 172795 := bstep (se 1 (by rfl) ⟨129596, by rfl⟩ : syracuseStep 172795 = 259193) B259193
theorem B730271 : Blo 151794 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B730579 : Blo 151794 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B993019 : Blo 151794 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B174847 : Blo 151794 174847 := bstep (se 1 (by rfl) ⟨131135, by rfl⟩ : syracuseStep 174847 = 262271) B262271
theorem B208027 : Blo 151794 208027 := bstep (se 1 (by rfl) ⟨156020, by rfl⟩ : syracuseStep 208027 = 312041) B312041
theorem B339839 : Blo 151794 339839 := bstep (se 1 (by rfl) ⟨254879, by rfl⟩ : syracuseStep 339839 = 509759) B509759
theorem B438335 : Blo 151794 438335 := bstep (se 1 (by rfl) ⟨328751, by rfl⟩ : syracuseStep 438335 = 657503) B657503
theorem B1487069 : Blo 151794 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B1683899 : Blo 151794 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B1487297 : Blo 151794 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B439451 : Blo 151794 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B570577 : Blo 151794 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B9549161 : Blo 151794 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B1161539 : Blo 151794 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B342611 : Blo 151794 342611 := bstep (se 1 (by rfl) ⟨256958, by rfl⟩ : syracuseStep 342611 = 513917) B513917
theorem B998183 : Blo 151794 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B834529 : Blo 151794 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B704027 : Blo 151794 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B441911 : Blo 151794 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B343673 : Blo 151794 343673 := bstep (se 2 (by rfl) ⟨128877, by rfl⟩ : syracuseStep 343673 = 257755) B257755
theorem B278689 : Blo 151794 278689 := bstep (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) B209017
theorem B344339 : Blo 151794 344339 := bstep (se 1 (by rfl) ⟨258254, by rfl⟩ : syracuseStep 344339 = 516509) B516509
theorem B344735 : Blo 151794 344735 := bstep (se 1 (by rfl) ⟨258551, by rfl⟩ : syracuseStep 344735 = 517103) B517103
theorem B312545 : Blo 151794 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B345671 : Blo 151794 345671 := bstep (se 1 (by rfl) ⟨259253, by rfl⟩ : syracuseStep 345671 = 518507) B518507
theorem B345743 : Blo 151794 345743 := bstep (se 1 (by rfl) ⟨259307, by rfl⟩ : syracuseStep 345743 = 518615) B518615
theorem B411383 : Blo 151794 411383 := bstep (se 1 (by rfl) ⟨308537, by rfl⟩ : syracuseStep 411383 = 617075) B617075
theorem B1951897 : Blo 151794 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B346751 : Blo 151794 346751 := bstep (se 1 (by rfl) ⟨260063, by rfl⟩ : syracuseStep 346751 = 520127) B520127
theorem B707201 : Blo 151794 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B871337 : Blo 151794 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B412703 : Blo 151794 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B773711 : Blo 151794 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B1659113 : Blo 151794 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B10080773 : Blo 151794 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B2937383 : Blo 151794 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B512567 : Blo 151794 512567 := bstep (se 1 (by rfl) ⟨384425, by rfl⟩ : syracuseStep 512567 = 768851) B768851
theorem B152255 : Blo 151794 152255 := bstep (se 1 (by rfl) ⟨114191, by rfl⟩ : syracuseStep 152255 = 228383) B228383
theorem B414433 : Blo 151794 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B578447 : Blo 151794 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B1233863 : Blo 151794 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B152607 : Blo 151794 152607 := bstep (se 1 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 152607 = 228911) B228911
theorem B218575 : Blo 151794 218575 := bstep (se 1 (by rfl) ⟨163931, by rfl⟩ : syracuseStep 218575 = 327863) B327863
theorem B153055 : Blo 151794 153055 := bstep (se 1 (by rfl) ⟨114791, by rfl⟩ : syracuseStep 153055 = 229583) B229583
theorem B775817 : Blo 151794 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B1300445 : Blo 151794 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B514025 : Blo 151794 514025 := bstep (se 2 (by rfl) ⟨192759, by rfl⟩ : syracuseStep 514025 = 385519) B385519
theorem B154159 : Blo 151794 154159 := bstep (se 1 (by rfl) ⟨115619, by rfl⟩ : syracuseStep 154159 = 231239) B231239
theorem B154267 : Blo 151794 154267 := bstep (se 1 (by rfl) ⟨115700, by rfl⟩ : syracuseStep 154267 = 231401) B231401
theorem B514943 : Blo 151794 514943 := bstep (se 1 (by rfl) ⟨386207, by rfl⟩ : syracuseStep 514943 = 772415) B772415
theorem B154559 : Blo 151794 154559 := bstep (se 1 (by rfl) ⟨115919, by rfl⟩ : syracuseStep 154559 = 231839) B231839
theorem B154591 : Blo 151794 154591 := bstep (se 1 (by rfl) ⟨115943, by rfl⟩ : syracuseStep 154591 = 231887) B231887
theorem B1563623 : Blo 151794 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B580679 : Blo 151794 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B154791 : Blo 151794 154791 := bstep (se 1 (by rfl) ⟨116093, by rfl⟩ : syracuseStep 154791 = 232187) B232187
theorem B154927 : Blo 151794 154927 := bstep (se 1 (by rfl) ⟨116195, by rfl⟩ : syracuseStep 154927 = 232391) B232391
theorem B155167 : Blo 151794 155167 := bstep (se 1 (by rfl) ⟨116375, by rfl⟩ : syracuseStep 155167 = 232751) B232751
theorem B155239 : Blo 151794 155239 := bstep (se 1 (by rfl) ⟨116429, by rfl⟩ : syracuseStep 155239 = 232859) B232859
theorem B155291 : Blo 151794 155291 := bstep (se 1 (by rfl) ⟨116468, by rfl⟩ : syracuseStep 155291 = 232937) B232937
theorem B155327 : Blo 151794 155327 := bstep (se 1 (by rfl) ⟨116495, by rfl⟩ : syracuseStep 155327 = 232991) B232991
theorem B155483 : Blo 151794 155483 := bstep (se 1 (by rfl) ⟨116612, by rfl⟩ : syracuseStep 155483 = 233225) B233225
theorem B155519 : Blo 151794 155519 := bstep (se 1 (by rfl) ⟨116639, by rfl⟩ : syracuseStep 155519 = 233279) B233279
theorem B155679 : Blo 151794 155679 := bstep (se 1 (by rfl) ⟨116759, by rfl⟩ : syracuseStep 155679 = 233519) B233519
theorem B1401025 : Blo 151794 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B1106135 : Blo 151794 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1302905 : Blo 151794 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B877625 : Blo 151794 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B517373 : Blo 151794 517373 := bstep (se 3 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 517373 = 194015) B194015
theorem B386927 : Blo 151794 386927 := bstep (se 1 (by rfl) ⟨290195, by rfl⟩ : syracuseStep 386927 = 580391) B580391
theorem B1304819 : Blo 151794 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B1764179 : Blo 151794 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B519101 : Blo 151794 519101 := bstep (se 3 (by rfl) ⟨97331, by rfl⟩ : syracuseStep 519101 = 194663) B194663
theorem B650207 : Blo 151794 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B519263 : Blo 151794 519263 := bstep (se 1 (by rfl) ⟨389447, by rfl⟩ : syracuseStep 519263 = 778895) B778895
theorem B23981275 : Blo 151794 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B781649 : Blo 151794 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B618113 : Blo 151794 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B1240895 : Blo 151794 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B520505 : Blo 151794 520505 := bstep (se 2 (by rfl) ⟨195189, by rfl⟩ : syracuseStep 520505 = 390379) B390379
theorem B553355 : Blo 151794 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B782783 : Blo 151794 782783 := bstep (se 1 (by rfl) ⟨587087, by rfl⟩ : syracuseStep 782783 = 1174175) B1174175
theorem B8516177 : Blo 151794 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B717427 : Blo 151794 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B3044243 : Blo 151794 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B553961 : Blo 151794 553961 := bstep (se 2 (by rfl) ⟨207735, by rfl⟩ : syracuseStep 553961 = 415471) B415471
theorem B1176605 : Blo 151794 1176605 := bstep (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) B441227
theorem B324719 : Blo 151794 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B521423 : Blo 151794 521423 := bstep (se 1 (by rfl) ⟨391067, by rfl⟩ : syracuseStep 521423 = 782135) B782135
theorem B1668887 : Blo 151794 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B653129 : Blo 151794 653129 := bstep (se 2 (by rfl) ⟨244923, by rfl⟩ : syracuseStep 653129 = 489847) B489847
theorem B522139 : Blo 151794 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B6649937 : Blo 151794 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B424111 : Blo 151794 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B260347 : Blo 151794 260347 := bstep (se 1 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 260347 = 390521) B390521
theorem B620903 : Blo 151794 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B7010975 : Blo 151794 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B293537 : Blo 151794 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B228347 : Blo 151794 228347 := bstep (se 1 (by rfl) ⟨171260, by rfl⟩ : syracuseStep 228347 = 342521) B342521
theorem B8092871 : Blo 151794 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B228587 : Blo 151794 228587 := bstep (se 1 (by rfl) ⟨171440, by rfl⟩ : syracuseStep 228587 = 342881) B342881
theorem B228635 : Blo 151794 228635 := bstep (se 1 (by rfl) ⟨171476, by rfl⟩ : syracuseStep 228635 = 342953) B342953
theorem B262217 : Blo 151794 262217 := bstep (se 2 (by rfl) ⟨98331, by rfl⟩ : syracuseStep 262217 = 196663) B196663
theorem B229559 : Blo 151794 229559 := bstep (se 1 (by rfl) ⟨172169, by rfl⟩ : syracuseStep 229559 = 344339) B344339
theorem B1868033 : Blo 151794 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B229823 : Blo 151794 229823 := bstep (se 1 (by rfl) ⟨172367, by rfl⟩ : syracuseStep 229823 = 344735) B344735
theorem B524987 : Blo 151794 524987 := bstep (se 1 (by rfl) ⟨393740, by rfl⟩ : syracuseStep 524987 = 787481) B787481
theorem B230393 : Blo 151794 230393 := bstep (se 2 (by rfl) ⟨86397, by rfl⟩ : syracuseStep 230393 = 172795) B172795
theorem B525311 : Blo 151794 525311 := bstep (se 1 (by rfl) ⟨393983, by rfl⟩ : syracuseStep 525311 = 787967) B787967
theorem B230447 : Blo 151794 230447 := bstep (se 1 (by rfl) ⟨172835, by rfl⟩ : syracuseStep 230447 = 345671) B345671
theorem B230495 : Blo 151794 230495 := bstep (se 1 (by rfl) ⟨172871, by rfl⟩ : syracuseStep 230495 = 345743) B345743
theorem B231167 : Blo 151794 231167 := bstep (se 1 (by rfl) ⟨173375, by rfl⟩ : syracuseStep 231167 = 346751) B346751
theorem B329683 : Blo 151794 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B6720515 : Blo 151794 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B822575 : Blo 151794 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B233129 : Blo 151794 233129 := bstep (se 2 (by rfl) ⟨87423, by rfl⟩ : syracuseStep 233129 = 174847) B174847
theorem B1119395 : Blo 151794 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B956569 : Blo 151794 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B760769 : Blo 151794 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B433471 : Blo 151794 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B696185 : Blo 151794 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B827263 : Blo 151794 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B2236481 : Blo 151794 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B991379 : Blo 151794 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B565481 : Blo 151794 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B368903 : Blo 151794 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B1122599 : Blo 151794 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B991531 : Blo 151794 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B5677451 : Blo 151794 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B369307 : Blo 151794 369307 := bstep (se 1 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 369307 = 553961) B553961
theorem B6366107 : Blo 151794 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B435419 : Blo 151794 435419 := bstep (se 1 (by rfl) ⟨326564, by rfl⟩ : syracuseStep 435419 = 653129) B653129
theorem B4433291 : Blo 151794 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B665455 : Blo 151794 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B469351 : Blo 151794 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B371585 : Blo 151794 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B175135 : Blo 151794 175135 := bstep (se 1 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 175135 = 262703) B262703
theorem B208363 : Blo 151794 208363 := bstep (se 1 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 208363 = 312545) B312545
theorem B274255 : Blo 151794 274255 := bstep (se 1 (by rfl) ⟨205691, by rfl⟩ : syracuseStep 274255 = 411383) B411383
theorem B471467 : Blo 151794 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B307817 : Blo 151794 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B438889 : Blo 151794 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B275135 : Blo 151794 275135 := bstep (se 1 (by rfl) ⟨206351, by rfl⟩ : syracuseStep 275135 = 412703) B412703
theorem B1324025 : Blo 151794 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B832799 : Blo 151794 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B2602529 : Blo 151794 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B341711 : Blo 151794 341711 := bstep (se 1 (by rfl) ⟨256283, by rfl⟩ : syracuseStep 341711 = 512567) B512567
theorem B866963 : Blo 151794 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B342683 : Blo 151794 342683 := bstep (se 1 (by rfl) ⟨257012, by rfl⟩ : syracuseStep 342683 = 514025) B514025
theorem B2210647 : Blo 151794 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B343295 : Blo 151794 343295 := bstep (se 1 (by rfl) ⟨257471, by rfl⟩ : syracuseStep 343295 = 514943) B514943
theorem B2014703 : Blo 151794 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B737423 : Blo 151794 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B868603 : Blo 151794 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B344915 : Blo 151794 344915 := bstep (se 1 (by rfl) ⟨258686, by rfl⟩ : syracuseStep 344915 = 517373) B517373
theorem B1655741 : Blo 151794 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B443369 : Blo 151794 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B869879 : Blo 151794 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B18695933 : Blo 151794 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B346067 : Blo 151794 346067 := bstep (se 1 (by rfl) ⟨259550, by rfl⟩ : syracuseStep 346067 = 519101) B519101
theorem B346175 : Blo 151794 346175 := bstep (se 1 (by rfl) ⟨259631, by rfl⟩ : syracuseStep 346175 = 519263) B519263
theorem B1231037 : Blo 151794 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B412075 : Blo 151794 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B347003 : Blo 151794 347003 := bstep (se 1 (by rfl) ⟨260252, by rfl⟩ : syracuseStep 347003 = 520505) B520505
theorem B347129 : Blo 151794 347129 := bstep (se 2 (by rfl) ⟨130173, by rfl⟩ : syracuseStep 347129 = 260347) B260347
theorem B216479 : Blo 151794 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B347615 : Blo 151794 347615 := bstep (se 1 (by rfl) ⟨260711, by rfl⟩ : syracuseStep 347615 = 521423) B521423
theorem B4476653 : Blo 151794 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B774359 : Blo 151794 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B152231 : Blo 151794 152231 := bstep (se 1 (by rfl) ⟨114173, by rfl⟩ : syracuseStep 152231 = 228347) B228347
theorem B5395247 : Blo 151794 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B152391 : Blo 151794 152391 := bstep (se 1 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 152391 = 228587) B228587
theorem B152423 : Blo 151794 152423 := bstep (se 1 (by rfl) ⟨114317, by rfl⟩ : syracuseStep 152423 = 228635) B228635
theorem B153115 : Blo 151794 153115 := bstep (se 1 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 153115 = 229673) B229673
theorem B36591587 : Blo 151794 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B153711 : Blo 151794 153711 := bstep (se 1 (by rfl) ⟨115283, by rfl⟩ : syracuseStep 153711 = 230567) B230567
theorem B154607 : Blo 151794 154607 := bstep (se 1 (by rfl) ⟨115955, by rfl⟩ : syracuseStep 154607 = 231911) B231911
theorem B974105 : Blo 151794 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B580891 : Blo 151794 580891 := bstep (se 1 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 580891 = 871337) B871337
theorem B876167 : Blo 151794 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B515807 : Blo 151794 515807 := bstep (se 1 (by rfl) ⟨386855, by rfl⟩ : syracuseStep 515807 = 773711) B773711
theorem B155495 : Blo 151794 155495 := bstep (se 1 (by rfl) ⟨116621, by rfl⟩ : syracuseStep 155495 = 233243) B233243
theorem B1106075 : Blo 151794 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B1958255 : Blo 151794 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B385631 : Blo 151794 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B517211 : Blo 151794 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B31975033 : Blo 151794 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1042415 : Blo 151794 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B387119 : Blo 151794 387119 := bstep (se 1 (by rfl) ⟨290339, by rfl⟩ : syracuseStep 387119 = 580679) B580679
theorem B585083 : Blo 151794 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B486847 : Blo 151794 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B1109477 : Blo 151794 1109477 := bstep (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) B208027
theorem B552577 : Blo 151794 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B257951 : Blo 151794 257951 := bstep (se 1 (by rfl) ⟨193463, by rfl⟩ : syracuseStep 257951 = 386927) B386927
theorem B1176119 : Blo 151794 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B291433 : Blo 151794 291433 := bstep (se 2 (by rfl) ⟨109287, by rfl⟩ : syracuseStep 291433 = 218575) B218575
theorem B521099 : Blo 151794 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B226559 : Blo 151794 226559 := bstep (se 1 (by rfl) ⟨169919, by rfl⟩ : syracuseStep 226559 = 339839) B339839
theorem B292223 : Blo 151794 292223 := bstep (se 1 (by rfl) ⟨219167, by rfl⟩ : syracuseStep 292223 = 438335) B438335
theorem B521855 : Blo 151794 521855 := bstep (se 1 (by rfl) ⟨391391, by rfl⟩ : syracuseStep 521855 = 782783) B782783
theorem B2029495 : Blo 151794 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B784403 : Blo 151794 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B292967 : Blo 151794 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B4422113 : Blo 151794 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B1112591 : Blo 151794 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B1112705 : Blo 151794 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B228407 : Blo 151794 228407 := bstep (se 1 (by rfl) ⟨171305, by rfl⟩ : syracuseStep 228407 = 342611) B342611
theorem B195691 : Blo 151794 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B228905 : Blo 151794 228905 := bstep (se 2 (by rfl) ⟨85839, by rfl⟩ : syracuseStep 228905 = 171679) B171679
theorem B294607 : Blo 151794 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B229115 : Blo 151794 229115 := bstep (se 1 (by rfl) ⟨171836, by rfl⟩ : syracuseStep 229115 = 343673) B343673
theorem B491615 : Blo 151794 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B2949533 : Blo 151794 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B229943 : Blo 151794 229943 := bstep (se 1 (by rfl) ⟨172457, by rfl⟩ : syracuseStep 229943 = 344915) B344915
theorem B295579 : Blo 151794 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B4981421 : Blo 151794 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B492409 : Blo 151794 492409 := bstep (se 2 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 492409 = 369307) B369307
theorem B230711 : Blo 151794 230711 := bstep (se 1 (by rfl) ⟨173033, by rfl⟩ : syracuseStep 230711 = 346067) B346067
theorem B230783 : Blo 151794 230783 := bstep (se 1 (by rfl) ⟨173087, by rfl⟩ : syracuseStep 230783 = 346175) B346175
theorem B820691 : Blo 151794 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B231335 : Blo 151794 231335 := bstep (se 1 (by rfl) ⟨173501, by rfl⟩ : syracuseStep 231335 = 347003) B347003
theorem B231419 : Blo 151794 231419 := bstep (se 1 (by rfl) ⟨173564, by rfl⟩ : syracuseStep 231419 = 347129) B347129
theorem B42633377 : Blo 151794 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B231743 : Blo 151794 231743 := bstep (se 1 (by rfl) ⟨173807, by rfl⟩ : syracuseStep 231743 = 347615) B347615
theorem B887273 : Blo 151794 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B2984435 : Blo 151794 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B625801 : Blo 151794 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B233513 : Blo 151794 233513 := bstep (se 2 (by rfl) ⟨87567, by rfl⟩ : syracuseStep 233513 = 175135) B175135
theorem B464123 : Blo 151794 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B660919 : Blo 151794 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B2955527 : Blo 151794 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B694943 : Blo 151794 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B990893 : Blo 151794 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B171967 : Blo 151794 171967 := bstep (se 1 (by rfl) ⟨128975, by rfl⟩ : syracuseStep 171967 = 257951) B257951
theorem B205211 : Blo 151794 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B174811 : Blo 151794 174811 := bstep (se 1 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 174811 = 262217) B262217
theorem B1158137 : Blo 151794 1158137 := bstep (se 2 (by rfl) ⟨434301, by rfl⟩ : syracuseStep 1158137 = 868603) B868603
theorem B1322041 : Blo 151794 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B1257245 : Blo 151794 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B12463955 : Blo 151794 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B733693 : Blo 151794 733693 := bstep (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) B275135
theorem B439577 : Blo 151794 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B604157 : Blo 151794 604157 := bstep (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) B226559
theorem B24394391 : Blo 151794 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B507179 : Blo 151794 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B736769 : Blo 151794 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B343871 : Blo 151794 343871 := bstep (se 1 (by rfl) ⟨257903, by rfl⟩ : syracuseStep 343871 = 515807) B515807
theorem B1490987 : Blo 151794 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B376987 : Blo 151794 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B245935 : Blo 151794 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B3784967 : Blo 151794 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B4244071 : Blo 151794 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B344807 : Blo 151794 344807 := bstep (se 1 (by rfl) ⟨258605, by rfl⟩ : syracuseStep 344807 = 517211) B517211
theorem B739651 : Blo 151794 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B2705993 : Blo 151794 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B347399 : Blo 151794 347399 := bstep (se 1 (by rfl) ⟨260549, by rfl⟩ : syracuseStep 347399 = 521099) B521099
theorem B577277 : Blo 151794 577277 := bstep (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) B216479
theorem B347903 : Blo 151794 347903 := bstep (se 1 (by rfl) ⟨260927, by rfl⟩ : syracuseStep 347903 = 521855) B521855
theorem B741727 : Blo 151794 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B774521 : Blo 151794 774521 := bstep (se 2 (by rfl) ⟨290445, by rfl⟩ : syracuseStep 774521 = 580891) B580891
theorem B1462693 : Blo 151794 1462693 := bstep (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) B274255
theorem B577961 : Blo 151794 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B741803 : Blo 151794 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B577975 : Blo 151794 577975 := bstep (se 1 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 577975 = 866963) B866963
theorem B4412069 : Blo 151794 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B152271 : Blo 151794 152271 := bstep (se 1 (by rfl) ⟨114203, by rfl⟩ : syracuseStep 152271 = 228407) B228407
theorem B4445077 : Blo 151794 4445077 := bstep (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) B208363
theorem B152603 : Blo 151794 152603 := bstep (se 1 (by rfl) ⟨114452, by rfl⟩ : syracuseStep 152603 = 228905) B228905
theorem B152743 : Blo 151794 152743 := bstep (se 1 (by rfl) ⟨114557, by rfl⟩ : syracuseStep 152743 = 229115) B229115
theorem B153039 : Blo 151794 153039 := bstep (se 1 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 153039 = 229559) B229559
theorem B153215 : Blo 151794 153215 := bstep (se 1 (by rfl) ⟨114911, by rfl⟩ : syracuseStep 153215 = 229823) B229823
theorem B349991 : Blo 151794 349991 := bstep (se 1 (by rfl) ⟨262493, by rfl⟩ : syracuseStep 349991 = 524987) B524987
theorem B1103827 : Blo 151794 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B153595 : Blo 151794 153595 := bstep (se 1 (by rfl) ⟨115196, by rfl⟩ : syracuseStep 153595 = 230393) B230393
theorem B350207 : Blo 151794 350207 := bstep (se 1 (by rfl) ⟨262655, by rfl⟩ : syracuseStep 350207 = 525311) B525311
theorem B153631 : Blo 151794 153631 := bstep (se 1 (by rfl) ⟨115223, by rfl⟩ : syracuseStep 153631 = 230447) B230447
theorem B153663 : Blo 151794 153663 := bstep (se 1 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 153663 = 230495) B230495
theorem B579919 : Blo 151794 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B154111 : Blo 151794 154111 := bstep (se 1 (by rfl) ⟨115583, by rfl⟩ : syracuseStep 154111 = 231167) B231167
theorem B4480343 : Blo 151794 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B548383 : Blo 151794 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B155419 : Blo 151794 155419 := bstep (se 1 (by rfl) ⟨116564, by rfl⟩ : syracuseStep 155419 = 233129) B233129
theorem B516239 : Blo 151794 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B3596831 : Blo 151794 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B549433 : Blo 151794 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B2220797 : Blo 151794 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B746263 : Blo 151794 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B649129 : Blo 151794 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B649403 : Blo 151794 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B584111 : Blo 151794 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B748399 : Blo 151794 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B1305503 : Blo 151794 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B257087 : Blo 151794 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B585185 : Blo 151794 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B388577 : Blo 151794 388577 := bstep (se 2 (by rfl) ⟨145716, by rfl⟩ : syracuseStep 388577 = 291433) B291433
theorem B290279 : Blo 151794 290279 := bstep (se 1 (by rfl) ⟨217709, by rfl⟩ : syracuseStep 290279 = 435419) B435419
theorem B258079 : Blo 151794 258079 := bstep (se 1 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 258079 = 387119) B387119
theorem B390055 : Blo 151794 390055 := bstep (se 1 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 390055 = 585083) B585083
theorem B1275425 : Blo 151794 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B784079 : Blo 151794 784079 := bstep (se 1 (by rfl) ⟨588059, by rfl⟩ : syracuseStep 784079 = 1176119) B1176119
theorem B882683 : Blo 151794 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B194815 : Blo 151794 194815 := bstep (se 1 (by rfl) ⟨146111, by rfl⟩ : syracuseStep 194815 = 292223) B292223
theorem B1735019 : Blo 151794 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B2947529 : Blo 151794 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B227807 : Blo 151794 227807 := bstep (se 1 (by rfl) ⟨170855, by rfl⟩ : syracuseStep 227807 = 341711) B341711
theorem B522935 : Blo 151794 522935 := bstep (se 1 (by rfl) ⟨392201, by rfl⟩ : syracuseStep 522935 = 784403) B784403
theorem B195311 : Blo 151794 195311 := bstep (se 1 (by rfl) ⟨146483, by rfl⟩ : syracuseStep 195311 = 292967) B292967
theorem B260921 : Blo 151794 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B2948075 : Blo 151794 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B228455 : Blo 151794 228455 := bstep (se 1 (by rfl) ⟨171341, by rfl⟩ : syracuseStep 228455 = 342683) B342683
theorem B228863 : Blo 151794 228863 := bstep (se 1 (by rfl) ⟨171647, by rfl⟩ : syracuseStep 228863 = 343295) B343295
theorem B392809 : Blo 151794 392809 := bstep (se 2 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 392809 = 294607) B294607
theorem B1343135 : Blo 151794 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B327743 : Blo 151794 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B2523311 : Blo 151794 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B1966355 : Blo 151794 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B229871 : Blo 151794 229871 := bstep (se 1 (by rfl) ⟨172403, by rfl⟩ : syracuseStep 229871 = 344807) B344807
theorem B394105 : Blo 151794 394105 := bstep (se 2 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 394105 = 295579) B295579
theorem B1311653 : Blo 151794 1311653 := bstep (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) B245935
theorem B656545 : Blo 151794 656545 := bstep (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) B492409
theorem B591515 : Blo 151794 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B1803995 : Blo 151794 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B231599 : Blo 151794 231599 := bstep (se 1 (by rfl) ⟨173699, by rfl⟩ : syracuseStep 231599 = 347399) B347399
theorem B231935 : Blo 151794 231935 := bstep (se 1 (by rfl) ⟨173951, by rfl⟩ : syracuseStep 231935 = 347903) B347903
theorem B986201 : Blo 151794 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B1576421 : Blo 151794 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B233081 : Blo 151794 233081 := bstep (se 2 (by rfl) ⟨87405, by rfl⟩ : syracuseStep 233081 = 174811) B174811
theorem B233327 : Blo 151794 233327 := bstep (se 1 (by rfl) ⟨174995, by rfl⟩ : syracuseStep 233327 = 349991) B349991
theorem B233471 : Blo 151794 233471 := bstep (se 1 (by rfl) ⟨175103, by rfl⟩ : syracuseStep 233471 = 350207) B350207
theorem B1970351 : Blo 151794 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B463295 : Blo 151794 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B2986895 : Blo 151794 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B660595 : Blo 151794 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B1611085 : Blo 151794 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B2397887 : Blo 151794 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B988969 : Blo 151794 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B1480531 : Blo 151794 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B432935 : Blo 151794 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B171391 : Blo 151794 171391 := bstep (se 1 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 171391 = 257087) B257087
theorem B1352477 : Blo 151794 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B1156679 : Blo 151794 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B16262927 : Blo 151794 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B173947 : Blo 151794 173947 := bstep (se 1 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 173947 = 260921) B260921
theorem B731177 : Blo 151794 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B895423 : Blo 151794 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B3975965 : Blo 151794 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B502649 : Blo 151794 502649 := bstep (se 2 (by rfl) ⟨188493, by rfl⟩ : syracuseStep 502649 = 376987) B376987
theorem B3320947 : Blo 151794 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B732577 : Blo 151794 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B995017 : Blo 151794 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B1978141 : Blo 151794 1978141 := bstep (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) B741803
theorem B28422251 : Blo 151794 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B865505 : Blo 151794 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B309415 : Blo 151794 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B997865 : Blo 151794 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B834401 : Blo 151794 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B344105 : Blo 151794 344105 := bstep (se 2 (by rfl) ⟨129039, by rfl⟩ : syracuseStep 344105 = 258079) B258079
theorem B344159 : Blo 151794 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B1950257 : Blo 151794 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B770633 : Blo 151794 770633 := bstep (se 2 (by rfl) ⟨288987, by rfl⟩ : syracuseStep 770633 = 577975) B577975
theorem B870335 : Blo 151794 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B772091 : Blo 151794 772091 := bstep (se 1 (by rfl) ⟨579068, by rfl⟩ : syracuseStep 772091 = 1158137) B1158137
theorem B838163 : Blo 151794 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B8309303 : Blo 151794 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B773225 : Blo 151794 773225 := bstep (se 2 (by rfl) ⟨289959, by rfl⟩ : syracuseStep 773225 = 579919) B579919
theorem B1560493 : Blo 151794 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B151871 : Blo 151794 151871 := bstep (se 1 (by rfl) ⟨113903, by rfl⟩ : syracuseStep 151871 = 227807) B227807
theorem B348623 : Blo 151794 348623 := bstep (se 1 (by rfl) ⟨261467, by rfl⟩ : syracuseStep 348623 = 522935) B522935
theorem B152303 : Blo 151794 152303 := bstep (se 1 (by rfl) ⟨114227, by rfl⟩ : syracuseStep 152303 = 228455) B228455
theorem B152575 : Blo 151794 152575 := bstep (se 1 (by rfl) ⟨114431, by rfl⟩ : syracuseStep 152575 = 228863) B228863
theorem B153295 : Blo 151794 153295 := bstep (se 1 (by rfl) ⟨114971, by rfl⟩ : syracuseStep 153295 = 229943) B229943
theorem B5658761 : Blo 151794 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B153807 : Blo 151794 153807 := bstep (se 1 (by rfl) ⟨115355, by rfl⟩ : syracuseStep 153807 = 230711) B230711
theorem B153855 : Blo 151794 153855 := bstep (se 1 (by rfl) ⟨115391, by rfl⟩ : syracuseStep 153855 = 230783) B230783
theorem B547127 : Blo 151794 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B547229 : Blo 151794 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B154223 : Blo 151794 154223 := bstep (se 1 (by rfl) ⟨115667, by rfl⟩ : syracuseStep 154223 = 231335) B231335
theorem B154279 : Blo 151794 154279 := bstep (se 1 (by rfl) ⟨115709, by rfl⟩ : syracuseStep 154279 = 231419) B231419
theorem B154495 : Blo 151794 154495 := bstep (se 1 (by rfl) ⟨115871, by rfl⟩ : syracuseStep 154495 = 231743) B231743
theorem B1989623 : Blo 151794 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B384851 : Blo 151794 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B155675 : Blo 151794 155675 := bstep (se 1 (by rfl) ⟨116756, by rfl⟩ : syracuseStep 155675 = 233513) B233513
theorem B516347 : Blo 151794 516347 := bstep (se 1 (by rfl) ⟨387260, by rfl⟩ : syracuseStep 516347 = 774521) B774521
theorem B385307 : Blo 151794 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B2941379 : Blo 151794 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1762721 : Blo 151794 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B978257 : Blo 151794 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B5926769 : Blo 151794 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B520073 : Blo 151794 520073 := bstep (se 2 (by rfl) ⟨195027, by rfl⟩ : syracuseStep 520073 = 390055) B390055
theorem B389407 : Blo 151794 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B881225 : Blo 151794 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B520829 : Blo 151794 520829 := bstep (se 3 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 520829 = 195311) B195311
theorem B259051 : Blo 151794 259051 := bstep (se 1 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 259051 = 388577) B388577
theorem B193519 : Blo 151794 193519 := bstep (se 1 (by rfl) ⟨145139, by rfl⟩ : syracuseStep 193519 = 290279) B290279
theorem B1471769 : Blo 151794 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B259753 : Blo 151794 259753 := bstep (se 2 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 259753 = 194815) B194815
theorem B293051 : Blo 151794 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B850283 : Blo 151794 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B522719 : Blo 151794 522719 := bstep (se 1 (by rfl) ⟨392039, by rfl⟩ : syracuseStep 522719 = 784079) B784079
theorem B588455 : Blo 151794 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B1965019 : Blo 151794 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B1965383 : Blo 151794 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B523745 : Blo 151794 523745 := bstep (se 2 (by rfl) ⟨196404, by rfl⟩ : syracuseStep 523745 = 392809) B392809
theorem B491179 : Blo 151794 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B229247 : Blo 151794 229247 := bstep (se 1 (by rfl) ⟨171935, by rfl⟩ : syracuseStep 229247 = 343871) B343871
theorem B229289 : Blo 151794 229289 := bstep (se 2 (by rfl) ⟨85983, by rfl⟩ : syracuseStep 229289 = 171967) B171967
theorem B229403 : Blo 151794 229403 := bstep (se 1 (by rfl) ⟨172052, by rfl⟩ : syracuseStep 229403 = 344105) B344105
theorem B229439 : Blo 151794 229439 := bstep (se 1 (by rfl) ⟨172079, by rfl⟩ : syracuseStep 229439 = 344159) B344159
theorem B1310903 : Blo 151794 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B394343 : Blo 151794 394343 := bstep (se 1 (by rfl) ⟨295757, by rfl⟩ : syracuseStep 394343 = 591515) B591515
theorem B525473 : Blo 151794 525473 := bstep (se 2 (by rfl) ⟨197052, by rfl⟩ : syracuseStep 525473 = 394105) B394105
theorem B558775 : Blo 151794 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B5539535 : Blo 151794 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B657467 : Blo 151794 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B3606605 : Blo 151794 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B1050947 : Blo 151794 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B231929 : Blo 151794 231929 := bstep (se 2 (by rfl) ⟨86973, by rfl⟩ : syracuseStep 231929 = 173947) B173947
theorem B1313567 : Blo 151794 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B232415 : Blo 151794 232415 := bstep (se 1 (by rfl) ⟨174311, by rfl⟩ : syracuseStep 232415 = 348623) B348623
theorem B3772507 : Blo 151794 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B4427929 : Blo 151794 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B364751 : Blo 151794 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B364819 : Blo 151794 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B335099 : Blo 151794 335099 := bstep (se 1 (by rfl) ⟨251324, by rfl⟩ : syracuseStep 335099 = 502649) B502649
theorem B1318625 : Blo 151794 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B1974041 : Blo 151794 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B18948167 : Blo 151794 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B566855 : Blo 151794 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B665243 : Blo 151794 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B1682207 : Blo 151794 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B308863 : Blo 151794 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B1193897 : Blo 151794 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1326415 : Blo 151794 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B1326689 : Blo 151794 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B2637521 : Blo 151794 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B2080657 : Blo 151794 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B344231 : Blo 151794 344231 := bstep (se 1 (by rfl) ⟨258173, by rfl⟩ : syracuseStep 344231 = 516347) B516347
theorem B771119 : Blo 151794 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B345401 : Blo 151794 345401 := bstep (se 2 (by rfl) ⟨129525, by rfl⟩ : syracuseStep 345401 = 259051) B259051
theorem B2148113 : Blo 151794 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B346337 : Blo 151794 346337 := bstep (se 2 (by rfl) ⟨129876, by rfl⟩ : syracuseStep 346337 = 259753) B259753
theorem B3951179 : Blo 151794 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B346715 : Blo 151794 346715 := bstep (se 1 (by rfl) ⟨260036, by rfl⟩ : syracuseStep 346715 = 520073) B520073
theorem B412553 : Blo 151794 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B347219 : Blo 151794 347219 := bstep (se 1 (by rfl) ⟨260414, by rfl⟩ : syracuseStep 347219 = 520829) B520829
theorem B577003 : Blo 151794 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B348479 : Blo 151794 348479 := bstep (se 1 (by rfl) ⟨261359, by rfl⟩ : syracuseStep 348479 = 522719) B522719
theorem B349163 : Blo 151794 349163 := bstep (se 1 (by rfl) ⟨261872, by rfl⟩ : syracuseStep 349163 = 523745) B523745
theorem B152831 : Blo 151794 152831 := bstep (se 1 (by rfl) ⟨114623, by rfl⟩ : syracuseStep 152831 = 229247) B229247
theorem B152859 : Blo 151794 152859 := bstep (se 1 (by rfl) ⟨114644, by rfl⟩ : syracuseStep 152859 = 229289) B229289
theorem B218495 : Blo 151794 218495 := bstep (se 1 (by rfl) ⟨163871, by rfl⟩ : syracuseStep 218495 = 327743) B327743
theorem B153247 : Blo 151794 153247 := bstep (se 1 (by rfl) ⟨114935, by rfl⟩ : syracuseStep 153247 = 229871) B229871
theorem B1300171 : Blo 151794 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B513755 : Blo 151794 513755 := bstep (se 1 (by rfl) ⟨385316, by rfl⟩ : syracuseStep 513755 = 770633) B770633
theorem B874435 : Blo 151794 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B1202663 : Blo 151794 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B580223 : Blo 151794 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B514727 : Blo 151794 514727 := bstep (se 1 (by rfl) ⟨386045, by rfl⟩ : syracuseStep 514727 = 772091) B772091
theorem B154399 : Blo 151794 154399 := bstep (se 1 (by rfl) ⟨115799, by rfl⟩ : syracuseStep 154399 = 231599) B231599
theorem B875393 : Blo 151794 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B154623 : Blo 151794 154623 := bstep (se 1 (by rfl) ⟨115967, by rfl⟩ : syracuseStep 154623 = 231935) B231935
theorem B515483 : Blo 151794 515483 := bstep (se 1 (by rfl) ⟨386612, by rfl⟩ : syracuseStep 515483 = 773225) B773225
theorem B155387 : Blo 151794 155387 := bstep (se 1 (by rfl) ⟨116540, by rfl⟩ : syracuseStep 155387 = 233081) B233081
theorem B155551 : Blo 151794 155551 := bstep (se 1 (by rfl) ⟨116663, by rfl⟩ : syracuseStep 155551 = 233327) B233327
theorem B155647 : Blo 151794 155647 := bstep (se 1 (by rfl) ⟨116735, by rfl⟩ : syracuseStep 155647 = 233471) B233471
theorem B1991263 : Blo 151794 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B1598591 : Blo 151794 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B288623 : Blo 151794 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B976769 : Blo 151794 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B256567 : Blo 151794 256567 := bstep (se 1 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 256567 = 384851) B384851
theorem B256871 : Blo 151794 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B1960919 : Blo 151794 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B519209 : Blo 151794 519209 := bstep (se 2 (by rfl) ⟨194703, by rfl⟩ : syracuseStep 519209 = 389407) B389407
theorem B1175147 : Blo 151794 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B10841951 : Blo 151794 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B258025 : Blo 151794 258025 := bstep (se 2 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 258025 = 193519) B193519
theorem B487451 : Blo 151794 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B880793 : Blo 151794 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B2650643 : Blo 151794 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B652171 : Blo 151794 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B2225069 : Blo 151794 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B587483 : Blo 151794 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B981179 : Blo 151794 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B2620025 : Blo 151794 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B195367 : Blo 151794 195367 := bstep (se 1 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 195367 = 293051) B293051
theorem B392303 : Blo 151794 392303 := bstep (se 1 (by rfl) ⟨294227, by rfl⟩ : syracuseStep 392303 = 588455) B588455
theorem B228521 : Blo 151794 228521 := bstep (se 2 (by rfl) ⟨85695, by rfl⟩ : syracuseStep 228521 = 171391) B171391
theorem B1310255 : Blo 151794 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B654905 : Blo 151794 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B229487 : Blo 151794 229487 := bstep (se 1 (by rfl) ⟨172115, by rfl⟩ : syracuseStep 229487 = 344231) B344231
theorem B262895 : Blo 151794 262895 := bstep (se 1 (by rfl) ⟨197171, by rfl⟩ : syracuseStep 262895 = 394343) B394343
theorem B2655017 : Blo 151794 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B230267 : Blo 151794 230267 := bstep (se 1 (by rfl) ⟨172700, by rfl⟩ : syracuseStep 230267 = 345401) B345401
theorem B230891 : Blo 151794 230891 := bstep (se 1 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 230891 = 346337) B346337
theorem B231143 : Blo 151794 231143 := bstep (se 1 (by rfl) ⟨173357, by rfl⟩ : syracuseStep 231143 = 346715) B346715
theorem B231479 : Blo 151794 231479 := bstep (se 1 (by rfl) ⟨173609, by rfl⟩ : syracuseStep 231479 = 347219) B347219
theorem B232319 : Blo 151794 232319 := bstep (se 1 (by rfl) ⟨174239, by rfl⟩ : syracuseStep 232319 = 348479) B348479
theorem B232775 : Blo 151794 232775 := bstep (se 1 (by rfl) ⟨174581, by rfl⟩ : syracuseStep 232775 = 349163) B349163
theorem B3183725 : Blo 151794 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B1316027 : Blo 151794 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1121471 : Blo 151794 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B171247 : Blo 151794 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B1483379 : Blo 151794 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B1746683 : Blo 151794 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B436603 : Blo 151794 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B438311 : Blo 151794 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B2404403 : Blo 151794 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B700631 : Blo 151794 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B2634119 : Blo 151794 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B275035 : Blo 151794 275035 := bstep (se 1 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 275035 = 412553) B412553
theorem B243167 : Blo 151794 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B342089 : Blo 151794 342089 := bstep (se 2 (by rfl) ⟨128283, by rfl⟩ : syracuseStep 342089 = 256567) B256567
theorem B342503 : Blo 151794 342503 := bstep (se 1 (by rfl) ⟨256877, by rfl⟩ : syracuseStep 342503 = 513755) B513755
theorem B801775 : Blo 151794 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B343151 : Blo 151794 343151 := bstep (se 1 (by rfl) ⟨257363, by rfl⟩ : syracuseStep 343151 = 514727) B514727
theorem B769337 : Blo 151794 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B343655 : Blo 151794 343655 := bstep (se 1 (by rfl) ⟨257741, by rfl⟩ : syracuseStep 343655 = 515483) B515483
theorem B769661 : Blo 151794 769661 := bstep (se 3 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 769661 = 288623) B288623
theorem B344033 : Blo 151794 344033 := bstep (se 2 (by rfl) ⟨129012, by rfl⟩ : syracuseStep 344033 = 258025) B258025
theorem B12632111 : Blo 151794 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B5030009 : Blo 151794 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B1065727 : Blo 151794 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B377903 : Blo 151794 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B443495 : Blo 151794 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B869561 : Blo 151794 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B346139 : Blo 151794 346139 := bstep (se 1 (by rfl) ⟨259604, by rfl⟩ : syracuseStep 346139 = 519209) B519209
theorem B411817 : Blo 151794 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B7227967 : Blo 151794 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B1165913 : Blo 151794 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B11096837 : Blo 151794 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B152347 : Blo 151794 152347 := bstep (se 1 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 152347 = 228521) B228521
theorem B873503 : Blo 151794 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B1758347 : Blo 151794 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B152935 : Blo 151794 152935 := bstep (se 1 (by rfl) ⟨114701, by rfl⟩ : syracuseStep 152935 = 229403) B229403
theorem B152959 : Blo 151794 152959 := bstep (se 1 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 152959 = 229439) B229439
theorem B873935 : Blo 151794 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B514079 : Blo 151794 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B350315 : Blo 151794 350315 := bstep (se 1 (by rfl) ⟨262736, by rfl⟩ : syracuseStep 350315 = 525473) B525473
theorem B23615621 : Blo 151794 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B3693023 : Blo 151794 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B1432075 : Blo 151794 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B154619 : Blo 151794 154619 := bstep (se 1 (by rfl) ⟨115964, by rfl⟩ : syracuseStep 154619 = 231929) B231929
theorem B875711 : Blo 151794 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B154943 : Blo 151794 154943 := bstep (se 1 (by rfl) ⟨116207, by rfl⟩ : syracuseStep 154943 = 232415) B232415
theorem B745033 : Blo 151794 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B582653 : Blo 151794 582653 := bstep (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) B218495
theorem B386815 : Blo 151794 386815 := bstep (se 1 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 386815 = 580223) B580223
theorem B583595 : Blo 151794 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B223399 : Blo 151794 223399 := bstep (se 1 (by rfl) ⟨167549, by rfl⟩ : syracuseStep 223399 = 335099) B335099
theorem B879083 : Blo 151794 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B486425 : Blo 151794 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B651179 : Blo 151794 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B1307279 : Blo 151794 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1733561 : Blo 151794 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B783431 : Blo 151794 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B324967 : Blo 151794 324967 := bstep (se 1 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 324967 = 487451) B487451
theorem B587195 : Blo 151794 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B1767095 : Blo 151794 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B260489 : Blo 151794 260489 := bstep (se 2 (by rfl) ⟨97683, by rfl⟩ : syracuseStep 260489 = 195367) B195367
theorem B391655 : Blo 151794 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B654119 : Blo 151794 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B1768553 : Blo 151794 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B261535 : Blo 151794 261535 := bstep (se 1 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 261535 = 392303) B392303
theorem B884459 : Blo 151794 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B8421407 : Blo 151794 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B1770011 : Blo 151794 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B295663 : Blo 151794 295663 := bstep (se 1 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 295663 = 443495) B443495
theorem B230759 : Blo 151794 230759 := bstep (se 1 (by rfl) ⟨173069, by rfl⟩ : syracuseStep 230759 = 346139) B346139
theorem B297865 : Blo 151794 297865 := bstep (se 2 (by rfl) ⟨111699, by rfl⟩ : syracuseStep 297865 = 223399) B223399
theorem B9637289 : Blo 151794 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B233543 : Blo 151794 233543 := bstep (se 1 (by rfl) ⟨175157, by rfl⟩ : syracuseStep 233543 = 350315) B350315
theorem B2462015 : Blo 151794 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B2593781 : Blo 151794 2593781 := bstep (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) B243167
theorem B988919 : Blo 151794 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B366713 : Blo 151794 366713 := bstep (se 2 (by rfl) ⟨137517, by rfl⟩ : syracuseStep 366713 = 275035) B275035
theorem B433289 : Blo 151794 433289 := bstep (se 2 (by rfl) ⟨162483, by rfl⟩ : syracuseStep 433289 = 324967) B324967
theorem B467087 : Blo 151794 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B1155707 : Blo 151794 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B1909433 : Blo 151794 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B173659 : Blo 151794 173659 := bstep (se 1 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 173659 = 260489) B260489
theorem B436079 : Blo 151794 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B993377 : Blo 151794 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B3353339 : Blo 151794 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B5683877 : Blo 151794 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B342719 : Blo 151794 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B15743747 : Blo 151794 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B1164455 : Blo 151794 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B2804213 : Blo 151794 2804213 := bstep (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) B262895
theorem B1297133 : Blo 151794 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B1756079 : Blo 151794 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B871519 : Blo 151794 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B1069033 : Blo 151794 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B348713 : Blo 151794 348713 := bstep (se 2 (by rfl) ⟨130767, by rfl⟩ : syracuseStep 348713 = 261535) B261535
theorem B512891 : Blo 151794 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B513107 : Blo 151794 513107 := bstep (se 1 (by rfl) ⟨384830, by rfl⟩ : syracuseStep 513107 = 769661) B769661
theorem B152991 : Blo 151794 152991 := bstep (se 1 (by rfl) ⟨114743, by rfl⟩ : syracuseStep 152991 = 229487) B229487
theorem B1168829 : Blo 151794 1168829 := bstep (se 3 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 1168829 = 438311) B438311
theorem B153511 : Blo 151794 153511 := bstep (se 1 (by rfl) ⟨115133, by rfl⟩ : syracuseStep 153511 = 230267) B230267
theorem B251935 : Blo 151794 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B579707 : Blo 151794 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B153927 : Blo 151794 153927 := bstep (se 1 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 153927 = 230891) B230891
theorem B154095 : Blo 151794 154095 := bstep (se 1 (by rfl) ⟨115571, by rfl⟩ : syracuseStep 154095 = 231143) B231143
theorem B154319 : Blo 151794 154319 := bstep (se 1 (by rfl) ⟨115739, by rfl⟩ : syracuseStep 154319 = 231479) B231479
theorem B777275 : Blo 151794 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B154879 : Blo 151794 154879 := bstep (se 1 (by rfl) ⟨116159, by rfl⟩ : syracuseStep 154879 = 232319) B232319
theorem B155183 : Blo 151794 155183 := bstep (se 1 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 155183 = 232775) B232775
theorem B515753 : Blo 151794 515753 := bstep (se 2 (by rfl) ⟨193407, by rfl⟩ : syracuseStep 515753 = 386815) B386815
theorem B549089 : Blo 151794 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B582137 : Blo 151794 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B7397891 : Blo 151794 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B582335 : Blo 151794 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B2122483 : Blo 151794 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1172231 : Blo 151794 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B877351 : Blo 151794 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B582623 : Blo 151794 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B583807 : Blo 151794 583807 := bstep (se 1 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 583807 = 875711) B875711
theorem B747647 : Blo 151794 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B388435 : Blo 151794 388435 := bstep (se 1 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 388435 = 582653) B582653
theorem B389063 : Blo 151794 389063 := bstep (se 1 (by rfl) ⟨291797, by rfl⟩ : syracuseStep 389063 = 583595) B583595
theorem B586055 : Blo 151794 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B1602935 : Blo 151794 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B522287 : Blo 151794 522287 := bstep (se 1 (by rfl) ⟨391715, by rfl⟩ : syracuseStep 522287 = 783431) B783431
theorem B391463 : Blo 151794 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B1178063 : Blo 151794 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B228059 : Blo 151794 228059 := bstep (se 1 (by rfl) ⟨171044, by rfl⟩ : syracuseStep 228059 = 342089) B342089
theorem B228329 : Blo 151794 228329 := bstep (se 2 (by rfl) ⟨85623, by rfl⟩ : syracuseStep 228329 = 171247) B171247
theorem B261103 : Blo 151794 261103 := bstep (se 1 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 261103 = 391655) B391655
theorem B228335 : Blo 151794 228335 := bstep (se 1 (by rfl) ⟨171251, by rfl⟩ : syracuseStep 228335 = 342503) B342503
theorem B1179035 : Blo 151794 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B228767 : Blo 151794 228767 := bstep (se 1 (by rfl) ⟨171575, by rfl⟩ : syracuseStep 228767 = 343151) B343151
theorem B229103 : Blo 151794 229103 := bstep (se 1 (by rfl) ⟨171827, by rfl⟩ : syracuseStep 229103 = 343655) B343655
theorem B1736477 : Blo 151794 1736477 := bstep (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) B651179
theorem B589639 : Blo 151794 589639 := bstep (se 1 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 589639 = 884459) B884459
theorem B229355 : Blo 151794 229355 := bstep (se 1 (by rfl) ⟨172016, by rfl⟩ : syracuseStep 229355 = 344033) B344033
theorem B1180007 : Blo 151794 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B1245565 : Blo 151794 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B5374613 : Blo 151794 5374613 := bstep (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) B251935
theorem B394217 : Blo 151794 394217 := bstep (se 2 (by rfl) ⟨147831, by rfl⟩ : syracuseStep 394217 = 295663) B295663
theorem B1869475 : Blo 151794 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B231545 : Blo 151794 231545 := bstep (se 2 (by rfl) ⟨86829, by rfl⟩ : syracuseStep 231545 = 173659) B173659
theorem B6424859 : Blo 151794 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B1641343 : Blo 151794 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B232475 : Blo 151794 232475 := bstep (se 1 (by rfl) ⟨174356, by rfl⟩ : syracuseStep 232475 = 348713) B348713
theorem B659279 : Blo 151794 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B397153 : Blo 151794 397153 := bstep (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) B297865
theorem B366059 : Blo 151794 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B662251 : Blo 151794 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B498431 : Blo 151794 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B2235559 : Blo 151794 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B10495831 : Blo 151794 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B1157651 : Blo 151794 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B5614271 : Blo 151794 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B2829977 : Blo 151794 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B864755 : Blo 151794 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B341927 : Blo 151794 341927 := bstep (se 1 (by rfl) ⟨256445, by rfl⟩ : syracuseStep 341927 = 512891) B512891
theorem B342071 : Blo 151794 342071 := bstep (se 1 (by rfl) ⟨256553, by rfl⟩ : syracuseStep 342071 = 513107) B513107
theorem B244475 : Blo 151794 244475 := bstep (se 1 (by rfl) ⟨183356, by rfl⟩ : syracuseStep 244475 = 366713) B366713
theorem B1162025 : Blo 151794 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B343835 : Blo 151794 343835 := bstep (se 1 (by rfl) ⟨257876, by rfl⟩ : syracuseStep 343835 = 515753) B515753
theorem B1425377 : Blo 151794 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B4931927 : Blo 151794 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B770471 : Blo 151794 770471 := bstep (se 1 (by rfl) ⟨577853, by rfl⟩ : syracuseStep 770471 = 1155707) B1155707
theorem B1068623 : Blo 151794 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B348137 : Blo 151794 348137 := bstep (se 2 (by rfl) ⟨130551, by rfl⟩ : syracuseStep 348137 = 261103) B261103
theorem B348191 : Blo 151794 348191 := bstep (se 1 (by rfl) ⟨261143, by rfl⟩ : syracuseStep 348191 = 522287) B522287
theorem B3789251 : Blo 151794 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B152039 : Blo 151794 152039 := bstep (se 1 (by rfl) ⟨114029, by rfl⟩ : syracuseStep 152039 = 228059) B228059
theorem B152219 : Blo 151794 152219 := bstep (se 1 (by rfl) ⟨114164, by rfl⟩ : syracuseStep 152219 = 228329) B228329
theorem B152223 : Blo 151794 152223 := bstep (se 1 (by rfl) ⟨114167, by rfl⟩ : syracuseStep 152223 = 228335) B228335
theorem B152511 : Blo 151794 152511 := bstep (se 1 (by rfl) ⟨114383, by rfl⟩ : syracuseStep 152511 = 228767) B228767
theorem B152735 : Blo 151794 152735 := bstep (se 1 (by rfl) ⟨114551, by rfl⟩ : syracuseStep 152735 = 229103) B229103
theorem B152903 : Blo 151794 152903 := bstep (se 1 (by rfl) ⟨114677, by rfl⟩ : syracuseStep 152903 = 229355) B229355
theorem B776303 : Blo 151794 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B153839 : Blo 151794 153839 := bstep (se 1 (by rfl) ⟨115379, by rfl⟩ : syracuseStep 153839 = 230759) B230759
theorem B1169801 : Blo 151794 1169801 := bstep (se 2 (by rfl) ⟨438675, by rfl⟩ : syracuseStep 1169801 = 877351) B877351
theorem B1170719 : Blo 151794 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B155695 : Blo 151794 155695 := bstep (se 1 (by rfl) ⟨116771, by rfl⟩ : syracuseStep 155695 = 233543) B233543
theorem B778409 : Blo 151794 778409 := bstep (se 2 (by rfl) ⟨291903, by rfl⟩ : syracuseStep 778409 = 583807) B583807
theorem B1729187 : Blo 151794 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B779219 : Blo 151794 779219 := bstep (se 1 (by rfl) ⟨584414, by rfl⟩ : syracuseStep 779219 = 1168829) B1168829
theorem B386471 : Blo 151794 386471 := bstep (se 1 (by rfl) ⟨289853, by rfl⟩ : syracuseStep 386471 = 579707) B579707
theorem B517913 : Blo 151794 517913 := bstep (se 2 (by rfl) ⟨194217, by rfl⟩ : syracuseStep 517913 = 388435) B388435
theorem B518183 : Blo 151794 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B288859 : Blo 151794 288859 := bstep (se 1 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 288859 = 433289) B433289
theorem B388091 : Blo 151794 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B1272955 : Blo 151794 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B388223 : Blo 151794 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B781487 : Blo 151794 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B388415 : Blo 151794 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B290719 : Blo 151794 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B259375 : Blo 151794 259375 := bstep (se 1 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 259375 = 389063) B389063
theorem B390703 : Blo 151794 390703 := bstep (se 1 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 390703 = 586055) B586055
theorem B260975 : Blo 151794 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B785375 : Blo 151794 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B228479 : Blo 151794 228479 := bstep (se 1 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 228479 = 342719) B342719
theorem B786023 : Blo 151794 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B786185 : Blo 151794 786185 := bstep (se 2 (by rfl) ⟨294819, by rfl⟩ : syracuseStep 786185 = 589639) B589639
theorem B786671 : Blo 151794 786671 := bstep (se 1 (by rfl) ⟨590003, by rfl⟩ : syracuseStep 786671 = 1180007) B1180007
theorem B262811 : Blo 151794 262811 := bstep (se 1 (by rfl) ⟨197108, by rfl⟩ : syracuseStep 262811 = 394217) B394217
theorem B2492633 : Blo 151794 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B13994441 : Blo 151794 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B232091 : Blo 151794 232091 := bstep (se 1 (by rfl) ⟨174068, by rfl⟩ : syracuseStep 232091 = 348137) B348137
theorem B232127 : Blo 151794 232127 := bstep (se 1 (by rfl) ⟨174095, by rfl⟩ : syracuseStep 232127 = 348191) B348191
theorem B2526167 : Blo 151794 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B1152791 : Blo 151794 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B3742847 : Blo 151794 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B173983 : Blo 151794 173983 := bstep (se 1 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 173983 = 260975) B260975
theorem B3287951 : Blo 151794 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B14332301 : Blo 151794 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B439519 : Blo 151794 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B244039 : Blo 151794 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B345275 : Blo 151794 345275 := bstep (se 1 (by rfl) ⟨258956, by rfl⟩ : syracuseStep 345275 = 517913) B517913
theorem B345455 : Blo 151794 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B771767 : Blo 151794 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B345833 : Blo 151794 345833 := bstep (se 2 (by rfl) ⟨129687, by rfl⟩ : syracuseStep 345833 = 259375) B259375
theorem B1329149 : Blo 151794 1329149 := bstep (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) B498431
theorem B1886651 : Blo 151794 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B576503 : Blo 151794 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B2118149 : Blo 151794 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B774683 : Blo 151794 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B152319 : Blo 151794 152319 := bstep (se 1 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 152319 = 228479) B228479
theorem B513647 : Blo 151794 513647 := bstep (se 1 (by rfl) ⟨385235, by rfl⟩ : syracuseStep 513647 = 770471) B770471
theorem B1660753 : Blo 151794 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B154363 : Blo 151794 154363 := bstep (se 1 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 154363 = 231545) B231545
theorem B4283239 : Blo 151794 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B154983 : Blo 151794 154983 := bstep (se 1 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 154983 = 232475) B232475
theorem B712415 : Blo 151794 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B385145 : Blo 151794 385145 := bstep (se 2 (by rfl) ⟨144429, by rfl⟩ : syracuseStep 385145 = 288859) B288859
theorem B2188457 : Blo 151794 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B517535 : Blo 151794 517535 := bstep (se 1 (by rfl) ⟨388151, by rfl⟩ : syracuseStep 517535 = 776303) B776303
theorem B1697273 : Blo 151794 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B779867 : Blo 151794 779867 := bstep (se 1 (by rfl) ⟨584900, by rfl⟩ : syracuseStep 779867 = 1169801) B1169801
theorem B780479 : Blo 151794 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B387625 : Blo 151794 387625 := bstep (se 2 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 387625 = 290719) B290719
theorem B518939 : Blo 151794 518939 := bstep (se 1 (by rfl) ⟨389204, by rfl⟩ : syracuseStep 518939 = 778409) B778409
theorem B519479 : Blo 151794 519479 := bstep (se 1 (by rfl) ⟨389609, by rfl⟩ : syracuseStep 519479 = 779219) B779219
theorem B257647 : Blo 151794 257647 := bstep (se 1 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 257647 = 386471) B386471
theorem B258727 : Blo 151794 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B520937 : Blo 151794 520937 := bstep (se 2 (by rfl) ⟨195351, by rfl⟩ : syracuseStep 520937 = 390703) B390703
theorem B258815 : Blo 151794 258815 := bstep (se 1 (by rfl) ⟨194111, by rfl⟩ : syracuseStep 258815 = 388223) B388223
theorem B520991 : Blo 151794 520991 := bstep (se 1 (by rfl) ⟨390743, by rfl⟩ : syracuseStep 520991 = 781487) B781487
theorem B258943 : Blo 151794 258943 := bstep (se 1 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 258943 = 388415) B388415
theorem B883001 : Blo 151794 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B227951 : Blo 151794 227951 := bstep (se 1 (by rfl) ⟨170963, by rfl⟩ : syracuseStep 227951 = 341927) B341927
theorem B228047 : Blo 151794 228047 := bstep (se 1 (by rfl) ⟨171035, by rfl⟩ : syracuseStep 228047 = 342071) B342071
theorem B2980745 : Blo 151794 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B162983 : Blo 151794 162983 := bstep (se 1 (by rfl) ⟨122237, by rfl⟩ : syracuseStep 162983 = 244475) B244475
theorem B523583 : Blo 151794 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B524015 : Blo 151794 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B524123 : Blo 151794 524123 := bstep (se 1 (by rfl) ⟨393092, by rfl⟩ : syracuseStep 524123 = 786185) B786185
theorem B229223 : Blo 151794 229223 := bstep (se 1 (by rfl) ⟨171917, by rfl⟩ : syracuseStep 229223 = 343835) B343835
theorem B3801005 : Blo 151794 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B524447 : Blo 151794 524447 := bstep (se 1 (by rfl) ⟨393335, by rfl⟩ : syracuseStep 524447 = 786671) B786671
theorem B230183 : Blo 151794 230183 := bstep (se 1 (by rfl) ⟨172637, by rfl⟩ : syracuseStep 230183 = 345275) B345275
theorem B230303 : Blo 151794 230303 := bstep (se 1 (by rfl) ⟨172727, by rfl⟩ : syracuseStep 230303 = 345455) B345455
theorem B230555 : Blo 151794 230555 := bstep (se 1 (by rfl) ⟨172916, by rfl⟩ : syracuseStep 230555 = 345833) B345833
theorem B886099 : Blo 151794 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B231977 : Blo 151794 231977 := bstep (se 2 (by rfl) ⟨86991, by rfl⟩ : syracuseStep 231977 = 173983) B173983
theorem B1412099 : Blo 151794 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B2495231 : Blo 151794 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B434621 : Blo 151794 434621 := bstep (se 3 (by rfl) ⟨81491, by rfl⟩ : syracuseStep 434621 = 162983) B162983
theorem B172543 : Blo 151794 172543 := bstep (se 1 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 172543 = 258815) B258815
theorem B5710985 : Blo 151794 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B8857349 : Blo 151794 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B2534003 : Blo 151794 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B175207 : Blo 151794 175207 := bstep (se 1 (by rfl) ⟨131405, by rfl⟩ : syracuseStep 175207 = 262811) B262811
theorem B1257767 : Blo 151794 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1684111 : Blo 151794 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B342431 : Blo 151794 342431 := bstep (se 1 (by rfl) ⟨256823, by rfl⟩ : syracuseStep 342431 = 513647) B513647
theorem B768527 : Blo 151794 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B343529 : Blo 151794 343529 := bstep (se 2 (by rfl) ⟨128823, by rfl⟩ : syracuseStep 343529 = 257647) B257647
theorem B1458971 : Blo 151794 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B344969 : Blo 151794 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B345023 : Blo 151794 345023 := bstep (se 1 (by rfl) ⟨258767, by rfl⟩ : syracuseStep 345023 = 517535) B517535
theorem B1131515 : Blo 151794 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B345257 : Blo 151794 345257 := bstep (se 2 (by rfl) ⟨129471, by rfl⟩ : syracuseStep 345257 = 258943) B258943
theorem B345959 : Blo 151794 345959 := bstep (se 1 (by rfl) ⟨259469, by rfl⟩ : syracuseStep 345959 = 518939) B518939
theorem B346319 : Blo 151794 346319 := bstep (se 1 (by rfl) ⟨259739, by rfl⟩ : syracuseStep 346319 = 519479) B519479
theorem B9554867 : Blo 151794 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B347291 : Blo 151794 347291 := bstep (se 1 (by rfl) ⟨260468, by rfl⟩ : syracuseStep 347291 = 520937) B520937
theorem B347327 : Blo 151794 347327 := bstep (se 1 (by rfl) ⟨260495, by rfl⟩ : syracuseStep 347327 = 520991) B520991
theorem B151967 : Blo 151794 151967 := bstep (se 1 (by rfl) ⟨113975, by rfl⟩ : syracuseStep 151967 = 227951) B227951
theorem B152031 : Blo 151794 152031 := bstep (se 1 (by rfl) ⟨114023, by rfl⟩ : syracuseStep 152031 = 228047) B228047
theorem B1987163 : Blo 151794 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B349055 : Blo 151794 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B349343 : Blo 151794 349343 := bstep (se 1 (by rfl) ⟨262007, by rfl⟩ : syracuseStep 349343 = 524015) B524015
theorem B349415 : Blo 151794 349415 := bstep (se 1 (by rfl) ⟨262061, by rfl⟩ : syracuseStep 349415 = 524123) B524123
theorem B152815 : Blo 151794 152815 := bstep (se 1 (by rfl) ⟨114611, by rfl⟩ : syracuseStep 152815 = 229223) B229223
theorem B514511 : Blo 151794 514511 := bstep (se 1 (by rfl) ⟨385883, by rfl⟩ : syracuseStep 514511 = 771767) B771767
theorem B1661755 : Blo 151794 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B9329627 : Blo 151794 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B154727 : Blo 151794 154727 := bstep (se 1 (by rfl) ⟨116045, by rfl⟩ : syracuseStep 154727 = 232091) B232091
theorem B154751 : Blo 151794 154751 := bstep (se 1 (by rfl) ⟨116063, by rfl⟩ : syracuseStep 154751 = 232127) B232127
theorem B384335 : Blo 151794 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B516455 : Blo 151794 516455 := bstep (se 1 (by rfl) ⟨387341, by rfl⟩ : syracuseStep 516455 = 774683) B774683
theorem B516833 : Blo 151794 516833 := bstep (se 2 (by rfl) ⟨193812, by rfl⟩ : syracuseStep 516833 = 387625) B387625
theorem B256763 : Blo 151794 256763 := bstep (se 1 (by rfl) ⟨192572, by rfl⟩ : syracuseStep 256763 = 385145) B385145
theorem B519911 : Blo 151794 519911 := bstep (se 1 (by rfl) ⟨389933, by rfl⟩ : syracuseStep 519911 = 779867) B779867
theorem B520319 : Blo 151794 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B586025 : Blo 151794 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B2191967 : Blo 151794 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B325385 : Blo 151794 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B588667 : Blo 151794 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B1899773 : Blo 151794 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B229979 : Blo 151794 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B230015 : Blo 151794 230015 := bstep (se 1 (by rfl) ⟨172511, by rfl⟩ : syracuseStep 230015 = 345023) B345023
theorem B754343 : Blo 151794 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B230057 : Blo 151794 230057 := bstep (se 2 (by rfl) ⟨86271, by rfl⟩ : syracuseStep 230057 = 172543) B172543
theorem B230171 : Blo 151794 230171 := bstep (se 1 (by rfl) ⟨172628, by rfl⟩ : syracuseStep 230171 = 345257) B345257
theorem B230639 : Blo 151794 230639 := bstep (se 1 (by rfl) ⟨172979, by rfl⟩ : syracuseStep 230639 = 345959) B345959
theorem B230879 : Blo 151794 230879 := bstep (se 1 (by rfl) ⟨173159, by rfl⟩ : syracuseStep 230879 = 346319) B346319
theorem B1181465 : Blo 151794 1181465 := bstep (se 2 (by rfl) ⟨443049, by rfl⟩ : syracuseStep 1181465 = 886099) B886099
theorem B231527 : Blo 151794 231527 := bstep (se 1 (by rfl) ⟨173645, by rfl⟩ : syracuseStep 231527 = 347291) B347291
theorem B231551 : Blo 151794 231551 := bstep (se 1 (by rfl) ⟨173663, by rfl⟩ : syracuseStep 231551 = 347327) B347327
theorem B232703 : Blo 151794 232703 := bstep (se 1 (by rfl) ⟨174527, by rfl⟩ : syracuseStep 232703 = 349055) B349055
theorem B232895 : Blo 151794 232895 := bstep (se 1 (by rfl) ⟨174671, by rfl⟩ : syracuseStep 232895 = 349343) B349343
theorem B232943 : Blo 151794 232943 := bstep (se 1 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 232943 = 349415) B349415
theorem B233609 : Blo 151794 233609 := bstep (se 2 (by rfl) ⟨87603, by rfl⟩ : syracuseStep 233609 = 175207) B175207
theorem B3807323 : Blo 151794 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B5904899 : Blo 151794 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B171175 : Blo 151794 171175 := bstep (se 1 (by rfl) ⟨128381, by rfl⟩ : syracuseStep 171175 = 256763) B256763
theorem B24879005 : Blo 151794 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B6369911 : Blo 151794 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B1324775 : Blo 151794 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B343007 : Blo 151794 343007 := bstep (se 1 (by rfl) ⟨257255, by rfl⟩ : syracuseStep 343007 = 514511) B514511
theorem B344303 : Blo 151794 344303 := bstep (se 1 (by rfl) ⟨258227, by rfl⟩ : syracuseStep 344303 = 516455) B516455
theorem B344555 : Blo 151794 344555 := bstep (se 1 (by rfl) ⟨258416, by rfl⟩ : syracuseStep 344555 = 516833) B516833
theorem B2245481 : Blo 151794 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B1689335 : Blo 151794 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B346607 : Blo 151794 346607 := bstep (se 1 (by rfl) ⟨259955, by rfl⟩ : syracuseStep 346607 = 519911) B519911
theorem B346879 : Blo 151794 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B838511 : Blo 151794 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B1461311 : Blo 151794 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B2215673 : Blo 151794 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B216923 : Blo 151794 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B512351 : Blo 151794 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B1266515 : Blo 151794 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B349631 : Blo 151794 349631 := bstep (se 1 (by rfl) ⟨262223, by rfl⟩ : syracuseStep 349631 = 524447) B524447
theorem B972647 : Blo 151794 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B153455 : Blo 151794 153455 := bstep (se 1 (by rfl) ⟨115091, by rfl⟩ : syracuseStep 153455 = 230183) B230183
theorem B153535 : Blo 151794 153535 := bstep (se 1 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 153535 = 230303) B230303
theorem B153703 : Blo 151794 153703 := bstep (se 1 (by rfl) ⟨115277, by rfl⟩ : syracuseStep 153703 = 230555) B230555
theorem B154651 : Blo 151794 154651 := bstep (se 1 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 154651 = 231977) B231977
theorem B941399 : Blo 151794 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B1663487 : Blo 151794 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B256223 : Blo 151794 256223 := bstep (se 1 (by rfl) ⟨192167, by rfl⟩ : syracuseStep 256223 = 384335) B384335
theorem B289747 : Blo 151794 289747 := bstep (se 1 (by rfl) ⟨217310, by rfl⟩ : syracuseStep 289747 = 434621) B434621
theorem B390683 : Blo 151794 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B784889 : Blo 151794 784889 := bstep (se 2 (by rfl) ⟨294333, by rfl⟩ : syracuseStep 784889 = 588667) B588667
theorem B228287 : Blo 151794 228287 := bstep (se 1 (by rfl) ⟨171215, by rfl⟩ : syracuseStep 228287 = 342431) B342431
theorem B229019 : Blo 151794 229019 := bstep (se 1 (by rfl) ⟨171764, by rfl⟩ : syracuseStep 229019 = 343529) B343529
theorem B229535 : Blo 151794 229535 := bstep (se 1 (by rfl) ⟨172151, by rfl⟩ : syracuseStep 229535 = 344303) B344303
theorem B229703 : Blo 151794 229703 := bstep (se 1 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 229703 = 344555) B344555
theorem B787643 : Blo 151794 787643 := bstep (se 1 (by rfl) ⟨590732, by rfl⟩ : syracuseStep 787643 = 1181465) B1181465
theorem B231071 : Blo 151794 231071 := bstep (se 1 (by rfl) ⟨173303, by rfl⟩ : syracuseStep 231071 = 346607) B346607
theorem B559007 : Blo 151794 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B1477115 : Blo 151794 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B233087 : Blo 151794 233087 := bstep (se 1 (by rfl) ⟨174815, by rfl⟩ : syracuseStep 233087 = 349631) B349631
theorem B462505 : Blo 151794 462505 := bstep (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) B346879
theorem B3936599 : Blo 151794 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B627599 : Blo 151794 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B16586003 : Blo 151794 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B170815 : Blo 151794 170815 := bstep (se 1 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 170815 = 256223) B256223
theorem B502895 : Blo 151794 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B1126223 : Blo 151794 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B341567 : Blo 151794 341567 := bstep (se 1 (by rfl) ⟨256175, by rfl⟩ : syracuseStep 341567 = 512351) B512351
theorem B2538215 : Blo 151794 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B4246607 : Blo 151794 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B152191 : Blo 151794 152191 := bstep (se 1 (by rfl) ⟨114143, by rfl⟩ : syracuseStep 152191 = 228287) B228287
theorem B578461 : Blo 151794 578461 := bstep (se 3 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 578461 = 216923) B216923
theorem B152679 : Blo 151794 152679 := bstep (se 1 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 152679 = 229019) B229019
theorem B153319 : Blo 151794 153319 := bstep (se 1 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 153319 = 229979) B229979
theorem B153343 : Blo 151794 153343 := bstep (se 1 (by rfl) ⟨115007, by rfl⟩ : syracuseStep 153343 = 230015) B230015
theorem B153371 : Blo 151794 153371 := bstep (se 1 (by rfl) ⟨115028, by rfl⟩ : syracuseStep 153371 = 230057) B230057
theorem B153447 : Blo 151794 153447 := bstep (se 1 (by rfl) ⟨115085, by rfl⟩ : syracuseStep 153447 = 230171) B230171
theorem B1496987 : Blo 151794 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B153759 : Blo 151794 153759 := bstep (se 1 (by rfl) ⟨115319, by rfl⟩ : syracuseStep 153759 = 230639) B230639
theorem B153919 : Blo 151794 153919 := bstep (se 1 (by rfl) ⟨115439, by rfl⟩ : syracuseStep 153919 = 230879) B230879
theorem B154351 : Blo 151794 154351 := bstep (se 1 (by rfl) ⟨115763, by rfl⟩ : syracuseStep 154351 = 231527) B231527
theorem B154367 : Blo 151794 154367 := bstep (se 1 (by rfl) ⟨115775, by rfl⟩ : syracuseStep 154367 = 231551) B231551
theorem B974207 : Blo 151794 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B155135 : Blo 151794 155135 := bstep (se 1 (by rfl) ⟨116351, by rfl⟩ : syracuseStep 155135 = 232703) B232703
theorem B155263 : Blo 151794 155263 := bstep (se 1 (by rfl) ⟨116447, by rfl⟩ : syracuseStep 155263 = 232895) B232895
theorem B155295 : Blo 151794 155295 := bstep (se 1 (by rfl) ⟨116471, by rfl⟩ : syracuseStep 155295 = 232943) B232943
theorem B155739 : Blo 151794 155739 := bstep (se 1 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 155739 = 233609) B233609
theorem B844343 : Blo 151794 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B648431 : Blo 151794 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B386329 : Blo 151794 386329 := bstep (se 2 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 386329 = 289747) B289747
theorem B1108991 : Blo 151794 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B260455 : Blo 151794 260455 := bstep (se 1 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 260455 = 390683) B390683
theorem B883183 : Blo 151794 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B228233 : Blo 151794 228233 := bstep (se 2 (by rfl) ⟨85587, by rfl⟩ : syracuseStep 228233 = 171175) B171175
theorem B523259 : Blo 151794 523259 := bstep (se 1 (by rfl) ⟨392444, by rfl⟩ : syracuseStep 523259 = 784889) B784889
theorem B228671 : Blo 151794 228671 := bstep (se 1 (by rfl) ⟨171503, by rfl⟩ : syracuseStep 228671 = 343007) B343007
theorem B525095 : Blo 151794 525095 := bstep (se 1 (by rfl) ⟨393821, by rfl⟩ : syracuseStep 525095 = 787643) B787643
theorem B984743 : Blo 151794 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B1673597 : Blo 151794 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B2624399 : Blo 151794 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B562895 : Blo 151794 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B432287 : Blo 151794 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B372671 : Blo 151794 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B2831071 : Blo 151794 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B997991 : Blo 151794 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B771281 : Blo 151794 771281 := bstep (se 2 (by rfl) ⟨289230, by rfl⟩ : syracuseStep 771281 = 578461) B578461
theorem B739327 : Blo 151794 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B347273 : Blo 151794 347273 := bstep (se 2 (by rfl) ⟨130227, by rfl⟩ : syracuseStep 347273 = 260455) B260455
theorem B1692143 : Blo 151794 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B152155 : Blo 151794 152155 := bstep (se 1 (by rfl) ⟨114116, by rfl⟩ : syracuseStep 152155 = 228233) B228233
theorem B348839 : Blo 151794 348839 := bstep (se 1 (by rfl) ⟨261629, by rfl⟩ : syracuseStep 348839 = 523259) B523259
theorem B152447 : Blo 151794 152447 := bstep (se 1 (by rfl) ⟨114335, by rfl⟩ : syracuseStep 152447 = 228671) B228671
theorem B153023 : Blo 151794 153023 := bstep (se 1 (by rfl) ⟨114767, by rfl⟩ : syracuseStep 153023 = 229535) B229535
theorem B153135 : Blo 151794 153135 := bstep (se 1 (by rfl) ⟨114851, by rfl⟩ : syracuseStep 153135 = 229703) B229703
theorem B154047 : Blo 151794 154047 := bstep (se 1 (by rfl) ⟨115535, by rfl⟩ : syracuseStep 154047 = 231071) B231071
theorem B515105 : Blo 151794 515105 := bstep (se 2 (by rfl) ⟨193164, by rfl⟩ : syracuseStep 515105 = 386329) B386329
theorem B155391 : Blo 151794 155391 := bstep (se 1 (by rfl) ⟨116543, by rfl⟩ : syracuseStep 155391 = 233087) B233087
theorem B44229341 : Blo 151794 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B616673 : Blo 151794 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B649471 : Blo 151794 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B750815 : Blo 151794 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B1341053 : Blo 151794 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B1177577 : Blo 151794 1177577 := bstep (se 2 (by rfl) ⟨441591, by rfl⟩ : syracuseStep 1177577 = 883183) B883183
theorem B227711 : Blo 151794 227711 := bstep (se 1 (by rfl) ⟨170783, by rfl⟩ : syracuseStep 227711 = 341567) B341567
theorem B227753 : Blo 151794 227753 := bstep (se 2 (by rfl) ⟨85407, by rfl⟩ : syracuseStep 227753 = 170815) B170815
theorem B656495 : Blo 151794 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B1115731 : Blo 151794 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B231515 : Blo 151794 231515 := bstep (se 1 (by rfl) ⟨173636, by rfl⟩ : syracuseStep 231515 = 347273) B347273
theorem B985769 : Blo 151794 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B232559 : Blo 151794 232559 := bstep (se 1 (by rfl) ⟨174419, by rfl⟩ : syracuseStep 232559 = 348839) B348839
theorem B3774761 : Blo 151794 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B500543 : Blo 151794 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B894035 : Blo 151794 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B665327 : Blo 151794 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B1749599 : Blo 151794 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B1128095 : Blo 151794 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B865961 : Blo 151794 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B375263 : Blo 151794 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B343403 : Blo 151794 343403 := bstep (se 1 (by rfl) ⟨257552, by rfl⟩ : syracuseStep 343403 = 515105) B515105
theorem B411115 : Blo 151794 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B248447 : Blo 151794 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B151807 : Blo 151794 151807 := bstep (se 1 (by rfl) ⟨113855, by rfl⟩ : syracuseStep 151807 = 227711) B227711
theorem B151835 : Blo 151794 151835 := bstep (se 1 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 151835 = 227753) B227753
theorem B350063 : Blo 151794 350063 := bstep (se 1 (by rfl) ⟨262547, by rfl⟩ : syracuseStep 350063 = 525095) B525095
theorem B514187 : Blo 151794 514187 := bstep (se 1 (by rfl) ⟨385640, by rfl⟩ : syracuseStep 514187 = 771281) B771281
theorem B288191 : Blo 151794 288191 := bstep (se 1 (by rfl) ⟨216143, by rfl⟩ : syracuseStep 288191 = 432287) B432287
theorem B29486227 : Blo 151794 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B785051 : Blo 151794 785051 := bstep (se 1 (by rfl) ⟨588788, by rfl⟩ : syracuseStep 785051 = 1177577) B1177577
theorem B657179 : Blo 151794 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B233375 : Blo 151794 233375 := bstep (se 1 (by rfl) ⟨175031, by rfl⟩ : syracuseStep 233375 = 350063) B350063
theorem B333695 : Blo 151794 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B662525 : Blo 151794 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B437663 : Blo 151794 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B1487641 : Blo 151794 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B342791 : Blo 151794 342791 := bstep (se 1 (by rfl) ⟨257093, by rfl⟩ : syracuseStep 342791 = 514187) B514187
theorem B443551 : Blo 151794 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B1166399 : Blo 151794 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B577307 : Blo 151794 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B250175 : Blo 151794 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B154343 : Blo 151794 154343 := bstep (se 1 (by rfl) ⟨115757, by rfl⟩ : syracuseStep 154343 = 231515) B231515
theorem B548153 : Blo 151794 548153 := bstep (se 2 (by rfl) ⟨205557, by rfl⟩ : syracuseStep 548153 = 411115) B411115
theorem B155039 : Blo 151794 155039 := bstep (se 1 (by rfl) ⟨116279, by rfl⟩ : syracuseStep 155039 = 232559) B232559
theorem B2384093 : Blo 151794 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B39314969 : Blo 151794 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B2516507 : Blo 151794 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B192127 : Blo 151794 192127 := bstep (se 1 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 192127 = 288191) B288191
theorem B752063 : Blo 151794 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B523367 : Blo 151794 523367 := bstep (se 1 (by rfl) ⟨392525, by rfl⟩ : syracuseStep 523367 = 785051) B785051
theorem B228935 : Blo 151794 228935 := bstep (se 1 (by rfl) ⟨171701, by rfl⟩ : syracuseStep 228935 = 343403) B343403
theorem B591401 : Blo 151794 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B365435 : Blo 151794 365435 := bstep (se 1 (by rfl) ⟨274076, by rfl⟩ : syracuseStep 365435 = 548153) B548153
theorem B1677671 : Blo 151794 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B2005501 : Blo 151794 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B667133 : Blo 151794 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B438119 : Blo 151794 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B441683 : Blo 151794 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B1589395 : Blo 151794 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1983521 : Blo 151794 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B348911 : Blo 151794 348911 := bstep (se 1 (by rfl) ⟨261683, by rfl⟩ : syracuseStep 348911 = 523367) B523367
theorem B152623 : Blo 151794 152623 := bstep (se 1 (by rfl) ⟨114467, by rfl⟩ : syracuseStep 152623 = 228935) B228935
theorem B777599 : Blo 151794 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B384871 : Blo 151794 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B155583 : Blo 151794 155583 := bstep (se 1 (by rfl) ⟨116687, by rfl⟩ : syracuseStep 155583 = 233375) B233375
theorem B222463 : Blo 151794 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B256169 : Blo 151794 256169 := bstep (se 2 (by rfl) ⟨96063, by rfl⟩ : syracuseStep 256169 = 192127) B192127
theorem B26209979 : Blo 151794 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B291775 : Blo 151794 291775 := bstep (se 1 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 291775 = 437663) B437663
theorem B228527 : Blo 151794 228527 := bstep (se 1 (by rfl) ⟨171395, by rfl⟩ : syracuseStep 228527 = 342791) B342791
theorem B394267 : Blo 151794 394267 := bstep (se 1 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 394267 = 591401) B591401
theorem B296617 : Blo 151794 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B232607 : Blo 151794 232607 := bstep (se 1 (by rfl) ⟨174455, by rfl⟩ : syracuseStep 232607 = 348911) B348911
theorem B1118447 : Blo 151794 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B170779 : Blo 151794 170779 := bstep (se 1 (by rfl) ⟨128084, by rfl⟩ : syracuseStep 170779 = 256169) B256169
theorem B17473319 : Blo 151794 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B1322347 : Blo 151794 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B243623 : Blo 151794 243623 := bstep (se 1 (by rfl) ⟨182717, by rfl⟩ : syracuseStep 243623 = 365435) B365435
theorem B444755 : Blo 151794 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B2674001 : Blo 151794 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B152351 : Blo 151794 152351 := bstep (se 1 (by rfl) ⟨114263, by rfl⟩ : syracuseStep 152351 = 228527) B228527
theorem B513161 : Blo 151794 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B2119193 : Blo 151794 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B518399 : Blo 151794 518399 := bstep (se 1 (by rfl) ⟨388799, by rfl⟩ : syracuseStep 518399 = 777599) B777599
theorem B389033 : Blo 151794 389033 := bstep (se 2 (by rfl) ⟨145887, by rfl⟩ : syracuseStep 389033 = 291775) B291775
theorem B292079 : Blo 151794 292079 := bstep (se 1 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 292079 = 438119) B438119
theorem B294455 : Blo 151794 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B525689 : Blo 151794 525689 := bstep (se 2 (by rfl) ⟨197133, by rfl⟩ : syracuseStep 525689 = 394267) B394267
theorem B296503 : Blo 151794 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B395489 : Blo 151794 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B1412795 : Blo 151794 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B1782667 : Blo 151794 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B342107 : Blo 151794 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B11648879 : Blo 151794 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B345599 : Blo 151794 345599 := bstep (se 1 (by rfl) ⟨259199, by rfl⟩ : syracuseStep 345599 = 518399) B518399
theorem B155071 : Blo 151794 155071 := bstep (se 1 (by rfl) ⟨116303, by rfl⟩ : syracuseStep 155071 = 232607) B232607
theorem B745631 : Blo 151794 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B1763129 : Blo 151794 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B259355 : Blo 151794 259355 := bstep (se 1 (by rfl) ⟨194516, by rfl⟩ : syracuseStep 259355 = 389033) B389033
theorem B194719 : Blo 151794 194719 := bstep (se 1 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 194719 = 292079) B292079
theorem B227705 : Blo 151794 227705 := bstep (se 2 (by rfl) ⟨85389, by rfl⟩ : syracuseStep 227705 = 170779) B170779
theorem B162415 : Blo 151794 162415 := bstep (se 1 (by rfl) ⟨121811, by rfl⟩ : syracuseStep 162415 = 243623) B243623
theorem B785213 : Blo 151794 785213 := bstep (se 3 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 785213 = 294455) B294455
theorem B230399 : Blo 151794 230399 := bstep (se 1 (by rfl) ⟨172799, by rfl⟩ : syracuseStep 230399 = 345599) B345599
theorem B6325397 : Blo 151794 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B9507557 : Blo 151794 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B497087 : Blo 151794 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B1054637 : Blo 151794 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B172903 : Blo 151794 172903 := bstep (se 1 (by rfl) ⟨129677, by rfl⟩ : syracuseStep 172903 = 259355) B259355
theorem B866213 : Blo 151794 866213 := bstep (se 4 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 866213 = 162415) B162415
theorem B151803 : Blo 151794 151803 := bstep (se 1 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 151803 = 227705) B227705
theorem B350459 : Blo 151794 350459 := bstep (se 1 (by rfl) ⟨262844, by rfl⟩ : syracuseStep 350459 = 525689) B525689
theorem B941863 : Blo 151794 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B1175419 : Blo 151794 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B259625 : Blo 151794 259625 := bstep (se 2 (by rfl) ⟨97359, by rfl⟩ : syracuseStep 259625 = 194719) B194719
theorem B228071 : Blo 151794 228071 := bstep (se 1 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 228071 = 342107) B342107
theorem B523475 : Blo 151794 523475 := bstep (se 1 (by rfl) ⟨392606, by rfl⟩ : syracuseStep 523475 = 785213) B785213
theorem B7765919 : Blo 151794 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B230537 : Blo 151794 230537 := bstep (se 2 (by rfl) ⟨86451, by rfl⟩ : syracuseStep 230537 = 172903) B172903
theorem B331391 : Blo 151794 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B233639 : Blo 151794 233639 := bstep (se 1 (by rfl) ⟨175229, by rfl⟩ : syracuseStep 233639 = 350459) B350459
theorem B173083 : Blo 151794 173083 := bstep (se 1 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 173083 = 259625) B259625
theorem B1255817 : Blo 151794 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B6338371 : Blo 151794 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B703091 : Blo 151794 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B577475 : Blo 151794 577475 := bstep (se 1 (by rfl) ⟨433106, by rfl⟩ : syracuseStep 577475 = 866213) B866213
theorem B152047 : Blo 151794 152047 := bstep (se 1 (by rfl) ⟨114035, by rfl⟩ : syracuseStep 152047 = 228071) B228071
theorem B348983 : Blo 151794 348983 := bstep (se 1 (by rfl) ⟨261737, by rfl⟩ : syracuseStep 348983 = 523475) B523475
theorem B153599 : Blo 151794 153599 := bstep (se 1 (by rfl) ⟨115199, by rfl⟩ : syracuseStep 153599 = 230399) B230399
theorem B4216931 : Blo 151794 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B1567225 : Blo 151794 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B5177279 : Blo 151794 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B230777 : Blo 151794 230777 := bstep (se 2 (by rfl) ⟨86541, by rfl⟩ : syracuseStep 230777 = 173083) B173083
theorem B232655 : Blo 151794 232655 := bstep (se 1 (by rfl) ⟨174491, by rfl⟩ : syracuseStep 232655 = 348983) B348983
theorem B1874909 : Blo 151794 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B13806077 : Blo 151794 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B837211 : Blo 151794 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B153691 : Blo 151794 153691 := bstep (se 1 (by rfl) ⟨115268, by rfl⟩ : syracuseStep 153691 = 230537) B230537
theorem B384983 : Blo 151794 384983 := bstep (se 1 (by rfl) ⟨288737, by rfl⟩ : syracuseStep 384983 = 577475) B577475
theorem B155759 : Blo 151794 155759 := bstep (se 1 (by rfl) ⟨116819, by rfl⟩ : syracuseStep 155759 = 233639) B233639
theorem B2089633 : Blo 151794 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B2811287 : Blo 151794 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B8451161 : Blo 151794 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B883709 : Blo 151794 883709 := bstep (se 3 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 883709 = 331391) B331391
theorem B2786177 : Blo 151794 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B1116281 : Blo 151794 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B1249939 : Blo 151794 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1874191 : Blo 151794 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B36816205 : Blo 151794 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B153851 : Blo 151794 153851 := bstep (se 1 (by rfl) ⟨115388, by rfl⟩ : syracuseStep 153851 = 230777) B230777
theorem B155103 : Blo 151794 155103 := bstep (se 1 (by rfl) ⟨116327, by rfl⟩ : syracuseStep 155103 = 232655) B232655
theorem B256655 : Blo 151794 256655 := bstep (se 1 (by rfl) ⟨192491, by rfl⟩ : syracuseStep 256655 = 384983) B384983
theorem B5634107 : Blo 151794 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B589139 : Blo 151794 589139 := bstep (se 1 (by rfl) ⟨441854, by rfl⟩ : syracuseStep 589139 = 883709) B883709
theorem B49088273 : Blo 151794 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B171103 : Blo 151794 171103 := bstep (se 1 (by rfl) ⟨128327, by rfl⟩ : syracuseStep 171103 = 256655) B256655
theorem B2498921 : Blo 151794 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B3756071 : Blo 151794 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B1857451 : Blo 151794 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B2976749 : Blo 151794 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B1666585 : Blo 151794 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B392759 : Blo 151794 392759 := bstep (se 1 (by rfl) ⟨294569, by rfl⟩ : syracuseStep 392759 = 589139) B589139
theorem B523608245 : Blo 151794 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B2504047 : Blo 151794 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B1984499 : Blo 151794 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B2476601 : Blo 151794 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B2222113 : Blo 151794 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B1665947 : Blo 151794 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B228137 : Blo 151794 228137 := bstep (se 2 (by rfl) ⟨85551, by rfl⟩ : syracuseStep 228137 = 171103) B171103
theorem B261839 : Blo 151794 261839 := bstep (se 1 (by rfl) ⟨196379, by rfl⟩ : syracuseStep 261839 = 392759) B392759
theorem B174559 : Blo 151794 174559 := bstep (se 1 (by rfl) ⟨130919, by rfl⟩ : syracuseStep 174559 = 261839) B261839
theorem B1322999 : Blo 151794 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B1651067 : Blo 151794 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B2962817 : Blo 151794 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B152091 : Blo 151794 152091 := bstep (se 1 (by rfl) ⟨114068, by rfl⟩ : syracuseStep 152091 = 228137) B228137
theorem B349072163 : Blo 151794 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B3338729 : Blo 151794 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B1110631 : Blo 151794 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B232745 : Blo 151794 232745 := bstep (se 2 (by rfl) ⟨87279, by rfl⟩ : syracuseStep 232745 = 174559) B174559
theorem B1480841 : Blo 151794 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B1975211 : Blo 151794 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B1100711 : Blo 151794 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B232714775 : Blo 151794 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B881999 : Blo 151794 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B2225819 : Blo 151794 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B987227 : Blo 151794 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B1316807 : Blo 151794 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B1483879 : Blo 151794 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B733807 : Blo 151794 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B155143183 : Blo 151794 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B155163 : Blo 151794 155163 := bstep (se 1 (by rfl) ⟨116372, by rfl⟩ : syracuseStep 155163 = 232745) B232745
theorem B587999 : Blo 151794 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B658151 : Blo 151794 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B1978505 : Blo 151794 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B877871 : Blo 151794 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B206857577 : Blo 151794 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B978409 : Blo 151794 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B391999 : Blo 151794 391999 := bstep (se 1 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 391999 = 587999) B587999
theorem B1319003 : Blo 151794 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B438767 : Blo 151794 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B137905051 : Blo 151794 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B1304545 : Blo 151794 1304545 := bstep (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) B978409
theorem B585247 : Blo 151794 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B522665 : Blo 151794 522665 := bstep (se 2 (by rfl) ⟨195999, by rfl⟩ : syracuseStep 522665 = 391999) B391999
theorem B1739393 : Blo 151794 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B183873401 : Blo 151794 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B348443 : Blo 151794 348443 := bstep (se 1 (by rfl) ⟨261332, by rfl⟩ : syracuseStep 348443 = 522665) B522665
theorem B780329 : Blo 151794 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B879335 : Blo 151794 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B292511 : Blo 151794 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B232295 : Blo 151794 232295 := bstep (se 1 (by rfl) ⟨174221, by rfl⟩ : syracuseStep 232295 = 348443) B348443
theorem B1159595 : Blo 151794 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B780029 : Blo 151794 780029 := bstep (se 3 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 780029 = 292511) B292511
theorem B520219 : Blo 151794 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B586223 : Blo 151794 586223 := bstep (se 1 (by rfl) ⟨439667, by rfl⟩ : syracuseStep 586223 = 879335) B879335
theorem B122582267 : Blo 151794 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B693625 : Blo 151794 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B773063 : Blo 151794 773063 := bstep (se 1 (by rfl) ⟨579797, by rfl⟩ : syracuseStep 773063 = 1159595) B1159595
theorem B154863 : Blo 151794 154863 := bstep (se 1 (by rfl) ⟨116147, by rfl⟩ : syracuseStep 154863 = 232295) B232295
theorem B520019 : Blo 151794 520019 := bstep (se 1 (by rfl) ⟨390014, by rfl⟩ : syracuseStep 520019 = 780029) B780029
theorem B390815 : Blo 151794 390815 := bstep (se 1 (by rfl) ⟨293111, by rfl⟩ : syracuseStep 390815 = 586223) B586223
theorem B81721511 : Blo 151794 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B924833 : Blo 151794 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B346679 : Blo 151794 346679 := bstep (se 1 (by rfl) ⟨260009, by rfl⟩ : syracuseStep 346679 = 520019) B520019
theorem B54481007 : Blo 151794 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B515375 : Blo 151794 515375 := bstep (se 1 (by rfl) ⟨386531, by rfl⟩ : syracuseStep 515375 = 773063) B773063
theorem B260543 : Blo 151794 260543 := bstep (se 1 (by rfl) ⟨195407, by rfl⟩ : syracuseStep 260543 = 390815) B390815
theorem B231119 : Blo 151794 231119 := bstep (se 1 (by rfl) ⟨173339, by rfl⟩ : syracuseStep 231119 = 346679) B346679
theorem B173695 : Blo 151794 173695 := bstep (se 1 (by rfl) ⟨130271, by rfl⟩ : syracuseStep 173695 = 260543) B260543
theorem B36320671 : Blo 151794 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B343583 : Blo 151794 343583 := bstep (se 1 (by rfl) ⟨257687, by rfl⟩ : syracuseStep 343583 = 515375) B515375
theorem B616555 : Blo 151794 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B231593 : Blo 151794 231593 := bstep (se 2 (by rfl) ⟨86847, by rfl⟩ : syracuseStep 231593 = 173695) B173695
theorem B822073 : Blo 151794 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B154079 : Blo 151794 154079 := bstep (se 1 (by rfl) ⟨115559, by rfl⟩ : syracuseStep 154079 = 231119) B231119
theorem B48427561 : Blo 151794 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B229055 : Blo 151794 229055 := bstep (se 1 (by rfl) ⟨171791, by rfl⟩ : syracuseStep 229055 = 343583) B343583
theorem B1096097 : Blo 151794 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B64570081 : Blo 151794 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B152703 : Blo 151794 152703 := bstep (se 1 (by rfl) ⟨114527, by rfl⟩ : syracuseStep 152703 = 229055) B229055
theorem B154395 : Blo 151794 154395 := bstep (se 1 (by rfl) ⟨115796, by rfl⟩ : syracuseStep 154395 = 231593) B231593
theorem B2922925 : Blo 151794 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B86093441 : Blo 151794 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B57395627 : Blo 151794 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B3897233 : Blo 151794 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B2598155 : Blo 151794 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B38263751 : Blo 151794 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B25509167 : Blo 151794 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B1732103 : Blo 151794 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B1154735 : Blo 151794 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B17006111 : Blo 151794 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B769823 : Blo 151794 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B11337407 : Blo 151794 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B7558271 : Blo 151794 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B513215 : Blo 151794 513215 := bstep (se 1 (by rfl) ⟨384911, by rfl⟩ : syracuseStep 513215 = 769823) B769823
theorem B342143 : Blo 151794 342143 := bstep (se 1 (by rfl) ⟨256607, by rfl⟩ : syracuseStep 342143 = 513215) B513215
theorem B5038847 : Blo 151794 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B3359231 : Blo 151794 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B228095 : Blo 151794 228095 := bstep (se 1 (by rfl) ⟨171071, by rfl⟩ : syracuseStep 228095 = 342143) B342143
theorem B2239487 : Blo 151794 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B152063 : Blo 151794 152063 := bstep (se 1 (by rfl) ⟨114047, by rfl⟩ : syracuseStep 152063 = 228095) B228095
theorem B1492991 : Blo 151794 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B995327 : Blo 151794 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B663551 : Blo 151794 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B442367 : Blo 151794 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B294911 : Blo 151794 294911 := bstep (se 1 (by rfl) ⟨221183, by rfl⟩ : syracuseStep 294911 = 442367) B442367
theorem B196607 : Blo 151794 196607 := bstep (se 1 (by rfl) ⟨147455, by rfl⟩ : syracuseStep 196607 = 294911) B294911
theorem B524285 : Blo 151794 524285 := bstep (se 3 (by rfl) ⟨98303, by rfl⟩ : syracuseStep 524285 = 196607) B196607
theorem B349523 : Blo 151794 349523 := bstep (se 1 (by rfl) ⟨262142, by rfl⟩ : syracuseStep 349523 = 524285) B524285
theorem B233015 : Blo 151794 233015 := bstep (se 1 (by rfl) ⟨174761, by rfl⟩ : syracuseStep 233015 = 349523) B349523
theorem B155343 : Blo 151794 155343 := bstep (se 1 (by rfl) ⟨116507, by rfl⟩ : syracuseStep 155343 = 233015) B233015

theorem C0 (j : ℕ) (h1 : 37948 ≤ j) (h2 : j ≤ 38647) : Blo 151794 (4 * j + 3) := by
  interval_cases j
  · exact B151795
  · exact B151799
  · exact B151803
  · exact B151807
  · exact B151811
  · exact B151815
  · exact B151819
  · exact B151823
  · exact B151827
  · exact B151831
  · exact B151835
  · exact B151839
  · exact B151843
  · exact B151847
  · exact B151851
  · exact B151855
  · exact B151859
  · exact B151863
  · exact B151867
  · exact B151871
  · exact B151875
  · exact B151879
  · exact B151883
  · exact B151887
  · exact B151891
  · exact B151895
  · exact B151899
  · exact B151903
  · exact B151907
  · exact B151911
  · exact B151915
  · exact B151919
  · exact B151923
  · exact B151927
  · exact B151931
  · exact B151935
  · exact B151939
  · exact B151943
  · exact B151947
  · exact B151951
  · exact B151955
  · exact B151959
  · exact B151963
  · exact B151967
  · exact B151971
  · exact B151975
  · exact B151979
  · exact B151983
  · exact B151987
  · exact B151991
  · exact B151995
  · exact B151999
  · exact B152003
  · exact B152007
  · exact B152011
  · exact B152015
  · exact B152019
  · exact B152023
  · exact B152027
  · exact B152031
  · exact B152035
  · exact B152039
  · exact B152043
  · exact B152047
  · exact B152051
  · exact B152055
  · exact B152059
  · exact B152063
  · exact B152067
  · exact B152071
  · exact B152075
  · exact B152079
  · exact B152083
  · exact B152087
  · exact B152091
  · exact B152095
  · exact B152099
  · exact B152103
  · exact B152107
  · exact B152111
  · exact B152115
  · exact B152119
  · exact B152123
  · exact B152127
  · exact B152131
  · exact B152135
  · exact B152139
  · exact B152143
  · exact B152147
  · exact B152151
  · exact B152155
  · exact B152159
  · exact B152163
  · exact B152167
  · exact B152171
  · exact B152175
  · exact B152179
  · exact B152183
  · exact B152187
  · exact B152191
  · exact B152195
  · exact B152199
  · exact B152203
  · exact B152207
  · exact B152211
  · exact B152215
  · exact B152219
  · exact B152223
  · exact B152227
  · exact B152231
  · exact B152235
  · exact B152239
  · exact B152243
  · exact B152247
  · exact B152251
  · exact B152255
  · exact B152259
  · exact B152263
  · exact B152267
  · exact B152271
  · exact B152275
  · exact B152279
  · exact B152283
  · exact B152287
  · exact B152291
  · exact B152295
  · exact B152299
  · exact B152303
  · exact B152307
  · exact B152311
  · exact B152315
  · exact B152319
  · exact B152323
  · exact B152327
  · exact B152331
  · exact B152335
  · exact B152339
  · exact B152343
  · exact B152347
  · exact B152351
  · exact B152355
  · exact B152359
  · exact B152363
  · exact B152367
  · exact B152371
  · exact B152375
  · exact B152379
  · exact B152383
  · exact B152387
  · exact B152391
  · exact B152395
  · exact B152399
  · exact B152403
  · exact B152407
  · exact B152411
  · exact B152415
  · exact B152419
  · exact B152423
  · exact B152427
  · exact B152431
  · exact B152435
  · exact B152439
  · exact B152443
  · exact B152447
  · exact B152451
  · exact B152455
  · exact B152459
  · exact B152463
  · exact B152467
  · exact B152471
  · exact B152475
  · exact B152479
  · exact B152483
  · exact B152487
  · exact B152491
  · exact B152495
  · exact B152499
  · exact B152503
  · exact B152507
  · exact B152511
  · exact B152515
  · exact B152519
  · exact B152523
  · exact B152527
  · exact B152531
  · exact B152535
  · exact B152539
  · exact B152543
  · exact B152547
  · exact B152551
  · exact B152555
  · exact B152559
  · exact B152563
  · exact B152567
  · exact B152571
  · exact B152575
  · exact B152579
  · exact B152583
  · exact B152587
  · exact B152591
  · exact B152595
  · exact B152599
  · exact B152603
  · exact B152607
  · exact B152611
  · exact B152615
  · exact B152619
  · exact B152623
  · exact B152627
  · exact B152631
  · exact B152635
  · exact B152639
  · exact B152643
  · exact B152647
  · exact B152651
  · exact B152655
  · exact B152659
  · exact B152663
  · exact B152667
  · exact B152671
  · exact B152675
  · exact B152679
  · exact B152683
  · exact B152687
  · exact B152691
  · exact B152695
  · exact B152699
  · exact B152703
  · exact B152707
  · exact B152711
  · exact B152715
  · exact B152719
  · exact B152723
  · exact B152727
  · exact B152731
  · exact B152735
  · exact B152739
  · exact B152743
  · exact B152747
  · exact B152751
  · exact B152755
  · exact B152759
  · exact B152763
  · exact B152767
  · exact B152771
  · exact B152775
  · exact B152779
  · exact B152783
  · exact B152787
  · exact B152791
  · exact B152795
  · exact B152799
  · exact B152803
  · exact B152807
  · exact B152811
  · exact B152815
  · exact B152819
  · exact B152823
  · exact B152827
  · exact B152831
  · exact B152835
  · exact B152839
  · exact B152843
  · exact B152847
  · exact B152851
  · exact B152855
  · exact B152859
  · exact B152863
  · exact B152867
  · exact B152871
  · exact B152875
  · exact B152879
  · exact B152883
  · exact B152887
  · exact B152891
  · exact B152895
  · exact B152899
  · exact B152903
  · exact B152907
  · exact B152911
  · exact B152915
  · exact B152919
  · exact B152923
  · exact B152927
  · exact B152931
  · exact B152935
  · exact B152939
  · exact B152943
  · exact B152947
  · exact B152951
  · exact B152955
  · exact B152959
  · exact B152963
  · exact B152967
  · exact B152971
  · exact B152975
  · exact B152979
  · exact B152983
  · exact B152987
  · exact B152991
  · exact B152995
  · exact B152999
  · exact B153003
  · exact B153007
  · exact B153011
  · exact B153015
  · exact B153019
  · exact B153023
  · exact B153027
  · exact B153031
  · exact B153035
  · exact B153039
  · exact B153043
  · exact B153047
  · exact B153051
  · exact B153055
  · exact B153059
  · exact B153063
  · exact B153067
  · exact B153071
  · exact B153075
  · exact B153079
  · exact B153083
  · exact B153087
  · exact B153091
  · exact B153095
  · exact B153099
  · exact B153103
  · exact B153107
  · exact B153111
  · exact B153115
  · exact B153119
  · exact B153123
  · exact B153127
  · exact B153131
  · exact B153135
  · exact B153139
  · exact B153143
  · exact B153147
  · exact B153151
  · exact B153155
  · exact B153159
  · exact B153163
  · exact B153167
  · exact B153171
  · exact B153175
  · exact B153179
  · exact B153183
  · exact B153187
  · exact B153191
  · exact B153195
  · exact B153199
  · exact B153203
  · exact B153207
  · exact B153211
  · exact B153215
  · exact B153219
  · exact B153223
  · exact B153227
  · exact B153231
  · exact B153235
  · exact B153239
  · exact B153243
  · exact B153247
  · exact B153251
  · exact B153255
  · exact B153259
  · exact B153263
  · exact B153267
  · exact B153271
  · exact B153275
  · exact B153279
  · exact B153283
  · exact B153287
  · exact B153291
  · exact B153295
  · exact B153299
  · exact B153303
  · exact B153307
  · exact B153311
  · exact B153315
  · exact B153319
  · exact B153323
  · exact B153327
  · exact B153331
  · exact B153335
  · exact B153339
  · exact B153343
  · exact B153347
  · exact B153351
  · exact B153355
  · exact B153359
  · exact B153363
  · exact B153367
  · exact B153371
  · exact B153375
  · exact B153379
  · exact B153383
  · exact B153387
  · exact B153391
  · exact B153395
  · exact B153399
  · exact B153403
  · exact B153407
  · exact B153411
  · exact B153415
  · exact B153419
  · exact B153423
  · exact B153427
  · exact B153431
  · exact B153435
  · exact B153439
  · exact B153443
  · exact B153447
  · exact B153451
  · exact B153455
  · exact B153459
  · exact B153463
  · exact B153467
  · exact B153471
  · exact B153475
  · exact B153479
  · exact B153483
  · exact B153487
  · exact B153491
  · exact B153495
  · exact B153499
  · exact B153503
  · exact B153507
  · exact B153511
  · exact B153515
  · exact B153519
  · exact B153523
  · exact B153527
  · exact B153531
  · exact B153535
  · exact B153539
  · exact B153543
  · exact B153547
  · exact B153551
  · exact B153555
  · exact B153559
  · exact B153563
  · exact B153567
  · exact B153571
  · exact B153575
  · exact B153579
  · exact B153583
  · exact B153587
  · exact B153591
  · exact B153595
  · exact B153599
  · exact B153603
  · exact B153607
  · exact B153611
  · exact B153615
  · exact B153619
  · exact B153623
  · exact B153627
  · exact B153631
  · exact B153635
  · exact B153639
  · exact B153643
  · exact B153647
  · exact B153651
  · exact B153655
  · exact B153659
  · exact B153663
  · exact B153667
  · exact B153671
  · exact B153675
  · exact B153679
  · exact B153683
  · exact B153687
  · exact B153691
  · exact B153695
  · exact B153699
  · exact B153703
  · exact B153707
  · exact B153711
  · exact B153715
  · exact B153719
  · exact B153723
  · exact B153727
  · exact B153731
  · exact B153735
  · exact B153739
  · exact B153743
  · exact B153747
  · exact B153751
  · exact B153755
  · exact B153759
  · exact B153763
  · exact B153767
  · exact B153771
  · exact B153775
  · exact B153779
  · exact B153783
  · exact B153787
  · exact B153791
  · exact B153795
  · exact B153799
  · exact B153803
  · exact B153807
  · exact B153811
  · exact B153815
  · exact B153819
  · exact B153823
  · exact B153827
  · exact B153831
  · exact B153835
  · exact B153839
  · exact B153843
  · exact B153847
  · exact B153851
  · exact B153855
  · exact B153859
  · exact B153863
  · exact B153867
  · exact B153871
  · exact B153875
  · exact B153879
  · exact B153883
  · exact B153887
  · exact B153891
  · exact B153895
  · exact B153899
  · exact B153903
  · exact B153907
  · exact B153911
  · exact B153915
  · exact B153919
  · exact B153923
  · exact B153927
  · exact B153931
  · exact B153935
  · exact B153939
  · exact B153943
  · exact B153947
  · exact B153951
  · exact B153955
  · exact B153959
  · exact B153963
  · exact B153967
  · exact B153971
  · exact B153975
  · exact B153979
  · exact B153983
  · exact B153987
  · exact B153991
  · exact B153995
  · exact B153999
  · exact B154003
  · exact B154007
  · exact B154011
  · exact B154015
  · exact B154019
  · exact B154023
  · exact B154027
  · exact B154031
  · exact B154035
  · exact B154039
  · exact B154043
  · exact B154047
  · exact B154051
  · exact B154055
  · exact B154059
  · exact B154063
  · exact B154067
  · exact B154071
  · exact B154075
  · exact B154079
  · exact B154083
  · exact B154087
  · exact B154091
  · exact B154095
  · exact B154099
  · exact B154103
  · exact B154107
  · exact B154111
  · exact B154115
  · exact B154119
  · exact B154123
  · exact B154127
  · exact B154131
  · exact B154135
  · exact B154139
  · exact B154143
  · exact B154147
  · exact B154151
  · exact B154155
  · exact B154159
  · exact B154163
  · exact B154167
  · exact B154171
  · exact B154175
  · exact B154179
  · exact B154183
  · exact B154187
  · exact B154191
  · exact B154195
  · exact B154199
  · exact B154203
  · exact B154207
  · exact B154211
  · exact B154215
  · exact B154219
  · exact B154223
  · exact B154227
  · exact B154231
  · exact B154235
  · exact B154239
  · exact B154243
  · exact B154247
  · exact B154251
  · exact B154255
  · exact B154259
  · exact B154263
  · exact B154267
  · exact B154271
  · exact B154275
  · exact B154279
  · exact B154283
  · exact B154287
  · exact B154291
  · exact B154295
  · exact B154299
  · exact B154303
  · exact B154307
  · exact B154311
  · exact B154315
  · exact B154319
  · exact B154323
  · exact B154327
  · exact B154331
  · exact B154335
  · exact B154339
  · exact B154343
  · exact B154347
  · exact B154351
  · exact B154355
  · exact B154359
  · exact B154363
  · exact B154367
  · exact B154371
  · exact B154375
  · exact B154379
  · exact B154383
  · exact B154387
  · exact B154391
  · exact B154395
  · exact B154399
  · exact B154403
  · exact B154407
  · exact B154411
  · exact B154415
  · exact B154419
  · exact B154423
  · exact B154427
  · exact B154431
  · exact B154435
  · exact B154439
  · exact B154443
  · exact B154447
  · exact B154451
  · exact B154455
  · exact B154459
  · exact B154463
  · exact B154467
  · exact B154471
  · exact B154475
  · exact B154479
  · exact B154483
  · exact B154487
  · exact B154491
  · exact B154495
  · exact B154499
  · exact B154503
  · exact B154507
  · exact B154511
  · exact B154515
  · exact B154519
  · exact B154523
  · exact B154527
  · exact B154531
  · exact B154535
  · exact B154539
  · exact B154543
  · exact B154547
  · exact B154551
  · exact B154555
  · exact B154559
  · exact B154563
  · exact B154567
  · exact B154571
  · exact B154575
  · exact B154579
  · exact B154583
  · exact B154587
  · exact B154591

theorem C1 (j : ℕ) (h1 : 38648 ≤ j) (h2 : j ≤ 38947) : Blo 151794 (4 * j + 3) := by
  interval_cases j
  · exact B154595
  · exact B154599
  · exact B154603
  · exact B154607
  · exact B154611
  · exact B154615
  · exact B154619
  · exact B154623
  · exact B154627
  · exact B154631
  · exact B154635
  · exact B154639
  · exact B154643
  · exact B154647
  · exact B154651
  · exact B154655
  · exact B154659
  · exact B154663
  · exact B154667
  · exact B154671
  · exact B154675
  · exact B154679
  · exact B154683
  · exact B154687
  · exact B154691
  · exact B154695
  · exact B154699
  · exact B154703
  · exact B154707
  · exact B154711
  · exact B154715
  · exact B154719
  · exact B154723
  · exact B154727
  · exact B154731
  · exact B154735
  · exact B154739
  · exact B154743
  · exact B154747
  · exact B154751
  · exact B154755
  · exact B154759
  · exact B154763
  · exact B154767
  · exact B154771
  · exact B154775
  · exact B154779
  · exact B154783
  · exact B154787
  · exact B154791
  · exact B154795
  · exact B154799
  · exact B154803
  · exact B154807
  · exact B154811
  · exact B154815
  · exact B154819
  · exact B154823
  · exact B154827
  · exact B154831
  · exact B154835
  · exact B154839
  · exact B154843
  · exact B154847
  · exact B154851
  · exact B154855
  · exact B154859
  · exact B154863
  · exact B154867
  · exact B154871
  · exact B154875
  · exact B154879
  · exact B154883
  · exact B154887
  · exact B154891
  · exact B154895
  · exact B154899
  · exact B154903
  · exact B154907
  · exact B154911
  · exact B154915
  · exact B154919
  · exact B154923
  · exact B154927
  · exact B154931
  · exact B154935
  · exact B154939
  · exact B154943
  · exact B154947
  · exact B154951
  · exact B154955
  · exact B154959
  · exact B154963
  · exact B154967
  · exact B154971
  · exact B154975
  · exact B154979
  · exact B154983
  · exact B154987
  · exact B154991
  · exact B154995
  · exact B154999
  · exact B155003
  · exact B155007
  · exact B155011
  · exact B155015
  · exact B155019
  · exact B155023
  · exact B155027
  · exact B155031
  · exact B155035
  · exact B155039
  · exact B155043
  · exact B155047
  · exact B155051
  · exact B155055
  · exact B155059
  · exact B155063
  · exact B155067
  · exact B155071
  · exact B155075
  · exact B155079
  · exact B155083
  · exact B155087
  · exact B155091
  · exact B155095
  · exact B155099
  · exact B155103
  · exact B155107
  · exact B155111
  · exact B155115
  · exact B155119
  · exact B155123
  · exact B155127
  · exact B155131
  · exact B155135
  · exact B155139
  · exact B155143
  · exact B155147
  · exact B155151
  · exact B155155
  · exact B155159
  · exact B155163
  · exact B155167
  · exact B155171
  · exact B155175
  · exact B155179
  · exact B155183
  · exact B155187
  · exact B155191
  · exact B155195
  · exact B155199
  · exact B155203
  · exact B155207
  · exact B155211
  · exact B155215
  · exact B155219
  · exact B155223
  · exact B155227
  · exact B155231
  · exact B155235
  · exact B155239
  · exact B155243
  · exact B155247
  · exact B155251
  · exact B155255
  · exact B155259
  · exact B155263
  · exact B155267
  · exact B155271
  · exact B155275
  · exact B155279
  · exact B155283
  · exact B155287
  · exact B155291
  · exact B155295
  · exact B155299
  · exact B155303
  · exact B155307
  · exact B155311
  · exact B155315
  · exact B155319
  · exact B155323
  · exact B155327
  · exact B155331
  · exact B155335
  · exact B155339
  · exact B155343
  · exact B155347
  · exact B155351
  · exact B155355
  · exact B155359
  · exact B155363
  · exact B155367
  · exact B155371
  · exact B155375
  · exact B155379
  · exact B155383
  · exact B155387
  · exact B155391
  · exact B155395
  · exact B155399
  · exact B155403
  · exact B155407
  · exact B155411
  · exact B155415
  · exact B155419
  · exact B155423
  · exact B155427
  · exact B155431
  · exact B155435
  · exact B155439
  · exact B155443
  · exact B155447
  · exact B155451
  · exact B155455
  · exact B155459
  · exact B155463
  · exact B155467
  · exact B155471
  · exact B155475
  · exact B155479
  · exact B155483
  · exact B155487
  · exact B155491
  · exact B155495
  · exact B155499
  · exact B155503
  · exact B155507
  · exact B155511
  · exact B155515
  · exact B155519
  · exact B155523
  · exact B155527
  · exact B155531
  · exact B155535
  · exact B155539
  · exact B155543
  · exact B155547
  · exact B155551
  · exact B155555
  · exact B155559
  · exact B155563
  · exact B155567
  · exact B155571
  · exact B155575
  · exact B155579
  · exact B155583
  · exact B155587
  · exact B155591
  · exact B155595
  · exact B155599
  · exact B155603
  · exact B155607
  · exact B155611
  · exact B155615
  · exact B155619
  · exact B155623
  · exact B155627
  · exact B155631
  · exact B155635
  · exact B155639
  · exact B155643
  · exact B155647
  · exact B155651
  · exact B155655
  · exact B155659
  · exact B155663
  · exact B155667
  · exact B155671
  · exact B155675
  · exact B155679
  · exact B155683
  · exact B155687
  · exact B155691
  · exact B155695
  · exact B155699
  · exact B155703
  · exact B155707
  · exact B155711
  · exact B155715
  · exact B155719
  · exact B155723
  · exact B155727
  · exact B155731
  · exact B155735
  · exact B155739
  · exact B155743
  · exact B155747
  · exact B155751
  · exact B155755
  · exact B155759
  · exact B155763
  · exact B155767
  · exact B155771
  · exact B155775
  · exact B155779
  · exact B155783
  · exact B155787
  · exact B155791

theorem solution (m : ℕ) (hlo : 151794 ≤ m) (hhi : m ≤ 155794) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 37948 ≤ j := by omega
    have hj2 : j ≤ 38947 := by omega
    have hb : Blo 151794 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 38648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
