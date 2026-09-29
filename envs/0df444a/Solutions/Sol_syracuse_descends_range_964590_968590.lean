-- Prove2me | solution 1 for syracuse_descends_range_964590_968590
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:03.33501+00:00
-- url     : https://prove2.me/submissions/c6a84d04-2e6d-4198-87e4-bbd87ff61534

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


theorem B1835045 : Blo 964590 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B3309605 : Blo 964590 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B2752613 : Blo 964590 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B2326661 : Blo 964590 2326661 := bbase (se 4 (by rfl) ⟨218124, by rfl⟩ : syracuseStep 2326661 = 436249) (by norm_num)
theorem B3670181 : Blo 964590 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B9306677 : Blo 964590 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B2064973 : Blo 964590 2064973 := bbase (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) (by norm_num)
theorem B1377013 : Blo 964590 1377013 := bbase (se 5 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 1377013 = 129095) (by norm_num)
theorem B1835797 : Blo 964590 1835797 := bbase (se 6 (by rfl) ⟨43026, by rfl⟩ : syracuseStep 1835797 = 86053) (by norm_num)
theorem B2753365 : Blo 964590 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B1835941 : Blo 964590 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B1836101 : Blo 964590 1836101 := bbase (se 4 (by rfl) ⟨172134, by rfl⟩ : syracuseStep 1836101 = 344269) (by norm_num)
theorem B2786501 : Blo 964590 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B1836245 : Blo 964590 1836245 := bbase (se 7 (by rfl) ⟨21518, by rfl⟩ : syracuseStep 1836245 = 43037) (by norm_num)
theorem B3671365 : Blo 964590 3671365 := bbase (se 4 (by rfl) ⟨344190, by rfl⟩ : syracuseStep 3671365 = 688381) (by norm_num)
theorem B1377605 : Blo 964590 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B4883813 : Blo 964590 4883813 := bbase (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) (by norm_num)
theorem B1377685 : Blo 964590 1377685 := bbase (se 6 (by rfl) ⟨32289, by rfl⟩ : syracuseStep 1377685 = 64579) (by norm_num)
theorem B2065861 : Blo 964590 2065861 := bbase (se 4 (by rfl) ⟨193674, by rfl⟩ : syracuseStep 2065861 = 387349) (by norm_num)
theorem B1836533 : Blo 964590 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B1377805 : Blo 964590 1377805 := bbase (se 3 (by rfl) ⟨258338, by rfl⟩ : syracuseStep 1377805 = 516677) (by norm_num)
theorem B2065981 : Blo 964590 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B1377901 : Blo 964590 1377901 := bbase (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) (by norm_num)
theorem B3671669 : Blo 964590 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B1836685 : Blo 964590 1836685 := bbase (se 3 (by rfl) ⟨344378, by rfl⟩ : syracuseStep 1836685 = 688757) (by norm_num)
theorem B11175637 : Blo 964590 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B2066237 : Blo 964590 2066237 := bbase (se 3 (by rfl) ⟨387419, by rfl⟩ : syracuseStep 2066237 = 774839) (by norm_num)
theorem B1836989 : Blo 964590 1836989 := bbase (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) (by norm_num)
theorem B1378397 : Blo 964590 1378397 := bbase (se 3 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 1378397 = 516899) (by norm_num)
theorem B4885109 : Blo 964590 4885109 := bbase (se 5 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 4885109 = 457979) (by norm_num)
theorem B1378949 : Blo 964590 1378949 := bbase (se 4 (by rfl) ⟨129276, by rfl⟩ : syracuseStep 1378949 = 258553) (by norm_num)
theorem B1837741 : Blo 964590 1837741 := bbase (se 3 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 1837741 = 689153) (by norm_num)
theorem B2067125 : Blo 964590 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B5966581 : Blo 964590 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B4950821 : Blo 964590 4950821 := bbase (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) (by norm_num)
theorem B1837885 : Blo 964590 1837885 := bbase (se 3 (by rfl) ⟨344603, by rfl⟩ : syracuseStep 1837885 = 689207) (by norm_num)
theorem B2067365 : Blo 964590 2067365 := bbase (se 4 (by rfl) ⟨193815, by rfl⟩ : syracuseStep 2067365 = 387631) (by norm_num)
theorem B1838045 : Blo 964590 1838045 := bbase (se 3 (by rfl) ⟨344633, by rfl⟩ : syracuseStep 1838045 = 689267) (by norm_num)
theorem B1838189 : Blo 964590 1838189 := bbase (se 3 (by rfl) ⟨344660, by rfl⟩ : syracuseStep 1838189 = 689321) (by norm_num)
theorem B4132133 : Blo 964590 4132133 := bbase (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) (by norm_num)
theorem B1838477 : Blo 964590 1838477 := bbase (se 3 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 1838477 = 689429) (by norm_num)
theorem B2067869 : Blo 964590 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B2067877 : Blo 964590 2067877 := bbase (se 4 (by rfl) ⟨193863, by rfl⟩ : syracuseStep 2067877 = 387727) (by norm_num)
theorem B6196661 : Blo 964590 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B1838629 : Blo 964590 1838629 := bbase (se 4 (by rfl) ⟨172371, by rfl⟩ : syracuseStep 1838629 = 344743) (by norm_num)
theorem B29724245 : Blo 964590 29724245 := bbase (se 8 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 29724245 = 348331) (by norm_num)
theorem B2756213 : Blo 964590 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B13962901 : Blo 964590 13962901 := bbase (se 6 (by rfl) ⟨327255, by rfl⟩ : syracuseStep 13962901 = 654511) (by norm_num)
theorem B3673781 : Blo 964590 3673781 := bbase (se 5 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 3673781 = 344417) (by norm_num)
theorem B1740533 : Blo 964590 1740533 := bbase (se 5 (by rfl) ⟨81587, by rfl⟩ : syracuseStep 1740533 = 163175) (by norm_num)
theorem B1117957 : Blo 964590 1117957 := bbase (se 4 (by rfl) ⟨104808, by rfl⟩ : syracuseStep 1117957 = 209617) (by norm_num)
theorem B1085197 : Blo 964590 1085197 := bbase (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) (by norm_num)
theorem B1085233 : Blo 964590 1085233 := bbase (se 2 (by rfl) ⟨406962, by rfl⟩ : syracuseStep 1085233 = 813925) (by norm_num)
theorem B5508917 : Blo 964590 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B1740613 : Blo 964590 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B1085269 : Blo 964590 1085269 := bbase (se 9 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 1085269 = 6359) (by norm_num)
theorem B1085305 : Blo 964590 1085305 := bbase (se 2 (by rfl) ⟨406989, by rfl⟩ : syracuseStep 1085305 = 813979) (by norm_num)
theorem B4886405 : Blo 964590 4886405 := bbase (se 4 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 4886405 = 916201) (by norm_num)
theorem B1085341 : Blo 964590 1085341 := bbase (se 3 (by rfl) ⟨203501, by rfl⟩ : syracuseStep 1085341 = 407003) (by norm_num)
theorem B1085377 : Blo 964590 1085377 := bbase (se 2 (by rfl) ⟨407016, by rfl⟩ : syracuseStep 1085377 = 814033) (by norm_num)
theorem B3674069 : Blo 964590 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B1085413 : Blo 964590 1085413 := bbase (se 4 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 1085413 = 203515) (by norm_num)
theorem B1085449 : Blo 964590 1085449 := bbase (se 2 (by rfl) ⟨407043, by rfl⟩ : syracuseStep 1085449 = 814087) (by norm_num)
theorem B1085485 : Blo 964590 1085485 := bbase (se 3 (by rfl) ⟨203528, by rfl⟩ : syracuseStep 1085485 = 407057) (by norm_num)
theorem B1740845 : Blo 964590 1740845 := bbase (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) (by norm_num)
theorem B1085521 : Blo 964590 1085521 := bbase (se 2 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 1085521 = 814141) (by norm_num)
theorem B1085557 : Blo 964590 1085557 := bbase (se 5 (by rfl) ⟨50885, by rfl⟩ : syracuseStep 1085557 = 101771) (by norm_num)
theorem B1085593 : Blo 964590 1085593 := bbase (se 2 (by rfl) ⟨407097, by rfl⟩ : syracuseStep 1085593 = 814195) (by norm_num)
theorem B1085629 : Blo 964590 1085629 := bbase (se 3 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 1085629 = 407111) (by norm_num)
theorem B1085665 : Blo 964590 1085665 := bbase (se 2 (by rfl) ⟨407124, by rfl⟩ : syracuseStep 1085665 = 814249) (by norm_num)
theorem B1085701 : Blo 964590 1085701 := bbase (se 4 (by rfl) ⟨101784, by rfl⟩ : syracuseStep 1085701 = 203569) (by norm_num)
theorem B18583829 : Blo 964590 18583829 := bbase (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) (by norm_num)
theorem B1085737 : Blo 964590 1085737 := bbase (se 2 (by rfl) ⟨407151, by rfl⟩ : syracuseStep 1085737 = 814303) (by norm_num)
theorem B1085773 : Blo 964590 1085773 := bbase (se 3 (by rfl) ⟨203582, by rfl⟩ : syracuseStep 1085773 = 407165) (by norm_num)
theorem B1085809 : Blo 964590 1085809 := bbase (se 2 (by rfl) ⟨407178, by rfl⟩ : syracuseStep 1085809 = 814357) (by norm_num)
theorem B1085845 : Blo 964590 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B1085881 : Blo 964590 1085881 := bbase (se 2 (by rfl) ⟨407205, by rfl⟩ : syracuseStep 1085881 = 814411) (by norm_num)
theorem B1085917 : Blo 964590 1085917 := bbase (se 3 (by rfl) ⟨203609, by rfl⟩ : syracuseStep 1085917 = 407219) (by norm_num)
theorem B1085953 : Blo 964590 1085953 := bbase (se 2 (by rfl) ⟨407232, by rfl⟩ : syracuseStep 1085953 = 814465) (by norm_num)
theorem B2789893 : Blo 964590 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B1085989 : Blo 964590 1085989 := bbase (se 4 (by rfl) ⟨101811, by rfl⟩ : syracuseStep 1085989 = 203623) (by norm_num)
theorem B1086025 : Blo 964590 1086025 := bbase (se 2 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 1086025 = 814519) (by norm_num)
theorem B1086061 : Blo 964590 1086061 := bbase (se 3 (by rfl) ⟨203636, by rfl⟩ : syracuseStep 1086061 = 407273) (by norm_num)
theorem B1086097 : Blo 964590 1086097 := bbase (se 2 (by rfl) ⟨407286, by rfl⟩ : syracuseStep 1086097 = 814573) (by norm_num)
theorem B1086133 : Blo 964590 1086133 := bbase (se 5 (by rfl) ⟨50912, by rfl⟩ : syracuseStep 1086133 = 101825) (by norm_num)
theorem B1086169 : Blo 964590 1086169 := bbase (se 2 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 1086169 = 814627) (by norm_num)
theorem B1086205 : Blo 964590 1086205 := bbase (se 3 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 1086205 = 407327) (by norm_num)
theorem B7344917 : Blo 964590 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B2757397 : Blo 964590 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B1086241 : Blo 964590 1086241 := bbase (se 2 (by rfl) ⟨407340, by rfl⟩ : syracuseStep 1086241 = 814681) (by norm_num)
theorem B1086277 : Blo 964590 1086277 := bbase (se 4 (by rfl) ⟨101838, by rfl⟩ : syracuseStep 1086277 = 203677) (by norm_num)
theorem B1086313 : Blo 964590 1086313 := bbase (se 2 (by rfl) ⟨407367, by rfl⟩ : syracuseStep 1086313 = 814735) (by norm_num)
theorem B1086349 : Blo 964590 1086349 := bbase (se 3 (by rfl) ⟨203690, by rfl⟩ : syracuseStep 1086349 = 407381) (by norm_num)
theorem B1086385 : Blo 964590 1086385 := bbase (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) (by norm_num)
theorem B2757557 : Blo 964590 2757557 := bbase (se 5 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 2757557 = 258521) (by norm_num)
theorem B1086421 : Blo 964590 1086421 := bbase (se 7 (by rfl) ⟨12731, by rfl⟩ : syracuseStep 1086421 = 25463) (by norm_num)
theorem B1446893 : Blo 964590 1446893 := bbase (se 3 (by rfl) ⟨271292, by rfl⟩ : syracuseStep 1446893 = 542585) (by norm_num)
theorem B1086457 : Blo 964590 1086457 := bbase (se 2 (by rfl) ⟨407421, by rfl⟩ : syracuseStep 1086457 = 814843) (by norm_num)
theorem B1446917 : Blo 964590 1446917 := bbase (se 4 (by rfl) ⟨135648, by rfl⟩ : syracuseStep 1446917 = 271297) (by norm_num)
theorem B11015189 : Blo 964590 11015189 := bbase (se 6 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 11015189 = 516337) (by norm_num)
theorem B4133909 : Blo 964590 4133909 := bbase (se 6 (by rfl) ⟨96888, by rfl⟩ : syracuseStep 4133909 = 193777) (by norm_num)
theorem B1446941 : Blo 964590 1446941 := bbase (se 3 (by rfl) ⟨271301, by rfl⟩ : syracuseStep 1446941 = 542603) (by norm_num)
theorem B1086493 : Blo 964590 1086493 := bbase (se 3 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 1086493 = 407435) (by norm_num)
theorem B1446965 : Blo 964590 1446965 := bbase (se 5 (by rfl) ⟨67826, by rfl⟩ : syracuseStep 1446965 = 135653) (by norm_num)
theorem B1086529 : Blo 964590 1086529 := bbase (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) (by norm_num)
theorem B1446989 : Blo 964590 1446989 := bbase (se 3 (by rfl) ⟨271310, by rfl⟩ : syracuseStep 1446989 = 542621) (by norm_num)
theorem B1447013 : Blo 964590 1447013 := bbase (se 4 (by rfl) ⟨135657, by rfl⟩ : syracuseStep 1447013 = 271315) (by norm_num)
theorem B1086565 : Blo 964590 1086565 := bbase (se 4 (by rfl) ⟨101865, by rfl⟩ : syracuseStep 1086565 = 203731) (by norm_num)
theorem B3675253 : Blo 964590 3675253 := bbase (se 5 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 3675253 = 344555) (by norm_num)
theorem B1447037 : Blo 964590 1447037 := bbase (se 3 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 1447037 = 542639) (by norm_num)
theorem B1086601 : Blo 964590 1086601 := bbase (se 2 (by rfl) ⟨407475, by rfl⟩ : syracuseStep 1086601 = 814951) (by norm_num)
theorem B1447061 : Blo 964590 1447061 := bbase (se 6 (by rfl) ⟨33915, by rfl⟩ : syracuseStep 1447061 = 67831) (by norm_num)
theorem B4887701 : Blo 964590 4887701 := bbase (se 6 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 4887701 = 229111) (by norm_num)
theorem B2757797 : Blo 964590 2757797 := bbase (se 4 (by rfl) ⟨258543, by rfl⟩ : syracuseStep 2757797 = 517087) (by norm_num)
theorem B1447085 : Blo 964590 1447085 := bbase (se 3 (by rfl) ⟨271328, by rfl⟩ : syracuseStep 1447085 = 542657) (by norm_num)
theorem B1086637 : Blo 964590 1086637 := bbase (se 3 (by rfl) ⟨203744, by rfl⟩ : syracuseStep 1086637 = 407489) (by norm_num)
theorem B1741997 : Blo 964590 1741997 := bbase (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) (by norm_num)
theorem B1447109 : Blo 964590 1447109 := bbase (se 4 (by rfl) ⟨135666, by rfl⟩ : syracuseStep 1447109 = 271333) (by norm_num)
theorem B1086673 : Blo 964590 1086673 := bbase (se 2 (by rfl) ⟨407502, by rfl⟩ : syracuseStep 1086673 = 815005) (by norm_num)
theorem B1447133 : Blo 964590 1447133 := bbase (se 3 (by rfl) ⟨271337, by rfl⟩ : syracuseStep 1447133 = 542675) (by norm_num)
theorem B1447157 : Blo 964590 1447157 := bbase (se 5 (by rfl) ⟨67835, by rfl⟩ : syracuseStep 1447157 = 135671) (by norm_num)
theorem B1086709 : Blo 964590 1086709 := bbase (se 5 (by rfl) ⟨50939, by rfl⟩ : syracuseStep 1086709 = 101879) (by norm_num)
theorem B1742077 : Blo 964590 1742077 := bbase (se 3 (by rfl) ⟨326639, by rfl⟩ : syracuseStep 1742077 = 653279) (by norm_num)
theorem B4134149 : Blo 964590 4134149 := bbase (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) (by norm_num)
theorem B1447181 : Blo 964590 1447181 := bbase (se 3 (by rfl) ⟨271346, by rfl⟩ : syracuseStep 1447181 = 542693) (by norm_num)
theorem B1086745 : Blo 964590 1086745 := bbase (se 2 (by rfl) ⟨407529, by rfl⟩ : syracuseStep 1086745 = 815059) (by norm_num)
theorem B1447205 : Blo 964590 1447205 := bbase (se 4 (by rfl) ⟨135675, by rfl⟩ : syracuseStep 1447205 = 271351) (by norm_num)
theorem B1447229 : Blo 964590 1447229 := bbase (se 3 (by rfl) ⟨271355, by rfl⟩ : syracuseStep 1447229 = 542711) (by norm_num)
theorem B1086781 : Blo 964590 1086781 := bbase (se 3 (by rfl) ⟨203771, by rfl⟩ : syracuseStep 1086781 = 407543) (by norm_num)
theorem B1447253 : Blo 964590 1447253 := bbase (se 14 (by rfl) ⟨132, by rfl⟩ : syracuseStep 1447253 = 265) (by norm_num)
theorem B1086817 : Blo 964590 1086817 := bbase (se 2 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 1086817 = 815113) (by norm_num)
theorem B2757989 : Blo 964590 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B1447277 : Blo 964590 1447277 := bbase (se 3 (by rfl) ⟨271364, by rfl⟩ : syracuseStep 1447277 = 542729) (by norm_num)
theorem B1447301 : Blo 964590 1447301 := bbase (se 4 (by rfl) ⟨135684, by rfl⟩ : syracuseStep 1447301 = 271369) (by norm_num)
theorem B1086853 : Blo 964590 1086853 := bbase (se 4 (by rfl) ⟨101892, by rfl⟩ : syracuseStep 1086853 = 203785) (by norm_num)
theorem B16520597 : Blo 964590 16520597 := bbase (se 6 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 16520597 = 774403) (by norm_num)
theorem B1447325 : Blo 964590 1447325 := bbase (se 3 (by rfl) ⟨271373, by rfl⟩ : syracuseStep 1447325 = 542747) (by norm_num)
theorem B3675557 : Blo 964590 3675557 := bbase (se 4 (by rfl) ⟨344583, by rfl⟩ : syracuseStep 3675557 = 689167) (by norm_num)
theorem B1086889 : Blo 964590 1086889 := bbase (se 2 (by rfl) ⟨407583, by rfl⟩ : syracuseStep 1086889 = 815167) (by norm_num)
theorem B1447349 : Blo 964590 1447349 := bbase (se 5 (by rfl) ⟨67844, by rfl⟩ : syracuseStep 1447349 = 135689) (by norm_num)
theorem B1447373 : Blo 964590 1447373 := bbase (se 3 (by rfl) ⟨271382, by rfl⟩ : syracuseStep 1447373 = 542765) (by norm_num)
theorem B1086925 : Blo 964590 1086925 := bbase (se 3 (by rfl) ⟨203798, by rfl⟩ : syracuseStep 1086925 = 407597) (by norm_num)
theorem B1447397 : Blo 964590 1447397 := bbase (se 4 (by rfl) ⟨135693, by rfl⟩ : syracuseStep 1447397 = 271387) (by norm_num)
theorem B1086961 : Blo 964590 1086961 := bbase (se 2 (by rfl) ⟨407610, by rfl⟩ : syracuseStep 1086961 = 815221) (by norm_num)
theorem B1447421 : Blo 964590 1447421 := bbase (se 3 (by rfl) ⟨271391, by rfl⟩ : syracuseStep 1447421 = 542783) (by norm_num)
theorem B1447445 : Blo 964590 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B1086997 : Blo 964590 1086997 := bbase (se 6 (by rfl) ⟨25476, by rfl⟩ : syracuseStep 1086997 = 50953) (by norm_num)
theorem B1447469 : Blo 964590 1447469 := bbase (se 3 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 1447469 = 542801) (by norm_num)
theorem B1087033 : Blo 964590 1087033 := bbase (se 2 (by rfl) ⟨407637, by rfl⟩ : syracuseStep 1087033 = 815275) (by norm_num)
theorem B1447493 : Blo 964590 1447493 := bbase (se 4 (by rfl) ⟨135702, by rfl⟩ : syracuseStep 1447493 = 271405) (by norm_num)
theorem B1447517 : Blo 964590 1447517 := bbase (se 3 (by rfl) ⟨271409, by rfl⟩ : syracuseStep 1447517 = 542819) (by norm_num)
theorem B1087069 : Blo 964590 1087069 := bbase (se 3 (by rfl) ⟨203825, by rfl⟩ : syracuseStep 1087069 = 407651) (by norm_num)
theorem B1447541 : Blo 964590 1447541 := bbase (se 5 (by rfl) ⟨67853, by rfl⟩ : syracuseStep 1447541 = 135707) (by norm_num)
theorem B1087105 : Blo 964590 1087105 := bbase (se 2 (by rfl) ⟨407664, by rfl⟩ : syracuseStep 1087105 = 815329) (by norm_num)
theorem B1447565 : Blo 964590 1447565 := bbase (se 3 (by rfl) ⟨271418, by rfl⟩ : syracuseStep 1447565 = 542837) (by norm_num)
theorem B1447589 : Blo 964590 1447589 := bbase (se 4 (by rfl) ⟨135711, by rfl⟩ : syracuseStep 1447589 = 271423) (by norm_num)
theorem B1087141 : Blo 964590 1087141 := bbase (se 4 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 1087141 = 203839) (by norm_num)
theorem B3479221 : Blo 964590 3479221 := bbase (se 5 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 3479221 = 326177) (by norm_num)
theorem B1447613 : Blo 964590 1447613 := bbase (se 3 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 1447613 = 542855) (by norm_num)
theorem B1087177 : Blo 964590 1087177 := bbase (se 2 (by rfl) ⟨407691, by rfl⟩ : syracuseStep 1087177 = 815383) (by norm_num)
theorem B1447637 : Blo 964590 1447637 := bbase (se 7 (by rfl) ⟨16964, by rfl⟩ : syracuseStep 1447637 = 33929) (by norm_num)
theorem B1447661 : Blo 964590 1447661 := bbase (se 3 (by rfl) ⟨271436, by rfl⟩ : syracuseStep 1447661 = 542873) (by norm_num)
theorem B1087213 : Blo 964590 1087213 := bbase (se 3 (by rfl) ⟨203852, by rfl⟩ : syracuseStep 1087213 = 407705) (by norm_num)
theorem B1447685 : Blo 964590 1447685 := bbase (se 4 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 1447685 = 271441) (by norm_num)
theorem B1087249 : Blo 964590 1087249 := bbase (se 2 (by rfl) ⟨407718, by rfl⟩ : syracuseStep 1087249 = 815437) (by norm_num)
theorem B1447709 : Blo 964590 1447709 := bbase (se 3 (by rfl) ⟨271445, by rfl⟩ : syracuseStep 1447709 = 542891) (by norm_num)
theorem B1546013 : Blo 964590 1546013 := bbase (se 3 (by rfl) ⟨289877, by rfl⟩ : syracuseStep 1546013 = 579755) (by norm_num)
theorem B1447733 : Blo 964590 1447733 := bbase (se 5 (by rfl) ⟨67862, by rfl⟩ : syracuseStep 1447733 = 135725) (by norm_num)
theorem B1087285 : Blo 964590 1087285 := bbase (se 5 (by rfl) ⟨50966, by rfl⟩ : syracuseStep 1087285 = 101933) (by norm_num)
theorem B1447757 : Blo 964590 1447757 := bbase (se 3 (by rfl) ⟨271454, by rfl⟩ : syracuseStep 1447757 = 542909) (by norm_num)
theorem B1087321 : Blo 964590 1087321 := bbase (se 2 (by rfl) ⟨407745, by rfl⟩ : syracuseStep 1087321 = 815491) (by norm_num)
theorem B1447781 : Blo 964590 1447781 := bbase (se 4 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 1447781 = 271459) (by norm_num)
theorem B1447805 : Blo 964590 1447805 := bbase (se 3 (by rfl) ⟨271463, by rfl⟩ : syracuseStep 1447805 = 542927) (by norm_num)
theorem B1087357 : Blo 964590 1087357 := bbase (se 3 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 1087357 = 407759) (by norm_num)
theorem B1447829 : Blo 964590 1447829 := bbase (se 6 (by rfl) ⟨33933, by rfl⟩ : syracuseStep 1447829 = 67867) (by norm_num)
theorem B1087393 : Blo 964590 1087393 := bbase (se 2 (by rfl) ⟨407772, by rfl⟩ : syracuseStep 1087393 = 815545) (by norm_num)
theorem B1447853 : Blo 964590 1447853 := bbase (se 3 (by rfl) ⟨271472, by rfl⟩ : syracuseStep 1447853 = 542945) (by norm_num)
theorem B1447877 : Blo 964590 1447877 := bbase (se 4 (by rfl) ⟨135738, by rfl⟩ : syracuseStep 1447877 = 271477) (by norm_num)
theorem B1087429 : Blo 964590 1087429 := bbase (se 4 (by rfl) ⟨101946, by rfl⟩ : syracuseStep 1087429 = 203893) (by norm_num)
theorem B1447901 : Blo 964590 1447901 := bbase (se 3 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 1447901 = 542963) (by norm_num)
theorem B1087465 : Blo 964590 1087465 := bbase (se 2 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 1087465 = 815599) (by norm_num)
theorem B1447925 : Blo 964590 1447925 := bbase (se 5 (by rfl) ⟨67871, by rfl⟩ : syracuseStep 1447925 = 135743) (by norm_num)
theorem B1447949 : Blo 964590 1447949 := bbase (se 3 (by rfl) ⟨271490, by rfl⟩ : syracuseStep 1447949 = 542981) (by norm_num)
theorem B1087501 : Blo 964590 1087501 := bbase (se 3 (by rfl) ⟨203906, by rfl⟩ : syracuseStep 1087501 = 407813) (by norm_num)
theorem B1447973 : Blo 964590 1447973 := bbase (se 4 (by rfl) ⟨135747, by rfl⟩ : syracuseStep 1447973 = 271495) (by norm_num)
theorem B1087537 : Blo 964590 1087537 := bbase (se 2 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 1087537 = 815653) (by norm_num)
theorem B1447997 : Blo 964590 1447997 := bbase (se 3 (by rfl) ⟨271499, by rfl⟩ : syracuseStep 1447997 = 542999) (by norm_num)
theorem B1448021 : Blo 964590 1448021 := bbase (se 8 (by rfl) ⟨8484, by rfl⟩ : syracuseStep 1448021 = 16969) (by norm_num)
theorem B1087573 : Blo 964590 1087573 := bbase (se 8 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 1087573 = 12745) (by norm_num)
theorem B1448045 : Blo 964590 1448045 := bbase (se 3 (by rfl) ⟨271508, by rfl⟩ : syracuseStep 1448045 = 543017) (by norm_num)
theorem B4954229 : Blo 964590 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B1087609 : Blo 964590 1087609 := bbase (se 2 (by rfl) ⟨407853, by rfl⟩ : syracuseStep 1087609 = 815707) (by norm_num)
theorem B1448069 : Blo 964590 1448069 := bbase (se 4 (by rfl) ⟨135756, by rfl⟩ : syracuseStep 1448069 = 271513) (by norm_num)
theorem B1448093 : Blo 964590 1448093 := bbase (se 3 (by rfl) ⟨271517, by rfl⟩ : syracuseStep 1448093 = 543035) (by norm_num)
theorem B1087645 : Blo 964590 1087645 := bbase (se 3 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 1087645 = 407867) (by norm_num)
theorem B1448117 : Blo 964590 1448117 := bbase (se 5 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 1448117 = 135761) (by norm_num)
theorem B1087681 : Blo 964590 1087681 := bbase (se 2 (by rfl) ⟨407880, by rfl⟩ : syracuseStep 1087681 = 815761) (by norm_num)
theorem B1448141 : Blo 964590 1448141 := bbase (se 3 (by rfl) ⟨271526, by rfl⟩ : syracuseStep 1448141 = 543053) (by norm_num)
theorem B1448165 : Blo 964590 1448165 := bbase (se 4 (by rfl) ⟨135765, by rfl⟩ : syracuseStep 1448165 = 271531) (by norm_num)
theorem B1087717 : Blo 964590 1087717 := bbase (se 4 (by rfl) ⟨101973, by rfl⟩ : syracuseStep 1087717 = 203947) (by norm_num)
theorem B1448189 : Blo 964590 1448189 := bbase (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) (by norm_num)
theorem B1087753 : Blo 964590 1087753 := bbase (se 2 (by rfl) ⟨407907, by rfl⟩ : syracuseStep 1087753 = 815815) (by norm_num)
theorem B1448213 : Blo 964590 1448213 := bbase (se 6 (by rfl) ⟨33942, by rfl⟩ : syracuseStep 1448213 = 67885) (by norm_num)
theorem B1448237 : Blo 964590 1448237 := bbase (se 3 (by rfl) ⟨271544, by rfl⟩ : syracuseStep 1448237 = 543089) (by norm_num)
theorem B1087789 : Blo 964590 1087789 := bbase (se 3 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 1087789 = 407921) (by norm_num)
theorem B1743157 : Blo 964590 1743157 := bbase (se 5 (by rfl) ⟨81710, by rfl⟩ : syracuseStep 1743157 = 163421) (by norm_num)
theorem B1448261 : Blo 964590 1448261 := bbase (se 4 (by rfl) ⟨135774, by rfl⟩ : syracuseStep 1448261 = 271549) (by norm_num)
theorem B1087825 : Blo 964590 1087825 := bbase (se 2 (by rfl) ⟨407934, by rfl⟩ : syracuseStep 1087825 = 815869) (by norm_num)
theorem B1448285 : Blo 964590 1448285 := bbase (se 3 (by rfl) ⟨271553, by rfl⟩ : syracuseStep 1448285 = 543107) (by norm_num)
theorem B1448309 : Blo 964590 1448309 := bbase (se 5 (by rfl) ⟨67889, by rfl⟩ : syracuseStep 1448309 = 135779) (by norm_num)
theorem B1087861 : Blo 964590 1087861 := bbase (se 5 (by rfl) ⟨50993, by rfl⟩ : syracuseStep 1087861 = 101987) (by norm_num)
theorem B1448333 : Blo 964590 1448333 := bbase (se 3 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 1448333 = 543125) (by norm_num)
theorem B1087897 : Blo 964590 1087897 := bbase (se 2 (by rfl) ⟨407961, by rfl⟩ : syracuseStep 1087897 = 815923) (by norm_num)
theorem B1448357 : Blo 964590 1448357 := bbase (se 4 (by rfl) ⟨135783, by rfl⟩ : syracuseStep 1448357 = 271567) (by norm_num)
theorem B4888997 : Blo 964590 4888997 := bbase (se 4 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 4888997 = 916687) (by norm_num)
theorem B1448381 : Blo 964590 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B1087933 : Blo 964590 1087933 := bbase (se 3 (by rfl) ⟨203987, by rfl⟩ : syracuseStep 1087933 = 407975) (by norm_num)
theorem B1743301 : Blo 964590 1743301 := bbase (se 4 (by rfl) ⟨163434, by rfl⟩ : syracuseStep 1743301 = 326869) (by norm_num)
theorem B1448405 : Blo 964590 1448405 := bbase (se 7 (by rfl) ⟨16973, by rfl⟩ : syracuseStep 1448405 = 33947) (by norm_num)
theorem B1087969 : Blo 964590 1087969 := bbase (se 2 (by rfl) ⟨407988, by rfl⟩ : syracuseStep 1087969 = 815977) (by norm_num)
theorem B1448429 : Blo 964590 1448429 := bbase (se 3 (by rfl) ⟨271580, by rfl⟩ : syracuseStep 1448429 = 543161) (by norm_num)
theorem B1448453 : Blo 964590 1448453 := bbase (se 4 (by rfl) ⟨135792, by rfl⟩ : syracuseStep 1448453 = 271585) (by norm_num)
theorem B1088005 : Blo 964590 1088005 := bbase (se 4 (by rfl) ⟨102000, by rfl⟩ : syracuseStep 1088005 = 204001) (by norm_num)
theorem B1448477 : Blo 964590 1448477 := bbase (se 3 (by rfl) ⟨271589, by rfl⟩ : syracuseStep 1448477 = 543179) (by norm_num)
theorem B1088041 : Blo 964590 1088041 := bbase (se 2 (by rfl) ⟨408015, by rfl⟩ : syracuseStep 1088041 = 816031) (by norm_num)
theorem B1448501 : Blo 964590 1448501 := bbase (se 5 (by rfl) ⟨67898, by rfl⟩ : syracuseStep 1448501 = 135797) (by norm_num)
theorem B1448525 : Blo 964590 1448525 := bbase (se 3 (by rfl) ⟨271598, by rfl⟩ : syracuseStep 1448525 = 543197) (by norm_num)
theorem B1088077 : Blo 964590 1088077 := bbase (se 3 (by rfl) ⟨204014, by rfl⟩ : syracuseStep 1088077 = 408029) (by norm_num)
theorem B1448549 : Blo 964590 1448549 := bbase (se 4 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 1448549 = 271603) (by norm_num)
theorem B1743461 : Blo 964590 1743461 := bbase (se 4 (by rfl) ⟨163449, by rfl⟩ : syracuseStep 1743461 = 326899) (by norm_num)
theorem B1088113 : Blo 964590 1088113 := bbase (se 2 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 1088113 = 816085) (by norm_num)
theorem B1448573 : Blo 964590 1448573 := bbase (se 3 (by rfl) ⟨271607, by rfl⟩ : syracuseStep 1448573 = 543215) (by norm_num)
theorem B1448597 : Blo 964590 1448597 := bbase (se 6 (by rfl) ⟨33951, by rfl⟩ : syracuseStep 1448597 = 67903) (by norm_num)
theorem B1088149 : Blo 964590 1088149 := bbase (se 6 (by rfl) ⟨25503, by rfl⟩ : syracuseStep 1088149 = 51007) (by norm_num)
theorem B1448621 : Blo 964590 1448621 := bbase (se 3 (by rfl) ⟨271616, by rfl⟩ : syracuseStep 1448621 = 543233) (by norm_num)
theorem B1088185 : Blo 964590 1088185 := bbase (se 2 (by rfl) ⟨408069, by rfl⟩ : syracuseStep 1088185 = 816139) (by norm_num)
theorem B1448645 : Blo 964590 1448645 := bbase (se 4 (by rfl) ⟨135810, by rfl⟩ : syracuseStep 1448645 = 271621) (by norm_num)
theorem B1448669 : Blo 964590 1448669 := bbase (se 3 (by rfl) ⟨271625, by rfl⟩ : syracuseStep 1448669 = 543251) (by norm_num)
theorem B1088221 : Blo 964590 1088221 := bbase (se 3 (by rfl) ⟨204041, by rfl⟩ : syracuseStep 1088221 = 408083) (by norm_num)
theorem B1448693 : Blo 964590 1448693 := bbase (se 5 (by rfl) ⟨67907, by rfl⟩ : syracuseStep 1448693 = 135815) (by norm_num)
theorem B1088257 : Blo 964590 1088257 := bbase (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) (by norm_num)
theorem B1448717 : Blo 964590 1448717 := bbase (se 3 (by rfl) ⟨271634, by rfl⟩ : syracuseStep 1448717 = 543269) (by norm_num)
theorem B1448741 : Blo 964590 1448741 := bbase (se 4 (by rfl) ⟨135819, by rfl⟩ : syracuseStep 1448741 = 271639) (by norm_num)
theorem B1088293 : Blo 964590 1088293 := bbase (se 4 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 1088293 = 204055) (by norm_num)
theorem B1448765 : Blo 964590 1448765 := bbase (se 3 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 1448765 = 543287) (by norm_num)
theorem B1088329 : Blo 964590 1088329 := bbase (se 2 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 1088329 = 816247) (by norm_num)
theorem B1448789 : Blo 964590 1448789 := bbase (se 9 (by rfl) ⟨4244, by rfl⟩ : syracuseStep 1448789 = 8489) (by norm_num)
theorem B1448813 : Blo 964590 1448813 := bbase (se 3 (by rfl) ⟨271652, by rfl⟩ : syracuseStep 1448813 = 543305) (by norm_num)
theorem B1088365 : Blo 964590 1088365 := bbase (se 3 (by rfl) ⟨204068, by rfl⟩ : syracuseStep 1088365 = 408137) (by norm_num)
theorem B1448837 : Blo 964590 1448837 := bbase (se 4 (by rfl) ⟨135828, by rfl⟩ : syracuseStep 1448837 = 271657) (by norm_num)
theorem B1088401 : Blo 964590 1088401 := bbase (se 2 (by rfl) ⟨408150, by rfl⟩ : syracuseStep 1088401 = 816301) (by norm_num)
theorem B1448861 : Blo 964590 1448861 := bbase (se 3 (by rfl) ⟨271661, by rfl⟩ : syracuseStep 1448861 = 543323) (by norm_num)
theorem B8919989 : Blo 964590 8919989 := bbase (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) (by norm_num)
theorem B1448885 : Blo 964590 1448885 := bbase (se 5 (by rfl) ⟨67916, by rfl⟩ : syracuseStep 1448885 = 135833) (by norm_num)
theorem B1088437 : Blo 964590 1088437 := bbase (se 5 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 1088437 = 102041) (by norm_num)
theorem B1448909 : Blo 964590 1448909 := bbase (se 3 (by rfl) ⟨271670, by rfl⟩ : syracuseStep 1448909 = 543341) (by norm_num)
theorem B1088473 : Blo 964590 1088473 := bbase (se 2 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 1088473 = 816355) (by norm_num)
theorem B1448933 : Blo 964590 1448933 := bbase (se 4 (by rfl) ⟨135837, by rfl⟩ : syracuseStep 1448933 = 271675) (by norm_num)
theorem B1448957 : Blo 964590 1448957 := bbase (se 3 (by rfl) ⟨271679, by rfl⟩ : syracuseStep 1448957 = 543359) (by norm_num)
theorem B1088509 : Blo 964590 1088509 := bbase (se 3 (by rfl) ⟨204095, by rfl⟩ : syracuseStep 1088509 = 408191) (by norm_num)
theorem B1448981 : Blo 964590 1448981 := bbase (se 6 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 1448981 = 67921) (by norm_num)
theorem B1088545 : Blo 964590 1088545 := bbase (se 2 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 1088545 = 816409) (by norm_num)
theorem B1449005 : Blo 964590 1449005 := bbase (se 3 (by rfl) ⟨271688, by rfl⟩ : syracuseStep 1449005 = 543377) (by norm_num)
theorem B1449029 : Blo 964590 1449029 := bbase (se 4 (by rfl) ⟨135846, by rfl⟩ : syracuseStep 1449029 = 271693) (by norm_num)
theorem B1088581 : Blo 964590 1088581 := bbase (se 4 (by rfl) ⟨102054, by rfl⟩ : syracuseStep 1088581 = 204109) (by norm_num)
theorem B1449053 : Blo 964590 1449053 := bbase (se 3 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 1449053 = 543395) (by norm_num)
theorem B1088617 : Blo 964590 1088617 := bbase (se 2 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 1088617 = 816463) (by norm_num)
theorem B1449077 : Blo 964590 1449077 := bbase (se 5 (by rfl) ⟨67925, by rfl⟩ : syracuseStep 1449077 = 135851) (by norm_num)
theorem B7445621 : Blo 964590 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B1449101 : Blo 964590 1449101 := bbase (se 3 (by rfl) ⟨271706, by rfl⟩ : syracuseStep 1449101 = 543413) (by norm_num)
theorem B1088653 : Blo 964590 1088653 := bbase (se 3 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 1088653 = 408245) (by norm_num)
theorem B1449125 : Blo 964590 1449125 := bbase (se 4 (by rfl) ⟨135855, by rfl⟩ : syracuseStep 1449125 = 271711) (by norm_num)
theorem B1088689 : Blo 964590 1088689 := bbase (se 2 (by rfl) ⟨408258, by rfl⟩ : syracuseStep 1088689 = 816517) (by norm_num)
theorem B1449149 : Blo 964590 1449149 := bbase (se 3 (by rfl) ⟨271715, by rfl⟩ : syracuseStep 1449149 = 543431) (by norm_num)
theorem B1449173 : Blo 964590 1449173 := bbase (se 7 (by rfl) ⟨16982, by rfl⟩ : syracuseStep 1449173 = 33965) (by norm_num)
theorem B1088725 : Blo 964590 1088725 := bbase (se 7 (by rfl) ⟨12758, by rfl⟩ : syracuseStep 1088725 = 25517) (by norm_num)
theorem B1449197 : Blo 964590 1449197 := bbase (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) (by norm_num)
theorem B6462709 : Blo 964590 6462709 := bbase (se 5 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 6462709 = 605879) (by norm_num)
theorem B1088761 : Blo 964590 1088761 := bbase (se 2 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 1088761 = 816571) (by norm_num)
theorem B1547525 : Blo 964590 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B1449221 : Blo 964590 1449221 := bbase (se 4 (by rfl) ⟨135864, by rfl⟩ : syracuseStep 1449221 = 271729) (by norm_num)
theorem B1449245 : Blo 964590 1449245 := bbase (se 3 (by rfl) ⟨271733, by rfl⟩ : syracuseStep 1449245 = 543467) (by norm_num)
theorem B1088797 : Blo 964590 1088797 := bbase (se 3 (by rfl) ⟨204149, by rfl⟩ : syracuseStep 1088797 = 408299) (by norm_num)
theorem B1449269 : Blo 964590 1449269 := bbase (se 5 (by rfl) ⟨67934, by rfl⟩ : syracuseStep 1449269 = 135869) (by norm_num)
theorem B1088833 : Blo 964590 1088833 := bbase (se 2 (by rfl) ⟨408312, by rfl⟩ : syracuseStep 1088833 = 816625) (by norm_num)
theorem B1449293 : Blo 964590 1449293 := bbase (se 3 (by rfl) ⟨271742, by rfl⟩ : syracuseStep 1449293 = 543485) (by norm_num)
theorem B1449317 : Blo 964590 1449317 := bbase (se 4 (by rfl) ⟨135873, by rfl⟩ : syracuseStep 1449317 = 271747) (by norm_num)
theorem B1088869 : Blo 964590 1088869 := bbase (se 4 (by rfl) ⟨102081, by rfl⟩ : syracuseStep 1088869 = 204163) (by norm_num)
theorem B1449341 : Blo 964590 1449341 := bbase (se 3 (by rfl) ⟨271751, by rfl⟩ : syracuseStep 1449341 = 543503) (by norm_num)
theorem B1088905 : Blo 964590 1088905 := bbase (se 2 (by rfl) ⟨408339, by rfl⟩ : syracuseStep 1088905 = 816679) (by norm_num)
theorem B1449365 : Blo 964590 1449365 := bbase (se 6 (by rfl) ⟨33969, by rfl⟩ : syracuseStep 1449365 = 67939) (by norm_num)
theorem B1449389 : Blo 964590 1449389 := bbase (se 3 (by rfl) ⟨271760, by rfl⟩ : syracuseStep 1449389 = 543521) (by norm_num)
theorem B1088941 : Blo 964590 1088941 := bbase (se 3 (by rfl) ⟨204176, by rfl⟩ : syracuseStep 1088941 = 408353) (by norm_num)
theorem B1449413 : Blo 964590 1449413 := bbase (se 4 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 1449413 = 271765) (by norm_num)
theorem B1088977 : Blo 964590 1088977 := bbase (se 2 (by rfl) ⟨408366, by rfl⟩ : syracuseStep 1088977 = 816733) (by norm_num)
theorem B1449437 : Blo 964590 1449437 := bbase (se 3 (by rfl) ⟨271769, by rfl⟩ : syracuseStep 1449437 = 543539) (by norm_num)
theorem B2170349 : Blo 964590 2170349 := bbase (se 3 (by rfl) ⟨406940, by rfl⟩ : syracuseStep 2170349 = 813881) (by norm_num)
theorem B1449461 : Blo 964590 1449461 := bbase (se 5 (by rfl) ⟨67943, by rfl⟩ : syracuseStep 1449461 = 135887) (by norm_num)
theorem B1089013 : Blo 964590 1089013 := bbase (se 5 (by rfl) ⟨51047, by rfl⟩ : syracuseStep 1089013 = 102095) (by norm_num)
theorem B4136437 : Blo 964590 4136437 := bbase (se 5 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 4136437 = 387791) (by norm_num)
theorem B1449485 : Blo 964590 1449485 := bbase (se 3 (by rfl) ⟨271778, by rfl⟩ : syracuseStep 1449485 = 543557) (by norm_num)
theorem B1089049 : Blo 964590 1089049 := bbase (se 2 (by rfl) ⟨408393, by rfl⟩ : syracuseStep 1089049 = 816787) (by norm_num)
theorem B1449509 : Blo 964590 1449509 := bbase (se 4 (by rfl) ⟨135891, by rfl⟩ : syracuseStep 1449509 = 271783) (by norm_num)
theorem B2170421 : Blo 964590 2170421 := bbase (se 5 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 2170421 = 203477) (by norm_num)
theorem B1449533 : Blo 964590 1449533 := bbase (se 3 (by rfl) ⟨271787, by rfl⟩ : syracuseStep 1449533 = 543575) (by norm_num)
theorem B1089085 : Blo 964590 1089085 := bbase (se 3 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 1089085 = 408407) (by norm_num)
theorem B1449557 : Blo 964590 1449557 := bbase (se 8 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 1449557 = 16987) (by norm_num)
theorem B1089121 : Blo 964590 1089121 := bbase (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) (by norm_num)
theorem B1449581 : Blo 964590 1449581 := bbase (se 3 (by rfl) ⟨271796, by rfl⟩ : syracuseStep 1449581 = 543593) (by norm_num)
theorem B2170493 : Blo 964590 2170493 := bbase (se 3 (by rfl) ⟨406967, by rfl⟩ : syracuseStep 2170493 = 813935) (by norm_num)
theorem B1449605 : Blo 964590 1449605 := bbase (se 4 (by rfl) ⟨135900, by rfl⟩ : syracuseStep 1449605 = 271801) (by norm_num)
theorem B1089157 : Blo 964590 1089157 := bbase (se 4 (by rfl) ⟨102108, by rfl⟩ : syracuseStep 1089157 = 204217) (by norm_num)
theorem B9936533 : Blo 964590 9936533 := bbase (se 6 (by rfl) ⟨232887, by rfl⟩ : syracuseStep 9936533 = 465775) (by norm_num)
theorem B1449629 : Blo 964590 1449629 := bbase (se 3 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 1449629 = 543611) (by norm_num)
theorem B1089193 : Blo 964590 1089193 := bbase (se 2 (by rfl) ⟨408447, by rfl⟩ : syracuseStep 1089193 = 816895) (by norm_num)
theorem B4890293 : Blo 964590 4890293 := bbase (se 5 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 4890293 = 458465) (by norm_num)
theorem B1449653 : Blo 964590 1449653 := bbase (se 5 (by rfl) ⟨67952, by rfl⟩ : syracuseStep 1449653 = 135905) (by norm_num)
theorem B2170565 : Blo 964590 2170565 := bbase (se 4 (by rfl) ⟨203490, by rfl⟩ : syracuseStep 2170565 = 406981) (by norm_num)
theorem B1547981 : Blo 964590 1547981 := bbase (se 3 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 1547981 = 580493) (by norm_num)
theorem B1449677 : Blo 964590 1449677 := bbase (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) (by norm_num)
theorem B1089229 : Blo 964590 1089229 := bbase (se 3 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 1089229 = 408461) (by norm_num)
theorem B3776213 : Blo 964590 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B1449701 : Blo 964590 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B1089265 : Blo 964590 1089265 := bbase (se 2 (by rfl) ⟨408474, by rfl⟩ : syracuseStep 1089265 = 816949) (by norm_num)
theorem B1449725 : Blo 964590 1449725 := bbase (se 3 (by rfl) ⟨271823, by rfl⟩ : syracuseStep 1449725 = 543647) (by norm_num)
theorem B2170637 : Blo 964590 2170637 := bbase (se 3 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 2170637 = 813989) (by norm_num)
theorem B1449749 : Blo 964590 1449749 := bbase (se 6 (by rfl) ⟨33978, by rfl⟩ : syracuseStep 1449749 = 67957) (by norm_num)
theorem B1089301 : Blo 964590 1089301 := bbase (se 6 (by rfl) ⟨25530, by rfl⟩ : syracuseStep 1089301 = 51061) (by norm_num)
theorem B1449773 : Blo 964590 1449773 := bbase (se 3 (by rfl) ⟨271832, by rfl⟩ : syracuseStep 1449773 = 543665) (by norm_num)
theorem B1089337 : Blo 964590 1089337 := bbase (se 2 (by rfl) ⟨408501, by rfl⟩ : syracuseStep 1089337 = 817003) (by norm_num)
theorem B1449797 : Blo 964590 1449797 := bbase (se 4 (by rfl) ⟨135918, by rfl⟩ : syracuseStep 1449797 = 271837) (by norm_num)
theorem B2170709 : Blo 964590 2170709 := bbase (se 9 (by rfl) ⟨6359, by rfl⟩ : syracuseStep 2170709 = 12719) (by norm_num)
theorem B1449821 : Blo 964590 1449821 := bbase (se 3 (by rfl) ⟨271841, by rfl⟩ : syracuseStep 1449821 = 543683) (by norm_num)
theorem B1089373 : Blo 964590 1089373 := bbase (se 3 (by rfl) ⟨204257, by rfl⟩ : syracuseStep 1089373 = 408515) (by norm_num)
theorem B1449845 : Blo 964590 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B1089409 : Blo 964590 1089409 := bbase (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) (by norm_num)
theorem B1449869 : Blo 964590 1449869 := bbase (se 3 (by rfl) ⟨271850, by rfl⟩ : syracuseStep 1449869 = 543701) (by norm_num)
theorem B2170781 : Blo 964590 2170781 := bbase (se 3 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 2170781 = 814043) (by norm_num)
theorem B1449893 : Blo 964590 1449893 := bbase (se 4 (by rfl) ⟨135927, by rfl⟩ : syracuseStep 1449893 = 271855) (by norm_num)
theorem B1089445 : Blo 964590 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1449917 : Blo 964590 1449917 := bbase (se 3 (by rfl) ⟨271859, by rfl⟩ : syracuseStep 1449917 = 543719) (by norm_num)
theorem B1089481 : Blo 964590 1089481 := bbase (se 2 (by rfl) ⟨408555, by rfl⟩ : syracuseStep 1089481 = 817111) (by norm_num)
theorem B1449941 : Blo 964590 1449941 := bbase (se 7 (by rfl) ⟨16991, by rfl⟩ : syracuseStep 1449941 = 33983) (by norm_num)
theorem B2170853 : Blo 964590 2170853 := bbase (se 4 (by rfl) ⟨203517, by rfl⟩ : syracuseStep 2170853 = 407035) (by norm_num)
theorem B1449965 : Blo 964590 1449965 := bbase (se 3 (by rfl) ⟨271868, by rfl⟩ : syracuseStep 1449965 = 543737) (by norm_num)
theorem B1089517 : Blo 964590 1089517 := bbase (se 3 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 1089517 = 408569) (by norm_num)
theorem B1449989 : Blo 964590 1449989 := bbase (se 4 (by rfl) ⟨135936, by rfl⟩ : syracuseStep 1449989 = 271873) (by norm_num)
theorem B1089553 : Blo 964590 1089553 := bbase (se 2 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 1089553 = 817165) (by norm_num)
theorem B1450013 : Blo 964590 1450013 := bbase (se 3 (by rfl) ⟨271877, by rfl⟩ : syracuseStep 1450013 = 543755) (by norm_num)
theorem B2170925 : Blo 964590 2170925 := bbase (se 3 (by rfl) ⟨407048, by rfl⟩ : syracuseStep 2170925 = 814097) (by norm_num)
theorem B1450037 : Blo 964590 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B1089589 : Blo 964590 1089589 := bbase (se 5 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 1089589 = 102149) (by norm_num)
theorem B1450061 : Blo 964590 1450061 := bbase (se 3 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 1450061 = 543773) (by norm_num)
theorem B1089625 : Blo 964590 1089625 := bbase (se 2 (by rfl) ⟨408609, by rfl⟩ : syracuseStep 1089625 = 817219) (by norm_num)
theorem B1450085 : Blo 964590 1450085 := bbase (se 4 (by rfl) ⟨135945, by rfl⟩ : syracuseStep 1450085 = 271891) (by norm_num)
theorem B2170997 : Blo 964590 2170997 := bbase (se 5 (by rfl) ⟨101765, by rfl⟩ : syracuseStep 2170997 = 203531) (by norm_num)
theorem B1450109 : Blo 964590 1450109 := bbase (se 3 (by rfl) ⟨271895, by rfl⟩ : syracuseStep 1450109 = 543791) (by norm_num)
theorem B1089661 : Blo 964590 1089661 := bbase (se 3 (by rfl) ⟨204311, by rfl⟩ : syracuseStep 1089661 = 408623) (by norm_num)
theorem B5873813 : Blo 964590 5873813 := bbase (se 6 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 5873813 = 275335) (by norm_num)
theorem B1450133 : Blo 964590 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B1450157 : Blo 964590 1450157 := bbase (se 3 (by rfl) ⟨271904, by rfl⟩ : syracuseStep 1450157 = 543809) (by norm_num)
theorem B2171069 : Blo 964590 2171069 := bbase (se 3 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 2171069 = 814151) (by norm_num)
theorem B1450181 : Blo 964590 1450181 := bbase (se 4 (by rfl) ⟨135954, by rfl⟩ : syracuseStep 1450181 = 271909) (by norm_num)
theorem B1450205 : Blo 964590 1450205 := bbase (se 3 (by rfl) ⟨271913, by rfl⟩ : syracuseStep 1450205 = 543827) (by norm_num)
theorem B1450229 : Blo 964590 1450229 := bbase (se 5 (by rfl) ⟨67979, by rfl⟩ : syracuseStep 1450229 = 135959) (by norm_num)
theorem B2171141 : Blo 964590 2171141 := bbase (se 4 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 2171141 = 407089) (by norm_num)
theorem B1450253 : Blo 964590 1450253 := bbase (se 3 (by rfl) ⟨271922, by rfl⟩ : syracuseStep 1450253 = 543845) (by norm_num)
theorem B1450277 : Blo 964590 1450277 := bbase (se 4 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 1450277 = 271927) (by norm_num)
theorem B1450301 : Blo 964590 1450301 := bbase (se 3 (by rfl) ⟨271931, by rfl⟩ : syracuseStep 1450301 = 543863) (by norm_num)
theorem B1220933 : Blo 964590 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B2171213 : Blo 964590 2171213 := bbase (se 3 (by rfl) ⟨407102, by rfl⟩ : syracuseStep 2171213 = 814205) (by norm_num)
theorem B1450325 : Blo 964590 1450325 := bbase (se 10 (by rfl) ⟨2124, by rfl⟩ : syracuseStep 1450325 = 4249) (by norm_num)
theorem B1450349 : Blo 964590 1450349 := bbase (se 3 (by rfl) ⟨271940, by rfl⟩ : syracuseStep 1450349 = 543881) (by norm_num)
theorem B1220989 : Blo 964590 1220989 := bbase (se 3 (by rfl) ⟨228935, by rfl⟩ : syracuseStep 1220989 = 457871) (by norm_num)
theorem B1450373 : Blo 964590 1450373 := bbase (se 4 (by rfl) ⟨135972, by rfl⟩ : syracuseStep 1450373 = 271945) (by norm_num)
theorem B2171285 : Blo 964590 2171285 := bbase (se 6 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 2171285 = 101779) (by norm_num)
theorem B1450397 : Blo 964590 1450397 := bbase (se 3 (by rfl) ⟨271949, by rfl⟩ : syracuseStep 1450397 = 543899) (by norm_num)
theorem B1450421 : Blo 964590 1450421 := bbase (se 5 (by rfl) ⟨67988, by rfl⟩ : syracuseStep 1450421 = 135977) (by norm_num)
theorem B1450445 : Blo 964590 1450445 := bbase (se 3 (by rfl) ⟨271958, by rfl⟩ : syracuseStep 1450445 = 543917) (by norm_num)
theorem B1221085 : Blo 964590 1221085 := bbase (se 3 (by rfl) ⟨228953, by rfl⟩ : syracuseStep 1221085 = 457907) (by norm_num)
theorem B2171357 : Blo 964590 2171357 := bbase (se 3 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 2171357 = 814259) (by norm_num)
theorem B1450469 : Blo 964590 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B1450493 : Blo 964590 1450493 := bbase (se 3 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 1450493 = 543935) (by norm_num)
theorem B1450517 : Blo 964590 1450517 := bbase (se 6 (by rfl) ⟨33996, by rfl⟩ : syracuseStep 1450517 = 67993) (by norm_num)
theorem B2171429 : Blo 964590 2171429 := bbase (se 4 (by rfl) ⟨203571, by rfl⟩ : syracuseStep 2171429 = 407143) (by norm_num)
theorem B3482149 : Blo 964590 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B1450541 : Blo 964590 1450541 := bbase (se 3 (by rfl) ⟨271976, by rfl⟩ : syracuseStep 1450541 = 543953) (by norm_num)
theorem B1450565 : Blo 964590 1450565 := bbase (se 4 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 1450565 = 271981) (by norm_num)
theorem B5218901 : Blo 964590 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B1450589 : Blo 964590 1450589 := bbase (se 3 (by rfl) ⟨271985, by rfl⟩ : syracuseStep 1450589 = 543971) (by norm_num)
theorem B2171501 : Blo 964590 2171501 := bbase (se 3 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 2171501 = 814313) (by norm_num)
theorem B1450613 : Blo 964590 1450613 := bbase (se 5 (by rfl) ⟨67997, by rfl⟩ : syracuseStep 1450613 = 135995) (by norm_num)
theorem B1221257 : Blo 964590 1221257 := bbase (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) (by norm_num)
theorem B1450637 : Blo 964590 1450637 := bbase (se 3 (by rfl) ⟨271994, by rfl⟩ : syracuseStep 1450637 = 543989) (by norm_num)
theorem B1450661 : Blo 964590 1450661 := bbase (se 4 (by rfl) ⟨135999, by rfl⟩ : syracuseStep 1450661 = 271999) (by norm_num)
theorem B1548973 : Blo 964590 1548973 := bbase (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) (by norm_num)
theorem B2171573 : Blo 964590 2171573 := bbase (se 5 (by rfl) ⟨101792, by rfl⟩ : syracuseStep 2171573 = 203585) (by norm_num)
theorem B1450685 : Blo 964590 1450685 := bbase (se 3 (by rfl) ⟨272003, by rfl⟩ : syracuseStep 1450685 = 544007) (by norm_num)
theorem B1221313 : Blo 964590 1221313 := bbase (se 2 (by rfl) ⟨457992, by rfl⟩ : syracuseStep 1221313 = 915985) (by norm_num)
theorem B1450709 : Blo 964590 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B1450733 : Blo 964590 1450733 := bbase (se 3 (by rfl) ⟨272012, by rfl⟩ : syracuseStep 1450733 = 544025) (by norm_num)
theorem B2171645 : Blo 964590 2171645 := bbase (se 3 (by rfl) ⟨407183, by rfl⟩ : syracuseStep 2171645 = 814367) (by norm_num)
theorem B1450757 : Blo 964590 1450757 := bbase (se 4 (by rfl) ⟨136008, by rfl⟩ : syracuseStep 1450757 = 272017) (by norm_num)
theorem B5219093 : Blo 964590 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1450781 : Blo 964590 1450781 := bbase (se 3 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 1450781 = 544043) (by norm_num)
theorem B1221409 : Blo 964590 1221409 := bbase (se 2 (by rfl) ⟨458028, by rfl⟩ : syracuseStep 1221409 = 916057) (by norm_num)
theorem B1450805 : Blo 964590 1450805 := bbase (se 5 (by rfl) ⟨68006, by rfl⟩ : syracuseStep 1450805 = 136013) (by norm_num)
theorem B2171717 : Blo 964590 2171717 := bbase (se 4 (by rfl) ⟨203598, by rfl⟩ : syracuseStep 2171717 = 407197) (by norm_num)
theorem B1450829 : Blo 964590 1450829 := bbase (se 3 (by rfl) ⟨272030, by rfl⟩ : syracuseStep 1450829 = 544061) (by norm_num)
theorem B1450853 : Blo 964590 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1450877 : Blo 964590 1450877 := bbase (se 3 (by rfl) ⟨272039, by rfl⟩ : syracuseStep 1450877 = 544079) (by norm_num)
theorem B2171789 : Blo 964590 2171789 := bbase (se 3 (by rfl) ⟨407210, by rfl⟩ : syracuseStep 2171789 = 814421) (by norm_num)
theorem B1450901 : Blo 964590 1450901 := bbase (se 6 (by rfl) ⟨34005, by rfl⟩ : syracuseStep 1450901 = 68011) (by norm_num)
theorem B1450925 : Blo 964590 1450925 := bbase (se 3 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 1450925 = 544097) (by norm_num)
theorem B4891589 : Blo 964590 4891589 := bbase (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) (by norm_num)
theorem B1450949 : Blo 964590 1450949 := bbase (se 4 (by rfl) ⟨136026, by rfl⟩ : syracuseStep 1450949 = 272053) (by norm_num)
theorem B1221581 : Blo 964590 1221581 := bbase (se 3 (by rfl) ⟨229046, by rfl⟩ : syracuseStep 1221581 = 458093) (by norm_num)
theorem B2171861 : Blo 964590 2171861 := bbase (se 7 (by rfl) ⟨25451, by rfl⟩ : syracuseStep 2171861 = 50903) (by norm_num)
theorem B1450973 : Blo 964590 1450973 := bbase (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) (by norm_num)
theorem B1450997 : Blo 964590 1450997 := bbase (se 5 (by rfl) ⟨68015, by rfl⟩ : syracuseStep 1450997 = 136031) (by norm_num)
theorem B1221637 : Blo 964590 1221637 := bbase (se 4 (by rfl) ⟨114528, by rfl⟩ : syracuseStep 1221637 = 229057) (by norm_num)
theorem B1451021 : Blo 964590 1451021 := bbase (se 3 (by rfl) ⟨272066, by rfl⟩ : syracuseStep 1451021 = 544133) (by norm_num)
theorem B2171933 : Blo 964590 2171933 := bbase (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) (by norm_num)
theorem B1451045 : Blo 964590 1451045 := bbase (se 4 (by rfl) ⟨136035, by rfl⟩ : syracuseStep 1451045 = 272071) (by norm_num)
theorem B1451069 : Blo 964590 1451069 := bbase (se 3 (by rfl) ⟨272075, by rfl⟩ : syracuseStep 1451069 = 544151) (by norm_num)
theorem B5022805 : Blo 964590 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B1451093 : Blo 964590 1451093 := bbase (se 8 (by rfl) ⟨8502, by rfl⟩ : syracuseStep 1451093 = 17005) (by norm_num)
theorem B6202453 : Blo 964590 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B1221733 : Blo 964590 1221733 := bbase (se 4 (by rfl) ⟨114537, by rfl⟩ : syracuseStep 1221733 = 229075) (by norm_num)
theorem B2172005 : Blo 964590 2172005 := bbase (se 4 (by rfl) ⟨203625, by rfl⟩ : syracuseStep 2172005 = 407251) (by norm_num)
theorem B1451117 : Blo 964590 1451117 := bbase (se 3 (by rfl) ⟨272084, by rfl⟩ : syracuseStep 1451117 = 544169) (by norm_num)
theorem B1451141 : Blo 964590 1451141 := bbase (se 4 (by rfl) ⟨136044, by rfl⟩ : syracuseStep 1451141 = 272089) (by norm_num)
theorem B1451165 : Blo 964590 1451165 := bbase (se 3 (by rfl) ⟨272093, by rfl⟩ : syracuseStep 1451165 = 544187) (by norm_num)
theorem B2172077 : Blo 964590 2172077 := bbase (se 3 (by rfl) ⟨407264, by rfl⟩ : syracuseStep 2172077 = 814529) (by norm_num)
theorem B1451189 : Blo 964590 1451189 := bbase (se 5 (by rfl) ⟨68024, by rfl⟩ : syracuseStep 1451189 = 136049) (by norm_num)
theorem B1451213 : Blo 964590 1451213 := bbase (se 3 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 1451213 = 544205) (by norm_num)
theorem B1451237 : Blo 964590 1451237 := bbase (se 4 (by rfl) ⟨136053, by rfl⟩ : syracuseStep 1451237 = 272107) (by norm_num)
theorem B2172149 : Blo 964590 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B1451261 : Blo 964590 1451261 := bbase (se 3 (by rfl) ⟨272111, by rfl⟩ : syracuseStep 1451261 = 544223) (by norm_num)
theorem B1221905 : Blo 964590 1221905 := bbase (se 2 (by rfl) ⟨458214, by rfl⟩ : syracuseStep 1221905 = 916429) (by norm_num)
theorem B1451285 : Blo 964590 1451285 := bbase (se 6 (by rfl) ⟨34014, by rfl⟩ : syracuseStep 1451285 = 68029) (by norm_num)
theorem B1451309 : Blo 964590 1451309 := bbase (se 3 (by rfl) ⟨272120, by rfl⟩ : syracuseStep 1451309 = 544241) (by norm_num)
theorem B1549621 : Blo 964590 1549621 := bbase (se 5 (by rfl) ⟨72638, by rfl⟩ : syracuseStep 1549621 = 145277) (by norm_num)
theorem B2172221 : Blo 964590 2172221 := bbase (se 3 (by rfl) ⟨407291, by rfl⟩ : syracuseStep 2172221 = 814583) (by norm_num)
theorem B1451333 : Blo 964590 1451333 := bbase (se 4 (by rfl) ⟨136062, by rfl⟩ : syracuseStep 1451333 = 272125) (by norm_num)
theorem B1221961 : Blo 964590 1221961 := bbase (se 2 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 1221961 = 916471) (by norm_num)
theorem B1451357 : Blo 964590 1451357 := bbase (se 3 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 1451357 = 544259) (by norm_num)
theorem B1451381 : Blo 964590 1451381 := bbase (se 5 (by rfl) ⟨68033, by rfl⟩ : syracuseStep 1451381 = 136067) (by norm_num)
theorem B2172293 : Blo 964590 2172293 := bbase (se 4 (by rfl) ⟨203652, by rfl⟩ : syracuseStep 2172293 = 407305) (by norm_num)
theorem B1451405 : Blo 964590 1451405 := bbase (se 3 (by rfl) ⟨272138, by rfl⟩ : syracuseStep 1451405 = 544277) (by norm_num)
theorem B1451429 : Blo 964590 1451429 := bbase (se 4 (by rfl) ⟨136071, by rfl⟩ : syracuseStep 1451429 = 272143) (by norm_num)
theorem B1222057 : Blo 964590 1222057 := bbase (se 2 (by rfl) ⟨458271, by rfl⟩ : syracuseStep 1222057 = 916543) (by norm_num)
theorem B1451453 : Blo 964590 1451453 := bbase (se 3 (by rfl) ⟨272147, by rfl⟩ : syracuseStep 1451453 = 544295) (by norm_num)
theorem B2172365 : Blo 964590 2172365 := bbase (se 3 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 2172365 = 814637) (by norm_num)
theorem B1451477 : Blo 964590 1451477 := bbase (se 7 (by rfl) ⟨17009, by rfl⟩ : syracuseStep 1451477 = 34019) (by norm_num)
theorem B1451501 : Blo 964590 1451501 := bbase (se 3 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 1451501 = 544313) (by norm_num)
theorem B1451525 : Blo 964590 1451525 := bbase (se 4 (by rfl) ⟨136080, by rfl⟩ : syracuseStep 1451525 = 272161) (by norm_num)
theorem B2041357 : Blo 964590 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B2172437 : Blo 964590 2172437 := bbase (se 6 (by rfl) ⟨50916, by rfl⟩ : syracuseStep 2172437 = 101833) (by norm_num)
theorem B1451549 : Blo 964590 1451549 := bbase (se 3 (by rfl) ⟨272165, by rfl⟩ : syracuseStep 1451549 = 544331) (by norm_num)
theorem B6956597 : Blo 964590 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B1451573 : Blo 964590 1451573 := bbase (se 5 (by rfl) ⟨68042, by rfl⟩ : syracuseStep 1451573 = 136085) (by norm_num)
theorem B1451597 : Blo 964590 1451597 := bbase (se 3 (by rfl) ⟨272174, by rfl⟩ : syracuseStep 1451597 = 544349) (by norm_num)
theorem B1222229 : Blo 964590 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B2172509 : Blo 964590 2172509 := bbase (se 3 (by rfl) ⟨407345, by rfl⟩ : syracuseStep 2172509 = 814691) (by norm_num)
theorem B1451621 : Blo 964590 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B1451645 : Blo 964590 1451645 := bbase (se 3 (by rfl) ⟨272183, by rfl⟩ : syracuseStep 1451645 = 544367) (by norm_num)
theorem B1222285 : Blo 964590 1222285 := bbase (se 3 (by rfl) ⟨229178, by rfl⟩ : syracuseStep 1222285 = 458357) (by norm_num)
theorem B1451669 : Blo 964590 1451669 := bbase (se 6 (by rfl) ⟨34023, by rfl⟩ : syracuseStep 1451669 = 68047) (by norm_num)
theorem B2172581 : Blo 964590 2172581 := bbase (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) (by norm_num)
theorem B1451693 : Blo 964590 1451693 := bbase (se 3 (by rfl) ⟨272192, by rfl⟩ : syracuseStep 1451693 = 544385) (by norm_num)
theorem B1451717 : Blo 964590 1451717 := bbase (se 4 (by rfl) ⟨136098, by rfl⟩ : syracuseStep 1451717 = 272197) (by norm_num)
theorem B1451741 : Blo 964590 1451741 := bbase (se 3 (by rfl) ⟨272201, by rfl⟩ : syracuseStep 1451741 = 544403) (by norm_num)
theorem B2238173 : Blo 964590 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B2172653 : Blo 964590 2172653 := bbase (se 3 (by rfl) ⟨407372, by rfl⟩ : syracuseStep 2172653 = 814745) (by norm_num)
theorem B1222381 : Blo 964590 1222381 := bbase (se 3 (by rfl) ⟨229196, by rfl⟩ : syracuseStep 1222381 = 458393) (by norm_num)
theorem B1451765 : Blo 964590 1451765 := bbase (se 5 (by rfl) ⟨68051, by rfl⟩ : syracuseStep 1451765 = 136103) (by norm_num)
theorem B1451789 : Blo 964590 1451789 := bbase (se 3 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 1451789 = 544421) (by norm_num)
theorem B1451813 : Blo 964590 1451813 := bbase (se 4 (by rfl) ⟨136107, by rfl⟩ : syracuseStep 1451813 = 272215) (by norm_num)
theorem B2172725 : Blo 964590 2172725 := bbase (se 5 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 2172725 = 203693) (by norm_num)
theorem B1451837 : Blo 964590 1451837 := bbase (se 3 (by rfl) ⟨272219, by rfl⟩ : syracuseStep 1451837 = 544439) (by norm_num)
theorem B1451861 : Blo 964590 1451861 := bbase (se 9 (by rfl) ⟨4253, by rfl⟩ : syracuseStep 1451861 = 8507) (by norm_num)
theorem B1451885 : Blo 964590 1451885 := bbase (se 3 (by rfl) ⟨272228, by rfl⟩ : syracuseStep 1451885 = 544457) (by norm_num)
theorem B2172797 : Blo 964590 2172797 := bbase (se 3 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 2172797 = 814799) (by norm_num)
theorem B1451909 : Blo 964590 1451909 := bbase (se 4 (by rfl) ⟨136116, by rfl⟩ : syracuseStep 1451909 = 272233) (by norm_num)
theorem B1222553 : Blo 964590 1222553 := bbase (se 2 (by rfl) ⟨458457, by rfl⟩ : syracuseStep 1222553 = 916915) (by norm_num)
theorem B1451933 : Blo 964590 1451933 := bbase (se 3 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 1451933 = 544475) (by norm_num)
theorem B1451957 : Blo 964590 1451957 := bbase (se 5 (by rfl) ⟨68060, by rfl⟩ : syracuseStep 1451957 = 136121) (by norm_num)
theorem B2172869 : Blo 964590 2172869 := bbase (se 4 (by rfl) ⟨203706, by rfl⟩ : syracuseStep 2172869 = 407413) (by norm_num)
theorem B1451981 : Blo 964590 1451981 := bbase (se 3 (by rfl) ⟨272246, by rfl⟩ : syracuseStep 1451981 = 544493) (by norm_num)
theorem B1222609 : Blo 964590 1222609 := bbase (se 2 (by rfl) ⟨458478, by rfl⟩ : syracuseStep 1222609 = 916957) (by norm_num)
theorem B1452005 : Blo 964590 1452005 := bbase (se 4 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 1452005 = 272251) (by norm_num)
theorem B1452029 : Blo 964590 1452029 := bbase (se 3 (by rfl) ⟨272255, by rfl⟩ : syracuseStep 1452029 = 544511) (by norm_num)
theorem B3090437 : Blo 964590 3090437 := bbase (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) (by norm_num)
theorem B2172941 : Blo 964590 2172941 := bbase (se 3 (by rfl) ⟨407426, by rfl⟩ : syracuseStep 2172941 = 814853) (by norm_num)
theorem B1452053 : Blo 964590 1452053 := bbase (se 6 (by rfl) ⟨34032, by rfl⟩ : syracuseStep 1452053 = 68065) (by norm_num)
theorem B1452077 : Blo 964590 1452077 := bbase (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) (by norm_num)
theorem B1222705 : Blo 964590 1222705 := bbase (se 2 (by rfl) ⟨458514, by rfl⟩ : syracuseStep 1222705 = 917029) (by norm_num)
theorem B1452101 : Blo 964590 1452101 := bbase (se 4 (by rfl) ⟨136134, by rfl⟩ : syracuseStep 1452101 = 272269) (by norm_num)
theorem B2173013 : Blo 964590 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1452125 : Blo 964590 1452125 := bbase (se 3 (by rfl) ⟨272273, by rfl⟩ : syracuseStep 1452125 = 544547) (by norm_num)
theorem B1452149 : Blo 964590 1452149 := bbase (se 5 (by rfl) ⟨68069, by rfl⟩ : syracuseStep 1452149 = 136139) (by norm_num)
theorem B3090565 : Blo 964590 3090565 := bbase (se 4 (by rfl) ⟨289740, by rfl⟩ : syracuseStep 3090565 = 579481) (by norm_num)
theorem B1452173 : Blo 964590 1452173 := bbase (se 3 (by rfl) ⟨272282, by rfl⟩ : syracuseStep 1452173 = 544565) (by norm_num)
theorem B2173085 : Blo 964590 2173085 := bbase (se 3 (by rfl) ⟨407453, by rfl⟩ : syracuseStep 2173085 = 814907) (by norm_num)
theorem B1452197 : Blo 964590 1452197 := bbase (se 4 (by rfl) ⟨136143, by rfl⟩ : syracuseStep 1452197 = 272287) (by norm_num)
theorem B1452221 : Blo 964590 1452221 := bbase (se 3 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 1452221 = 544583) (by norm_num)
theorem B4892885 : Blo 964590 4892885 := bbase (se 7 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 4892885 = 114677) (by norm_num)
theorem B1550549 : Blo 964590 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B1452245 : Blo 964590 1452245 := bbase (se 7 (by rfl) ⟨17018, by rfl⟩ : syracuseStep 1452245 = 34037) (by norm_num)
theorem B1222877 : Blo 964590 1222877 := bbase (se 3 (by rfl) ⟨229289, by rfl⟩ : syracuseStep 1222877 = 458579) (by norm_num)
theorem B2173157 : Blo 964590 2173157 := bbase (se 4 (by rfl) ⟨203733, by rfl⟩ : syracuseStep 2173157 = 407467) (by norm_num)
theorem B1452269 : Blo 964590 1452269 := bbase (se 3 (by rfl) ⟨272300, by rfl⟩ : syracuseStep 1452269 = 544601) (by norm_num)
theorem B1452293 : Blo 964590 1452293 := bbase (se 4 (by rfl) ⟨136152, by rfl⟩ : syracuseStep 1452293 = 272305) (by norm_num)
theorem B1222933 : Blo 964590 1222933 := bbase (se 6 (by rfl) ⟨28662, by rfl⟩ : syracuseStep 1222933 = 57325) (by norm_num)
theorem B1452317 : Blo 964590 1452317 := bbase (se 3 (by rfl) ⟨272309, by rfl⟩ : syracuseStep 1452317 = 544619) (by norm_num)
theorem B2173229 : Blo 964590 2173229 := bbase (se 3 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 2173229 = 814961) (by norm_num)
theorem B1452341 : Blo 964590 1452341 := bbase (se 5 (by rfl) ⟨68078, by rfl⟩ : syracuseStep 1452341 = 136157) (by norm_num)
theorem B1452365 : Blo 964590 1452365 := bbase (se 3 (by rfl) ⟨272318, by rfl⟩ : syracuseStep 1452365 = 544637) (by norm_num)
theorem B1452389 : Blo 964590 1452389 := bbase (se 4 (by rfl) ⟨136161, by rfl⟩ : syracuseStep 1452389 = 272323) (by norm_num)
theorem B2173301 : Blo 964590 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B1223029 : Blo 964590 1223029 := bbase (se 5 (by rfl) ⟨57329, by rfl⟩ : syracuseStep 1223029 = 114659) (by norm_num)
theorem B1452413 : Blo 964590 1452413 := bbase (se 3 (by rfl) ⟨272327, by rfl⟩ : syracuseStep 1452413 = 544655) (by norm_num)
theorem B1452437 : Blo 964590 1452437 := bbase (se 6 (by rfl) ⟨34041, by rfl⟩ : syracuseStep 1452437 = 68083) (by norm_num)
theorem B1452461 : Blo 964590 1452461 := bbase (se 3 (by rfl) ⟨272336, by rfl⟩ : syracuseStep 1452461 = 544673) (by norm_num)
theorem B2173373 : Blo 964590 2173373 := bbase (se 3 (by rfl) ⟨407507, by rfl⟩ : syracuseStep 2173373 = 815015) (by norm_num)
theorem B1452485 : Blo 964590 1452485 := bbase (se 4 (by rfl) ⟨136170, by rfl⟩ : syracuseStep 1452485 = 272341) (by norm_num)
theorem B1452509 : Blo 964590 1452509 := bbase (se 3 (by rfl) ⟨272345, by rfl⟩ : syracuseStep 1452509 = 544691) (by norm_num)
theorem B1452533 : Blo 964590 1452533 := bbase (se 5 (by rfl) ⟨68087, by rfl⟩ : syracuseStep 1452533 = 136175) (by norm_num)
theorem B2173445 : Blo 964590 2173445 := bbase (se 4 (by rfl) ⟨203760, by rfl⟩ : syracuseStep 2173445 = 407521) (by norm_num)
theorem B1452557 : Blo 964590 1452557 := bbase (se 3 (by rfl) ⟨272354, by rfl⟩ : syracuseStep 1452557 = 544709) (by norm_num)
theorem B5286421 : Blo 964590 5286421 := bbase (se 6 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 5286421 = 247801) (by norm_num)
theorem B1223201 : Blo 964590 1223201 := bbase (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) (by norm_num)
theorem B1452581 : Blo 964590 1452581 := bbase (se 4 (by rfl) ⟨136179, by rfl⟩ : syracuseStep 1452581 = 272359) (by norm_num)
theorem B1321525 : Blo 964590 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1452605 : Blo 964590 1452605 := bbase (se 3 (by rfl) ⟨272363, by rfl⟩ : syracuseStep 1452605 = 544727) (by norm_num)
theorem B2173517 : Blo 964590 2173517 := bbase (se 3 (by rfl) ⟨407534, by rfl⟩ : syracuseStep 2173517 = 815069) (by norm_num)
theorem B1452629 : Blo 964590 1452629 := bbase (se 8 (by rfl) ⟨8511, by rfl⟩ : syracuseStep 1452629 = 17023) (by norm_num)
theorem B1223257 : Blo 964590 1223257 := bbase (se 2 (by rfl) ⟨458721, by rfl⟩ : syracuseStep 1223257 = 917443) (by norm_num)
theorem B1452653 : Blo 964590 1452653 := bbase (se 3 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 1452653 = 544745) (by norm_num)
theorem B1452677 : Blo 964590 1452677 := bbase (se 4 (by rfl) ⟨136188, by rfl⟩ : syracuseStep 1452677 = 272377) (by norm_num)
theorem B2206349 : Blo 964590 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B2173589 : Blo 964590 2173589 := bbase (se 6 (by rfl) ⟨50943, by rfl⟩ : syracuseStep 2173589 = 101887) (by norm_num)
theorem B3353237 : Blo 964590 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B1551005 : Blo 964590 1551005 := bbase (se 3 (by rfl) ⟨290813, by rfl⟩ : syracuseStep 1551005 = 581627) (by norm_num)
theorem B1452701 : Blo 964590 1452701 := bbase (se 3 (by rfl) ⟨272381, by rfl⟩ : syracuseStep 1452701 = 544763) (by norm_num)
theorem B1452725 : Blo 964590 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B1223353 : Blo 964590 1223353 := bbase (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) (by norm_num)
theorem B1452749 : Blo 964590 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B2173661 : Blo 964590 2173661 := bbase (se 3 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 2173661 = 815123) (by norm_num)
theorem B1452773 : Blo 964590 1452773 := bbase (se 4 (by rfl) ⟨136197, by rfl⟩ : syracuseStep 1452773 = 272395) (by norm_num)
theorem B1452797 : Blo 964590 1452797 := bbase (se 3 (by rfl) ⟨272399, by rfl⟩ : syracuseStep 1452797 = 544799) (by norm_num)
theorem B1452821 : Blo 964590 1452821 := bbase (se 6 (by rfl) ⟨34050, by rfl⟩ : syracuseStep 1452821 = 68101) (by norm_num)
theorem B2173733 : Blo 964590 2173733 := bbase (se 4 (by rfl) ⟨203787, by rfl⟩ : syracuseStep 2173733 = 407575) (by norm_num)
theorem B1452845 : Blo 964590 1452845 := bbase (se 3 (by rfl) ⟨272408, by rfl⟩ : syracuseStep 1452845 = 544817) (by norm_num)
theorem B1452869 : Blo 964590 1452869 := bbase (se 4 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 1452869 = 272413) (by norm_num)
theorem B1223525 : Blo 964590 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B2173805 : Blo 964590 2173805 := bbase (se 3 (by rfl) ⟨407588, by rfl⟩ : syracuseStep 2173805 = 815177) (by norm_num)
theorem B1223581 : Blo 964590 1223581 := bbase (se 3 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 1223581 = 458843) (by norm_num)
theorem B2173877 : Blo 964590 2173877 := bbase (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) (by norm_num)
theorem B2173949 : Blo 964590 2173949 := bbase (se 3 (by rfl) ⟨407615, by rfl⟩ : syracuseStep 2173949 = 815231) (by norm_num)
theorem B1223677 : Blo 964590 1223677 := bbase (se 3 (by rfl) ⟨229439, by rfl⟩ : syracuseStep 1223677 = 458879) (by norm_num)
theorem B2174021 : Blo 964590 2174021 := bbase (se 4 (by rfl) ⟨203814, by rfl⟩ : syracuseStep 2174021 = 407629) (by norm_num)
theorem B3484757 : Blo 964590 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B2174093 : Blo 964590 2174093 := bbase (se 3 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 2174093 = 815285) (by norm_num)
theorem B1223849 : Blo 964590 1223849 := bbase (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) (by norm_num)
theorem B2174165 : Blo 964590 2174165 := bbase (se 7 (by rfl) ⟨25478, by rfl⟩ : syracuseStep 2174165 = 50957) (by norm_num)
theorem B1223905 : Blo 964590 1223905 := bbase (se 2 (by rfl) ⟨458964, by rfl⟩ : syracuseStep 1223905 = 917929) (by norm_num)
theorem B1551637 : Blo 964590 1551637 := bbase (se 6 (by rfl) ⟨36366, by rfl⟩ : syracuseStep 1551637 = 72733) (by norm_num)
theorem B2174237 : Blo 964590 2174237 := bbase (se 3 (by rfl) ⟨407669, by rfl⟩ : syracuseStep 2174237 = 815339) (by norm_num)
theorem B3255605 : Blo 964590 3255605 := bbase (se 5 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 3255605 = 305213) (by norm_num)
theorem B5221685 : Blo 964590 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B1224001 : Blo 964590 1224001 := bbase (se 2 (by rfl) ⟨459000, by rfl⟩ : syracuseStep 1224001 = 918001) (by norm_num)
theorem B2174309 : Blo 964590 2174309 := bbase (se 4 (by rfl) ⟨203841, by rfl⟩ : syracuseStep 2174309 = 407683) (by norm_num)
theorem B3485045 : Blo 964590 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B2174381 : Blo 964590 2174381 := bbase (se 3 (by rfl) ⟨407696, by rfl⟩ : syracuseStep 2174381 = 815393) (by norm_num)
theorem B4894181 : Blo 964590 4894181 := bbase (se 4 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 4894181 = 917659) (by norm_num)
theorem B1224173 : Blo 964590 1224173 := bbase (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) (by norm_num)
theorem B2174453 : Blo 964590 2174453 := bbase (se 5 (by rfl) ⟨101927, by rfl⟩ : syracuseStep 2174453 = 203855) (by norm_num)
theorem B1224229 : Blo 964590 1224229 := bbase (se 4 (by rfl) ⟨114771, by rfl⟩ : syracuseStep 1224229 = 229543) (by norm_num)
theorem B2174525 : Blo 964590 2174525 := bbase (se 3 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 2174525 = 815447) (by norm_num)
theorem B2174597 : Blo 964590 2174597 := bbase (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) (by norm_num)
theorem B1224325 : Blo 964590 1224325 := bbase (se 4 (by rfl) ⟨114780, by rfl⟩ : syracuseStep 1224325 = 229561) (by norm_num)
theorem B1158833 : Blo 964590 1158833 := bbase (se 2 (by rfl) ⟨434562, by rfl⟩ : syracuseStep 1158833 = 869125) (by norm_num)
theorem B2174669 : Blo 964590 2174669 := bbase (se 3 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 2174669 = 815501) (by norm_num)
theorem B3256037 : Blo 964590 3256037 := bbase (se 4 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 3256037 = 610507) (by norm_num)
theorem B2174741 : Blo 964590 2174741 := bbase (se 6 (by rfl) ⟨50970, by rfl⟩ : syracuseStep 2174741 = 101941) (by norm_num)
theorem B1224497 : Blo 964590 1224497 := bbase (se 2 (by rfl) ⟨459186, by rfl⟩ : syracuseStep 1224497 = 918373) (by norm_num)
theorem B2174813 : Blo 964590 2174813 := bbase (se 3 (by rfl) ⟨407777, by rfl⟩ : syracuseStep 2174813 = 815555) (by norm_num)
theorem B1224553 : Blo 964590 1224553 := bbase (se 2 (by rfl) ⟨459207, by rfl⟩ : syracuseStep 1224553 = 918415) (by norm_num)
theorem B2174885 : Blo 964590 2174885 := bbase (se 4 (by rfl) ⟨203895, by rfl⟩ : syracuseStep 2174885 = 407791) (by norm_num)
theorem B1224649 : Blo 964590 1224649 := bbase (se 2 (by rfl) ⟨459243, by rfl⟩ : syracuseStep 1224649 = 918487) (by norm_num)
theorem B39727061 : Blo 964590 39727061 := bbase (se 7 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 39727061 = 931103) (by norm_num)
theorem B2174957 : Blo 964590 2174957 := bbase (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) (by norm_num)
theorem B2175029 : Blo 964590 2175029 := bbase (se 5 (by rfl) ⟨101954, by rfl⟩ : syracuseStep 2175029 = 203909) (by norm_num)
theorem B1224821 : Blo 964590 1224821 := bbase (se 5 (by rfl) ⟨57413, by rfl⟩ : syracuseStep 1224821 = 114827) (by norm_num)
theorem B2175101 : Blo 964590 2175101 := bbase (se 3 (by rfl) ⟨407831, by rfl⟩ : syracuseStep 2175101 = 815663) (by norm_num)
theorem B3256469 : Blo 964590 3256469 := bbase (se 6 (by rfl) ⟨76323, by rfl⟩ : syracuseStep 3256469 = 152647) (by norm_num)
theorem B1224877 : Blo 964590 1224877 := bbase (se 3 (by rfl) ⟨229664, by rfl⟩ : syracuseStep 1224877 = 459329) (by norm_num)
theorem B2175173 : Blo 964590 2175173 := bbase (se 4 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 2175173 = 407845) (by norm_num)
theorem B2175245 : Blo 964590 2175245 := bbase (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) (by norm_num)
theorem B1224973 : Blo 964590 1224973 := bbase (se 3 (by rfl) ⟨229682, by rfl⟩ : syracuseStep 1224973 = 459365) (by norm_num)
theorem B2175317 : Blo 964590 2175317 := bbase (se 10 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 2175317 = 6373) (by norm_num)
theorem B7352693 : Blo 964590 7352693 := bbase (se 5 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 7352693 = 689315) (by norm_num)
theorem B7942549 : Blo 964590 7942549 := bbase (se 6 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 7942549 = 372307) (by norm_num)
theorem B2175389 : Blo 964590 2175389 := bbase (se 3 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 2175389 = 815771) (by norm_num)
theorem B1225145 : Blo 964590 1225145 := bbase (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) (by norm_num)
theorem B2175461 : Blo 964590 2175461 := bbase (se 4 (by rfl) ⟨203949, by rfl⟩ : syracuseStep 2175461 = 407899) (by norm_num)
theorem B1225201 : Blo 964590 1225201 := bbase (se 2 (by rfl) ⟨459450, by rfl⟩ : syracuseStep 1225201 = 918901) (by norm_num)
theorem B2175533 : Blo 964590 2175533 := bbase (se 3 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 2175533 = 815825) (by norm_num)
theorem B3256901 : Blo 964590 3256901 := bbase (se 4 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 3256901 = 610669) (by norm_num)
theorem B1225297 : Blo 964590 1225297 := bbase (se 2 (by rfl) ⟨459486, by rfl⟩ : syracuseStep 1225297 = 918973) (by norm_num)
theorem B2175605 : Blo 964590 2175605 := bbase (se 5 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 2175605 = 203963) (by norm_num)
theorem B2175677 : Blo 964590 2175677 := bbase (se 3 (by rfl) ⟨407939, by rfl⟩ : syracuseStep 2175677 = 815879) (by norm_num)
theorem B4895477 : Blo 964590 4895477 := bbase (se 5 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 4895477 = 458951) (by norm_num)
theorem B1225469 : Blo 964590 1225469 := bbase (se 3 (by rfl) ⟨229775, by rfl⟩ : syracuseStep 1225469 = 459551) (by norm_num)
theorem B2175749 : Blo 964590 2175749 := bbase (se 4 (by rfl) ⟨203976, by rfl⟩ : syracuseStep 2175749 = 407953) (by norm_num)
theorem B1225525 : Blo 964590 1225525 := bbase (se 5 (by rfl) ⟨57446, by rfl⟩ : syracuseStep 1225525 = 114893) (by norm_num)
theorem B2175821 : Blo 964590 2175821 := bbase (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) (by norm_num)
theorem B1160029 : Blo 964590 1160029 := bbase (se 3 (by rfl) ⟨217505, by rfl⟩ : syracuseStep 1160029 = 435011) (by norm_num)
theorem B2175893 : Blo 964590 2175893 := bbase (se 6 (by rfl) ⟨50997, by rfl⟩ : syracuseStep 2175893 = 101995) (by norm_num)
theorem B1225621 : Blo 964590 1225621 := bbase (se 6 (by rfl) ⟨28725, by rfl⟩ : syracuseStep 1225621 = 57451) (by norm_num)
theorem B1160101 : Blo 964590 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B3093461 : Blo 964590 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B2175965 : Blo 964590 2175965 := bbase (se 3 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 2175965 = 815987) (by norm_num)
theorem B3257333 : Blo 964590 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B2176037 : Blo 964590 2176037 := bbase (se 4 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 2176037 = 408007) (by norm_num)
theorem B1225793 : Blo 964590 1225793 := bbase (se 2 (by rfl) ⟨459672, by rfl⟩ : syracuseStep 1225793 = 919345) (by norm_num)
theorem B2176109 : Blo 964590 2176109 := bbase (se 3 (by rfl) ⟨408020, by rfl⟩ : syracuseStep 2176109 = 816041) (by norm_num)
theorem B1225849 : Blo 964590 1225849 := bbase (se 2 (by rfl) ⟨459693, by rfl⟩ : syracuseStep 1225849 = 919387) (by norm_num)
theorem B2176181 : Blo 964590 2176181 := bbase (se 5 (by rfl) ⟨102008, by rfl⟩ : syracuseStep 2176181 = 204017) (by norm_num)
theorem B2176253 : Blo 964590 2176253 := bbase (se 3 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 2176253 = 816095) (by norm_num)
theorem B1652005 : Blo 964590 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B2176325 : Blo 964590 2176325 := bbase (se 4 (by rfl) ⟨204030, by rfl⟩ : syracuseStep 2176325 = 408061) (by norm_num)
theorem B2176397 : Blo 964590 2176397 := bbase (se 3 (by rfl) ⟨408074, by rfl⟩ : syracuseStep 2176397 = 816149) (by norm_num)
theorem B4404629 : Blo 964590 4404629 := bbase (se 6 (by rfl) ⟨103233, by rfl⟩ : syracuseStep 4404629 = 206467) (by norm_num)
theorem B1258909 : Blo 964590 1258909 := bbase (se 3 (by rfl) ⟨236045, by rfl⟩ : syracuseStep 1258909 = 472091) (by norm_num)
theorem B3257765 : Blo 964590 3257765 := bbase (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) (by norm_num)
theorem B3716533 : Blo 964590 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2176469 : Blo 964590 2176469 := bbase (se 7 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 2176469 = 51011) (by norm_num)
theorem B2176541 : Blo 964590 2176541 := bbase (se 3 (by rfl) ⟨408101, by rfl⟩ : syracuseStep 2176541 = 816203) (by norm_num)
theorem B1652285 : Blo 964590 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B2176613 : Blo 964590 2176613 := bbase (se 4 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 2176613 = 408115) (by norm_num)
theorem B2176685 : Blo 964590 2176685 := bbase (se 3 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 2176685 = 816257) (by norm_num)
theorem B2176757 : Blo 964590 2176757 := bbase (se 5 (by rfl) ⟨102035, by rfl⟩ : syracuseStep 2176757 = 204071) (by norm_num)
theorem B2176829 : Blo 964590 2176829 := bbase (se 3 (by rfl) ⟨408155, by rfl⟩ : syracuseStep 2176829 = 816311) (by norm_num)
theorem B3258197 : Blo 964590 3258197 := bbase (se 9 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 3258197 = 19091) (by norm_num)
theorem B2176901 : Blo 964590 2176901 := bbase (se 4 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 2176901 = 408169) (by norm_num)
theorem B1161101 : Blo 964590 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B2176973 : Blo 964590 2176973 := bbase (se 3 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 2176973 = 816365) (by norm_num)
theorem B4896773 : Blo 964590 4896773 := bbase (se 4 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 4896773 = 918145) (by norm_num)
theorem B2177045 : Blo 964590 2177045 := bbase (se 6 (by rfl) ⟨51024, by rfl⟩ : syracuseStep 2177045 = 102049) (by norm_num)
theorem B2177117 : Blo 964590 2177117 := bbase (se 3 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 2177117 = 816419) (by norm_num)
theorem B2177189 : Blo 964590 2177189 := bbase (se 4 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 2177189 = 408223) (by norm_num)
theorem B1030325 : Blo 964590 1030325 := bbase (se 5 (by rfl) ⟨48296, by rfl⟩ : syracuseStep 1030325 = 96593) (by norm_num)
theorem B2177261 : Blo 964590 2177261 := bbase (se 3 (by rfl) ⟨408236, by rfl⟩ : syracuseStep 2177261 = 816473) (by norm_num)
theorem B3258629 : Blo 964590 3258629 := bbase (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) (by norm_num)
theorem B2177333 : Blo 964590 2177333 := bbase (se 5 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 2177333 = 204125) (by norm_num)
theorem B2177405 : Blo 964590 2177405 := bbase (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) (by norm_num)
theorem B1030573 : Blo 964590 1030573 := bbase (se 3 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 1030573 = 386465) (by norm_num)
theorem B2177477 : Blo 964590 2177477 := bbase (se 4 (by rfl) ⟨204138, by rfl⟩ : syracuseStep 2177477 = 408277) (by norm_num)
theorem B2177549 : Blo 964590 2177549 := bbase (se 3 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 2177549 = 816581) (by norm_num)
theorem B1489469 : Blo 964590 1489469 := bbase (se 3 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 1489469 = 558551) (by norm_num)
theorem B1161793 : Blo 964590 1161793 := bbase (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) (by norm_num)
theorem B1161797 : Blo 964590 1161797 := bbase (se 4 (by rfl) ⟨108918, by rfl⟩ : syracuseStep 1161797 = 217837) (by norm_num)
theorem B2177621 : Blo 964590 2177621 := bbase (se 8 (by rfl) ⟨12759, by rfl⟩ : syracuseStep 2177621 = 25519) (by norm_num)
theorem B10074773 : Blo 964590 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B2177693 : Blo 964590 2177693 := bbase (se 3 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 2177693 = 816635) (by norm_num)
theorem B3259061 : Blo 964590 3259061 := bbase (se 5 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 3259061 = 305537) (by norm_num)
theorem B2177765 : Blo 964590 2177765 := bbase (se 4 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 2177765 = 408331) (by norm_num)
theorem B4406021 : Blo 964590 4406021 := bbase (se 4 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 4406021 = 826129) (by norm_num)
theorem B2177837 : Blo 964590 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B7060277 : Blo 964590 7060277 := bbase (se 5 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 7060277 = 661901) (by norm_num)
theorem B1031017 : Blo 964590 1031017 := bbase (se 2 (by rfl) ⟨386631, by rfl⟩ : syracuseStep 1031017 = 773263) (by norm_num)
theorem B2177909 : Blo 964590 2177909 := bbase (se 5 (by rfl) ⟨102089, by rfl⟩ : syracuseStep 2177909 = 204179) (by norm_num)
theorem B1031077 : Blo 964590 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B2177981 : Blo 964590 2177981 := bbase (se 3 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 2177981 = 816743) (by norm_num)
theorem B1653709 : Blo 964590 1653709 := bbase (se 3 (by rfl) ⟨310070, by rfl⟩ : syracuseStep 1653709 = 620141) (by norm_num)
theorem B3718133 : Blo 964590 3718133 := bbase (se 5 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 3718133 = 348575) (by norm_num)
theorem B2178053 : Blo 964590 2178053 := bbase (se 4 (by rfl) ⟨204192, by rfl⟩ : syracuseStep 2178053 = 408385) (by norm_num)
theorem B1162297 : Blo 964590 1162297 := bbase (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) (by norm_num)
theorem B2178125 : Blo 964590 2178125 := bbase (se 3 (by rfl) ⟨408398, by rfl⟩ : syracuseStep 2178125 = 816797) (by norm_num)
theorem B3259493 : Blo 964590 3259493 := bbase (se 4 (by rfl) ⟨305577, by rfl⟩ : syracuseStep 3259493 = 611155) (by norm_num)
theorem B3095653 : Blo 964590 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B2178197 : Blo 964590 2178197 := bbase (se 6 (by rfl) ⟨51051, by rfl⟩ : syracuseStep 2178197 = 102103) (by norm_num)
theorem B2178269 : Blo 964590 2178269 := bbase (se 3 (by rfl) ⟨408425, by rfl⟩ : syracuseStep 2178269 = 816851) (by norm_num)
theorem B1031393 : Blo 964590 1031393 := bbase (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) (by norm_num)
theorem B4898069 : Blo 964590 4898069 := bbase (se 6 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 4898069 = 229597) (by norm_num)
theorem B2178341 : Blo 964590 2178341 := bbase (se 4 (by rfl) ⟨204219, by rfl⟩ : syracuseStep 2178341 = 408439) (by norm_num)
theorem B2178413 : Blo 964590 2178413 := bbase (se 3 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 2178413 = 816905) (by norm_num)
theorem B2178485 : Blo 964590 2178485 := bbase (se 5 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 2178485 = 204233) (by norm_num)
theorem B1162681 : Blo 964590 1162681 := bbase (se 2 (by rfl) ⟨436005, by rfl⟩ : syracuseStep 1162681 = 872011) (by norm_num)
theorem B2178557 : Blo 964590 2178557 := bbase (se 3 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 2178557 = 816959) (by norm_num)
theorem B3259925 : Blo 964590 3259925 := bbase (se 6 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 3259925 = 152809) (by norm_num)
theorem B2178629 : Blo 964590 2178629 := bbase (se 4 (by rfl) ⟨204246, by rfl⟩ : syracuseStep 2178629 = 408493) (by norm_num)
theorem B2178701 : Blo 964590 2178701 := bbase (se 3 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 2178701 = 817013) (by norm_num)
theorem B1031837 : Blo 964590 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B2178773 : Blo 964590 2178773 := bbase (se 7 (by rfl) ⟨25532, by rfl⟩ : syracuseStep 2178773 = 51065) (by norm_num)
theorem B1031897 : Blo 964590 1031897 := bbase (se 2 (by rfl) ⟨386961, by rfl⟩ : syracuseStep 1031897 = 773923) (by norm_num)
theorem B2178845 : Blo 964590 2178845 := bbase (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) (by norm_num)
theorem B1032025 : Blo 964590 1032025 := bbase (se 2 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 1032025 = 774019) (by norm_num)
theorem B2178917 : Blo 964590 2178917 := bbase (se 4 (by rfl) ⟨204273, by rfl⟩ : syracuseStep 2178917 = 408547) (by norm_num)
theorem B3096485 : Blo 964590 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B2178989 : Blo 964590 2178989 := bbase (se 3 (by rfl) ⟨408560, by rfl⟩ : syracuseStep 2178989 = 817121) (by norm_num)
theorem B3260357 : Blo 964590 3260357 := bbase (se 4 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 3260357 = 611317) (by norm_num)
theorem B2179061 : Blo 964590 2179061 := bbase (se 5 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 2179061 = 204287) (by norm_num)
theorem B2179133 : Blo 964590 2179133 := bbase (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) (by norm_num)
theorem B2179205 : Blo 964590 2179205 := bbase (se 4 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 2179205 = 408601) (by norm_num)
theorem B2179277 : Blo 964590 2179277 := bbase (se 3 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 2179277 = 817229) (by norm_num)
theorem B4636885 : Blo 964590 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B1032469 : Blo 964590 1032469 := bbase (se 6 (by rfl) ⟨24198, by rfl⟩ : syracuseStep 1032469 = 48397) (by norm_num)
theorem B1163585 : Blo 964590 1163585 := bbase (se 2 (by rfl) ⟨436344, by rfl⟩ : syracuseStep 1163585 = 872689) (by norm_num)
theorem B3260789 : Blo 964590 3260789 := bbase (se 5 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 3260789 = 305699) (by norm_num)
theorem B1032589 : Blo 964590 1032589 := bbase (se 3 (by rfl) ⟨193610, by rfl⟩ : syracuseStep 1032589 = 387221) (by norm_num)
theorem B4964885 : Blo 964590 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B4899365 : Blo 964590 4899365 := bbase (se 4 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 4899365 = 918631) (by norm_num)
theorem B2441765 : Blo 964590 2441765 := bbase (se 4 (by rfl) ⟨228915, by rfl⟩ : syracuseStep 2441765 = 457831) (by norm_num)
theorem B1032841 : Blo 964590 1032841 := bbase (se 2 (by rfl) ⟨387315, by rfl⟩ : syracuseStep 1032841 = 774631) (by norm_num)
theorem B1032845 : Blo 964590 1032845 := bbase (se 3 (by rfl) ⟨193658, by rfl⟩ : syracuseStep 1032845 = 387317) (by norm_num)
theorem B3261221 : Blo 964590 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B3490613 : Blo 964590 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B2442109 : Blo 964590 2442109 := bbase (se 3 (by rfl) ⟨457895, by rfl⟩ : syracuseStep 2442109 = 915791) (by norm_num)
theorem B2442221 : Blo 964590 2442221 := bbase (se 3 (by rfl) ⟨457916, by rfl⟩ : syracuseStep 2442221 = 915833) (by norm_num)
theorem B2442413 : Blo 964590 2442413 := bbase (se 3 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 2442413 = 915905) (by norm_num)
theorem B2933941 : Blo 964590 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1033409 : Blo 964590 1033409 := bbase (se 2 (by rfl) ⟨387528, by rfl⟩ : syracuseStep 1033409 = 775057) (by norm_num)
theorem B3261653 : Blo 964590 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B2934085 : Blo 964590 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B1033597 : Blo 964590 1033597 := bbase (se 3 (by rfl) ⟨193799, by rfl⟩ : syracuseStep 1033597 = 387599) (by norm_num)
theorem B5883349 : Blo 964590 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B1394173 : Blo 964590 1394173 := bbase (se 3 (by rfl) ⟨261407, by rfl⟩ : syracuseStep 1394173 = 522815) (by norm_num)
theorem B2442757 : Blo 964590 2442757 := bbase (se 4 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 2442757 = 458017) (by norm_num)
theorem B2442869 : Blo 964590 2442869 := bbase (se 5 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 2442869 = 229019) (by norm_num)
theorem B3262085 : Blo 964590 3262085 := bbase (se 4 (by rfl) ⟨305820, by rfl⟩ : syracuseStep 3262085 = 611641) (by norm_num)
theorem B3098357 : Blo 964590 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B2443061 : Blo 964590 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B4900661 : Blo 964590 4900661 := bbase (se 5 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 4900661 = 459437) (by norm_num)
theorem B3262517 : Blo 964590 3262517 := bbase (se 5 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 3262517 = 305861) (by norm_num)
theorem B2443405 : Blo 964590 2443405 := bbase (se 3 (by rfl) ⟨458138, by rfl⟩ : syracuseStep 2443405 = 916277) (by norm_num)
theorem B2443517 : Blo 964590 2443517 := bbase (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) (by norm_num)
theorem B2607461 : Blo 964590 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B2935205 : Blo 964590 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B4180405 : Blo 964590 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B2443709 : Blo 964590 2443709 := bbase (se 3 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 2443709 = 916391) (by norm_num)
theorem B2935253 : Blo 964590 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B3262949 : Blo 964590 3262949 := bbase (se 4 (by rfl) ⟨305901, by rfl⟩ : syracuseStep 3262949 = 611803) (by norm_num)
theorem B1100461 : Blo 964590 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B8833781 : Blo 964590 8833781 := bbase (se 5 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 8833781 = 828167) (by norm_num)
theorem B2444053 : Blo 964590 2444053 := bbase (se 6 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 2444053 = 114565) (by norm_num)
theorem B1395541 : Blo 964590 1395541 := bbase (se 9 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 1395541 = 8177) (by norm_num)
theorem B2444165 : Blo 964590 2444165 := bbase (se 4 (by rfl) ⟨229140, by rfl⟩ : syracuseStep 2444165 = 458281) (by norm_num)
theorem B3263381 : Blo 964590 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B4410325 : Blo 964590 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B2444357 : Blo 964590 2444357 := bbase (se 4 (by rfl) ⟨229158, by rfl⟩ : syracuseStep 2444357 = 458317) (by norm_num)
theorem B4901957 : Blo 964590 4901957 := bbase (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) (by norm_num)
theorem B2608357 : Blo 964590 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B3263813 : Blo 964590 3263813 := bbase (se 4 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 3263813 = 611965) (by norm_num)
theorem B11750741 : Blo 964590 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B2444701 : Blo 964590 2444701 := bbase (se 3 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 2444701 = 916763) (by norm_num)
theorem B2444813 : Blo 964590 2444813 := bbase (se 3 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 2444813 = 916805) (by norm_num)
theorem B2445005 : Blo 964590 2445005 := bbase (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) (by norm_num)
theorem B3264245 : Blo 964590 3264245 := bbase (se 5 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 3264245 = 306023) (by norm_num)
theorem B2477893 : Blo 964590 2477893 := bbase (se 4 (by rfl) ⟨232302, by rfl⟩ : syracuseStep 2477893 = 464605) (by norm_num)
theorem B2543605 : Blo 964590 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B2445349 : Blo 964590 2445349 := bbase (se 4 (by rfl) ⟨229251, by rfl⟩ : syracuseStep 2445349 = 458503) (by norm_num)
theorem B1101961 : Blo 964590 1101961 := bbase (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) (by norm_num)
theorem B2445461 : Blo 964590 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B3723413 : Blo 964590 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B3264677 : Blo 964590 3264677 := bbase (se 4 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 3264677 = 612127) (by norm_num)
theorem B4903157 : Blo 964590 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B4641077 : Blo 964590 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B23482709 : Blo 964590 23482709 := bbase (se 10 (by rfl) ⟨34398, by rfl⟩ : syracuseStep 23482709 = 68797) (by norm_num)
theorem B2445653 : Blo 964590 2445653 := bbase (se 10 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 2445653 = 7165) (by norm_num)
theorem B4903253 : Blo 964590 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B3101125 : Blo 964590 3101125 := bbase (se 4 (by rfl) ⟨290730, by rfl⟩ : syracuseStep 3101125 = 581461) (by norm_num)
theorem B3265109 : Blo 964590 3265109 := bbase (se 8 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 3265109 = 38263) (by norm_num)
theorem B2445997 : Blo 964590 2445997 := bbase (se 3 (by rfl) ⟨458624, by rfl⟩ : syracuseStep 2445997 = 917249) (by norm_num)
theorem B2446109 : Blo 964590 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B5493653 : Blo 964590 5493653 := bbase (se 6 (by rfl) ⟨128757, by rfl⟩ : syracuseStep 5493653 = 257515) (by norm_num)
theorem B2446301 : Blo 964590 2446301 := bbase (se 3 (by rfl) ⟨458681, by rfl⟩ : syracuseStep 2446301 = 917363) (by norm_num)
theorem B1102837 : Blo 964590 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B3265541 : Blo 964590 3265541 := bbase (se 4 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 3265541 = 612289) (by norm_num)
theorem B8246357 : Blo 964590 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B2446645 : Blo 964590 2446645 := bbase (se 5 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 2446645 = 229373) (by norm_num)
theorem B2446757 : Blo 964590 2446757 := bbase (se 4 (by rfl) ⟨229383, by rfl⟩ : syracuseStep 2446757 = 458767) (by norm_num)
theorem B3265973 : Blo 964590 3265973 := bbase (se 5 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 3265973 = 306185) (by norm_num)
theorem B7329365 : Blo 964590 7329365 := bbase (se 8 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 7329365 = 85891) (by norm_num)
theorem B2446949 : Blo 964590 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B1627789 : Blo 964590 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B1627877 : Blo 964590 1627877 := bbase (se 4 (by rfl) ⟨152613, by rfl⟩ : syracuseStep 1627877 = 305227) (by norm_num)
theorem B1628005 : Blo 964590 1628005 := bbase (se 4 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 1628005 = 305251) (by norm_num)
theorem B3266405 : Blo 964590 3266405 := bbase (se 4 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 3266405 = 612451) (by norm_num)
theorem B1955765 : Blo 964590 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B1628093 : Blo 964590 1628093 := bbase (se 3 (by rfl) ⟨305267, by rfl⟩ : syracuseStep 1628093 = 610535) (by norm_num)
theorem B2447293 : Blo 964590 2447293 := bbase (se 3 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 2447293 = 917735) (by norm_num)
theorem B2447405 : Blo 964590 2447405 := bbase (se 3 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 2447405 = 917777) (by norm_num)
theorem B5494837 : Blo 964590 5494837 := bbase (se 5 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 5494837 = 515141) (by norm_num)
theorem B1628221 : Blo 964590 1628221 := bbase (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) (by norm_num)
theorem B5232757 : Blo 964590 5232757 := bbase (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) (by norm_num)
theorem B1628309 : Blo 964590 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B1104041 : Blo 964590 1104041 := bbase (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) (by norm_num)
theorem B1104077 : Blo 964590 1104077 := bbase (se 3 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 1104077 = 414029) (by norm_num)
theorem B2447597 : Blo 964590 2447597 := bbase (se 3 (by rfl) ⟨458924, by rfl⟩ : syracuseStep 2447597 = 917849) (by norm_num)
theorem B1628437 : Blo 964590 1628437 := bbase (se 6 (by rfl) ⟨38166, by rfl⟩ : syracuseStep 1628437 = 76333) (by norm_num)
theorem B3266837 : Blo 964590 3266837 := bbase (se 6 (by rfl) ⟨76566, by rfl⟩ : syracuseStep 3266837 = 153133) (by norm_num)
theorem B2611493 : Blo 964590 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B1628525 : Blo 964590 1628525 := bbase (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) (by norm_num)
theorem B1628653 : Blo 964590 1628653 := bbase (se 3 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 1628653 = 610745) (by norm_num)
theorem B1628741 : Blo 964590 1628741 := bbase (se 4 (by rfl) ⟨152694, by rfl⟩ : syracuseStep 1628741 = 305389) (by norm_num)
theorem B2447941 : Blo 964590 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B2349685 : Blo 964590 2349685 := bbase (se 5 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 2349685 = 220283) (by norm_num)
theorem B2120357 : Blo 964590 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2448053 : Blo 964590 2448053 := bbase (se 5 (by rfl) ⟨114752, by rfl⟩ : syracuseStep 2448053 = 229505) (by norm_num)
theorem B1628869 : Blo 964590 1628869 := bbase (se 4 (by rfl) ⟨152706, by rfl⟩ : syracuseStep 1628869 = 305413) (by norm_num)
theorem B3267269 : Blo 964590 3267269 := bbase (se 4 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 3267269 = 612613) (by norm_num)
theorem B1628957 : Blo 964590 1628957 := bbase (se 3 (by rfl) ⟨305429, by rfl⟩ : syracuseStep 1628957 = 610859) (by norm_num)
theorem B1858405 : Blo 964590 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B2448245 : Blo 964590 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B1629085 : Blo 964590 1629085 := bbase (se 3 (by rfl) ⟨305453, by rfl⟩ : syracuseStep 1629085 = 610907) (by norm_num)
theorem B4709333 : Blo 964590 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B1629173 : Blo 964590 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1956917 : Blo 964590 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B17849429 : Blo 964590 17849429 := bbase (se 8 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 17849429 = 209173) (by norm_num)
theorem B1629301 : Blo 964590 1629301 := bbase (se 5 (by rfl) ⟨76373, by rfl⟩ : syracuseStep 1629301 = 152747) (by norm_num)
theorem B3267701 : Blo 964590 3267701 := bbase (se 5 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 3267701 = 306347) (by norm_num)
theorem B1629389 : Blo 964590 1629389 := bbase (se 3 (by rfl) ⟨305510, by rfl⟩ : syracuseStep 1629389 = 611021) (by norm_num)
theorem B2448589 : Blo 964590 2448589 := bbase (se 3 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 2448589 = 918221) (by norm_num)
theorem B2448701 : Blo 964590 2448701 := bbase (se 3 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 2448701 = 918263) (by norm_num)
theorem B1629517 : Blo 964590 1629517 := bbase (se 3 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 1629517 = 611069) (by norm_num)
theorem B1629605 : Blo 964590 1629605 := bbase (se 4 (by rfl) ⟨152775, by rfl⟩ : syracuseStep 1629605 = 305551) (by norm_num)
theorem B2448893 : Blo 964590 2448893 := bbase (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) (by norm_num)
theorem B1629733 : Blo 964590 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B3268133 : Blo 964590 3268133 := bbase (se 4 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 3268133 = 612775) (by norm_num)
theorem B1629821 : Blo 964590 1629821 := bbase (se 3 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 1629821 = 611183) (by norm_num)
theorem B2317981 : Blo 964590 2317981 := bbase (se 3 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 2317981 = 869243) (by norm_num)
theorem B3301093 : Blo 964590 3301093 := bbase (se 4 (by rfl) ⟨309477, by rfl⟩ : syracuseStep 3301093 = 618955) (by norm_num)
theorem B1629949 : Blo 964590 1629949 := bbase (se 3 (by rfl) ⟨305615, by rfl⟩ : syracuseStep 1629949 = 611231) (by norm_num)
theorem B4185877 : Blo 964590 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B2449237 : Blo 964590 2449237 := bbase (se 9 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 2449237 = 14351) (by norm_num)
theorem B1630037 : Blo 964590 1630037 := bbase (se 9 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 1630037 = 9551) (by norm_num)
theorem B3137381 : Blo 964590 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B1007461 : Blo 964590 1007461 := bbase (se 4 (by rfl) ⟨94449, by rfl⟩ : syracuseStep 1007461 = 188899) (by norm_num)
theorem B2318213 : Blo 964590 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B2449349 : Blo 964590 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B1630165 : Blo 964590 1630165 := bbase (se 7 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 1630165 = 38207) (by norm_num)
theorem B3268565 : Blo 964590 3268565 := bbase (se 7 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 3268565 = 76607) (by norm_num)
theorem B5496821 : Blo 964590 5496821 := bbase (se 5 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 5496821 = 515327) (by norm_num)
theorem B2318357 : Blo 964590 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B1630253 : Blo 964590 1630253 := bbase (se 3 (by rfl) ⟨305672, by rfl⟩ : syracuseStep 1630253 = 611345) (by norm_num)
theorem B2449541 : Blo 964590 2449541 := bbase (se 4 (by rfl) ⟨229644, by rfl⟩ : syracuseStep 2449541 = 459289) (by norm_num)
theorem B1630381 : Blo 964590 1630381 := bbase (se 3 (by rfl) ⟨305696, by rfl⟩ : syracuseStep 1630381 = 611393) (by norm_num)
theorem B2318597 : Blo 964590 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B1630469 : Blo 964590 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B1630597 : Blo 964590 1630597 := bbase (se 4 (by rfl) ⟨152868, by rfl⟩ : syracuseStep 1630597 = 305737) (by norm_num)
theorem B1630685 : Blo 964590 1630685 := bbase (se 3 (by rfl) ⟨305753, by rfl⟩ : syracuseStep 1630685 = 611507) (by norm_num)
theorem B2449885 : Blo 964590 2449885 := bbase (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) (by norm_num)
theorem B2449997 : Blo 964590 2449997 := bbase (se 3 (by rfl) ⟨459374, by rfl⟩ : syracuseStep 2449997 = 918749) (by norm_num)
theorem B1630813 : Blo 964590 1630813 := bbase (se 3 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 1630813 = 611555) (by norm_num)
theorem B1630901 : Blo 964590 1630901 := bbase (se 5 (by rfl) ⟨76448, by rfl⟩ : syracuseStep 1630901 = 152897) (by norm_num)
theorem B2482933 : Blo 964590 2482933 := bbase (se 5 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 2482933 = 232775) (by norm_num)
theorem B2450189 : Blo 964590 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B1631029 : Blo 964590 1631029 := bbase (se 5 (by rfl) ⟨76454, by rfl⟩ : syracuseStep 1631029 = 152909) (by norm_num)
theorem B1958717 : Blo 964590 1958717 := bbase (se 3 (by rfl) ⟨367259, by rfl⟩ : syracuseStep 1958717 = 734519) (by norm_num)
theorem B1631117 : Blo 964590 1631117 := bbase (se 3 (by rfl) ⟨305834, by rfl⟩ : syracuseStep 1631117 = 611669) (by norm_num)
theorem B2319365 : Blo 964590 2319365 := bbase (se 4 (by rfl) ⟨217440, by rfl⟩ : syracuseStep 2319365 = 434881) (by norm_num)
theorem B1631245 : Blo 964590 1631245 := bbase (se 3 (by rfl) ⟨305858, by rfl⟩ : syracuseStep 1631245 = 611717) (by norm_num)
theorem B1631333 : Blo 964590 1631333 := bbase (se 4 (by rfl) ⟨152937, by rfl⟩ : syracuseStep 1631333 = 305875) (by norm_num)
theorem B2450533 : Blo 964590 2450533 := bbase (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) (by norm_num)
theorem B2450645 : Blo 964590 2450645 := bbase (se 7 (by rfl) ⟨28718, by rfl⟩ : syracuseStep 2450645 = 57437) (by norm_num)
theorem B1631461 : Blo 964590 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B1631549 : Blo 964590 1631549 := bbase (se 3 (by rfl) ⟨305915, by rfl⟩ : syracuseStep 1631549 = 611831) (by norm_num)
theorem B1467749 : Blo 964590 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B2450837 : Blo 964590 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B1467821 : Blo 964590 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1631677 : Blo 964590 1631677 := bbase (se 3 (by rfl) ⟨305939, by rfl⟩ : syracuseStep 1631677 = 611879) (by norm_num)
theorem B4122085 : Blo 964590 4122085 := bbase (se 4 (by rfl) ⟨386445, by rfl⟩ : syracuseStep 4122085 = 772891) (by norm_num)
theorem B2942453 : Blo 964590 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1631765 : Blo 964590 1631765 := bbase (se 6 (by rfl) ⟨38244, by rfl⟩ : syracuseStep 1631765 = 76489) (by norm_num)
theorem B23881301 : Blo 964590 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B6186613 : Blo 964590 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B1631893 : Blo 964590 1631893 := bbase (se 6 (by rfl) ⟨38247, by rfl⟩ : syracuseStep 1631893 = 76495) (by norm_num)
theorem B3663589 : Blo 964590 3663589 := bbase (se 4 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 3663589 = 686923) (by norm_num)
theorem B1631981 : Blo 964590 1631981 := bbase (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) (by norm_num)
theorem B2451181 : Blo 964590 2451181 := bbase (se 3 (by rfl) ⟨459596, by rfl⟩ : syracuseStep 2451181 = 919193) (by norm_num)
theorem B2451293 : Blo 964590 2451293 := bbase (se 3 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 2451293 = 919235) (by norm_num)
theorem B1632109 : Blo 964590 1632109 := bbase (se 3 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 1632109 = 612041) (by norm_num)
theorem B1468309 : Blo 964590 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B1959877 : Blo 964590 1959877 := bbase (se 4 (by rfl) ⟨183738, by rfl⟩ : syracuseStep 1959877 = 367477) (by norm_num)
theorem B1632197 : Blo 964590 1632197 := bbase (se 4 (by rfl) ⟨153018, by rfl⟩ : syracuseStep 1632197 = 306037) (by norm_num)
theorem B1304525 : Blo 964590 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B1468405 : Blo 964590 1468405 := bbase (se 5 (by rfl) ⟨68831, by rfl⟩ : syracuseStep 1468405 = 137663) (by norm_num)
theorem B1239049 : Blo 964590 1239049 := bbase (se 2 (by rfl) ⟨464643, by rfl⟩ : syracuseStep 1239049 = 929287) (by norm_num)
theorem B3663893 : Blo 964590 3663893 := bbase (se 6 (by rfl) ⟨85872, by rfl⟩ : syracuseStep 3663893 = 171745) (by norm_num)
theorem B2451485 : Blo 964590 2451485 := bbase (se 3 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 2451485 = 919307) (by norm_num)
theorem B1632325 : Blo 964590 1632325 := bbase (se 4 (by rfl) ⟨153030, by rfl⟩ : syracuseStep 1632325 = 306061) (by norm_num)
theorem B2615429 : Blo 964590 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B5499029 : Blo 964590 5499029 := bbase (se 6 (by rfl) ⟨128883, by rfl⟩ : syracuseStep 5499029 = 257767) (by norm_num)
theorem B2943125 : Blo 964590 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1632413 : Blo 964590 1632413 := bbase (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) (by norm_num)
theorem B1632541 : Blo 964590 1632541 := bbase (se 3 (by rfl) ⟨306101, by rfl⟩ : syracuseStep 1632541 = 612203) (by norm_num)
theorem B2320741 : Blo 964590 2320741 := bbase (se 4 (by rfl) ⟨217569, by rfl⟩ : syracuseStep 2320741 = 435139) (by norm_num)
theorem B7825781 : Blo 964590 7825781 := bbase (se 5 (by rfl) ⟨366833, by rfl⟩ : syracuseStep 7825781 = 733667) (by norm_num)
theorem B1632629 : Blo 964590 1632629 := bbase (se 5 (by rfl) ⟨76529, by rfl⟩ : syracuseStep 1632629 = 153059) (by norm_num)
theorem B1632757 : Blo 964590 1632757 := bbase (se 5 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 1632757 = 153071) (by norm_num)
theorem B2353661 : Blo 964590 2353661 := bbase (se 3 (by rfl) ⟨441311, by rfl⟩ : syracuseStep 2353661 = 882623) (by norm_num)
theorem B3926549 : Blo 964590 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B1632845 : Blo 964590 1632845 := bbase (se 3 (by rfl) ⟨306158, by rfl⟩ : syracuseStep 1632845 = 612317) (by norm_num)
theorem B1632973 : Blo 964590 1632973 := bbase (se 3 (by rfl) ⟨306182, by rfl⟩ : syracuseStep 1632973 = 612365) (by norm_num)
theorem B1633061 : Blo 964590 1633061 := bbase (se 4 (by rfl) ⟨153099, by rfl⟩ : syracuseStep 1633061 = 306199) (by norm_num)
theorem B1633189 : Blo 964590 1633189 := bbase (se 4 (by rfl) ⟨153111, by rfl⟩ : syracuseStep 1633189 = 306223) (by norm_num)
theorem B2747317 : Blo 964590 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B1633277 : Blo 964590 1633277 := bbase (se 3 (by rfl) ⟨306239, by rfl⟩ : syracuseStep 1633277 = 612479) (by norm_num)
theorem B1469477 : Blo 964590 1469477 := bbase (se 4 (by rfl) ⟨137763, by rfl⟩ : syracuseStep 1469477 = 275527) (by norm_num)
theorem B978025 : Blo 964590 978025 := bbase (se 2 (by rfl) ⟨366759, by rfl⟩ : syracuseStep 978025 = 733519) (by norm_num)
theorem B1633405 : Blo 964590 1633405 := bbase (se 3 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 1633405 = 612527) (by norm_num)
theorem B1633493 : Blo 964590 1633493 := bbase (se 7 (by rfl) ⟨19142, by rfl⟩ : syracuseStep 1633493 = 38285) (by norm_num)
theorem B1633621 : Blo 964590 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B2616725 : Blo 964590 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B1633709 : Blo 964590 1633709 := bbase (se 3 (by rfl) ⟨306320, by rfl⟩ : syracuseStep 1633709 = 612641) (by norm_num)
theorem B2321941 : Blo 964590 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B1633837 : Blo 964590 1633837 := bbase (se 3 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 1633837 = 612689) (by norm_num)
theorem B1633925 : Blo 964590 1633925 := bbase (se 4 (by rfl) ⟨153180, by rfl⟩ : syracuseStep 1633925 = 306361) (by norm_num)
theorem B1175233 : Blo 964590 1175233 := bbase (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) (by norm_num)
theorem B978653 : Blo 964590 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B1306373 : Blo 964590 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B1634053 : Blo 964590 1634053 := bbase (se 4 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 1634053 = 306385) (by norm_num)
theorem B5959477 : Blo 964590 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B1634141 : Blo 964590 1634141 := bbase (se 3 (by rfl) ⟨306401, by rfl⟩ : syracuseStep 1634141 = 612803) (by norm_num)
theorem B1306525 : Blo 964590 1306525 := bbase (se 3 (by rfl) ⟨244973, by rfl⟩ : syracuseStep 1306525 = 489947) (by norm_num)
theorem B1634269 : Blo 964590 1634269 := bbase (se 3 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 1634269 = 612851) (by norm_num)
theorem B2748421 : Blo 964590 2748421 := bbase (se 4 (by rfl) ⟨257664, by rfl⟩ : syracuseStep 2748421 = 515329) (by norm_num)
theorem B2060309 : Blo 964590 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1634357 : Blo 964590 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B3666005 : Blo 964590 3666005 := bbase (se 8 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 3666005 = 42961) (by norm_num)
theorem B2650229 : Blo 964590 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B2322557 : Blo 964590 2322557 := bbase (se 3 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 2322557 = 870959) (by norm_num)
theorem B1634485 : Blo 964590 1634485 := bbase (se 5 (by rfl) ⟨76616, by rfl⟩ : syracuseStep 1634485 = 153233) (by norm_num)
theorem B1863869 : Blo 964590 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B2322749 : Blo 964590 2322749 := bbase (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) (by norm_num)
theorem B1765709 : Blo 964590 1765709 := bbase (se 3 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 1765709 = 662141) (by norm_num)
theorem B3666293 : Blo 964590 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B4125077 : Blo 964590 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B2322845 : Blo 964590 2322845 := bbase (se 3 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 2322845 = 871067) (by norm_num)
theorem B2388557 : Blo 964590 2388557 := bbase (se 3 (by rfl) ⟨447854, by rfl⟩ : syracuseStep 2388557 = 895709) (by norm_num)
theorem B979537 : Blo 964590 979537 := bbase (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) (by norm_num)
theorem B1471301 : Blo 964590 1471301 := bbase (se 4 (by rfl) ⟨137934, by rfl⟩ : syracuseStep 1471301 = 275869) (by norm_num)
theorem B2061197 : Blo 964590 2061197 := bbase (se 3 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 2061197 = 772949) (by norm_num)
theorem B1962901 : Blo 964590 1962901 := bbase (se 6 (by rfl) ⟨46005, by rfl⟩ : syracuseStep 1962901 = 92011) (by norm_num)
theorem B1831909 : Blo 964590 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B4649957 : Blo 964590 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B1832053 : Blo 964590 1832053 := bbase (se 5 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 1832053 = 171755) (by norm_num)
theorem B2061445 : Blo 964590 2061445 := bbase (se 4 (by rfl) ⟨193260, by rfl⟩ : syracuseStep 2061445 = 386521) (by norm_num)
theorem B980101 : Blo 964590 980101 := bbase (se 4 (by rfl) ⟨91884, by rfl⟩ : syracuseStep 980101 = 183769) (by norm_num)
theorem B1045657 : Blo 964590 1045657 := bbase (se 2 (by rfl) ⟨392121, by rfl⟩ : syracuseStep 1045657 = 784243) (by norm_num)
theorem B7337141 : Blo 964590 7337141 := bbase (se 5 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 7337141 = 687857) (by norm_num)
theorem B1471709 : Blo 964590 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1832213 : Blo 964590 1832213 := bbase (se 6 (by rfl) ⟨42942, by rfl⟩ : syracuseStep 1832213 = 85885) (by norm_num)
theorem B4126085 : Blo 964590 4126085 := bbase (se 4 (by rfl) ⟨386820, by rfl⟩ : syracuseStep 4126085 = 773641) (by norm_num)
theorem B1832357 : Blo 964590 1832357 := bbase (se 4 (by rfl) ⟨171783, by rfl⟩ : syracuseStep 1832357 = 343567) (by norm_num)
theorem B2749925 : Blo 964590 2749925 := bbase (se 4 (by rfl) ⟨257805, by rfl⟩ : syracuseStep 2749925 = 515611) (by norm_num)
theorem B1472005 : Blo 964590 1472005 := bbase (se 4 (by rfl) ⟨138000, by rfl⟩ : syracuseStep 1472005 = 276001) (by norm_num)
theorem B3667477 : Blo 964590 3667477 := bbase (se 6 (by rfl) ⟨85956, by rfl⟩ : syracuseStep 3667477 = 171913) (by norm_num)
theorem B6190613 : Blo 964590 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B2061949 : Blo 964590 2061949 := bbase (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) (by norm_num)
theorem B1373869 : Blo 964590 1373869 := bbase (se 3 (by rfl) ⟨257600, by rfl⟩ : syracuseStep 1373869 = 515201) (by norm_num)
theorem B2291381 : Blo 964590 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B1832645 : Blo 964590 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B1472261 : Blo 964590 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B980753 : Blo 964590 980753 := bbase (se 2 (by rfl) ⟨367782, by rfl⟩ : syracuseStep 980753 = 735565) (by norm_num)
theorem B3667781 : Blo 964590 3667781 := bbase (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) (by norm_num)
theorem B1832797 : Blo 964590 1832797 := bbase (se 3 (by rfl) ⟨343649, by rfl⟩ : syracuseStep 1832797 = 687299) (by norm_num)
theorem B980957 : Blo 964590 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B2095141 : Blo 964590 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B1833101 : Blo 964590 1833101 := bbase (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) (by norm_num)
theorem B1177825 : Blo 964590 1177825 := bbase (se 2 (by rfl) ⟨441684, by rfl⟩ : syracuseStep 1177825 = 883369) (by norm_num)
theorem B1046885 : Blo 964590 1046885 := bbase (se 4 (by rfl) ⟨98145, by rfl⟩ : syracuseStep 1046885 = 196291) (by norm_num)
theorem B1374661 : Blo 964590 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B2062837 : Blo 964590 2062837 := bbase (se 5 (by rfl) ⟨96695, by rfl⟩ : syracuseStep 2062837 = 193391) (by norm_num)
theorem B981613 : Blo 964590 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B1374997 : Blo 964590 1374997 := bbase (se 6 (by rfl) ⟨32226, by rfl⟩ : syracuseStep 1374997 = 64453) (by norm_num)
theorem B1178389 : Blo 964590 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B2325277 : Blo 964590 2325277 := bbase (se 3 (by rfl) ⟨435989, by rfl⟩ : syracuseStep 2325277 = 871979) (by norm_num)
theorem B1833853 : Blo 964590 1833853 := bbase (se 3 (by rfl) ⟨343847, by rfl⟩ : syracuseStep 1833853 = 687695) (by norm_num)
theorem B2063333 : Blo 964590 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B1375213 : Blo 964590 1375213 := bbase (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) (by norm_num)
theorem B1833997 : Blo 964590 1833997 := bbase (se 3 (by rfl) ⟨343874, by rfl⟩ : syracuseStep 1833997 = 687749) (by norm_num)
theorem B2751509 : Blo 964590 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B2325613 : Blo 964590 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B4127861 : Blo 964590 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B1834157 : Blo 964590 1834157 := bbase (se 3 (by rfl) ⟨343904, by rfl⟩ : syracuseStep 1834157 = 687809) (by norm_num)
theorem B1834301 : Blo 964590 1834301 := bbase (se 3 (by rfl) ⟨343931, by rfl⟩ : syracuseStep 1834301 = 687863) (by norm_num)
theorem B1375589 : Blo 964590 1375589 := bbase (se 4 (by rfl) ⟨128961, by rfl⟩ : syracuseStep 1375589 = 257923) (by norm_num)
theorem B1834589 : Blo 964590 1834589 := bbase (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) (by norm_num)
theorem B2358877 : Blo 964590 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B2752181 : Blo 964590 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B2326229 : Blo 964590 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B1834741 : Blo 964590 1834741 := bbase (se 5 (by rfl) ⟨86003, by rfl⟩ : syracuseStep 1834741 = 172007) (by norm_num)
theorem B2064221 : Blo 964590 2064221 := bbase (se 3 (by rfl) ⟨387041, by rfl⟩ : syracuseStep 2064221 = 774083) (by norm_num)
theorem B3669893 : Blo 964590 3669893 := bbase (se 4 (by rfl) ⟨344052, by rfl⟩ : syracuseStep 3669893 = 688105) (by norm_num)
theorem B2064341 : Blo 964590 2064341 := bbase (se 7 (by rfl) ⟨24191, by rfl⟩ : syracuseStep 2064341 = 48383) (by norm_num)
theorem B1835075 : Blo 964590 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B3309923 : Blo 964590 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B9929101 : Blo 964590 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1376785 : Blo 964590 1376785 := bstep (se 2 (by rfl) ⟨516294, by rfl⟩ : syracuseStep 1376785 = 1032589) B1032589
theorem B2327075 : Blo 964590 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B13075085 : Blo 964590 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B2753297 : Blo 964590 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B1836017 : Blo 964590 1836017 := bstep (se 2 (by rfl) ⟨688506, by rfl⟩ : syracuseStep 1836017 = 1377013) B1377013
theorem B3310577 : Blo 964590 3310577 := bstep (se 2 (by rfl) ⟨1241466, by rfl⟩ : syracuseStep 3310577 = 2482933) B2482933
theorem B3671153 : Blo 964590 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B2065571 : Blo 964590 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B1377491 : Blo 964590 1377491 := bstep (se 1 (by rfl) ⟨1033118, by rfl⟩ : syracuseStep 1377491 = 2066237) B2066237
theorem B5506501 : Blo 964590 5506501 := bstep (se 4 (by rfl) ⟨516234, by rfl⟩ : syracuseStep 5506501 = 1032469) B1032469
theorem B1738307 : Blo 964590 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B2754253 : Blo 964590 2754253 := bstep (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) B1032845
theorem B2066161 : Blo 964590 2066161 := bstep (se 2 (by rfl) ⟨774810, by rfl⟩ : syracuseStep 2066161 = 1549621) B1549621
theorem B1378129 : Blo 964590 1378129 := bstep (se 2 (by rfl) ⟨516798, by rfl⟩ : syracuseStep 1378129 = 1033597) B1033597
theorem B1836913 : Blo 964590 1836913 := bstep (se 2 (by rfl) ⟨688842, by rfl⟩ : syracuseStep 1836913 = 1377685) B1377685
theorem B2754481 : Blo 964590 2754481 := bstep (se 2 (by rfl) ⟨1032930, by rfl⟩ : syracuseStep 2754481 = 2065861) B2065861
theorem B1378243 : Blo 964590 1378243 := bstep (se 1 (by rfl) ⟨1033682, by rfl⟩ : syracuseStep 1378243 = 2067365) B2067365
theorem B2721809 : Blo 964590 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B1837073 : Blo 964590 1837073 := bstep (se 2 (by rfl) ⟨688902, by rfl⟩ : syracuseStep 1837073 = 1377805) B1377805
theorem B2754641 : Blo 964590 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B2754755 : Blo 964590 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B7833827 : Blo 964590 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B4131107 : Blo 964590 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B4884785 : Blo 964590 4884785 := bstep (se 2 (by rfl) ⟨1831794, by rfl⟩ : syracuseStep 4884785 = 3663589) B3663589
theorem B1837475 : Blo 964590 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B3672611 : Blo 964590 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B12389219 : Blo 964590 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B7048133 : Blo 964590 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B2755757 : Blo 964590 2755757 := bstep (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) B1033409
theorem B5573873 : Blo 964590 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B1838371 : Blo 964590 1838371 := bstep (se 1 (by rfl) ⟨1378778, by rfl⟩ : syracuseStep 1838371 = 2757557) B2757557
theorem B7343459 : Blo 964590 7343459 := bstep (se 1 (by rfl) ⟨5507594, by rfl⟩ : syracuseStep 7343459 = 11015189) B11015189
theorem B2755939 : Blo 964590 2755939 := bstep (se 1 (by rfl) ⟨2066954, by rfl⟩ : syracuseStep 2755939 = 4133909) B4133909
theorem B7048561 : Blo 964590 7048561 := bstep (se 2 (by rfl) ⟨2643210, by rfl⟩ : syracuseStep 7048561 = 5286421) B5286421
theorem B5508485 : Blo 964590 5508485 := bstep (se 4 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 5508485 = 1032841) B1032841
theorem B1838531 : Blo 964590 1838531 := bstep (se 1 (by rfl) ⟨1378898, by rfl⟩ : syracuseStep 1838531 = 2757797) B2757797
theorem B2756099 : Blo 964590 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B3673613 : Blo 964590 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B8261189 : Blo 964590 8261189 := bstep (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) B1548973
theorem B11013731 : Blo 964590 11013731 := bstep (se 1 (by rfl) ⟨8260298, by rfl⟩ : syracuseStep 11013731 = 16520597) B16520597
theorem B4886243 : Blo 964590 4886243 := bstep (se 1 (by rfl) ⟨3664682, by rfl⟩ : syracuseStep 4886243 = 7329365) B7329365
theorem B1085251 : Blo 964590 1085251 := bstep (se 1 (by rfl) ⟨813938, by rfl⟩ : syracuseStep 1085251 = 1627877) B1627877
theorem B1085395 : Blo 964590 1085395 := bstep (se 1 (by rfl) ⟨814046, by rfl⟩ : syracuseStep 1085395 = 1628093) B1628093
theorem B1085539 : Blo 964590 1085539 := bstep (se 1 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 1085539 = 1628309) B1628309
theorem B1740995 : Blo 964590 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B1085683 : Blo 964590 1085683 := bstep (se 1 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 1085683 = 1628525) B1628525
theorem B3477809 : Blo 964590 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B2068849 : Blo 964590 2068849 := bstep (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) B1551637
theorem B1085827 : Blo 964590 1085827 := bstep (se 1 (by rfl) ⟨814370, by rfl⟩ : syracuseStep 1085827 = 1628741) B1628741
theorem B7442885 : Blo 964590 7442885 := bstep (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) B1395541
theorem B4887053 : Blo 964590 4887053 := bstep (se 3 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 4887053 = 1832645) B1832645
theorem B1085971 : Blo 964590 1085971 := bstep (se 1 (by rfl) ⟨814478, by rfl⟩ : syracuseStep 1085971 = 1628957) B1628957
theorem B2757169 : Blo 964590 2757169 := bstep (se 2 (by rfl) ⟨1033938, by rfl⟩ : syracuseStep 2757169 = 2067877) B2067877
theorem B1086115 : Blo 964590 1086115 := bstep (se 1 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 1086115 = 1629173) B1629173
theorem B11899619 : Blo 964590 11899619 := bstep (se 1 (by rfl) ⟨8924714, by rfl⟩ : syracuseStep 11899619 = 17849429) B17849429
theorem B1086259 : Blo 964590 1086259 := bstep (se 1 (by rfl) ⟨814694, by rfl⟩ : syracuseStep 1086259 = 1629389) B1629389
theorem B18617201 : Blo 964590 18617201 := bstep (se 2 (by rfl) ⟨6981450, by rfl⟩ : syracuseStep 18617201 = 13962901) B13962901
theorem B1086403 : Blo 964590 1086403 := bstep (se 1 (by rfl) ⟨814802, by rfl⟩ : syracuseStep 1086403 = 1629605) B1629605
theorem B1446899 : Blo 964590 1446899 := bstep (se 1 (by rfl) ⟨1085174, by rfl⟩ : syracuseStep 1446899 = 2170349) B2170349
theorem B1446929 : Blo 964590 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B1446947 : Blo 964590 1446947 := bstep (se 1 (by rfl) ⟨1085210, by rfl⟩ : syracuseStep 1446947 = 2170421) B2170421
theorem B1446977 : Blo 964590 1446977 := bstep (se 2 (by rfl) ⟨542616, by rfl⟩ : syracuseStep 1446977 = 1085233) B1085233
theorem B1446995 : Blo 964590 1446995 := bstep (se 1 (by rfl) ⟨1085246, by rfl⟩ : syracuseStep 1446995 = 2170493) B2170493
theorem B1086547 : Blo 964590 1086547 := bstep (se 1 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 1086547 = 1629821) B1629821
theorem B6624355 : Blo 964590 6624355 := bstep (se 1 (by rfl) ⟨4968266, by rfl⟩ : syracuseStep 6624355 = 9936533) B9936533
theorem B1447025 : Blo 964590 1447025 := bstep (se 2 (by rfl) ⟨542634, by rfl⟩ : syracuseStep 1447025 = 1085269) B1085269
theorem B1447043 : Blo 964590 1447043 := bstep (se 1 (by rfl) ⟨1085282, by rfl⟩ : syracuseStep 1447043 = 2170565) B2170565
theorem B5215373 : Blo 964590 5215373 := bstep (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) B1955765
theorem B1447073 : Blo 964590 1447073 := bstep (se 2 (by rfl) ⟨542652, by rfl⟩ : syracuseStep 1447073 = 1085305) B1085305
theorem B1447091 : Blo 964590 1447091 := bstep (se 1 (by rfl) ⟨1085318, by rfl⟩ : syracuseStep 1447091 = 2170637) B2170637
theorem B3478733 : Blo 964590 3478733 := bstep (se 3 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 3478733 = 1304525) B1304525
theorem B1447121 : Blo 964590 1447121 := bstep (se 2 (by rfl) ⟨542670, by rfl⟩ : syracuseStep 1447121 = 1085341) B1085341
theorem B1742033 : Blo 964590 1742033 := bstep (se 2 (by rfl) ⟨653262, by rfl⟩ : syracuseStep 1742033 = 1306525) B1306525
theorem B1447139 : Blo 964590 1447139 := bstep (se 1 (by rfl) ⟨1085354, by rfl⟩ : syracuseStep 1447139 = 2170709) B2170709
theorem B1086691 : Blo 964590 1086691 := bstep (se 1 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 1086691 = 1630037) B1630037
theorem B1447169 : Blo 964590 1447169 := bstep (se 2 (by rfl) ⟨542688, by rfl⟩ : syracuseStep 1447169 = 1085377) B1085377
theorem B1545475 : Blo 964590 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1447187 : Blo 964590 1447187 := bstep (se 1 (by rfl) ⟨1085390, by rfl⟩ : syracuseStep 1447187 = 2170781) B2170781
theorem B1447217 : Blo 964590 1447217 := bstep (se 2 (by rfl) ⟨542706, by rfl⟩ : syracuseStep 1447217 = 1085413) B1085413
theorem B1447235 : Blo 964590 1447235 := bstep (se 1 (by rfl) ⟨1085426, by rfl⟩ : syracuseStep 1447235 = 2170853) B2170853
theorem B1447265 : Blo 964590 1447265 := bstep (se 2 (by rfl) ⟨542724, by rfl⟩ : syracuseStep 1447265 = 1085449) B1085449
theorem B1545571 : Blo 964590 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1447283 : Blo 964590 1447283 := bstep (se 1 (by rfl) ⟨1085462, by rfl⟩ : syracuseStep 1447283 = 2170925) B2170925
theorem B1086835 : Blo 964590 1086835 := bstep (se 1 (by rfl) ⟨815126, by rfl⟩ : syracuseStep 1086835 = 1630253) B1630253
theorem B1447313 : Blo 964590 1447313 := bstep (se 2 (by rfl) ⟨542742, by rfl⟩ : syracuseStep 1447313 = 1085485) B1085485
theorem B1447331 : Blo 964590 1447331 := bstep (se 1 (by rfl) ⟨1085498, by rfl⟩ : syracuseStep 1447331 = 2170997) B2170997
theorem B1447361 : Blo 964590 1447361 := bstep (se 2 (by rfl) ⟨542760, by rfl⟩ : syracuseStep 1447361 = 1085521) B1085521
theorem B1447379 : Blo 964590 1447379 := bstep (se 1 (by rfl) ⟨1085534, by rfl⟩ : syracuseStep 1447379 = 2171069) B2171069
theorem B1447409 : Blo 964590 1447409 := bstep (se 2 (by rfl) ⟨542778, by rfl⟩ : syracuseStep 1447409 = 1085557) B1085557
theorem B1447427 : Blo 964590 1447427 := bstep (se 1 (by rfl) ⟨1085570, by rfl⟩ : syracuseStep 1447427 = 2171141) B2171141
theorem B1545731 : Blo 964590 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B1086979 : Blo 964590 1086979 := bstep (se 1 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 1086979 = 1630469) B1630469
theorem B1447457 : Blo 964590 1447457 := bstep (se 2 (by rfl) ⟨542796, by rfl⟩ : syracuseStep 1447457 = 1085593) B1085593
theorem B1447475 : Blo 964590 1447475 := bstep (se 1 (by rfl) ⟨1085606, by rfl⟩ : syracuseStep 1447475 = 2171213) B2171213
theorem B3675725 : Blo 964590 3675725 := bstep (se 3 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 3675725 = 1378397) B1378397
theorem B1447505 : Blo 964590 1447505 := bstep (se 2 (by rfl) ⟨542814, by rfl⟩ : syracuseStep 1447505 = 1085629) B1085629
theorem B1447523 : Blo 964590 1447523 := bstep (se 1 (by rfl) ⟨1085642, by rfl⟩ : syracuseStep 1447523 = 2171285) B2171285
theorem B1447553 : Blo 964590 1447553 := bstep (se 2 (by rfl) ⟨542832, by rfl⟩ : syracuseStep 1447553 = 1085665) B1085665
theorem B1447571 : Blo 964590 1447571 := bstep (se 1 (by rfl) ⟨1085678, by rfl⟩ : syracuseStep 1447571 = 2171357) B2171357
theorem B1087123 : Blo 964590 1087123 := bstep (se 1 (by rfl) ⟨815342, by rfl⟩ : syracuseStep 1087123 = 1630685) B1630685
theorem B1447601 : Blo 964590 1447601 := bstep (se 2 (by rfl) ⟨542850, by rfl⟩ : syracuseStep 1447601 = 1085701) B1085701
theorem B1447619 : Blo 964590 1447619 := bstep (se 1 (by rfl) ⟨1085714, by rfl⟩ : syracuseStep 1447619 = 2171429) B2171429
theorem B1447649 : Blo 964590 1447649 := bstep (se 2 (by rfl) ⟨542868, by rfl⟩ : syracuseStep 1447649 = 1085737) B1085737
theorem B3479267 : Blo 964590 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B1447667 : Blo 964590 1447667 := bstep (se 1 (by rfl) ⟨1085750, by rfl⟩ : syracuseStep 1447667 = 2171501) B2171501
theorem B1447697 : Blo 964590 1447697 := bstep (se 2 (by rfl) ⟨542886, by rfl⟩ : syracuseStep 1447697 = 1085773) B1085773
theorem B1447715 : Blo 964590 1447715 := bstep (se 1 (by rfl) ⟨1085786, by rfl⟩ : syracuseStep 1447715 = 2171573) B2171573
theorem B1087267 : Blo 964590 1087267 := bstep (se 1 (by rfl) ⟨815450, by rfl⟩ : syracuseStep 1087267 = 1630901) B1630901
theorem B1447745 : Blo 964590 1447745 := bstep (se 2 (by rfl) ⟨542904, by rfl⟩ : syracuseStep 1447745 = 1085809) B1085809
theorem B1447763 : Blo 964590 1447763 := bstep (se 1 (by rfl) ⟨1085822, by rfl⟩ : syracuseStep 1447763 = 2171645) B2171645
theorem B3479395 : Blo 964590 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B1447793 : Blo 964590 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B10590065 : Blo 964590 10590065 := bstep (se 2 (by rfl) ⟨3971274, by rfl⟩ : syracuseStep 10590065 = 7942549) B7942549
theorem B1447811 : Blo 964590 1447811 := bstep (se 1 (by rfl) ⟨1085858, by rfl⟩ : syracuseStep 1447811 = 2171717) B2171717
theorem B4134797 : Blo 964590 4134797 := bstep (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) B1550549
theorem B1447841 : Blo 964590 1447841 := bstep (se 2 (by rfl) ⟨542940, by rfl⟩ : syracuseStep 1447841 = 1085881) B1085881
theorem B4134833 : Blo 964590 4134833 := bstep (se 2 (by rfl) ⟨1550562, by rfl⟩ : syracuseStep 4134833 = 3101125) B3101125
theorem B1447859 : Blo 964590 1447859 := bstep (se 1 (by rfl) ⟨1085894, by rfl⟩ : syracuseStep 1447859 = 2171789) B2171789
theorem B1087411 : Blo 964590 1087411 := bstep (se 1 (by rfl) ⟨815558, by rfl⟩ : syracuseStep 1087411 = 1631117) B1631117
theorem B1447889 : Blo 964590 1447889 := bstep (se 2 (by rfl) ⟨542958, by rfl⟩ : syracuseStep 1447889 = 1085917) B1085917
theorem B1447907 : Blo 964590 1447907 := bstep (se 1 (by rfl) ⟨1085930, by rfl⟩ : syracuseStep 1447907 = 2171861) B2171861
theorem B1447937 : Blo 964590 1447937 := bstep (se 2 (by rfl) ⟨542976, by rfl⟩ : syracuseStep 1447937 = 1085953) B1085953
theorem B1447955 : Blo 964590 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B1447985 : Blo 964590 1447985 := bstep (se 2 (by rfl) ⟨542994, by rfl⟩ : syracuseStep 1447985 = 1085989) B1085989
theorem B1448003 : Blo 964590 1448003 := bstep (se 1 (by rfl) ⟨1086002, by rfl⟩ : syracuseStep 1448003 = 2172005) B2172005
theorem B1087555 : Blo 964590 1087555 := bstep (se 1 (by rfl) ⟨815666, by rfl⟩ : syracuseStep 1087555 = 1631333) B1631333
theorem B1448033 : Blo 964590 1448033 := bstep (se 2 (by rfl) ⟨543012, by rfl⟩ : syracuseStep 1448033 = 1086025) B1086025
theorem B1448051 : Blo 964590 1448051 := bstep (se 1 (by rfl) ⟨1086038, by rfl⟩ : syracuseStep 1448051 = 2172077) B2172077
theorem B1448081 : Blo 964590 1448081 := bstep (se 2 (by rfl) ⟨543030, by rfl⟩ : syracuseStep 1448081 = 1086061) B1086061
theorem B1448099 : Blo 964590 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1448129 : Blo 964590 1448129 := bstep (se 2 (by rfl) ⟨543048, by rfl⟩ : syracuseStep 1448129 = 1086097) B1086097
theorem B1448147 : Blo 964590 1448147 := bstep (se 1 (by rfl) ⟨1086110, by rfl⟩ : syracuseStep 1448147 = 2172221) B2172221
theorem B1087699 : Blo 964590 1087699 := bstep (se 1 (by rfl) ⟨815774, by rfl⟩ : syracuseStep 1087699 = 1631549) B1631549
theorem B1448177 : Blo 964590 1448177 := bstep (se 2 (by rfl) ⟨543066, by rfl⟩ : syracuseStep 1448177 = 1086133) B1086133
theorem B1448195 : Blo 964590 1448195 := bstep (se 1 (by rfl) ⟨1086146, by rfl⟩ : syracuseStep 1448195 = 2172293) B2172293
theorem B2791693 : Blo 964590 2791693 := bstep (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) B1046885
theorem B1448225 : Blo 964590 1448225 := bstep (se 2 (by rfl) ⟨543084, by rfl⟩ : syracuseStep 1448225 = 1086169) B1086169
theorem B1448243 : Blo 964590 1448243 := bstep (se 1 (by rfl) ⟨1086182, by rfl⟩ : syracuseStep 1448243 = 2172365) B2172365
theorem B1448273 : Blo 964590 1448273 := bstep (se 2 (by rfl) ⟨543102, by rfl⟩ : syracuseStep 1448273 = 1086205) B1086205
theorem B1448291 : Blo 964590 1448291 := bstep (se 1 (by rfl) ⟨1086218, by rfl⟩ : syracuseStep 1448291 = 2172437) B2172437
theorem B1087843 : Blo 964590 1087843 := bstep (se 1 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 1087843 = 1631765) B1631765
theorem B3676529 : Blo 964590 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B1448321 : Blo 964590 1448321 := bstep (se 2 (by rfl) ⟨543120, by rfl⟩ : syracuseStep 1448321 = 1086241) B1086241
theorem B1448339 : Blo 964590 1448339 := bstep (se 1 (by rfl) ⟨1086254, by rfl⟩ : syracuseStep 1448339 = 2172509) B2172509
theorem B1448369 : Blo 964590 1448369 := bstep (se 2 (by rfl) ⟨543138, by rfl⟩ : syracuseStep 1448369 = 1086277) B1086277
theorem B1448387 : Blo 964590 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B1546705 : Blo 964590 1546705 := bstep (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) B1160029
theorem B1448417 : Blo 964590 1448417 := bstep (se 2 (by rfl) ⟨543156, by rfl⟩ : syracuseStep 1448417 = 1086313) B1086313
theorem B1448435 : Blo 964590 1448435 := bstep (se 1 (by rfl) ⟨1086326, by rfl⟩ : syracuseStep 1448435 = 2172653) B2172653
theorem B1087987 : Blo 964590 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B1448465 : Blo 964590 1448465 := bstep (se 2 (by rfl) ⟨543174, by rfl⟩ : syracuseStep 1448465 = 1086349) B1086349
theorem B1448483 : Blo 964590 1448483 := bstep (se 1 (by rfl) ⟨1086362, by rfl⟩ : syracuseStep 1448483 = 2172725) B2172725
theorem B1448513 : Blo 964590 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B1448531 : Blo 964590 1448531 := bstep (se 1 (by rfl) ⟨1086398, by rfl⟩ : syracuseStep 1448531 = 2172797) B2172797
theorem B1448561 : Blo 964590 1448561 := bstep (se 2 (by rfl) ⟨543210, by rfl⟩ : syracuseStep 1448561 = 1086421) B1086421
theorem B1448579 : Blo 964590 1448579 := bstep (se 1 (by rfl) ⟨1086434, by rfl⟩ : syracuseStep 1448579 = 2172869) B2172869
theorem B1088131 : Blo 964590 1088131 := bstep (se 1 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 1088131 = 1632197) B1632197
theorem B1448609 : Blo 964590 1448609 := bstep (se 2 (by rfl) ⟨543228, by rfl⟩ : syracuseStep 1448609 = 1086457) B1086457
theorem B1448627 : Blo 964590 1448627 := bstep (se 1 (by rfl) ⟨1086470, by rfl⟩ : syracuseStep 1448627 = 2172941) B2172941
theorem B1448657 : Blo 964590 1448657 := bstep (se 2 (by rfl) ⟨543246, by rfl⟩ : syracuseStep 1448657 = 1086493) B1086493
theorem B1448675 : Blo 964590 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B1448705 : Blo 964590 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B1743619 : Blo 964590 1743619 := bstep (se 1 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 1743619 = 2615429) B2615429
theorem B1448723 : Blo 964590 1448723 := bstep (se 1 (by rfl) ⟨1086542, by rfl⟩ : syracuseStep 1448723 = 2173085) B2173085
theorem B1088275 : Blo 964590 1088275 := bstep (se 1 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 1088275 = 1632413) B1632413
theorem B1448753 : Blo 964590 1448753 := bstep (se 2 (by rfl) ⟨543282, by rfl⟩ : syracuseStep 1448753 = 1086565) B1086565
theorem B1448771 : Blo 964590 1448771 := bstep (se 1 (by rfl) ⟨1086578, by rfl⟩ : syracuseStep 1448771 = 2173157) B2173157
theorem B3971917 : Blo 964590 3971917 := bstep (se 3 (by rfl) ⟨744734, by rfl⟩ : syracuseStep 3971917 = 1489469) B1489469
theorem B1448801 : Blo 964590 1448801 := bstep (se 2 (by rfl) ⟨543300, by rfl⟩ : syracuseStep 1448801 = 1086601) B1086601
theorem B1448819 : Blo 964590 1448819 := bstep (se 1 (by rfl) ⟨1086614, by rfl⟩ : syracuseStep 1448819 = 2173229) B2173229
theorem B1448849 : Blo 964590 1448849 := bstep (se 2 (by rfl) ⟨543318, by rfl⟩ : syracuseStep 1448849 = 1086637) B1086637
theorem B1448867 : Blo 964590 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B1088419 : Blo 964590 1088419 := bstep (se 1 (by rfl) ⟨816314, by rfl⟩ : syracuseStep 1088419 = 1632629) B1632629
theorem B1448897 : Blo 964590 1448897 := bstep (se 2 (by rfl) ⟨543336, by rfl⟩ : syracuseStep 1448897 = 1086673) B1086673
theorem B1448915 : Blo 964590 1448915 := bstep (se 1 (by rfl) ⟨1086686, by rfl⟩ : syracuseStep 1448915 = 2173373) B2173373
theorem B1448945 : Blo 964590 1448945 := bstep (se 2 (by rfl) ⟨543354, by rfl⟩ : syracuseStep 1448945 = 1086709) B1086709
theorem B1448963 : Blo 964590 1448963 := bstep (se 1 (by rfl) ⟨1086722, by rfl⟩ : syracuseStep 1448963 = 2173445) B2173445
theorem B3677197 : Blo 964590 3677197 := bstep (se 3 (by rfl) ⟨689474, by rfl⟩ : syracuseStep 3677197 = 1378949) B1378949
theorem B1448993 : Blo 964590 1448993 := bstep (se 2 (by rfl) ⟨543372, by rfl⟩ : syracuseStep 1448993 = 1086745) B1086745
theorem B1449011 : Blo 964590 1449011 := bstep (se 1 (by rfl) ⟨1086758, by rfl⟩ : syracuseStep 1449011 = 2173517) B2173517
theorem B1088563 : Blo 964590 1088563 := bstep (se 1 (by rfl) ⟨816422, by rfl⟩ : syracuseStep 1088563 = 1632845) B1632845
theorem B1449041 : Blo 964590 1449041 := bstep (se 2 (by rfl) ⟨543390, by rfl⟩ : syracuseStep 1449041 = 1086781) B1086781
theorem B1449059 : Blo 964590 1449059 := bstep (se 1 (by rfl) ⟨1086794, by rfl⟩ : syracuseStep 1449059 = 2173589) B2173589
theorem B2235491 : Blo 964590 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B1449089 : Blo 964590 1449089 := bstep (se 2 (by rfl) ⟨543408, by rfl⟩ : syracuseStep 1449089 = 1086817) B1086817
theorem B5512333 : Blo 964590 5512333 := bstep (se 3 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 5512333 = 2067125) B2067125
theorem B1449107 : Blo 964590 1449107 := bstep (se 1 (by rfl) ⟨1086830, by rfl⟩ : syracuseStep 1449107 = 2173661) B2173661
theorem B1449137 : Blo 964590 1449137 := bstep (se 2 (by rfl) ⟨543426, by rfl⟩ : syracuseStep 1449137 = 1086853) B1086853
theorem B1449155 : Blo 964590 1449155 := bstep (se 1 (by rfl) ⟨1086866, by rfl⟩ : syracuseStep 1449155 = 2173733) B2173733
theorem B1088707 : Blo 964590 1088707 := bstep (se 1 (by rfl) ⟨816530, by rfl⟩ : syracuseStep 1088707 = 1633061) B1633061
theorem B1449185 : Blo 964590 1449185 := bstep (se 2 (by rfl) ⟨543444, by rfl⟩ : syracuseStep 1449185 = 1086889) B1086889
theorem B4955377 : Blo 964590 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1449203 : Blo 964590 1449203 := bstep (se 1 (by rfl) ⟨1086902, by rfl⟩ : syracuseStep 1449203 = 2173805) B2173805
theorem B1449233 : Blo 964590 1449233 := bstep (se 2 (by rfl) ⟨543462, by rfl⟩ : syracuseStep 1449233 = 1086925) B1086925
theorem B1449251 : Blo 964590 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B1449281 : Blo 964590 1449281 := bstep (se 2 (by rfl) ⟨543480, by rfl⟩ : syracuseStep 1449281 = 1086961) B1086961
theorem B1449299 : Blo 964590 1449299 := bstep (se 1 (by rfl) ⟨1086974, by rfl⟩ : syracuseStep 1449299 = 2173949) B2173949
theorem B1088851 : Blo 964590 1088851 := bstep (se 1 (by rfl) ⟨816638, by rfl⟩ : syracuseStep 1088851 = 1633277) B1633277
theorem B4889969 : Blo 964590 4889969 := bstep (se 2 (by rfl) ⟨1833738, by rfl⟩ : syracuseStep 4889969 = 3667477) B3667477
theorem B1449329 : Blo 964590 1449329 := bstep (se 2 (by rfl) ⟨543498, by rfl⟩ : syracuseStep 1449329 = 1086997) B1086997
theorem B1449347 : Blo 964590 1449347 := bstep (se 1 (by rfl) ⟨1087010, by rfl⟩ : syracuseStep 1449347 = 2174021) B2174021
theorem B1449377 : Blo 964590 1449377 := bstep (se 2 (by rfl) ⟨543516, by rfl⟩ : syracuseStep 1449377 = 1087033) B1087033
theorem B1449395 : Blo 964590 1449395 := bstep (se 1 (by rfl) ⟨1087046, by rfl⟩ : syracuseStep 1449395 = 2174093) B2174093
theorem B1449425 : Blo 964590 1449425 := bstep (se 2 (by rfl) ⟨543534, by rfl⟩ : syracuseStep 1449425 = 1087069) B1087069
theorem B1449443 : Blo 964590 1449443 := bstep (se 1 (by rfl) ⟨1087082, by rfl⟩ : syracuseStep 1449443 = 2174165) B2174165
theorem B1088995 : Blo 964590 1088995 := bstep (se 1 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 1088995 = 1633493) B1633493
theorem B1449473 : Blo 964590 1449473 := bstep (se 2 (by rfl) ⟨543552, by rfl⟩ : syracuseStep 1449473 = 1087105) B1087105
theorem B2170385 : Blo 964590 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B1449491 : Blo 964590 1449491 := bstep (se 1 (by rfl) ⟨1087118, by rfl⟩ : syracuseStep 1449491 = 2174237) B2174237
theorem B2170403 : Blo 964590 2170403 := bstep (se 1 (by rfl) ⟨1627802, by rfl⟩ : syracuseStep 2170403 = 3255605) B3255605
theorem B1449521 : Blo 964590 1449521 := bstep (se 2 (by rfl) ⟨543570, by rfl⟩ : syracuseStep 1449521 = 1087141) B1087141
theorem B1449539 : Blo 964590 1449539 := bstep (se 1 (by rfl) ⟨1087154, by rfl⟩ : syracuseStep 1449539 = 2174309) B2174309
theorem B1449569 : Blo 964590 1449569 := bstep (se 2 (by rfl) ⟨543588, by rfl⟩ : syracuseStep 1449569 = 1087177) B1087177
theorem B1449587 : Blo 964590 1449587 := bstep (se 1 (by rfl) ⟨1087190, by rfl⟩ : syracuseStep 1449587 = 2174381) B2174381
theorem B1089139 : Blo 964590 1089139 := bstep (se 1 (by rfl) ⟨816854, by rfl⟩ : syracuseStep 1089139 = 1633709) B1633709
theorem B6200965 : Blo 964590 6200965 := bstep (se 4 (by rfl) ⟨581340, by rfl⟩ : syracuseStep 6200965 = 1162681) B1162681
theorem B1449617 : Blo 964590 1449617 := bstep (se 2 (by rfl) ⟨543606, by rfl⟩ : syracuseStep 1449617 = 1087213) B1087213
theorem B1449635 : Blo 964590 1449635 := bstep (se 1 (by rfl) ⟨1087226, by rfl⟩ : syracuseStep 1449635 = 2174453) B2174453
theorem B1449665 : Blo 964590 1449665 := bstep (se 2 (by rfl) ⟨543624, by rfl⟩ : syracuseStep 1449665 = 1087249) B1087249
theorem B1449683 : Blo 964590 1449683 := bstep (se 1 (by rfl) ⟨1087262, by rfl⟩ : syracuseStep 1449683 = 2174525) B2174525
theorem B1449713 : Blo 964590 1449713 := bstep (se 2 (by rfl) ⟨543642, by rfl⟩ : syracuseStep 1449713 = 1087285) B1087285
theorem B1449731 : Blo 964590 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B1089283 : Blo 964590 1089283 := bstep (se 1 (by rfl) ⟨816962, by rfl⟩ : syracuseStep 1089283 = 1633925) B1633925
theorem B1449761 : Blo 964590 1449761 := bstep (se 2 (by rfl) ⟨543660, by rfl⟩ : syracuseStep 1449761 = 1087321) B1087321
theorem B2170673 : Blo 964590 2170673 := bstep (se 2 (by rfl) ⟨814002, by rfl⟩ : syracuseStep 2170673 = 1628005) B1628005
theorem B1449779 : Blo 964590 1449779 := bstep (se 1 (by rfl) ⟨1087334, by rfl⟩ : syracuseStep 1449779 = 2174669) B2174669
theorem B2170691 : Blo 964590 2170691 := bstep (se 1 (by rfl) ⟨1628018, by rfl⟩ : syracuseStep 2170691 = 3256037) B3256037
theorem B1449809 : Blo 964590 1449809 := bstep (se 2 (by rfl) ⟨543678, by rfl⟩ : syracuseStep 1449809 = 1087357) B1087357
theorem B1449827 : Blo 964590 1449827 := bstep (se 1 (by rfl) ⟨1087370, by rfl⟩ : syracuseStep 1449827 = 2174741) B2174741
theorem B1449857 : Blo 964590 1449857 := bstep (se 2 (by rfl) ⟨543696, by rfl⟩ : syracuseStep 1449857 = 1087393) B1087393
theorem B1449875 : Blo 964590 1449875 := bstep (se 1 (by rfl) ⟨1087406, by rfl⟩ : syracuseStep 1449875 = 2174813) B2174813
theorem B1089427 : Blo 964590 1089427 := bstep (se 1 (by rfl) ⟨817070, by rfl⟩ : syracuseStep 1089427 = 1634141) B1634141
theorem B1449905 : Blo 964590 1449905 := bstep (se 2 (by rfl) ⟨543714, by rfl⟩ : syracuseStep 1449905 = 1087429) B1087429
theorem B1449923 : Blo 964590 1449923 := bstep (se 1 (by rfl) ⟨1087442, by rfl⟩ : syracuseStep 1449923 = 2174885) B2174885
theorem B1449953 : Blo 964590 1449953 := bstep (se 2 (by rfl) ⟨543732, by rfl⟩ : syracuseStep 1449953 = 1087465) B1087465
theorem B26484707 : Blo 964590 26484707 := bstep (se 1 (by rfl) ⟨19863530, by rfl⟩ : syracuseStep 26484707 = 39727061) B39727061
theorem B1449971 : Blo 964590 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B1450001 : Blo 964590 1450001 := bstep (se 2 (by rfl) ⟨543750, by rfl⟩ : syracuseStep 1450001 = 1087501) B1087501
theorem B1450019 : Blo 964590 1450019 := bstep (se 1 (by rfl) ⟨1087514, by rfl⟩ : syracuseStep 1450019 = 2175029) B2175029
theorem B1089571 : Blo 964590 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B2793521 : Blo 964590 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B15704117 : Blo 964590 15704117 := bstep (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) B1472261
theorem B1450049 : Blo 964590 1450049 := bstep (se 2 (by rfl) ⟨543768, by rfl⟩ : syracuseStep 1450049 = 1087537) B1087537
theorem B2170961 : Blo 964590 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B1548371 : Blo 964590 1548371 := bstep (se 1 (by rfl) ⟨1161278, by rfl⟩ : syracuseStep 1548371 = 2322557) B2322557
theorem B1450067 : Blo 964590 1450067 := bstep (se 1 (by rfl) ⟨1087550, by rfl⟩ : syracuseStep 1450067 = 2175101) B2175101
theorem B2170979 : Blo 964590 2170979 := bstep (se 1 (by rfl) ⟨1628234, by rfl⟩ : syracuseStep 2170979 = 3256469) B3256469
theorem B1450097 : Blo 964590 1450097 := bstep (se 2 (by rfl) ⟨543786, by rfl⟩ : syracuseStep 1450097 = 1087573) B1087573
theorem B1450115 : Blo 964590 1450115 := bstep (se 1 (by rfl) ⟨1087586, by rfl⟩ : syracuseStep 1450115 = 2175173) B2175173
theorem B5218445 : Blo 964590 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B1450145 : Blo 964590 1450145 := bstep (se 2 (by rfl) ⟨543804, by rfl⟩ : syracuseStep 1450145 = 1087609) B1087609
theorem B1450163 : Blo 964590 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B1450193 : Blo 964590 1450193 := bstep (se 2 (by rfl) ⟨543822, by rfl⟩ : syracuseStep 1450193 = 1087645) B1087645
theorem B1548499 : Blo 964590 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B1450211 : Blo 964590 1450211 := bstep (se 1 (by rfl) ⟨1087658, by rfl⟩ : syracuseStep 1450211 = 2175317) B2175317
theorem B1450241 : Blo 964590 1450241 := bstep (se 2 (by rfl) ⟨543840, by rfl⟩ : syracuseStep 1450241 = 1087681) B1087681
theorem B1548563 : Blo 964590 1548563 := bstep (se 1 (by rfl) ⟨1161422, by rfl⟩ : syracuseStep 1548563 = 2322845) B2322845
theorem B1450259 : Blo 964590 1450259 := bstep (se 1 (by rfl) ⟨1087694, by rfl⟩ : syracuseStep 1450259 = 2175389) B2175389
theorem B1450289 : Blo 964590 1450289 := bstep (se 2 (by rfl) ⟨543858, by rfl⟩ : syracuseStep 1450289 = 1087717) B1087717
theorem B1450307 : Blo 964590 1450307 := bstep (se 1 (by rfl) ⟨1087730, by rfl⟩ : syracuseStep 1450307 = 2175461) B2175461
theorem B1450337 : Blo 964590 1450337 := bstep (se 2 (by rfl) ⟨543876, by rfl⟩ : syracuseStep 1450337 = 1087753) B1087753
theorem B2171249 : Blo 964590 2171249 := bstep (se 2 (by rfl) ⟨814218, by rfl⟩ : syracuseStep 2171249 = 1628437) B1628437
theorem B1450355 : Blo 964590 1450355 := bstep (se 1 (by rfl) ⟨1087766, by rfl⟩ : syracuseStep 1450355 = 2175533) B2175533
theorem B2171267 : Blo 964590 2171267 := bstep (se 1 (by rfl) ⟨1628450, by rfl⟩ : syracuseStep 2171267 = 3256901) B3256901
theorem B1450385 : Blo 964590 1450385 := bstep (se 2 (by rfl) ⟨543894, by rfl⟩ : syracuseStep 1450385 = 1087789) B1087789
theorem B1450403 : Blo 964590 1450403 := bstep (se 1 (by rfl) ⟨1087802, by rfl⟩ : syracuseStep 1450403 = 2175605) B2175605
theorem B1450433 : Blo 964590 1450433 := bstep (se 2 (by rfl) ⟨543912, by rfl⟩ : syracuseStep 1450433 = 1087825) B1087825
theorem B1450451 : Blo 964590 1450451 := bstep (se 1 (by rfl) ⟨1087838, by rfl⟩ : syracuseStep 1450451 = 2175677) B2175677
theorem B1450481 : Blo 964590 1450481 := bstep (se 2 (by rfl) ⟨543930, by rfl⟩ : syracuseStep 1450481 = 1087861) B1087861
theorem B1450499 : Blo 964590 1450499 := bstep (se 1 (by rfl) ⟨1087874, by rfl⟩ : syracuseStep 1450499 = 2175749) B2175749
theorem B1450529 : Blo 964590 1450529 := bstep (se 2 (by rfl) ⟨543948, by rfl⟩ : syracuseStep 1450529 = 1087897) B1087897
theorem B1450547 : Blo 964590 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B7348805 : Blo 964590 7348805 := bstep (se 4 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 7348805 = 1377901) B1377901
theorem B1450577 : Blo 964590 1450577 := bstep (se 2 (by rfl) ⟨543966, by rfl⟩ : syracuseStep 1450577 = 1087933) B1087933
theorem B1450595 : Blo 964590 1450595 := bstep (se 1 (by rfl) ⟨1087946, by rfl⟩ : syracuseStep 1450595 = 2175893) B2175893
theorem B1450625 : Blo 964590 1450625 := bstep (se 2 (by rfl) ⟨543984, by rfl⟩ : syracuseStep 1450625 = 1087969) B1087969
theorem B2171537 : Blo 964590 2171537 := bstep (se 2 (by rfl) ⟨814326, by rfl⟩ : syracuseStep 2171537 = 1628653) B1628653
theorem B1450643 : Blo 964590 1450643 := bstep (se 1 (by rfl) ⟨1087982, by rfl⟩ : syracuseStep 1450643 = 2175965) B2175965
theorem B2171555 : Blo 964590 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B1450673 : Blo 964590 1450673 := bstep (se 2 (by rfl) ⟨544002, by rfl⟩ : syracuseStep 1450673 = 1088005) B1088005
theorem B1450691 : Blo 964590 1450691 := bstep (se 1 (by rfl) ⟨1088018, by rfl⟩ : syracuseStep 1450691 = 2176037) B2176037
theorem B1450721 : Blo 964590 1450721 := bstep (se 2 (by rfl) ⟨544020, by rfl⟩ : syracuseStep 1450721 = 1088041) B1088041
theorem B1450739 : Blo 964590 1450739 := bstep (se 1 (by rfl) ⟨1088054, by rfl⟩ : syracuseStep 1450739 = 2176109) B2176109
theorem B1549057 : Blo 964590 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B1450769 : Blo 964590 1450769 := bstep (se 2 (by rfl) ⟨544038, by rfl⟩ : syracuseStep 1450769 = 1088077) B1088077
theorem B4891427 : Blo 964590 4891427 := bstep (se 1 (by rfl) ⟨3668570, by rfl⟩ : syracuseStep 4891427 = 7337141) B7337141
theorem B1450787 : Blo 964590 1450787 := bstep (se 1 (by rfl) ⟨1088090, by rfl⟩ : syracuseStep 1450787 = 2176181) B2176181
theorem B1450817 : Blo 964590 1450817 := bstep (se 2 (by rfl) ⟨544056, by rfl⟩ : syracuseStep 1450817 = 1088113) B1088113
theorem B1450835 : Blo 964590 1450835 := bstep (se 1 (by rfl) ⟨1088126, by rfl⟩ : syracuseStep 1450835 = 2176253) B2176253
theorem B1221475 : Blo 964590 1221475 := bstep (se 1 (by rfl) ⟨916106, by rfl⟩ : syracuseStep 1221475 = 1832213) B1832213
theorem B1450865 : Blo 964590 1450865 := bstep (se 2 (by rfl) ⟨544074, by rfl⟩ : syracuseStep 1450865 = 1088149) B1088149
theorem B1450883 : Blo 964590 1450883 := bstep (se 1 (by rfl) ⟨1088162, by rfl⟩ : syracuseStep 1450883 = 2176325) B2176325
theorem B1450913 : Blo 964590 1450913 := bstep (se 2 (by rfl) ⟨544092, by rfl⟩ : syracuseStep 1450913 = 1088185) B1088185
theorem B2171825 : Blo 964590 2171825 := bstep (se 2 (by rfl) ⟨814434, by rfl⟩ : syracuseStep 2171825 = 1628869) B1628869
theorem B1450931 : Blo 964590 1450931 := bstep (se 1 (by rfl) ⟨1088198, by rfl⟩ : syracuseStep 1450931 = 2176397) B2176397
theorem B1221571 : Blo 964590 1221571 := bstep (se 1 (by rfl) ⟨916178, by rfl⟩ : syracuseStep 1221571 = 1832357) B1832357
theorem B2171843 : Blo 964590 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B1450961 : Blo 964590 1450961 := bstep (se 2 (by rfl) ⟨544110, by rfl⟩ : syracuseStep 1450961 = 1088221) B1088221
theorem B1450979 : Blo 964590 1450979 := bstep (se 1 (by rfl) ⟨1088234, by rfl⟩ : syracuseStep 1450979 = 2176469) B2176469
theorem B1451009 : Blo 964590 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B1451027 : Blo 964590 1451027 := bstep (se 1 (by rfl) ⟨1088270, by rfl⟩ : syracuseStep 1451027 = 2176541) B2176541
theorem B1451057 : Blo 964590 1451057 := bstep (se 2 (by rfl) ⟨544146, by rfl⟩ : syracuseStep 1451057 = 1088293) B1088293
theorem B1451075 : Blo 964590 1451075 := bstep (se 1 (by rfl) ⟨1088306, by rfl⟩ : syracuseStep 1451075 = 2176613) B2176613
theorem B5514317 : Blo 964590 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B1451105 : Blo 964590 1451105 := bstep (se 2 (by rfl) ⟨544164, by rfl⟩ : syracuseStep 1451105 = 1088329) B1088329
theorem B1451123 : Blo 964590 1451123 := bstep (se 1 (by rfl) ⟨1088342, by rfl⟩ : syracuseStep 1451123 = 2176685) B2176685
theorem B1451153 : Blo 964590 1451153 := bstep (se 2 (by rfl) ⟨544182, by rfl⟩ : syracuseStep 1451153 = 1088365) B1088365
theorem B1451171 : Blo 964590 1451171 := bstep (se 1 (by rfl) ⟨1088378, by rfl⟩ : syracuseStep 1451171 = 2176757) B2176757
theorem B1451201 : Blo 964590 1451201 := bstep (se 2 (by rfl) ⟨544200, by rfl⟩ : syracuseStep 1451201 = 1088401) B1088401
theorem B17605829 : Blo 964590 17605829 := bstep (se 4 (by rfl) ⟨1650546, by rfl⟩ : syracuseStep 17605829 = 3301093) B3301093
theorem B2172113 : Blo 964590 2172113 := bstep (se 2 (by rfl) ⟨814542, by rfl⟩ : syracuseStep 2172113 = 1629085) B1629085
theorem B1451219 : Blo 964590 1451219 := bstep (se 1 (by rfl) ⟨1088414, by rfl⟩ : syracuseStep 1451219 = 2176829) B2176829
theorem B2172131 : Blo 964590 2172131 := bstep (se 1 (by rfl) ⟨1629098, by rfl⟩ : syracuseStep 2172131 = 3258197) B3258197
theorem B1451249 : Blo 964590 1451249 := bstep (se 2 (by rfl) ⟨544218, by rfl⟩ : syracuseStep 1451249 = 1088437) B1088437
theorem B1451267 : Blo 964590 1451267 := bstep (se 1 (by rfl) ⟨1088450, by rfl⟩ : syracuseStep 1451267 = 2176901) B2176901
theorem B2204945 : Blo 964590 2204945 := bstep (se 2 (by rfl) ⟨826854, by rfl⟩ : syracuseStep 2204945 = 1653709) B1653709
theorem B1451297 : Blo 964590 1451297 := bstep (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) B1088473
theorem B1451315 : Blo 964590 1451315 := bstep (se 1 (by rfl) ⟨1088486, by rfl⟩ : syracuseStep 1451315 = 2176973) B2176973
theorem B1451345 : Blo 964590 1451345 := bstep (se 2 (by rfl) ⟨544254, by rfl⟩ : syracuseStep 1451345 = 1088509) B1088509
theorem B1451363 : Blo 964590 1451363 := bstep (se 1 (by rfl) ⟨1088522, by rfl⟩ : syracuseStep 1451363 = 2177045) B2177045
theorem B1451393 : Blo 964590 1451393 := bstep (se 2 (by rfl) ⟨544272, by rfl⟩ : syracuseStep 1451393 = 1088545) B1088545
theorem B1451411 : Blo 964590 1451411 := bstep (se 1 (by rfl) ⟨1088558, by rfl⟩ : syracuseStep 1451411 = 2177117) B2177117
theorem B1549729 : Blo 964590 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B1451441 : Blo 964590 1451441 := bstep (se 2 (by rfl) ⟨544290, by rfl⟩ : syracuseStep 1451441 = 1088581) B1088581
theorem B1222067 : Blo 964590 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B1451459 : Blo 964590 1451459 := bstep (se 1 (by rfl) ⟨1088594, by rfl⟩ : syracuseStep 1451459 = 2177189) B2177189
theorem B1451489 : Blo 964590 1451489 := bstep (se 2 (by rfl) ⟨544308, by rfl⟩ : syracuseStep 1451489 = 1088617) B1088617
theorem B2172401 : Blo 964590 2172401 := bstep (se 2 (by rfl) ⟨814650, by rfl⟩ : syracuseStep 2172401 = 1629301) B1629301
theorem B1451507 : Blo 964590 1451507 := bstep (se 1 (by rfl) ⟨1088630, by rfl⟩ : syracuseStep 1451507 = 2177261) B2177261
theorem B2172419 : Blo 964590 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B1451537 : Blo 964590 1451537 := bstep (se 2 (by rfl) ⟨544326, by rfl⟩ : syracuseStep 1451537 = 1088653) B1088653
theorem B1451555 : Blo 964590 1451555 := bstep (se 1 (by rfl) ⟨1088666, by rfl⟩ : syracuseStep 1451555 = 2177333) B2177333
theorem B1451585 : Blo 964590 1451585 := bstep (se 2 (by rfl) ⟨544344, by rfl⟩ : syracuseStep 1451585 = 1088689) B1088689
theorem B4892237 : Blo 964590 4892237 := bstep (se 3 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 4892237 = 1834589) B1834589
theorem B1451603 : Blo 964590 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B1451633 : Blo 964590 1451633 := bstep (se 2 (by rfl) ⟨544362, by rfl⟩ : syracuseStep 1451633 = 1088725) B1088725
theorem B1451651 : Blo 964590 1451651 := bstep (se 1 (by rfl) ⟨1088738, by rfl⟩ : syracuseStep 1451651 = 2177477) B2177477
theorem B1451681 : Blo 964590 1451681 := bstep (se 2 (by rfl) ⟨544380, by rfl⟩ : syracuseStep 1451681 = 1088761) B1088761
theorem B1451699 : Blo 964590 1451699 := bstep (se 1 (by rfl) ⟨1088774, by rfl⟩ : syracuseStep 1451699 = 2177549) B2177549
theorem B1451729 : Blo 964590 1451729 := bstep (se 2 (by rfl) ⟨544398, by rfl⟩ : syracuseStep 1451729 = 1088797) B1088797
theorem B1451747 : Blo 964590 1451747 := bstep (se 1 (by rfl) ⟨1088810, by rfl⟩ : syracuseStep 1451747 = 2177621) B2177621
theorem B1451777 : Blo 964590 1451777 := bstep (se 2 (by rfl) ⟨544416, by rfl⟩ : syracuseStep 1451777 = 1088833) B1088833
theorem B2172689 : Blo 964590 2172689 := bstep (se 2 (by rfl) ⟨814758, by rfl⟩ : syracuseStep 2172689 = 1629517) B1629517
theorem B1451795 : Blo 964590 1451795 := bstep (se 1 (by rfl) ⟨1088846, by rfl⟩ : syracuseStep 1451795 = 2177693) B2177693
theorem B2172707 : Blo 964590 2172707 := bstep (se 1 (by rfl) ⟨1629530, by rfl⟩ : syracuseStep 2172707 = 3259061) B3259061
theorem B3090221 : Blo 964590 3090221 := bstep (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) B1158833
theorem B1451825 : Blo 964590 1451825 := bstep (se 2 (by rfl) ⟨544434, by rfl⟩ : syracuseStep 1451825 = 1088869) B1088869
theorem B1451843 : Blo 964590 1451843 := bstep (se 1 (by rfl) ⟨1088882, by rfl⟩ : syracuseStep 1451843 = 2177765) B2177765
theorem B1451873 : Blo 964590 1451873 := bstep (se 2 (by rfl) ⟨544452, by rfl⟩ : syracuseStep 1451873 = 1088905) B1088905
theorem B1451891 : Blo 964590 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B1451921 : Blo 964590 1451921 := bstep (se 2 (by rfl) ⟨544470, by rfl⟩ : syracuseStep 1451921 = 1088941) B1088941
theorem B1451939 : Blo 964590 1451939 := bstep (se 1 (by rfl) ⟨1088954, by rfl⟩ : syracuseStep 1451939 = 2177909) B2177909
theorem B1451969 : Blo 964590 1451969 := bstep (se 2 (by rfl) ⟨544488, by rfl⟩ : syracuseStep 1451969 = 1088977) B1088977
theorem B1451987 : Blo 964590 1451987 := bstep (se 1 (by rfl) ⟨1088990, by rfl⟩ : syracuseStep 1451987 = 2177981) B2177981
theorem B1452017 : Blo 964590 1452017 := bstep (se 2 (by rfl) ⟨544506, by rfl⟩ : syracuseStep 1452017 = 1089013) B1089013
theorem B5515249 : Blo 964590 5515249 := bstep (se 2 (by rfl) ⟨2068218, by rfl⟩ : syracuseStep 5515249 = 4136437) B4136437
theorem B1452035 : Blo 964590 1452035 := bstep (se 1 (by rfl) ⟨1089026, by rfl⟩ : syracuseStep 1452035 = 2178053) B2178053
theorem B3483661 : Blo 964590 3483661 := bstep (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) B1306373
theorem B1452065 : Blo 964590 1452065 := bstep (se 2 (by rfl) ⟨544524, by rfl⟩ : syracuseStep 1452065 = 1089049) B1089049
theorem B2172977 : Blo 964590 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B1452083 : Blo 964590 1452083 := bstep (se 1 (by rfl) ⟨1089062, by rfl⟩ : syracuseStep 1452083 = 2178125) B2178125
theorem B2172995 : Blo 964590 2172995 := bstep (se 1 (by rfl) ⟨1629746, by rfl⟩ : syracuseStep 2172995 = 3259493) B3259493
theorem B1452113 : Blo 964590 1452113 := bstep (se 2 (by rfl) ⟨544542, by rfl⟩ : syracuseStep 1452113 = 1089085) B1089085
theorem B1452131 : Blo 964590 1452131 := bstep (se 1 (by rfl) ⟨1089098, by rfl⟩ : syracuseStep 1452131 = 2178197) B2178197
theorem B1222771 : Blo 964590 1222771 := bstep (se 1 (by rfl) ⟨917078, by rfl⟩ : syracuseStep 1222771 = 1834157) B1834157
theorem B1452161 : Blo 964590 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B1452179 : Blo 964590 1452179 := bstep (se 1 (by rfl) ⟨1089134, by rfl⟩ : syracuseStep 1452179 = 2178269) B2178269
theorem B1452209 : Blo 964590 1452209 := bstep (se 2 (by rfl) ⟨544578, by rfl⟩ : syracuseStep 1452209 = 1089157) B1089157
theorem B1452227 : Blo 964590 1452227 := bstep (se 1 (by rfl) ⟨1089170, by rfl⟩ : syracuseStep 1452227 = 2178341) B2178341
theorem B3090641 : Blo 964590 3090641 := bstep (se 2 (by rfl) ⟨1158990, by rfl⟩ : syracuseStep 3090641 = 2317981) B2317981
theorem B1222867 : Blo 964590 1222867 := bstep (se 1 (by rfl) ⟨917150, by rfl⟩ : syracuseStep 1222867 = 1834301) B1834301
theorem B1452257 : Blo 964590 1452257 := bstep (se 2 (by rfl) ⟨544596, by rfl⟩ : syracuseStep 1452257 = 1089193) B1089193
theorem B1452275 : Blo 964590 1452275 := bstep (se 1 (by rfl) ⟨1089206, by rfl⟩ : syracuseStep 1452275 = 2178413) B2178413
theorem B1452305 : Blo 964590 1452305 := bstep (se 2 (by rfl) ⟨544614, by rfl⟩ : syracuseStep 1452305 = 1089229) B1089229
theorem B1452323 : Blo 964590 1452323 := bstep (se 1 (by rfl) ⟨1089242, by rfl⟩ : syracuseStep 1452323 = 2178485) B2178485
theorem B1452353 : Blo 964590 1452353 := bstep (se 2 (by rfl) ⟨544632, by rfl⟩ : syracuseStep 1452353 = 1089265) B1089265
theorem B2173265 : Blo 964590 2173265 := bstep (se 2 (by rfl) ⟨814974, by rfl⟩ : syracuseStep 2173265 = 1629949) B1629949
theorem B1452371 : Blo 964590 1452371 := bstep (se 1 (by rfl) ⟨1089278, by rfl⟩ : syracuseStep 1452371 = 2178557) B2178557
theorem B2173283 : Blo 964590 2173283 := bstep (se 1 (by rfl) ⟨1629962, by rfl⟩ : syracuseStep 2173283 = 3259925) B3259925
theorem B5581169 : Blo 964590 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B1452401 : Blo 964590 1452401 := bstep (se 2 (by rfl) ⟨544650, by rfl⟩ : syracuseStep 1452401 = 1089301) B1089301
theorem B1452419 : Blo 964590 1452419 := bstep (se 1 (by rfl) ⟨1089314, by rfl⟩ : syracuseStep 1452419 = 2178629) B2178629
theorem B1452449 : Blo 964590 1452449 := bstep (se 2 (by rfl) ⟨544668, by rfl⟩ : syracuseStep 1452449 = 1089337) B1089337
theorem B1452467 : Blo 964590 1452467 := bstep (se 1 (by rfl) ⟨1089350, by rfl⟩ : syracuseStep 1452467 = 2178701) B2178701
theorem B1452497 : Blo 964590 1452497 := bstep (se 2 (by rfl) ⟨544686, by rfl⟩ : syracuseStep 1452497 = 1089373) B1089373
theorem B1550819 : Blo 964590 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1452515 : Blo 964590 1452515 := bstep (se 1 (by rfl) ⟨1089386, by rfl⟩ : syracuseStep 1452515 = 2178773) B2178773
theorem B1452545 : Blo 964590 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B1452563 : Blo 964590 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B1452593 : Blo 964590 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B1452611 : Blo 964590 1452611 := bstep (se 1 (by rfl) ⟨1089458, by rfl⟩ : syracuseStep 1452611 = 2178917) B2178917
theorem B1452641 : Blo 964590 1452641 := bstep (se 2 (by rfl) ⟨544740, by rfl⟩ : syracuseStep 1452641 = 1089481) B1089481
theorem B2173553 : Blo 964590 2173553 := bstep (se 2 (by rfl) ⟨815082, by rfl⟩ : syracuseStep 2173553 = 1630165) B1630165
theorem B1452659 : Blo 964590 1452659 := bstep (se 1 (by rfl) ⟨1089494, by rfl⟩ : syracuseStep 1452659 = 2178989) B2178989
theorem B2173571 : Blo 964590 2173571 := bstep (se 1 (by rfl) ⟨1630178, by rfl⟩ : syracuseStep 2173571 = 3260357) B3260357
theorem B1452689 : Blo 964590 1452689 := bstep (se 2 (by rfl) ⟨544758, by rfl⟩ : syracuseStep 1452689 = 1089517) B1089517
theorem B1452707 : Blo 964590 1452707 := bstep (se 1 (by rfl) ⟨1089530, by rfl⟩ : syracuseStep 1452707 = 2179061) B2179061
theorem B1452737 : Blo 964590 1452737 := bstep (se 2 (by rfl) ⟨544776, by rfl⟩ : syracuseStep 1452737 = 1089553) B1089553
theorem B1223363 : Blo 964590 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B2206403 : Blo 964590 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1452755 : Blo 964590 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B1452785 : Blo 964590 1452785 := bstep (se 2 (by rfl) ⟨544794, by rfl⟩ : syracuseStep 1452785 = 1089589) B1089589
theorem B1551107 : Blo 964590 1551107 := bstep (se 1 (by rfl) ⟨1163330, by rfl⟩ : syracuseStep 1551107 = 2326661) B2326661
theorem B1452803 : Blo 964590 1452803 := bstep (se 1 (by rfl) ⟨1089602, by rfl⟩ : syracuseStep 1452803 = 2179205) B2179205
theorem B1452833 : Blo 964590 1452833 := bstep (se 2 (by rfl) ⟨544812, by rfl⟩ : syracuseStep 1452833 = 1089625) B1089625
theorem B1452851 : Blo 964590 1452851 := bstep (se 1 (by rfl) ⟨1089638, by rfl⟩ : syracuseStep 1452851 = 2179277) B2179277
theorem B1452881 : Blo 964590 1452881 := bstep (se 2 (by rfl) ⟨544830, by rfl⟩ : syracuseStep 1452881 = 1089661) B1089661
theorem B2173841 : Blo 964590 2173841 := bstep (se 2 (by rfl) ⟨815190, by rfl⟩ : syracuseStep 2173841 = 1630381) B1630381
theorem B2173859 : Blo 964590 2173859 := bstep (se 1 (by rfl) ⟨1630394, by rfl⟩ : syracuseStep 2173859 = 3260789) B3260789
theorem B6204451 : Blo 964590 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B2174129 : Blo 964590 2174129 := bstep (se 2 (by rfl) ⟨815298, by rfl⟩ : syracuseStep 2174129 = 1630597) B1630597
theorem B2174147 : Blo 964590 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B1224067 : Blo 964590 1224067 := bstep (se 1 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 1224067 = 1836101) B1836101
theorem B2174417 : Blo 964590 2174417 := bstep (se 2 (by rfl) ⟨815406, by rfl⟩ : syracuseStep 2174417 = 1630813) B1630813
theorem B2174435 : Blo 964590 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B1224163 : Blo 964590 1224163 := bstep (se 1 (by rfl) ⟨918122, by rfl⟩ : syracuseStep 1224163 = 1836245) B1836245
theorem B3255821 : Blo 964590 3255821 := bstep (se 3 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 3255821 = 1220933) B1220933
theorem B3255875 : Blo 964590 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B2174705 : Blo 964590 2174705 := bstep (se 2 (by rfl) ⟨815514, by rfl⟩ : syracuseStep 2174705 = 1631029) B1631029
theorem B2174723 : Blo 964590 2174723 := bstep (se 1 (by rfl) ⟨1631042, by rfl⟩ : syracuseStep 2174723 = 3262085) B3262085
theorem B3256145 : Blo 964590 3256145 := bstep (se 2 (by rfl) ⟨1221054, by rfl⟩ : syracuseStep 3256145 = 2442109) B2442109
theorem B1224659 : Blo 964590 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B2174993 : Blo 964590 2174993 := bstep (se 2 (by rfl) ⟨815622, by rfl⟩ : syracuseStep 2174993 = 1631245) B1631245
theorem B2175011 : Blo 964590 2175011 := bstep (se 1 (by rfl) ⟨1631258, by rfl⟩ : syracuseStep 2175011 = 3262517) B3262517
theorem B6697073 : Blo 964590 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B8269937 : Blo 964590 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B3911921 : Blo 964590 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B2175281 : Blo 964590 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B2175299 : Blo 964590 2175299 := bstep (se 1 (by rfl) ⟨1631474, by rfl⟩ : syracuseStep 2175299 = 3262949) B3262949
theorem B3256685 : Blo 964590 3256685 := bstep (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) B1221257
theorem B3256739 : Blo 964590 3256739 := bstep (se 1 (by rfl) ⟨2442554, by rfl⟩ : syracuseStep 3256739 = 4885109) B4885109
theorem B3912113 : Blo 964590 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B4895153 : Blo 964590 4895153 := bstep (se 2 (by rfl) ⟨1835682, by rfl⟩ : syracuseStep 4895153 = 3671365) B3671365
theorem B2175569 : Blo 964590 2175569 := bstep (se 2 (by rfl) ⟨815838, by rfl⟩ : syracuseStep 2175569 = 1631677) B1631677
theorem B2175587 : Blo 964590 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B7844465 : Blo 964590 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B1225363 : Blo 964590 1225363 := bstep (se 1 (by rfl) ⟨919022, by rfl⟩ : syracuseStep 1225363 = 1838045) B1838045
theorem B3257009 : Blo 964590 3257009 := bstep (se 2 (by rfl) ⟨1221378, by rfl⟩ : syracuseStep 3257009 = 2442757) B2442757
theorem B1225459 : Blo 964590 1225459 := bstep (se 1 (by rfl) ⟨919094, by rfl⟩ : syracuseStep 1225459 = 1838189) B1838189
theorem B2175857 : Blo 964590 2175857 := bstep (se 2 (by rfl) ⟨815946, by rfl⟩ : syracuseStep 2175857 = 1631893) B1631893
theorem B2175875 : Blo 964590 2175875 := bstep (se 1 (by rfl) ⟨1631906, by rfl⟩ : syracuseStep 2175875 = 3263813) B3263813
theorem B2176145 : Blo 964590 2176145 := bstep (se 2 (by rfl) ⟨816054, by rfl⟩ : syracuseStep 2176145 = 1632109) B1632109
theorem B2176163 : Blo 964590 2176163 := bstep (se 1 (by rfl) ⟨1632122, by rfl⟩ : syracuseStep 2176163 = 3264245) B3264245
theorem B3257549 : Blo 964590 3257549 := bstep (se 3 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 3257549 = 1221581) B1221581
theorem B3257603 : Blo 964590 3257603 := bstep (se 1 (by rfl) ⟨2443202, by rfl⟩ : syracuseStep 3257603 = 4886405) B4886405
theorem B1652065 : Blo 964590 1652065 := bstep (se 2 (by rfl) ⟨619524, by rfl⟩ : syracuseStep 1652065 = 1239049) B1239049
theorem B1160563 : Blo 964590 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B2176433 : Blo 964590 2176433 := bstep (se 2 (by rfl) ⟨816162, by rfl⟩ : syracuseStep 2176433 = 1632325) B1632325
theorem B2176451 : Blo 964590 2176451 := bstep (se 1 (by rfl) ⟨1632338, by rfl⟩ : syracuseStep 2176451 = 3264677) B3264677
theorem B3257873 : Blo 964590 3257873 := bstep (se 2 (by rfl) ⟨1221702, by rfl⟩ : syracuseStep 3257873 = 2443405) B2443405
theorem B3094051 : Blo 964590 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B2176721 : Blo 964590 2176721 := bstep (se 2 (by rfl) ⟨816270, by rfl⟩ : syracuseStep 2176721 = 1632541) B1632541
theorem B2176739 : Blo 964590 2176739 := bstep (se 1 (by rfl) ⟨1632554, by rfl⟩ : syracuseStep 2176739 = 3265109) B3265109
theorem B3094321 : Blo 964590 3094321 := bstep (se 2 (by rfl) ⟨1160370, by rfl⟩ : syracuseStep 3094321 = 2320741) B2320741
theorem B4896611 : Blo 964590 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B2177009 : Blo 964590 2177009 := bstep (se 2 (by rfl) ⟨816378, by rfl⟩ : syracuseStep 2177009 = 1632757) B1632757
theorem B964595 : Blo 964590 964595 := bstep (se 1 (by rfl) ⟨723446, by rfl⟩ : syracuseStep 964595 = 1446893) B1446893
theorem B964611 : Blo 964590 964611 := bstep (se 1 (by rfl) ⟨723458, by rfl⟩ : syracuseStep 964611 = 1446917) B1446917
theorem B2177027 : Blo 964590 2177027 := bstep (se 1 (by rfl) ⟨1632770, by rfl⟩ : syracuseStep 2177027 = 3265541) B3265541
theorem B964627 : Blo 964590 964627 := bstep (se 1 (by rfl) ⟨723470, by rfl⟩ : syracuseStep 964627 = 1446941) B1446941
theorem B964643 : Blo 964590 964643 := bstep (se 1 (by rfl) ⟨723482, by rfl⟩ : syracuseStep 964643 = 1446965) B1446965
theorem B3258413 : Blo 964590 3258413 := bstep (se 3 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 3258413 = 1221905) B1221905
theorem B964659 : Blo 964590 964659 := bstep (se 1 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 964659 = 1446989) B1446989
theorem B964675 : Blo 964590 964675 := bstep (se 1 (by rfl) ⟨723506, by rfl⟩ : syracuseStep 964675 = 1447013) B1447013
theorem B964691 : Blo 964590 964691 := bstep (se 1 (by rfl) ⟨723518, by rfl⟩ : syracuseStep 964691 = 1447037) B1447037
theorem B964707 : Blo 964590 964707 := bstep (se 1 (by rfl) ⟨723530, by rfl⟩ : syracuseStep 964707 = 1447061) B1447061
theorem B3258467 : Blo 964590 3258467 := bstep (se 1 (by rfl) ⟨2443850, by rfl⟩ : syracuseStep 3258467 = 4887701) B4887701
theorem B964723 : Blo 964590 964723 := bstep (se 1 (by rfl) ⟨723542, by rfl⟩ : syracuseStep 964723 = 1447085) B1447085
theorem B964739 : Blo 964590 964739 := bstep (se 1 (by rfl) ⟨723554, by rfl⟩ : syracuseStep 964739 = 1447109) B1447109
theorem B964755 : Blo 964590 964755 := bstep (se 1 (by rfl) ⟨723566, by rfl⟩ : syracuseStep 964755 = 1447133) B1447133
theorem B964771 : Blo 964590 964771 := bstep (se 1 (by rfl) ⟨723578, by rfl⟩ : syracuseStep 964771 = 1447157) B1447157
theorem B964787 : Blo 964590 964787 := bstep (se 1 (by rfl) ⟨723590, by rfl⟩ : syracuseStep 964787 = 1447181) B1447181
theorem B964803 : Blo 964590 964803 := bstep (se 1 (by rfl) ⟨723602, by rfl⟩ : syracuseStep 964803 = 1447205) B1447205
theorem B964819 : Blo 964590 964819 := bstep (se 1 (by rfl) ⟨723614, by rfl⟩ : syracuseStep 964819 = 1447229) B1447229
theorem B964835 : Blo 964590 964835 := bstep (se 1 (by rfl) ⟨723626, by rfl⟩ : syracuseStep 964835 = 1447253) B1447253
theorem B964851 : Blo 964590 964851 := bstep (se 1 (by rfl) ⟨723638, by rfl⟩ : syracuseStep 964851 = 1447277) B1447277
theorem B964867 : Blo 964590 964867 := bstep (se 1 (by rfl) ⟨723650, by rfl⟩ : syracuseStep 964867 = 1447301) B1447301
theorem B7354637 : Blo 964590 7354637 := bstep (se 3 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 7354637 = 2757989) B2757989
theorem B2177297 : Blo 964590 2177297 := bstep (se 2 (by rfl) ⟨816486, by rfl⟩ : syracuseStep 2177297 = 1632973) B1632973
theorem B964883 : Blo 964590 964883 := bstep (se 1 (by rfl) ⟨723662, by rfl⟩ : syracuseStep 964883 = 1447325) B1447325
theorem B964899 : Blo 964590 964899 := bstep (se 1 (by rfl) ⟨723674, by rfl⟩ : syracuseStep 964899 = 1447349) B1447349
theorem B2177315 : Blo 964590 2177315 := bstep (se 1 (by rfl) ⟨1632986, by rfl⟩ : syracuseStep 2177315 = 3265973) B3265973
theorem B964915 : Blo 964590 964915 := bstep (se 1 (by rfl) ⟨723686, by rfl⟩ : syracuseStep 964915 = 1447373) B1447373
theorem B964931 : Blo 964590 964931 := bstep (se 1 (by rfl) ⟨723698, by rfl⟩ : syracuseStep 964931 = 1447397) B1447397
theorem B964947 : Blo 964590 964947 := bstep (se 1 (by rfl) ⟨723710, by rfl⟩ : syracuseStep 964947 = 1447421) B1447421
theorem B964963 : Blo 964590 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B3258737 : Blo 964590 3258737 := bstep (se 2 (by rfl) ⟨1222026, by rfl⟩ : syracuseStep 3258737 = 2444053) B2444053
theorem B964979 : Blo 964590 964979 := bstep (se 1 (by rfl) ⟨723734, by rfl⟩ : syracuseStep 964979 = 1447469) B1447469
theorem B964995 : Blo 964590 964995 := bstep (se 1 (by rfl) ⟨723746, by rfl⟩ : syracuseStep 964995 = 1447493) B1447493
theorem B11745677 : Blo 964590 11745677 := bstep (se 3 (by rfl) ⟨2202314, by rfl⟩ : syracuseStep 11745677 = 4404629) B4404629
theorem B965011 : Blo 964590 965011 := bstep (se 1 (by rfl) ⟨723758, by rfl⟩ : syracuseStep 965011 = 1447517) B1447517
theorem B965027 : Blo 964590 965027 := bstep (se 1 (by rfl) ⟨723770, by rfl⟩ : syracuseStep 965027 = 1447541) B1447541
theorem B965043 : Blo 964590 965043 := bstep (se 1 (by rfl) ⟨723782, by rfl⟩ : syracuseStep 965043 = 1447565) B1447565
theorem B965059 : Blo 964590 965059 := bstep (se 1 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 965059 = 1447589) B1447589
theorem B3914189 : Blo 964590 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B965075 : Blo 964590 965075 := bstep (se 1 (by rfl) ⟨723806, by rfl⟩ : syracuseStep 965075 = 1447613) B1447613
theorem B965091 : Blo 964590 965091 := bstep (se 1 (by rfl) ⟨723818, by rfl⟩ : syracuseStep 965091 = 1447637) B1447637
theorem B965107 : Blo 964590 965107 := bstep (se 1 (by rfl) ⟨723830, by rfl⟩ : syracuseStep 965107 = 1447661) B1447661
theorem B965123 : Blo 964590 965123 := bstep (se 1 (by rfl) ⟨723842, by rfl⟩ : syracuseStep 965123 = 1447685) B1447685
theorem B965139 : Blo 964590 965139 := bstep (se 1 (by rfl) ⟨723854, by rfl⟩ : syracuseStep 965139 = 1447709) B1447709
theorem B965155 : Blo 964590 965155 := bstep (se 1 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 965155 = 1447733) B1447733
theorem B2177585 : Blo 964590 2177585 := bstep (se 2 (by rfl) ⟨816594, by rfl⟩ : syracuseStep 2177585 = 1633189) B1633189
theorem B965171 : Blo 964590 965171 := bstep (se 1 (by rfl) ⟨723878, by rfl⟩ : syracuseStep 965171 = 1447757) B1447757
theorem B2177603 : Blo 964590 2177603 := bstep (se 1 (by rfl) ⟨1633202, by rfl⟩ : syracuseStep 2177603 = 3266405) B3266405
theorem B965187 : Blo 964590 965187 := bstep (se 1 (by rfl) ⟨723890, by rfl⟩ : syracuseStep 965187 = 1447781) B1447781
theorem B965203 : Blo 964590 965203 := bstep (se 1 (by rfl) ⟨723902, by rfl⟩ : syracuseStep 965203 = 1447805) B1447805
theorem B965219 : Blo 964590 965219 := bstep (se 1 (by rfl) ⟨723914, by rfl⟩ : syracuseStep 965219 = 1447829) B1447829
theorem B5880433 : Blo 964590 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B965235 : Blo 964590 965235 := bstep (se 1 (by rfl) ⟨723926, by rfl⟩ : syracuseStep 965235 = 1447853) B1447853
theorem B965251 : Blo 964590 965251 := bstep (se 1 (by rfl) ⟨723938, by rfl⟩ : syracuseStep 965251 = 1447877) B1447877
theorem B4897421 : Blo 964590 4897421 := bstep (se 3 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 4897421 = 1836533) B1836533
theorem B7846541 : Blo 964590 7846541 := bstep (se 3 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 7846541 = 2942453) B2942453
theorem B965267 : Blo 964590 965267 := bstep (se 1 (by rfl) ⟨723950, by rfl⟩ : syracuseStep 965267 = 1447901) B1447901
theorem B965283 : Blo 964590 965283 := bstep (se 1 (by rfl) ⟨723962, by rfl⟩ : syracuseStep 965283 = 1447925) B1447925
theorem B965299 : Blo 964590 965299 := bstep (se 1 (by rfl) ⟨723974, by rfl⟩ : syracuseStep 965299 = 1447949) B1447949
theorem B965315 : Blo 964590 965315 := bstep (se 1 (by rfl) ⟨723986, by rfl⟩ : syracuseStep 965315 = 1447973) B1447973
theorem B965331 : Blo 964590 965331 := bstep (se 1 (by rfl) ⟨723998, by rfl⟩ : syracuseStep 965331 = 1447997) B1447997
theorem B965347 : Blo 964590 965347 := bstep (se 1 (by rfl) ⟨724010, by rfl⟩ : syracuseStep 965347 = 1448021) B1448021
theorem B965363 : Blo 964590 965363 := bstep (se 1 (by rfl) ⟨724022, by rfl⟩ : syracuseStep 965363 = 1448045) B1448045
theorem B965379 : Blo 964590 965379 := bstep (se 1 (by rfl) ⟨724034, by rfl⟩ : syracuseStep 965379 = 1448069) B1448069
theorem B965395 : Blo 964590 965395 := bstep (se 1 (by rfl) ⟨724046, by rfl⟩ : syracuseStep 965395 = 1448093) B1448093
theorem B965411 : Blo 964590 965411 := bstep (se 1 (by rfl) ⟨724058, by rfl⟩ : syracuseStep 965411 = 1448117) B1448117
theorem B965427 : Blo 964590 965427 := bstep (se 1 (by rfl) ⟨724070, by rfl⟩ : syracuseStep 965427 = 1448141) B1448141
theorem B965443 : Blo 964590 965443 := bstep (se 1 (by rfl) ⟨724082, by rfl⟩ : syracuseStep 965443 = 1448165) B1448165
theorem B2177873 : Blo 964590 2177873 := bstep (se 2 (by rfl) ⟨816702, by rfl⟩ : syracuseStep 2177873 = 1633405) B1633405
theorem B965459 : Blo 964590 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B965475 : Blo 964590 965475 := bstep (se 1 (by rfl) ⟨724106, by rfl⟩ : syracuseStep 965475 = 1448213) B1448213
theorem B2177891 : Blo 964590 2177891 := bstep (se 1 (by rfl) ⟨1633418, by rfl⟩ : syracuseStep 2177891 = 3266837) B3266837
theorem B965491 : Blo 964590 965491 := bstep (se 1 (by rfl) ⟨724118, by rfl⟩ : syracuseStep 965491 = 1448237) B1448237
theorem B965507 : Blo 964590 965507 := bstep (se 1 (by rfl) ⟨724130, by rfl⟩ : syracuseStep 965507 = 1448261) B1448261
theorem B3259277 : Blo 964590 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B965523 : Blo 964590 965523 := bstep (se 1 (by rfl) ⟨724142, by rfl⟩ : syracuseStep 965523 = 1448285) B1448285
theorem B965539 : Blo 964590 965539 := bstep (se 1 (by rfl) ⟨724154, by rfl⟩ : syracuseStep 965539 = 1448309) B1448309
theorem B965555 : Blo 964590 965555 := bstep (se 1 (by rfl) ⟨724166, by rfl⟩ : syracuseStep 965555 = 1448333) B1448333
theorem B965571 : Blo 964590 965571 := bstep (se 1 (by rfl) ⟨724178, by rfl⟩ : syracuseStep 965571 = 1448357) B1448357
theorem B3259331 : Blo 964590 3259331 := bstep (se 1 (by rfl) ⟨2444498, by rfl⟩ : syracuseStep 3259331 = 4888997) B4888997
theorem B965587 : Blo 964590 965587 := bstep (se 1 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 965587 = 1448381) B1448381
theorem B965603 : Blo 964590 965603 := bstep (se 1 (by rfl) ⟨724202, by rfl⟩ : syracuseStep 965603 = 1448405) B1448405
theorem B965619 : Blo 964590 965619 := bstep (se 1 (by rfl) ⟨724214, by rfl⟩ : syracuseStep 965619 = 1448429) B1448429
theorem B965635 : Blo 964590 965635 := bstep (se 1 (by rfl) ⟨724226, by rfl⟩ : syracuseStep 965635 = 1448453) B1448453
theorem B965651 : Blo 964590 965651 := bstep (se 1 (by rfl) ⟨724238, by rfl⟩ : syracuseStep 965651 = 1448477) B1448477
theorem B965667 : Blo 964590 965667 := bstep (se 1 (by rfl) ⟨724250, by rfl⟩ : syracuseStep 965667 = 1448501) B1448501
theorem B965683 : Blo 964590 965683 := bstep (se 1 (by rfl) ⟨724262, by rfl⟩ : syracuseStep 965683 = 1448525) B1448525
theorem B965699 : Blo 964590 965699 := bstep (se 1 (by rfl) ⟨724274, by rfl⟩ : syracuseStep 965699 = 1448549) B1448549
theorem B1162307 : Blo 964590 1162307 := bstep (se 1 (by rfl) ⟨871730, by rfl⟩ : syracuseStep 1162307 = 1743461) B1743461
theorem B965715 : Blo 964590 965715 := bstep (se 1 (by rfl) ⟨724286, by rfl⟩ : syracuseStep 965715 = 1448573) B1448573
theorem B965731 : Blo 964590 965731 := bstep (se 1 (by rfl) ⟨724298, by rfl⟩ : syracuseStep 965731 = 1448597) B1448597
theorem B2178161 : Blo 964590 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B965747 : Blo 964590 965747 := bstep (se 1 (by rfl) ⟨724310, by rfl⟩ : syracuseStep 965747 = 1448621) B1448621
theorem B965763 : Blo 964590 965763 := bstep (se 1 (by rfl) ⟨724322, by rfl⟩ : syracuseStep 965763 = 1448645) B1448645
theorem B2178179 : Blo 964590 2178179 := bstep (se 1 (by rfl) ⟨1633634, by rfl⟩ : syracuseStep 2178179 = 3267269) B3267269
theorem B965779 : Blo 964590 965779 := bstep (se 1 (by rfl) ⟨724334, by rfl⟩ : syracuseStep 965779 = 1448669) B1448669
theorem B965795 : Blo 964590 965795 := bstep (se 1 (by rfl) ⟨724346, by rfl⟩ : syracuseStep 965795 = 1448693) B1448693
theorem B965811 : Blo 964590 965811 := bstep (se 1 (by rfl) ⟨724358, by rfl⟩ : syracuseStep 965811 = 1448717) B1448717
theorem B965827 : Blo 964590 965827 := bstep (se 1 (by rfl) ⟨724370, by rfl⟩ : syracuseStep 965827 = 1448741) B1448741
theorem B3259601 : Blo 964590 3259601 := bstep (se 2 (by rfl) ⟨1222350, by rfl⟩ : syracuseStep 3259601 = 2444701) B2444701
theorem B965843 : Blo 964590 965843 := bstep (se 1 (by rfl) ⟨724382, by rfl⟩ : syracuseStep 965843 = 1448765) B1448765
theorem B965859 : Blo 964590 965859 := bstep (se 1 (by rfl) ⟨724394, by rfl⟩ : syracuseStep 965859 = 1448789) B1448789
theorem B965875 : Blo 964590 965875 := bstep (se 1 (by rfl) ⟨724406, by rfl⟩ : syracuseStep 965875 = 1448813) B1448813
theorem B965891 : Blo 964590 965891 := bstep (se 1 (by rfl) ⟨724418, by rfl⟩ : syracuseStep 965891 = 1448837) B1448837
theorem B965907 : Blo 964590 965907 := bstep (se 1 (by rfl) ⟨724430, by rfl⟩ : syracuseStep 965907 = 1448861) B1448861
theorem B5946659 : Blo 964590 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B965923 : Blo 964590 965923 := bstep (se 1 (by rfl) ⟨724442, by rfl⟩ : syracuseStep 965923 = 1448885) B1448885
theorem B965939 : Blo 964590 965939 := bstep (se 1 (by rfl) ⟨724454, by rfl⟩ : syracuseStep 965939 = 1448909) B1448909
theorem B965955 : Blo 964590 965955 := bstep (se 1 (by rfl) ⟨724466, by rfl⟩ : syracuseStep 965955 = 1448933) B1448933
theorem B965971 : Blo 964590 965971 := bstep (se 1 (by rfl) ⟨724478, by rfl⟩ : syracuseStep 965971 = 1448957) B1448957
theorem B965987 : Blo 964590 965987 := bstep (se 1 (by rfl) ⟨724490, by rfl⟩ : syracuseStep 965987 = 1448981) B1448981
theorem B3095921 : Blo 964590 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B966003 : Blo 964590 966003 := bstep (se 1 (by rfl) ⟨724502, by rfl⟩ : syracuseStep 966003 = 1449005) B1449005
theorem B966019 : Blo 964590 966019 := bstep (se 1 (by rfl) ⟨724514, by rfl⟩ : syracuseStep 966019 = 1449029) B1449029
theorem B2178449 : Blo 964590 2178449 := bstep (se 2 (by rfl) ⟨816918, by rfl⟩ : syracuseStep 2178449 = 1633837) B1633837
theorem B966035 : Blo 964590 966035 := bstep (se 1 (by rfl) ⟨724526, by rfl⟩ : syracuseStep 966035 = 1449053) B1449053
theorem B966051 : Blo 964590 966051 := bstep (se 1 (by rfl) ⟨724538, by rfl⟩ : syracuseStep 966051 = 1449077) B1449077
theorem B2178467 : Blo 964590 2178467 := bstep (se 1 (by rfl) ⟨1633850, by rfl⟩ : syracuseStep 2178467 = 3267701) B3267701
theorem B966067 : Blo 964590 966067 := bstep (se 1 (by rfl) ⟨724550, by rfl⟩ : syracuseStep 966067 = 1449101) B1449101
theorem B966083 : Blo 964590 966083 := bstep (se 1 (by rfl) ⟨724562, by rfl⟩ : syracuseStep 966083 = 1449125) B1449125
theorem B966099 : Blo 964590 966099 := bstep (se 1 (by rfl) ⟨724574, by rfl⟩ : syracuseStep 966099 = 1449149) B1449149
theorem B966115 : Blo 964590 966115 := bstep (se 1 (by rfl) ⟨724586, by rfl⟩ : syracuseStep 966115 = 1449173) B1449173
theorem B966131 : Blo 964590 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B966147 : Blo 964590 966147 := bstep (se 1 (by rfl) ⟨724610, by rfl⟩ : syracuseStep 966147 = 1449221) B1449221
theorem B966163 : Blo 964590 966163 := bstep (se 1 (by rfl) ⟨724622, by rfl⟩ : syracuseStep 966163 = 1449245) B1449245
theorem B966179 : Blo 964590 966179 := bstep (se 1 (by rfl) ⟨724634, by rfl⟩ : syracuseStep 966179 = 1449269) B1449269
theorem B966195 : Blo 964590 966195 := bstep (se 1 (by rfl) ⟨724646, by rfl⟩ : syracuseStep 966195 = 1449293) B1449293
theorem B966211 : Blo 964590 966211 := bstep (se 1 (by rfl) ⟨724658, by rfl⟩ : syracuseStep 966211 = 1449317) B1449317
theorem B966227 : Blo 964590 966227 := bstep (se 1 (by rfl) ⟨724670, by rfl⟩ : syracuseStep 966227 = 1449341) B1449341
theorem B966243 : Blo 964590 966243 := bstep (se 1 (by rfl) ⟨724682, by rfl⟩ : syracuseStep 966243 = 1449365) B1449365
theorem B966259 : Blo 964590 966259 := bstep (se 1 (by rfl) ⟨724694, by rfl⟩ : syracuseStep 966259 = 1449389) B1449389
theorem B966275 : Blo 964590 966275 := bstep (se 1 (by rfl) ⟨724706, by rfl⟩ : syracuseStep 966275 = 1449413) B1449413
theorem B966291 : Blo 964590 966291 := bstep (se 1 (by rfl) ⟨724718, by rfl⟩ : syracuseStep 966291 = 1449437) B1449437
theorem B966307 : Blo 964590 966307 := bstep (se 1 (by rfl) ⟨724730, by rfl⟩ : syracuseStep 966307 = 1449461) B1449461
theorem B1490609 : Blo 964590 1490609 := bstep (se 2 (by rfl) ⟨558978, by rfl⟩ : syracuseStep 1490609 = 1117957) B1117957
theorem B2178737 : Blo 964590 2178737 := bstep (se 2 (by rfl) ⟨817026, by rfl⟩ : syracuseStep 2178737 = 1634053) B1634053
theorem B966323 : Blo 964590 966323 := bstep (se 1 (by rfl) ⟨724742, by rfl⟩ : syracuseStep 966323 = 1449485) B1449485
theorem B966339 : Blo 964590 966339 := bstep (se 1 (by rfl) ⟨724754, by rfl⟩ : syracuseStep 966339 = 1449509) B1449509
theorem B2178755 : Blo 964590 2178755 := bstep (se 1 (by rfl) ⟨1634066, by rfl⟩ : syracuseStep 2178755 = 3268133) B3268133
theorem B3096269 : Blo 964590 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B966355 : Blo 964590 966355 := bstep (se 1 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 966355 = 1449533) B1449533
theorem B966371 : Blo 964590 966371 := bstep (se 1 (by rfl) ⟨724778, by rfl⟩ : syracuseStep 966371 = 1449557) B1449557
theorem B3260141 : Blo 964590 3260141 := bstep (se 3 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 3260141 = 1222553) B1222553
theorem B966387 : Blo 964590 966387 := bstep (se 1 (by rfl) ⟨724790, by rfl⟩ : syracuseStep 966387 = 1449581) B1449581
theorem B966403 : Blo 964590 966403 := bstep (se 1 (by rfl) ⟨724802, by rfl⟩ : syracuseStep 966403 = 1449605) B1449605
theorem B966419 : Blo 964590 966419 := bstep (se 1 (by rfl) ⟨724814, by rfl⟩ : syracuseStep 966419 = 1449629) B1449629
theorem B3260195 : Blo 964590 3260195 := bstep (se 1 (by rfl) ⟨2445146, by rfl⟩ : syracuseStep 3260195 = 4890293) B4890293
theorem B966435 : Blo 964590 966435 := bstep (se 1 (by rfl) ⟨724826, by rfl⟩ : syracuseStep 966435 = 1449653) B1449653
theorem B1031987 : Blo 964590 1031987 := bstep (se 1 (by rfl) ⟨773990, by rfl⟩ : syracuseStep 1031987 = 1547981) B1547981
theorem B966451 : Blo 964590 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B966467 : Blo 964590 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B966483 : Blo 964590 966483 := bstep (se 1 (by rfl) ⟨724862, by rfl⟩ : syracuseStep 966483 = 1449725) B1449725
theorem B966499 : Blo 964590 966499 := bstep (se 1 (by rfl) ⟨724874, by rfl⟩ : syracuseStep 966499 = 1449749) B1449749
theorem B966515 : Blo 964590 966515 := bstep (se 1 (by rfl) ⟨724886, by rfl⟩ : syracuseStep 966515 = 1449773) B1449773
theorem B966531 : Blo 964590 966531 := bstep (se 1 (by rfl) ⟨724898, by rfl⟩ : syracuseStep 966531 = 1449797) B1449797
theorem B966547 : Blo 964590 966547 := bstep (se 1 (by rfl) ⟨724910, by rfl⟩ : syracuseStep 966547 = 1449821) B1449821
theorem B966563 : Blo 964590 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B966579 : Blo 964590 966579 := bstep (se 1 (by rfl) ⟨724934, by rfl⟩ : syracuseStep 966579 = 1449869) B1449869
theorem B966595 : Blo 964590 966595 := bstep (se 1 (by rfl) ⟨724946, by rfl⟩ : syracuseStep 966595 = 1449893) B1449893
theorem B2179025 : Blo 964590 2179025 := bstep (se 2 (by rfl) ⟨817134, by rfl⟩ : syracuseStep 2179025 = 1634269) B1634269
theorem B966611 : Blo 964590 966611 := bstep (se 1 (by rfl) ⟨724958, by rfl⟩ : syracuseStep 966611 = 1449917) B1449917
theorem B966627 : Blo 964590 966627 := bstep (se 1 (by rfl) ⟨724970, by rfl⟩ : syracuseStep 966627 = 1449941) B1449941
theorem B2179043 : Blo 964590 2179043 := bstep (se 1 (by rfl) ⟨1634282, by rfl⟩ : syracuseStep 2179043 = 3268565) B3268565
theorem B966643 : Blo 964590 966643 := bstep (se 1 (by rfl) ⟨724982, by rfl⟩ : syracuseStep 966643 = 1449965) B1449965
theorem B966659 : Blo 964590 966659 := bstep (se 1 (by rfl) ⟨724994, by rfl⟩ : syracuseStep 966659 = 1449989) B1449989
theorem B966675 : Blo 964590 966675 := bstep (se 1 (by rfl) ⟨725006, by rfl⟩ : syracuseStep 966675 = 1450013) B1450013
theorem B966691 : Blo 964590 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B3260465 : Blo 964590 3260465 := bstep (se 2 (by rfl) ⟨1222674, by rfl⟩ : syracuseStep 3260465 = 2445349) B2445349
theorem B966707 : Blo 964590 966707 := bstep (se 1 (by rfl) ⟨725030, by rfl⟩ : syracuseStep 966707 = 1450061) B1450061
theorem B966723 : Blo 964590 966723 := bstep (se 1 (by rfl) ⟨725042, by rfl⟩ : syracuseStep 966723 = 1450085) B1450085
theorem B966739 : Blo 964590 966739 := bstep (se 1 (by rfl) ⟨725054, by rfl⟩ : syracuseStep 966739 = 1450109) B1450109
theorem B3915875 : Blo 964590 3915875 := bstep (se 1 (by rfl) ⟨2936906, by rfl⟩ : syracuseStep 3915875 = 5873813) B5873813
theorem B966755 : Blo 964590 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B966771 : Blo 964590 966771 := bstep (se 1 (by rfl) ⟨725078, by rfl⟩ : syracuseStep 966771 = 1450157) B1450157
theorem B966787 : Blo 964590 966787 := bstep (se 1 (by rfl) ⟨725090, by rfl⟩ : syracuseStep 966787 = 1450181) B1450181
theorem B966803 : Blo 964590 966803 := bstep (se 1 (by rfl) ⟨725102, by rfl⟩ : syracuseStep 966803 = 1450205) B1450205
theorem B966819 : Blo 964590 966819 := bstep (se 1 (by rfl) ⟨725114, by rfl⟩ : syracuseStep 966819 = 1450229) B1450229
theorem B966835 : Blo 964590 966835 := bstep (se 1 (by rfl) ⟨725126, by rfl⟩ : syracuseStep 966835 = 1450253) B1450253
theorem B966851 : Blo 964590 966851 := bstep (se 1 (by rfl) ⟨725138, by rfl⟩ : syracuseStep 966851 = 1450277) B1450277
theorem B966867 : Blo 964590 966867 := bstep (se 1 (by rfl) ⟨725150, by rfl⟩ : syracuseStep 966867 = 1450301) B1450301
theorem B966883 : Blo 964590 966883 := bstep (se 1 (by rfl) ⟨725162, by rfl⟩ : syracuseStep 966883 = 1450325) B1450325
theorem B2179313 : Blo 964590 2179313 := bstep (se 2 (by rfl) ⟨817242, by rfl⟩ : syracuseStep 2179313 = 1634485) B1634485
theorem B966899 : Blo 964590 966899 := bstep (se 1 (by rfl) ⟨725174, by rfl⟩ : syracuseStep 966899 = 1450349) B1450349
theorem B966915 : Blo 964590 966915 := bstep (se 1 (by rfl) ⟨725186, by rfl⟩ : syracuseStep 966915 = 1450373) B1450373
theorem B966931 : Blo 964590 966931 := bstep (se 1 (by rfl) ⟨725198, by rfl⟩ : syracuseStep 966931 = 1450397) B1450397
theorem B966947 : Blo 964590 966947 := bstep (se 1 (by rfl) ⟨725210, by rfl⟩ : syracuseStep 966947 = 1450421) B1450421
theorem B966963 : Blo 964590 966963 := bstep (se 1 (by rfl) ⟨725222, by rfl⟩ : syracuseStep 966963 = 1450445) B1450445
theorem B966979 : Blo 964590 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B966995 : Blo 964590 966995 := bstep (se 1 (by rfl) ⟨725246, by rfl⟩ : syracuseStep 966995 = 1450493) B1450493
theorem B967011 : Blo 964590 967011 := bstep (se 1 (by rfl) ⟨725258, by rfl⟩ : syracuseStep 967011 = 1450517) B1450517
theorem B967027 : Blo 964590 967027 := bstep (se 1 (by rfl) ⟨725270, by rfl⟩ : syracuseStep 967027 = 1450541) B1450541
theorem B967043 : Blo 964590 967043 := bstep (se 1 (by rfl) ⟨725282, by rfl⟩ : syracuseStep 967043 = 1450565) B1450565
theorem B967059 : Blo 964590 967059 := bstep (se 1 (by rfl) ⟨725294, by rfl⟩ : syracuseStep 967059 = 1450589) B1450589
theorem B967075 : Blo 964590 967075 := bstep (se 1 (by rfl) ⟨725306, by rfl⟩ : syracuseStep 967075 = 1450613) B1450613
theorem B967091 : Blo 964590 967091 := bstep (se 1 (by rfl) ⟨725318, by rfl⟩ : syracuseStep 967091 = 1450637) B1450637
theorem B967107 : Blo 964590 967107 := bstep (se 1 (by rfl) ⟨725330, by rfl⟩ : syracuseStep 967107 = 1450661) B1450661
theorem B967123 : Blo 964590 967123 := bstep (se 1 (by rfl) ⟨725342, by rfl⟩ : syracuseStep 967123 = 1450685) B1450685
theorem B967139 : Blo 964590 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B967155 : Blo 964590 967155 := bstep (se 1 (by rfl) ⟨725366, by rfl⟩ : syracuseStep 967155 = 1450733) B1450733
theorem B967171 : Blo 964590 967171 := bstep (se 1 (by rfl) ⟨725378, by rfl⟩ : syracuseStep 967171 = 1450757) B1450757
theorem B967187 : Blo 964590 967187 := bstep (se 1 (by rfl) ⟨725390, by rfl⟩ : syracuseStep 967187 = 1450781) B1450781
theorem B967203 : Blo 964590 967203 := bstep (se 1 (by rfl) ⟨725402, by rfl⟩ : syracuseStep 967203 = 1450805) B1450805
theorem B967219 : Blo 964590 967219 := bstep (se 1 (by rfl) ⟨725414, by rfl⟩ : syracuseStep 967219 = 1450829) B1450829
theorem B967235 : Blo 964590 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B3261005 : Blo 964590 3261005 := bstep (se 3 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 3261005 = 1222877) B1222877
theorem B967251 : Blo 964590 967251 := bstep (se 1 (by rfl) ⟨725438, by rfl⟩ : syracuseStep 967251 = 1450877) B1450877
theorem B967267 : Blo 964590 967267 := bstep (se 1 (by rfl) ⟨725450, by rfl⟩ : syracuseStep 967267 = 1450901) B1450901
theorem B967283 : Blo 964590 967283 := bstep (se 1 (by rfl) ⟨725462, by rfl⟩ : syracuseStep 967283 = 1450925) B1450925
theorem B3261059 : Blo 964590 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B967299 : Blo 964590 967299 := bstep (se 1 (by rfl) ⟨725474, by rfl⟩ : syracuseStep 967299 = 1450949) B1450949
theorem B967315 : Blo 964590 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B967331 : Blo 964590 967331 := bstep (se 1 (by rfl) ⟨725498, by rfl⟩ : syracuseStep 967331 = 1450997) B1450997
theorem B3719857 : Blo 964590 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B967347 : Blo 964590 967347 := bstep (se 1 (by rfl) ⟨725510, by rfl⟩ : syracuseStep 967347 = 1451021) B1451021
theorem B967363 : Blo 964590 967363 := bstep (se 1 (by rfl) ⟨725522, by rfl⟩ : syracuseStep 967363 = 1451045) B1451045
theorem B967379 : Blo 964590 967379 := bstep (se 1 (by rfl) ⟨725534, by rfl⟩ : syracuseStep 967379 = 1451069) B1451069
theorem B967395 : Blo 964590 967395 := bstep (se 1 (by rfl) ⟨725546, by rfl⟩ : syracuseStep 967395 = 1451093) B1451093
theorem B967411 : Blo 964590 967411 := bstep (se 1 (by rfl) ⟨725558, by rfl⟩ : syracuseStep 967411 = 1451117) B1451117
theorem B967427 : Blo 964590 967427 := bstep (se 1 (by rfl) ⟨725570, by rfl⟩ : syracuseStep 967427 = 1451141) B1451141
theorem B967443 : Blo 964590 967443 := bstep (se 1 (by rfl) ⟨725582, by rfl⟩ : syracuseStep 967443 = 1451165) B1451165
theorem B967459 : Blo 964590 967459 := bstep (se 1 (by rfl) ⟨725594, by rfl⟩ : syracuseStep 967459 = 1451189) B1451189
theorem B967475 : Blo 964590 967475 := bstep (se 1 (by rfl) ⟨725606, by rfl⟩ : syracuseStep 967475 = 1451213) B1451213
theorem B967491 : Blo 964590 967491 := bstep (se 1 (by rfl) ⟨725618, by rfl⟩ : syracuseStep 967491 = 1451237) B1451237
theorem B967507 : Blo 964590 967507 := bstep (se 1 (by rfl) ⟨725630, by rfl⟩ : syracuseStep 967507 = 1451261) B1451261
theorem B967523 : Blo 964590 967523 := bstep (se 1 (by rfl) ⟨725642, by rfl⟩ : syracuseStep 967523 = 1451285) B1451285
theorem B967539 : Blo 964590 967539 := bstep (se 1 (by rfl) ⟨725654, by rfl⟩ : syracuseStep 967539 = 1451309) B1451309
theorem B967555 : Blo 964590 967555 := bstep (se 1 (by rfl) ⟨725666, by rfl⟩ : syracuseStep 967555 = 1451333) B1451333
theorem B3261329 : Blo 964590 3261329 := bstep (se 2 (by rfl) ⟨1222998, by rfl⟩ : syracuseStep 3261329 = 2445997) B2445997
theorem B967571 : Blo 964590 967571 := bstep (se 1 (by rfl) ⟨725678, by rfl⟩ : syracuseStep 967571 = 1451357) B1451357
theorem B967587 : Blo 964590 967587 := bstep (se 1 (by rfl) ⟨725690, by rfl⟩ : syracuseStep 967587 = 1451381) B1451381
theorem B967603 : Blo 964590 967603 := bstep (se 1 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 967603 = 1451405) B1451405
theorem B967619 : Blo 964590 967619 := bstep (se 1 (by rfl) ⟨725714, by rfl⟩ : syracuseStep 967619 = 1451429) B1451429
theorem B967635 : Blo 964590 967635 := bstep (se 1 (by rfl) ⟨725726, by rfl⟩ : syracuseStep 967635 = 1451453) B1451453
theorem B967651 : Blo 964590 967651 := bstep (se 1 (by rfl) ⟨725738, by rfl⟩ : syracuseStep 967651 = 1451477) B1451477
theorem B967667 : Blo 964590 967667 := bstep (se 1 (by rfl) ⟨725750, by rfl⟩ : syracuseStep 967667 = 1451501) B1451501
theorem B967683 : Blo 964590 967683 := bstep (se 1 (by rfl) ⟨725762, by rfl⟩ : syracuseStep 967683 = 1451525) B1451525
theorem B967699 : Blo 964590 967699 := bstep (se 1 (by rfl) ⟨725774, by rfl⟩ : syracuseStep 967699 = 1451549) B1451549
theorem B4637731 : Blo 964590 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B967715 : Blo 964590 967715 := bstep (se 1 (by rfl) ⟨725786, by rfl⟩ : syracuseStep 967715 = 1451573) B1451573
theorem B967731 : Blo 964590 967731 := bstep (se 1 (by rfl) ⟨725798, by rfl⟩ : syracuseStep 967731 = 1451597) B1451597
theorem B967747 : Blo 964590 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B967763 : Blo 964590 967763 := bstep (se 1 (by rfl) ⟨725822, by rfl⟩ : syracuseStep 967763 = 1451645) B1451645
theorem B967779 : Blo 964590 967779 := bstep (se 1 (by rfl) ⟨725834, by rfl⟩ : syracuseStep 967779 = 1451669) B1451669
theorem B967795 : Blo 964590 967795 := bstep (se 1 (by rfl) ⟨725846, by rfl⟩ : syracuseStep 967795 = 1451693) B1451693
theorem B967811 : Blo 964590 967811 := bstep (se 1 (by rfl) ⟨725858, by rfl⟩ : syracuseStep 967811 = 1451717) B1451717
theorem B967827 : Blo 964590 967827 := bstep (se 1 (by rfl) ⟨725870, by rfl⟩ : syracuseStep 967827 = 1451741) B1451741
theorem B1492115 : Blo 964590 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B967843 : Blo 964590 967843 := bstep (se 1 (by rfl) ⟨725882, by rfl⟩ : syracuseStep 967843 = 1451765) B1451765
theorem B967859 : Blo 964590 967859 := bstep (se 1 (by rfl) ⟨725894, by rfl⟩ : syracuseStep 967859 = 1451789) B1451789
theorem B967875 : Blo 964590 967875 := bstep (se 1 (by rfl) ⟨725906, by rfl⟩ : syracuseStep 967875 = 1451813) B1451813
theorem B967891 : Blo 964590 967891 := bstep (se 1 (by rfl) ⟨725918, by rfl⟩ : syracuseStep 967891 = 1451837) B1451837
theorem B967907 : Blo 964590 967907 := bstep (se 1 (by rfl) ⟨725930, by rfl⟩ : syracuseStep 967907 = 1451861) B1451861
theorem B967923 : Blo 964590 967923 := bstep (se 1 (by rfl) ⟨725942, by rfl⟩ : syracuseStep 967923 = 1451885) B1451885
theorem B967939 : Blo 964590 967939 := bstep (se 1 (by rfl) ⟨725954, by rfl⟩ : syracuseStep 967939 = 1451909) B1451909
theorem B967955 : Blo 964590 967955 := bstep (se 1 (by rfl) ⟨725966, by rfl⟩ : syracuseStep 967955 = 1451933) B1451933
theorem B967971 : Blo 964590 967971 := bstep (se 1 (by rfl) ⟨725978, by rfl⟩ : syracuseStep 967971 = 1451957) B1451957
theorem B2442545 : Blo 964590 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B967987 : Blo 964590 967987 := bstep (se 1 (by rfl) ⟨725990, by rfl⟩ : syracuseStep 967987 = 1451981) B1451981
theorem B968003 : Blo 964590 968003 := bstep (se 1 (by rfl) ⟨726002, by rfl⟩ : syracuseStep 968003 = 1452005) B1452005
theorem B968019 : Blo 964590 968019 := bstep (se 1 (by rfl) ⟨726014, by rfl⟩ : syracuseStep 968019 = 1452029) B1452029
theorem B2442595 : Blo 964590 2442595 := bstep (se 1 (by rfl) ⟨1831946, by rfl⟩ : syracuseStep 2442595 = 3663893) B3663893
theorem B968035 : Blo 964590 968035 := bstep (se 1 (by rfl) ⟨726026, by rfl⟩ : syracuseStep 968035 = 1452053) B1452053
theorem B968051 : Blo 964590 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B968067 : Blo 964590 968067 := bstep (se 1 (by rfl) ⟨726050, by rfl⟩ : syracuseStep 968067 = 1452101) B1452101
theorem B968083 : Blo 964590 968083 := bstep (se 1 (by rfl) ⟨726062, by rfl⟩ : syracuseStep 968083 = 1452125) B1452125
theorem B968099 : Blo 964590 968099 := bstep (se 1 (by rfl) ⟨726074, by rfl⟩ : syracuseStep 968099 = 1452149) B1452149
theorem B3261869 : Blo 964590 3261869 := bstep (se 3 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 3261869 = 1223201) B1223201
theorem B968115 : Blo 964590 968115 := bstep (se 1 (by rfl) ⟨726086, by rfl⟩ : syracuseStep 968115 = 1452173) B1452173
theorem B968131 : Blo 964590 968131 := bstep (se 1 (by rfl) ⟨726098, by rfl⟩ : syracuseStep 968131 = 1452197) B1452197
theorem B968147 : Blo 964590 968147 := bstep (se 1 (by rfl) ⟨726110, by rfl⟩ : syracuseStep 968147 = 1452221) B1452221
theorem B3261923 : Blo 964590 3261923 := bstep (se 1 (by rfl) ⟨2446442, by rfl⟩ : syracuseStep 3261923 = 4892885) B4892885
theorem B968163 : Blo 964590 968163 := bstep (se 1 (by rfl) ⟨726122, by rfl⟩ : syracuseStep 968163 = 1452245) B1452245
theorem B2442737 : Blo 964590 2442737 := bstep (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) B1832053
theorem B4900337 : Blo 964590 4900337 := bstep (se 2 (by rfl) ⟨1837626, by rfl⟩ : syracuseStep 4900337 = 3675253) B3675253
theorem B968179 : Blo 964590 968179 := bstep (se 1 (by rfl) ⟨726134, by rfl⟩ : syracuseStep 968179 = 1452269) B1452269
theorem B968195 : Blo 964590 968195 := bstep (se 1 (by rfl) ⟨726146, by rfl⟩ : syracuseStep 968195 = 1452293) B1452293
theorem B3098125 : Blo 964590 3098125 := bstep (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) B1161797
theorem B968211 : Blo 964590 968211 := bstep (se 1 (by rfl) ⟨726158, by rfl⟩ : syracuseStep 968211 = 1452317) B1452317
theorem B1394209 : Blo 964590 1394209 := bstep (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) B1045657
theorem B968227 : Blo 964590 968227 := bstep (se 1 (by rfl) ⟨726170, by rfl⟩ : syracuseStep 968227 = 1452341) B1452341
theorem B968243 : Blo 964590 968243 := bstep (se 1 (by rfl) ⟨726182, by rfl⟩ : syracuseStep 968243 = 1452365) B1452365
theorem B968259 : Blo 964590 968259 := bstep (se 1 (by rfl) ⟨726194, by rfl⟩ : syracuseStep 968259 = 1452389) B1452389
theorem B968275 : Blo 964590 968275 := bstep (se 1 (by rfl) ⟨726206, by rfl⟩ : syracuseStep 968275 = 1452413) B1452413
theorem B968291 : Blo 964590 968291 := bstep (se 1 (by rfl) ⟨726218, by rfl⟩ : syracuseStep 968291 = 1452437) B1452437
theorem B968307 : Blo 964590 968307 := bstep (se 1 (by rfl) ⟨726230, by rfl⟩ : syracuseStep 968307 = 1452461) B1452461
theorem B968323 : Blo 964590 968323 := bstep (se 1 (by rfl) ⟨726242, by rfl⟩ : syracuseStep 968323 = 1452485) B1452485
theorem B968339 : Blo 964590 968339 := bstep (se 1 (by rfl) ⟨726254, by rfl⟩ : syracuseStep 968339 = 1452509) B1452509
theorem B968355 : Blo 964590 968355 := bstep (se 1 (by rfl) ⟨726266, by rfl⟩ : syracuseStep 968355 = 1452533) B1452533
theorem B968371 : Blo 964590 968371 := bstep (se 1 (by rfl) ⟨726278, by rfl⟩ : syracuseStep 968371 = 1452557) B1452557
theorem B968387 : Blo 964590 968387 := bstep (se 1 (by rfl) ⟨726290, by rfl⟩ : syracuseStep 968387 = 1452581) B1452581
theorem B968403 : Blo 964590 968403 := bstep (se 1 (by rfl) ⟨726302, by rfl⟩ : syracuseStep 968403 = 1452605) B1452605
theorem B968419 : Blo 964590 968419 := bstep (se 1 (by rfl) ⟨726314, by rfl⟩ : syracuseStep 968419 = 1452629) B1452629
theorem B3262193 : Blo 964590 3262193 := bstep (se 2 (by rfl) ⟨1223322, by rfl⟩ : syracuseStep 3262193 = 2446645) B2446645
theorem B968435 : Blo 964590 968435 := bstep (se 1 (by rfl) ⟨726326, by rfl⟩ : syracuseStep 968435 = 1452653) B1452653
theorem B968451 : Blo 964590 968451 := bstep (se 1 (by rfl) ⟨726338, by rfl⟩ : syracuseStep 968451 = 1452677) B1452677
theorem B5654285 : Blo 964590 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B1034003 : Blo 964590 1034003 := bstep (se 1 (by rfl) ⟨775502, by rfl⟩ : syracuseStep 1034003 = 1551005) B1551005
theorem B968467 : Blo 964590 968467 := bstep (se 1 (by rfl) ⟨726350, by rfl⟩ : syracuseStep 968467 = 1452701) B1452701
theorem B968483 : Blo 964590 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B968499 : Blo 964590 968499 := bstep (se 1 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 968499 = 1452749) B1452749
theorem B968515 : Blo 964590 968515 := bstep (se 1 (by rfl) ⟨726386, by rfl⟩ : syracuseStep 968515 = 1452773) B1452773
theorem B968531 : Blo 964590 968531 := bstep (se 1 (by rfl) ⟨726398, by rfl⟩ : syracuseStep 968531 = 1452797) B1452797
theorem B968547 : Blo 964590 968547 := bstep (se 1 (by rfl) ⟨726410, by rfl⟩ : syracuseStep 968547 = 1452821) B1452821
theorem B968563 : Blo 964590 968563 := bstep (se 1 (by rfl) ⟨726422, by rfl⟩ : syracuseStep 968563 = 1452845) B1452845
theorem B968579 : Blo 964590 968579 := bstep (se 1 (by rfl) ⟨726434, by rfl⟩ : syracuseStep 968579 = 1452869) B1452869
theorem B18827405 : Blo 964590 18827405 := bstep (se 3 (by rfl) ⟨3530138, by rfl⟩ : syracuseStep 18827405 = 7060277) B7060277
theorem B4638961 : Blo 964590 4638961 := bstep (se 2 (by rfl) ⟨1739610, by rfl⟩ : syracuseStep 4638961 = 3479221) B3479221
theorem B3262733 : Blo 964590 3262733 := bstep (se 3 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 3262733 = 1223525) B1223525
theorem B3262787 : Blo 964590 3262787 := bstep (se 1 (by rfl) ⟨2447090, by rfl⟩ : syracuseStep 3262787 = 4894181) B4894181
theorem B2443729 : Blo 964590 2443729 := bstep (se 2 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 2443729 = 1832797) B1832797
theorem B18565685 : Blo 964590 18565685 := bstep (se 5 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 18565685 = 1740533) B1740533
theorem B3263057 : Blo 964590 3263057 := bstep (se 2 (by rfl) ⟨1223646, by rfl⟩ : syracuseStep 3263057 = 2447293) B2447293
theorem B2444003 : Blo 964590 2444003 := bstep (se 1 (by rfl) ⟨1833002, by rfl⟩ : syracuseStep 2444003 = 3666005) B3666005
theorem B7326449 : Blo 964590 7326449 := bstep (se 2 (by rfl) ⟨2747418, by rfl⟩ : syracuseStep 7326449 = 5494837) B5494837
theorem B2444195 : Blo 964590 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B4901795 : Blo 964590 4901795 := bstep (se 1 (by rfl) ⟨3676346, by rfl⟩ : syracuseStep 4901795 = 7352693) B7352693
theorem B1592371 : Blo 964590 1592371 := bstep (se 1 (by rfl) ⟨1194278, by rfl⟩ : syracuseStep 1592371 = 2388557) B2388557
theorem B3263597 : Blo 964590 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B3263651 : Blo 964590 3263651 := bstep (se 1 (by rfl) ⟨2447738, by rfl⟩ : syracuseStep 3263651 = 4895477) B4895477
theorem B3099971 : Blo 964590 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B3263921 : Blo 964590 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B3132913 : Blo 964590 3132913 := bstep (se 2 (by rfl) ⟨1174842, by rfl⟩ : syracuseStep 3132913 = 2349685) B2349685
theorem B9293453 : Blo 964590 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B4902605 : Blo 964590 4902605 := bstep (se 3 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 4902605 = 1838477) B1838477
theorem B3100369 : Blo 964590 3100369 := bstep (se 2 (by rfl) ⟨1162638, by rfl⟩ : syracuseStep 3100369 = 2325277) B2325277
theorem B1101523 : Blo 964590 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B1527587 : Blo 964590 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B2477873 : Blo 964590 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B2445137 : Blo 964590 2445137 := bstep (se 2 (by rfl) ⟨916926, by rfl⟩ : syracuseStep 2445137 = 1833853) B1833853
theorem B2445187 : Blo 964590 2445187 := bstep (se 1 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 2445187 = 3667781) B3667781
theorem B3264461 : Blo 964590 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B3264515 : Blo 964590 3264515 := bstep (se 1 (by rfl) ⟨2448386, by rfl⟩ : syracuseStep 3264515 = 4896773) B4896773
theorem B2445329 : Blo 964590 2445329 := bstep (se 2 (by rfl) ⟨916998, by rfl⟩ : syracuseStep 2445329 = 1833997) B1833997
theorem B3100817 : Blo 964590 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B3264785 : Blo 964590 3264785 := bstep (se 2 (by rfl) ⟨1224294, by rfl⟩ : syracuseStep 3264785 = 2448589) B2448589
theorem B2937347 : Blo 964590 2937347 := bstep (se 1 (by rfl) ⟨2203010, by rfl⟩ : syracuseStep 2937347 = 4406021) B4406021
theorem B2609741 : Blo 964590 2609741 := bstep (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) B978653
theorem B2478755 : Blo 964590 2478755 := bstep (se 1 (by rfl) ⟨1859066, by rfl⟩ : syracuseStep 2478755 = 3718133) B3718133
theorem B3265325 : Blo 964590 3265325 := bstep (se 3 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 3265325 = 1224497) B1224497
theorem B3265379 : Blo 964590 3265379 := bstep (se 1 (by rfl) ⟨2449034, by rfl⟩ : syracuseStep 3265379 = 4898069) B4898069
theorem B2446321 : Blo 964590 2446321 := bstep (se 2 (by rfl) ⟨917370, by rfl⟩ : syracuseStep 2446321 = 1834741) B1834741
theorem B3265649 : Blo 964590 3265649 := bstep (se 2 (by rfl) ⟨1224618, by rfl⟩ : syracuseStep 3265649 = 2449237) B2449237
theorem B2446595 : Blo 964590 2446595 := bstep (se 1 (by rfl) ⟨1834946, by rfl⟩ : syracuseStep 2446595 = 3669893) B3669893
theorem B2446787 : Blo 964590 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B6182513 : Blo 964590 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B3266189 : Blo 964590 3266189 := bstep (se 3 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 3266189 = 1224821) B1224821
theorem B1627843 : Blo 964590 1627843 := bstep (se 1 (by rfl) ⟨1220882, by rfl⟩ : syracuseStep 1627843 = 2441765) B2441765
theorem B3266243 : Blo 964590 3266243 := bstep (se 1 (by rfl) ⟨2449682, by rfl⟩ : syracuseStep 3266243 = 4899365) B4899365
theorem B4970317 : Blo 964590 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B1627985 : Blo 964590 1627985 := bstep (se 2 (by rfl) ⟨610494, by rfl⟩ : syracuseStep 1627985 = 1220989) B1220989
theorem B1628113 : Blo 964590 1628113 := bstep (se 2 (by rfl) ⟨610542, by rfl⟩ : syracuseStep 1628113 = 1221085) B1221085
theorem B3266513 : Blo 964590 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B1628147 : Blo 964590 1628147 := bstep (se 1 (by rfl) ⟨1221110, by rfl⟩ : syracuseStep 1628147 = 2442221) B2442221
theorem B4642865 : Blo 964590 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B1628275 : Blo 964590 1628275 := bstep (se 1 (by rfl) ⟨1221206, by rfl⟩ : syracuseStep 1628275 = 2442413) B2442413
theorem B1857667 : Blo 964590 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B3102893 : Blo 964590 3102893 := bstep (se 3 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 3102893 = 1163585) B1163585
theorem B1628417 : Blo 964590 1628417 := bstep (se 2 (by rfl) ⟨610656, by rfl⟩ : syracuseStep 1628417 = 1221313) B1221313
theorem B2447729 : Blo 964590 2447729 := bstep (se 2 (by rfl) ⟨917898, by rfl⟩ : syracuseStep 2447729 = 1835797) B1835797
theorem B1628545 : Blo 964590 1628545 := bstep (se 2 (by rfl) ⟨610704, by rfl⟩ : syracuseStep 1628545 = 1221409) B1221409
theorem B1628579 : Blo 964590 1628579 := bstep (se 1 (by rfl) ⟨1221434, by rfl⟩ : syracuseStep 1628579 = 2442869) B2442869
theorem B2447779 : Blo 964590 2447779 := bstep (se 1 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 2447779 = 3671669) B3671669
theorem B3267053 : Blo 964590 3267053 := bstep (se 3 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 3267053 = 1225145) B1225145
theorem B1628707 : Blo 964590 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B3267107 : Blo 964590 3267107 := bstep (se 1 (by rfl) ⟨2450330, by rfl⟩ : syracuseStep 3267107 = 4900661) B4900661
theorem B2447921 : Blo 964590 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B1628849 : Blo 964590 1628849 := bstep (se 2 (by rfl) ⟨610818, by rfl⟩ : syracuseStep 1628849 = 1221637) B1221637
theorem B1628977 : Blo 964590 1628977 := bstep (se 2 (by rfl) ⟨610866, by rfl⟩ : syracuseStep 1628977 = 1221733) B1221733
theorem B3267377 : Blo 964590 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B1629011 : Blo 964590 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B1956803 : Blo 964590 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B1629139 : Blo 964590 1629139 := bstep (se 1 (by rfl) ⟨1221854, by rfl⟩ : syracuseStep 1629139 = 2443709) B2443709
theorem B1956835 : Blo 964590 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B1629281 : Blo 964590 1629281 := bstep (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) B1221961
theorem B5889187 : Blo 964590 5889187 := bstep (se 1 (by rfl) ⟨4416890, by rfl⟩ : syracuseStep 5889187 = 8833781) B8833781
theorem B1629409 : Blo 964590 1629409 := bstep (se 2 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 1629409 = 1222057) B1222057
theorem B1629443 : Blo 964590 1629443 := bstep (se 1 (by rfl) ⟨1222082, by rfl⟩ : syracuseStep 1629443 = 2444165) B2444165
theorem B5496113 : Blo 964590 5496113 := bstep (se 2 (by rfl) ⟨2061042, by rfl⟩ : syracuseStep 5496113 = 4122085) B4122085
theorem B3267917 : Blo 964590 3267917 := bstep (se 3 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 3267917 = 1225469) B1225469
theorem B1858897 : Blo 964590 1858897 := bstep (se 2 (by rfl) ⟨697086, by rfl⟩ : syracuseStep 1858897 = 1394173) B1394173
theorem B1629571 : Blo 964590 1629571 := bstep (se 1 (by rfl) ⟨1222178, by rfl⟩ : syracuseStep 1629571 = 2444357) B2444357
theorem B3267971 : Blo 964590 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B8248817 : Blo 964590 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B2448913 : Blo 964590 2448913 := bstep (se 2 (by rfl) ⟨918342, by rfl⟩ : syracuseStep 2448913 = 1836685) B1836685
theorem B1629713 : Blo 964590 1629713 := bstep (se 2 (by rfl) ⟨611142, by rfl⟩ : syracuseStep 1629713 = 1222285) B1222285
theorem B14900849 : Blo 964590 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B1629841 : Blo 964590 1629841 := bstep (se 2 (by rfl) ⟨611190, by rfl⟩ : syracuseStep 1629841 = 1222381) B1222381
theorem B3268241 : Blo 964590 3268241 := bstep (se 2 (by rfl) ⟨1225590, by rfl⟩ : syracuseStep 3268241 = 2451181) B2451181
theorem B1629875 : Blo 964590 1629875 := bstep (se 1 (by rfl) ⟨1222406, by rfl⟩ : syracuseStep 1629875 = 2444813) B2444813
theorem B9297605 : Blo 964590 9297605 := bstep (se 4 (by rfl) ⟨871650, by rfl⟩ : syracuseStep 9297605 = 1743301) B1743301
theorem B19816163 : Blo 964590 19816163 := bstep (se 1 (by rfl) ⟨14862122, by rfl⟩ : syracuseStep 19816163 = 29724245) B29724245
theorem B2449187 : Blo 964590 2449187 := bstep (se 1 (by rfl) ⟨1836890, by rfl⟩ : syracuseStep 2449187 = 3673781) B3673781
theorem B1630003 : Blo 964590 1630003 := bstep (se 1 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 1630003 = 2445005) B2445005
theorem B1957745 : Blo 964590 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B2613169 : Blo 964590 2613169 := bstep (se 2 (by rfl) ⟨979938, by rfl⟩ : syracuseStep 2613169 = 1959877) B1959877
theorem B1630145 : Blo 964590 1630145 := bstep (se 2 (by rfl) ⟨611304, by rfl⟩ : syracuseStep 1630145 = 1222609) B1222609
theorem B2449379 : Blo 964590 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B1957873 : Blo 964590 1957873 := bstep (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) B1468405
theorem B6184973 : Blo 964590 6184973 := bstep (se 3 (by rfl) ⟨1159682, by rfl⟩ : syracuseStep 6184973 = 2319365) B2319365
theorem B1630273 : Blo 964590 1630273 := bstep (se 2 (by rfl) ⟨611352, by rfl⟩ : syracuseStep 1630273 = 1222705) B1222705
theorem B1630307 : Blo 964590 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B3268781 : Blo 964590 3268781 := bstep (se 3 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 3268781 = 1225793) B1225793
theorem B4120753 : Blo 964590 4120753 := bstep (se 2 (by rfl) ⟨1545282, by rfl⟩ : syracuseStep 4120753 = 3090565) B3090565
theorem B15655139 : Blo 964590 15655139 := bstep (se 1 (by rfl) ⟨11741354, by rfl⟩ : syracuseStep 15655139 = 23482709) B23482709
theorem B1630435 : Blo 964590 1630435 := bstep (se 1 (by rfl) ⟨1222826, by rfl⟩ : syracuseStep 1630435 = 2445653) B2445653
theorem B3268835 : Blo 964590 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B1630577 : Blo 964590 1630577 := bstep (se 2 (by rfl) ⟨611466, by rfl⟩ : syracuseStep 1630577 = 1222933) B1222933
theorem B4645325 : Blo 964590 4645325 := bstep (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) B1741997
theorem B1630705 : Blo 964590 1630705 := bstep (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) B1223029
theorem B1630739 : Blo 964590 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B3924557 : Blo 964590 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B3662435 : Blo 964590 3662435 := bstep (se 1 (by rfl) ⟨2746826, by rfl⟩ : syracuseStep 3662435 = 5493653) B5493653
theorem B1630867 : Blo 964590 1630867 := bstep (se 1 (by rfl) ⟨1223150, by rfl⟩ : syracuseStep 1630867 = 2446301) B2446301
theorem B5497571 : Blo 964590 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B1631009 : Blo 964590 1631009 := bstep (se 2 (by rfl) ⟨611628, by rfl⟩ : syracuseStep 1631009 = 1223257) B1223257
theorem B1467281 : Blo 964590 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B2450321 : Blo 964590 2450321 := bstep (se 2 (by rfl) ⟨918870, by rfl⟩ : syracuseStep 2450321 = 1837741) B1837741
theorem B1631137 : Blo 964590 1631137 := bstep (se 2 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 1631137 = 1223353) B1223353
theorem B1631171 : Blo 964590 1631171 := bstep (se 1 (by rfl) ⟨1223378, by rfl⟩ : syracuseStep 1631171 = 2446757) B2446757
theorem B2450371 : Blo 964590 2450371 := bstep (se 1 (by rfl) ⟨1837778, by rfl⟩ : syracuseStep 2450371 = 3675557) B3675557
theorem B7955441 : Blo 964590 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B1631299 : Blo 964590 1631299 := bstep (se 1 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 1631299 = 2446949) B2446949
theorem B2450513 : Blo 964590 2450513 := bstep (se 2 (by rfl) ⟨918942, by rfl⟩ : syracuseStep 2450513 = 1837885) B1837885
theorem B1631441 : Blo 964590 1631441 := bstep (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) B1223581
theorem B3663089 : Blo 964590 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B1631569 : Blo 964590 1631569 := bstep (se 2 (by rfl) ⟨611838, by rfl⟩ : syracuseStep 1631569 = 1223677) B1223677
theorem B1631603 : Blo 964590 1631603 := bstep (se 1 (by rfl) ⟨1223702, by rfl⟩ : syracuseStep 1631603 = 2447405) B2447405
theorem B3302819 : Blo 964590 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B1304033 : Blo 964590 1304033 := bstep (se 2 (by rfl) ⟨489012, by rfl⟩ : syracuseStep 1304033 = 978025) B978025
theorem B1631731 : Blo 964590 1631731 := bstep (se 1 (by rfl) ⟨1223798, by rfl⟩ : syracuseStep 1631731 = 2447597) B2447597
theorem B1631873 : Blo 964590 1631873 := bstep (se 2 (by rfl) ⟨611952, by rfl⟩ : syracuseStep 1631873 = 1223905) B1223905
theorem B1632001 : Blo 964590 1632001 := bstep (se 2 (by rfl) ⟨612000, by rfl⟩ : syracuseStep 1632001 = 1224001) B1224001
theorem B1632035 : Blo 964590 1632035 := bstep (se 1 (by rfl) ⟨1224026, by rfl⟩ : syracuseStep 1632035 = 2448053) B2448053
theorem B1632163 : Blo 964590 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B3139555 : Blo 964590 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B2615341 : Blo 964590 2615341 := bstep (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) B980753
theorem B1632305 : Blo 964590 1632305 := bstep (se 2 (by rfl) ⟨612114, by rfl⟩ : syracuseStep 1632305 = 1224229) B1224229
theorem B2451505 : Blo 964590 2451505 := bstep (se 2 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 2451505 = 1838629) B1838629
theorem B4122701 : Blo 964590 4122701 := bstep (se 3 (by rfl) ⟨773006, by rfl⟩ : syracuseStep 4122701 = 1546013) B1546013
theorem B1632433 : Blo 964590 1632433 := bstep (se 2 (by rfl) ⟨612162, by rfl⟩ : syracuseStep 1632433 = 1224325) B1224325
theorem B6187205 : Blo 964590 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1632467 : Blo 964590 1632467 := bstep (se 1 (by rfl) ⟨1224350, by rfl⟩ : syracuseStep 1632467 = 2448701) B2448701
theorem B1566977 : Blo 964590 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1632595 : Blo 964590 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B3303857 : Blo 964590 3303857 := bstep (se 2 (by rfl) ⟨1238946, by rfl⟩ : syracuseStep 3303857 = 2477893) B2477893
theorem B2320817 : Blo 964590 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1632737 : Blo 964590 1632737 := bstep (se 2 (by rfl) ⟨612276, by rfl⟩ : syracuseStep 1632737 = 1224553) B1224553
theorem B2517475 : Blo 964590 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B2091587 : Blo 964590 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B2615885 : Blo 964590 2615885 := bstep (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) B980957
theorem B1632865 : Blo 964590 1632865 := bstep (se 2 (by rfl) ⟨612324, by rfl⟩ : syracuseStep 1632865 = 1224649) B1224649
theorem B1632899 : Blo 964590 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B3664547 : Blo 964590 3664547 := bstep (se 1 (by rfl) ⟨2748410, by rfl⟩ : syracuseStep 3664547 = 5496821) B5496821
theorem B3664561 : Blo 964590 3664561 := bstep (se 2 (by rfl) ⟨1374210, by rfl⟩ : syracuseStep 3664561 = 2748421) B2748421
theorem B1633027 : Blo 964590 1633027 := bstep (se 1 (by rfl) ⟨1224770, by rfl⟩ : syracuseStep 1633027 = 2449541) B2449541
theorem B1469281 : Blo 964590 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B1633169 : Blo 964590 1633169 := bstep (se 2 (by rfl) ⟨612438, by rfl⟩ : syracuseStep 1633169 = 1224877) B1224877
theorem B1633297 : Blo 964590 1633297 := bstep (se 2 (by rfl) ⟨612486, by rfl⟩ : syracuseStep 1633297 = 1224973) B1224973
theorem B1633331 : Blo 964590 1633331 := bstep (se 1 (by rfl) ⟨1224998, by rfl⟩ : syracuseStep 1633331 = 2449997) B2449997
theorem B2944109 : Blo 964590 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B2747533 : Blo 964590 2747533 := bstep (se 3 (by rfl) ⟨515162, by rfl⟩ : syracuseStep 2747533 = 1030325) B1030325
theorem B1633459 : Blo 964590 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B2944205 : Blo 964590 2944205 := bstep (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) B1104077
theorem B1305811 : Blo 964590 1305811 := bstep (se 1 (by rfl) ⟨979358, by rfl⟩ : syracuseStep 1305811 = 1958717) B1958717
theorem B1633601 : Blo 964590 1633601 := bstep (se 2 (by rfl) ⟨612600, by rfl⟩ : syracuseStep 1633601 = 1225201) B1225201
theorem B1306049 : Blo 964590 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B1633729 : Blo 964590 1633729 := bstep (se 2 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 1633729 = 1225297) B1225297
theorem B1633763 : Blo 964590 1633763 := bstep (se 1 (by rfl) ⟨1225322, by rfl⟩ : syracuseStep 1633763 = 2450645) B2450645
theorem B978499 : Blo 964590 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B1633891 : Blo 964590 1633891 := bstep (se 1 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 1633891 = 2450837) B2450837
theorem B20868749 : Blo 964590 20868749 := bstep (se 3 (by rfl) ⟨3912890, by rfl⟩ : syracuseStep 20868749 = 7825781) B7825781
theorem B15920867 : Blo 964590 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B1634033 : Blo 964590 1634033 := bstep (se 2 (by rfl) ⟨612762, by rfl⟩ : syracuseStep 1634033 = 1225525) B1225525
theorem B2617201 : Blo 964590 2617201 := bstep (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) B1962901
theorem B1634161 : Blo 964590 1634161 := bstep (se 2 (by rfl) ⟨612810, by rfl⟩ : syracuseStep 1634161 = 1225621) B1225621
theorem B1634195 : Blo 964590 1634195 := bstep (se 1 (by rfl) ⟨1225646, by rfl⟩ : syracuseStep 1634195 = 2451293) B2451293
theorem B34467781 : Blo 964590 34467781 := bstep (se 4 (by rfl) ⟨3231354, by rfl⟩ : syracuseStep 34467781 = 6462709) B6462709
theorem B1470449 : Blo 964590 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B2060291 : Blo 964590 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B1634323 : Blo 964590 1634323 := bstep (se 1 (by rfl) ⟨1225742, by rfl⟩ : syracuseStep 1634323 = 2451485) B2451485
theorem B3666019 : Blo 964590 3666019 := bstep (se 1 (by rfl) ⟨2749514, by rfl⟩ : syracuseStep 3666019 = 5499029) B5499029
theorem B1962083 : Blo 964590 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B1634465 : Blo 964590 1634465 := bstep (se 2 (by rfl) ⟨612924, by rfl⟩ : syracuseStep 1634465 = 1225849) B1225849
theorem B2748593 : Blo 964590 2748593 := bstep (se 2 (by rfl) ⟨1030722, by rfl⟩ : syracuseStep 2748593 = 2061445) B2061445
theorem B1306801 : Blo 964590 1306801 := bstep (se 2 (by rfl) ⟨490050, by rfl⟩ : syracuseStep 1306801 = 980101) B980101
theorem B8810693 : Blo 964590 8810693 := bstep (se 4 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 8810693 = 1652005) B1652005
theorem B2322769 : Blo 964590 2322769 := bstep (se 2 (by rfl) ⟨871038, by rfl⟩ : syracuseStep 2322769 = 1742077) B1742077
theorem B1569107 : Blo 964590 1569107 := bstep (se 1 (by rfl) ⟨1176830, by rfl⟩ : syracuseStep 1569107 = 2353661) B2353661
theorem B2617699 : Blo 964590 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B1470899 : Blo 964590 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B1962673 : Blo 964590 1962673 := bstep (se 2 (by rfl) ⟨736002, by rfl⟩ : syracuseStep 1962673 = 1472005) B1472005
theorem B979651 : Blo 964590 979651 := bstep (se 1 (by rfl) ⟨734738, by rfl⟩ : syracuseStep 979651 = 1469477) B1469477
theorem B2323171 : Blo 964590 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B13202189 : Blo 964590 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B6714181 : Blo 964590 6714181 := bstep (se 4 (by rfl) ⟨629454, by rfl⟩ : syracuseStep 6714181 = 1258909) B1258909
theorem B2749265 : Blo 964590 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B1831825 : Blo 964590 1831825 := bstep (se 2 (by rfl) ⟨686934, by rfl⟩ : syracuseStep 1831825 = 1373869) B1373869
theorem B1373539 : Blo 964590 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B1766819 : Blo 964590 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B6977009 : Blo 964590 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B1177139 : Blo 964590 1177139 := bstep (se 1 (by rfl) ⟨882854, by rfl⟩ : syracuseStep 1177139 = 1765709) B1765709
theorem B2750051 : Blo 964590 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B1570433 : Blo 964590 1570433 := bstep (se 2 (by rfl) ⟨588912, by rfl⟩ : syracuseStep 1570433 = 1177825) B1177825
theorem B19854989 : Blo 964590 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B2324209 : Blo 964590 2324209 := bstep (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) B1743157
theorem B980867 : Blo 964590 980867 := bstep (se 1 (by rfl) ⟨735650, by rfl⟩ : syracuseStep 980867 = 1471301) B1471301
theorem B1374097 : Blo 964590 1374097 := bstep (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) B1030573
theorem B2750381 : Blo 964590 2750381 := bstep (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) B1031393
theorem B1832881 : Blo 964590 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1374131 : Blo 964590 1374131 := bstep (se 1 (by rfl) ⟨1030598, by rfl⟩ : syracuseStep 1374131 = 2061197) B2061197
theorem B2062307 : Blo 964590 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B2750449 : Blo 964590 2750449 := bstep (se 2 (by rfl) ⟨1031418, by rfl⟩ : syracuseStep 2750449 = 2062837) B2062837
theorem B4126733 : Blo 964590 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B13924493 : Blo 964590 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B1308817 : Blo 964590 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B2750723 : Blo 964590 2750723 := bstep (se 1 (by rfl) ⟨2063042, by rfl⟩ : syracuseStep 2750723 = 4126085) B4126085
theorem B3668237 : Blo 964590 3668237 := bstep (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) B1375589
theorem B1833283 : Blo 964590 1833283 := bstep (se 1 (by rfl) ⟨1374962, by rfl⟩ : syracuseStep 1833283 = 2749925) B2749925
theorem B4127075 : Blo 964590 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B1833329 : Blo 964590 1833329 := bstep (se 2 (by rfl) ⟨687498, by rfl⟩ : syracuseStep 1833329 = 1374997) B1374997
theorem B1571185 : Blo 964590 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B6977933 : Blo 964590 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B1374689 : Blo 964590 1374689 := bstep (se 2 (by rfl) ⟨515508, by rfl⟩ : syracuseStep 1374689 = 1031017) B1031017
theorem B1374769 : Blo 964590 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B1833617 : Blo 964590 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B4127537 : Blo 964590 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B31783877 : Blo 964590 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B2751565 : Blo 964590 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B6716515 : Blo 964590 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B2751725 : Blo 964590 2751725 := bstep (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) B1031897
theorem B1375555 : Blo 964590 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B1834339 : Blo 964590 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B2751907 : Blo 964590 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B3145169 : Blo 964590 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B1376033 : Blo 964590 1376033 := bstep (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) B1032025
theorem B1834787 : Blo 964590 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B1343281 : Blo 964590 1343281 := bstep (se 2 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 1343281 = 1007461) B1007461
theorem B1376147 : Blo 964590 1376147 := bstep (se 1 (by rfl) ⟨1032110, by rfl⟩ : syracuseStep 1376147 = 2064221) B2064221
theorem B2064323 : Blo 964590 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B13565893 : Blo 964590 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B1376227 : Blo 964590 1376227 := bstep (se 1 (by rfl) ⟨1032170, by rfl⟩ : syracuseStep 1376227 = 2064341) B2064341
theorem B2064665 : Blo 964590 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B1835531 : Blo 964590 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B13238801 : Blo 964590 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B1835713 : Blo 964590 1835713 := bstep (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) B1376785
theorem B4129501 : Blo 964590 4129501 := bstep (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) B1548563
theorem B6980357 : Blo 964590 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B1377047 : Blo 964590 1377047 := bstep (se 1 (by rfl) ⟨1032785, by rfl⟩ : syracuseStep 1377047 = 2065571) B2065571
theorem B2065409 : Blo 964590 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B3769523 : Blo 964590 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B1836427 : Blo 964590 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B12551603 : Blo 964590 12551603 := bstep (se 1 (by rfl) ⟨9413702, by rfl⟩ : syracuseStep 12551603 = 18827405) B18827405
theorem B1836503 : Blo 964590 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B2754071 : Blo 964590 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B34866893 : Blo 964590 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B4884299 : Blo 964590 4884299 := bstep (se 1 (by rfl) ⟨3663224, by rfl⟩ : syracuseStep 4884299 = 7326449) B7326449
theorem B2066305 : Blo 964590 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B8259479 : Blo 964590 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B7342001 : Blo 964590 7342001 := bstep (se 2 (by rfl) ⟨2753250, by rfl⟩ : syracuseStep 7342001 = 5506501) B5506501
theorem B4130833 : Blo 964590 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B1837171 : Blo 964590 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B2066647 : Blo 964590 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B3672323 : Blo 964590 3672323 := bstep (se 1 (by rfl) ⟨2754242, by rfl⟩ : syracuseStep 3672323 = 5508485) B5508485
theorem B3672337 : Blo 964590 3672337 := bstep (se 2 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 3672337 = 2754253) B2754253
theorem B2754881 : Blo 964590 2754881 := bstep (se 2 (by rfl) ⟨1033080, by rfl⟩ : syracuseStep 2754881 = 2066161) B2066161
theorem B1837399 : Blo 964590 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B5507459 : Blo 964590 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B7342487 : Blo 964590 7342487 := bstep (se 1 (by rfl) ⟨5506865, by rfl⟩ : syracuseStep 7342487 = 11013731) B11013731
theorem B6195635 : Blo 964590 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B1837505 : Blo 964590 1837505 := bstep (se 2 (by rfl) ⟨689064, by rfl⟩ : syracuseStep 1837505 = 1378129) B1378129
theorem B1018391 : Blo 964590 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B3672641 : Blo 964590 3672641 := bstep (se 2 (by rfl) ⟨1377240, by rfl⟩ : syracuseStep 3672641 = 2754481) B2754481
theorem B1837657 : Blo 964590 1837657 := bstep (se 2 (by rfl) ⟨689121, by rfl⟩ : syracuseStep 1837657 = 1378243) B1378243
theorem B16714421 : Blo 964590 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B2067211 : Blo 964590 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B1739827 : Blo 964590 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B7933079 : Blo 964590 7933079 := bstep (se 1 (by rfl) ⟨5949809, by rfl⟩ : syracuseStep 7933079 = 11899619) B11899619
theorem B3673309 : Blo 964590 3673309 := bstep (se 3 (by rfl) ⟨688745, by rfl⟩ : syracuseStep 3673309 = 1377491) B1377491
theorem B3476915 : Blo 964590 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B4886081 : Blo 964590 4886081 := bstep (se 2 (by rfl) ⟨1832280, by rfl⟩ : syracuseStep 4886081 = 3664561) B3664561
theorem B12390245 : Blo 964590 12390245 := bstep (se 4 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 12390245 = 2323171) B2323171
theorem B1085323 : Blo 964590 1085323 := bstep (se 1 (by rfl) ⟨813992, by rfl⟩ : syracuseStep 1085323 = 1627985) B1627985
theorem B3477421 : Blo 964590 3477421 := bstep (se 3 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 3477421 = 1304033) B1304033
theorem B2756531 : Blo 964590 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B2756555 : Blo 964590 2756555 := bstep (se 1 (by rfl) ⟨2067416, by rfl⟩ : syracuseStep 2756555 = 4134833) B4134833
theorem B1085431 : Blo 964590 1085431 := bstep (se 1 (by rfl) ⟨814073, by rfl⟩ : syracuseStep 1085431 = 1628147) B1628147
theorem B2068595 : Blo 964590 2068595 := bstep (se 1 (by rfl) ⟨1551446, by rfl⟩ : syracuseStep 2068595 = 3102893) B3102893
theorem B1085611 : Blo 964590 1085611 := bstep (se 1 (by rfl) ⟨814208, by rfl⟩ : syracuseStep 1085611 = 1628417) B1628417
theorem B1085719 : Blo 964590 1085719 := bstep (se 1 (by rfl) ⟨814289, by rfl⟩ : syracuseStep 1085719 = 1628579) B1628579
theorem B1085899 : Blo 964590 1085899 := bstep (se 1 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 1085899 = 1628849) B1628849
theorem B3674585 : Blo 964590 3674585 := bstep (se 2 (by rfl) ⟨1377969, by rfl⟩ : syracuseStep 3674585 = 2755939) B2755939
theorem B1086007 : Blo 964590 1086007 := bstep (se 1 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 1086007 = 1629011) B1629011
theorem B13931189 : Blo 964590 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B2757341 : Blo 964590 2757341 := bstep (se 3 (by rfl) ⟨517001, by rfl⟩ : syracuseStep 2757341 = 1034003) B1034003
theorem B1086187 : Blo 964590 1086187 := bstep (se 1 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 1086187 = 1629281) B1629281
theorem B1086295 : Blo 964590 1086295 := bstep (se 1 (by rfl) ⟨814721, by rfl⟩ : syracuseStep 1086295 = 1629443) B1629443
theorem B4133825 : Blo 964590 4133825 := bstep (se 2 (by rfl) ⟨1550184, by rfl⟩ : syracuseStep 4133825 = 3100369) B3100369
theorem B1446923 : Blo 964590 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B1086475 : Blo 964590 1086475 := bstep (se 1 (by rfl) ⟨814856, by rfl⟩ : syracuseStep 1086475 = 1629713) B1629713
theorem B1446935 : Blo 964590 1446935 := bstep (se 1 (by rfl) ⟨1085201, by rfl⟩ : syracuseStep 1446935 = 2170403) B2170403
theorem B9933899 : Blo 964590 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B1447001 : Blo 964590 1447001 := bstep (se 2 (by rfl) ⟨542625, by rfl⟩ : syracuseStep 1447001 = 1085251) B1085251
theorem B1086583 : Blo 964590 1086583 := bstep (se 1 (by rfl) ⟨814937, by rfl⟩ : syracuseStep 1086583 = 1629875) B1629875
theorem B6198403 : Blo 964590 6198403 := bstep (se 1 (by rfl) ⟨4648802, by rfl⟩ : syracuseStep 6198403 = 9297605) B9297605
theorem B13210775 : Blo 964590 13210775 := bstep (se 1 (by rfl) ⟨9908081, by rfl⟩ : syracuseStep 13210775 = 19816163) B19816163
theorem B1447115 : Blo 964590 1447115 := bstep (se 1 (by rfl) ⟨1085336, by rfl⟩ : syracuseStep 1447115 = 2170673) B2170673
theorem B1447127 : Blo 964590 1447127 := bstep (se 1 (by rfl) ⟨1085345, by rfl⟩ : syracuseStep 1447127 = 2170691) B2170691
theorem B1447193 : Blo 964590 1447193 := bstep (se 2 (by rfl) ⟨542697, by rfl⟩ : syracuseStep 1447193 = 1085395) B1085395
theorem B1086763 : Blo 964590 1086763 := bstep (se 1 (by rfl) ⟨815072, by rfl⟩ : syracuseStep 1086763 = 1630145) B1630145
theorem B1447307 : Blo 964590 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B1447319 : Blo 964590 1447319 := bstep (se 1 (by rfl) ⟨1085489, by rfl⟩ : syracuseStep 1447319 = 2170979) B2170979
theorem B1086871 : Blo 964590 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B3478963 : Blo 964590 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1447385 : Blo 964590 1447385 := bstep (se 2 (by rfl) ⟨542769, by rfl⟩ : syracuseStep 1447385 = 1085539) B1085539
theorem B4888025 : Blo 964590 4888025 := bstep (se 2 (by rfl) ⟨1833009, by rfl⟩ : syracuseStep 4888025 = 3666019) B3666019
theorem B1742401 : Blo 964590 1742401 := bstep (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) B1306801
theorem B1447499 : Blo 964590 1447499 := bstep (se 1 (by rfl) ⟨1085624, by rfl⟩ : syracuseStep 1447499 = 2171249) B2171249
theorem B1087051 : Blo 964590 1087051 := bstep (se 1 (by rfl) ⟨815288, by rfl⟩ : syracuseStep 1087051 = 1630577) B1630577
theorem B1447511 : Blo 964590 1447511 := bstep (se 1 (by rfl) ⟨1085633, by rfl⟩ : syracuseStep 1447511 = 2171267) B2171267
theorem B8492645 : Blo 964590 8492645 := bstep (se 4 (by rfl) ⟨796185, by rfl⟩ : syracuseStep 8492645 = 1592371) B1592371
theorem B1447577 : Blo 964590 1447577 := bstep (se 2 (by rfl) ⟨542841, by rfl⟩ : syracuseStep 1447577 = 1085683) B1085683
theorem B1087159 : Blo 964590 1087159 := bstep (se 1 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 1087159 = 1630739) B1630739
theorem B1447691 : Blo 964590 1447691 := bstep (se 1 (by rfl) ⟨1085768, by rfl⟩ : syracuseStep 1447691 = 2171537) B2171537
theorem B1447703 : Blo 964590 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B2758465 : Blo 964590 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B1447769 : Blo 964590 1447769 := bstep (se 2 (by rfl) ⟨542913, by rfl⟩ : syracuseStep 1447769 = 1085827) B1085827
theorem B1087339 : Blo 964590 1087339 := bstep (se 1 (by rfl) ⟨815504, by rfl⟩ : syracuseStep 1087339 = 1631009) B1631009
theorem B1447883 : Blo 964590 1447883 := bstep (se 1 (by rfl) ⟨1085912, by rfl⟩ : syracuseStep 1447883 = 2171825) B2171825
theorem B1447895 : Blo 964590 1447895 := bstep (se 1 (by rfl) ⟨1085921, by rfl⟩ : syracuseStep 1447895 = 2171843) B2171843
theorem B1087447 : Blo 964590 1087447 := bstep (se 1 (by rfl) ⟨815585, by rfl⟩ : syracuseStep 1087447 = 1631171) B1631171
theorem B1447961 : Blo 964590 1447961 := bstep (se 2 (by rfl) ⟨542985, by rfl⟩ : syracuseStep 1447961 = 1085971) B1085971
theorem B3676211 : Blo 964590 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B3676225 : Blo 964590 3676225 := bstep (se 2 (by rfl) ⟨1378584, by rfl⟩ : syracuseStep 3676225 = 2757169) B2757169
theorem B11737219 : Blo 964590 11737219 := bstep (se 1 (by rfl) ⟨8802914, by rfl⟩ : syracuseStep 11737219 = 17605829) B17605829
theorem B1448075 : Blo 964590 1448075 := bstep (se 1 (by rfl) ⟨1086056, by rfl⟩ : syracuseStep 1448075 = 2172113) B2172113
theorem B1087627 : Blo 964590 1087627 := bstep (se 1 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 1087627 = 1631441) B1631441
theorem B1448087 : Blo 964590 1448087 := bstep (se 1 (by rfl) ⟨1086065, by rfl⟩ : syracuseStep 1448087 = 2172131) B2172131
theorem B1448153 : Blo 964590 1448153 := bstep (se 2 (by rfl) ⟨543057, by rfl⟩ : syracuseStep 1448153 = 1086115) B1086115
theorem B1087735 : Blo 964590 1087735 := bstep (se 1 (by rfl) ⟨815801, by rfl⟩ : syracuseStep 1087735 = 1631603) B1631603
theorem B2201879 : Blo 964590 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1448267 : Blo 964590 1448267 := bstep (se 1 (by rfl) ⟨1086200, by rfl⟩ : syracuseStep 1448267 = 2172401) B2172401
theorem B1448279 : Blo 964590 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B1448345 : Blo 964590 1448345 := bstep (se 2 (by rfl) ⟨543129, by rfl⟩ : syracuseStep 1448345 = 1086259) B1086259
theorem B1087915 : Blo 964590 1087915 := bstep (se 1 (by rfl) ⟨815936, by rfl⟩ : syracuseStep 1087915 = 1631873) B1631873
theorem B8952241 : Blo 964590 8952241 := bstep (se 2 (by rfl) ⟨3357090, by rfl⟩ : syracuseStep 8952241 = 6714181) B6714181
theorem B1448459 : Blo 964590 1448459 := bstep (se 1 (by rfl) ⟨1086344, by rfl⟩ : syracuseStep 1448459 = 2172689) B2172689
theorem B1448471 : Blo 964590 1448471 := bstep (se 1 (by rfl) ⟨1086353, by rfl⟩ : syracuseStep 1448471 = 2172707) B2172707
theorem B1088023 : Blo 964590 1088023 := bstep (se 1 (by rfl) ⟨816017, by rfl⟩ : syracuseStep 1088023 = 1632035) B1632035
theorem B1448537 : Blo 964590 1448537 := bstep (se 2 (by rfl) ⟨543201, by rfl⟩ : syracuseStep 1448537 = 1086403) B1086403
theorem B1448651 : Blo 964590 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B1088203 : Blo 964590 1088203 := bstep (se 1 (by rfl) ⟨816152, by rfl⟩ : syracuseStep 1088203 = 1632305) B1632305
theorem B1448663 : Blo 964590 1448663 := bstep (se 1 (by rfl) ⟨1086497, by rfl⟩ : syracuseStep 1448663 = 2172995) B2172995
theorem B1448729 : Blo 964590 1448729 := bstep (se 2 (by rfl) ⟨543273, by rfl⟩ : syracuseStep 1448729 = 1086547) B1086547
theorem B1088311 : Blo 964590 1088311 := bstep (se 1 (by rfl) ⟨816233, by rfl⟩ : syracuseStep 1088311 = 1632467) B1632467
theorem B1448843 : Blo 964590 1448843 := bstep (se 1 (by rfl) ⟨1086632, by rfl⟩ : syracuseStep 1448843 = 2173265) B2173265
theorem B1448855 : Blo 964590 1448855 := bstep (se 1 (by rfl) ⟨1086641, by rfl⟩ : syracuseStep 1448855 = 2173283) B2173283
theorem B2202571 : Blo 964590 2202571 := bstep (se 1 (by rfl) ⟨1651928, by rfl⟩ : syracuseStep 2202571 = 3303857) B3303857
theorem B1448921 : Blo 964590 1448921 := bstep (se 2 (by rfl) ⟨543345, by rfl⟩ : syracuseStep 1448921 = 1086691) B1086691
theorem B1088491 : Blo 964590 1088491 := bstep (se 1 (by rfl) ⟨816368, by rfl⟩ : syracuseStep 1088491 = 1632737) B1632737
theorem B4889645 : Blo 964590 4889645 := bstep (se 3 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 4889645 = 1833617) B1833617
theorem B1743923 : Blo 964590 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1449035 : Blo 964590 1449035 := bstep (se 1 (by rfl) ⟨1086776, by rfl⟩ : syracuseStep 1449035 = 2173553) B2173553
theorem B1449047 : Blo 964590 1449047 := bstep (se 1 (by rfl) ⟨1086785, by rfl⟩ : syracuseStep 1449047 = 2173571) B2173571
theorem B1088599 : Blo 964590 1088599 := bstep (se 1 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 1088599 = 1632899) B1632899
theorem B1547417 : Blo 964590 1547417 := bstep (se 2 (by rfl) ⟨580281, by rfl⟩ : syracuseStep 1547417 = 1160563) B1160563
theorem B1449113 : Blo 964590 1449113 := bstep (se 2 (by rfl) ⟨543417, by rfl⟩ : syracuseStep 1449113 = 1086835) B1086835
theorem B1449227 : Blo 964590 1449227 := bstep (se 1 (by rfl) ⟨1086920, by rfl⟩ : syracuseStep 1449227 = 2173841) B2173841
theorem B1088779 : Blo 964590 1088779 := bstep (se 1 (by rfl) ⟨816584, by rfl⟩ : syracuseStep 1088779 = 1633169) B1633169
theorem B1449239 : Blo 964590 1449239 := bstep (se 1 (by rfl) ⟨1086929, by rfl⟩ : syracuseStep 1449239 = 2173859) B2173859
theorem B1449305 : Blo 964590 1449305 := bstep (se 2 (by rfl) ⟨543489, by rfl⟩ : syracuseStep 1449305 = 1086979) B1086979
theorem B4136285 : Blo 964590 4136285 := bstep (se 3 (by rfl) ⟨775553, by rfl⟩ : syracuseStep 4136285 = 1551107) B1551107
theorem B1088887 : Blo 964590 1088887 := bstep (se 1 (by rfl) ⟨816665, by rfl⟩ : syracuseStep 1088887 = 1633331) B1633331
theorem B1449419 : Blo 964590 1449419 := bstep (se 1 (by rfl) ⟨1087064, by rfl⟩ : syracuseStep 1449419 = 2174129) B2174129
theorem B1449431 : Blo 964590 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B1449497 : Blo 964590 1449497 := bstep (se 2 (by rfl) ⟨543561, by rfl⟩ : syracuseStep 1449497 = 1087123) B1087123
theorem B1089067 : Blo 964590 1089067 := bstep (se 1 (by rfl) ⟨816800, by rfl⟩ : syracuseStep 1089067 = 1633601) B1633601
theorem B2170457 : Blo 964590 2170457 := bstep (se 2 (by rfl) ⟨813921, by rfl⟩ : syracuseStep 2170457 = 1627843) B1627843
theorem B1449611 : Blo 964590 1449611 := bstep (se 1 (by rfl) ⟨1087208, by rfl⟩ : syracuseStep 1449611 = 2174417) B2174417
theorem B1449623 : Blo 964590 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B1089175 : Blo 964590 1089175 := bstep (se 1 (by rfl) ⟨816881, by rfl⟩ : syracuseStep 1089175 = 1633763) B1633763
theorem B2170547 : Blo 964590 2170547 := bstep (se 1 (by rfl) ⟨1627910, by rfl⟩ : syracuseStep 2170547 = 3255821) B3255821
theorem B2170583 : Blo 964590 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B1449689 : Blo 964590 1449689 := bstep (se 2 (by rfl) ⟨543633, by rfl⟩ : syracuseStep 1449689 = 1087267) B1087267
theorem B6627089 : Blo 964590 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B1449803 : Blo 964590 1449803 := bstep (se 1 (by rfl) ⟨1087352, by rfl⟩ : syracuseStep 1449803 = 2174705) B2174705
theorem B1089355 : Blo 964590 1089355 := bstep (se 1 (by rfl) ⟨817016, by rfl⟩ : syracuseStep 1089355 = 1634033) B1634033
theorem B1449815 : Blo 964590 1449815 := bstep (se 1 (by rfl) ⟨1087361, by rfl⟩ : syracuseStep 1449815 = 2174723) B2174723
theorem B5218141 : Blo 964590 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B2170763 : Blo 964590 2170763 := bstep (se 1 (by rfl) ⟨1628072, by rfl⟩ : syracuseStep 2170763 = 3256145) B3256145
theorem B1449881 : Blo 964590 1449881 := bstep (se 2 (by rfl) ⟨543705, by rfl⟩ : syracuseStep 1449881 = 1087411) B1087411
theorem B1089463 : Blo 964590 1089463 := bstep (se 1 (by rfl) ⟨817097, by rfl⟩ : syracuseStep 1089463 = 1634195) B1634195
theorem B2170817 : Blo 964590 2170817 := bstep (se 2 (by rfl) ⟨814056, by rfl⟩ : syracuseStep 2170817 = 1628113) B1628113
theorem B1449995 : Blo 964590 1449995 := bstep (se 1 (by rfl) ⟨1087496, by rfl⟩ : syracuseStep 1449995 = 2174993) B2174993
theorem B1450007 : Blo 964590 1450007 := bstep (se 1 (by rfl) ⟨1087505, by rfl⟩ : syracuseStep 1450007 = 2175011) B2175011
theorem B4464715 : Blo 964590 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5513291 : Blo 964590 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B1450073 : Blo 964590 1450073 := bstep (se 2 (by rfl) ⟨543777, by rfl⟩ : syracuseStep 1450073 = 1087555) B1087555
theorem B1089643 : Blo 964590 1089643 := bstep (se 1 (by rfl) ⟨817232, by rfl⟩ : syracuseStep 1089643 = 1634465) B1634465
theorem B5873795 : Blo 964590 5873795 := bstep (se 1 (by rfl) ⟨4405346, by rfl⟩ : syracuseStep 5873795 = 8810693) B8810693
theorem B2171033 : Blo 964590 2171033 := bstep (se 2 (by rfl) ⟨814137, by rfl⟩ : syracuseStep 2171033 = 1628275) B1628275
theorem B1450187 : Blo 964590 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B1450199 : Blo 964590 1450199 := bstep (se 1 (by rfl) ⟨1087649, by rfl⟩ : syracuseStep 1450199 = 2175299) B2175299
theorem B2171123 : Blo 964590 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B2171159 : Blo 964590 2171159 := bstep (se 1 (by rfl) ⟨1628369, by rfl⟩ : syracuseStep 2171159 = 3256739) B3256739
theorem B1450265 : Blo 964590 1450265 := bstep (se 2 (by rfl) ⟨543849, by rfl⟩ : syracuseStep 1450265 = 1087699) B1087699
theorem B5218661 : Blo 964590 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B1450379 : Blo 964590 1450379 := bstep (se 1 (by rfl) ⟨1087784, by rfl⟩ : syracuseStep 1450379 = 2175569) B2175569
theorem B1450391 : Blo 964590 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B2171339 : Blo 964590 2171339 := bstep (se 1 (by rfl) ⟨1628504, by rfl⟩ : syracuseStep 2171339 = 3257009) B3257009
theorem B1450457 : Blo 964590 1450457 := bstep (se 2 (by rfl) ⟨543921, by rfl⟩ : syracuseStep 1450457 = 1087843) B1087843
theorem B2171393 : Blo 964590 2171393 := bstep (se 2 (by rfl) ⟨814272, by rfl⟩ : syracuseStep 2171393 = 1628545) B1628545
theorem B1450571 : Blo 964590 1450571 := bstep (se 1 (by rfl) ⟨1087928, by rfl⟩ : syracuseStep 1450571 = 2175857) B2175857
theorem B1450583 : Blo 964590 1450583 := bstep (se 1 (by rfl) ⟨1087937, by rfl⟩ : syracuseStep 1450583 = 2175875) B2175875
theorem B1450649 : Blo 964590 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B2171609 : Blo 964590 2171609 := bstep (se 2 (by rfl) ⟨814353, by rfl⟩ : syracuseStep 2171609 = 1628707) B1628707
theorem B1450763 : Blo 964590 1450763 := bstep (se 1 (by rfl) ⟨1088072, by rfl⟩ : syracuseStep 1450763 = 2176145) B2176145
theorem B1450775 : Blo 964590 1450775 := bstep (se 1 (by rfl) ⟨1088081, by rfl⟩ : syracuseStep 1450775 = 2176163) B2176163
theorem B2171699 : Blo 964590 2171699 := bstep (se 1 (by rfl) ⟨1628774, by rfl⟩ : syracuseStep 2171699 = 3257549) B3257549
theorem B7840577 : Blo 964590 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B2171735 : Blo 964590 2171735 := bstep (se 1 (by rfl) ⟨1628801, by rfl⟩ : syracuseStep 2171735 = 3257603) B3257603
theorem B1450841 : Blo 964590 1450841 := bstep (se 2 (by rfl) ⟨544065, by rfl⟩ : syracuseStep 1450841 = 1088131) B1088131
theorem B1450955 : Blo 964590 1450955 := bstep (se 1 (by rfl) ⟨1088216, by rfl⟩ : syracuseStep 1450955 = 2176433) B2176433
theorem B1450967 : Blo 964590 1450967 := bstep (se 1 (by rfl) ⟨1088225, by rfl⟩ : syracuseStep 1450967 = 2176451) B2176451
theorem B2171915 : Blo 964590 2171915 := bstep (se 1 (by rfl) ⟨1628936, by rfl⟩ : syracuseStep 2171915 = 3257873) B3257873
theorem B1451033 : Blo 964590 1451033 := bstep (se 2 (by rfl) ⟨544137, by rfl⟩ : syracuseStep 1451033 = 1088275) B1088275
theorem B2171969 : Blo 964590 2171969 := bstep (se 2 (by rfl) ⟨814488, by rfl⟩ : syracuseStep 2171969 = 1628977) B1628977
theorem B1451147 : Blo 964590 1451147 := bstep (se 1 (by rfl) ⟨1088360, by rfl⟩ : syracuseStep 1451147 = 2176721) B2176721
theorem B1451159 : Blo 964590 1451159 := bstep (se 1 (by rfl) ⟨1088369, by rfl⟩ : syracuseStep 1451159 = 2176739) B2176739
theorem B1451225 : Blo 964590 1451225 := bstep (se 2 (by rfl) ⟨544209, by rfl⟩ : syracuseStep 1451225 = 1088419) B1088419
theorem B2172185 : Blo 964590 2172185 := bstep (se 2 (by rfl) ⟨814569, by rfl⟩ : syracuseStep 2172185 = 1629139) B1629139
theorem B1451339 : Blo 964590 1451339 := bstep (se 1 (by rfl) ⟨1088504, by rfl⟩ : syracuseStep 1451339 = 2177009) B2177009
theorem B1451351 : Blo 964590 1451351 := bstep (se 1 (by rfl) ⟨1088513, by rfl⟩ : syracuseStep 1451351 = 2177027) B2177027
theorem B2172275 : Blo 964590 2172275 := bstep (se 1 (by rfl) ⟨1629206, by rfl⟩ : syracuseStep 2172275 = 3258413) B3258413
theorem B2172311 : Blo 964590 2172311 := bstep (se 1 (by rfl) ⟨1629233, by rfl⟩ : syracuseStep 2172311 = 3258467) B3258467
theorem B1451417 : Blo 964590 1451417 := bstep (se 2 (by rfl) ⟨544281, by rfl⟩ : syracuseStep 1451417 = 1088563) B1088563
theorem B9282995 : Blo 964590 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B8955353 : Blo 964590 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B1451531 : Blo 964590 1451531 := bstep (se 1 (by rfl) ⟨1088648, by rfl⟩ : syracuseStep 1451531 = 2177297) B2177297
theorem B7349777 : Blo 964590 7349777 := bstep (se 2 (by rfl) ⟨2756166, by rfl⟩ : syracuseStep 7349777 = 5512333) B5512333
theorem B1451543 : Blo 964590 1451543 := bstep (se 1 (by rfl) ⟨1088657, by rfl⟩ : syracuseStep 1451543 = 2177315) B2177315
theorem B2172491 : Blo 964590 2172491 := bstep (se 1 (by rfl) ⟨1629368, by rfl⟩ : syracuseStep 2172491 = 3258737) B3258737
theorem B1222219 : Blo 964590 1222219 := bstep (se 1 (by rfl) ⟨916664, by rfl⟩ : syracuseStep 1222219 = 1833329) B1833329
theorem B1451609 : Blo 964590 1451609 := bstep (se 2 (by rfl) ⟨544353, by rfl⟩ : syracuseStep 1451609 = 1088707) B1088707
theorem B2172545 : Blo 964590 2172545 := bstep (se 2 (by rfl) ⟨814704, by rfl⟩ : syracuseStep 2172545 = 1629409) B1629409
theorem B1451723 : Blo 964590 1451723 := bstep (se 1 (by rfl) ⟨1088792, by rfl⟩ : syracuseStep 1451723 = 2177585) B2177585
theorem B1451735 : Blo 964590 1451735 := bstep (se 1 (by rfl) ⟨1088801, by rfl⟩ : syracuseStep 1451735 = 2177603) B2177603
theorem B1451801 : Blo 964590 1451801 := bstep (se 2 (by rfl) ⟨544425, by rfl⟩ : syracuseStep 1451801 = 1088851) B1088851
theorem B2172761 : Blo 964590 2172761 := bstep (se 2 (by rfl) ⟨814785, by rfl⟩ : syracuseStep 2172761 = 1629571) B1629571
theorem B1451915 : Blo 964590 1451915 := bstep (se 1 (by rfl) ⟨1088936, by rfl⟩ : syracuseStep 1451915 = 2177873) B2177873
theorem B1451927 : Blo 964590 1451927 := bstep (se 1 (by rfl) ⟨1088945, by rfl⟩ : syracuseStep 1451927 = 2177891) B2177891
theorem B2172851 : Blo 964590 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B2172887 : Blo 964590 2172887 := bstep (se 1 (by rfl) ⟨1629665, by rfl⟩ : syracuseStep 2172887 = 3259331) B3259331
theorem B1451993 : Blo 964590 1451993 := bstep (se 2 (by rfl) ⟨544497, by rfl⟩ : syracuseStep 1451993 = 1088995) B1088995
theorem B1452107 : Blo 964590 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B1452119 : Blo 964590 1452119 := bstep (se 1 (by rfl) ⟨1089089, by rfl⟩ : syracuseStep 1452119 = 2178179) B2178179
theorem B2173067 : Blo 964590 2173067 := bstep (se 1 (by rfl) ⟨1629800, by rfl⟩ : syracuseStep 2173067 = 3259601) B3259601
theorem B1452185 : Blo 964590 1452185 := bstep (se 2 (by rfl) ⟨544569, by rfl⟩ : syracuseStep 1452185 = 1089139) B1089139
theorem B8267953 : Blo 964590 8267953 := bstep (se 2 (by rfl) ⟨3100482, by rfl⟩ : syracuseStep 8267953 = 6200965) B6200965
theorem B2173121 : Blo 964590 2173121 := bstep (se 2 (by rfl) ⟨814920, by rfl⟩ : syracuseStep 2173121 = 1629841) B1629841
theorem B1452299 : Blo 964590 1452299 := bstep (se 1 (by rfl) ⟨1089224, by rfl⟩ : syracuseStep 1452299 = 2178449) B2178449
theorem B1452311 : Blo 964590 1452311 := bstep (se 1 (by rfl) ⟨1089233, by rfl⟩ : syracuseStep 1452311 = 2178467) B2178467
theorem B1452377 : Blo 964590 1452377 := bstep (se 2 (by rfl) ⟨544641, by rfl⟩ : syracuseStep 1452377 = 1089283) B1089283
theorem B2173337 : Blo 964590 2173337 := bstep (se 2 (by rfl) ⟨815001, by rfl⟩ : syracuseStep 2173337 = 1630003) B1630003
theorem B993739 : Blo 964590 993739 := bstep (se 1 (by rfl) ⟨745304, by rfl⟩ : syracuseStep 993739 = 1490609) B1490609
theorem B1452491 : Blo 964590 1452491 := bstep (se 1 (by rfl) ⟨1089368, by rfl⟩ : syracuseStep 1452491 = 2178737) B2178737
theorem B1452503 : Blo 964590 1452503 := bstep (se 1 (by rfl) ⟨1089377, by rfl⟩ : syracuseStep 1452503 = 2178755) B2178755
theorem B2173427 : Blo 964590 2173427 := bstep (se 1 (by rfl) ⟨1630070, by rfl⟩ : syracuseStep 2173427 = 3260141) B3260141
theorem B2173463 : Blo 964590 2173463 := bstep (se 1 (by rfl) ⟨1630097, by rfl⟩ : syracuseStep 2173463 = 3260195) B3260195
theorem B1223191 : Blo 964590 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B1452569 : Blo 964590 1452569 := bstep (se 2 (by rfl) ⟨544713, by rfl⟩ : syracuseStep 1452569 = 1089427) B1089427
theorem B3484225 : Blo 964590 3484225 := bstep (se 2 (by rfl) ⟨1306584, by rfl⟩ : syracuseStep 3484225 = 2613169) B2613169
theorem B1452683 : Blo 964590 1452683 := bstep (se 1 (by rfl) ⟨1089512, by rfl⟩ : syracuseStep 1452683 = 2179025) B2179025
theorem B1452695 : Blo 964590 1452695 := bstep (se 1 (by rfl) ⟨1089521, by rfl⟩ : syracuseStep 1452695 = 2179043) B2179043
theorem B2173643 : Blo 964590 2173643 := bstep (se 1 (by rfl) ⟨1630232, by rfl⟩ : syracuseStep 2173643 = 3260465) B3260465
theorem B1452761 : Blo 964590 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B2173697 : Blo 964590 2173697 := bstep (se 2 (by rfl) ⟨815136, by rfl⟩ : syracuseStep 2173697 = 1630273) B1630273
theorem B1452875 : Blo 964590 1452875 := bstep (se 1 (by rfl) ⟨1089656, by rfl⟩ : syracuseStep 1452875 = 2179313) B2179313
theorem B4893533 : Blo 964590 4893533 := bstep (se 3 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 4893533 = 1835075) B1835075
theorem B2206615 : Blo 964590 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B2173913 : Blo 964590 2173913 := bstep (se 2 (by rfl) ⟨815217, by rfl⟩ : syracuseStep 2173913 = 1630435) B1630435
theorem B1551383 : Blo 964590 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B2174003 : Blo 964590 2174003 := bstep (se 1 (by rfl) ⟨1630502, by rfl⟩ : syracuseStep 2174003 = 3261005) B3261005
theorem B2174039 : Blo 964590 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B2174219 : Blo 964590 2174219 := bstep (se 1 (by rfl) ⟨1630664, by rfl⟩ : syracuseStep 2174219 = 3261329) B3261329
theorem B2174273 : Blo 964590 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B1224011 : Blo 964590 1224011 := bstep (se 1 (by rfl) ⟨918008, by rfl⟩ : syracuseStep 1224011 = 1836017) B1836017
theorem B2207051 : Blo 964590 2207051 := bstep (se 1 (by rfl) ⟨1655288, by rfl⟩ : syracuseStep 2207051 = 3310577) B3310577
theorem B2174489 : Blo 964590 2174489 := bstep (se 2 (by rfl) ⟨815433, by rfl⟩ : syracuseStep 2174489 = 1630867) B1630867
theorem B4959809 : Blo 964590 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B2174579 : Blo 964590 2174579 := bstep (se 1 (by rfl) ⟨1630934, by rfl⟩ : syracuseStep 2174579 = 3261869) B3261869
theorem B2174615 : Blo 964590 2174615 := bstep (se 1 (by rfl) ⟨1630961, by rfl⟩ : syracuseStep 2174615 = 3261923) B3261923
theorem B1158871 : Blo 964590 1158871 := bstep (se 1 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 1158871 = 1738307) B1738307
theorem B2174795 : Blo 964590 2174795 := bstep (se 1 (by rfl) ⟨1631096, by rfl⟩ : syracuseStep 2174795 = 3262193) B3262193
theorem B2174849 : Blo 964590 2174849 := bstep (se 2 (by rfl) ⟨815568, by rfl⟩ : syracuseStep 2174849 = 1631137) B1631137
theorem B1224715 : Blo 964590 1224715 := bstep (se 1 (by rfl) ⟨918536, by rfl⟩ : syracuseStep 1224715 = 1837073) B1837073
theorem B2175065 : Blo 964590 2175065 := bstep (se 2 (by rfl) ⟨815649, by rfl⟩ : syracuseStep 2175065 = 1631299) B1631299
theorem B5222551 : Blo 964590 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B2175155 : Blo 964590 2175155 := bstep (se 1 (by rfl) ⟨1631366, by rfl⟩ : syracuseStep 2175155 = 3262733) B3262733
theorem B3256523 : Blo 964590 3256523 := bstep (se 1 (by rfl) ⟨2442392, by rfl⟩ : syracuseStep 3256523 = 4884785) B4884785
theorem B2175191 : Blo 964590 2175191 := bstep (se 1 (by rfl) ⟨1631393, by rfl⟩ : syracuseStep 2175191 = 3262787) B3262787
theorem B1224983 : Blo 964590 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B20918573 : Blo 964590 20918573 := bstep (se 3 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 20918573 = 7844465) B7844465
theorem B2175371 : Blo 964590 2175371 := bstep (se 1 (by rfl) ⟨1631528, by rfl⟩ : syracuseStep 2175371 = 3263057) B3263057
theorem B2175425 : Blo 964590 2175425 := bstep (se 2 (by rfl) ⟨815784, by rfl⟩ : syracuseStep 2175425 = 1631569) B1631569
theorem B3256793 : Blo 964590 3256793 := bstep (se 2 (by rfl) ⟨1221297, by rfl⟩ : syracuseStep 3256793 = 2442595) B2442595
theorem B4698755 : Blo 964590 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B2175641 : Blo 964590 2175641 := bstep (se 2 (by rfl) ⟨815865, by rfl⟩ : syracuseStep 2175641 = 1631731) B1631731
theorem B2175731 : Blo 964590 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B2175767 : Blo 964590 2175767 := bstep (se 1 (by rfl) ⟨1631825, by rfl⟩ : syracuseStep 2175767 = 3263651) B3263651
theorem B3715915 : Blo 964590 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B4895639 : Blo 964590 4895639 := bstep (se 1 (by rfl) ⟨3671729, by rfl⟩ : syracuseStep 4895639 = 7343459) B7343459
theorem B2175947 : Blo 964590 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1225687 : Blo 964590 1225687 := bstep (se 1 (by rfl) ⟨919265, by rfl⟩ : syracuseStep 1225687 = 1838531) B1838531
theorem B2176001 : Blo 964590 2176001 := bstep (se 2 (by rfl) ⟨816000, by rfl⟩ : syracuseStep 2176001 = 1632001) B1632001
theorem B3912749 : Blo 964590 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B3257495 : Blo 964590 3257495 := bstep (se 1 (by rfl) ⟨2443121, by rfl⟩ : syracuseStep 3257495 = 4886243) B4886243
theorem B1651915 : Blo 964590 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B2176217 : Blo 964590 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B2176307 : Blo 964590 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B7353665 : Blo 964590 7353665 := bstep (se 2 (by rfl) ⟨2757624, by rfl⟩ : syracuseStep 7353665 = 5515249) B5515249
theorem B2176343 : Blo 964590 2176343 := bstep (se 1 (by rfl) ⟨1632257, by rfl⟩ : syracuseStep 2176343 = 3264515) B3264515
theorem B3487121 : Blo 964590 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B1160663 : Blo 964590 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B2176523 : Blo 964590 2176523 := bstep (se 1 (by rfl) ⟨1632392, by rfl⟩ : syracuseStep 2176523 = 3264785) B3264785
theorem B2176577 : Blo 964590 2176577 := bstep (se 2 (by rfl) ⟨816216, by rfl⟩ : syracuseStep 2176577 = 1632433) B1632433
theorem B3258035 : Blo 964590 3258035 := bstep (se 1 (by rfl) ⟨2443526, by rfl⟩ : syracuseStep 3258035 = 4887053) B4887053
theorem B3978973 : Blo 964590 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B1652503 : Blo 964590 1652503 := bstep (se 1 (by rfl) ⟨1239377, by rfl⟩ : syracuseStep 1652503 = 2478755) B2478755
theorem B2176793 : Blo 964590 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B2176883 : Blo 964590 2176883 := bstep (se 1 (by rfl) ⟨1632662, by rfl⟩ : syracuseStep 2176883 = 3265325) B3265325
theorem B2176919 : Blo 964590 2176919 := bstep (se 1 (by rfl) ⟨1632689, by rfl⟩ : syracuseStep 2176919 = 3265379) B3265379
theorem B3258305 : Blo 964590 3258305 := bstep (se 2 (by rfl) ⟨1221864, by rfl⟩ : syracuseStep 3258305 = 2443729) B2443729
theorem B3356633 : Blo 964590 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B964599 : Blo 964590 964599 := bstep (se 1 (by rfl) ⟨723449, by rfl⟩ : syracuseStep 964599 = 1446899) B1446899
theorem B964619 : Blo 964590 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B964631 : Blo 964590 964631 := bstep (se 1 (by rfl) ⟨723473, by rfl⟩ : syracuseStep 964631 = 1446947) B1446947
theorem B964651 : Blo 964590 964651 := bstep (se 1 (by rfl) ⟨723488, by rfl⟩ : syracuseStep 964651 = 1446977) B1446977
theorem B964663 : Blo 964590 964663 := bstep (se 1 (by rfl) ⟨723497, by rfl⟩ : syracuseStep 964663 = 1446995) B1446995
theorem B964683 : Blo 964590 964683 := bstep (se 1 (by rfl) ⟨723512, by rfl⟩ : syracuseStep 964683 = 1447025) B1447025
theorem B2177099 : Blo 964590 2177099 := bstep (se 1 (by rfl) ⟨1632824, by rfl⟩ : syracuseStep 2177099 = 3265649) B3265649
theorem B964695 : Blo 964590 964695 := bstep (se 1 (by rfl) ⟨723521, by rfl⟩ : syracuseStep 964695 = 1447043) B1447043
theorem B964715 : Blo 964590 964715 := bstep (se 1 (by rfl) ⟨723536, by rfl⟩ : syracuseStep 964715 = 1447073) B1447073
theorem B964727 : Blo 964590 964727 := bstep (se 1 (by rfl) ⟨723545, by rfl⟩ : syracuseStep 964727 = 1447091) B1447091
theorem B2177153 : Blo 964590 2177153 := bstep (se 2 (by rfl) ⟨816432, by rfl⟩ : syracuseStep 2177153 = 1632865) B1632865
theorem B964747 : Blo 964590 964747 := bstep (se 1 (by rfl) ⟨723560, by rfl⟩ : syracuseStep 964747 = 1447121) B1447121
theorem B964759 : Blo 964590 964759 := bstep (se 1 (by rfl) ⟨723569, by rfl⟩ : syracuseStep 964759 = 1447139) B1447139
theorem B964779 : Blo 964590 964779 := bstep (se 1 (by rfl) ⟨723584, by rfl⟩ : syracuseStep 964779 = 1447169) B1447169
theorem B964791 : Blo 964590 964791 := bstep (se 1 (by rfl) ⟨723593, by rfl⟩ : syracuseStep 964791 = 1447187) B1447187
theorem B964811 : Blo 964590 964811 := bstep (se 1 (by rfl) ⟨723608, by rfl⟩ : syracuseStep 964811 = 1447217) B1447217
theorem B964823 : Blo 964590 964823 := bstep (se 1 (by rfl) ⟨723617, by rfl⟩ : syracuseStep 964823 = 1447235) B1447235
theorem B964843 : Blo 964590 964843 := bstep (se 1 (by rfl) ⟨723632, by rfl⟩ : syracuseStep 964843 = 1447265) B1447265
theorem B964855 : Blo 964590 964855 := bstep (se 1 (by rfl) ⟨723641, by rfl⟩ : syracuseStep 964855 = 1447283) B1447283
theorem B964875 : Blo 964590 964875 := bstep (se 1 (by rfl) ⟨723656, by rfl⟩ : syracuseStep 964875 = 1447313) B1447313
theorem B964887 : Blo 964590 964887 := bstep (se 1 (by rfl) ⟨723665, by rfl⟩ : syracuseStep 964887 = 1447331) B1447331
theorem B964907 : Blo 964590 964907 := bstep (se 1 (by rfl) ⟨723680, by rfl⟩ : syracuseStep 964907 = 1447361) B1447361
theorem B964919 : Blo 964590 964919 := bstep (se 1 (by rfl) ⟨723689, by rfl⟩ : syracuseStep 964919 = 1447379) B1447379
theorem B964939 : Blo 964590 964939 := bstep (se 1 (by rfl) ⟨723704, by rfl⟩ : syracuseStep 964939 = 1447409) B1447409
theorem B964951 : Blo 964590 964951 := bstep (se 1 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 964951 = 1447427) B1447427
theorem B1030487 : Blo 964590 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B2177369 : Blo 964590 2177369 := bstep (se 2 (by rfl) ⟨816513, by rfl⟩ : syracuseStep 2177369 = 1633027) B1633027
theorem B964971 : Blo 964590 964971 := bstep (se 1 (by rfl) ⟨723728, by rfl⟩ : syracuseStep 964971 = 1447457) B1447457
theorem B964983 : Blo 964590 964983 := bstep (se 1 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 964983 = 1447475) B1447475
theorem B965003 : Blo 964590 965003 := bstep (se 1 (by rfl) ⟨723752, by rfl⟩ : syracuseStep 965003 = 1447505) B1447505
theorem B965015 : Blo 964590 965015 := bstep (se 1 (by rfl) ⟨723761, by rfl⟩ : syracuseStep 965015 = 1447523) B1447523
theorem B965035 : Blo 964590 965035 := bstep (se 1 (by rfl) ⟨723776, by rfl⟩ : syracuseStep 965035 = 1447553) B1447553
theorem B2177459 : Blo 964590 2177459 := bstep (se 1 (by rfl) ⟨1633094, by rfl⟩ : syracuseStep 2177459 = 3266189) B3266189
theorem B965047 : Blo 964590 965047 := bstep (se 1 (by rfl) ⟨723785, by rfl⟩ : syracuseStep 965047 = 1447571) B1447571
theorem B965067 : Blo 964590 965067 := bstep (se 1 (by rfl) ⟨723800, by rfl⟩ : syracuseStep 965067 = 1447601) B1447601
theorem B965079 : Blo 964590 965079 := bstep (se 1 (by rfl) ⟨723809, by rfl⟩ : syracuseStep 965079 = 1447619) B1447619
theorem B2177495 : Blo 964590 2177495 := bstep (se 1 (by rfl) ⟨1633121, by rfl⟩ : syracuseStep 2177495 = 3266243) B3266243
theorem B3258845 : Blo 964590 3258845 := bstep (se 3 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 3258845 = 1222067) B1222067
theorem B965099 : Blo 964590 965099 := bstep (se 1 (by rfl) ⟨723824, by rfl⟩ : syracuseStep 965099 = 1447649) B1447649
theorem B965111 : Blo 964590 965111 := bstep (se 1 (by rfl) ⟨723833, by rfl⟩ : syracuseStep 965111 = 1447667) B1447667
theorem B965131 : Blo 964590 965131 := bstep (se 1 (by rfl) ⟨723848, by rfl⟩ : syracuseStep 965131 = 1447697) B1447697
theorem B965143 : Blo 964590 965143 := bstep (se 1 (by rfl) ⟨723857, by rfl⟩ : syracuseStep 965143 = 1447715) B1447715
theorem B965163 : Blo 964590 965163 := bstep (se 1 (by rfl) ⟨723872, by rfl⟩ : syracuseStep 965163 = 1447745) B1447745
theorem B965175 : Blo 964590 965175 := bstep (se 1 (by rfl) ⟨723881, by rfl⟩ : syracuseStep 965175 = 1447763) B1447763
theorem B965195 : Blo 964590 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B7060043 : Blo 964590 7060043 := bstep (se 1 (by rfl) ⟨5295032, by rfl⟩ : syracuseStep 7060043 = 10590065) B10590065
theorem B965207 : Blo 964590 965207 := bstep (se 1 (by rfl) ⟨723905, by rfl⟩ : syracuseStep 965207 = 1447811) B1447811
theorem B965227 : Blo 964590 965227 := bstep (se 1 (by rfl) ⟨723920, by rfl⟩ : syracuseStep 965227 = 1447841) B1447841
theorem B965239 : Blo 964590 965239 := bstep (se 1 (by rfl) ⟨723929, by rfl⟩ : syracuseStep 965239 = 1447859) B1447859
theorem B965259 : Blo 964590 965259 := bstep (se 1 (by rfl) ⟨723944, by rfl⟩ : syracuseStep 965259 = 1447889) B1447889
theorem B2177675 : Blo 964590 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B965271 : Blo 964590 965271 := bstep (se 1 (by rfl) ⟨723953, by rfl⟩ : syracuseStep 965271 = 1447907) B1447907
theorem B965291 : Blo 964590 965291 := bstep (se 1 (by rfl) ⟨723968, by rfl⟩ : syracuseStep 965291 = 1447937) B1447937
theorem B965303 : Blo 964590 965303 := bstep (se 1 (by rfl) ⟨723977, by rfl⟩ : syracuseStep 965303 = 1447955) B1447955
theorem B2177729 : Blo 964590 2177729 := bstep (se 2 (by rfl) ⟨816648, by rfl⟩ : syracuseStep 2177729 = 1633297) B1633297
theorem B965323 : Blo 964590 965323 := bstep (se 1 (by rfl) ⟨723992, by rfl⟩ : syracuseStep 965323 = 1447985) B1447985
theorem B3095243 : Blo 964590 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B965335 : Blo 964590 965335 := bstep (se 1 (by rfl) ⟨724001, by rfl⟩ : syracuseStep 965335 = 1448003) B1448003
theorem B8272601 : Blo 964590 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B965355 : Blo 964590 965355 := bstep (se 1 (by rfl) ⟨724016, by rfl⟩ : syracuseStep 965355 = 1448033) B1448033
theorem B965367 : Blo 964590 965367 := bstep (se 1 (by rfl) ⟨724025, by rfl⟩ : syracuseStep 965367 = 1448051) B1448051
theorem B965387 : Blo 964590 965387 := bstep (se 1 (by rfl) ⟨724040, by rfl⟩ : syracuseStep 965387 = 1448081) B1448081
theorem B965399 : Blo 964590 965399 := bstep (se 1 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 965399 = 1448099) B1448099
theorem B965419 : Blo 964590 965419 := bstep (se 1 (by rfl) ⟨724064, by rfl⟩ : syracuseStep 965419 = 1448129) B1448129
theorem B965431 : Blo 964590 965431 := bstep (se 1 (by rfl) ⟨724073, by rfl⟩ : syracuseStep 965431 = 1448147) B1448147
theorem B965451 : Blo 964590 965451 := bstep (se 1 (by rfl) ⟨724088, by rfl⟩ : syracuseStep 965451 = 1448177) B1448177
theorem B965463 : Blo 964590 965463 := bstep (se 1 (by rfl) ⟨724097, by rfl⟩ : syracuseStep 965463 = 1448195) B1448195
theorem B965483 : Blo 964590 965483 := bstep (se 1 (by rfl) ⟨724112, by rfl⟩ : syracuseStep 965483 = 1448225) B1448225
theorem B965495 : Blo 964590 965495 := bstep (se 1 (by rfl) ⟨724121, by rfl⟩ : syracuseStep 965495 = 1448243) B1448243
theorem B965515 : Blo 964590 965515 := bstep (se 1 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 965515 = 1448273) B1448273
theorem B965527 : Blo 964590 965527 := bstep (se 1 (by rfl) ⟨724145, by rfl⟩ : syracuseStep 965527 = 1448291) B1448291
theorem B2177945 : Blo 964590 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B965547 : Blo 964590 965547 := bstep (se 1 (by rfl) ⟨724160, by rfl⟩ : syracuseStep 965547 = 1448321) B1448321
theorem B965559 : Blo 964590 965559 := bstep (se 1 (by rfl) ⟨724169, by rfl⟩ : syracuseStep 965559 = 1448339) B1448339
theorem B965579 : Blo 964590 965579 := bstep (se 1 (by rfl) ⟨724184, by rfl⟩ : syracuseStep 965579 = 1448369) B1448369
theorem B965591 : Blo 964590 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B965611 : Blo 964590 965611 := bstep (se 1 (by rfl) ⟨724208, by rfl⟩ : syracuseStep 965611 = 1448417) B1448417
theorem B2178035 : Blo 964590 2178035 := bstep (se 1 (by rfl) ⟨1633526, by rfl⟩ : syracuseStep 2178035 = 3267053) B3267053
theorem B965623 : Blo 964590 965623 := bstep (se 1 (by rfl) ⟨724217, by rfl⟩ : syracuseStep 965623 = 1448435) B1448435
theorem B965643 : Blo 964590 965643 := bstep (se 1 (by rfl) ⟨724232, by rfl⟩ : syracuseStep 965643 = 1448465) B1448465
theorem B965655 : Blo 964590 965655 := bstep (se 1 (by rfl) ⟨724241, by rfl⟩ : syracuseStep 965655 = 1448483) B1448483
theorem B2178071 : Blo 964590 2178071 := bstep (se 1 (by rfl) ⟨1633553, by rfl⟩ : syracuseStep 2178071 = 3267107) B3267107
theorem B965675 : Blo 964590 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B965687 : Blo 964590 965687 := bstep (se 1 (by rfl) ⟨724265, by rfl⟩ : syracuseStep 965687 = 1448531) B1448531
theorem B965707 : Blo 964590 965707 := bstep (se 1 (by rfl) ⟨724280, by rfl⟩ : syracuseStep 965707 = 1448561) B1448561
theorem B965719 : Blo 964590 965719 := bstep (se 1 (by rfl) ⟨724289, by rfl⟩ : syracuseStep 965719 = 1448579) B1448579
theorem B965739 : Blo 964590 965739 := bstep (se 1 (by rfl) ⟨724304, by rfl⟩ : syracuseStep 965739 = 1448609) B1448609
theorem B965751 : Blo 964590 965751 := bstep (se 1 (by rfl) ⟨724313, by rfl⟩ : syracuseStep 965751 = 1448627) B1448627
theorem B965771 : Blo 964590 965771 := bstep (se 1 (by rfl) ⟨724328, by rfl⟩ : syracuseStep 965771 = 1448657) B1448657
theorem B965783 : Blo 964590 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B965803 : Blo 964590 965803 := bstep (se 1 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 965803 = 1448705) B1448705
theorem B965815 : Blo 964590 965815 := bstep (se 1 (by rfl) ⟨724361, by rfl⟩ : syracuseStep 965815 = 1448723) B1448723
theorem B965835 : Blo 964590 965835 := bstep (se 1 (by rfl) ⟨724376, by rfl⟩ : syracuseStep 965835 = 1448753) B1448753
theorem B2178251 : Blo 964590 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B965847 : Blo 964590 965847 := bstep (se 1 (by rfl) ⟨724385, by rfl⟩ : syracuseStep 965847 = 1448771) B1448771
theorem B965867 : Blo 964590 965867 := bstep (se 1 (by rfl) ⟨724400, by rfl⟩ : syracuseStep 965867 = 1448801) B1448801
theorem B965879 : Blo 964590 965879 := bstep (se 1 (by rfl) ⟨724409, by rfl⟩ : syracuseStep 965879 = 1448819) B1448819
theorem B2178305 : Blo 964590 2178305 := bstep (se 2 (by rfl) ⟨816864, by rfl⟩ : syracuseStep 2178305 = 1633729) B1633729
theorem B965899 : Blo 964590 965899 := bstep (se 1 (by rfl) ⟨724424, by rfl⟩ : syracuseStep 965899 = 1448849) B1448849
theorem B965911 : Blo 964590 965911 := bstep (se 1 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 965911 = 1448867) B1448867
theorem B965931 : Blo 964590 965931 := bstep (se 1 (by rfl) ⟨724448, by rfl⟩ : syracuseStep 965931 = 1448897) B1448897
theorem B965943 : Blo 964590 965943 := bstep (se 1 (by rfl) ⟨724457, by rfl⟩ : syracuseStep 965943 = 1448915) B1448915
theorem B4177217 : Blo 964590 4177217 := bstep (se 2 (by rfl) ⟨1566456, by rfl⟩ : syracuseStep 4177217 = 3132913) B3132913
theorem B965963 : Blo 964590 965963 := bstep (se 1 (by rfl) ⟨724472, by rfl⟩ : syracuseStep 965963 = 1448945) B1448945
theorem B965975 : Blo 964590 965975 := bstep (se 1 (by rfl) ⟨724481, by rfl⟩ : syracuseStep 965975 = 1448963) B1448963
theorem B965995 : Blo 964590 965995 := bstep (se 1 (by rfl) ⟨724496, by rfl⟩ : syracuseStep 965995 = 1448993) B1448993
theorem B966007 : Blo 964590 966007 := bstep (se 1 (by rfl) ⟨724505, by rfl⟩ : syracuseStep 966007 = 1449011) B1449011
theorem B966027 : Blo 964590 966027 := bstep (se 1 (by rfl) ⟨724520, by rfl⟩ : syracuseStep 966027 = 1449041) B1449041
theorem B966039 : Blo 964590 966039 := bstep (se 1 (by rfl) ⟨724529, by rfl⟩ : syracuseStep 966039 = 1449059) B1449059
theorem B1490327 : Blo 964590 1490327 := bstep (se 1 (by rfl) ⟨1117745, by rfl⟩ : syracuseStep 1490327 = 2235491) B2235491
theorem B966059 : Blo 964590 966059 := bstep (se 1 (by rfl) ⟨724544, by rfl⟩ : syracuseStep 966059 = 1449089) B1449089
theorem B966071 : Blo 964590 966071 := bstep (se 1 (by rfl) ⟨724553, by rfl⟩ : syracuseStep 966071 = 1449107) B1449107
theorem B966091 : Blo 964590 966091 := bstep (se 1 (by rfl) ⟨724568, by rfl⟩ : syracuseStep 966091 = 1449137) B1449137
theorem B966103 : Blo 964590 966103 := bstep (se 1 (by rfl) ⟨724577, by rfl⟩ : syracuseStep 966103 = 1449155) B1449155
theorem B2178521 : Blo 964590 2178521 := bstep (se 2 (by rfl) ⟨816945, by rfl⟩ : syracuseStep 2178521 = 1633891) B1633891
theorem B966123 : Blo 964590 966123 := bstep (se 1 (by rfl) ⟨724592, by rfl⟩ : syracuseStep 966123 = 1449185) B1449185
theorem B966135 : Blo 964590 966135 := bstep (se 1 (by rfl) ⟨724601, by rfl⟩ : syracuseStep 966135 = 1449203) B1449203
theorem B966155 : Blo 964590 966155 := bstep (se 1 (by rfl) ⟨724616, by rfl⟩ : syracuseStep 966155 = 1449233) B1449233
theorem B966167 : Blo 964590 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B966187 : Blo 964590 966187 := bstep (se 1 (by rfl) ⟨724640, by rfl⟩ : syracuseStep 966187 = 1449281) B1449281
theorem B2178611 : Blo 964590 2178611 := bstep (se 1 (by rfl) ⟨1633958, by rfl⟩ : syracuseStep 2178611 = 3267917) B3267917
theorem B966199 : Blo 964590 966199 := bstep (se 1 (by rfl) ⟨724649, by rfl⟩ : syracuseStep 966199 = 1449299) B1449299
theorem B3259979 : Blo 964590 3259979 := bstep (se 1 (by rfl) ⟨2444984, by rfl⟩ : syracuseStep 3259979 = 4889969) B4889969
theorem B966219 : Blo 964590 966219 := bstep (se 1 (by rfl) ⟨724664, by rfl⟩ : syracuseStep 966219 = 1449329) B1449329
theorem B966231 : Blo 964590 966231 := bstep (se 1 (by rfl) ⟨724673, by rfl⟩ : syracuseStep 966231 = 1449347) B1449347
theorem B2178647 : Blo 964590 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B966251 : Blo 964590 966251 := bstep (se 1 (by rfl) ⟨724688, by rfl⟩ : syracuseStep 966251 = 1449377) B1449377
theorem B966263 : Blo 964590 966263 := bstep (se 1 (by rfl) ⟨724697, by rfl⟩ : syracuseStep 966263 = 1449395) B1449395
theorem B966283 : Blo 964590 966283 := bstep (se 1 (by rfl) ⟨724712, by rfl⟩ : syracuseStep 966283 = 1449425) B1449425
theorem B966295 : Blo 964590 966295 := bstep (se 1 (by rfl) ⟨724721, by rfl⟩ : syracuseStep 966295 = 1449443) B1449443
theorem B966315 : Blo 964590 966315 := bstep (se 1 (by rfl) ⟨724736, by rfl⟩ : syracuseStep 966315 = 1449473) B1449473
theorem B966327 : Blo 964590 966327 := bstep (se 1 (by rfl) ⟨724745, by rfl⟩ : syracuseStep 966327 = 1449491) B1449491
theorem B966347 : Blo 964590 966347 := bstep (se 1 (by rfl) ⟨724760, by rfl⟩ : syracuseStep 966347 = 1449521) B1449521
theorem B966359 : Blo 964590 966359 := bstep (se 1 (by rfl) ⟨724769, by rfl⟩ : syracuseStep 966359 = 1449539) B1449539
theorem B966379 : Blo 964590 966379 := bstep (se 1 (by rfl) ⟨724784, by rfl⟩ : syracuseStep 966379 = 1449569) B1449569
theorem B966391 : Blo 964590 966391 := bstep (se 1 (by rfl) ⟨724793, by rfl⟩ : syracuseStep 966391 = 1449587) B1449587
theorem B966411 : Blo 964590 966411 := bstep (se 1 (by rfl) ⟨724808, by rfl⟩ : syracuseStep 966411 = 1449617) B1449617
theorem B2178827 : Blo 964590 2178827 := bstep (se 1 (by rfl) ⟨1634120, by rfl⟩ : syracuseStep 2178827 = 3268241) B3268241
theorem B966423 : Blo 964590 966423 := bstep (se 1 (by rfl) ⟨724817, by rfl⟩ : syracuseStep 966423 = 1449635) B1449635
theorem B966443 : Blo 964590 966443 := bstep (se 1 (by rfl) ⟨724832, by rfl⟩ : syracuseStep 966443 = 1449665) B1449665
theorem B966455 : Blo 964590 966455 := bstep (se 1 (by rfl) ⟨724841, by rfl⟩ : syracuseStep 966455 = 1449683) B1449683
theorem B2178881 : Blo 964590 2178881 := bstep (se 2 (by rfl) ⟨817080, by rfl⟩ : syracuseStep 2178881 = 1634161) B1634161
theorem B966475 : Blo 964590 966475 := bstep (se 1 (by rfl) ⟨724856, by rfl⟩ : syracuseStep 966475 = 1449713) B1449713
theorem B966487 : Blo 964590 966487 := bstep (se 1 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 966487 = 1449731) B1449731
theorem B3260249 : Blo 964590 3260249 := bstep (se 2 (by rfl) ⟨1222593, by rfl⟩ : syracuseStep 3260249 = 2445187) B2445187
theorem B966507 : Blo 964590 966507 := bstep (se 1 (by rfl) ⟨724880, by rfl⟩ : syracuseStep 966507 = 1449761) B1449761
theorem B966519 : Blo 964590 966519 := bstep (se 1 (by rfl) ⟨724889, by rfl⟩ : syracuseStep 966519 = 1449779) B1449779
theorem B966539 : Blo 964590 966539 := bstep (se 1 (by rfl) ⟨724904, by rfl⟩ : syracuseStep 966539 = 1449809) B1449809
theorem B966551 : Blo 964590 966551 := bstep (se 1 (by rfl) ⟨724913, by rfl⟩ : syracuseStep 966551 = 1449827) B1449827
theorem B966571 : Blo 964590 966571 := bstep (se 1 (by rfl) ⟨724928, by rfl⟩ : syracuseStep 966571 = 1449857) B1449857
theorem B45957041 : Blo 964590 45957041 := bstep (se 2 (by rfl) ⟨17233890, by rfl⟩ : syracuseStep 45957041 = 34467781) B34467781
theorem B966583 : Blo 964590 966583 := bstep (se 1 (by rfl) ⟨724937, by rfl⟩ : syracuseStep 966583 = 1449875) B1449875
theorem B966603 : Blo 964590 966603 := bstep (se 1 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 966603 = 1449905) B1449905
theorem B966615 : Blo 964590 966615 := bstep (se 1 (by rfl) ⟨724961, by rfl⟩ : syracuseStep 966615 = 1449923) B1449923
theorem B966635 : Blo 964590 966635 := bstep (se 1 (by rfl) ⟨724976, by rfl⟩ : syracuseStep 966635 = 1449953) B1449953
theorem B966647 : Blo 964590 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B966667 : Blo 964590 966667 := bstep (se 1 (by rfl) ⟨725000, by rfl⟩ : syracuseStep 966667 = 1450001) B1450001
theorem B966679 : Blo 964590 966679 := bstep (se 1 (by rfl) ⟨725009, by rfl⟩ : syracuseStep 966679 = 1450019) B1450019
theorem B2179097 : Blo 964590 2179097 := bstep (se 2 (by rfl) ⟨817161, by rfl⟩ : syracuseStep 2179097 = 1634323) B1634323
theorem B10469411 : Blo 964590 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B966699 : Blo 964590 966699 := bstep (se 1 (by rfl) ⟨725024, by rfl⟩ : syracuseStep 966699 = 1450049) B1450049
theorem B7258157 : Blo 964590 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B1032247 : Blo 964590 1032247 := bstep (se 1 (by rfl) ⟨774185, by rfl⟩ : syracuseStep 1032247 = 1548371) B1548371
theorem B966711 : Blo 964590 966711 := bstep (se 1 (by rfl) ⟨725033, by rfl⟩ : syracuseStep 966711 = 1450067) B1450067
theorem B966731 : Blo 964590 966731 := bstep (se 1 (by rfl) ⟨725048, by rfl⟩ : syracuseStep 966731 = 1450097) B1450097
theorem B966743 : Blo 964590 966743 := bstep (se 1 (by rfl) ⟨725057, by rfl⟩ : syracuseStep 966743 = 1450115) B1450115
theorem B966763 : Blo 964590 966763 := bstep (se 1 (by rfl) ⟨725072, by rfl⟩ : syracuseStep 966763 = 1450145) B1450145
theorem B2179187 : Blo 964590 2179187 := bstep (se 1 (by rfl) ⟨1634390, by rfl⟩ : syracuseStep 2179187 = 3268781) B3268781
theorem B966775 : Blo 964590 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B966795 : Blo 964590 966795 := bstep (se 1 (by rfl) ⟨725096, by rfl⟩ : syracuseStep 966795 = 1450193) B1450193
theorem B10436759 : Blo 964590 10436759 := bstep (se 1 (by rfl) ⟨7827569, by rfl⟩ : syracuseStep 10436759 = 15655139) B15655139
theorem B966807 : Blo 964590 966807 := bstep (se 1 (by rfl) ⟨725105, by rfl⟩ : syracuseStep 966807 = 1450211) B1450211
theorem B2179223 : Blo 964590 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B966827 : Blo 964590 966827 := bstep (se 1 (by rfl) ⟨725120, by rfl⟩ : syracuseStep 966827 = 1450241) B1450241
theorem B966839 : Blo 964590 966839 := bstep (se 1 (by rfl) ⟨725129, by rfl⟩ : syracuseStep 966839 = 1450259) B1450259
theorem B966859 : Blo 964590 966859 := bstep (se 1 (by rfl) ⟨725144, by rfl⟩ : syracuseStep 966859 = 1450289) B1450289
theorem B966871 : Blo 964590 966871 := bstep (se 1 (by rfl) ⟨725153, by rfl⟩ : syracuseStep 966871 = 1450307) B1450307
theorem B966891 : Blo 964590 966891 := bstep (se 1 (by rfl) ⟨725168, by rfl⟩ : syracuseStep 966891 = 1450337) B1450337
theorem B966903 : Blo 964590 966903 := bstep (se 1 (by rfl) ⟨725177, by rfl⟩ : syracuseStep 966903 = 1450355) B1450355
theorem B966923 : Blo 964590 966923 := bstep (se 1 (by rfl) ⟨725192, by rfl⟩ : syracuseStep 966923 = 1450385) B1450385
theorem B966935 : Blo 964590 966935 := bstep (se 1 (by rfl) ⟨725201, by rfl⟩ : syracuseStep 966935 = 1450403) B1450403
theorem B966955 : Blo 964590 966955 := bstep (se 1 (by rfl) ⟨725216, by rfl⟩ : syracuseStep 966955 = 1450433) B1450433
theorem B3096883 : Blo 964590 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B966967 : Blo 964590 966967 := bstep (se 1 (by rfl) ⟨725225, by rfl⟩ : syracuseStep 966967 = 1450451) B1450451
theorem B966987 : Blo 964590 966987 := bstep (se 1 (by rfl) ⟨725240, by rfl⟩ : syracuseStep 966987 = 1450481) B1450481
theorem B966999 : Blo 964590 966999 := bstep (se 1 (by rfl) ⟨725249, by rfl⟩ : syracuseStep 966999 = 1450499) B1450499
theorem B967019 : Blo 964590 967019 := bstep (se 1 (by rfl) ⟨725264, by rfl⟩ : syracuseStep 967019 = 1450529) B1450529
theorem B967031 : Blo 964590 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B4899203 : Blo 964590 4899203 := bstep (se 1 (by rfl) ⟨3674402, by rfl⟩ : syracuseStep 4899203 = 7348805) B7348805
theorem B967051 : Blo 964590 967051 := bstep (se 1 (by rfl) ⟨725288, by rfl⟩ : syracuseStep 967051 = 1450577) B1450577
theorem B2441623 : Blo 964590 2441623 := bstep (se 1 (by rfl) ⟨1831217, by rfl⟩ : syracuseStep 2441623 = 3662435) B3662435
theorem B967063 : Blo 964590 967063 := bstep (se 1 (by rfl) ⟨725297, by rfl⟩ : syracuseStep 967063 = 1450595) B1450595
theorem B967083 : Blo 964590 967083 := bstep (se 1 (by rfl) ⟨725312, by rfl⟩ : syracuseStep 967083 = 1450625) B1450625
theorem B967095 : Blo 964590 967095 := bstep (se 1 (by rfl) ⟨725321, by rfl⟩ : syracuseStep 967095 = 1450643) B1450643
theorem B3097025 : Blo 964590 3097025 := bstep (se 2 (by rfl) ⟨1161384, by rfl⟩ : syracuseStep 3097025 = 2322769) B2322769
theorem B967115 : Blo 964590 967115 := bstep (se 1 (by rfl) ⟨725336, by rfl⟩ : syracuseStep 967115 = 1450673) B1450673
theorem B967127 : Blo 964590 967127 := bstep (se 1 (by rfl) ⟨725345, by rfl⟩ : syracuseStep 967127 = 1450691) B1450691
theorem B3490265 : Blo 964590 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B967147 : Blo 964590 967147 := bstep (se 1 (by rfl) ⟨725360, by rfl⟩ : syracuseStep 967147 = 1450721) B1450721
theorem B967159 : Blo 964590 967159 := bstep (se 1 (by rfl) ⟨725369, by rfl⟩ : syracuseStep 967159 = 1450739) B1450739
theorem B967179 : Blo 964590 967179 := bstep (se 1 (by rfl) ⟨725384, by rfl⟩ : syracuseStep 967179 = 1450769) B1450769
theorem B3260951 : Blo 964590 3260951 := bstep (se 1 (by rfl) ⟨2445713, by rfl⟩ : syracuseStep 3260951 = 4891427) B4891427
theorem B967191 : Blo 964590 967191 := bstep (se 1 (by rfl) ⟨725393, by rfl⟩ : syracuseStep 967191 = 1450787) B1450787
theorem B8241709 : Blo 964590 8241709 := bstep (se 3 (by rfl) ⟨1545320, by rfl⟩ : syracuseStep 8241709 = 3090641) B3090641
theorem B967211 : Blo 964590 967211 := bstep (se 1 (by rfl) ⟨725408, by rfl⟩ : syracuseStep 967211 = 1450817) B1450817
theorem B967223 : Blo 964590 967223 := bstep (se 1 (by rfl) ⟨725417, by rfl⟩ : syracuseStep 967223 = 1450835) B1450835
theorem B967243 : Blo 964590 967243 := bstep (se 1 (by rfl) ⟨725432, by rfl⟩ : syracuseStep 967243 = 1450865) B1450865
theorem B967255 : Blo 964590 967255 := bstep (se 1 (by rfl) ⟨725441, by rfl⟩ : syracuseStep 967255 = 1450883) B1450883
theorem B967275 : Blo 964590 967275 := bstep (se 1 (by rfl) ⟨725456, by rfl⟩ : syracuseStep 967275 = 1450913) B1450913
theorem B967287 : Blo 964590 967287 := bstep (se 1 (by rfl) ⟨725465, by rfl⟩ : syracuseStep 967287 = 1450931) B1450931
theorem B967307 : Blo 964590 967307 := bstep (se 1 (by rfl) ⟨725480, by rfl⟩ : syracuseStep 967307 = 1450961) B1450961
theorem B967319 : Blo 964590 967319 := bstep (se 1 (by rfl) ⟨725489, by rfl⟩ : syracuseStep 967319 = 1450979) B1450979
theorem B967339 : Blo 964590 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B967351 : Blo 964590 967351 := bstep (se 1 (by rfl) ⟨725513, by rfl⟩ : syracuseStep 967351 = 1451027) B1451027
theorem B967371 : Blo 964590 967371 := bstep (se 1 (by rfl) ⟨725528, by rfl⟩ : syracuseStep 967371 = 1451057) B1451057
theorem B967383 : Blo 964590 967383 := bstep (se 1 (by rfl) ⟨725537, by rfl⟩ : syracuseStep 967383 = 1451075) B1451075
theorem B967403 : Blo 964590 967403 := bstep (se 1 (by rfl) ⟨725552, by rfl⟩ : syracuseStep 967403 = 1451105) B1451105
theorem B967415 : Blo 964590 967415 := bstep (se 1 (by rfl) ⟨725561, by rfl⟩ : syracuseStep 967415 = 1451123) B1451123
theorem B967435 : Blo 964590 967435 := bstep (se 1 (by rfl) ⟨725576, by rfl⟩ : syracuseStep 967435 = 1451153) B1451153
theorem B967447 : Blo 964590 967447 := bstep (se 1 (by rfl) ⟨725585, by rfl⟩ : syracuseStep 967447 = 1451171) B1451171
theorem B967467 : Blo 964590 967467 := bstep (se 1 (by rfl) ⟨725600, by rfl⟩ : syracuseStep 967467 = 1451201) B1451201
theorem B967479 : Blo 964590 967479 := bstep (se 1 (by rfl) ⟨725609, by rfl⟩ : syracuseStep 967479 = 1451219) B1451219
theorem B2442059 : Blo 964590 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B967499 : Blo 964590 967499 := bstep (se 1 (by rfl) ⟨725624, by rfl⟩ : syracuseStep 967499 = 1451249) B1451249
theorem B967511 : Blo 964590 967511 := bstep (se 1 (by rfl) ⟨725633, by rfl⟩ : syracuseStep 967511 = 1451267) B1451267
theorem B967531 : Blo 964590 967531 := bstep (se 1 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 967531 = 1451297) B1451297
theorem B967543 : Blo 964590 967543 := bstep (se 1 (by rfl) ⟨725657, by rfl⟩ : syracuseStep 967543 = 1451315) B1451315
theorem B967563 : Blo 964590 967563 := bstep (se 1 (by rfl) ⟨725672, by rfl⟩ : syracuseStep 967563 = 1451345) B1451345
theorem B967575 : Blo 964590 967575 := bstep (se 1 (by rfl) ⟨725681, by rfl⟩ : syracuseStep 967575 = 1451363) B1451363
theorem B967595 : Blo 964590 967595 := bstep (se 1 (by rfl) ⟨725696, by rfl⟩ : syracuseStep 967595 = 1451393) B1451393
theorem B967607 : Blo 964590 967607 := bstep (se 1 (by rfl) ⟨725705, by rfl⟩ : syracuseStep 967607 = 1451411) B1451411
theorem B967627 : Blo 964590 967627 := bstep (se 1 (by rfl) ⟨725720, by rfl⟩ : syracuseStep 967627 = 1451441) B1451441
theorem B967639 : Blo 964590 967639 := bstep (se 1 (by rfl) ⟨725729, by rfl⟩ : syracuseStep 967639 = 1451459) B1451459
theorem B967659 : Blo 964590 967659 := bstep (se 1 (by rfl) ⟨725744, by rfl⟩ : syracuseStep 967659 = 1451489) B1451489
theorem B967671 : Blo 964590 967671 := bstep (se 1 (by rfl) ⟨725753, by rfl⟩ : syracuseStep 967671 = 1451507) B1451507
theorem B967691 : Blo 964590 967691 := bstep (se 1 (by rfl) ⟨725768, by rfl⟩ : syracuseStep 967691 = 1451537) B1451537
theorem B967703 : Blo 964590 967703 := bstep (se 1 (by rfl) ⟨725777, by rfl⟩ : syracuseStep 967703 = 1451555) B1451555
theorem B967723 : Blo 964590 967723 := bstep (se 1 (by rfl) ⟨725792, by rfl⟩ : syracuseStep 967723 = 1451585) B1451585
theorem B3261491 : Blo 964590 3261491 := bstep (se 1 (by rfl) ⟨2446118, by rfl⟩ : syracuseStep 3261491 = 4892237) B4892237
theorem B967735 : Blo 964590 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B967755 : Blo 964590 967755 := bstep (se 1 (by rfl) ⟨725816, by rfl⟩ : syracuseStep 967755 = 1451633) B1451633
theorem B967767 : Blo 964590 967767 := bstep (se 1 (by rfl) ⟨725825, by rfl⟩ : syracuseStep 967767 = 1451651) B1451651
theorem B6964325 : Blo 964590 6964325 := bstep (se 4 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 6964325 = 1305811) B1305811
theorem B967787 : Blo 964590 967787 := bstep (se 1 (by rfl) ⟨725840, by rfl⟩ : syracuseStep 967787 = 1451681) B1451681
theorem B967799 : Blo 964590 967799 := bstep (se 1 (by rfl) ⟨725849, by rfl⟩ : syracuseStep 967799 = 1451699) B1451699
theorem B967819 : Blo 964590 967819 := bstep (se 1 (by rfl) ⟨725864, by rfl⟩ : syracuseStep 967819 = 1451729) B1451729
theorem B967831 : Blo 964590 967831 := bstep (se 1 (by rfl) ⟨725873, by rfl⟩ : syracuseStep 967831 = 1451747) B1451747
theorem B967851 : Blo 964590 967851 := bstep (se 1 (by rfl) ⟨725888, by rfl⟩ : syracuseStep 967851 = 1451777) B1451777
theorem B967863 : Blo 964590 967863 := bstep (se 1 (by rfl) ⟨725897, by rfl⟩ : syracuseStep 967863 = 1451795) B1451795
theorem B2442433 : Blo 964590 2442433 := bstep (se 2 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 2442433 = 1831825) B1831825
theorem B967883 : Blo 964590 967883 := bstep (se 1 (by rfl) ⟨725912, by rfl⟩ : syracuseStep 967883 = 1451825) B1451825
theorem B967895 : Blo 964590 967895 := bstep (se 1 (by rfl) ⟨725921, by rfl⟩ : syracuseStep 967895 = 1451843) B1451843
theorem B967915 : Blo 964590 967915 := bstep (se 1 (by rfl) ⟨725936, by rfl⟩ : syracuseStep 967915 = 1451873) B1451873
theorem B967927 : Blo 964590 967927 := bstep (se 1 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 967927 = 1451891) B1451891
theorem B967947 : Blo 964590 967947 := bstep (se 1 (by rfl) ⟨725960, by rfl⟩ : syracuseStep 967947 = 1451921) B1451921
theorem B967959 : Blo 964590 967959 := bstep (se 1 (by rfl) ⟨725969, by rfl⟩ : syracuseStep 967959 = 1451939) B1451939
theorem B967979 : Blo 964590 967979 := bstep (se 1 (by rfl) ⟨725984, by rfl⟩ : syracuseStep 967979 = 1451969) B1451969
theorem B967991 : Blo 964590 967991 := bstep (se 1 (by rfl) ⟨725993, by rfl⟩ : syracuseStep 967991 = 1451987) B1451987
theorem B3261761 : Blo 964590 3261761 := bstep (se 2 (by rfl) ⟨1223160, by rfl⟩ : syracuseStep 3261761 = 2446321) B2446321
theorem B968011 : Blo 964590 968011 := bstep (se 1 (by rfl) ⟨726008, by rfl⟩ : syracuseStep 968011 = 1452017) B1452017
theorem B968023 : Blo 964590 968023 := bstep (se 1 (by rfl) ⟨726017, by rfl⟩ : syracuseStep 968023 = 1452035) B1452035
theorem B968043 : Blo 964590 968043 := bstep (se 1 (by rfl) ⟨726032, by rfl⟩ : syracuseStep 968043 = 1452065) B1452065
theorem B968055 : Blo 964590 968055 := bstep (se 1 (by rfl) ⟨726041, by rfl⟩ : syracuseStep 968055 = 1452083) B1452083
theorem B968075 : Blo 964590 968075 := bstep (se 1 (by rfl) ⟨726056, by rfl⟩ : syracuseStep 968075 = 1452113) B1452113
theorem B968087 : Blo 964590 968087 := bstep (se 1 (by rfl) ⟨726065, by rfl⟩ : syracuseStep 968087 = 1452131) B1452131
theorem B968107 : Blo 964590 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B968119 : Blo 964590 968119 := bstep (se 1 (by rfl) ⟨726089, by rfl⟩ : syracuseStep 968119 = 1452179) B1452179
theorem B968139 : Blo 964590 968139 := bstep (se 1 (by rfl) ⟨726104, by rfl⟩ : syracuseStep 968139 = 1452209) B1452209
theorem B968151 : Blo 964590 968151 := bstep (se 1 (by rfl) ⟨726113, by rfl⟩ : syracuseStep 968151 = 1452227) B1452227
theorem B8832473 : Blo 964590 8832473 := bstep (se 2 (by rfl) ⟨3312177, by rfl⟩ : syracuseStep 8832473 = 6624355) B6624355
theorem B968171 : Blo 964590 968171 := bstep (se 1 (by rfl) ⟨726128, by rfl⟩ : syracuseStep 968171 = 1452257) B1452257
theorem B968183 : Blo 964590 968183 := bstep (se 1 (by rfl) ⟨726137, by rfl⟩ : syracuseStep 968183 = 1452275) B1452275
theorem B968203 : Blo 964590 968203 := bstep (se 1 (by rfl) ⟨726152, by rfl⟩ : syracuseStep 968203 = 1452305) B1452305
theorem B968215 : Blo 964590 968215 := bstep (se 1 (by rfl) ⟨726161, by rfl⟩ : syracuseStep 968215 = 1452323) B1452323
theorem B968235 : Blo 964590 968235 := bstep (se 1 (by rfl) ⟨726176, by rfl⟩ : syracuseStep 968235 = 1452353) B1452353
theorem B968247 : Blo 964590 968247 := bstep (se 1 (by rfl) ⟨726185, by rfl⟩ : syracuseStep 968247 = 1452371) B1452371
theorem B3720779 : Blo 964590 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B968267 : Blo 964590 968267 := bstep (se 1 (by rfl) ⟨726200, by rfl⟩ : syracuseStep 968267 = 1452401) B1452401
theorem B968279 : Blo 964590 968279 := bstep (se 1 (by rfl) ⟨726209, by rfl⟩ : syracuseStep 968279 = 1452419) B1452419
theorem B968299 : Blo 964590 968299 := bstep (se 1 (by rfl) ⟨726224, by rfl⟩ : syracuseStep 968299 = 1452449) B1452449
theorem B968311 : Blo 964590 968311 := bstep (se 1 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 968311 = 1452467) B1452467
theorem B968331 : Blo 964590 968331 := bstep (se 1 (by rfl) ⟨726248, by rfl⟩ : syracuseStep 968331 = 1452497) B1452497
theorem B1033879 : Blo 964590 1033879 := bstep (se 1 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 1033879 = 1550819) B1550819
theorem B968343 : Blo 964590 968343 := bstep (se 1 (by rfl) ⟨726257, by rfl⟩ : syracuseStep 968343 = 1452515) B1452515
theorem B968363 : Blo 964590 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B968375 : Blo 964590 968375 := bstep (se 1 (by rfl) ⟨726281, by rfl⟩ : syracuseStep 968375 = 1452563) B1452563
theorem B968395 : Blo 964590 968395 := bstep (se 1 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 968395 = 1452593) B1452593
theorem B968407 : Blo 964590 968407 := bstep (se 1 (by rfl) ⟨726305, by rfl⟩ : syracuseStep 968407 = 1452611) B1452611
theorem B968427 : Blo 964590 968427 := bstep (se 1 (by rfl) ⟨726320, by rfl⟩ : syracuseStep 968427 = 1452641) B1452641
theorem B968439 : Blo 964590 968439 := bstep (se 1 (by rfl) ⟨726329, by rfl⟩ : syracuseStep 968439 = 1452659) B1452659
theorem B968459 : Blo 964590 968459 := bstep (se 1 (by rfl) ⟨726344, by rfl⟩ : syracuseStep 968459 = 1452689) B1452689
theorem B2443031 : Blo 964590 2443031 := bstep (se 1 (by rfl) ⟨1832273, by rfl⟩ : syracuseStep 2443031 = 3664547) B3664547
theorem B968471 : Blo 964590 968471 := bstep (se 1 (by rfl) ⟨726353, by rfl⟩ : syracuseStep 968471 = 1452707) B1452707
theorem B968491 : Blo 964590 968491 := bstep (se 1 (by rfl) ⟨726368, by rfl⟩ : syracuseStep 968491 = 1452737) B1452737
theorem B968503 : Blo 964590 968503 := bstep (se 1 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 968503 = 1452755) B1452755
theorem B968523 : Blo 964590 968523 := bstep (se 1 (by rfl) ⟨726392, by rfl⟩ : syracuseStep 968523 = 1452785) B1452785
theorem B968535 : Blo 964590 968535 := bstep (se 1 (by rfl) ⟨726401, by rfl⟩ : syracuseStep 968535 = 1452803) B1452803
theorem B3262301 : Blo 964590 3262301 := bstep (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) B1223363
theorem B8243045 : Blo 964590 8243045 := bstep (se 4 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 8243045 = 1545571) B1545571
theorem B968555 : Blo 964590 968555 := bstep (se 1 (by rfl) ⟨726416, by rfl⟩ : syracuseStep 968555 = 1452833) B1452833
theorem B968567 : Blo 964590 968567 := bstep (se 1 (by rfl) ⟨726425, by rfl⟩ : syracuseStep 968567 = 1452851) B1452851
theorem B968587 : Blo 964590 968587 := bstep (se 1 (by rfl) ⟨726440, by rfl⟩ : syracuseStep 968587 = 1452881) B1452881
theorem B3098945 : Blo 964590 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B13912499 : Blo 964590 13912499 := bstep (se 1 (by rfl) ⟨10434374, by rfl⟩ : syracuseStep 13912499 = 20868749) B20868749
theorem B4639193 : Blo 964590 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B2443841 : Blo 964590 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B2607947 : Blo 964590 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B2476889 : Blo 964590 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B3099485 : Blo 964590 3099485 := bstep (se 3 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 3099485 = 1162307) B1162307
theorem B2608075 : Blo 964590 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B3263435 : Blo 964590 3263435 := bstep (se 1 (by rfl) ⟨2447576, by rfl⟩ : syracuseStep 3263435 = 4895153) B4895153
theorem B3722257 : Blo 964590 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B2444377 : Blo 964590 2444377 := bstep (se 2 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 2444377 = 1833283) B1833283
theorem B8801459 : Blo 964590 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B3263705 : Blo 964590 3263705 := bstep (se 2 (by rfl) ⟨1223889, by rfl⟩ : syracuseStep 3263705 = 2447779) B2447779
theorem B5295889 : Blo 964590 5295889 := bstep (se 2 (by rfl) ⟨1985958, by rfl⟩ : syracuseStep 5295889 = 3971917) B3971917
theorem B3264407 : Blo 964590 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B2609113 : Blo 964590 2609113 := bstep (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) B1956835
theorem B4902929 : Blo 964590 4902929 := bstep (se 2 (by rfl) ⟨1838598, by rfl⟩ : syracuseStep 4902929 = 3677197) B3677197
theorem B2445491 : Blo 964590 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B4903091 : Blo 964590 4903091 := bstep (se 1 (by rfl) ⟨3677318, by rfl⟩ : syracuseStep 4903091 = 7354637) B7354637
theorem B7852249 : Blo 964590 7852249 := bstep (se 2 (by rfl) ⟨2944593, by rfl⟩ : syracuseStep 7852249 = 5889187) B5889187
theorem B2609459 : Blo 964590 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B6607169 : Blo 964590 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B3264947 : Blo 964590 3264947 := bstep (se 1 (by rfl) ⟨2448710, by rfl⟩ : syracuseStep 3264947 = 4897421) B4897421
theorem B5231027 : Blo 964590 5231027 := bstep (se 1 (by rfl) ⟨3923270, by rfl⟩ : syracuseStep 5231027 = 7846541) B7846541
theorem B2478529 : Blo 964590 2478529 := bstep (se 2 (by rfl) ⟨929448, by rfl⟩ : syracuseStep 2478529 = 1858897) B1858897
theorem B2445785 : Blo 964590 2445785 := bstep (se 2 (by rfl) ⟨917169, by rfl⟩ : syracuseStep 2445785 = 1834339) B1834339
theorem B21189251 : Blo 964590 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B3265217 : Blo 964590 3265217 := bstep (se 2 (by rfl) ⟨1224456, by rfl⟩ : syracuseStep 3265217 = 2448913) B2448913
theorem B1791041 : Blo 964590 1791041 := bstep (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) B1343281
theorem B3265757 : Blo 964590 3265757 := bstep (se 3 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 3265757 = 1224659) B1224659
theorem B2610497 : Blo 964590 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B5494337 : Blo 964590 5494337 := bstep (se 2 (by rfl) ⟨2060376, by rfl⟩ : syracuseStep 5494337 = 4120753) B4120753
theorem B10442333 : Blo 964590 10442333 := bstep (se 3 (by rfl) ⟨1957937, by rfl⟩ : syracuseStep 10442333 = 3915875) B3915875
theorem B5232221 : Blo 964590 5232221 := bstep (se 3 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 5232221 = 1962083) B1962083
theorem B2447435 : Blo 964590 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B1628363 : Blo 964590 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B1628491 : Blo 964590 1628491 := bstep (se 1 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 1628491 = 2442737) B2442737
theorem B3266891 : Blo 964590 3266891 := bstep (se 1 (by rfl) ⟨2450168, by rfl⟩ : syracuseStep 3266891 = 4900337) B4900337
theorem B1628633 : Blo 964590 1628633 := bstep (se 2 (by rfl) ⟨610737, by rfl⟩ : syracuseStep 1628633 = 1221475) B1221475
theorem B3922397 : Blo 964590 3922397 := bstep (se 3 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 3922397 = 1470899) B1470899
theorem B19847693 : Blo 964590 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B1628761 : Blo 964590 1628761 := bstep (se 2 (by rfl) ⟨610785, by rfl⟩ : syracuseStep 1628761 = 1221571) B1221571
theorem B3267161 : Blo 964590 3267161 := bstep (se 2 (by rfl) ⟨1225185, by rfl⟩ : syracuseStep 3267161 = 2450371) B2450371
theorem B6183641 : Blo 964590 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B2448407 : Blo 964590 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B12377123 : Blo 964590 12377123 := bstep (se 1 (by rfl) ⟨9282842, by rfl⟩ : syracuseStep 12377123 = 18565685) B18565685
theorem B1629335 : Blo 964590 1629335 := bstep (se 1 (by rfl) ⟨1222001, by rfl⟩ : syracuseStep 1629335 = 2444003) B2444003
theorem B1629463 : Blo 964590 1629463 := bstep (se 1 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 1629463 = 2444195) B2444195
theorem B3267863 : Blo 964590 3267863 := bstep (se 1 (by rfl) ⟨2450897, by rfl⟩ : syracuseStep 3267863 = 4901795) B4901795
theorem B1858945 : Blo 964590 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B2449075 : Blo 964590 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B3268403 : Blo 964590 3268403 := bstep (se 1 (by rfl) ⟨2451302, by rfl⟩ : syracuseStep 3268403 = 4902605) B4902605
theorem B2449217 : Blo 964590 2449217 := bstep (se 2 (by rfl) ⟨918456, by rfl⟩ : syracuseStep 2449217 = 1836913) B1836913
theorem B1630091 : Blo 964590 1630091 := bstep (se 1 (by rfl) ⟨1222568, by rfl⟩ : syracuseStep 1630091 = 2445137) B2445137
theorem B4186073 : Blo 964590 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B1630219 : Blo 964590 1630219 := bstep (se 1 (by rfl) ⟨1222664, by rfl⟩ : syracuseStep 1630219 = 2445329) B2445329
theorem B4644881 : Blo 964590 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B3268673 : Blo 964590 3268673 := bstep (se 2 (by rfl) ⟨1225752, by rfl⟩ : syracuseStep 3268673 = 2451505) B2451505
theorem B1630361 : Blo 964590 1630361 := bstep (se 2 (by rfl) ⟨611385, by rfl⟩ : syracuseStep 1630361 = 1222771) B1222771
theorem B2318539 : Blo 964590 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B1630489 : Blo 964590 1630489 := bstep (se 2 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 1630489 = 1222867) B1222867
theorem B6185281 : Blo 964590 6185281 := bstep (se 2 (by rfl) ⟨2319480, by rfl⟩ : syracuseStep 6185281 = 4638961) B4638961
theorem B1958231 : Blo 964590 1958231 := bstep (se 1 (by rfl) ⟨1468673, by rfl⟩ : syracuseStep 1958231 = 2937347) B2937347
theorem B4645421 : Blo 964590 4645421 := bstep (se 3 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 4645421 = 1742033) B1742033
theorem B12411467 : Blo 964590 12411467 := bstep (se 1 (by rfl) ⟨9308600, by rfl⟩ : syracuseStep 12411467 = 18617201) B18617201
theorem B2319155 : Blo 964590 2319155 := bstep (se 1 (by rfl) ⟨1739366, by rfl⟩ : syracuseStep 2319155 = 3478733) B3478733
theorem B1631063 : Blo 964590 1631063 := bstep (se 1 (by rfl) ⟨1223297, by rfl⟩ : syracuseStep 1631063 = 2446595) B2446595
theorem B1631191 : Blo 964590 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B41870357 : Blo 964590 41870357 := bstep (se 6 (by rfl) ⟨981336, by rfl⟩ : syracuseStep 41870357 = 1962673) B1962673
theorem B2450483 : Blo 964590 2450483 := bstep (se 1 (by rfl) ⟨1837862, by rfl⟩ : syracuseStep 2450483 = 3675725) B3675725
theorem B4121675 : Blo 964590 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B4711517 : Blo 964590 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B1959041 : Blo 964590 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B2319511 : Blo 964590 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B3139037 : Blo 964590 3139037 := bstep (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) B1177139
theorem B3663377 : Blo 964590 3663377 := bstep (se 2 (by rfl) ⟨1373766, by rfl⟩ : syracuseStep 3663377 = 2747533) B2747533
theorem B1631819 : Blo 964590 1631819 := bstep (se 1 (by rfl) ⟨1223864, by rfl⟩ : syracuseStep 1631819 = 2447729) B2447729
theorem B2451019 : Blo 964590 2451019 := bstep (se 1 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 2451019 = 3676529) B3676529
theorem B4187821 : Blo 964590 4187821 := bstep (se 3 (by rfl) ⟨785216, by rfl⟩ : syracuseStep 4187821 = 1570433) B1570433
theorem B1631947 : Blo 964590 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B2451161 : Blo 964590 2451161 := bstep (se 2 (by rfl) ⟨919185, by rfl⟩ : syracuseStep 2451161 = 1838371) B1838371
theorem B9398081 : Blo 964590 9398081 := bstep (se 2 (by rfl) ⟨3524280, by rfl⟩ : syracuseStep 9398081 = 7048561) B7048561
theorem B1632089 : Blo 964590 1632089 := bstep (se 2 (by rfl) ⟨612033, by rfl⟩ : syracuseStep 1632089 = 1224067) B1224067
theorem B1632217 : Blo 964590 1632217 := bstep (se 2 (by rfl) ⟨612081, by rfl⟩ : syracuseStep 1632217 = 1224163) B1224163
theorem B3664075 : Blo 964590 3664075 := bstep (se 1 (by rfl) ⟨2748056, by rfl⟩ : syracuseStep 3664075 = 5496113) B5496113
theorem B1468697 : Blo 964590 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B5499211 : Blo 964590 5499211 := bstep (se 1 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 5499211 = 8248817) B8248817
theorem B2615645 : Blo 964590 2615645 := bstep (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) B980867
theorem B3664349 : Blo 964590 3664349 := bstep (se 3 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 3664349 = 1374131) B1374131
theorem B1632791 : Blo 964590 1632791 := bstep (se 1 (by rfl) ⟨1224593, by rfl⟩ : syracuseStep 1632791 = 2449187) B2449187
theorem B1305163 : Blo 964590 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B5499485 : Blo 964590 5499485 := bstep (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) B2062307
theorem B1632919 : Blo 964590 1632919 := bstep (se 1 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 1632919 = 2449379) B2449379
theorem B17656471 : Blo 964590 17656471 := bstep (se 1 (by rfl) ⟨13242353, by rfl⟩ : syracuseStep 17656471 = 26484707) B26484707
theorem B4123315 : Blo 964590 4123315 := bstep (se 1 (by rfl) ⟨3092486, by rfl⟩ : syracuseStep 4123315 = 6184973) B6184973
theorem B1862347 : Blo 964590 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B2616371 : Blo 964590 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B3665047 : Blo 964590 3665047 := bstep (se 1 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 3665047 = 5497571) B5497571
theorem B1633547 : Blo 964590 1633547 := bstep (se 1 (by rfl) ⟨1225160, by rfl⟩ : syracuseStep 1633547 = 2450321) B2450321
theorem B5303627 : Blo 964590 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B22310261 : Blo 964590 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B1633675 : Blo 964590 1633675 := bstep (se 1 (by rfl) ⟨1225256, by rfl⟩ : syracuseStep 1633675 = 2450513) B2450513
theorem B1469963 : Blo 964590 1469963 := bstep (se 1 (by rfl) ⟨1102472, by rfl⟩ : syracuseStep 1469963 = 2204945) B2204945
theorem B1633817 : Blo 964590 1633817 := bstep (se 2 (by rfl) ⟨612681, by rfl⟩ : syracuseStep 1633817 = 1225363) B1225363
theorem B1306201 : Blo 964590 1306201 := bstep (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) B979651
theorem B1633945 : Blo 964590 1633945 := bstep (se 2 (by rfl) ⟨612729, by rfl⟩ : syracuseStep 1633945 = 1225459) B1225459
theorem B6188845 : Blo 964590 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B2060147 : Blo 964590 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B3665837 : Blo 964590 3665837 := bstep (se 3 (by rfl) ⟨687344, by rfl⟩ : syracuseStep 3665837 = 1374689) B1374689
theorem B2748467 : Blo 964590 2748467 := bstep (se 1 (by rfl) ⟨2061350, by rfl⟩ : syracuseStep 2748467 = 4122701) B4122701
theorem B4124803 : Blo 964590 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B2060633 : Blo 964590 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1470935 : Blo 964590 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B1831385 : Blo 964590 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B8811013 : Blo 964590 8811013 := bstep (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) B1652065
theorem B4125401 : Blo 964590 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B1962739 : Blo 964590 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B1962803 : Blo 964590 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B4125761 : Blo 964590 4125761 := bstep (se 2 (by rfl) ⟨1547160, by rfl⟩ : syracuseStep 4125761 = 3094321) B3094321
theorem B10613911 : Blo 964590 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B1832129 : Blo 964590 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B3667265 : Blo 964590 3667265 := bstep (se 2 (by rfl) ⟨1375224, by rfl⟩ : syracuseStep 3667265 = 2750449) B2750449
theorem B980299 : Blo 964590 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B1373527 : Blo 964590 1373527 := bstep (se 1 (by rfl) ⟨1030145, by rfl⟩ : syracuseStep 1373527 = 2060291) B2060291
theorem B1832395 : Blo 964590 1832395 := bstep (se 1 (by rfl) ⟨1374296, by rfl⟩ : syracuseStep 1832395 = 2748593) B2748593
theorem B1046071 : Blo 964590 1046071 := bstep (se 1 (by rfl) ⟨784553, by rfl⟩ : syracuseStep 1046071 = 1569107) B1569107
theorem B2094913 : Blo 964590 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1832843 : Blo 964590 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B2062273 : Blo 964590 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B1833025 : Blo 964590 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B8255789 : Blo 964590 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B4651339 : Blo 964590 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B2324825 : Blo 964590 2324825 := bstep (se 2 (by rfl) ⟨871809, by rfl⟩ : syracuseStep 2324825 = 1743619) B1743619
theorem B1833367 : Blo 964590 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B13236659 : Blo 964590 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B1833587 : Blo 964590 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B2751155 : Blo 964590 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B3668753 : Blo 964590 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1833815 : Blo 964590 1833815 := bstep (se 1 (by rfl) ⟨1375361, by rfl⟩ : syracuseStep 1833815 = 2750723) B2750723
theorem B2751383 : Blo 964590 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B7830451 : Blo 964590 7830451 := bstep (se 1 (by rfl) ⟨5872838, by rfl⟩ : syracuseStep 7830451 = 11745677) B11745677
theorem B4651955 : Blo 964590 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B1834073 : Blo 964590 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B2751691 : Blo 964590 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B3669209 : Blo 964590 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B13958405 : Blo 964590 13958405 := bstep (se 4 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 13958405 = 2617201) B2617201
theorem B3669421 : Blo 964590 3669421 := bstep (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) B1376033
theorem B2751965 : Blo 964590 2751965 := bstep (se 3 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 2751965 = 1031987) B1031987
theorem B1834483 : Blo 964590 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B3964439 : Blo 964590 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B2096779 : Blo 964590 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B3669725 : Blo 964590 3669725 := bstep (se 3 (by rfl) ⟨688073, by rfl⟩ : syracuseStep 3669725 = 1376147) B1376147
theorem B2064179 : Blo 964590 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B5504861 : Blo 964590 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B18087857 : Blo 964590 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B1834969 : Blo 964590 1834969 := bstep (se 2 (by rfl) ⟨688113, by rfl⟩ : syracuseStep 1834969 = 1376227) B1376227
theorem B6979607 : Blo 964590 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B1376443 : Blo 964590 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B5505317 : Blo 964590 5505317 := bstep (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) B1032247
theorem B2064683 : Blo 964590 2064683 := bstep (se 1 (by rfl) ⟨1548512, by rfl⟩ : syracuseStep 2064683 = 3097025) B3097025
theorem B2326843 : Blo 964590 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B4129177 : Blo 964590 4129177 := bstep (se 2 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 4129177 = 3096883) B3096883
theorem B4653571 : Blo 964590 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B1376939 : Blo 964590 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B19104437 : Blo 964590 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B5506001 : Blo 964590 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B1836047 : Blo 964590 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B5506319 : Blo 964590 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1836587 : Blo 964590 1836587 := bstep (se 1 (by rfl) ⟨1377440, by rfl⟩ : syracuseStep 1836587 = 2754881) B2754881
theorem B3671639 : Blo 964590 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B9274999 : Blo 964590 9274999 := bstep (se 1 (by rfl) ⟨6956249, by rfl⟩ : syracuseStep 9274999 = 13912499) B13912499
theorem B4130423 : Blo 964590 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B11142947 : Blo 964590 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B1738631 : Blo 964590 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B2066323 : Blo 964590 2066323 := bstep (se 1 (by rfl) ⟨1549742, by rfl⟩ : syracuseStep 2066323 = 3099485) B3099485
theorem B3672125 : Blo 964590 3672125 := bstep (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) B1377047
theorem B5867639 : Blo 964590 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1378505 : Blo 964590 1378505 := bstep (se 2 (by rfl) ⟨516939, by rfl⟩ : syracuseStep 1378505 = 1033879) B1033879
theorem B2755073 : Blo 964590 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B8260163 : Blo 964590 8260163 := bstep (se 1 (by rfl) ⟨6195122, by rfl⟩ : syracuseStep 8260163 = 12390245) B12390245
theorem B1837703 : Blo 964590 1837703 := bstep (se 1 (by rfl) ⟨1378277, by rfl⟩ : syracuseStep 1837703 = 2756555) B2756555
theorem B5507777 : Blo 964590 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B1379063 : Blo 964590 1379063 := bstep (se 1 (by rfl) ⟨1034297, by rfl⟩ : syracuseStep 1379063 = 2068595) B2068595
theorem B1739639 : Blo 964590 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B4885433 : Blo 964590 4885433 := bstep (se 2 (by rfl) ⟨1832037, by rfl⟩ : syracuseStep 4885433 = 3664075) B3664075
theorem B2755529 : Blo 964590 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B14126167 : Blo 964590 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B1838227 : Blo 964590 1838227 := bstep (se 1 (by rfl) ⟨1378670, by rfl⟩ : syracuseStep 1838227 = 2757341) B2757341
theorem B2755883 : Blo 964590 2755883 := bstep (se 1 (by rfl) ⟨2066912, by rfl⟩ : syracuseStep 2755883 = 4133825) B4133825
theorem B1740217 : Blo 964590 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B1740331 : Blo 964590 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B2756281 : Blo 964590 2756281 := bstep (se 2 (by rfl) ⟨1033605, by rfl⟩ : syracuseStep 2756281 = 2067211) B2067211
theorem B3477433 : Blo 964590 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B1085575 : Blo 964590 1085575 := bstep (se 1 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 1085575 = 1628363) B1628363
theorem B4886729 : Blo 964590 4886729 := bstep (se 2 (by rfl) ⟨1832523, by rfl⟩ : syracuseStep 4886729 = 3665047) B3665047
theorem B22647053 : Blo 964590 22647053 := bstep (se 3 (by rfl) ⟨4246322, by rfl⟩ : syracuseStep 22647053 = 8492645) B8492645
theorem B1085755 : Blo 964590 1085755 := bstep (se 1 (by rfl) ⟨814316, by rfl⟩ : syracuseStep 1085755 = 1628633) B1628633
theorem B1086223 : Blo 964590 1086223 := bstep (se 1 (by rfl) ⟨814667, by rfl⟩ : syracuseStep 1086223 = 1629335) B1629335
theorem B1741601 : Blo 964590 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B2757523 : Blo 964590 2757523 := bstep (se 1 (by rfl) ⟨2068142, by rfl⟩ : syracuseStep 2757523 = 4136285) B4136285
theorem B1545161 : Blo 964590 1545161 := bstep (se 2 (by rfl) ⟨579435, by rfl⟩ : syracuseStep 1545161 = 1158871) B1158871
theorem B1446971 : Blo 964590 1446971 := bstep (se 1 (by rfl) ⟨1085228, by rfl⟩ : syracuseStep 1446971 = 2170457) B2170457
theorem B1447031 : Blo 964590 1447031 := bstep (se 1 (by rfl) ⟨1085273, by rfl⟩ : syracuseStep 1447031 = 2170547) B2170547
theorem B1447055 : Blo 964590 1447055 := bstep (se 1 (by rfl) ⟨1085291, by rfl⟩ : syracuseStep 1447055 = 2170583) B2170583
theorem B1447097 : Blo 964590 1447097 := bstep (se 2 (by rfl) ⟨542661, by rfl⟩ : syracuseStep 1447097 = 1085323) B1085323
theorem B1447175 : Blo 964590 1447175 := bstep (se 1 (by rfl) ⟨1085381, by rfl⟩ : syracuseStep 1447175 = 2170763) B2170763
theorem B1086727 : Blo 964590 1086727 := bstep (se 1 (by rfl) ⟨815045, by rfl⟩ : syracuseStep 1086727 = 1630091) B1630091
theorem B3478817 : Blo 964590 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B1447211 : Blo 964590 1447211 := bstep (se 1 (by rfl) ⟨1085408, by rfl⟩ : syracuseStep 1447211 = 2170817) B2170817
theorem B2790715 : Blo 964590 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B1447241 : Blo 964590 1447241 := bstep (se 2 (by rfl) ⟨542715, by rfl⟩ : syracuseStep 1447241 = 1085431) B1085431
theorem B3675527 : Blo 964590 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B1447355 : Blo 964590 1447355 := bstep (se 1 (by rfl) ⟨1085516, by rfl⟩ : syracuseStep 1447355 = 2171033) B2171033
theorem B1086907 : Blo 964590 1086907 := bstep (se 1 (by rfl) ⟨815180, by rfl⟩ : syracuseStep 1086907 = 1630361) B1630361
theorem B1447415 : Blo 964590 1447415 := bstep (se 1 (by rfl) ⟨1085561, by rfl⟩ : syracuseStep 1447415 = 2171123) B2171123
theorem B1447439 : Blo 964590 1447439 := bstep (se 1 (by rfl) ⟨1085579, by rfl⟩ : syracuseStep 1447439 = 2171159) B2171159
theorem B1447481 : Blo 964590 1447481 := bstep (se 2 (by rfl) ⟨542805, by rfl⟩ : syracuseStep 1447481 = 1085611) B1085611
theorem B3479107 : Blo 964590 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B1447559 : Blo 964590 1447559 := bstep (se 1 (by rfl) ⟨1085669, by rfl⟩ : syracuseStep 1447559 = 2171339) B2171339
theorem B1447595 : Blo 964590 1447595 := bstep (se 1 (by rfl) ⟨1085696, by rfl⟩ : syracuseStep 1447595 = 2171393) B2171393
theorem B1447625 : Blo 964590 1447625 := bstep (se 2 (by rfl) ⟨542859, by rfl⟩ : syracuseStep 1447625 = 1085719) B1085719
theorem B1447739 : Blo 964590 1447739 := bstep (se 1 (by rfl) ⟨1085804, by rfl⟩ : syracuseStep 1447739 = 2171609) B2171609
theorem B1447799 : Blo 964590 1447799 := bstep (se 1 (by rfl) ⟨1085849, by rfl⟩ : syracuseStep 1447799 = 2171699) B2171699
theorem B1546103 : Blo 964590 1546103 := bstep (se 1 (by rfl) ⟨1159577, by rfl⟩ : syracuseStep 1546103 = 2319155) B2319155
theorem B1447823 : Blo 964590 1447823 := bstep (se 1 (by rfl) ⟨1085867, by rfl⟩ : syracuseStep 1447823 = 2171735) B2171735
theorem B1087375 : Blo 964590 1087375 := bstep (se 1 (by rfl) ⟨815531, by rfl⟩ : syracuseStep 1087375 = 1631063) B1631063
theorem B1447865 : Blo 964590 1447865 := bstep (se 2 (by rfl) ⟨542949, by rfl⟩ : syracuseStep 1447865 = 1085899) B1085899
theorem B1447943 : Blo 964590 1447943 := bstep (se 1 (by rfl) ⟨1085957, by rfl⟩ : syracuseStep 1447943 = 2171915) B2171915
theorem B1447979 : Blo 964590 1447979 := bstep (se 1 (by rfl) ⟨1085984, by rfl⟩ : syracuseStep 1447979 = 2171969) B2171969
theorem B1448009 : Blo 964590 1448009 := bstep (se 2 (by rfl) ⟨543003, by rfl⟩ : syracuseStep 1448009 = 1086007) B1086007
theorem B39688309 : Blo 964590 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B8263853 : Blo 964590 8263853 := bstep (se 3 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 8263853 = 3098945) B3098945
theorem B1448123 : Blo 964590 1448123 := bstep (se 1 (by rfl) ⟨1086092, by rfl⟩ : syracuseStep 1448123 = 2172185) B2172185
theorem B1448183 : Blo 964590 1448183 := bstep (se 1 (by rfl) ⟨1086137, by rfl⟩ : syracuseStep 1448183 = 2172275) B2172275
theorem B1448207 : Blo 964590 1448207 := bstep (se 1 (by rfl) ⟨1086155, by rfl⟩ : syracuseStep 1448207 = 2172311) B2172311
theorem B1448249 : Blo 964590 1448249 := bstep (se 2 (by rfl) ⟨543093, by rfl⟩ : syracuseStep 1448249 = 1086187) B1086187
theorem B5970235 : Blo 964590 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1448327 : Blo 964590 1448327 := bstep (se 1 (by rfl) ⟨1086245, by rfl⟩ : syracuseStep 1448327 = 2172491) B2172491
theorem B1087879 : Blo 964590 1087879 := bstep (se 1 (by rfl) ⟨815909, by rfl⟩ : syracuseStep 1087879 = 1631819) B1631819
theorem B1448363 : Blo 964590 1448363 := bstep (se 1 (by rfl) ⟨1086272, by rfl⟩ : syracuseStep 1448363 = 2172545) B2172545
theorem B4954553 : Blo 964590 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B1448393 : Blo 964590 1448393 := bstep (se 2 (by rfl) ⟨543147, by rfl⟩ : syracuseStep 1448393 = 1086295) B1086295
theorem B6265387 : Blo 964590 6265387 := bstep (se 1 (by rfl) ⟨4699040, by rfl⟩ : syracuseStep 6265387 = 9398081) B9398081
theorem B1088059 : Blo 964590 1088059 := bstep (se 1 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 1088059 = 1632089) B1632089
theorem B1448507 : Blo 964590 1448507 := bstep (se 1 (by rfl) ⟨1086380, by rfl⟩ : syracuseStep 1448507 = 2172761) B2172761
theorem B1448567 : Blo 964590 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B1448591 : Blo 964590 1448591 := bstep (se 1 (by rfl) ⟨1086443, by rfl⟩ : syracuseStep 1448591 = 2172887) B2172887
theorem B1448633 : Blo 964590 1448633 := bstep (se 2 (by rfl) ⟨543237, by rfl⟩ : syracuseStep 1448633 = 1086475) B1086475
theorem B1448711 : Blo 964590 1448711 := bstep (se 1 (by rfl) ⟨1086533, by rfl⟩ : syracuseStep 1448711 = 2173067) B2173067
theorem B1448747 : Blo 964590 1448747 := bstep (se 1 (by rfl) ⟨1086560, by rfl⟩ : syracuseStep 1448747 = 2173121) B2173121
theorem B1448777 : Blo 964590 1448777 := bstep (se 2 (by rfl) ⟨543291, by rfl⟩ : syracuseStep 1448777 = 1086583) B1086583
theorem B8264537 : Blo 964590 8264537 := bstep (se 2 (by rfl) ⟨3099201, by rfl⟩ : syracuseStep 8264537 = 6198403) B6198403
theorem B1743763 : Blo 964590 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B2202553 : Blo 964590 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1448891 : Blo 964590 1448891 := bstep (se 1 (by rfl) ⟨1086668, by rfl⟩ : syracuseStep 1448891 = 2173337) B2173337
theorem B1448951 : Blo 964590 1448951 := bstep (se 1 (by rfl) ⟨1086713, by rfl⟩ : syracuseStep 1448951 = 2173427) B2173427
theorem B1448975 : Blo 964590 1448975 := bstep (se 1 (by rfl) ⟨1086731, by rfl⟩ : syracuseStep 1448975 = 2173463) B2173463
theorem B1088527 : Blo 964590 1088527 := bstep (se 1 (by rfl) ⟨816395, by rfl⟩ : syracuseStep 1088527 = 1632791) B1632791
theorem B1449017 : Blo 964590 1449017 := bstep (se 2 (by rfl) ⟨543381, by rfl⟩ : syracuseStep 1449017 = 1086763) B1086763
theorem B1449095 : Blo 964590 1449095 := bstep (se 1 (by rfl) ⟨1086821, by rfl⟩ : syracuseStep 1449095 = 2173643) B2173643
theorem B1449131 : Blo 964590 1449131 := bstep (se 1 (by rfl) ⟨1086848, by rfl⟩ : syracuseStep 1449131 = 2173697) B2173697
theorem B1449161 : Blo 964590 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B1449275 : Blo 964590 1449275 := bstep (se 1 (by rfl) ⟨1086956, by rfl⟩ : syracuseStep 1449275 = 2173913) B2173913
theorem B1449335 : Blo 964590 1449335 := bstep (se 1 (by rfl) ⟨1087001, by rfl⟩ : syracuseStep 1449335 = 2174003) B2174003
theorem B1744247 : Blo 964590 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B1449359 : Blo 964590 1449359 := bstep (se 1 (by rfl) ⟨1087019, by rfl⟩ : syracuseStep 1449359 = 2174039) B2174039
theorem B1449401 : Blo 964590 1449401 := bstep (se 2 (by rfl) ⟨543525, by rfl⟩ : syracuseStep 1449401 = 1087051) B1087051
theorem B1449479 : Blo 964590 1449479 := bstep (se 1 (by rfl) ⟨1087109, by rfl⟩ : syracuseStep 1449479 = 2174219) B2174219
theorem B1089031 : Blo 964590 1089031 := bstep (se 1 (by rfl) ⟨816773, by rfl⟩ : syracuseStep 1089031 = 1633547) B1633547
theorem B1449515 : Blo 964590 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B1449545 : Blo 964590 1449545 := bstep (se 2 (by rfl) ⟨543579, by rfl⟩ : syracuseStep 1449545 = 1087159) B1087159
theorem B1449659 : Blo 964590 1449659 := bstep (se 1 (by rfl) ⟨1087244, by rfl⟩ : syracuseStep 1449659 = 2174489) B2174489
theorem B1089211 : Blo 964590 1089211 := bstep (se 1 (by rfl) ⟨816908, by rfl⟩ : syracuseStep 1089211 = 1633817) B1633817
theorem B2203337 : Blo 964590 2203337 := bstep (se 2 (by rfl) ⟨826251, by rfl⟩ : syracuseStep 2203337 = 1652503) B1652503
theorem B1449719 : Blo 964590 1449719 := bstep (se 1 (by rfl) ⟨1087289, by rfl⟩ : syracuseStep 1449719 = 2174579) B2174579
theorem B2793217 : Blo 964590 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1449743 : Blo 964590 1449743 := bstep (se 1 (by rfl) ⟨1087307, by rfl⟩ : syracuseStep 1449743 = 2174615) B2174615
theorem B1449785 : Blo 964590 1449785 := bstep (se 2 (by rfl) ⟨543669, by rfl⟩ : syracuseStep 1449785 = 1087339) B1087339
theorem B1449863 : Blo 964590 1449863 := bstep (se 1 (by rfl) ⟨1087397, by rfl⟩ : syracuseStep 1449863 = 2174795) B2174795
theorem B1449899 : Blo 964590 1449899 := bstep (se 1 (by rfl) ⟨1087424, by rfl⟩ : syracuseStep 1449899 = 2174849) B2174849
theorem B1449929 : Blo 964590 1449929 := bstep (se 2 (by rfl) ⟨543723, by rfl⟩ : syracuseStep 1449929 = 1087447) B1087447
theorem B1450043 : Blo 964590 1450043 := bstep (se 1 (by rfl) ⟨1087532, by rfl⟩ : syracuseStep 1450043 = 2175065) B2175065
theorem B1450103 : Blo 964590 1450103 := bstep (se 1 (by rfl) ⟨1087577, by rfl⟩ : syracuseStep 1450103 = 2175155) B2175155
theorem B2171015 : Blo 964590 2171015 := bstep (se 1 (by rfl) ⟨1628261, by rfl⟩ : syracuseStep 2171015 = 3256523) B3256523
theorem B1450127 : Blo 964590 1450127 := bstep (se 1 (by rfl) ⟨1087595, by rfl⟩ : syracuseStep 1450127 = 2175191) B2175191
theorem B1450169 : Blo 964590 1450169 := bstep (se 2 (by rfl) ⟨543813, by rfl⟩ : syracuseStep 1450169 = 1087627) B1087627
theorem B1450247 : Blo 964590 1450247 := bstep (se 1 (by rfl) ⟨1087685, by rfl⟩ : syracuseStep 1450247 = 2175371) B2175371
theorem B1450283 : Blo 964590 1450283 := bstep (se 1 (by rfl) ⟨1087712, by rfl⟩ : syracuseStep 1450283 = 2175425) B2175425
theorem B1220923 : Blo 964590 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B2171195 : Blo 964590 2171195 := bstep (se 1 (by rfl) ⟨1628396, by rfl⟩ : syracuseStep 2171195 = 3256793) B3256793
theorem B1450313 : Blo 964590 1450313 := bstep (se 2 (by rfl) ⟨543867, by rfl⟩ : syracuseStep 1450313 = 1087735) B1087735
theorem B2171321 : Blo 964590 2171321 := bstep (se 2 (by rfl) ⟨814245, by rfl⟩ : syracuseStep 2171321 = 1628491) B1628491
theorem B6201785 : Blo 964590 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B1450427 : Blo 964590 1450427 := bstep (se 1 (by rfl) ⟨1087820, by rfl⟩ : syracuseStep 1450427 = 2175641) B2175641
theorem B1450487 : Blo 964590 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B1450511 : Blo 964590 1450511 := bstep (se 1 (by rfl) ⟨1087883, by rfl⟩ : syracuseStep 1450511 = 2175767) B2175767
theorem B1450553 : Blo 964590 1450553 := bstep (se 2 (by rfl) ⟨543957, by rfl⟩ : syracuseStep 1450553 = 1087915) B1087915
theorem B11936321 : Blo 964590 11936321 := bstep (se 2 (by rfl) ⟨4476120, by rfl⟩ : syracuseStep 11936321 = 8952241) B8952241
theorem B1450631 : Blo 964590 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B1450667 : Blo 964590 1450667 := bstep (se 1 (by rfl) ⟨1088000, by rfl⟩ : syracuseStep 1450667 = 2176001) B2176001
theorem B1450697 : Blo 964590 1450697 := bstep (se 2 (by rfl) ⟨544011, by rfl⟩ : syracuseStep 1450697 = 1088023) B1088023
theorem B2171663 : Blo 964590 2171663 := bstep (se 1 (by rfl) ⟨1628747, by rfl⟩ : syracuseStep 2171663 = 3257495) B3257495
theorem B2171681 : Blo 964590 2171681 := bstep (se 2 (by rfl) ⟨814380, by rfl⟩ : syracuseStep 2171681 = 1628761) B1628761
theorem B1221419 : Blo 964590 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B1450811 : Blo 964590 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B1450871 : Blo 964590 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B1450895 : Blo 964590 1450895 := bstep (se 1 (by rfl) ⟨1088171, by rfl⟩ : syracuseStep 1450895 = 2176343) B2176343
theorem B1450937 : Blo 964590 1450937 := bstep (se 2 (by rfl) ⟨544101, by rfl⟩ : syracuseStep 1450937 = 1088203) B1088203
theorem B1451015 : Blo 964590 1451015 := bstep (se 1 (by rfl) ⟨1088261, by rfl⟩ : syracuseStep 1451015 = 2176523) B2176523
theorem B1451051 : Blo 964590 1451051 := bstep (se 1 (by rfl) ⟨1088288, by rfl⟩ : syracuseStep 1451051 = 2176577) B2176577
theorem B1451081 : Blo 964590 1451081 := bstep (se 2 (by rfl) ⟨544155, by rfl⟩ : syracuseStep 1451081 = 1088311) B1088311
theorem B2172023 : Blo 964590 2172023 := bstep (se 1 (by rfl) ⟨1629017, by rfl⟩ : syracuseStep 2172023 = 3258035) B3258035
theorem B1451195 : Blo 964590 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B1451255 : Blo 964590 1451255 := bstep (se 1 (by rfl) ⟨1088441, by rfl⟩ : syracuseStep 1451255 = 2176883) B2176883
theorem B1221895 : Blo 964590 1221895 := bstep (se 1 (by rfl) ⟨916421, by rfl⟩ : syracuseStep 1221895 = 1832843) B1832843
theorem B1451279 : Blo 964590 1451279 := bstep (se 1 (by rfl) ⟨1088459, by rfl⟩ : syracuseStep 1451279 = 2176919) B2176919
theorem B2172203 : Blo 964590 2172203 := bstep (se 1 (by rfl) ⟨1629152, by rfl⟩ : syracuseStep 2172203 = 3258305) B3258305
theorem B1451321 : Blo 964590 1451321 := bstep (se 2 (by rfl) ⟨544245, by rfl⟩ : syracuseStep 1451321 = 1088491) B1088491
theorem B2237755 : Blo 964590 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B1451399 : Blo 964590 1451399 := bstep (se 1 (by rfl) ⟨1088549, by rfl⟩ : syracuseStep 1451399 = 2177099) B2177099
theorem B1451435 : Blo 964590 1451435 := bstep (se 1 (by rfl) ⟨1088576, by rfl⟩ : syracuseStep 1451435 = 2177153) B2177153
theorem B1451465 : Blo 964590 1451465 := bstep (se 2 (by rfl) ⟨544299, by rfl⟩ : syracuseStep 1451465 = 1088599) B1088599
theorem B1549883 : Blo 964590 1549883 := bstep (se 1 (by rfl) ⟨1162412, by rfl⟩ : syracuseStep 1549883 = 2324825) B2324825
theorem B1451579 : Blo 964590 1451579 := bstep (se 1 (by rfl) ⟨1088684, by rfl⟩ : syracuseStep 1451579 = 2177369) B2177369
theorem B8824439 : Blo 964590 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B1451639 : Blo 964590 1451639 := bstep (se 1 (by rfl) ⟨1088729, by rfl⟩ : syracuseStep 1451639 = 2177459) B2177459
theorem B1451663 : Blo 964590 1451663 := bstep (se 1 (by rfl) ⟨1088747, by rfl⟩ : syracuseStep 1451663 = 2177495) B2177495
theorem B2172563 : Blo 964590 2172563 := bstep (se 1 (by rfl) ⟨1629422, by rfl⟩ : syracuseStep 2172563 = 3258845) B3258845
theorem B1451705 : Blo 964590 1451705 := bstep (se 2 (by rfl) ⟨544389, by rfl⟩ : syracuseStep 1451705 = 1088779) B1088779
theorem B2172617 : Blo 964590 2172617 := bstep (se 2 (by rfl) ⟨814731, by rfl⟩ : syracuseStep 2172617 = 1629463) B1629463
theorem B1222391 : Blo 964590 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B1451783 : Blo 964590 1451783 := bstep (se 1 (by rfl) ⟨1088837, by rfl⟩ : syracuseStep 1451783 = 2177675) B2177675
theorem B1451819 : Blo 964590 1451819 := bstep (se 1 (by rfl) ⟨1088864, by rfl⟩ : syracuseStep 1451819 = 2177729) B2177729
theorem B5515067 : Blo 964590 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B1451849 : Blo 964590 1451849 := bstep (se 2 (by rfl) ⟨544443, by rfl⟩ : syracuseStep 1451849 = 1088887) B1088887
theorem B1222543 : Blo 964590 1222543 := bstep (se 1 (by rfl) ⟨916907, by rfl⟩ : syracuseStep 1222543 = 1833815) B1833815
theorem B4892561 : Blo 964590 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B1451963 : Blo 964590 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B1452023 : Blo 964590 1452023 := bstep (se 1 (by rfl) ⟨1089017, by rfl⟩ : syracuseStep 1452023 = 2178035) B2178035
theorem B1452047 : Blo 964590 1452047 := bstep (se 1 (by rfl) ⟨1089035, by rfl⟩ : syracuseStep 1452047 = 2178071) B2178071
theorem B1452089 : Blo 964590 1452089 := bstep (se 2 (by rfl) ⟨544533, by rfl⟩ : syracuseStep 1452089 = 1089067) B1089067
theorem B1222715 : Blo 964590 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1452167 : Blo 964590 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B1452203 : Blo 964590 1452203 := bstep (se 1 (by rfl) ⟨1089152, by rfl⟩ : syracuseStep 1452203 = 2178305) B2178305
theorem B2795705 : Blo 964590 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B1452233 : Blo 964590 1452233 := bstep (se 2 (by rfl) ⟨544587, by rfl⟩ : syracuseStep 1452233 = 1089175) B1089175
theorem B993551 : Blo 964590 993551 := bstep (se 1 (by rfl) ⟨745163, by rfl⟩ : syracuseStep 993551 = 1490327) B1490327
theorem B1452347 : Blo 964590 1452347 := bstep (se 1 (by rfl) ⟨1089260, by rfl⟩ : syracuseStep 1452347 = 2178521) B2178521
theorem B1452407 : Blo 964590 1452407 := bstep (se 1 (by rfl) ⟨1089305, by rfl⟩ : syracuseStep 1452407 = 2178611) B2178611
theorem B2173319 : Blo 964590 2173319 := bstep (se 1 (by rfl) ⟨1629989, by rfl⟩ : syracuseStep 2173319 = 3259979) B3259979
theorem B1452431 : Blo 964590 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B1452473 : Blo 964590 1452473 := bstep (se 2 (by rfl) ⟨544677, by rfl⟩ : syracuseStep 1452473 = 1089355) B1089355
theorem B6957521 : Blo 964590 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B7350749 : Blo 964590 7350749 := bstep (se 3 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 7350749 = 2756531) B2756531
theorem B1452551 : Blo 964590 1452551 := bstep (se 1 (by rfl) ⟨1089413, by rfl⟩ : syracuseStep 1452551 = 2178827) B2178827
theorem B1452587 : Blo 964590 1452587 := bstep (se 1 (by rfl) ⟨1089440, by rfl⟩ : syracuseStep 1452587 = 2178881) B2178881
theorem B2173499 : Blo 964590 2173499 := bstep (se 1 (by rfl) ⟨1630124, by rfl⟩ : syracuseStep 2173499 = 3260249) B3260249
theorem B1452617 : Blo 964590 1452617 := bstep (se 2 (by rfl) ⟨544731, by rfl⟩ : syracuseStep 1452617 = 1089463) B1089463
theorem B2173625 : Blo 964590 2173625 := bstep (se 2 (by rfl) ⟨815109, by rfl⟩ : syracuseStep 2173625 = 1630219) B1630219
theorem B1452731 : Blo 964590 1452731 := bstep (se 1 (by rfl) ⟨1089548, by rfl⟩ : syracuseStep 1452731 = 2179097) B2179097
theorem B1452791 : Blo 964590 1452791 := bstep (se 1 (by rfl) ⟨1089593, by rfl⟩ : syracuseStep 1452791 = 2179187) B2179187
theorem B6957839 : Blo 964590 6957839 := bstep (se 1 (by rfl) ⟨5218379, by rfl⟩ : syracuseStep 6957839 = 10436759) B10436759
theorem B1452815 : Blo 964590 1452815 := bstep (se 1 (by rfl) ⟨1089611, by rfl⟩ : syracuseStep 1452815 = 2179223) B2179223
theorem B1452857 : Blo 964590 1452857 := bstep (se 2 (by rfl) ⟨544821, by rfl⟩ : syracuseStep 1452857 = 1089643) B1089643
theorem B3091385 : Blo 964590 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B1223687 : Blo 964590 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B8825867 : Blo 964590 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B2173967 : Blo 964590 2173967 := bstep (se 1 (by rfl) ⟨1630475, by rfl⟩ : syracuseStep 2173967 = 3260951) B3260951
theorem B2173985 : Blo 964590 2173985 := bstep (se 2 (by rfl) ⟨815244, by rfl⟩ : syracuseStep 2173985 = 1630489) B1630489
theorem B3255497 : Blo 964590 3255497 := bstep (se 2 (by rfl) ⟨1220811, by rfl⟩ : syracuseStep 3255497 = 2441623) B2441623
theorem B2174327 : Blo 964590 2174327 := bstep (se 1 (by rfl) ⟨1630745, by rfl⟩ : syracuseStep 2174327 = 3261491) B3261491
theorem B10988945 : Blo 964590 10988945 := bstep (se 2 (by rfl) ⟨4120854, by rfl⟩ : syracuseStep 10988945 = 8241709) B8241709
theorem B2174507 : Blo 964590 2174507 := bstep (se 1 (by rfl) ⟨1630880, by rfl⟩ : syracuseStep 2174507 = 3261761) B3261761
theorem B1224335 : Blo 964590 1224335 := bstep (se 1 (by rfl) ⟨918251, by rfl⟩ : syracuseStep 1224335 = 1836503) B1836503
theorem B3256199 : Blo 964590 3256199 := bstep (se 1 (by rfl) ⟨2442149, by rfl⟩ : syracuseStep 3256199 = 4884299) B4884299
theorem B2174867 : Blo 964590 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B2174921 : Blo 964590 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B4894667 : Blo 964590 4894667 := bstep (se 1 (by rfl) ⟨3671000, by rfl⟩ : syracuseStep 4894667 = 7342001) B7342001
theorem B3092681 : Blo 964590 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B3256577 : Blo 964590 3256577 := bstep (se 2 (by rfl) ⟨1221216, by rfl⟩ : syracuseStep 3256577 = 2442433) B2442433
theorem B4894991 : Blo 964590 4894991 := bstep (se 1 (by rfl) ⟨3671243, by rfl⟩ : syracuseStep 4894991 = 7342487) B7342487
theorem B3092795 : Blo 964590 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B1651259 : Blo 964590 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B2175623 : Blo 964590 2175623 := bstep (se 1 (by rfl) ⟨1631717, by rfl⟩ : syracuseStep 2175623 = 3263435) B3263435
theorem B5288719 : Blo 964590 5288719 := bstep (se 1 (by rfl) ⟨3966539, by rfl⟩ : syracuseStep 5288719 = 7933079) B7933079
theorem B2175803 : Blo 964590 2175803 := bstep (se 1 (by rfl) ⟨1631852, by rfl⟩ : syracuseStep 2175803 = 3263705) B3263705
theorem B5583761 : Blo 964590 5583761 := bstep (se 2 (by rfl) ⟨2093910, by rfl⟩ : syracuseStep 5583761 = 4187821) B4187821
theorem B2175929 : Blo 964590 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B13218821 : Blo 964590 13218821 := bstep (se 4 (by rfl) ⟨1239264, by rfl⟩ : syracuseStep 13218821 = 2478529) B2478529
theorem B3257387 : Blo 964590 3257387 := bstep (se 1 (by rfl) ⟨2443040, by rfl⟩ : syracuseStep 3257387 = 4886081) B4886081
theorem B2176271 : Blo 964590 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B2176289 : Blo 964590 2176289 := bstep (se 2 (by rfl) ⟨816108, by rfl⟩ : syracuseStep 2176289 = 1632217) B1632217
theorem B26490397 : Blo 964590 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B4404779 : Blo 964590 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B11023937 : Blo 964590 11023937 := bstep (se 2 (by rfl) ⟨4133976, by rfl⟩ : syracuseStep 11023937 = 8267953) B8267953
theorem B2176631 : Blo 964590 2176631 := bstep (se 1 (by rfl) ⟨1632473, by rfl⟩ : syracuseStep 2176631 = 3264947) B3264947
theorem B4896449 : Blo 964590 4896449 := bstep (se 2 (by rfl) ⟨1836168, by rfl⟩ : syracuseStep 4896449 = 3672337) B3672337
theorem B9287459 : Blo 964590 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B2176811 : Blo 964590 2176811 := bstep (se 1 (by rfl) ⟨1632608, by rfl⟩ : syracuseStep 2176811 = 3265217) B3265217
theorem B964615 : Blo 964590 964615 := bstep (se 1 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 964615 = 1446923) B1446923
theorem B964623 : Blo 964590 964623 := bstep (se 1 (by rfl) ⟨723467, by rfl⟩ : syracuseStep 964623 = 1446935) B1446935
theorem B964667 : Blo 964590 964667 := bstep (se 1 (by rfl) ⟨723500, by rfl⟩ : syracuseStep 964667 = 1447001) B1447001
theorem B964743 : Blo 964590 964743 := bstep (se 1 (by rfl) ⟨723557, by rfl⟩ : syracuseStep 964743 = 1447115) B1447115
theorem B964751 : Blo 964590 964751 := bstep (se 1 (by rfl) ⟨723563, by rfl⟩ : syracuseStep 964751 = 1447127) B1447127
theorem B2177171 : Blo 964590 2177171 := bstep (se 1 (by rfl) ⟨1632878, by rfl⟩ : syracuseStep 2177171 = 3265757) B3265757
theorem B964795 : Blo 964590 964795 := bstep (se 1 (by rfl) ⟨723596, by rfl⟩ : syracuseStep 964795 = 1447193) B1447193
theorem B2177225 : Blo 964590 2177225 := bstep (se 2 (by rfl) ⟨816459, by rfl⟩ : syracuseStep 2177225 = 1632919) B1632919
theorem B23541961 : Blo 964590 23541961 := bstep (se 2 (by rfl) ⟨8828235, by rfl⟩ : syracuseStep 23541961 = 17656471) B17656471
theorem B10991861 : Blo 964590 10991861 := bstep (se 5 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 10991861 = 1030487) B1030487
theorem B964871 : Blo 964590 964871 := bstep (se 1 (by rfl) ⟨723653, by rfl⟩ : syracuseStep 964871 = 1447307) B1447307
theorem B964879 : Blo 964590 964879 := bstep (se 1 (by rfl) ⟨723659, by rfl⟩ : syracuseStep 964879 = 1447319) B1447319
theorem B964923 : Blo 964590 964923 := bstep (se 1 (by rfl) ⟨723692, by rfl⟩ : syracuseStep 964923 = 1447385) B1447385
theorem B3258683 : Blo 964590 3258683 := bstep (se 1 (by rfl) ⟨2444012, by rfl⟩ : syracuseStep 3258683 = 4888025) B4888025
theorem B964999 : Blo 964590 964999 := bstep (se 1 (by rfl) ⟨723749, by rfl⟩ : syracuseStep 964999 = 1447499) B1447499
theorem B965007 : Blo 964590 965007 := bstep (se 1 (by rfl) ⟨723755, by rfl⟩ : syracuseStep 965007 = 1447511) B1447511
theorem B6961555 : Blo 964590 6961555 := bstep (se 1 (by rfl) ⟨5221166, by rfl⟩ : syracuseStep 6961555 = 10442333) B10442333
theorem B3488147 : Blo 964590 3488147 := bstep (se 1 (by rfl) ⟨2616110, by rfl⟩ : syracuseStep 3488147 = 5232221) B5232221
theorem B965051 : Blo 964590 965051 := bstep (se 1 (by rfl) ⟨723788, by rfl⟩ : syracuseStep 965051 = 1447577) B1447577
theorem B965127 : Blo 964590 965127 := bstep (se 1 (by rfl) ⟨723845, by rfl⟩ : syracuseStep 965127 = 1447691) B1447691
theorem B965135 : Blo 964590 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B965179 : Blo 964590 965179 := bstep (se 1 (by rfl) ⟨723884, by rfl⟩ : syracuseStep 965179 = 1447769) B1447769
theorem B3095101 : Blo 964590 3095101 := bstep (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) B1160663
theorem B965255 : Blo 964590 965255 := bstep (se 1 (by rfl) ⟨723941, by rfl⟩ : syracuseStep 965255 = 1447883) B1447883
theorem B965263 : Blo 964590 965263 := bstep (se 1 (by rfl) ⟨723947, by rfl⟩ : syracuseStep 965263 = 1447895) B1447895
theorem B965307 : Blo 964590 965307 := bstep (se 1 (by rfl) ⟨723980, by rfl⟩ : syracuseStep 965307 = 1447961) B1447961
theorem B965383 : Blo 964590 965383 := bstep (se 1 (by rfl) ⟨724037, by rfl⟩ : syracuseStep 965383 = 1448075) B1448075
theorem B965391 : Blo 964590 965391 := bstep (se 1 (by rfl) ⟨724043, by rfl⟩ : syracuseStep 965391 = 1448087) B1448087
theorem B3259169 : Blo 964590 3259169 := bstep (se 2 (by rfl) ⟨1222188, by rfl⟩ : syracuseStep 3259169 = 2444377) B2444377
theorem B965435 : Blo 964590 965435 := bstep (se 1 (by rfl) ⟨724076, by rfl⟩ : syracuseStep 965435 = 1448153) B1448153
theorem B965511 : Blo 964590 965511 := bstep (se 1 (by rfl) ⟨724133, by rfl⟩ : syracuseStep 965511 = 1448267) B1448267
theorem B2177927 : Blo 964590 2177927 := bstep (se 1 (by rfl) ⟨1633445, by rfl⟩ : syracuseStep 2177927 = 3266891) B3266891
theorem B965519 : Blo 964590 965519 := bstep (se 1 (by rfl) ⟨724139, by rfl⟩ : syracuseStep 965519 = 1448279) B1448279
theorem B965563 : Blo 964590 965563 := bstep (se 1 (by rfl) ⟨724172, by rfl⟩ : syracuseStep 965563 = 1448345) B1448345
theorem B4897745 : Blo 964590 4897745 := bstep (se 2 (by rfl) ⟨1836654, by rfl⟩ : syracuseStep 4897745 = 3673309) B3673309
theorem B965639 : Blo 964590 965639 := bstep (se 1 (by rfl) ⟨724229, by rfl⟩ : syracuseStep 965639 = 1448459) B1448459
theorem B965647 : Blo 964590 965647 := bstep (se 1 (by rfl) ⟨724235, by rfl⟩ : syracuseStep 965647 = 1448471) B1448471
theorem B965691 : Blo 964590 965691 := bstep (se 1 (by rfl) ⟨724268, by rfl⟩ : syracuseStep 965691 = 1448537) B1448537
theorem B2178107 : Blo 964590 2178107 := bstep (se 1 (by rfl) ⟨1633580, by rfl⟩ : syracuseStep 2178107 = 3267161) B3267161
theorem B965767 : Blo 964590 965767 := bstep (se 1 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 965767 = 1448651) B1448651
theorem B965775 : Blo 964590 965775 := bstep (se 1 (by rfl) ⟨724331, by rfl⟩ : syracuseStep 965775 = 1448663) B1448663
theorem B2178233 : Blo 964590 2178233 := bstep (se 2 (by rfl) ⟨816837, by rfl⟩ : syracuseStep 2178233 = 1633675) B1633675
theorem B965819 : Blo 964590 965819 := bstep (se 1 (by rfl) ⟨724364, by rfl⟩ : syracuseStep 965819 = 1448729) B1448729
theorem B92978381 : Blo 964590 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B965895 : Blo 964590 965895 := bstep (se 1 (by rfl) ⟨724421, by rfl⟩ : syracuseStep 965895 = 1448843) B1448843
theorem B965903 : Blo 964590 965903 := bstep (se 1 (by rfl) ⟨724427, by rfl⟩ : syracuseStep 965903 = 1448855) B1448855
theorem B965947 : Blo 964590 965947 := bstep (se 1 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 965947 = 1448921) B1448921
theorem B3259763 : Blo 964590 3259763 := bstep (se 1 (by rfl) ⟨2444822, by rfl⟩ : syracuseStep 3259763 = 4889645) B4889645
theorem B1162615 : Blo 964590 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B966023 : Blo 964590 966023 := bstep (se 1 (by rfl) ⟨724517, by rfl⟩ : syracuseStep 966023 = 1449035) B1449035
theorem B966031 : Blo 964590 966031 := bstep (se 1 (by rfl) ⟨724523, by rfl⟩ : syracuseStep 966031 = 1449047) B1449047
theorem B1031611 : Blo 964590 1031611 := bstep (se 1 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 1031611 = 1547417) B1547417
theorem B966075 : Blo 964590 966075 := bstep (se 1 (by rfl) ⟨724556, by rfl⟩ : syracuseStep 966075 = 1449113) B1449113
theorem B966151 : Blo 964590 966151 := bstep (se 1 (by rfl) ⟨724613, by rfl⟩ : syracuseStep 966151 = 1449227) B1449227
theorem B966159 : Blo 964590 966159 := bstep (se 1 (by rfl) ⟨724619, by rfl⟩ : syracuseStep 966159 = 1449239) B1449239
theorem B2178575 : Blo 964590 2178575 := bstep (se 1 (by rfl) ⟨1633931, by rfl⟩ : syracuseStep 2178575 = 3267863) B3267863
theorem B2178593 : Blo 964590 2178593 := bstep (se 2 (by rfl) ⟨816972, by rfl⟩ : syracuseStep 2178593 = 1633945) B1633945
theorem B966203 : Blo 964590 966203 := bstep (se 1 (by rfl) ⟨724652, by rfl⟩ : syracuseStep 966203 = 1449305) B1449305
theorem B41762405 : Blo 964590 41762405 := bstep (se 4 (by rfl) ⟨3915225, by rfl⟩ : syracuseStep 41762405 = 7830451) B7830451
theorem B966279 : Blo 964590 966279 := bstep (se 1 (by rfl) ⟨724709, by rfl⟩ : syracuseStep 966279 = 1449419) B1449419
theorem B966287 : Blo 964590 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B966331 : Blo 964590 966331 := bstep (se 1 (by rfl) ⟨724748, by rfl⟩ : syracuseStep 966331 = 1449497) B1449497
theorem B7061185 : Blo 964590 7061185 := bstep (se 2 (by rfl) ⟨2647944, by rfl⟩ : syracuseStep 7061185 = 5295889) B5295889
theorem B11747045 : Blo 964590 11747045 := bstep (se 4 (by rfl) ⟨1101285, by rfl⟩ : syracuseStep 11747045 = 2202571) B2202571
theorem B966407 : Blo 964590 966407 := bstep (se 1 (by rfl) ⟨724805, by rfl⟩ : syracuseStep 966407 = 1449611) B1449611
theorem B966415 : Blo 964590 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B966459 : Blo 964590 966459 := bstep (se 1 (by rfl) ⟨724844, by rfl⟩ : syracuseStep 966459 = 1449689) B1449689
theorem B2178935 : Blo 964590 2178935 := bstep (se 1 (by rfl) ⟨1634201, by rfl⟩ : syracuseStep 2178935 = 3268403) B3268403
theorem B966535 : Blo 964590 966535 := bstep (se 1 (by rfl) ⟨724901, by rfl⟩ : syracuseStep 966535 = 1449803) B1449803
theorem B966543 : Blo 964590 966543 := bstep (se 1 (by rfl) ⟨724907, by rfl⟩ : syracuseStep 966543 = 1449815) B1449815
theorem B4636561 : Blo 964590 4636561 := bstep (se 2 (by rfl) ⟨1738710, by rfl⟩ : syracuseStep 4636561 = 3477421) B3477421
theorem B966587 : Blo 964590 966587 := bstep (se 1 (by rfl) ⟨724940, by rfl⟩ : syracuseStep 966587 = 1449881) B1449881
theorem B966663 : Blo 964590 966663 := bstep (se 1 (by rfl) ⟨724997, by rfl⟩ : syracuseStep 966663 = 1449995) B1449995
theorem B3096587 : Blo 964590 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B966671 : Blo 964590 966671 := bstep (se 1 (by rfl) ⟨725003, by rfl⟩ : syracuseStep 966671 = 1450007) B1450007
theorem B2179115 : Blo 964590 2179115 := bstep (se 1 (by rfl) ⟨1634336, by rfl⟩ : syracuseStep 2179115 = 3268673) B3268673
theorem B966715 : Blo 964590 966715 := bstep (se 1 (by rfl) ⟨725036, by rfl⟩ : syracuseStep 966715 = 1450073) B1450073
theorem B3915863 : Blo 964590 3915863 := bstep (se 1 (by rfl) ⟨2936897, by rfl⟩ : syracuseStep 3915863 = 5873795) B5873795
theorem B966791 : Blo 964590 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B966799 : Blo 964590 966799 := bstep (se 1 (by rfl) ⟨725099, by rfl⟩ : syracuseStep 966799 = 1450199) B1450199
theorem B966843 : Blo 964590 966843 := bstep (se 1 (by rfl) ⟨725132, by rfl⟩ : syracuseStep 966843 = 1450265) B1450265
theorem B6963401 : Blo 964590 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B966919 : Blo 964590 966919 := bstep (se 1 (by rfl) ⟨725189, by rfl⟩ : syracuseStep 966919 = 1450379) B1450379
theorem B966927 : Blo 964590 966927 := bstep (se 1 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 966927 = 1450391) B1450391
theorem B10469665 : Blo 964590 10469665 := bstep (se 2 (by rfl) ⟨3926124, by rfl⟩ : syracuseStep 10469665 = 7852249) B7852249
theorem B966971 : Blo 964590 966971 := bstep (se 1 (by rfl) ⟨725228, by rfl⟩ : syracuseStep 966971 = 1450457) B1450457
theorem B3096947 : Blo 964590 3096947 := bstep (se 1 (by rfl) ⟨2322710, by rfl⟩ : syracuseStep 3096947 = 4645421) B4645421
theorem B967047 : Blo 964590 967047 := bstep (se 1 (by rfl) ⟨725285, by rfl⟩ : syracuseStep 967047 = 1450571) B1450571
theorem B8274311 : Blo 964590 8274311 := bstep (se 1 (by rfl) ⟨6205733, by rfl⟩ : syracuseStep 8274311 = 12411467) B12411467
theorem B967055 : Blo 964590 967055 := bstep (se 1 (by rfl) ⟨725291, by rfl⟩ : syracuseStep 967055 = 1450583) B1450583
theorem B967099 : Blo 964590 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B967175 : Blo 964590 967175 := bstep (se 1 (by rfl) ⟨725381, by rfl⟩ : syracuseStep 967175 = 1450763) B1450763
theorem B967183 : Blo 964590 967183 := bstep (se 1 (by rfl) ⟨725387, by rfl⟩ : syracuseStep 967183 = 1450775) B1450775
theorem B5227051 : Blo 964590 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B967227 : Blo 964590 967227 := bstep (se 1 (by rfl) ⟨725420, by rfl⟩ : syracuseStep 967227 = 1450841) B1450841
theorem B967303 : Blo 964590 967303 := bstep (se 1 (by rfl) ⟨725477, by rfl⟩ : syracuseStep 967303 = 1450955) B1450955
theorem B967311 : Blo 964590 967311 := bstep (se 1 (by rfl) ⟨725483, by rfl⟩ : syracuseStep 967311 = 1450967) B1450967
theorem B11748017 : Blo 964590 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B967355 : Blo 964590 967355 := bstep (se 1 (by rfl) ⟨725516, by rfl⟩ : syracuseStep 967355 = 1451033) B1451033
theorem B3916525 : Blo 964590 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B967431 : Blo 964590 967431 := bstep (se 1 (by rfl) ⟨725573, by rfl⟩ : syracuseStep 967431 = 1451147) B1451147
theorem B967439 : Blo 964590 967439 := bstep (se 1 (by rfl) ⟨725579, by rfl⟩ : syracuseStep 967439 = 1451159) B1451159
theorem B967483 : Blo 964590 967483 := bstep (se 1 (by rfl) ⟨725612, by rfl⟩ : syracuseStep 967483 = 1451225) B1451225
theorem B967559 : Blo 964590 967559 := bstep (se 1 (by rfl) ⟨725669, by rfl⟩ : syracuseStep 967559 = 1451339) B1451339
theorem B967567 : Blo 964590 967567 := bstep (se 1 (by rfl) ⟨725675, by rfl⟩ : syracuseStep 967567 = 1451351) B1451351
theorem B967611 : Blo 964590 967611 := bstep (se 1 (by rfl) ⟨725708, by rfl⟩ : syracuseStep 967611 = 1451417) B1451417
theorem B967687 : Blo 964590 967687 := bstep (se 1 (by rfl) ⟨725765, by rfl⟩ : syracuseStep 967687 = 1451531) B1451531
theorem B2442251 : Blo 964590 2442251 := bstep (se 1 (by rfl) ⟨1831688, by rfl⟩ : syracuseStep 2442251 = 3663377) B3663377
theorem B4899851 : Blo 964590 4899851 := bstep (se 1 (by rfl) ⟨3674888, by rfl⟩ : syracuseStep 4899851 = 7349777) B7349777
theorem B967695 : Blo 964590 967695 := bstep (se 1 (by rfl) ⟨725771, by rfl⟩ : syracuseStep 967695 = 1451543) B1451543
theorem B967739 : Blo 964590 967739 := bstep (se 1 (by rfl) ⟨725804, by rfl⟩ : syracuseStep 967739 = 1451609) B1451609
theorem B967815 : Blo 964590 967815 := bstep (se 1 (by rfl) ⟨725861, by rfl⟩ : syracuseStep 967815 = 1451723) B1451723
theorem B967823 : Blo 964590 967823 := bstep (se 1 (by rfl) ⟨725867, by rfl⟩ : syracuseStep 967823 = 1451735) B1451735
theorem B4900013 : Blo 964590 4900013 := bstep (se 3 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 4900013 = 1837505) B1837505
theorem B967867 : Blo 964590 967867 := bstep (se 1 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 967867 = 1451801) B1451801
theorem B967943 : Blo 964590 967943 := bstep (se 1 (by rfl) ⟨725957, by rfl⟩ : syracuseStep 967943 = 1451915) B1451915
theorem B967951 : Blo 964590 967951 := bstep (se 1 (by rfl) ⟨725963, by rfl⟩ : syracuseStep 967951 = 1451927) B1451927
theorem B967995 : Blo 964590 967995 := bstep (se 1 (by rfl) ⟨725996, by rfl⟩ : syracuseStep 967995 = 1451993) B1451993
theorem B968071 : Blo 964590 968071 := bstep (se 1 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 968071 = 1452107) B1452107
theorem B968079 : Blo 964590 968079 := bstep (se 1 (by rfl) ⟨726059, by rfl⟩ : syracuseStep 968079 = 1452119) B1452119
theorem B968123 : Blo 964590 968123 := bstep (se 1 (by rfl) ⟨726092, by rfl⟩ : syracuseStep 968123 = 1452185) B1452185
theorem B968199 : Blo 964590 968199 := bstep (se 1 (by rfl) ⟨726149, by rfl⟩ : syracuseStep 968199 = 1452299) B1452299
theorem B968207 : Blo 964590 968207 := bstep (se 1 (by rfl) ⟨726155, by rfl⟩ : syracuseStep 968207 = 1452311) B1452311
theorem B968251 : Blo 964590 968251 := bstep (se 1 (by rfl) ⟨726188, by rfl⟩ : syracuseStep 968251 = 1452377) B1452377
theorem B968327 : Blo 964590 968327 := bstep (se 1 (by rfl) ⟨726245, by rfl⟩ : syracuseStep 968327 = 1452491) B1452491
theorem B968335 : Blo 964590 968335 := bstep (se 1 (by rfl) ⟨726251, by rfl⟩ : syracuseStep 968335 = 1452503) B1452503
theorem B2442899 : Blo 964590 2442899 := bstep (se 1 (by rfl) ⟨1832174, by rfl⟩ : syracuseStep 2442899 = 3664349) B3664349
theorem B968379 : Blo 964590 968379 := bstep (se 1 (by rfl) ⟨726284, by rfl⟩ : syracuseStep 968379 = 1452569) B1452569
theorem B968455 : Blo 964590 968455 := bstep (se 1 (by rfl) ⟨726341, by rfl⟩ : syracuseStep 968455 = 1452683) B1452683
theorem B968463 : Blo 964590 968463 := bstep (se 1 (by rfl) ⟨726347, by rfl⟩ : syracuseStep 968463 = 1452695) B1452695
theorem B7325477 : Blo 964590 7325477 := bstep (se 4 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 7325477 = 1373527) B1373527
theorem B968507 : Blo 964590 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B968583 : Blo 964590 968583 := bstep (se 1 (by rfl) ⟨726437, by rfl⟩ : syracuseStep 968583 = 1452875) B1452875
theorem B3262355 : Blo 964590 3262355 := bstep (se 1 (by rfl) ⟨2446766, by rfl⟩ : syracuseStep 3262355 = 4893533) B4893533
theorem B4638617 : Blo 964590 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B2443193 : Blo 964590 2443193 := bstep (se 2 (by rfl) ⟨916197, by rfl⟩ : syracuseStep 2443193 = 1832395) B1832395
theorem B1034255 : Blo 964590 1034255 := bstep (se 1 (by rfl) ⟨775691, by rfl⟩ : syracuseStep 1034255 = 1551383) B1551383
theorem B1394761 : Blo 964590 1394761 := bstep (se 2 (by rfl) ⟨523035, by rfl⟩ : syracuseStep 1394761 = 1046071) B1046071
theorem B2443891 : Blo 964590 2443891 := bstep (se 1 (by rfl) ⟨1832918, by rfl⟩ : syracuseStep 2443891 = 3665837) B3665837
theorem B2444033 : Blo 964590 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B4901633 : Blo 964590 4901633 := bstep (se 2 (by rfl) ⟨1838112, by rfl⟩ : syracuseStep 4901633 = 3676225) B3676225
theorem B15649625 : Blo 964590 15649625 := bstep (se 2 (by rfl) ⟨5868609, by rfl⟩ : syracuseStep 15649625 = 11737219) B11737219
theorem B13945715 : Blo 964590 13945715 := bstep (se 1 (by rfl) ⟨10459286, by rfl⟩ : syracuseStep 13945715 = 20918573) B20918573
theorem B9292805 : Blo 964590 9292805 := bstep (se 4 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 9292805 = 1742401) B1742401
theorem B3132503 : Blo 964590 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B2444489 : Blo 964590 2444489 := bstep (se 2 (by rfl) ⟨916683, by rfl⟩ : syracuseStep 2444489 = 1833367) B1833367
theorem B3263759 : Blo 964590 3263759 := bstep (se 1 (by rfl) ⟨2447819, by rfl⟩ : syracuseStep 3263759 = 4895639) B4895639
theorem B2608499 : Blo 964590 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B3264029 : Blo 964590 3264029 := bstep (se 3 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 3264029 = 1224011) B1224011
theorem B2444843 : Blo 964590 2444843 := bstep (se 1 (by rfl) ⟨1833632, by rfl⟩ : syracuseStep 2444843 = 3667265) B3667265
theorem B4902443 : Blo 964590 4902443 := bstep (se 1 (by rfl) ⟨3676832, by rfl⟩ : syracuseStep 4902443 = 7353665) B7353665
theorem B21221189 : Blo 964590 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B4706695 : Blo 964590 4706695 := bstep (se 1 (by rfl) ⟨3530021, by rfl⟩ : syracuseStep 4706695 = 7060043) B7060043
theorem B2478593 : Blo 964590 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B2445835 : Blo 964590 2445835 := bstep (se 1 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 2445835 = 3668753) B3668753
theorem B3101303 : Blo 964590 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B2445977 : Blo 964590 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B2446139 : Blo 964590 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B3265433 : Blo 964590 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B2642959 : Blo 964590 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B2446483 : Blo 964590 2446483 := bstep (se 1 (by rfl) ⟨1834862, by rfl⟩ : syracuseStep 2446483 = 3669725) B3669725
theorem B2446625 : Blo 964590 2446625 := bstep (se 2 (by rfl) ⟨917484, by rfl⟩ : syracuseStep 2446625 = 1834969) B1834969
theorem B4838771 : Blo 964590 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B5952953 : Blo 964590 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B3266135 : Blo 964590 3266135 := bstep (se 1 (by rfl) ⟨2449601, by rfl⟩ : syracuseStep 3266135 = 4899203) B4899203
theorem B8247041 : Blo 964590 8247041 := bstep (se 2 (by rfl) ⟨3092640, by rfl⟩ : syracuseStep 8247041 = 6185281) B6185281
theorem B1628039 : Blo 964590 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B3266621 : Blo 964590 3266621 := bstep (se 3 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 3266621 = 1224983) B1224983
theorem B4642883 : Blo 964590 4642883 := bstep (se 1 (by rfl) ⟨3482162, by rfl⟩ : syracuseStep 4642883 = 6964325) B6964325
theorem B2513015 : Blo 964590 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B2447617 : Blo 964590 2447617 := bstep (se 2 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 2447617 = 1835713) B1835713
theorem B5888315 : Blo 964590 5888315 := bstep (se 1 (by rfl) ⟨4416236, by rfl⟩ : syracuseStep 5888315 = 8832473) B8832473
theorem B13949405 : Blo 964590 13949405 := bstep (se 3 (by rfl) ⟨2615513, by rfl⟩ : syracuseStep 13949405 = 5231027) B5231027
theorem B1628687 : Blo 964590 1628687 := bstep (se 1 (by rfl) ⟨1221515, by rfl⟩ : syracuseStep 1628687 = 2443031) B2443031
theorem B5495363 : Blo 964590 5495363 := bstep (se 1 (by rfl) ⟨4121522, by rfl⟩ : syracuseStep 5495363 = 8243045) B8243045
theorem B2448215 : Blo 964590 2448215 := bstep (se 1 (by rfl) ⟨1836161, by rfl⟩ : syracuseStep 2448215 = 3672323) B3672323
theorem B1629227 : Blo 964590 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B2448427 : Blo 964590 2448427 := bstep (se 1 (by rfl) ⟨1836320, by rfl⟩ : syracuseStep 2448427 = 3672641) B3672641
theorem B2448569 : Blo 964590 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B1629625 : Blo 964590 1629625 := bstep (se 2 (by rfl) ⟨611109, by rfl⟩ : syracuseStep 1629625 = 1222219) B1222219
theorem B3268025 : Blo 964590 3268025 := bstep (se 2 (by rfl) ⟨1225509, by rfl⟩ : syracuseStep 3268025 = 2451019) B2451019
theorem B5234141 : Blo 964590 5234141 := bstep (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) B1962803
theorem B2317943 : Blo 964590 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B3268619 : Blo 964590 3268619 := bstep (se 1 (by rfl) ⟨2451464, by rfl⟩ : syracuseStep 3268619 = 4902929) B4902929
theorem B1630327 : Blo 964590 1630327 := bstep (se 1 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 1630327 = 2445491) B2445491
theorem B3268727 : Blo 964590 3268727 := bstep (se 1 (by rfl) ⟨2451545, by rfl⟩ : syracuseStep 3268727 = 4903091) B4903091
theorem B2449561 : Blo 964590 2449561 := bstep (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) B1837171
theorem B1630523 : Blo 964590 1630523 := bstep (se 1 (by rfl) ⟨1222892, by rfl⟩ : syracuseStep 1630523 = 2445785) B2445785
theorem B2449723 : Blo 964590 2449723 := bstep (se 1 (by rfl) ⟨1837292, by rfl⟩ : syracuseStep 2449723 = 3674585) B3674585
theorem B7332281 : Blo 964590 7332281 := bstep (se 2 (by rfl) ⟨2749605, by rfl⟩ : syracuseStep 7332281 = 5499211) B5499211
theorem B2449865 : Blo 964590 2449865 := bstep (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) B1837399
theorem B1630921 : Blo 964590 1630921 := bstep (se 2 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 1630921 = 1223191) B1223191
theorem B4645633 : Blo 964590 4645633 := bstep (se 2 (by rfl) ⟨1742112, by rfl⟩ : syracuseStep 4645633 = 3484225) B3484225
theorem B8807183 : Blo 964590 8807183 := bstep (se 1 (by rfl) ⟨6605387, by rfl⟩ : syracuseStep 8807183 = 13210775) B13210775
theorem B2450209 : Blo 964590 2450209 := bstep (se 2 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 2450209 = 1837657) B1837657
theorem B5497753 : Blo 964590 5497753 := bstep (se 2 (by rfl) ⟨2061657, by rfl⟩ : syracuseStep 5497753 = 4123315) B4123315
theorem B2483129 : Blo 964590 2483129 := bstep (se 2 (by rfl) ⟨931173, by rfl⟩ : syracuseStep 2483129 = 1862347) B1862347
theorem B3662891 : Blo 964590 3662891 := bstep (se 1 (by rfl) ⟨2747168, by rfl⟩ : syracuseStep 3662891 = 5494337) B5494337
theorem B2942153 : Blo 964590 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B2450807 : Blo 964590 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B1631623 : Blo 964590 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B2319769 : Blo 964590 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B1467919 : Blo 964590 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B2614931 : Blo 964590 2614931 := bstep (se 1 (by rfl) ⟨1961198, by rfl⟩ : syracuseStep 2614931 = 3922397) B3922397
theorem B13231795 : Blo 964590 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B4122427 : Blo 964590 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B133883765 : Blo 964590 133883765 := bstep (se 5 (by rfl) ⟨6275801, by rfl⟩ : syracuseStep 133883765 = 12551603) B12551603
theorem B1632271 : Blo 964590 1632271 := bstep (se 1 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 1632271 = 2448407) B2448407
theorem B8251415 : Blo 964590 8251415 := bstep (se 1 (by rfl) ⟨6188561, by rfl⟩ : syracuseStep 8251415 = 12377123) B12377123
theorem B8251793 : Blo 964590 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B4418059 : Blo 964590 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B1632811 : Blo 964590 1632811 := bstep (se 1 (by rfl) ⟨1224608, by rfl⟩ : syracuseStep 1632811 = 2449217) B2449217
theorem B1632953 : Blo 964590 1632953 := bstep (se 2 (by rfl) ⟨612357, by rfl⟩ : syracuseStep 1632953 = 1224715) B1224715
theorem B19852037 : Blo 964590 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B5499737 : Blo 964590 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B1305487 : Blo 964590 1305487 := bstep (se 1 (by rfl) ⟨979115, by rfl⟩ : syracuseStep 1305487 = 1958231) B1958231
theorem B27913571 : Blo 964590 27913571 := bstep (se 1 (by rfl) ⟨20935178, by rfl⟩ : syracuseStep 27913571 = 41870357) B41870357
theorem B1633655 : Blo 964590 1633655 := bstep (se 1 (by rfl) ⟨1225241, by rfl⟩ : syracuseStep 1633655 = 2450483) B2450483
theorem B2747783 : Blo 964590 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B3141011 : Blo 964590 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B1306027 : Blo 964590 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B6188663 : Blo 964590 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B2092691 : Blo 964590 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B2616985 : Blo 964590 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B1634107 : Blo 964590 1634107 := bstep (se 1 (by rfl) ⟨1225580, by rfl⟩ : syracuseStep 1634107 = 2451161) B2451161
theorem B1634249 : Blo 964590 1634249 := bstep (se 2 (by rfl) ⟨612843, by rfl⟩ : syracuseStep 1634249 = 1225687) B1225687
theorem B2715709 : Blo 964590 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B14151881 : Blo 964590 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B3666323 : Blo 964590 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B1307065 : Blo 964590 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B1471367 : Blo 964590 1471367 := bstep (se 1 (by rfl) ⟨1103525, by rfl⟩ : syracuseStep 1471367 = 2207051) B2207051
theorem B3535751 : Blo 964590 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B14873507 : Blo 964590 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B979975 : Blo 964590 979975 := bstep (se 1 (by rfl) ⟨734981, by rfl⟩ : syracuseStep 979975 = 1469963) B1469963
theorem B3306539 : Blo 964590 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B1373431 : Blo 964590 1373431 := bstep (se 1 (by rfl) ⟨1030073, by rfl⟩ : syracuseStep 1373431 = 2060147) B2060147
theorem B2749697 : Blo 964590 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B1832311 : Blo 964590 1832311 := bstep (se 1 (by rfl) ⟨1374233, by rfl⟩ : syracuseStep 1832311 = 2748467) B2748467
theorem B1373755 : Blo 964590 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B980623 : Blo 964590 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B2750267 : Blo 964590 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B2750507 : Blo 964590 2750507 := bstep (se 1 (by rfl) ⟨2062880, by rfl⟩ : syracuseStep 2750507 = 4125761) B4125761
theorem B2324747 : Blo 964590 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B5503859 : Blo 964590 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B21199765 : Blo 964590 21199765 := bstep (se 6 (by rfl) ⟨496869, by rfl⟩ : syracuseStep 21199765 = 993739) B993739
theorem B3668921 : Blo 964590 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B14711813 : Blo 964590 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B1834103 : Blo 964590 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B2063495 : Blo 964590 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B1834255 : Blo 964590 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B9305603 : Blo 964590 9305603 := bstep (se 1 (by rfl) ⟨6979202, by rfl⟩ : syracuseStep 9305603 = 13958405) B13958405
theorem B2784811 : Blo 964590 2784811 := bstep (se 1 (by rfl) ⟨2088608, by rfl⟩ : syracuseStep 2784811 = 4177217) B4177217
theorem B1834643 : Blo 964590 1834643 := bstep (se 1 (by rfl) ⟨1375982, by rfl⟩ : syracuseStep 1834643 = 2751965) B2751965
theorem B1376119 : Blo 964590 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B3669907 : Blo 964590 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B12058571 : Blo 964590 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B30638027 : Blo 964590 30638027 := bstep (se 1 (by rfl) ⟨22978520, by rfl⟩ : syracuseStep 30638027 = 45957041) B45957041
theorem B4653071 : Blo 964590 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B8257565 : Blo 964590 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B3670211 : Blo 964590 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B1376455 : Blo 964590 1376455 := bstep (se 1 (by rfl) ⟨1032341, by rfl⟩ : syracuseStep 1376455 = 2064683) B2064683
theorem B2064631 : Blo 964590 2064631 := bstep (se 1 (by rfl) ⟨1548473, by rfl⟩ : syracuseStep 2064631 = 3096947) B3096947
theorem B13959553 : Blo 964590 13959553 := bstep (se 2 (by rfl) ⟨5234832, by rfl⟩ : syracuseStep 13959553 = 10469665) B10469665
theorem B7832011 : Blo 964590 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B5505569 : Blo 964590 5505569 := bstep (se 2 (by rfl) ⟨2064588, by rfl⟩ : syracuseStep 5505569 = 4129177) B4129177
theorem B3670667 : Blo 964590 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B3670879 : Blo 964590 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B7341029 : Blo 964590 7341029 := bstep (se 4 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 7341029 = 1376443) B1376443
theorem B6194177 : Blo 964590 6194177 := bstep (se 2 (by rfl) ⟨2322816, by rfl⟩ : syracuseStep 6194177 = 4645633) B4645633
theorem B2753615 : Blo 964590 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B4883651 : Blo 964590 4883651 := bstep (se 1 (by rfl) ⟨3662738, by rfl⟩ : syracuseStep 4883651 = 7325477) B7325477
theorem B5506775 : Blo 964590 5506775 := bstep (se 1 (by rfl) ⟨4130081, by rfl⟩ : syracuseStep 5506775 = 8260163) B8260163
theorem B2983673 : Blo 964590 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B3671837 : Blo 964590 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B3671851 : Blo 964590 3671851 := bstep (se 1 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 3671851 = 5507777) B5507777
theorem B1837019 : Blo 964590 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B6195203 : Blo 964590 6195203 := bstep (se 1 (by rfl) ⟨4646402, by rfl⟩ : syracuseStep 6195203 = 9292805) B9292805
theorem B1837255 : Blo 964590 1837255 := bstep (se 1 (by rfl) ⟨1377941, by rfl⟩ : syracuseStep 1837255 = 2755883) B2755883
theorem B1738999 : Blo 964590 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B2755097 : Blo 964590 2755097 := bstep (se 2 (by rfl) ⟨1033161, by rfl⟩ : syracuseStep 2755097 = 2066323) B2066323
theorem B8817437 : Blo 964590 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B2067535 : Blo 964590 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B3968635 : Blo 964590 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1085359 : Blo 964590 1085359 := bstep (se 1 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 1085359 = 1628039) B1628039
theorem B1675343 : Blo 964590 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B5509235 : Blo 964590 5509235 := bstep (se 1 (by rfl) ⟨4131926, by rfl⟩ : syracuseStep 5509235 = 8263853) B8263853
theorem B1085791 : Blo 964590 1085791 := bstep (se 1 (by rfl) ⟨814343, by rfl⟩ : syracuseStep 1085791 = 1628687) B1628687
theorem B5509691 : Blo 964590 5509691 := bstep (se 1 (by rfl) ⟨4132268, by rfl⟩ : syracuseStep 5509691 = 8264537) B8264537
theorem B1086151 : Blo 964590 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B3675041 : Blo 964590 3675041 := bstep (se 2 (by rfl) ⟨1378140, by rfl⟩ : syracuseStep 3675041 = 2756281) B2756281
theorem B2758013 : Blo 964590 2758013 := bstep (se 3 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 2758013 = 1034255) B1034255
theorem B1447343 : Blo 964590 1447343 := bstep (se 1 (by rfl) ⟨1085507, by rfl⟩ : syracuseStep 1447343 = 2171015) B2171015
theorem B1447433 : Blo 964590 1447433 := bstep (se 2 (by rfl) ⟨542787, by rfl⟩ : syracuseStep 1447433 = 1085575) B1085575
theorem B1447463 : Blo 964590 1447463 := bstep (se 1 (by rfl) ⟨1085597, by rfl⟩ : syracuseStep 1447463 = 2171195) B2171195
theorem B1087015 : Blo 964590 1087015 := bstep (se 1 (by rfl) ⟨815261, by rfl⟩ : syracuseStep 1087015 = 1630523) B1630523
theorem B1447547 : Blo 964590 1447547 := bstep (se 1 (by rfl) ⟨1085660, by rfl⟩ : syracuseStep 1447547 = 2171321) B2171321
theorem B4888187 : Blo 964590 4888187 := bstep (se 1 (by rfl) ⟨3666140, by rfl⟩ : syracuseStep 4888187 = 7332281) B7332281
theorem B1447673 : Blo 964590 1447673 := bstep (se 2 (by rfl) ⟨542877, by rfl⟩ : syracuseStep 1447673 = 1085755) B1085755
theorem B1447775 : Blo 964590 1447775 := bstep (se 1 (by rfl) ⟨1085831, by rfl⟩ : syracuseStep 1447775 = 2171663) B2171663
theorem B5871455 : Blo 964590 5871455 := bstep (se 1 (by rfl) ⟨4403591, by rfl⟩ : syracuseStep 5871455 = 8807183) B8807183
theorem B1447787 : Blo 964590 1447787 := bstep (se 1 (by rfl) ⟨1085840, by rfl⟩ : syracuseStep 1447787 = 2171681) B2171681
theorem B3676013 : Blo 964590 3676013 := bstep (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) B1378505
theorem B1742753 : Blo 964590 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B6199325 : Blo 964590 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B1448015 : Blo 964590 1448015 := bstep (se 1 (by rfl) ⟨1086011, by rfl⟩ : syracuseStep 1448015 = 2172023) B2172023
theorem B1448135 : Blo 964590 1448135 := bstep (se 1 (by rfl) ⟨1086101, by rfl⟩ : syracuseStep 1448135 = 2172203) B2172203
theorem B7051625 : Blo 964590 7051625 := bstep (se 2 (by rfl) ⟨2644359, by rfl⟩ : syracuseStep 7051625 = 5288719) B5288719
theorem B1448297 : Blo 964590 1448297 := bstep (se 2 (by rfl) ⟨543111, by rfl⟩ : syracuseStep 1448297 = 1086223) B1086223
theorem B1743287 : Blo 964590 1743287 := bstep (se 1 (by rfl) ⟨1307465, by rfl⟩ : syracuseStep 1743287 = 2614931) B2614931
theorem B1448375 : Blo 964590 1448375 := bstep (se 1 (by rfl) ⟨1086281, by rfl⟩ : syracuseStep 1448375 = 2172563) B2172563
theorem B1448411 : Blo 964590 1448411 := bstep (se 1 (by rfl) ⟨1086308, by rfl⟩ : syracuseStep 1448411 = 2172617) B2172617
theorem B3676697 : Blo 964590 3676697 := bstep (se 2 (by rfl) ⟨1378761, by rfl⟩ : syracuseStep 3676697 = 2757523) B2757523
theorem B3676711 : Blo 964590 3676711 := bstep (se 1 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 3676711 = 5515067) B5515067
theorem B7346861 : Blo 964590 7346861 := bstep (se 3 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 7346861 = 2755073) B2755073
theorem B1448879 : Blo 964590 1448879 := bstep (se 1 (by rfl) ⟨1086659, by rfl⟩ : syracuseStep 1448879 = 2173319) B2173319
theorem B1448969 : Blo 964590 1448969 := bstep (se 2 (by rfl) ⟨543363, by rfl⟩ : syracuseStep 1448969 = 1086727) B1086727
theorem B1448999 : Blo 964590 1448999 := bstep (se 1 (by rfl) ⟨1086749, by rfl⟩ : syracuseStep 1448999 = 2173499) B2173499
theorem B1449083 : Blo 964590 1449083 := bstep (se 1 (by rfl) ⟨1086812, by rfl⟩ : syracuseStep 1449083 = 2173625) B2173625
theorem B1088635 : Blo 964590 1088635 := bstep (se 1 (by rfl) ⟨816476, by rfl⟩ : syracuseStep 1088635 = 1632953) B1632953
theorem B1449209 : Blo 964590 1449209 := bstep (se 2 (by rfl) ⟨543453, by rfl⟩ : syracuseStep 1449209 = 1086907) B1086907
theorem B3677501 : Blo 964590 3677501 := bstep (se 3 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 3677501 = 1379063) B1379063
theorem B1449311 : Blo 964590 1449311 := bstep (se 1 (by rfl) ⟨1086983, by rfl⟩ : syracuseStep 1449311 = 2173967) B2173967
theorem B1449323 : Blo 964590 1449323 := bstep (se 1 (by rfl) ⟨1086992, by rfl⟩ : syracuseStep 1449323 = 2173985) B2173985
theorem B2170331 : Blo 964590 2170331 := bstep (se 1 (by rfl) ⟨1627748, by rfl⟩ : syracuseStep 2170331 = 3255497) B3255497
theorem B1449551 : Blo 964590 1449551 := bstep (se 1 (by rfl) ⟨1087163, by rfl⟩ : syracuseStep 1449551 = 2174327) B2174327
theorem B1089103 : Blo 964590 1089103 := bstep (se 1 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 1089103 = 1633655) B1633655
theorem B1449671 : Blo 964590 1449671 := bstep (se 1 (by rfl) ⟨1087253, by rfl⟩ : syracuseStep 1449671 = 2174507) B2174507
theorem B1449833 : Blo 964590 1449833 := bstep (se 2 (by rfl) ⟨543687, by rfl⟩ : syracuseStep 1449833 = 1087375) B1087375
theorem B2170799 : Blo 964590 2170799 := bstep (se 1 (by rfl) ⟨1628099, by rfl⟩ : syracuseStep 2170799 = 3256199) B3256199
theorem B1449911 : Blo 964590 1449911 := bstep (se 1 (by rfl) ⟨1087433, by rfl⟩ : syracuseStep 1449911 = 2174867) B2174867
theorem B1449947 : Blo 964590 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B1089499 : Blo 964590 1089499 := bstep (se 1 (by rfl) ⟨817124, by rfl⟩ : syracuseStep 1089499 = 1634249) B1634249
theorem B2171051 : Blo 964590 2171051 := bstep (se 1 (by rfl) ⟨1628288, by rfl⟩ : syracuseStep 2171051 = 3256577) B3256577
theorem B9281765 : Blo 964590 9281765 := bstep (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) B1740331
theorem B4890941 : Blo 964590 4890941 := bstep (se 3 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 4890941 = 1834103) B1834103
theorem B1450415 : Blo 964590 1450415 := bstep (se 1 (by rfl) ⟨1087811, by rfl⟩ : syracuseStep 1450415 = 2175623) B2175623
theorem B1450505 : Blo 964590 1450505 := bstep (se 2 (by rfl) ⟨543939, by rfl⟩ : syracuseStep 1450505 = 1087879) B1087879
theorem B9282073 : Blo 964590 9282073 := bstep (se 2 (by rfl) ⟨3480777, by rfl⟩ : syracuseStep 9282073 = 6961555) B6961555
theorem B1450535 : Blo 964590 1450535 := bstep (se 1 (by rfl) ⟨1087901, by rfl⟩ : syracuseStep 1450535 = 2175803) B2175803
theorem B1450619 : Blo 964590 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B2171591 : Blo 964590 2171591 := bstep (se 1 (by rfl) ⟨1628693, by rfl⟩ : syracuseStep 2171591 = 3257387) B3257387
theorem B1450745 : Blo 964590 1450745 := bstep (se 2 (by rfl) ⟨544029, by rfl⟩ : syracuseStep 1450745 = 1088059) B1088059
theorem B1450847 : Blo 964590 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B1450859 : Blo 964590 1450859 := bstep (se 1 (by rfl) ⟨1088144, by rfl⟩ : syracuseStep 1450859 = 2176289) B2176289
theorem B7349291 : Blo 964590 7349291 := bstep (se 1 (by rfl) ⟨5511968, by rfl⟩ : syracuseStep 7349291 = 11023937) B11023937
theorem B1451087 : Blo 964590 1451087 := bstep (se 1 (by rfl) ⟨1088315, by rfl⟩ : syracuseStep 1451087 = 2176631) B2176631
theorem B1451207 : Blo 964590 1451207 := bstep (se 1 (by rfl) ⟨1088405, by rfl⟩ : syracuseStep 1451207 = 2176811) B2176811
theorem B1451369 : Blo 964590 1451369 := bstep (se 2 (by rfl) ⟨544263, by rfl⟩ : syracuseStep 1451369 = 1088527) B1088527
theorem B1451447 : Blo 964590 1451447 := bstep (se 1 (by rfl) ⟨1088585, by rfl⟩ : syracuseStep 1451447 = 2177171) B2177171
theorem B1451483 : Blo 964590 1451483 := bstep (se 1 (by rfl) ⟨1088612, by rfl⟩ : syracuseStep 1451483 = 2177225) B2177225
theorem B2172455 : Blo 964590 2172455 := bstep (se 1 (by rfl) ⟨1629341, by rfl⟩ : syracuseStep 2172455 = 3258683) B3258683
theorem B1550153 : Blo 964590 1550153 := bstep (se 2 (by rfl) ⟨581307, by rfl⟩ : syracuseStep 1550153 = 1162615) B1162615
theorem B2172779 : Blo 964590 2172779 := bstep (se 1 (by rfl) ⟨1629584, by rfl⟩ : syracuseStep 2172779 = 3259169) B3259169
theorem B2172833 : Blo 964590 2172833 := bstep (se 2 (by rfl) ⟨814812, by rfl⟩ : syracuseStep 2172833 = 1629625) B1629625
theorem B1451951 : Blo 964590 1451951 := bstep (se 1 (by rfl) ⟨1088963, by rfl⟩ : syracuseStep 1451951 = 2177927) B2177927
theorem B9807875 : Blo 964590 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B1452041 : Blo 964590 1452041 := bstep (se 2 (by rfl) ⟨544515, by rfl⟩ : syracuseStep 1452041 = 1089031) B1089031
theorem B1452071 : Blo 964590 1452071 := bstep (se 1 (by rfl) ⟨1089053, by rfl⟩ : syracuseStep 1452071 = 2178107) B2178107
theorem B3713081 : Blo 964590 3713081 := bstep (se 2 (by rfl) ⟨1392405, by rfl⟩ : syracuseStep 3713081 = 2784811) B2784811
theorem B1452155 : Blo 964590 1452155 := bstep (se 1 (by rfl) ⟨1089116, by rfl⟩ : syracuseStep 1452155 = 2178233) B2178233
theorem B2173175 : Blo 964590 2173175 := bstep (se 1 (by rfl) ⟨1629881, by rfl⟩ : syracuseStep 2173175 = 3259763) B3259763
theorem B1452281 : Blo 964590 1452281 := bstep (se 2 (by rfl) ⟨544605, by rfl⟩ : syracuseStep 1452281 = 1089211) B1089211
theorem B9414913 : Blo 964590 9414913 := bstep (se 2 (by rfl) ⟨3530592, by rfl⟩ : syracuseStep 9414913 = 7061185) B7061185
theorem B6203735 : Blo 964590 6203735 := bstep (se 1 (by rfl) ⟨4652801, by rfl⟩ : syracuseStep 6203735 = 9305603) B9305603
theorem B1452383 : Blo 964590 1452383 := bstep (se 1 (by rfl) ⟨1089287, by rfl⟩ : syracuseStep 1452383 = 2178575) B2178575
theorem B1452395 : Blo 964590 1452395 := bstep (se 1 (by rfl) ⟨1089296, by rfl⟩ : syracuseStep 1452395 = 2178593) B2178593
theorem B1223095 : Blo 964590 1223095 := bstep (se 1 (by rfl) ⟨917321, by rfl⟩ : syracuseStep 1223095 = 1834643) B1834643
theorem B4893209 : Blo 964590 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B32156189 : Blo 964590 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B81701405 : Blo 964590 81701405 := bstep (se 3 (by rfl) ⟨15319013, by rfl⟩ : syracuseStep 81701405 = 30638027) B30638027
theorem B1452623 : Blo 964590 1452623 := bstep (se 1 (by rfl) ⟨1089467, by rfl⟩ : syracuseStep 1452623 = 2178935) B2178935
theorem B1452743 : Blo 964590 1452743 := bstep (se 1 (by rfl) ⟨1089557, by rfl⟩ : syracuseStep 1452743 = 2179115) B2179115
theorem B2173769 : Blo 964590 2173769 := bstep (se 2 (by rfl) ⟨815163, by rfl⟩ : syracuseStep 2173769 = 1630327) B1630327
theorem B5516207 : Blo 964590 5516207 := bstep (se 1 (by rfl) ⟨4137155, by rfl⟩ : syracuseStep 5516207 = 8274311) B8274311
theorem B6204761 : Blo 964590 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B2174561 : Blo 964590 2174561 := bstep (se 2 (by rfl) ⟨815460, by rfl⟩ : syracuseStep 2174561 = 1630921) B1630921
theorem B5222033 : Blo 964590 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B1224391 : Blo 964590 1224391 := bstep (se 1 (by rfl) ⟨918293, by rfl⟩ : syracuseStep 1224391 = 1836587) B1836587
theorem B2174903 : Blo 964590 2174903 := bstep (se 1 (by rfl) ⟨1631177, by rfl⟩ : syracuseStep 2174903 = 3262355) B3262355
theorem B3092411 : Blo 964590 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B3911759 : Blo 964590 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B1225135 : Blo 964590 1225135 := bstep (se 1 (by rfl) ⟨918851, by rfl⟩ : syracuseStep 1225135 = 1837703) B1837703
theorem B2175497 : Blo 964590 2175497 := bstep (se 2 (by rfl) ⟨815811, by rfl⟩ : syracuseStep 2175497 = 1631623) B1631623
theorem B10433083 : Blo 964590 10433083 := bstep (se 1 (by rfl) ⟨7824812, by rfl⟩ : syracuseStep 10433083 = 15649625) B15649625
theorem B3256955 : Blo 964590 3256955 := bstep (se 1 (by rfl) ⟨2442716, by rfl⟩ : syracuseStep 3256955 = 4885433) B4885433
theorem B3257117 : Blo 964590 3257117 := bstep (se 3 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 3257117 = 1221419) B1221419
theorem B12366665 : Blo 964590 12366665 := bstep (se 2 (by rfl) ⟨4637499, by rfl⟩ : syracuseStep 12366665 = 9274999) B9274999
theorem B2175839 : Blo 964590 2175839 := bstep (se 1 (by rfl) ⟨1631879, by rfl⟩ : syracuseStep 2175839 = 3263759) B3263759
theorem B17642393 : Blo 964590 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B2176019 : Blo 964590 2176019 := bstep (se 1 (by rfl) ⟨1632014, by rfl⟩ : syracuseStep 2176019 = 3264029) B3264029
theorem B2176361 : Blo 964590 2176361 := bstep (se 2 (by rfl) ⟨816135, by rfl⟩ : syracuseStep 2176361 = 1632271) B1632271
theorem B4896125 : Blo 964590 4896125 := bstep (se 3 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 4896125 = 1836047) B1836047
theorem B3257819 : Blo 964590 3257819 := bstep (se 1 (by rfl) ⟨2443364, by rfl⟩ : syracuseStep 3257819 = 4886729) B4886729
theorem B10597877 : Blo 964590 10597877 := bstep (se 5 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 10597877 = 993551) B993551
theorem B1652395 : Blo 964590 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B1161067 : Blo 964590 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B2176955 : Blo 964590 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B964647 : Blo 964590 964647 := bstep (se 1 (by rfl) ⟨723485, by rfl⟩ : syracuseStep 964647 = 1446971) B1446971
theorem B2177081 : Blo 964590 2177081 := bstep (se 2 (by rfl) ⟨816405, by rfl⟩ : syracuseStep 2177081 = 1632811) B1632811
theorem B964687 : Blo 964590 964687 := bstep (se 1 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 964687 = 1447031) B1447031
theorem B964703 : Blo 964590 964703 := bstep (se 1 (by rfl) ⟨723527, by rfl⟩ : syracuseStep 964703 = 1447055) B1447055
theorem B964731 : Blo 964590 964731 := bstep (se 1 (by rfl) ⟨723548, by rfl⟩ : syracuseStep 964731 = 1447097) B1447097
theorem B3258521 : Blo 964590 3258521 := bstep (se 2 (by rfl) ⟨1221945, by rfl⟩ : syracuseStep 3258521 = 2443891) B2443891
theorem B964783 : Blo 964590 964783 := bstep (se 1 (by rfl) ⟨723587, by rfl⟩ : syracuseStep 964783 = 1447175) B1447175
theorem B964807 : Blo 964590 964807 := bstep (se 1 (by rfl) ⟨723605, by rfl⟩ : syracuseStep 964807 = 1447211) B1447211
theorem B964827 : Blo 964590 964827 := bstep (se 1 (by rfl) ⟨723620, by rfl⟩ : syracuseStep 964827 = 1447241) B1447241
theorem B3225847 : Blo 964590 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B964903 : Blo 964590 964903 := bstep (se 1 (by rfl) ⟨723677, by rfl⟩ : syracuseStep 964903 = 1447355) B1447355
theorem B964943 : Blo 964590 964943 := bstep (se 1 (by rfl) ⟨723707, by rfl⟩ : syracuseStep 964943 = 1447415) B1447415
theorem B964959 : Blo 964590 964959 := bstep (se 1 (by rfl) ⟨723719, by rfl⟩ : syracuseStep 964959 = 1447439) B1447439
theorem B964987 : Blo 964590 964987 := bstep (se 1 (by rfl) ⟨723740, by rfl⟩ : syracuseStep 964987 = 1447481) B1447481
theorem B2177423 : Blo 964590 2177423 := bstep (se 1 (by rfl) ⟨1633067, by rfl⟩ : syracuseStep 2177423 = 3266135) B3266135
theorem B965039 : Blo 964590 965039 := bstep (se 1 (by rfl) ⟨723779, by rfl⟩ : syracuseStep 965039 = 1447559) B1447559
theorem B965063 : Blo 964590 965063 := bstep (se 1 (by rfl) ⟨723797, by rfl⟩ : syracuseStep 965063 = 1447595) B1447595
theorem B965083 : Blo 964590 965083 := bstep (se 1 (by rfl) ⟨723812, by rfl⟩ : syracuseStep 965083 = 1447625) B1447625
theorem B965159 : Blo 964590 965159 := bstep (se 1 (by rfl) ⟨723869, by rfl⟩ : syracuseStep 965159 = 1447739) B1447739
theorem B965199 : Blo 964590 965199 := bstep (se 1 (by rfl) ⟨723899, by rfl⟩ : syracuseStep 965199 = 1447799) B1447799
theorem B1030735 : Blo 964590 1030735 := bstep (se 1 (by rfl) ⟨773051, by rfl⟩ : syracuseStep 1030735 = 1546103) B1546103
theorem B965215 : Blo 964590 965215 := bstep (se 1 (by rfl) ⟨723911, by rfl⟩ : syracuseStep 965215 = 1447823) B1447823
theorem B965243 : Blo 964590 965243 := bstep (se 1 (by rfl) ⟨723932, by rfl⟩ : syracuseStep 965243 = 1447865) B1447865
theorem B965295 : Blo 964590 965295 := bstep (se 1 (by rfl) ⟨723971, by rfl⟩ : syracuseStep 965295 = 1447943) B1447943
theorem B965319 : Blo 964590 965319 := bstep (se 1 (by rfl) ⟨723989, by rfl⟩ : syracuseStep 965319 = 1447979) B1447979
theorem B2177747 : Blo 964590 2177747 := bstep (se 1 (by rfl) ⟨1633310, by rfl⟩ : syracuseStep 2177747 = 3266621) B3266621
theorem B3095255 : Blo 964590 3095255 := bstep (se 1 (by rfl) ⟨2321441, by rfl⟩ : syracuseStep 3095255 = 4642883) B4642883
theorem B965339 : Blo 964590 965339 := bstep (se 1 (by rfl) ⟨724004, by rfl⟩ : syracuseStep 965339 = 1448009) B1448009
theorem B965415 : Blo 964590 965415 := bstep (se 1 (by rfl) ⟨724061, by rfl⟩ : syracuseStep 965415 = 1448123) B1448123
theorem B965455 : Blo 964590 965455 := bstep (se 1 (by rfl) ⟨724091, by rfl⟩ : syracuseStep 965455 = 1448183) B1448183
theorem B965471 : Blo 964590 965471 := bstep (se 1 (by rfl) ⟨724103, by rfl⟩ : syracuseStep 965471 = 1448207) B1448207
theorem B965499 : Blo 964590 965499 := bstep (se 1 (by rfl) ⟨724124, by rfl⟩ : syracuseStep 965499 = 1448249) B1448249
theorem B965551 : Blo 964590 965551 := bstep (se 1 (by rfl) ⟨724163, by rfl⟩ : syracuseStep 965551 = 1448327) B1448327
theorem B965575 : Blo 964590 965575 := bstep (se 1 (by rfl) ⟨724181, by rfl⟩ : syracuseStep 965575 = 1448363) B1448363
theorem B965595 : Blo 964590 965595 := bstep (se 1 (by rfl) ⟨724196, by rfl⟩ : syracuseStep 965595 = 1448393) B1448393
theorem B965671 : Blo 964590 965671 := bstep (se 1 (by rfl) ⟨724253, by rfl⟩ : syracuseStep 965671 = 1448507) B1448507
theorem B965711 : Blo 964590 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B965727 : Blo 964590 965727 := bstep (se 1 (by rfl) ⟨724295, by rfl⟩ : syracuseStep 965727 = 1448591) B1448591
theorem B965755 : Blo 964590 965755 := bstep (se 1 (by rfl) ⟨724316, by rfl⟩ : syracuseStep 965755 = 1448633) B1448633
theorem B965807 : Blo 964590 965807 := bstep (se 1 (by rfl) ⟨724355, by rfl⟩ : syracuseStep 965807 = 1448711) B1448711
theorem B965831 : Blo 964590 965831 := bstep (se 1 (by rfl) ⟨724373, by rfl⟩ : syracuseStep 965831 = 1448747) B1448747
theorem B965851 : Blo 964590 965851 := bstep (se 1 (by rfl) ⟨724388, by rfl⟩ : syracuseStep 965851 = 1448777) B1448777
theorem B965927 : Blo 964590 965927 := bstep (se 1 (by rfl) ⟨724445, by rfl⟩ : syracuseStep 965927 = 1448891) B1448891
theorem B3259709 : Blo 964590 3259709 := bstep (se 3 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 3259709 = 1222391) B1222391
theorem B965967 : Blo 964590 965967 := bstep (se 1 (by rfl) ⟨724475, by rfl⟩ : syracuseStep 965967 = 1448951) B1448951
theorem B965983 : Blo 964590 965983 := bstep (se 1 (by rfl) ⟨724487, by rfl⟩ : syracuseStep 965983 = 1448975) B1448975
theorem B966011 : Blo 964590 966011 := bstep (se 1 (by rfl) ⟨724508, by rfl⟩ : syracuseStep 966011 = 1449017) B1449017
theorem B6962597 : Blo 964590 6962597 := bstep (se 4 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 6962597 = 1305487) B1305487
theorem B966063 : Blo 964590 966063 := bstep (se 1 (by rfl) ⟨724547, by rfl⟩ : syracuseStep 966063 = 1449095) B1449095
theorem B966087 : Blo 964590 966087 := bstep (se 1 (by rfl) ⟨724565, by rfl⟩ : syracuseStep 966087 = 1449131) B1449131
theorem B966107 : Blo 964590 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B3489313 : Blo 964590 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B966183 : Blo 964590 966183 := bstep (se 1 (by rfl) ⟨724637, by rfl⟩ : syracuseStep 966183 = 1449275) B1449275
theorem B966223 : Blo 964590 966223 := bstep (se 1 (by rfl) ⟨724667, by rfl⟩ : syracuseStep 966223 = 1449335) B1449335
theorem B1162831 : Blo 964590 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B966239 : Blo 964590 966239 := bstep (se 1 (by rfl) ⟨724679, by rfl⟩ : syracuseStep 966239 = 1449359) B1449359
theorem B966267 : Blo 964590 966267 := bstep (se 1 (by rfl) ⟨724700, by rfl⟩ : syracuseStep 966267 = 1449401) B1449401
theorem B2178683 : Blo 964590 2178683 := bstep (se 1 (by rfl) ⟨1634012, by rfl⟩ : syracuseStep 2178683 = 3268025) B3268025
theorem B3489427 : Blo 964590 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B966319 : Blo 964590 966319 := bstep (se 1 (by rfl) ⟨724739, by rfl⟩ : syracuseStep 966319 = 1449479) B1449479
theorem B4636349 : Blo 964590 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B966343 : Blo 964590 966343 := bstep (se 1 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 966343 = 1449515) B1449515
theorem B966363 : Blo 964590 966363 := bstep (se 1 (by rfl) ⟨724772, by rfl⟩ : syracuseStep 966363 = 1449545) B1449545
theorem B2178809 : Blo 964590 2178809 := bstep (se 2 (by rfl) ⟨817053, by rfl⟩ : syracuseStep 2178809 = 1634107) B1634107
theorem B966439 : Blo 964590 966439 := bstep (se 1 (by rfl) ⟨724829, by rfl⟩ : syracuseStep 966439 = 1449659) B1449659
theorem B966479 : Blo 964590 966479 := bstep (se 1 (by rfl) ⟨724859, by rfl⟩ : syracuseStep 966479 = 1449719) B1449719
theorem B966495 : Blo 964590 966495 := bstep (se 1 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 966495 = 1449743) B1449743
theorem B966523 : Blo 964590 966523 := bstep (se 1 (by rfl) ⟨724892, by rfl⟩ : syracuseStep 966523 = 1449785) B1449785
theorem B4636577 : Blo 964590 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B966575 : Blo 964590 966575 := bstep (se 1 (by rfl) ⟨724931, by rfl⟩ : syracuseStep 966575 = 1449863) B1449863
theorem B966599 : Blo 964590 966599 := bstep (se 1 (by rfl) ⟨724949, by rfl⟩ : syracuseStep 966599 = 1449899) B1449899
theorem B966619 : Blo 964590 966619 := bstep (se 1 (by rfl) ⟨724964, by rfl⟩ : syracuseStep 966619 = 1449929) B1449929
theorem B2179079 : Blo 964590 2179079 := bstep (se 1 (by rfl) ⟨1634309, by rfl⟩ : syracuseStep 2179079 = 3268619) B3268619
theorem B966695 : Blo 964590 966695 := bstep (se 1 (by rfl) ⟨725021, by rfl⟩ : syracuseStep 966695 = 1450043) B1450043
theorem B966735 : Blo 964590 966735 := bstep (se 1 (by rfl) ⟨725051, by rfl⟩ : syracuseStep 966735 = 1450103) B1450103
theorem B2179151 : Blo 964590 2179151 := bstep (se 1 (by rfl) ⟨1634363, by rfl⟩ : syracuseStep 2179151 = 3268727) B3268727
theorem B3620945 : Blo 964590 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B966751 : Blo 964590 966751 := bstep (se 1 (by rfl) ⟨725063, by rfl⟩ : syracuseStep 966751 = 1450127) B1450127
theorem B966779 : Blo 964590 966779 := bstep (se 1 (by rfl) ⟨725084, by rfl⟩ : syracuseStep 966779 = 1450169) B1450169
theorem B3260573 : Blo 964590 3260573 := bstep (se 3 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 3260573 = 1222715) B1222715
theorem B966831 : Blo 964590 966831 := bstep (se 1 (by rfl) ⟨725123, by rfl⟩ : syracuseStep 966831 = 1450247) B1450247
theorem B966855 : Blo 964590 966855 := bstep (se 1 (by rfl) ⟨725141, by rfl⟩ : syracuseStep 966855 = 1450283) B1450283
theorem B966875 : Blo 964590 966875 := bstep (se 1 (by rfl) ⟨725156, by rfl⟩ : syracuseStep 966875 = 1450313) B1450313
theorem B966951 : Blo 964590 966951 := bstep (se 1 (by rfl) ⟨725213, by rfl⟩ : syracuseStep 966951 = 1450427) B1450427
theorem B966991 : Blo 964590 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B967007 : Blo 964590 967007 := bstep (se 1 (by rfl) ⟨725255, by rfl⟩ : syracuseStep 967007 = 1450511) B1450511
theorem B967035 : Blo 964590 967035 := bstep (se 1 (by rfl) ⟨725276, by rfl⟩ : syracuseStep 967035 = 1450553) B1450553
theorem B967087 : Blo 964590 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B967111 : Blo 964590 967111 := bstep (se 1 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 967111 = 1450667) B1450667
theorem B967131 : Blo 964590 967131 := bstep (se 1 (by rfl) ⟨725348, by rfl⟩ : syracuseStep 967131 = 1450697) B1450697
theorem B6275593 : Blo 964590 6275593 := bstep (se 2 (by rfl) ⟨2353347, by rfl⟩ : syracuseStep 6275593 = 4706695) B4706695
theorem B967207 : Blo 964590 967207 := bstep (se 1 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 967207 = 1450811) B1450811
theorem B967247 : Blo 964590 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B967263 : Blo 964590 967263 := bstep (se 1 (by rfl) ⟨725447, by rfl⟩ : syracuseStep 967263 = 1450895) B1450895
theorem B967291 : Blo 964590 967291 := bstep (se 1 (by rfl) ⟨725468, by rfl⟩ : syracuseStep 967291 = 1450937) B1450937
theorem B1655419 : Blo 964590 1655419 := bstep (se 1 (by rfl) ⟨1241564, by rfl⟩ : syracuseStep 1655419 = 2483129) B2483129
theorem B967343 : Blo 964590 967343 := bstep (se 1 (by rfl) ⟨725507, by rfl⟩ : syracuseStep 967343 = 1451015) B1451015
theorem B3261113 : Blo 964590 3261113 := bstep (se 2 (by rfl) ⟨1222917, by rfl⟩ : syracuseStep 3261113 = 2445835) B2445835
theorem B2441927 : Blo 964590 2441927 := bstep (se 1 (by rfl) ⟨1831445, by rfl⟩ : syracuseStep 2441927 = 3662891) B3662891
theorem B967367 : Blo 964590 967367 := bstep (se 1 (by rfl) ⟨725525, by rfl⟩ : syracuseStep 967367 = 1451051) B1451051
theorem B967387 : Blo 964590 967387 := bstep (se 1 (by rfl) ⟨725540, by rfl⟩ : syracuseStep 967387 = 1451081) B1451081
theorem B967463 : Blo 964590 967463 := bstep (se 1 (by rfl) ⟨725597, by rfl⟩ : syracuseStep 967463 = 1451195) B1451195
theorem B967503 : Blo 964590 967503 := bstep (se 1 (by rfl) ⟨725627, by rfl⟩ : syracuseStep 967503 = 1451255) B1451255
theorem B967519 : Blo 964590 967519 := bstep (se 1 (by rfl) ⟨725639, by rfl⟩ : syracuseStep 967519 = 1451279) B1451279
theorem B967547 : Blo 964590 967547 := bstep (se 1 (by rfl) ⟨725660, by rfl⟩ : syracuseStep 967547 = 1451321) B1451321
theorem B967599 : Blo 964590 967599 := bstep (se 1 (by rfl) ⟨725699, by rfl⟩ : syracuseStep 967599 = 1451399) B1451399
theorem B967623 : Blo 964590 967623 := bstep (se 1 (by rfl) ⟨725717, by rfl⟩ : syracuseStep 967623 = 1451435) B1451435
theorem B967643 : Blo 964590 967643 := bstep (se 1 (by rfl) ⟨725732, by rfl⟩ : syracuseStep 967643 = 1451465) B1451465
theorem B1033255 : Blo 964590 1033255 := bstep (se 1 (by rfl) ⟨774941, by rfl⟩ : syracuseStep 1033255 = 1549883) B1549883
theorem B967719 : Blo 964590 967719 := bstep (se 1 (by rfl) ⟨725789, by rfl⟩ : syracuseStep 967719 = 1451579) B1451579
theorem B5882959 : Blo 964590 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B967759 : Blo 964590 967759 := bstep (se 1 (by rfl) ⟨725819, by rfl⟩ : syracuseStep 967759 = 1451639) B1451639
theorem B967775 : Blo 964590 967775 := bstep (se 1 (by rfl) ⟨725831, by rfl⟩ : syracuseStep 967775 = 1451663) B1451663
theorem B967803 : Blo 964590 967803 := bstep (se 1 (by rfl) ⟨725852, by rfl⟩ : syracuseStep 967803 = 1451705) B1451705
theorem B967855 : Blo 964590 967855 := bstep (se 1 (by rfl) ⟨725891, by rfl⟩ : syracuseStep 967855 = 1451783) B1451783
theorem B967879 : Blo 964590 967879 := bstep (se 1 (by rfl) ⟨725909, by rfl⟩ : syracuseStep 967879 = 1451819) B1451819
theorem B967899 : Blo 964590 967899 := bstep (se 1 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 967899 = 1451849) B1451849
theorem B3261707 : Blo 964590 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B967975 : Blo 964590 967975 := bstep (se 1 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 967975 = 1451963) B1451963
theorem B968015 : Blo 964590 968015 := bstep (se 1 (by rfl) ⟨726011, by rfl⟩ : syracuseStep 968015 = 1452023) B1452023
theorem B968031 : Blo 964590 968031 := bstep (se 1 (by rfl) ⟨726023, by rfl⟩ : syracuseStep 968031 = 1452047) B1452047
theorem B3523945 : Blo 964590 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B968059 : Blo 964590 968059 := bstep (se 1 (by rfl) ⟨726044, by rfl⟩ : syracuseStep 968059 = 1452089) B1452089
theorem B968111 : Blo 964590 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B968135 : Blo 964590 968135 := bstep (se 1 (by rfl) ⟨726101, by rfl⟩ : syracuseStep 968135 = 1452203) B1452203
theorem B968155 : Blo 964590 968155 := bstep (se 1 (by rfl) ⟨726116, by rfl⟩ : syracuseStep 968155 = 1452233) B1452233
theorem B3261977 : Blo 964590 3261977 := bstep (se 2 (by rfl) ⟨1223241, by rfl⟩ : syracuseStep 3261977 = 2446483) B2446483
theorem B968231 : Blo 964590 968231 := bstep (se 1 (by rfl) ⟨726173, by rfl⟩ : syracuseStep 968231 = 1452347) B1452347
theorem B968271 : Blo 964590 968271 := bstep (se 1 (by rfl) ⟨726203, by rfl⟩ : syracuseStep 968271 = 1452407) B1452407
theorem B968287 : Blo 964590 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B968315 : Blo 964590 968315 := bstep (se 1 (by rfl) ⟨726236, by rfl⟩ : syracuseStep 968315 = 1452473) B1452473
theorem B4638347 : Blo 964590 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B4900499 : Blo 964590 4900499 := bstep (se 1 (by rfl) ⟨3675374, by rfl⟩ : syracuseStep 4900499 = 7350749) B7350749
theorem B968367 : Blo 964590 968367 := bstep (se 1 (by rfl) ⟨726275, by rfl⟩ : syracuseStep 968367 = 1452551) B1452551
theorem B968391 : Blo 964590 968391 := bstep (se 1 (by rfl) ⟨726293, by rfl⟩ : syracuseStep 968391 = 1452587) B1452587
theorem B968411 : Blo 964590 968411 := bstep (se 1 (by rfl) ⟨726308, by rfl⟩ : syracuseStep 968411 = 1452617) B1452617
theorem B3720953 : Blo 964590 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B968487 : Blo 964590 968487 := bstep (se 1 (by rfl) ⟨726365, by rfl⟩ : syracuseStep 968487 = 1452731) B1452731
theorem B2443081 : Blo 964590 2443081 := bstep (se 2 (by rfl) ⟨916155, by rfl⟩ : syracuseStep 2443081 = 1832311) B1832311
theorem B968527 : Blo 964590 968527 := bstep (se 1 (by rfl) ⟨726395, by rfl⟩ : syracuseStep 968527 = 1452791) B1452791
theorem B4638559 : Blo 964590 4638559 := bstep (se 1 (by rfl) ⟨3478919, by rfl⟩ : syracuseStep 4638559 = 6957839) B6957839
theorem B968543 : Blo 964590 968543 := bstep (se 1 (by rfl) ⟨726407, by rfl⟩ : syracuseStep 968543 = 1452815) B1452815
theorem B968571 : Blo 964590 968571 := bstep (se 1 (by rfl) ⟨726428, by rfl⟩ : syracuseStep 968571 = 1452857) B1452857
theorem B5883911 : Blo 964590 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B4638809 : Blo 964590 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B12372101 : Blo 964590 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B6965477 : Blo 964590 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B7325963 : Blo 964590 7325963 := bstep (se 1 (by rfl) ⟨5494472, by rfl⟩ : syracuseStep 7325963 = 10988945) B10988945
theorem B4639037 : Blo 964590 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B1395127 : Blo 964590 1395127 := bstep (se 1 (by rfl) ⟨1046345, by rfl⟩ : syracuseStep 1395127 = 2092691) B2092691
theorem B8243693 : Blo 964590 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B3263111 : Blo 964590 3263111 := bstep (se 1 (by rfl) ⟨2447333, by rfl⟩ : syracuseStep 3263111 = 4894667) B4894667
theorem B3263165 : Blo 964590 3263165 := bstep (se 3 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 3263165 = 1223687) B1223687
theorem B3263327 : Blo 964590 3263327 := bstep (se 1 (by rfl) ⟨2447495, by rfl⟩ : syracuseStep 3263327 = 4894991) B4894991
theorem B2444215 : Blo 964590 2444215 := bstep (se 1 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 2444215 = 3666323) B3666323
theorem B3263489 : Blo 964590 3263489 := bstep (se 2 (by rfl) ⟨1223808, by rfl⟩ : syracuseStep 3263489 = 2447617) B2447617
theorem B1100839 : Blo 964590 1100839 := bstep (se 1 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 1100839 = 1651259) B1651259
theorem B3722507 : Blo 964590 3722507 := bstep (se 1 (by rfl) ⟨2791880, by rfl⟩ : syracuseStep 3722507 = 5583761) B5583761
theorem B9915671 : Blo 964590 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B5229989 : Blo 964590 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B7327421 : Blo 964590 7327421 := bstep (se 3 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 7327421 = 2747783) B2747783
theorem B2936519 : Blo 964590 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B3264299 : Blo 964590 3264299 := bstep (se 1 (by rfl) ⟨2448224, by rfl⟩ : syracuseStep 3264299 = 4896449) B4896449
theorem B28266353 : Blo 964590 28266353 := bstep (se 2 (by rfl) ⟨10599882, by rfl⟩ : syracuseStep 28266353 = 21199765) B21199765
theorem B2936737 : Blo 964590 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B3264569 : Blo 964590 3264569 := bstep (se 2 (by rfl) ⟨1224213, by rfl⟩ : syracuseStep 3264569 = 2448427) B2448427
theorem B7327907 : Blo 964590 7327907 := bstep (se 1 (by rfl) ⟨5495930, by rfl⟩ : syracuseStep 7327907 = 10991861) B10991861
theorem B6181181 : Blo 964590 6181181 := bstep (se 3 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 6181181 = 2317943) B2317943
theorem B16503101 : Blo 964590 16503101 := bstep (se 3 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 16503101 = 6188663) B6188663
theorem B2445673 : Blo 964590 2445673 := bstep (se 2 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 2445673 = 1834255) B1834255
theorem B3264893 : Blo 964590 3264893 := bstep (se 3 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 3264893 = 1224335) B1224335
theorem B2445947 : Blo 964590 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B3265163 : Blo 964590 3265163 := bstep (se 1 (by rfl) ⟨2448872, by rfl⟩ : syracuseStep 3265163 = 4897745) B4897745
theorem B61985587 : Blo 964590 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B3724289 : Blo 964590 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B27841603 : Blo 964590 27841603 := bstep (se 1 (by rfl) ⟨20881202, by rfl⟩ : syracuseStep 27841603 = 41762405) B41762405
theorem B6182081 : Blo 964590 6182081 := bstep (se 2 (by rfl) ⟨2318280, by rfl⟩ : syracuseStep 6182081 = 4636561) B4636561
theorem B2610575 : Blo 964590 2610575 := bstep (se 1 (by rfl) ⟨1957931, by rfl⟩ : syracuseStep 2610575 = 3915863) B3915863
theorem B4642267 : Blo 964590 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B3266081 : Blo 964590 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B1627897 : Blo 964590 1627897 := bstep (se 2 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 1627897 = 1220923) B1220923
theorem B3266297 : Blo 964590 3266297 := bstep (se 2 (by rfl) ⟨1224861, by rfl⟩ : syracuseStep 3266297 = 2449723) B2449723
theorem B3102457 : Blo 964590 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B12736291 : Blo 964590 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B37738349 : Blo 964590 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B1628167 : Blo 964590 1628167 := bstep (se 1 (by rfl) ⟨1221125, by rfl⟩ : syracuseStep 1628167 = 2442251) B2442251
theorem B3266567 : Blo 964590 3266567 := bstep (se 1 (by rfl) ⟨2449925, by rfl⟩ : syracuseStep 3266567 = 4899851) B4899851
theorem B6969401 : Blo 964590 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B3266675 : Blo 964590 3266675 := bstep (se 1 (by rfl) ⟨2450006, by rfl⟩ : syracuseStep 3266675 = 4900013) B4900013
theorem B3266945 : Blo 964590 3266945 := bstep (se 2 (by rfl) ⟨1225104, by rfl⟩ : syracuseStep 3266945 = 2450209) B2450209
theorem B2447759 : Blo 964590 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B1628599 : Blo 964590 1628599 := bstep (se 1 (by rfl) ⟨1221449, by rfl⟩ : syracuseStep 1628599 = 2442899) B2442899
theorem B16538093 : Blo 964590 16538093 := bstep (se 3 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 16538093 = 6201785) B6201785
theorem B7428631 : Blo 964590 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B7330337 : Blo 964590 7330337 := bstep (se 2 (by rfl) ⟨2748876, by rfl⟩ : syracuseStep 7330337 = 5497753) B5497753
theorem B1628795 : Blo 964590 1628795 := bstep (se 1 (by rfl) ⟨1221596, by rfl⟩ : syracuseStep 1628795 = 2443193) B2443193
theorem B2448083 : Blo 964590 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B1629193 : Blo 964590 1629193 := bstep (se 2 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 1629193 = 1221895) B1221895
theorem B1629355 : Blo 964590 1629355 := bstep (se 1 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 1629355 = 2444033) B2444033
theorem B3267755 : Blo 964590 3267755 := bstep (se 1 (by rfl) ⟨2450816, by rfl⟩ : syracuseStep 3267755 = 4901633) B4901633
theorem B9297143 : Blo 964590 9297143 := bstep (se 1 (by rfl) ⟨6972857, by rfl⟩ : syracuseStep 9297143 = 13945715) B13945715
theorem B1957225 : Blo 964590 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B2088335 : Blo 964590 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B1629659 : Blo 964590 1629659 := bstep (se 1 (by rfl) ⟨1222244, by rfl⟩ : syracuseStep 1629659 = 2444489) B2444489
theorem B9428669 : Blo 964590 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B3923645 : Blo 964590 3923645 := bstep (se 3 (by rfl) ⟨735683, by rfl⟩ : syracuseStep 3923645 = 1471367) B1471367
theorem B1629895 : Blo 964590 1629895 := bstep (se 1 (by rfl) ⟨1222421, by rfl⟩ : syracuseStep 1629895 = 2444843) B2444843
theorem B3268295 : Blo 964590 3268295 := bstep (se 1 (by rfl) ⟨2451221, by rfl⟩ : syracuseStep 3268295 = 4902443) B4902443
theorem B5496569 : Blo 964590 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B1630057 : Blo 964590 1630057 := bstep (se 2 (by rfl) ⟨611271, by rfl⟩ : syracuseStep 1630057 = 1222543) B1222543
theorem B4120429 : Blo 964590 4120429 := bstep (se 3 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 4120429 = 1545161) B1545161
theorem B14147459 : Blo 964590 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B1859681 : Blo 964590 1859681 := bstep (se 2 (by rfl) ⟨697380, by rfl⟩ : syracuseStep 1859681 = 1394761) B1394761
theorem B15098035 : Blo 964590 15098035 := bstep (se 1 (by rfl) ⟨11323526, by rfl⟩ : syracuseStep 15098035 = 22647053) B22647053
theorem B1630651 : Blo 964590 1630651 := bstep (se 1 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 1630651 = 2445977) B2445977
theorem B1630759 : Blo 964590 1630759 := bstep (se 1 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 1630759 = 2446139) B2446139
theorem B5890745 : Blo 964590 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B2319211 : Blo 964590 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B1631083 : Blo 964590 1631083 := bstep (se 1 (by rfl) ⟨1223312, by rfl⟩ : syracuseStep 1631083 = 2446625) B2446625
theorem B2450351 : Blo 964590 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B5498027 : Blo 964590 5498027 := bstep (se 1 (by rfl) ⟨4123520, by rfl⟩ : syracuseStep 5498027 = 8247041) B8247041
theorem B18834889 : Blo 964590 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B2450969 : Blo 964590 2450969 := bstep (se 2 (by rfl) ⟨919113, by rfl⟩ : syracuseStep 2450969 = 1838227) B1838227
theorem B3925543 : Blo 964590 3925543 := bstep (se 1 (by rfl) ⟨2944157, by rfl⟩ : syracuseStep 3925543 = 5888315) B5888315
theorem B3303035 : Blo 964590 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B9299603 : Blo 964590 9299603 := bstep (se 1 (by rfl) ⟨6974702, by rfl⟩ : syracuseStep 9299603 = 13949405) B13949405
theorem B3663575 : Blo 964590 3663575 := bstep (se 1 (by rfl) ⟨2747681, by rfl⟩ : syracuseStep 3663575 = 5495363) B5495363
theorem B1632143 : Blo 964590 1632143 := bstep (se 1 (by rfl) ⟨1224107, by rfl⟩ : syracuseStep 1632143 = 2448215) B2448215
theorem B2320289 : Blo 964590 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B1632379 : Blo 964590 1632379 := bstep (se 1 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 1632379 = 2448569) B2448569
theorem B1468891 : Blo 964590 1468891 := bstep (se 1 (by rfl) ⟨1101668, by rfl⟩ : syracuseStep 1468891 = 2203337) B2203337
theorem B1633243 : Blo 964590 1633243 := bstep (se 1 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 1633243 = 2449865) B2449865
theorem B7957547 : Blo 964590 7957547 := bstep (se 1 (by rfl) ⟨5968160, by rfl⟩ : syracuseStep 7957547 = 11936321) B11936321
theorem B1961435 : Blo 964590 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B1633871 : Blo 964590 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B89255843 : Blo 964590 89255843 := bstep (se 1 (by rfl) ⟨66941882, by rfl⟩ : syracuseStep 89255843 = 133883765) B133883765
theorem B1306633 : Blo 964590 1306633 := bstep (se 2 (by rfl) ⟨489987, by rfl⟩ : syracuseStep 1306633 = 979975) B979975
theorem B5500943 : Blo 964590 5500943 := bstep (se 1 (by rfl) ⟨4125707, by rfl⟩ : syracuseStep 5500943 = 8251415) B8251415
theorem B1863803 : Blo 964590 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B5501195 : Blo 964590 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B1831241 : Blo 964590 1831241 := bstep (se 2 (by rfl) ⟨686715, by rfl⟩ : syracuseStep 1831241 = 1373431) B1373431
theorem B13234691 : Blo 964590 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B3666491 : Blo 964590 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B35320529 : Blo 964590 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B1831673 : Blo 964590 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B18609047 : Blo 964590 18609047 := bstep (se 1 (by rfl) ⟨13956785, by rfl⟩ : syracuseStep 18609047 = 27913571) B27913571
theorem B2094007 : Blo 964590 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B2061787 : Blo 964590 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B52917745 : Blo 964590 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B2061863 : Blo 964590 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B31389281 : Blo 964590 31389281 := bstep (se 2 (by rfl) ⟨11770980, by rfl⟩ : syracuseStep 31389281 = 23541961) B23541961
theorem B5502653 : Blo 964590 5502653 := bstep (se 3 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 5502653 = 2063495) B2063495
theorem B7960313 : Blo 964590 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B8812547 : Blo 964590 8812547 := bstep (se 1 (by rfl) ⟨6609410, by rfl⟩ : syracuseStep 8812547 = 13218821) B13218821
theorem B8353849 : Blo 964590 8353849 := bstep (se 2 (by rfl) ⟨3132693, by rfl⟩ : syracuseStep 8353849 = 6265387) B6265387
theorem B4126801 : Blo 964590 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B1833131 : Blo 964590 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B6191639 : Blo 964590 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B2325017 : Blo 964590 2325017 := bstep (se 2 (by rfl) ⟨871881, by rfl⟩ : syracuseStep 2325017 = 1743763) B1743763
theorem B1833511 : Blo 964590 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B1833671 : Blo 964590 1833671 := bstep (se 1 (by rfl) ⟨1375253, by rfl⟩ : syracuseStep 1833671 = 2750507) B2750507
theorem B2325431 : Blo 964590 2325431 := bstep (se 1 (by rfl) ⟨1744073, by rfl⟩ : syracuseStep 2325431 = 3488147) B3488147
theorem B3669239 : Blo 964590 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B1375481 : Blo 964590 1375481 := bstep (se 2 (by rfl) ⟨515805, by rfl⟩ : syracuseStep 1375481 = 1031611) B1031611
theorem B7831363 : Blo 964590 7831363 := bstep (se 1 (by rfl) ⟨5873522, by rfl⟩ : syracuseStep 7831363 = 11747045) B11747045
theorem B1834825 : Blo 964590 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B5505043 : Blo 964590 5505043 := bstep (se 1 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 5505043 = 8257565) B8257565
theorem B1835273 : Blo 964590 1835273 := bstep (se 2 (by rfl) ⟨688227, by rfl⟩ : syracuseStep 1835273 = 1376455) B1376455
theorem B2752841 : Blo 964590 2752841 := bstep (se 2 (by rfl) ⟨1032315, by rfl⟩ : syracuseStep 2752841 = 2064631) B2064631
theorem B3670379 : Blo 964590 3670379 := bstep (se 1 (by rfl) ⟨2752784, by rfl⟩ : syracuseStep 3670379 = 5505569) B5505569
theorem B18612737 : Blo 964590 18612737 := bstep (se 2 (by rfl) ⟨6979776, by rfl⟩ : syracuseStep 18612737 = 13959553) B13959553
theorem B4129451 : Blo 964590 4129451 := bstep (se 1 (by rfl) ⟨3097088, by rfl⟩ : syracuseStep 4129451 = 6194177) B6194177
theorem B3671183 : Blo 964590 3671183 := bstep (se 1 (by rfl) ⟨2753387, by rfl⟩ : syracuseStep 3671183 = 5506775) B5506775
theorem B4130135 : Blo 964590 4130135 := bstep (se 1 (by rfl) ⟨3097601, by rfl⟩ : syracuseStep 4130135 = 6195203) B6195203
theorem B35292509 : Blo 964590 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B4883975 : Blo 964590 4883975 := bstep (se 1 (by rfl) ⟨3662981, by rfl⟩ : syracuseStep 4883975 = 7325963) B7325963
theorem B1836731 : Blo 964590 1836731 := bstep (se 1 (by rfl) ⟨1377548, by rfl⟩ : syracuseStep 1836731 = 2755097) B2755097
theorem B4884461 : Blo 964590 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B4884947 : Blo 964590 4884947 := bstep (se 1 (by rfl) ⟨3663710, by rfl⟩ : syracuseStep 4884947 = 7327421) B7327421
theorem B7834085 : Blo 964590 7834085 := bstep (se 4 (by rfl) ⟨734445, by rfl⟩ : syracuseStep 7834085 = 1468891) B1468891
theorem B18844235 : Blo 964590 18844235 := bstep (se 1 (by rfl) ⟨14133176, by rfl⟩ : syracuseStep 18844235 = 28266353) B28266353
theorem B3672823 : Blo 964590 3672823 := bstep (se 1 (by rfl) ⟨2754617, by rfl⟩ : syracuseStep 3672823 = 5509235) B5509235
theorem B4885271 : Blo 964590 4885271 := bstep (se 1 (by rfl) ⟨3663953, by rfl⟩ : syracuseStep 4885271 = 7327907) B7327907
theorem B7342973 : Blo 964590 7342973 := bstep (se 3 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 7342973 = 2753615) B2753615
theorem B12553217 : Blo 964590 12553217 := bstep (se 2 (by rfl) ⟨4707456, by rfl⟩ : syracuseStep 12553217 = 9414913) B9414913
theorem B3673127 : Blo 964590 3673127 := bstep (se 1 (by rfl) ⟨2754845, by rfl⟩ : syracuseStep 3673127 = 5509691) B5509691
theorem B1838675 : Blo 964590 1838675 := bstep (se 1 (by rfl) ⟨1379006, by rfl⟩ : syracuseStep 1838675 = 2758013) B2758013
theorem B1740383 : Blo 964590 1740383 := bstep (se 1 (by rfl) ⟨1305287, by rfl⟩ : syracuseStep 1740383 = 2610575) B2610575
theorem B4132883 : Blo 964590 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B4886891 : Blo 964590 4886891 := bstep (se 1 (by rfl) ⟨3665168, by rfl⟩ : syracuseStep 4886891 = 7330337) B7330337
theorem B1085863 : Blo 964590 1085863 := bstep (se 1 (by rfl) ⟨814397, by rfl⟩ : syracuseStep 1085863 = 1628795) B1628795
theorem B6198095 : Blo 964590 6198095 := bstep (se 1 (by rfl) ⟨4648571, by rfl⟩ : syracuseStep 6198095 = 9297143) B9297143
theorem B1446887 : Blo 964590 1446887 := bstep (se 1 (by rfl) ⟨1085165, by rfl⟩ : syracuseStep 1446887 = 2170331) B2170331
theorem B1086439 : Blo 964590 1086439 := bstep (se 1 (by rfl) ⟨814829, by rfl⟩ : syracuseStep 1086439 = 1629659) B1629659
theorem B1447145 : Blo 964590 1447145 := bstep (se 2 (by rfl) ⟨542679, by rfl⟩ : syracuseStep 1447145 = 1085359) B1085359
theorem B1447199 : Blo 964590 1447199 := bstep (se 1 (by rfl) ⟨1085399, by rfl⟩ : syracuseStep 1447199 = 2170799) B2170799
theorem B1742177 : Blo 964590 1742177 := bstep (se 2 (by rfl) ⟨653316, by rfl⟩ : syracuseStep 1742177 = 1306633) B1306633
theorem B1447367 : Blo 964590 1447367 := bstep (se 1 (by rfl) ⟨1085525, by rfl⟩ : syracuseStep 1447367 = 2171051) B2171051
theorem B9901549 : Blo 964590 9901549 := bstep (se 3 (by rfl) ⟨1856540, by rfl⟩ : syracuseStep 9901549 = 3713081) B3713081
theorem B5510693 : Blo 964590 5510693 := bstep (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) B1033255
theorem B4888349 : Blo 964590 4888349 := bstep (se 3 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 4888349 = 1833131) B1833131
theorem B1447721 : Blo 964590 1447721 := bstep (se 2 (by rfl) ⟨542895, by rfl⟩ : syracuseStep 1447721 = 1085791) B1085791
theorem B1447727 : Blo 964590 1447727 := bstep (se 1 (by rfl) ⟨1085795, by rfl⟩ : syracuseStep 1447727 = 2171591) B2171591
theorem B1448201 : Blo 964590 1448201 := bstep (se 2 (by rfl) ⟨543075, by rfl⟩ : syracuseStep 1448201 = 1086151) B1086151
theorem B1448303 : Blo 964590 1448303 := bstep (se 1 (by rfl) ⟨1086227, by rfl⟩ : syracuseStep 1448303 = 2172455) B2172455
theorem B82647449 : Blo 964590 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B2202023 : Blo 964590 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B6199735 : Blo 964590 6199735 := bstep (se 1 (by rfl) ⟨4649801, by rfl⟩ : syracuseStep 6199735 = 9299603) B9299603
theorem B1448519 : Blo 964590 1448519 := bstep (se 1 (by rfl) ⟨1086389, by rfl⟩ : syracuseStep 1448519 = 2172779) B2172779
theorem B2792009 : Blo 964590 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B1088095 : Blo 964590 1088095 := bstep (se 1 (by rfl) ⟨816071, by rfl⟩ : syracuseStep 1088095 = 1632143) B1632143
theorem B1546859 : Blo 964590 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B1448555 : Blo 964590 1448555 := bstep (se 1 (by rfl) ⟨1086416, by rfl⟩ : syracuseStep 1448555 = 2172833) B2172833
theorem B1448783 : Blo 964590 1448783 := bstep (se 1 (by rfl) ⟨1086587, by rfl⟩ : syracuseStep 1448783 = 2173175) B2173175
theorem B4135823 : Blo 964590 4135823 := bstep (se 1 (by rfl) ⟨3101867, by rfl⟩ : syracuseStep 4135823 = 6203735) B6203735
theorem B21437459 : Blo 964590 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B54467603 : Blo 964590 54467603 := bstep (se 1 (by rfl) ⟨40850702, by rfl⟩ : syracuseStep 54467603 = 81701405) B81701405
theorem B1449179 : Blo 964590 1449179 := bstep (se 1 (by rfl) ⟨1086884, by rfl⟩ : syracuseStep 1449179 = 2173769) B2173769
theorem B3677471 : Blo 964590 3677471 := bstep (se 1 (by rfl) ⟨2758103, by rfl⟩ : syracuseStep 3677471 = 5516207) B5516207
theorem B70556993 : Blo 964590 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B1449353 : Blo 964590 1449353 := bstep (se 2 (by rfl) ⟨543507, by rfl⟩ : syracuseStep 1449353 = 1087015) B1087015
theorem B2203193 : Blo 964590 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B4136507 : Blo 964590 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B2170529 : Blo 964590 2170529 := bstep (se 2 (by rfl) ⟨813948, by rfl⟩ : syracuseStep 2170529 = 1627897) B1627897
theorem B4136609 : Blo 964590 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B16981721 : Blo 964590 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B1089247 : Blo 964590 1089247 := bstep (se 1 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 1089247 = 1633871) B1633871
theorem B1449707 : Blo 964590 1449707 := bstep (se 1 (by rfl) ⟨1087280, by rfl⟩ : syracuseStep 1449707 = 2174561) B2174561
theorem B3481355 : Blo 964590 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1548089 : Blo 964590 1548089 := bstep (se 2 (by rfl) ⟨580533, by rfl⟩ : syracuseStep 1548089 = 1161067) B1161067
theorem B1449935 : Blo 964590 1449935 := bstep (se 1 (by rfl) ⟨1087451, by rfl⟩ : syracuseStep 1449935 = 2174903) B2174903
theorem B2170889 : Blo 964590 2170889 := bstep (se 2 (by rfl) ⟨814083, by rfl⟩ : syracuseStep 2170889 = 1628167) B1628167
theorem B1220827 : Blo 964590 1220827 := bstep (se 1 (by rfl) ⟨915620, by rfl⟩ : syracuseStep 1220827 = 1831241) B1831241
theorem B4301129 : Blo 964590 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B1450331 : Blo 964590 1450331 := bstep (se 1 (by rfl) ⟨1087748, by rfl⟩ : syracuseStep 1450331 = 2175497) B2175497
theorem B2171303 : Blo 964590 2171303 := bstep (se 1 (by rfl) ⟨1628477, by rfl⟩ : syracuseStep 2171303 = 3256955) B3256955
theorem B2171411 : Blo 964590 2171411 := bstep (se 1 (by rfl) ⟨1628558, by rfl⟩ : syracuseStep 2171411 = 3257117) B3257117
theorem B1450559 : Blo 964590 1450559 := bstep (se 1 (by rfl) ⟨1087919, by rfl⟩ : syracuseStep 1450559 = 2175839) B2175839
theorem B2171465 : Blo 964590 2171465 := bstep (se 2 (by rfl) ⟨814299, by rfl⟩ : syracuseStep 2171465 = 1628599) B1628599
theorem B1450679 : Blo 964590 1450679 := bstep (se 1 (by rfl) ⟨1088009, by rfl⟩ : syracuseStep 1450679 = 2176019) B2176019
theorem B9904841 : Blo 964590 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1450907 : Blo 964590 1450907 := bstep (se 1 (by rfl) ⟨1088180, by rfl⟩ : syracuseStep 1450907 = 2176361) B2176361
theorem B2171879 : Blo 964590 2171879 := bstep (se 1 (by rfl) ⟨1628909, by rfl⟩ : syracuseStep 2171879 = 3257819) B3257819
theorem B1451303 : Blo 964590 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B5875031 : Blo 964590 5875031 := bstep (se 1 (by rfl) ⟨4406273, by rfl⟩ : syracuseStep 5875031 = 8812547) B8812547
theorem B2172257 : Blo 964590 2172257 := bstep (se 2 (by rfl) ⟨814596, by rfl⟩ : syracuseStep 2172257 = 1629193) B1629193
theorem B1451387 : Blo 964590 1451387 := bstep (se 1 (by rfl) ⟨1088540, by rfl⟩ : syracuseStep 1451387 = 2177081) B2177081
theorem B2172347 : Blo 964590 2172347 := bstep (se 1 (by rfl) ⟨1629260, by rfl⟩ : syracuseStep 2172347 = 3258521) B3258521
theorem B1451513 : Blo 964590 1451513 := bstep (se 2 (by rfl) ⟨544317, by rfl⟩ : syracuseStep 1451513 = 1088635) B1088635
theorem B2172473 : Blo 964590 2172473 := bstep (se 2 (by rfl) ⟨814677, by rfl⟩ : syracuseStep 2172473 = 1629355) B1629355
theorem B1451615 : Blo 964590 1451615 := bstep (se 1 (by rfl) ⟨1088711, by rfl⟩ : syracuseStep 1451615 = 2177423) B2177423
theorem B1550011 : Blo 964590 1550011 := bstep (se 1 (by rfl) ⟨1162508, by rfl⟩ : syracuseStep 1550011 = 2325017) B2325017
theorem B1222447 : Blo 964590 1222447 := bstep (se 1 (by rfl) ⟨916835, by rfl⟩ : syracuseStep 1222447 = 1833671) B1833671
theorem B1451831 : Blo 964590 1451831 := bstep (se 1 (by rfl) ⟨1088873, by rfl⟩ : syracuseStep 1451831 = 2177747) B2177747
theorem B10463053 : Blo 964590 10463053 := bstep (se 3 (by rfl) ⟨1961822, by rfl⟩ : syracuseStep 10463053 = 3923645) B3923645
theorem B1550287 : Blo 964590 1550287 := bstep (se 1 (by rfl) ⟨1162715, by rfl⟩ : syracuseStep 1550287 = 2325431) B2325431
theorem B1550441 : Blo 964590 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B1452137 : Blo 964590 1452137 := bstep (se 2 (by rfl) ⟨544551, by rfl⟩ : syracuseStep 1452137 = 1089103) B1089103
theorem B2173139 : Blo 964590 2173139 := bstep (se 1 (by rfl) ⟨1629854, by rfl⟩ : syracuseStep 2173139 = 3259709) B3259709
theorem B2173193 : Blo 964590 2173193 := bstep (se 2 (by rfl) ⟨814947, by rfl⟩ : syracuseStep 2173193 = 1629895) B1629895
theorem B1452455 : Blo 964590 1452455 := bstep (se 1 (by rfl) ⟨1089341, by rfl⟩ : syracuseStep 1452455 = 2178683) B2178683
theorem B3090899 : Blo 964590 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B2173409 : Blo 964590 2173409 := bstep (se 2 (by rfl) ⟨815028, by rfl⟩ : syracuseStep 2173409 = 1630057) B1630057
theorem B1452539 : Blo 964590 1452539 := bstep (se 1 (by rfl) ⟨1089404, by rfl⟩ : syracuseStep 1452539 = 2178809) B2178809
theorem B3091051 : Blo 964590 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B1452665 : Blo 964590 1452665 := bstep (se 2 (by rfl) ⟨544749, by rfl⟩ : syracuseStep 1452665 = 1089499) B1089499
theorem B1452719 : Blo 964590 1452719 := bstep (se 1 (by rfl) ⟨1089539, by rfl⟩ : syracuseStep 1452719 = 2179079) B2179079
theorem B1452767 : Blo 964590 1452767 := bstep (se 1 (by rfl) ⟨1089575, by rfl⟩ : syracuseStep 1452767 = 2179151) B2179151
theorem B2173715 : Blo 964590 2173715 := bstep (se 1 (by rfl) ⟨1630286, by rfl⟩ : syracuseStep 2173715 = 3260573) B3260573
theorem B4467581 : Blo 964590 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B20130713 : Blo 964590 20130713 := bstep (se 2 (by rfl) ⟨7549017, by rfl⟩ : syracuseStep 20130713 = 15098035) B15098035
theorem B4959149 : Blo 964590 4959149 := bstep (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) B1859681
theorem B2174075 : Blo 964590 2174075 := bstep (se 1 (by rfl) ⟨1630556, by rfl⟩ : syracuseStep 2174075 = 3261113) B3261113
theorem B2174201 : Blo 964590 2174201 := bstep (se 2 (by rfl) ⟨815325, by rfl⟩ : syracuseStep 2174201 = 1630651) B1630651
theorem B4894019 : Blo 964590 4894019 := bstep (se 1 (by rfl) ⟨3670514, by rfl⟩ : syracuseStep 4894019 = 7341029) B7341029
theorem B8367457 : Blo 964590 8367457 := bstep (se 2 (by rfl) ⟨3137796, by rfl⟩ : syracuseStep 8367457 = 6275593) B6275593
theorem B2174345 : Blo 964590 2174345 := bstep (se 2 (by rfl) ⟨815379, by rfl⟩ : syracuseStep 2174345 = 1630759) B1630759
theorem B3255767 : Blo 964590 3255767 := bstep (se 1 (by rfl) ⟨2441825, by rfl⟩ : syracuseStep 3255767 = 4883651) B4883651
theorem B2207225 : Blo 964590 2207225 := bstep (se 2 (by rfl) ⟨827709, by rfl⟩ : syracuseStep 2207225 = 1655419) B1655419
theorem B2174471 : Blo 964590 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B2174651 : Blo 964590 2174651 := bstep (se 1 (by rfl) ⟨1630988, by rfl⟩ : syracuseStep 2174651 = 3261977) B3261977
theorem B3092231 : Blo 964590 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B4894505 : Blo 964590 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B2174777 : Blo 964590 2174777 := bstep (se 2 (by rfl) ⟨815541, by rfl⟩ : syracuseStep 2174777 = 1631083) B1631083
theorem B3092539 : Blo 964590 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B2175407 : Blo 964590 2175407 := bstep (se 1 (by rfl) ⟨1631555, by rfl⟩ : syracuseStep 2175407 = 3263111) B3263111
theorem B2175443 : Blo 964590 2175443 := bstep (se 1 (by rfl) ⟨1631582, by rfl⟩ : syracuseStep 2175443 = 3263165) B3263165
theorem B4698593 : Blo 964590 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B15708653 : Blo 964590 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B5878291 : Blo 964590 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B2175551 : Blo 964590 2175551 := bstep (se 1 (by rfl) ⟨1631663, by rfl⟩ : syracuseStep 2175551 = 3263327) B3263327
theorem B25113185 : Blo 964590 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B2175659 : Blo 964590 2175659 := bstep (se 1 (by rfl) ⟨1631744, by rfl⟩ : syracuseStep 2175659 = 3263489) B3263489
theorem B3486659 : Blo 964590 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B4895801 : Blo 964590 4895801 := bstep (se 2 (by rfl) ⟨1835925, by rfl⟩ : syracuseStep 4895801 = 3671851) B3671851
theorem B3257441 : Blo 964590 3257441 := bstep (se 2 (by rfl) ⟨1221540, by rfl⟩ : syracuseStep 3257441 = 2443081) B2443081
theorem B2176199 : Blo 964590 2176199 := bstep (se 1 (by rfl) ⟨1632149, by rfl⟩ : syracuseStep 2176199 = 3264299) B3264299
theorem B2176379 : Blo 964590 2176379 := bstep (se 1 (by rfl) ⟨1632284, by rfl⟩ : syracuseStep 2176379 = 3264569) B3264569
theorem B2176505 : Blo 964590 2176505 := bstep (se 2 (by rfl) ⟨816189, by rfl⟩ : syracuseStep 2176505 = 1632379) B1632379
theorem B2176595 : Blo 964590 2176595 := bstep (se 1 (by rfl) ⟨1632446, by rfl⟩ : syracuseStep 2176595 = 3264893) B3264893
theorem B2176775 : Blo 964590 2176775 := bstep (se 1 (by rfl) ⟨1632581, by rfl⟩ : syracuseStep 2176775 = 3265163) B3265163
theorem B964895 : Blo 964590 964895 := bstep (se 1 (by rfl) ⟨723671, by rfl⟩ : syracuseStep 964895 = 1447343) B1447343
theorem B964955 : Blo 964590 964955 := bstep (se 1 (by rfl) ⟨723716, by rfl⟩ : syracuseStep 964955 = 1447433) B1447433
theorem B2177387 : Blo 964590 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B964975 : Blo 964590 964975 := bstep (se 1 (by rfl) ⟨723731, by rfl⟩ : syracuseStep 964975 = 1447463) B1447463
theorem B965031 : Blo 964590 965031 := bstep (se 1 (by rfl) ⟨723773, by rfl⟩ : syracuseStep 965031 = 1447547) B1447547
theorem B3258791 : Blo 964590 3258791 := bstep (se 1 (by rfl) ⟨2444093, by rfl⟩ : syracuseStep 3258791 = 4888187) B4888187
theorem B965115 : Blo 964590 965115 := bstep (se 1 (by rfl) ⟨723836, by rfl⟩ : syracuseStep 965115 = 1447673) B1447673
theorem B2177531 : Blo 964590 2177531 := bstep (se 1 (by rfl) ⟨1633148, by rfl⟩ : syracuseStep 2177531 = 3266297) B3266297
theorem B965183 : Blo 964590 965183 := bstep (se 1 (by rfl) ⟨723887, by rfl⟩ : syracuseStep 965183 = 1447775) B1447775
theorem B3914303 : Blo 964590 3914303 := bstep (se 1 (by rfl) ⟨2935727, by rfl⟩ : syracuseStep 3914303 = 5871455) B5871455
theorem B965191 : Blo 964590 965191 := bstep (se 1 (by rfl) ⟨723893, by rfl⟩ : syracuseStep 965191 = 1447787) B1447787
theorem B3258953 : Blo 964590 3258953 := bstep (se 2 (by rfl) ⟨1222107, by rfl⟩ : syracuseStep 3258953 = 2444215) B2444215
theorem B2177657 : Blo 964590 2177657 := bstep (se 2 (by rfl) ⟨816621, by rfl⟩ : syracuseStep 2177657 = 1633243) B1633243
theorem B2177711 : Blo 964590 2177711 := bstep (se 1 (by rfl) ⟨1633283, by rfl⟩ : syracuseStep 2177711 = 3266567) B3266567
theorem B965343 : Blo 964590 965343 := bstep (se 1 (by rfl) ⟨724007, by rfl⟩ : syracuseStep 965343 = 1448015) B1448015
theorem B2177783 : Blo 964590 2177783 := bstep (se 1 (by rfl) ⟨1633337, by rfl⟩ : syracuseStep 2177783 = 3266675) B3266675
theorem B965423 : Blo 964590 965423 := bstep (se 1 (by rfl) ⟨724067, by rfl⟩ : syracuseStep 965423 = 1448135) B1448135
theorem B4701083 : Blo 964590 4701083 := bstep (se 1 (by rfl) ⟨3525812, by rfl⟩ : syracuseStep 4701083 = 7051625) B7051625
theorem B965531 : Blo 964590 965531 := bstep (se 1 (by rfl) ⟨724148, by rfl⟩ : syracuseStep 965531 = 1448297) B1448297
theorem B2177963 : Blo 964590 2177963 := bstep (se 1 (by rfl) ⟨1633472, by rfl⟩ : syracuseStep 2177963 = 3266945) B3266945
theorem B965583 : Blo 964590 965583 := bstep (se 1 (by rfl) ⟨724187, by rfl⟩ : syracuseStep 965583 = 1448375) B1448375
theorem B965607 : Blo 964590 965607 := bstep (se 1 (by rfl) ⟨724205, by rfl⟩ : syracuseStep 965607 = 1448411) B1448411
theorem B11025395 : Blo 964590 11025395 := bstep (se 1 (by rfl) ⟨8269046, by rfl⟩ : syracuseStep 11025395 = 16538093) B16538093
theorem B4897907 : Blo 964590 4897907 := bstep (se 1 (by rfl) ⟨3673430, by rfl⟩ : syracuseStep 4897907 = 7346861) B7346861
theorem B12369125 : Blo 964590 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B965919 : Blo 964590 965919 := bstep (se 1 (by rfl) ⟨724439, by rfl⟩ : syracuseStep 965919 = 1448879) B1448879
theorem B965979 : Blo 964590 965979 := bstep (se 1 (by rfl) ⟨724484, by rfl⟩ : syracuseStep 965979 = 1448969) B1448969
theorem B965999 : Blo 964590 965999 := bstep (se 1 (by rfl) ⟨724499, by rfl⟩ : syracuseStep 965999 = 1448999) B1448999
theorem B966055 : Blo 964590 966055 := bstep (se 1 (by rfl) ⟨724541, by rfl⟩ : syracuseStep 966055 = 1449083) B1449083
theorem B2178503 : Blo 964590 2178503 := bstep (se 1 (by rfl) ⟨1633877, by rfl⟩ : syracuseStep 2178503 = 3267755) B3267755
theorem B5291513 : Blo 964590 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B966139 : Blo 964590 966139 := bstep (se 1 (by rfl) ⟨724604, by rfl⟩ : syracuseStep 966139 = 1449209) B1449209
theorem B966207 : Blo 964590 966207 := bstep (se 1 (by rfl) ⟨724655, by rfl⟩ : syracuseStep 966207 = 1449311) B1449311
theorem B966215 : Blo 964590 966215 := bstep (se 1 (by rfl) ⟨724661, by rfl⟩ : syracuseStep 966215 = 1449323) B1449323
theorem B1392223 : Blo 964590 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B966367 : Blo 964590 966367 := bstep (se 1 (by rfl) ⟨724775, by rfl⟩ : syracuseStep 966367 = 1449551) B1449551
theorem B966447 : Blo 964590 966447 := bstep (se 1 (by rfl) ⟨724835, by rfl⟩ : syracuseStep 966447 = 1449671) B1449671
theorem B2178863 : Blo 964590 2178863 := bstep (se 1 (by rfl) ⟨1634147, by rfl⟩ : syracuseStep 2178863 = 3268295) B3268295
theorem B3915649 : Blo 964590 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B966555 : Blo 964590 966555 := bstep (se 1 (by rfl) ⟨724916, by rfl⟩ : syracuseStep 966555 = 1449833) B1449833
theorem B4898717 : Blo 964590 4898717 := bstep (se 3 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 4898717 = 1837019) B1837019
theorem B966607 : Blo 964590 966607 := bstep (se 1 (by rfl) ⟨724955, by rfl⟩ : syracuseStep 966607 = 1449911) B1449911
theorem B966631 : Blo 964590 966631 := bstep (se 1 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 966631 = 1449947) B1449947
theorem B3260627 : Blo 964590 3260627 := bstep (se 1 (by rfl) ⟨2445470, by rfl⟩ : syracuseStep 3260627 = 4890941) B4890941
theorem B966943 : Blo 964590 966943 := bstep (se 1 (by rfl) ⟨725207, by rfl⟩ : syracuseStep 966943 = 1450415) B1450415
theorem B967003 : Blo 964590 967003 := bstep (se 1 (by rfl) ⟨725252, by rfl⟩ : syracuseStep 967003 = 1450505) B1450505
theorem B967023 : Blo 964590 967023 := bstep (se 1 (by rfl) ⟨725267, by rfl⟩ : syracuseStep 967023 = 1450535) B1450535
theorem B31375781 : Blo 964590 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B11026853 : Blo 964590 11026853 := bstep (se 4 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 11026853 = 2067535) B2067535
theorem B967079 : Blo 964590 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B3260897 : Blo 964590 3260897 := bstep (se 2 (by rfl) ⟨1222836, by rfl⟩ : syracuseStep 3260897 = 2445673) B2445673
theorem B967163 : Blo 964590 967163 := bstep (se 1 (by rfl) ⟨725372, by rfl⟩ : syracuseStep 967163 = 1450745) B1450745
theorem B967231 : Blo 964590 967231 := bstep (se 1 (by rfl) ⟨725423, by rfl⟩ : syracuseStep 967231 = 1450847) B1450847
theorem B967239 : Blo 964590 967239 := bstep (se 1 (by rfl) ⟨725429, by rfl⟩ : syracuseStep 967239 = 1450859) B1450859
theorem B4899527 : Blo 964590 4899527 := bstep (se 1 (by rfl) ⟨3674645, by rfl⟩ : syracuseStep 4899527 = 7349291) B7349291
theorem B967391 : Blo 964590 967391 := bstep (se 1 (by rfl) ⟨725543, by rfl⟩ : syracuseStep 967391 = 1451087) B1451087
theorem B13910777 : Blo 964590 13910777 := bstep (se 2 (by rfl) ⟨5216541, by rfl⟩ : syracuseStep 13910777 = 10433083) B10433083
theorem B967471 : Blo 964590 967471 := bstep (se 1 (by rfl) ⟨725603, by rfl⟩ : syracuseStep 967471 = 1451207) B1451207
theorem B12370765 : Blo 964590 12370765 := bstep (se 3 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 12370765 = 4639037) B4639037
theorem B967579 : Blo 964590 967579 := bstep (se 1 (by rfl) ⟨725684, by rfl⟩ : syracuseStep 967579 = 1451369) B1451369
theorem B967631 : Blo 964590 967631 := bstep (se 1 (by rfl) ⟨725723, by rfl⟩ : syracuseStep 967631 = 1451447) B1451447
theorem B967655 : Blo 964590 967655 := bstep (se 1 (by rfl) ⟨725741, by rfl⟩ : syracuseStep 967655 = 1451483) B1451483
theorem B2442383 : Blo 964590 2442383 := bstep (se 1 (by rfl) ⟨1831787, by rfl⟩ : syracuseStep 2442383 = 3663575) B3663575
theorem B1033435 : Blo 964590 1033435 := bstep (se 1 (by rfl) ⟨775076, by rfl⟩ : syracuseStep 1033435 = 1550153) B1550153
theorem B967967 : Blo 964590 967967 := bstep (se 1 (by rfl) ⟨725975, by rfl⟩ : syracuseStep 967967 = 1451951) B1451951
theorem B6538583 : Blo 964590 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B968027 : Blo 964590 968027 := bstep (se 1 (by rfl) ⟨726020, by rfl⟩ : syracuseStep 968027 = 1452041) B1452041
theorem B968047 : Blo 964590 968047 := bstep (se 1 (by rfl) ⟨726035, by rfl⟩ : syracuseStep 968047 = 1452071) B1452071
theorem B968103 : Blo 964590 968103 := bstep (se 1 (by rfl) ⟨726077, by rfl⟩ : syracuseStep 968103 = 1452155) B1452155
theorem B968187 : Blo 964590 968187 := bstep (se 1 (by rfl) ⟨726140, by rfl⟩ : syracuseStep 968187 = 1452281) B1452281
theorem B968255 : Blo 964590 968255 := bstep (se 1 (by rfl) ⟨726191, by rfl⟩ : syracuseStep 968255 = 1452383) B1452383
theorem B968263 : Blo 964590 968263 := bstep (se 1 (by rfl) ⟨726197, by rfl⟩ : syracuseStep 968263 = 1452395) B1452395
theorem B3262139 : Blo 964590 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B968415 : Blo 964590 968415 := bstep (se 1 (by rfl) ⟨726311, by rfl⟩ : syracuseStep 968415 = 1452623) B1452623
theorem B968495 : Blo 964590 968495 := bstep (se 1 (by rfl) ⟨726371, by rfl⟩ : syracuseStep 968495 = 1452743) B1452743
theorem B2607839 : Blo 964590 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B2444327 : Blo 964590 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B23547019 : Blo 964590 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B8244443 : Blo 964590 8244443 := bstep (se 1 (by rfl) ⟨6183332, by rfl⟩ : syracuseStep 8244443 = 12366665) B12366665
theorem B12406031 : Blo 964590 12406031 := bstep (se 1 (by rfl) ⟨9304523, by rfl⟩ : syracuseStep 12406031 = 18609047) B18609047
theorem B2444681 : Blo 964590 2444681 := bstep (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) B1833511
theorem B4902281 : Blo 964590 4902281 := bstep (se 2 (by rfl) ⟨1838355, by rfl⟩ : syracuseStep 4902281 = 3676711) B3676711
theorem B3264083 : Blo 964590 3264083 := bstep (se 1 (by rfl) ⟨2448062, by rfl⟩ : syracuseStep 3264083 = 4896125) B4896125
theorem B7065251 : Blo 964590 7065251 := bstep (se 1 (by rfl) ⟨5298938, by rfl⟩ : syracuseStep 7065251 = 10597877) B10597877
theorem B20926187 : Blo 964590 20926187 := bstep (se 1 (by rfl) ⟨15694640, by rfl⟩ : syracuseStep 20926187 = 31389281) B31389281
theorem B5230493 : Blo 964590 5230493 := bstep (se 3 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 5230493 = 1961435) B1961435
theorem B2609633 : Blo 964590 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B2446159 : Blo 964590 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B4641731 : Blo 964590 4641731 := bstep (se 1 (by rfl) ⟨3481298, by rfl⟩ : syracuseStep 4641731 = 6962597) B6962597
theorem B10441817 : Blo 964590 10441817 := bstep (se 2 (by rfl) ⟨3915681, by rfl⟩ : syracuseStep 10441817 = 7831363) B7831363
theorem B2446433 : Blo 964590 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B5493905 : Blo 964590 5493905 := bstep (se 2 (by rfl) ⟨2060214, by rfl⟩ : syracuseStep 5493905 = 4120429) B4120429
theorem B3102047 : Blo 964590 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B2446807 : Blo 964590 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B9655853 : Blo 964590 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2447111 : Blo 964590 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B1627951 : Blo 964590 1627951 := bstep (se 1 (by rfl) ⟨1220963, by rfl⟩ : syracuseStep 1627951 = 2441927) B2441927
theorem B10442681 : Blo 964590 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B12376097 : Blo 964590 12376097 := bstep (se 2 (by rfl) ⟨4641036, by rfl⟩ : syracuseStep 12376097 = 9282073) B9282073
theorem B3266999 : Blo 964590 3266999 := bstep (se 1 (by rfl) ⟨2450249, by rfl⟩ : syracuseStep 3266999 = 4900499) B4900499
theorem B2480635 : Blo 964590 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B2447891 : Blo 964590 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B3922607 : Blo 964590 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B8248067 : Blo 964590 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B4643651 : Blo 964590 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B5495795 : Blo 964590 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B5234057 : Blo 964590 5234057 := bstep (se 2 (by rfl) ⟨1962771, by rfl⟩ : syracuseStep 5234057 = 3925543) B3925543
theorem B2481671 : Blo 964590 2481671 := bstep (se 1 (by rfl) ⟨1861253, by rfl⟩ : syracuseStep 2481671 = 3722507) B3722507
theorem B6610447 : Blo 964590 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B6184745 : Blo 964590 6184745 := bstep (se 2 (by rfl) ⟨2319279, by rfl⟩ : syracuseStep 6184745 = 4638559) B4638559
theorem B1957679 : Blo 964590 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B4120787 : Blo 964590 4120787 := bstep (se 1 (by rfl) ⟨3090590, by rfl⟩ : syracuseStep 4120787 = 6181181) B6181181
theorem B11002067 : Blo 964590 11002067 := bstep (se 1 (by rfl) ⟨8251550, by rfl⟩ : syracuseStep 11002067 = 16503101) B16503101
theorem B2449673 : Blo 964590 2449673 := bstep (se 2 (by rfl) ⟨918627, by rfl⟩ : syracuseStep 2449673 = 1837255) B1837255
theorem B2318665 : Blo 964590 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B5497253 : Blo 964590 5497253 := bstep (se 4 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 5497253 = 1030735) B1030735
theorem B1630631 : Blo 964590 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B1630793 : Blo 964590 1630793 := bstep (se 2 (by rfl) ⟨611547, by rfl⟩ : syracuseStep 1630793 = 1223095) B1223095
theorem B1860169 : Blo 964590 1860169 := bstep (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) B1395127
theorem B2450027 : Blo 964590 2450027 := bstep (se 1 (by rfl) ⟨1837520, by rfl⟩ : syracuseStep 2450027 = 3675041) B3675041
theorem B2482859 : Blo 964590 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B4121387 : Blo 964590 4121387 := bstep (se 1 (by rfl) ⟨3091040, by rfl⟩ : syracuseStep 4121387 = 6182081) B6182081
theorem B2450675 : Blo 964590 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B25158899 : Blo 964590 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B4646267 : Blo 964590 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B1467785 : Blo 964590 1467785 := bstep (se 2 (by rfl) ⟨550419, by rfl⟩ : syracuseStep 1467785 = 1100839) B1100839
theorem B1631839 : Blo 964590 1631839 := bstep (se 1 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 1631839 = 2447759) B2447759
theorem B2451131 : Blo 964590 2451131 := bstep (se 1 (by rfl) ⟨1838348, by rfl⟩ : syracuseStep 2451131 = 3676697) B3676697
theorem B1632055 : Blo 964590 1632055 := bstep (se 1 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 1632055 = 2448083) B2448083
theorem B7956461 : Blo 964590 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B21227501 : Blo 964590 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B2451667 : Blo 964590 2451667 := bstep (se 1 (by rfl) ⟨1838750, by rfl⟩ : syracuseStep 2451667 = 3677501) B3677501
theorem B1632521 : Blo 964590 1632521 := bstep (se 2 (by rfl) ⟨612195, by rfl⟩ : syracuseStep 1632521 = 1224391) B1224391
theorem B4647341 : Blo 964590 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B6285779 : Blo 964590 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B3664379 : Blo 964590 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B9431639 : Blo 964590 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B6187843 : Blo 964590 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B1633513 : Blo 964590 1633513 := bstep (se 2 (by rfl) ⟨612567, by rfl⟩ : syracuseStep 1633513 = 1225135) B1225135
theorem B1633567 : Blo 964590 1633567 := bstep (se 1 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 1633567 = 2450351) B2450351
theorem B3665351 : Blo 964590 3665351 := bstep (se 1 (by rfl) ⟨2749013, by rfl⟩ : syracuseStep 3665351 = 5498027) B5498027
theorem B1633979 : Blo 964590 1633979 := bstep (se 1 (by rfl) ⟨1225484, by rfl⟩ : syracuseStep 1633979 = 2450969) B2450969
theorem B4648765 : Blo 964590 4648765 := bstep (se 3 (by rfl) ⟨871643, by rfl⟩ : syracuseStep 4648765 = 1743287) B1743287
theorem B37122137 : Blo 964590 37122137 := bstep (se 2 (by rfl) ⟨13920801, by rfl⟩ : syracuseStep 37122137 = 27841603) B27841603
theorem B2749049 : Blo 964590 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B6189689 : Blo 964590 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B5305031 : Blo 964590 5305031 := bstep (se 1 (by rfl) ⟨3978773, by rfl⟩ : syracuseStep 5305031 = 7957547) B7957547
theorem B59503895 : Blo 964590 59503895 := bstep (se 1 (by rfl) ⟨44627921, by rfl⟩ : syracuseStep 59503895 = 89255843) B89255843
theorem B2061607 : Blo 964590 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B3667295 : Blo 964590 3667295 := bstep (se 1 (by rfl) ⟨2750471, by rfl⟩ : syracuseStep 3667295 = 5500943) B5500943
theorem B11138465 : Blo 964590 11138465 := bstep (se 2 (by rfl) ⟨4176924, by rfl⟩ : syracuseStep 11138465 = 8353849) B8353849
theorem B1242535 : Blo 964590 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B5502401 : Blo 964590 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B3667463 : Blo 964590 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B11761595 : Blo 964590 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B3667949 : Blo 964590 3667949 := bstep (se 3 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 3667949 = 1375481) B1375481
theorem B1374575 : Blo 964590 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B3668435 : Blo 964590 3668435 := bstep (se 1 (by rfl) ⟨2751326, by rfl⟩ : syracuseStep 3668435 = 5502653) B5502653
theorem B4127759 : Blo 964590 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B2063503 : Blo 964590 2063503 := bstep (se 1 (by rfl) ⟨1547627, by rfl⟩ : syracuseStep 2063503 = 3095255) B3095255
theorem B4652417 : Blo 964590 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B4652569 : Blo 964590 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B7340057 : Blo 964590 7340057 := bstep (se 2 (by rfl) ⟨2752521, by rfl⟩ : syracuseStep 7340057 = 5505043) B5505043
theorem B1835227 : Blo 964590 1835227 := bstep (se 1 (by rfl) ⟨1376420, by rfl⟩ : syracuseStep 1835227 = 2752841) B2752841
theorem B2752967 : Blo 964590 2752967 := bstep (se 1 (by rfl) ⟨2064725, by rfl⟩ : syracuseStep 2752967 = 4129451) B4129451
theorem B9273851 : Blo 964590 9273851 := bstep (se 1 (by rfl) ⟨6955388, by rfl⟩ : syracuseStep 9273851 = 13910777) B13910777
theorem B4359055 : Blo 964590 4359055 := bstep (se 1 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 4359055 = 6538583) B6538583
theorem B2753423 : Blo 964590 2753423 := bstep (se 1 (by rfl) ⟨2065067, by rfl⟩ : syracuseStep 2753423 = 4130135) B4130135
theorem B23528339 : Blo 964590 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B1377913 : Blo 964590 1377913 := bstep (se 2 (by rfl) ⟨516717, by rfl⟩ : syracuseStep 1377913 = 1033435) B1033435
theorem B6620957 : Blo 964590 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1738559 : Blo 964590 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B2066681 : Blo 964590 2066681 := bstep (se 2 (by rfl) ⟨775005, by rfl⟩ : syracuseStep 2066681 = 1550011) B1550011
theorem B2067049 : Blo 964590 2067049 := bstep (se 2 (by rfl) ⟨775143, by rfl⟩ : syracuseStep 2067049 = 1550287) B1550287
theorem B1739755 : Blo 964590 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B4132063 : Blo 964590 4132063 := bstep (se 1 (by rfl) ⟨3099047, by rfl⟩ : syracuseStep 4132063 = 6198095) B6198095
theorem B16485605 : Blo 964590 16485605 := bstep (se 4 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 16485605 = 3091051) B3091051
theorem B2068031 : Blo 964590 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B3673795 : Blo 964590 3673795 := bstep (se 1 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 3673795 = 5510693) B5510693
theorem B31396025 : Blo 964590 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B2757215 : Blo 964590 2757215 := bstep (se 1 (by rfl) ⟨2067911, by rfl⟩ : syracuseStep 2757215 = 4135823) B4135823
theorem B14291639 : Blo 964590 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B36311735 : Blo 964590 36311735 := bstep (se 1 (by rfl) ⟨27233801, by rfl⟩ : syracuseStep 36311735 = 54467603) B54467603
theorem B2757671 : Blo 964590 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B6198353 : Blo 964590 6198353 := bstep (se 2 (by rfl) ⟨2324382, by rfl⟩ : syracuseStep 6198353 = 4648765) B4648765
theorem B1447019 : Blo 964590 1447019 := bstep (se 1 (by rfl) ⟨1085264, by rfl⟩ : syracuseStep 1447019 = 2170529) B2170529
theorem B2757739 : Blo 964590 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B1447259 : Blo 964590 1447259 := bstep (se 1 (by rfl) ⟨1085444, by rfl⟩ : syracuseStep 1447259 = 2170889) B2170889
theorem B4134509 : Blo 964590 4134509 := bstep (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) B1550441
theorem B1447535 : Blo 964590 1447535 := bstep (se 1 (by rfl) ⟨1085651, by rfl⟩ : syracuseStep 1447535 = 2171303) B2171303
theorem B1087087 : Blo 964590 1087087 := bstep (se 1 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 1087087 = 1630631) B1630631
theorem B1447607 : Blo 964590 1447607 := bstep (se 1 (by rfl) ⟨1085705, by rfl⟩ : syracuseStep 1447607 = 2171411) B2171411
theorem B1447643 : Blo 964590 1447643 := bstep (se 1 (by rfl) ⟨1085732, by rfl⟩ : syracuseStep 1447643 = 2171465) B2171465
theorem B1087195 : Blo 964590 1087195 := bstep (se 1 (by rfl) ⟨815396, by rfl⟩ : syracuseStep 1087195 = 1630793) B1630793
theorem B1447817 : Blo 964590 1447817 := bstep (se 2 (by rfl) ⟨542931, by rfl⟩ : syracuseStep 1447817 = 1085863) B1085863
theorem B1447919 : Blo 964590 1447919 := bstep (se 1 (by rfl) ⟨1085939, by rfl⟩ : syracuseStep 1447919 = 2171879) B2171879
theorem B7837721 : Blo 964590 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1448171 : Blo 964590 1448171 := bstep (se 1 (by rfl) ⟨1086128, by rfl⟩ : syracuseStep 1448171 = 2172257) B2172257
theorem B1448231 : Blo 964590 1448231 := bstep (se 1 (by rfl) ⟨1086173, by rfl⟩ : syracuseStep 1448231 = 2172347) B2172347
theorem B1448315 : Blo 964590 1448315 := bstep (se 1 (by rfl) ⟨1086236, by rfl⟩ : syracuseStep 1448315 = 2172473) B2172473
theorem B5872061 : Blo 964590 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B12392909 : Blo 964590 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B1448585 : Blo 964590 1448585 := bstep (se 2 (by rfl) ⟨543219, by rfl⟩ : syracuseStep 1448585 = 1086439) B1086439
theorem B1448759 : Blo 964590 1448759 := bstep (se 1 (by rfl) ⟨1086569, by rfl⟩ : syracuseStep 1448759 = 2173139) B2173139
theorem B1448795 : Blo 964590 1448795 := bstep (se 1 (by rfl) ⟨1086596, by rfl⟩ : syracuseStep 1448795 = 2173193) B2173193
theorem B1088347 : Blo 964590 1088347 := bstep (se 1 (by rfl) ⟨816260, by rfl⟩ : syracuseStep 1088347 = 1632521) B1632521
theorem B1448939 : Blo 964590 1448939 := bstep (se 1 (by rfl) ⟨1086704, by rfl⟩ : syracuseStep 1448939 = 2173409) B2173409
theorem B10460285 : Blo 964590 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B1449143 : Blo 964590 1449143 := bstep (se 1 (by rfl) ⟨1086857, by rfl⟩ : syracuseStep 1449143 = 2173715) B2173715
theorem B1449383 : Blo 964590 1449383 := bstep (se 1 (by rfl) ⟨1087037, by rfl⟩ : syracuseStep 1449383 = 2174075) B2174075
theorem B1449467 : Blo 964590 1449467 := bstep (se 1 (by rfl) ⟨1087100, by rfl⟩ : syracuseStep 1449467 = 2174201) B2174201
theorem B1449563 : Blo 964590 1449563 := bstep (se 1 (by rfl) ⟨1087172, by rfl⟩ : syracuseStep 1449563 = 2174345) B2174345
theorem B2170511 : Blo 964590 2170511 := bstep (se 1 (by rfl) ⟨1627883, by rfl⟩ : syracuseStep 2170511 = 3255767) B3255767
theorem B1449647 : Blo 964590 1449647 := bstep (se 1 (by rfl) ⟨1087235, by rfl⟩ : syracuseStep 1449647 = 2174471) B2174471
theorem B2170601 : Blo 964590 2170601 := bstep (se 2 (by rfl) ⟨813975, by rfl⟩ : syracuseStep 2170601 = 1627951) B1627951
theorem B1449767 : Blo 964590 1449767 := bstep (se 1 (by rfl) ⟨1087325, by rfl⟩ : syracuseStep 1449767 = 2174651) B2174651
theorem B1089319 : Blo 964590 1089319 := bstep (se 1 (by rfl) ⟨816989, by rfl⟩ : syracuseStep 1089319 = 1633979) B1633979
theorem B1449851 : Blo 964590 1449851 := bstep (se 1 (by rfl) ⟨1087388, by rfl⟩ : syracuseStep 1449851 = 2174777) B2174777
theorem B24748091 : Blo 964590 24748091 := bstep (se 1 (by rfl) ⟨18561068, by rfl⟩ : syracuseStep 24748091 = 37122137) B37122137
theorem B24813701 : Blo 964590 24813701 := bstep (se 4 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 24813701 = 4652569) B4652569
theorem B1450271 : Blo 964590 1450271 := bstep (se 1 (by rfl) ⟨1087703, by rfl⟩ : syracuseStep 1450271 = 2175407) B2175407
theorem B1450295 : Blo 964590 1450295 := bstep (se 1 (by rfl) ⟨1087721, by rfl⟩ : syracuseStep 1450295 = 2175443) B2175443
theorem B1450367 : Blo 964590 1450367 := bstep (se 1 (by rfl) ⟨1087775, by rfl⟩ : syracuseStep 1450367 = 2175551) B2175551
theorem B1450439 : Blo 964590 1450439 := bstep (se 1 (by rfl) ⟨1087829, by rfl⟩ : syracuseStep 1450439 = 2175659) B2175659
theorem B8266313 : Blo 964590 8266313 := bstep (se 2 (by rfl) ⟨3099867, by rfl⟩ : syracuseStep 8266313 = 6199735) B6199735
theorem B2171627 : Blo 964590 2171627 := bstep (se 1 (by rfl) ⟨1628720, by rfl⟩ : syracuseStep 2171627 = 3257441) B3257441
theorem B1450793 : Blo 964590 1450793 := bstep (se 2 (by rfl) ⟨544047, by rfl⟩ : syracuseStep 1450793 = 1088095) B1088095
theorem B1450799 : Blo 964590 1450799 := bstep (se 1 (by rfl) ⟨1088099, by rfl⟩ : syracuseStep 1450799 = 2176199) B2176199
theorem B1450919 : Blo 964590 1450919 := bstep (se 1 (by rfl) ⟨1088189, by rfl⟩ : syracuseStep 1450919 = 2176379) B2176379
theorem B1451003 : Blo 964590 1451003 := bstep (se 1 (by rfl) ⟨1088252, by rfl⟩ : syracuseStep 1451003 = 2176505) B2176505
theorem B1451063 : Blo 964590 1451063 := bstep (se 1 (by rfl) ⟨1088297, by rfl⟩ : syracuseStep 1451063 = 2176595) B2176595
theorem B1451183 : Blo 964590 1451183 := bstep (se 1 (by rfl) ⟨1088387, by rfl⟩ : syracuseStep 1451183 = 2176775) B2176775
theorem B7841063 : Blo 964590 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B1451591 : Blo 964590 1451591 := bstep (se 1 (by rfl) ⟨1088693, by rfl⟩ : syracuseStep 1451591 = 2177387) B2177387
theorem B2172527 : Blo 964590 2172527 := bstep (se 1 (by rfl) ⟨1629395, by rfl⟩ : syracuseStep 2172527 = 3258791) B3258791
theorem B1451687 : Blo 964590 1451687 := bstep (se 1 (by rfl) ⟨1088765, by rfl⟩ : syracuseStep 1451687 = 2177531) B2177531
theorem B2172635 : Blo 964590 2172635 := bstep (se 1 (by rfl) ⟨1629476, by rfl⟩ : syracuseStep 2172635 = 3258953) B3258953
theorem B1451771 : Blo 964590 1451771 := bstep (se 1 (by rfl) ⟨1088828, by rfl⟩ : syracuseStep 1451771 = 2177657) B2177657
theorem B1451807 : Blo 964590 1451807 := bstep (se 1 (by rfl) ⟨1088855, by rfl⟩ : syracuseStep 1451807 = 2177711) B2177711
theorem B1451855 : Blo 964590 1451855 := bstep (se 1 (by rfl) ⟨1088891, by rfl⟩ : syracuseStep 1451855 = 2177783) B2177783
theorem B1451975 : Blo 964590 1451975 := bstep (se 1 (by rfl) ⟨1088981, by rfl⟩ : syracuseStep 1451975 = 2177963) B2177963
theorem B7350263 : Blo 964590 7350263 := bstep (se 1 (by rfl) ⟨5512697, by rfl⟩ : syracuseStep 7350263 = 11025395) B11025395
theorem B1452329 : Blo 964590 1452329 := bstep (se 2 (by rfl) ⟨544623, by rfl⟩ : syracuseStep 1452329 = 1089247) B1089247
theorem B1452335 : Blo 964590 1452335 := bstep (se 1 (by rfl) ⟨1089251, by rfl⟩ : syracuseStep 1452335 = 2178503) B2178503
theorem B5220865 : Blo 964590 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1452575 : Blo 964590 1452575 := bstep (se 1 (by rfl) ⟨1089431, by rfl⟩ : syracuseStep 1452575 = 2178863) B2178863
theorem B11021021 : Blo 964590 11021021 := bstep (se 3 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 11021021 = 4132883) B4132883
theorem B2173751 : Blo 964590 2173751 := bstep (se 1 (by rfl) ⟨1630313, by rfl⟩ : syracuseStep 2173751 = 3260627) B3260627
theorem B1223515 : Blo 964590 1223515 := bstep (se 1 (by rfl) ⟨917636, by rfl⟩ : syracuseStep 1223515 = 1835273) B1835273
theorem B20917187 : Blo 964590 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B7351235 : Blo 964590 7351235 := bstep (se 1 (by rfl) ⟨5513426, by rfl⟩ : syracuseStep 7351235 = 11026853) B11026853
theorem B2173931 : Blo 964590 2173931 := bstep (se 1 (by rfl) ⟨1630448, by rfl⟩ : syracuseStep 2173931 = 3260897) B3260897
theorem B3091553 : Blo 964590 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B3255983 : Blo 964590 3255983 := bstep (se 1 (by rfl) ⟨2441987, by rfl⟩ : syracuseStep 3255983 = 4883975) B4883975
theorem B16494353 : Blo 964590 16494353 := bstep (se 2 (by rfl) ⟨6185382, by rfl⟩ : syracuseStep 16494353 = 12370765) B12370765
theorem B2174759 : Blo 964590 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B1224487 : Blo 964590 1224487 := bstep (se 1 (by rfl) ⟨918365, by rfl⟩ : syracuseStep 1224487 = 1836731) B1836731
theorem B3256307 : Blo 964590 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B3256631 : Blo 964590 3256631 := bstep (se 1 (by rfl) ⟨2442473, by rfl⟩ : syracuseStep 3256631 = 4884947) B4884947
theorem B5222723 : Blo 964590 5222723 := bstep (se 1 (by rfl) ⟨3917042, by rfl⟩ : syracuseStep 5222723 = 7834085) B7834085
theorem B12562823 : Blo 964590 12562823 := bstep (se 1 (by rfl) ⟨9422117, by rfl⟩ : syracuseStep 12562823 = 18844235) B18844235
theorem B3256847 : Blo 964590 3256847 := bstep (se 1 (by rfl) ⟨2442635, by rfl⟩ : syracuseStep 3256847 = 4885271) B4885271
theorem B4895315 : Blo 964590 4895315 := bstep (se 1 (by rfl) ⟨3671486, by rfl⟩ : syracuseStep 4895315 = 7342973) B7342973
theorem B8368811 : Blo 964590 8368811 := bstep (se 1 (by rfl) ⟨6276608, by rfl⟩ : syracuseStep 8368811 = 12553217) B12553217
theorem B2175785 : Blo 964590 2175785 := bstep (se 2 (by rfl) ⟨815919, by rfl⟩ : syracuseStep 2175785 = 1631839) B1631839
theorem B8270687 : Blo 964590 8270687 := bstep (se 1 (by rfl) ⟨6203015, by rfl⟩ : syracuseStep 8270687 = 12406031) B12406031
theorem B2176055 : Blo 964590 2176055 := bstep (se 1 (by rfl) ⟨1632041, by rfl⟩ : syracuseStep 2176055 = 3264083) B3264083
theorem B1225783 : Blo 964590 1225783 := bstep (se 1 (by rfl) ⟨919337, by rfl⟩ : syracuseStep 1225783 = 1838675) B1838675
theorem B1160255 : Blo 964590 1160255 := bstep (se 1 (by rfl) ⟨870191, by rfl⟩ : syracuseStep 1160255 = 1740383) B1740383
theorem B2176073 : Blo 964590 2176073 := bstep (se 2 (by rfl) ⟨816027, by rfl⟩ : syracuseStep 2176073 = 1632055) B1632055
theorem B3486995 : Blo 964590 3486995 := bstep (se 1 (by rfl) ⟨2615246, by rfl⟩ : syracuseStep 3486995 = 5230493) B5230493
theorem B3257927 : Blo 964590 3257927 := bstep (se 1 (by rfl) ⟨2443445, by rfl⟩ : syracuseStep 3257927 = 4886891) B4886891
theorem B3094487 : Blo 964590 3094487 := bstep (se 1 (by rfl) ⟨2320865, by rfl⟩ : syracuseStep 3094487 = 4641731) B4641731
theorem B964591 : Blo 964590 964591 := bstep (se 1 (by rfl) ⟨723443, by rfl⟩ : syracuseStep 964591 = 1446887) B1446887
theorem B6961211 : Blo 964590 6961211 := bstep (se 1 (by rfl) ⟨5220908, by rfl⟩ : syracuseStep 6961211 = 10441817) B10441817
theorem B964763 : Blo 964590 964763 := bstep (se 1 (by rfl) ⟨723572, by rfl⟩ : syracuseStep 964763 = 1447145) B1447145
theorem B964799 : Blo 964590 964799 := bstep (se 1 (by rfl) ⟨723599, by rfl⟩ : syracuseStep 964799 = 1447199) B1447199
theorem B1161451 : Blo 964590 1161451 := bstep (se 1 (by rfl) ⟨871088, by rfl⟩ : syracuseStep 1161451 = 1742177) B1742177
theorem B964911 : Blo 964590 964911 := bstep (se 1 (by rfl) ⟨723683, by rfl⟩ : syracuseStep 964911 = 1447367) B1447367
theorem B4897097 : Blo 964590 4897097 := bstep (se 2 (by rfl) ⟨1836411, by rfl⟩ : syracuseStep 4897097 = 3672823) B3672823
theorem B3258899 : Blo 964590 3258899 := bstep (se 1 (by rfl) ⟨2444174, by rfl⟩ : syracuseStep 3258899 = 4888349) B4888349
theorem B965147 : Blo 964590 965147 := bstep (se 1 (by rfl) ⟨723860, by rfl⟩ : syracuseStep 965147 = 1447721) B1447721
theorem B965151 : Blo 964590 965151 := bstep (se 1 (by rfl) ⟨723863, by rfl⟩ : syracuseStep 965151 = 1447727) B1447727
theorem B6961787 : Blo 964590 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B965467 : Blo 964590 965467 := bstep (se 1 (by rfl) ⟨724100, by rfl⟩ : syracuseStep 965467 = 1448201) B1448201
theorem B965535 : Blo 964590 965535 := bstep (se 1 (by rfl) ⟨724151, by rfl⟩ : syracuseStep 965535 = 1448303) B1448303
theorem B55098299 : Blo 964590 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B2177999 : Blo 964590 2177999 := bstep (se 1 (by rfl) ⟨1633499, by rfl⟩ : syracuseStep 2177999 = 3266999) B3266999
theorem B2178017 : Blo 964590 2178017 := bstep (se 2 (by rfl) ⟨816756, by rfl⟩ : syracuseStep 2178017 = 1633513) B1633513
theorem B2178089 : Blo 964590 2178089 := bstep (se 2 (by rfl) ⟨816783, by rfl⟩ : syracuseStep 2178089 = 1633567) B1633567
theorem B965679 : Blo 964590 965679 := bstep (se 1 (by rfl) ⟨724259, by rfl⟩ : syracuseStep 965679 = 1448519) B1448519
theorem B1031239 : Blo 964590 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B965703 : Blo 964590 965703 := bstep (se 1 (by rfl) ⟨724277, by rfl⟩ : syracuseStep 965703 = 1448555) B1448555
theorem B11156609 : Blo 964590 11156609 := bstep (se 2 (by rfl) ⟨4183728, by rfl⟩ : syracuseStep 11156609 = 8367457) B8367457
theorem B3095767 : Blo 964590 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B965855 : Blo 964590 965855 := bstep (se 1 (by rfl) ⟨724391, by rfl⟩ : syracuseStep 965855 = 1448783) B1448783
theorem B966119 : Blo 964590 966119 := bstep (se 1 (by rfl) ⟨724589, by rfl⟩ : syracuseStep 966119 = 1449179) B1449179
theorem B47037995 : Blo 964590 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B966235 : Blo 964590 966235 := bstep (se 1 (by rfl) ⟨724676, by rfl⟩ : syracuseStep 966235 = 1449353) B1449353
theorem B3489371 : Blo 964590 3489371 := bstep (se 1 (by rfl) ⟨2617028, by rfl⟩ : syracuseStep 3489371 = 5234057) B5234057
theorem B1654447 : Blo 964590 1654447 := bstep (se 1 (by rfl) ⟨1240835, by rfl⟩ : syracuseStep 1654447 = 2481671) B2481671
theorem B11321147 : Blo 964590 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B966471 : Blo 964590 966471 := bstep (se 1 (by rfl) ⟨724853, by rfl⟩ : syracuseStep 966471 = 1449707) B1449707
theorem B1032059 : Blo 964590 1032059 := bstep (se 1 (by rfl) ⟨774044, by rfl⟩ : syracuseStep 1032059 = 1548089) B1548089
theorem B966623 : Blo 964590 966623 := bstep (se 1 (by rfl) ⟨724967, by rfl⟩ : syracuseStep 966623 = 1449935) B1449935
theorem B2867419 : Blo 964590 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B966887 : Blo 964590 966887 := bstep (se 1 (by rfl) ⟨725165, by rfl⟩ : syracuseStep 966887 = 1450331) B1450331
theorem B967039 : Blo 964590 967039 := bstep (se 1 (by rfl) ⟨725279, by rfl⟩ : syracuseStep 967039 = 1450559) B1450559
theorem B967119 : Blo 964590 967119 := bstep (se 1 (by rfl) ⟨725339, by rfl⟩ : syracuseStep 967119 = 1450679) B1450679
theorem B6603227 : Blo 964590 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B967271 : Blo 964590 967271 := bstep (se 1 (by rfl) ⟨725453, by rfl⟩ : syracuseStep 967271 = 1450907) B1450907
theorem B967535 : Blo 964590 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B3916687 : Blo 964590 3916687 := bstep (se 1 (by rfl) ⟨2937515, by rfl⟩ : syracuseStep 3916687 = 5875031) B5875031
theorem B3097511 : Blo 964590 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B967591 : Blo 964590 967591 := bstep (se 1 (by rfl) ⟨725693, by rfl⟩ : syracuseStep 967591 = 1451387) B1451387
theorem B967675 : Blo 964590 967675 := bstep (se 1 (by rfl) ⟨725756, by rfl⟩ : syracuseStep 967675 = 1451513) B1451513
theorem B967743 : Blo 964590 967743 := bstep (se 1 (by rfl) ⟨725807, by rfl⟩ : syracuseStep 967743 = 1451615) B1451615
theorem B3261545 : Blo 964590 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B967887 : Blo 964590 967887 := bstep (se 1 (by rfl) ⟨725915, by rfl⟩ : syracuseStep 967887 = 1451831) B1451831
theorem B968091 : Blo 964590 968091 := bstep (se 1 (by rfl) ⟨726068, by rfl⟩ : syracuseStep 968091 = 1452137) B1452137
theorem B10438141 : Blo 964590 10438141 := bstep (se 3 (by rfl) ⟨1957151, by rfl⟩ : syracuseStep 10438141 = 3914303) B3914303
theorem B968303 : Blo 964590 968303 := bstep (se 1 (by rfl) ⟨726227, by rfl⟩ : syracuseStep 968303 = 1452455) B1452455
theorem B2442919 : Blo 964590 2442919 := bstep (se 1 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 2442919 = 3664379) B3664379
theorem B968359 : Blo 964590 968359 := bstep (se 1 (by rfl) ⟨726269, by rfl⟩ : syracuseStep 968359 = 1452539) B1452539
theorem B968443 : Blo 964590 968443 := bstep (se 1 (by rfl) ⟨726332, by rfl⟩ : syracuseStep 968443 = 1452665) B1452665
theorem B968479 : Blo 964590 968479 := bstep (se 1 (by rfl) ⟨726359, by rfl⟩ : syracuseStep 968479 = 1452719) B1452719
theorem B968511 : Blo 964590 968511 := bstep (se 1 (by rfl) ⟨726383, by rfl⟩ : syracuseStep 968511 = 1452767) B1452767
theorem B1656713 : Blo 964590 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B13420475 : Blo 964590 13420475 := bstep (se 1 (by rfl) ⟨10065356, by rfl⟩ : syracuseStep 13420475 = 20130713) B20130713
theorem B3262409 : Blo 964590 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B3262679 : Blo 964590 3262679 := bstep (se 1 (by rfl) ⟨2447009, by rfl⟩ : syracuseStep 3262679 = 4894019) B4894019
theorem B2443567 : Blo 964590 2443567 := bstep (se 1 (by rfl) ⟨1832675, by rfl⟩ : syracuseStep 2443567 = 3665351) B3665351
theorem B12536221 : Blo 964590 12536221 := bstep (se 3 (by rfl) ⟨2350541, by rfl⟩ : syracuseStep 12536221 = 4701083) B4701083
theorem B13224397 : Blo 964590 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B3263003 : Blo 964590 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B3132395 : Blo 964590 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B10472435 : Blo 964590 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B3263867 : Blo 964590 3263867 := bstep (se 1 (by rfl) ⟨2447900, by rfl⟩ : syracuseStep 3263867 = 4895801) B4895801
theorem B39669263 : Blo 964590 39669263 := bstep (se 1 (by rfl) ⟨29751947, by rfl⟩ : syracuseStep 39669263 = 59503895) B59503895
theorem B2444863 : Blo 964590 2444863 := bstep (se 1 (by rfl) ⟨1833647, by rfl⟩ : syracuseStep 2444863 = 3667295) B3667295
theorem B7425643 : Blo 964590 7425643 := bstep (se 1 (by rfl) ⟨5569232, by rfl⟩ : syracuseStep 7425643 = 11138465) B11138465
theorem B2444975 : Blo 964590 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B2445299 : Blo 964590 2445299 := bstep (se 1 (by rfl) ⟨1833974, by rfl⟩ : syracuseStep 2445299 = 3667949) B3667949
theorem B2445623 : Blo 964590 2445623 := bstep (se 1 (by rfl) ⟨1834217, by rfl⟩ : syracuseStep 2445623 = 3668435) B3668435
theorem B3265271 : Blo 964590 3265271 := bstep (se 1 (by rfl) ⟨2448953, by rfl⟩ : syracuseStep 3265271 = 4897907) B4897907
theorem B1856297 : Blo 964590 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B8246083 : Blo 964590 8246083 := bstep (se 1 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 8246083 = 12369125) B12369125
theorem B3101611 : Blo 964590 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B3527675 : Blo 964590 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B3265811 : Blo 964590 3265811 := bstep (se 1 (by rfl) ⟨2449358, by rfl⟩ : syracuseStep 3265811 = 4898717) B4898717
theorem B2446919 : Blo 964590 2446919 := bstep (se 1 (by rfl) ⟨1835189, by rfl⟩ : syracuseStep 2446919 = 3670379) B3670379
theorem B1627769 : Blo 964590 1627769 := bstep (se 2 (by rfl) ⟨610413, by rfl⟩ : syracuseStep 1627769 = 1220827) B1220827
theorem B12408491 : Blo 964590 12408491 := bstep (se 1 (by rfl) ⟨9306368, by rfl⟩ : syracuseStep 12408491 = 18612737) B18612737
theorem B3266351 : Blo 964590 3266351 := bstep (se 1 (by rfl) ⟨2449763, by rfl⟩ : syracuseStep 3266351 = 4899527) B4899527
theorem B1628255 : Blo 964590 1628255 := bstep (se 1 (by rfl) ⟨1221191, by rfl⟩ : syracuseStep 1628255 = 2442383) B2442383
theorem B2447455 : Blo 964590 2447455 := bstep (se 1 (by rfl) ⟨1835591, by rfl⟩ : syracuseStep 2447455 = 3671183) B3671183
theorem B2480225 : Blo 964590 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B1629551 : Blo 964590 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B2448751 : Blo 964590 2448751 := bstep (se 1 (by rfl) ⟨1836563, by rfl⟩ : syracuseStep 2448751 = 3673127) B3673127
theorem B5496295 : Blo 964590 5496295 := bstep (se 1 (by rfl) ⟨4122221, by rfl⟩ : syracuseStep 5496295 = 8244443) B8244443
theorem B1629787 : Blo 964590 1629787 := bstep (se 1 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 1629787 = 2444681) B2444681
theorem B3268187 : Blo 964590 3268187 := bstep (se 1 (by rfl) ⟨2451140, by rfl⟩ : syracuseStep 3268187 = 4902281) B4902281
theorem B1629929 : Blo 964590 1629929 := bstep (se 2 (by rfl) ⟨611223, by rfl⟩ : syracuseStep 1629929 = 1222447) B1222447
theorem B13950737 : Blo 964590 13950737 := bstep (se 2 (by rfl) ⟨5231526, by rfl⟩ : syracuseStep 13950737 = 10463053) B10463053
theorem B4710167 : Blo 964590 4710167 := bstep (se 1 (by rfl) ⟨3532625, by rfl⟩ : syracuseStep 4710167 = 7065251) B7065251
theorem B13950791 : Blo 964590 13950791 := bstep (se 1 (by rfl) ⟨10463093, by rfl⟩ : syracuseStep 13950791 = 20926187) B20926187
theorem B9297757 : Blo 964590 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B13230053 : Blo 964590 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B3268889 : Blo 964590 3268889 := bstep (se 2 (by rfl) ⟨1225833, by rfl⟩ : syracuseStep 3268889 = 2451667) B2451667
theorem B1630955 : Blo 964590 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B3662603 : Blo 964590 3662603 := bstep (se 1 (by rfl) ⟨2746952, by rfl⟩ : syracuseStep 3662603 = 5493905) B5493905
theorem B8250457 : Blo 964590 8250457 := bstep (se 2 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 8250457 = 6187843) B6187843
theorem B1631407 : Blo 964590 1631407 := bstep (se 1 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 1631407 = 2447111) B2447111
theorem B8250731 : Blo 964590 8250731 := bstep (se 1 (by rfl) ⟨6188048, by rfl⟩ : syracuseStep 8250731 = 12376097) B12376097
theorem B25748941 : Blo 964590 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B1631927 : Blo 964590 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B1861339 : Blo 964590 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B5498711 : Blo 964590 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B3663863 : Blo 964590 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2451647 : Blo 964590 2451647 := bstep (se 1 (by rfl) ⟨1838735, by rfl⟩ : syracuseStep 2451647 = 3677471) B3677471
theorem B1468795 : Blo 964590 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B2320903 : Blo 964590 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B4123163 : Blo 964590 4123163 := bstep (se 1 (by rfl) ⟨3092372, by rfl⟩ : syracuseStep 4123163 = 6184745) B6184745
theorem B1305119 : Blo 964590 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B4123385 : Blo 964590 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B2747191 : Blo 964590 2747191 := bstep (se 1 (by rfl) ⟨2060393, by rfl⟩ : syracuseStep 2747191 = 4120787) B4120787
theorem B7334711 : Blo 964590 7334711 := bstep (se 1 (by rfl) ⟨5501033, by rfl⟩ : syracuseStep 7334711 = 11002067) B11002067
theorem B1633115 : Blo 964590 1633115 := bstep (se 1 (by rfl) ⟨1224836, by rfl⟩ : syracuseStep 1633115 = 2449673) B2449673
theorem B3664835 : Blo 964590 3664835 := bstep (se 1 (by rfl) ⟨2748626, by rfl⟩ : syracuseStep 3664835 = 5497253) B5497253
theorem B1633351 : Blo 964590 1633351 := bstep (se 1 (by rfl) ⟨1225013, by rfl⟩ : syracuseStep 1633351 = 2450027) B2450027
theorem B2747591 : Blo 964590 2747591 := bstep (se 1 (by rfl) ⟨2060693, by rfl⟩ : syracuseStep 2747591 = 4121387) B4121387
theorem B1633783 : Blo 964590 1633783 := bstep (se 1 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 1633783 = 2450675) B2450675
theorem B16772599 : Blo 964590 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B978523 : Blo 964590 978523 := bstep (se 1 (by rfl) ⟨733892, by rfl⟩ : syracuseStep 978523 = 1467785) B1467785
theorem B3665533 : Blo 964590 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B1634087 : Blo 964590 1634087 := bstep (se 1 (by rfl) ⟨1225565, by rfl⟩ : syracuseStep 1634087 = 2451131) B2451131
theorem B5304307 : Blo 964590 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B14151667 : Blo 964590 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B2060599 : Blo 964590 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B4190519 : Blo 964590 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B2748809 : Blo 964590 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B6287759 : Blo 964590 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B2978387 : Blo 964590 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B13202065 : Blo 964590 13202065 := bstep (se 2 (by rfl) ⟨4950774, by rfl⟩ : syracuseStep 13202065 = 9901549) B9901549
theorem B1471483 : Blo 964590 1471483 := bstep (se 1 (by rfl) ⟨1103612, by rfl⟩ : syracuseStep 1471483 = 2207225) B2207225
theorem B2061487 : Blo 964590 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B16742123 : Blo 964590 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B1832699 : Blo 964590 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B4126459 : Blo 964590 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B3536687 : Blo 964590 3536687 := bstep (se 1 (by rfl) ⟨2652515, by rfl⟩ : syracuseStep 3536687 = 5305031) B5305031
theorem B3668267 : Blo 964590 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B2751337 : Blo 964590 2751337 := bstep (se 2 (by rfl) ⟨1031751, by rfl⟩ : syracuseStep 2751337 = 2063503) B2063503
theorem B2751839 : Blo 964590 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B8813929 : Blo 964590 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B1835311 : Blo 964590 1835311 := bstep (se 1 (by rfl) ⟨1376483, by rfl⟩ : syracuseStep 1835311 = 2752967) B2752967
theorem B1835615 : Blo 964590 1835615 := bstep (se 1 (by rfl) ⟨1376711, by rfl⟩ : syracuseStep 1835615 = 2753423) B2753423
theorem B2065007 : Blo 964590 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B13927261 : Blo 964590 13927261 := bstep (se 3 (by rfl) ⟨2611361, by rfl⟩ : syracuseStep 13927261 = 5222723) B5222723
theorem B8946983 : Blo 964590 8946983 := bstep (se 1 (by rfl) ⟨6710237, by rfl⟩ : syracuseStep 8946983 = 13420475) B13420475
theorem B96831293 : Blo 964590 96831293 := bstep (se 3 (by rfl) ⟨18155867, by rfl⟩ : syracuseStep 96831293 = 36311735) B36311735
theorem B20875157 : Blo 964590 20875157 := bstep (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) B978523
theorem B6981623 : Blo 964590 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B1837217 : Blo 964590 1837217 := bstep (se 2 (by rfl) ⟨688956, by rfl⟩ : syracuseStep 1837217 = 1377913) B1377913
theorem B26446175 : Blo 964590 26446175 := bstep (se 1 (by rfl) ⟨19834631, by rfl⟩ : syracuseStep 26446175 = 39669263) B39669263
theorem B1838143 : Blo 964590 1838143 := bstep (se 1 (by rfl) ⟨1378607, by rfl⟩ : syracuseStep 1838143 = 2757215) B2757215
theorem B16714961 : Blo 964590 16714961 := bstep (se 2 (by rfl) ⟨6268110, by rfl⟩ : syracuseStep 16714961 = 12536221) B12536221
theorem B17632529 : Blo 964590 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B1838447 : Blo 964590 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B4132235 : Blo 964590 4132235 := bstep (se 1 (by rfl) ⟨3099176, by rfl⟩ : syracuseStep 4132235 = 6198353) B6198353
theorem B2756065 : Blo 964590 2756065 := bstep (se 2 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 2756065 = 2067049) B2067049
theorem B2756339 : Blo 964590 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B1085179 : Blo 964590 1085179 := bstep (se 1 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 1085179 = 1627769) B1627769
theorem B1085503 : Blo 964590 1085503 := bstep (se 1 (by rfl) ⟨814127, by rfl⟩ : syracuseStep 1085503 = 1628255) B1628255
theorem B5509417 : Blo 964590 5509417 := bstep (se 2 (by rfl) ⟨2066031, by rfl⟩ : syracuseStep 5509417 = 4132063) B4132063
theorem B8261939 : Blo 964590 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B9900857 : Blo 964590 9900857 := bstep (se 2 (by rfl) ⟨3712821, by rfl⟩ : syracuseStep 9900857 = 7425643) B7425643
theorem B4887377 : Blo 964590 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B1086367 : Blo 964590 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1447007 : Blo 964590 1447007 := bstep (se 1 (by rfl) ⟨1085255, by rfl⟩ : syracuseStep 1447007 = 2170511) B2170511
theorem B1447067 : Blo 964590 1447067 := bstep (se 1 (by rfl) ⟨1085300, by rfl⟩ : syracuseStep 1447067 = 2170601) B2170601
theorem B1086619 : Blo 964590 1086619 := bstep (se 1 (by rfl) ⟨814964, by rfl⟩ : syracuseStep 1086619 = 1629929) B1629929
theorem B8820035 : Blo 964590 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B5510875 : Blo 964590 5510875 := bstep (se 1 (by rfl) ⟨4133156, by rfl⟩ : syracuseStep 5510875 = 8266313) B8266313
theorem B1447751 : Blo 964590 1447751 := bstep (se 1 (by rfl) ⟨1085813, by rfl⟩ : syracuseStep 1447751 = 2171627) B2171627
theorem B1087303 : Blo 964590 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B5511149 : Blo 964590 5511149 := bstep (se 3 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 5511149 = 2066681) B2066681
theorem B17602753 : Blo 964590 17602753 := bstep (se 2 (by rfl) ⟨6601032, by rfl⟩ : syracuseStep 17602753 = 13202065) B13202065
theorem B1448351 : Blo 964590 1448351 := bstep (se 1 (by rfl) ⟨1086263, by rfl⟩ : syracuseStep 1448351 = 2172527) B2172527
theorem B1087951 : Blo 964590 1087951 := bstep (se 1 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 1087951 = 1631927) B1631927
theorem B1448423 : Blo 964590 1448423 := bstep (se 1 (by rfl) ⟨1086317, by rfl⟩ : syracuseStep 1448423 = 2172635) B2172635
theorem B4135481 : Blo 964590 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B3480317 : Blo 964590 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B3676985 : Blo 964590 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B7347347 : Blo 964590 7347347 := bstep (se 1 (by rfl) ⟨5510510, by rfl⟩ : syracuseStep 7347347 = 11021021) B11021021
theorem B4889807 : Blo 964590 4889807 := bstep (se 1 (by rfl) ⟨3667355, by rfl⟩ : syracuseStep 4889807 = 7334711) B7334711
theorem B1449167 : Blo 964590 1449167 := bstep (se 1 (by rfl) ⟨1086875, by rfl⟩ : syracuseStep 1449167 = 2173751) B2173751
theorem B1088743 : Blo 964590 1088743 := bstep (se 1 (by rfl) ⟨816557, by rfl⟩ : syracuseStep 1088743 = 1633115) B1633115
theorem B1449287 : Blo 964590 1449287 := bstep (se 1 (by rfl) ⟨1086965, by rfl⟩ : syracuseStep 1449287 = 2173931) B2173931
theorem B1449449 : Blo 964590 1449449 := bstep (se 2 (by rfl) ⟨543543, by rfl⟩ : syracuseStep 1449449 = 1087087) B1087087
theorem B1449593 : Blo 964590 1449593 := bstep (se 2 (by rfl) ⟨543597, by rfl⟩ : syracuseStep 1449593 = 1087195) B1087195
theorem B2170655 : Blo 964590 2170655 := bstep (se 1 (by rfl) ⟨1627991, by rfl⟩ : syracuseStep 2170655 = 3255983) B3255983
theorem B1449839 : Blo 964590 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B1089391 : Blo 964590 1089391 := bstep (se 1 (by rfl) ⟨817043, by rfl⟩ : syracuseStep 1089391 = 1634087) B1634087
theorem B2170871 : Blo 964590 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B2171087 : Blo 964590 2171087 := bstep (se 1 (by rfl) ⟨1628315, by rfl⟩ : syracuseStep 2171087 = 3256631) B3256631
theorem B2793679 : Blo 964590 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B1548601 : Blo 964590 1548601 := bstep (se 2 (by rfl) ⟨580725, by rfl⟩ : syracuseStep 1548601 = 1161451) B1161451
theorem B2171231 : Blo 964590 2171231 := bstep (se 1 (by rfl) ⟨1628423, by rfl⟩ : syracuseStep 2171231 = 3256847) B3256847
theorem B5579207 : Blo 964590 5579207 := bstep (se 1 (by rfl) ⟨4184405, by rfl⟩ : syracuseStep 5579207 = 8368811) B8368811
theorem B1450523 : Blo 964590 1450523 := bstep (se 1 (by rfl) ⟨1087892, by rfl⟩ : syracuseStep 1450523 = 2175785) B2175785
theorem B5513791 : Blo 964590 5513791 := bstep (se 1 (by rfl) ⟨4135343, by rfl⟩ : syracuseStep 5513791 = 8270687) B8270687
theorem B1450703 : Blo 964590 1450703 := bstep (se 1 (by rfl) ⟨1088027, by rfl⟩ : syracuseStep 1450703 = 2176055) B2176055
theorem B1450715 : Blo 964590 1450715 := bstep (se 1 (by rfl) ⟨1088036, by rfl⟩ : syracuseStep 1450715 = 2176073) B2176073
theorem B2171951 : Blo 964590 2171951 := bstep (se 1 (by rfl) ⟨1628963, by rfl⟩ : syracuseStep 2171951 = 3257927) B3257927
theorem B1451129 : Blo 964590 1451129 := bstep (se 2 (by rfl) ⟨544173, by rfl⟩ : syracuseStep 1451129 = 1088347) B1088347
theorem B1221799 : Blo 964590 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B5514749 : Blo 964590 5514749 := bstep (se 3 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 5514749 = 2068031) B2068031
theorem B2172599 : Blo 964590 2172599 := bstep (se 1 (by rfl) ⟨1629449, by rfl⟩ : syracuseStep 2172599 = 3258899) B3258899
theorem B1451999 : Blo 964590 1451999 := bstep (se 1 (by rfl) ⟨1088999, by rfl⟩ : syracuseStep 1451999 = 2177999) B2177999
theorem B1452011 : Blo 964590 1452011 := bstep (se 1 (by rfl) ⟨1089008, by rfl⟩ : syracuseStep 1452011 = 2178017) B2178017
theorem B1452059 : Blo 964590 1452059 := bstep (se 1 (by rfl) ⟨1089044, by rfl⟩ : syracuseStep 1452059 = 2178089) B2178089
theorem B2173049 : Blo 964590 2173049 := bstep (se 2 (by rfl) ⟨814893, by rfl⟩ : syracuseStep 2173049 = 1629787) B1629787
theorem B30189725 : Blo 964590 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B2205929 : Blo 964590 2205929 := bstep (se 2 (by rfl) ⟨827223, by rfl⟩ : syracuseStep 2205929 = 1654447) B1654447
theorem B1452425 : Blo 964590 1452425 := bstep (se 2 (by rfl) ⟨544659, by rfl⟩ : syracuseStep 1452425 = 1089319) B1089319
theorem B12397009 : Blo 964590 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B4893371 : Blo 964590 4893371 := bstep (se 1 (by rfl) ⟨3670028, by rfl⟩ : syracuseStep 4893371 = 7340057) B7340057
theorem B4402151 : Blo 964590 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B2174363 : Blo 964590 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B33500861 : Blo 964590 33500861 := bstep (se 3 (by rfl) ⟨6281411, by rfl⟩ : syracuseStep 33500861 = 12562823) B12562823
theorem B5222249 : Blo 964590 5222249 := bstep (se 2 (by rfl) ⟨1958343, by rfl⟩ : syracuseStep 5222249 = 3916687) B3916687
theorem B5812073 : Blo 964590 5812073 := bstep (se 2 (by rfl) ⟨2179527, by rfl⟩ : syracuseStep 5812073 = 4359055) B4359055
theorem B1159039 : Blo 964590 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B2174939 : Blo 964590 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B2175119 : Blo 964590 2175119 := bstep (se 1 (by rfl) ⟨1631339, by rfl⟩ : syracuseStep 2175119 = 3262679) B3262679
theorem B2175209 : Blo 964590 2175209 := bstep (se 2 (by rfl) ⟨815703, by rfl⟩ : syracuseStep 2175209 = 1631407) B1631407
theorem B2175335 : Blo 964590 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B10990403 : Blo 964590 10990403 := bstep (se 1 (by rfl) ⟨8242802, by rfl⟩ : syracuseStep 10990403 = 16485605) B16485605
theorem B3257225 : Blo 964590 3257225 := bstep (se 2 (by rfl) ⟨1221459, by rfl⟩ : syracuseStep 3257225 = 2442919) B2442919
theorem B2175911 : Blo 964590 2175911 := bstep (se 1 (by rfl) ⟨1631933, by rfl⟩ : syracuseStep 2175911 = 3263867) B3263867
theorem B3094013 : Blo 964590 3094013 := bstep (se 3 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 3094013 = 1160255) B1160255
theorem B3258089 : Blo 964590 3258089 := bstep (se 2 (by rfl) ⟨1221783, by rfl⟩ : syracuseStep 3258089 = 2443567) B2443567
theorem B2176847 : Blo 964590 2176847 := bstep (se 1 (by rfl) ⟨1632635, by rfl⟩ : syracuseStep 2176847 = 3265271) B3265271
theorem B6961153 : Blo 964590 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B3094537 : Blo 964590 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B964679 : Blo 964590 964679 := bstep (se 1 (by rfl) ⟨723509, by rfl⟩ : syracuseStep 964679 = 1447019) B1447019
theorem B2177207 : Blo 964590 2177207 := bstep (se 1 (by rfl) ⟨1632905, by rfl⟩ : syracuseStep 2177207 = 3265811) B3265811
theorem B964839 : Blo 964590 964839 := bstep (se 1 (by rfl) ⟨723629, by rfl⟩ : syracuseStep 964839 = 1447259) B1447259
theorem B965023 : Blo 964590 965023 := bstep (se 1 (by rfl) ⟨723767, by rfl⟩ : syracuseStep 965023 = 1447535) B1447535
theorem B8272327 : Blo 964590 8272327 := bstep (se 1 (by rfl) ⟨6204245, by rfl⟩ : syracuseStep 8272327 = 12408491) B12408491
theorem B965071 : Blo 964590 965071 := bstep (se 1 (by rfl) ⟨723803, by rfl⟩ : syracuseStep 965071 = 1447607) B1447607
theorem B965095 : Blo 964590 965095 := bstep (se 1 (by rfl) ⟨723821, by rfl⟩ : syracuseStep 965095 = 1447643) B1447643
theorem B2177567 : Blo 964590 2177567 := bstep (se 1 (by rfl) ⟨1633175, by rfl⟩ : syracuseStep 2177567 = 3266351) B3266351
theorem B965211 : Blo 964590 965211 := bstep (se 1 (by rfl) ⟨723908, by rfl⟩ : syracuseStep 965211 = 1447817) B1447817
theorem B965279 : Blo 964590 965279 := bstep (se 1 (by rfl) ⟨723959, by rfl⟩ : syracuseStep 965279 = 1447919) B1447919
theorem B5225147 : Blo 964590 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B2177801 : Blo 964590 2177801 := bstep (se 2 (by rfl) ⟨816675, by rfl⟩ : syracuseStep 2177801 = 1633351) B1633351
theorem B965447 : Blo 964590 965447 := bstep (se 1 (by rfl) ⟨724085, by rfl⟩ : syracuseStep 965447 = 1448171) B1448171
theorem B965487 : Blo 964590 965487 := bstep (se 1 (by rfl) ⟨724115, by rfl⟩ : syracuseStep 965487 = 1448231) B1448231
theorem B965543 : Blo 964590 965543 := bstep (se 1 (by rfl) ⟨724157, by rfl⟩ : syracuseStep 965543 = 1448315) B1448315
theorem B965723 : Blo 964590 965723 := bstep (se 1 (by rfl) ⟨724292, by rfl⟩ : syracuseStep 965723 = 1448585) B1448585
theorem B965839 : Blo 964590 965839 := bstep (se 1 (by rfl) ⟨724379, by rfl⟩ : syracuseStep 965839 = 1448759) B1448759
theorem B965863 : Blo 964590 965863 := bstep (se 1 (by rfl) ⟨724397, by rfl⟩ : syracuseStep 965863 = 1448795) B1448795
theorem B965959 : Blo 964590 965959 := bstep (se 1 (by rfl) ⟨724469, by rfl⟩ : syracuseStep 965959 = 1448939) B1448939
theorem B2178377 : Blo 964590 2178377 := bstep (se 2 (by rfl) ⟨816891, by rfl⟩ : syracuseStep 2178377 = 1633783) B1633783
theorem B22363465 : Blo 964590 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B3259817 : Blo 964590 3259817 := bstep (se 2 (by rfl) ⟨1222431, by rfl⟩ : syracuseStep 3259817 = 2444863) B2444863
theorem B966095 : Blo 964590 966095 := bstep (se 1 (by rfl) ⟨724571, by rfl⟩ : syracuseStep 966095 = 1449143) B1449143
theorem B4898393 : Blo 964590 4898393 := bstep (se 2 (by rfl) ⟨1836897, by rfl⟩ : syracuseStep 4898393 = 3673795) B3673795
theorem B966255 : Blo 964590 966255 := bstep (se 1 (by rfl) ⟨724691, by rfl⟩ : syracuseStep 966255 = 1449383) B1449383
theorem B966311 : Blo 964590 966311 := bstep (se 1 (by rfl) ⟨724733, by rfl⟩ : syracuseStep 966311 = 1449467) B1449467
theorem B966375 : Blo 964590 966375 := bstep (se 1 (by rfl) ⟨724781, by rfl⟩ : syracuseStep 966375 = 1449563) B1449563
theorem B2178791 : Blo 964590 2178791 := bstep (se 1 (by rfl) ⟨1634093, by rfl⟩ : syracuseStep 2178791 = 3268187) B3268187
theorem B966431 : Blo 964590 966431 := bstep (se 1 (by rfl) ⟨724823, by rfl⟩ : syracuseStep 966431 = 1449647) B1449647
theorem B966511 : Blo 964590 966511 := bstep (se 1 (by rfl) ⟨724883, by rfl⟩ : syracuseStep 966511 = 1449767) B1449767
theorem B966567 : Blo 964590 966567 := bstep (se 1 (by rfl) ⟨724925, by rfl⟩ : syracuseStep 966567 = 1449851) B1449851
theorem B16498727 : Blo 964590 16498727 := bstep (se 1 (by rfl) ⟨12374045, by rfl⟩ : syracuseStep 16498727 = 24748091) B24748091
theorem B2179259 : Blo 964590 2179259 := bstep (se 1 (by rfl) ⟨1634444, by rfl⟩ : syracuseStep 2179259 = 3268889) B3268889
theorem B966847 : Blo 964590 966847 := bstep (se 1 (by rfl) ⟨725135, by rfl⟩ : syracuseStep 966847 = 1450271) B1450271
theorem B966863 : Blo 964590 966863 := bstep (se 1 (by rfl) ⟨725147, by rfl⟩ : syracuseStep 966863 = 1450295) B1450295
theorem B966911 : Blo 964590 966911 := bstep (se 1 (by rfl) ⟨725183, by rfl⟩ : syracuseStep 966911 = 1450367) B1450367
theorem B966959 : Blo 964590 966959 := bstep (se 1 (by rfl) ⟨725219, by rfl⟩ : syracuseStep 966959 = 1450439) B1450439
theorem B2441735 : Blo 964590 2441735 := bstep (se 1 (by rfl) ⟨1831301, by rfl⟩ : syracuseStep 2441735 = 3662603) B3662603
theorem B967195 : Blo 964590 967195 := bstep (se 1 (by rfl) ⟨725396, by rfl⟩ : syracuseStep 967195 = 1450793) B1450793
theorem B967199 : Blo 964590 967199 := bstep (se 1 (by rfl) ⟨725399, by rfl⟩ : syracuseStep 967199 = 1450799) B1450799
theorem B967279 : Blo 964590 967279 := bstep (se 1 (by rfl) ⟨725459, by rfl⟩ : syracuseStep 967279 = 1450919) B1450919
theorem B967335 : Blo 964590 967335 := bstep (se 1 (by rfl) ⟨725501, by rfl⟩ : syracuseStep 967335 = 1451003) B1451003
theorem B967375 : Blo 964590 967375 := bstep (se 1 (by rfl) ⟨725531, by rfl⟩ : syracuseStep 967375 = 1451063) B1451063
theorem B967455 : Blo 964590 967455 := bstep (se 1 (by rfl) ⟨725591, by rfl⟩ : syracuseStep 967455 = 1451183) B1451183
theorem B5227375 : Blo 964590 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B967727 : Blo 964590 967727 := bstep (se 1 (by rfl) ⟨725795, by rfl⟩ : syracuseStep 967727 = 1451591) B1451591
theorem B10994777 : Blo 964590 10994777 := bstep (se 2 (by rfl) ⟨4123041, by rfl⟩ : syracuseStep 10994777 = 8246083) B8246083
theorem B967791 : Blo 964590 967791 := bstep (se 1 (by rfl) ⟨725843, by rfl⟩ : syracuseStep 967791 = 1451687) B1451687
theorem B967847 : Blo 964590 967847 := bstep (se 1 (by rfl) ⟨725885, by rfl⟩ : syracuseStep 967847 = 1451771) B1451771
theorem B967871 : Blo 964590 967871 := bstep (se 1 (by rfl) ⟨725903, by rfl⟩ : syracuseStep 967871 = 1451807) B1451807
theorem B967903 : Blo 964590 967903 := bstep (se 1 (by rfl) ⟨725927, by rfl⟩ : syracuseStep 967903 = 1451855) B1451855
theorem B967983 : Blo 964590 967983 := bstep (se 1 (by rfl) ⟨725987, by rfl⟩ : syracuseStep 967983 = 1451975) B1451975
theorem B2442575 : Blo 964590 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B4900175 : Blo 964590 4900175 := bstep (se 1 (by rfl) ⟨3675131, by rfl⟩ : syracuseStep 4900175 = 7350263) B7350263
theorem B968219 : Blo 964590 968219 := bstep (se 1 (by rfl) ⟨726164, by rfl⟩ : syracuseStep 968219 = 1452329) B1452329
theorem B968223 : Blo 964590 968223 := bstep (se 1 (by rfl) ⟨726167, by rfl⟩ : syracuseStep 968223 = 1452335) B1452335
theorem B968383 : Blo 964590 968383 := bstep (se 1 (by rfl) ⟨726287, by rfl⟩ : syracuseStep 968383 = 1452575) B1452575
theorem B2443223 : Blo 964590 2443223 := bstep (se 1 (by rfl) ⟨1832417, by rfl⟩ : syracuseStep 2443223 = 3664835) B3664835
theorem B13944791 : Blo 964590 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B4900823 : Blo 964590 4900823 := bstep (se 1 (by rfl) ⟨3675617, by rfl⟩ : syracuseStep 4900823 = 7351235) B7351235
theorem B10996235 : Blo 964590 10996235 := bstep (se 1 (by rfl) ⟨8247176, by rfl⟩ : syracuseStep 10996235 = 16494353) B16494353
theorem B3263273 : Blo 964590 3263273 := bstep (se 2 (by rfl) ⟨1223727, by rfl⟩ : syracuseStep 3263273 = 2447455) B2447455
theorem B1985591 : Blo 964590 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B3263543 : Blo 964590 3263543 := bstep (se 1 (by rfl) ⟨2447657, by rfl⟩ : syracuseStep 3263543 = 4895315) B4895315
theorem B11161415 : Blo 964590 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B4640807 : Blo 964590 4640807 := bstep (se 1 (by rfl) ⟨3480605, by rfl⟩ : syracuseStep 4640807 = 6961211) B6961211
theorem B2445511 : Blo 964590 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B3264731 : Blo 964590 3264731 := bstep (se 1 (by rfl) ⟨2448548, by rfl⟩ : syracuseStep 3264731 = 4897097) B4897097
theorem B4641191 : Blo 964590 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B11751905 : Blo 964590 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B3265001 : Blo 964590 3265001 := bstep (se 2 (by rfl) ⟨1224375, by rfl⟩ : syracuseStep 3265001 = 2448751) B2448751
theorem B7328393 : Blo 964590 7328393 := bstep (se 2 (by rfl) ⟨2748147, by rfl⟩ : syracuseStep 7328393 = 5496295) B5496295
theorem B2446969 : Blo 964590 2446969 := bstep (se 2 (by rfl) ⟨917613, by rfl⟩ : syracuseStep 2446969 = 1835227) B1835227
theorem B6182567 : Blo 964590 6182567 := bstep (se 1 (by rfl) ⟨4636925, by rfl⟩ : syracuseStep 6182567 = 9273851) B9273851
theorem B15685559 : Blo 964590 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B15292901 : Blo 964590 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B4413971 : Blo 964590 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B11000609 : Blo 964590 11000609 := bstep (se 2 (by rfl) ⟨4125228, by rfl⟩ : syracuseStep 11000609 = 8250457) B8250457
theorem B34331921 : Blo 964590 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B2088263 : Blo 964590 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B13917521 : Blo 964590 13917521 := bstep (se 2 (by rfl) ⟨5219070, by rfl⟩ : syracuseStep 13917521 = 10438141) B10438141
theorem B2481785 : Blo 964590 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B1629983 : Blo 964590 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B1630199 : Blo 964590 1630199 := bstep (se 1 (by rfl) ⟨1222649, by rfl⟩ : syracuseStep 1630199 = 2445299) B2445299
theorem B20930683 : Blo 964590 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B1630415 : Blo 964590 1630415 := bstep (se 1 (by rfl) ⟨1222811, by rfl⟩ : syracuseStep 1630415 = 2445623) B2445623
theorem B9527759 : Blo 964590 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B1958393 : Blo 964590 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B1237531 : Blo 964590 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B2351783 : Blo 964590 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1631279 : Blo 964590 1631279 := bstep (se 1 (by rfl) ⟨1223459, by rfl⟩ : syracuseStep 1631279 = 2446919) B2446919
theorem B3662921 : Blo 964590 3662921 := bstep (se 2 (by rfl) ⟨1373595, by rfl⟩ : syracuseStep 3662921 = 2747191) B2747191
theorem B1631353 : Blo 964590 1631353 := bstep (se 2 (by rfl) ⟨611757, by rfl⟩ : syracuseStep 1631353 = 1223515) B1223515
theorem B2319673 : Blo 964590 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B6973523 : Blo 964590 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B4417901 : Blo 964590 4417901 := bstep (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) B1656713
theorem B1632649 : Blo 964590 1632649 := bstep (se 2 (by rfl) ⟨612243, by rfl⟩ : syracuseStep 1632649 = 1224487) B1224487
theorem B9300491 : Blo 964590 9300491 := bstep (se 1 (by rfl) ⟨6975368, by rfl⟩ : syracuseStep 9300491 = 13950737) B13950737
theorem B3140111 : Blo 964590 3140111 := bstep (se 1 (by rfl) ⟨2355083, by rfl⟩ : syracuseStep 3140111 = 4710167) B4710167
theorem B9300527 : Blo 964590 9300527 := bstep (se 1 (by rfl) ⟨6975395, by rfl⟩ : syracuseStep 9300527 = 13950791) B13950791
theorem B7072409 : Blo 964590 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B18868889 : Blo 964590 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B16542467 : Blo 964590 16542467 := bstep (se 1 (by rfl) ⟨12406850, by rfl⟩ : syracuseStep 16542467 = 24813701) B24813701
theorem B6613933 : Blo 964590 6613933 := bstep (se 3 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 6613933 = 2480225) B2480225
theorem B2747465 : Blo 964590 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B5500487 : Blo 964590 5500487 := bstep (se 1 (by rfl) ⟨4125365, by rfl⟩ : syracuseStep 5500487 = 8250731) B8250731
theorem B15658829 : Blo 964590 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B3665807 : Blo 964590 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B1961977 : Blo 964590 1961977 := bstep (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) B1471483
theorem B1634377 : Blo 964590 1634377 := bstep (se 2 (by rfl) ⟨612891, by rfl⟩ : syracuseStep 1634377 = 1225783) B1225783
theorem B1634431 : Blo 964590 1634431 := bstep (se 1 (by rfl) ⟨1225823, by rfl⟩ : syracuseStep 1634431 = 2451647) B2451647
theorem B2748649 : Blo 964590 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B2748775 : Blo 964590 2748775 := bstep (se 1 (by rfl) ⟨2061581, by rfl⟩ : syracuseStep 2748775 = 4123163) B4123163
theorem B2748923 : Blo 964590 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B2061035 : Blo 964590 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B1831727 : Blo 964590 1831727 := bstep (se 1 (by rfl) ⟨1373795, by rfl⟩ : syracuseStep 1831727 = 2747591) B2747591
theorem B5501945 : Blo 964590 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B1832539 : Blo 964590 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B4191839 : Blo 964590 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B2324663 : Blo 964590 2324663 := bstep (se 1 (by rfl) ⟨1743497, by rfl⟩ : syracuseStep 2324663 = 3486995) B3486995
theorem B3668449 : Blo 964590 3668449 := bstep (se 2 (by rfl) ⟨1375668, by rfl⟩ : syracuseStep 3668449 = 2751337) B2751337
theorem B2357791 : Blo 964590 2357791 := bstep (se 1 (by rfl) ⟨1768343, by rfl⟩ : syracuseStep 2357791 = 3536687) B3536687
theorem B2062991 : Blo 964590 2062991 := bstep (se 1 (by rfl) ⟨1547243, by rfl⟩ : syracuseStep 2062991 = 3094487) B3094487
theorem B1374985 : Blo 964590 1374985 := bstep (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) B1031239
theorem B4127689 : Blo 964590 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B36732199 : Blo 964590 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B7437739 : Blo 964590 7437739 := bstep (se 1 (by rfl) ⟨5578304, by rfl⟩ : syracuseStep 7437739 = 11156609) B11156609
theorem B1834559 : Blo 964590 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B2752157 : Blo 964590 2752157 := bstep (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) B1032059
theorem B31358663 : Blo 964590 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B2326247 : Blo 964590 2326247 := bstep (se 1 (by rfl) ⟨1744685, by rfl⟩ : syracuseStep 2326247 = 3489371) B3489371
theorem B1376671 : Blo 964590 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B4654415 : Blo 964590 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B17630783 : Blo 964590 17630783 := bstep (se 1 (by rfl) ⟨13223087, by rfl⟩ : syracuseStep 17630783 = 26446175) B26446175
theorem B8259205 : Blo 964590 8259205 := bstep (se 4 (by rfl) ⟨774300, by rfl⟩ : syracuseStep 8259205 = 1548601) B1548601
theorem B11143307 : Blo 964590 11143307 := bstep (se 1 (by rfl) ⟨8357480, by rfl⟩ : syracuseStep 11143307 = 16714961) B16714961
theorem B2754823 : Blo 964590 2754823 := bstep (se 1 (by rfl) ⟨2066117, by rfl⟩ : syracuseStep 2754823 = 4132235) B4132235
theorem B1837559 : Blo 964590 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B5507959 : Blo 964590 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B4885595 : Blo 964590 4885595 := bstep (se 1 (by rfl) ⟨3664196, by rfl⟩ : syracuseStep 4885595 = 7328393) B7328393
theorem B23858621 : Blo 964590 23858621 := bstep (se 3 (by rfl) ⟨4473491, by rfl⟩ : syracuseStep 23858621 = 8946983) B8946983
theorem B8818577 : Blo 964590 8818577 := bstep (se 2 (by rfl) ⟨3306966, by rfl⟩ : syracuseStep 8818577 = 6613933) B6613933
theorem B10457039 : Blo 964590 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B3674099 : Blo 964590 3674099 := bstep (se 1 (by rfl) ⟨2755574, by rfl⟩ : syracuseStep 3674099 = 5511149) B5511149
theorem B10195267 : Blo 964590 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B2756987 : Blo 964590 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B3674753 : Blo 964590 3674753 := bstep (se 2 (by rfl) ⟨1378032, by rfl⟩ : syracuseStep 3674753 = 2756065) B2756065
theorem B258216781 : Blo 964590 258216781 := bstep (se 3 (by rfl) ⟨48415646, by rfl⟩ : syracuseStep 258216781 = 96831293) B96831293
theorem B9278347 : Blo 964590 9278347 := bstep (se 1 (by rfl) ⟨6958760, by rfl⟩ : syracuseStep 9278347 = 13917521) B13917521
theorem B1446905 : Blo 964590 1446905 := bstep (se 2 (by rfl) ⟨542589, by rfl⟩ : syracuseStep 1446905 = 1085179) B1085179
theorem B1447103 : Blo 964590 1447103 := bstep (se 1 (by rfl) ⟨1085327, by rfl⟩ : syracuseStep 1447103 = 2170655) B2170655
theorem B1086655 : Blo 964590 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B1447247 : Blo 964590 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B1086799 : Blo 964590 1086799 := bstep (se 1 (by rfl) ⟨815099, by rfl⟩ : syracuseStep 1086799 = 1630199) B1630199
theorem B1447337 : Blo 964590 1447337 := bstep (se 2 (by rfl) ⟨542751, by rfl⟩ : syracuseStep 1447337 = 1085503) B1085503
theorem B1447391 : Blo 964590 1447391 := bstep (se 1 (by rfl) ⟨1085543, by rfl⟩ : syracuseStep 1447391 = 2171087) B2171087
theorem B1086943 : Blo 964590 1086943 := bstep (se 1 (by rfl) ⟨815207, by rfl⟩ : syracuseStep 1086943 = 1630415) B1630415
theorem B1447487 : Blo 964590 1447487 := bstep (se 1 (by rfl) ⟨1085615, by rfl⟩ : syracuseStep 1447487 = 2171231) B2171231
theorem B7345889 : Blo 964590 7345889 := bstep (se 2 (by rfl) ⟨2754708, by rfl⟩ : syracuseStep 7345889 = 5509417) B5509417
theorem B1447967 : Blo 964590 1447967 := bstep (se 1 (by rfl) ⟨1085975, by rfl⟩ : syracuseStep 1447967 = 2171951) B2171951
theorem B1087519 : Blo 964590 1087519 := bstep (se 1 (by rfl) ⟨815639, by rfl⟩ : syracuseStep 1087519 = 1631279) B1631279
theorem B3676499 : Blo 964590 3676499 := bstep (se 1 (by rfl) ⟨2757374, by rfl⟩ : syracuseStep 3676499 = 5514749) B5514749
theorem B1448399 : Blo 964590 1448399 := bstep (se 1 (by rfl) ⟨1086299, by rfl⟩ : syracuseStep 1448399 = 2172599) B2172599
theorem B1448489 : Blo 964590 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B11770589 : Blo 964590 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B1448699 : Blo 964590 1448699 := bstep (se 1 (by rfl) ⟨1086524, by rfl⟩ : syracuseStep 1448699 = 2173049) B2173049
theorem B20126483 : Blo 964590 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B1448825 : Blo 964590 1448825 := bstep (se 2 (by rfl) ⟨543309, by rfl⟩ : syracuseStep 1448825 = 1086619) B1086619
theorem B6200327 : Blo 964590 6200327 := bstep (se 1 (by rfl) ⟨4650245, by rfl⟩ : syracuseStep 6200327 = 9300491) B9300491
theorem B6200351 : Blo 964590 6200351 := bstep (se 1 (by rfl) ⟨4650263, by rfl⟩ : syracuseStep 6200351 = 9300527) B9300527
theorem B1449575 : Blo 964590 1449575 := bstep (se 1 (by rfl) ⟨1087181, by rfl⟩ : syracuseStep 1449575 = 2174363) B2174363
theorem B7347833 : Blo 964590 7347833 := bstep (se 2 (by rfl) ⟨2755437, by rfl⟩ : syracuseStep 7347833 = 5510875) B5510875
theorem B1449737 : Blo 964590 1449737 := bstep (se 2 (by rfl) ⟨543651, by rfl⟩ : syracuseStep 1449737 = 1087303) B1087303
theorem B3481499 : Blo 964590 3481499 := bstep (se 1 (by rfl) ⟨2611124, by rfl⟩ : syracuseStep 3481499 = 5222249) B5222249
theorem B3874715 : Blo 964590 3874715 := bstep (se 1 (by rfl) ⟨2906036, by rfl⟩ : syracuseStep 3874715 = 5812073) B5812073
theorem B1449959 : Blo 964590 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B9281537 : Blo 964590 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B1450079 : Blo 964590 1450079 := bstep (se 1 (by rfl) ⟨1087559, by rfl⟩ : syracuseStep 1450079 = 2175119) B2175119
theorem B1450139 : Blo 964590 1450139 := bstep (se 1 (by rfl) ⟨1087604, by rfl⟩ : syracuseStep 1450139 = 2175209) B2175209
theorem B1450223 : Blo 964590 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B23470337 : Blo 964590 23470337 := bstep (se 2 (by rfl) ⟨8801376, by rfl⟩ : syracuseStep 23470337 = 17602753) B17602753
theorem B1221151 : Blo 964590 1221151 := bstep (se 1 (by rfl) ⟨915863, by rfl⟩ : syracuseStep 1221151 = 1831727) B1831727
theorem B2171483 : Blo 964590 2171483 := bstep (se 1 (by rfl) ⟨1628612, by rfl⟩ : syracuseStep 2171483 = 3257225) B3257225
theorem B1450601 : Blo 964590 1450601 := bstep (se 2 (by rfl) ⟨543975, by rfl⟩ : syracuseStep 1450601 = 1087951) B1087951
theorem B1450607 : Blo 964590 1450607 := bstep (se 1 (by rfl) ⟨1087955, by rfl⟩ : syracuseStep 1450607 = 2175911) B2175911
theorem B4891265 : Blo 964590 4891265 := bstep (se 2 (by rfl) ⟨1834224, by rfl⟩ : syracuseStep 4891265 = 3668449) B3668449
theorem B2794559 : Blo 964590 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B2172059 : Blo 964590 2172059 := bstep (se 1 (by rfl) ⟨1629044, by rfl⟩ : syracuseStep 2172059 = 3258089) B3258089
theorem B1451231 : Blo 964590 1451231 := bstep (se 1 (by rfl) ⟨1088423, by rfl⟩ : syracuseStep 1451231 = 2176847) B2176847
theorem B1549775 : Blo 964590 1549775 := bstep (se 1 (by rfl) ⟨1162331, by rfl⟩ : syracuseStep 1549775 = 2324663) B2324663
theorem B1451471 : Blo 964590 1451471 := bstep (se 1 (by rfl) ⟨1088603, by rfl⟩ : syracuseStep 1451471 = 2177207) B2177207
theorem B1451657 : Blo 964590 1451657 := bstep (se 2 (by rfl) ⟨544371, by rfl⟩ : syracuseStep 1451657 = 1088743) B1088743
theorem B1451711 : Blo 964590 1451711 := bstep (se 1 (by rfl) ⟨1088783, by rfl⟩ : syracuseStep 1451711 = 2177567) B2177567
theorem B3483431 : Blo 964590 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B1451867 : Blo 964590 1451867 := bstep (se 1 (by rfl) ⟨1088900, by rfl⟩ : syracuseStep 1451867 = 2177801) B2177801
theorem B29763773 : Blo 964590 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B1452251 : Blo 964590 1452251 := bstep (se 1 (by rfl) ⟨1089188, by rfl⟩ : syracuseStep 1452251 = 2178377) B2178377
theorem B2173211 : Blo 964590 2173211 := bstep (se 1 (by rfl) ⟨1629908, by rfl⟩ : syracuseStep 2173211 = 3259817) B3259817
theorem B1223039 : Blo 964590 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B1452521 : Blo 964590 1452521 := bstep (se 2 (by rfl) ⟨544695, by rfl⟩ : syracuseStep 1452521 = 1089391) B1089391
theorem B1550831 : Blo 964590 1550831 := bstep (se 1 (by rfl) ⟨1163123, by rfl⟩ : syracuseStep 1550831 = 2326247) B2326247
theorem B1452527 : Blo 964590 1452527 := bstep (se 1 (by rfl) ⟨1089395, by rfl⟩ : syracuseStep 1452527 = 2178791) B2178791
theorem B1452839 : Blo 964590 1452839 := bstep (se 1 (by rfl) ⟨1089629, by rfl⟩ : syracuseStep 1452839 = 2179259) B2179259
theorem B1223743 : Blo 964590 1223743 := bstep (se 1 (by rfl) ⟨917807, by rfl⟩ : syracuseStep 1223743 = 1835615) B1835615
theorem B1650041 : Blo 964590 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B7351721 : Blo 964590 7351721 := bstep (se 2 (by rfl) ⟨2756895, by rfl⟩ : syracuseStep 7351721 = 5513791) B5513791
theorem B31338413 : Blo 964590 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B1224811 : Blo 964590 1224811 := bstep (se 1 (by rfl) ⟨918608, by rfl⟩ : syracuseStep 1224811 = 1837217) B1837217
theorem B2175137 : Blo 964590 2175137 := bstep (se 2 (by rfl) ⟨815676, by rfl⟩ : syracuseStep 2175137 = 1631353) B1631353
theorem B3092897 : Blo 964590 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B2175515 : Blo 964590 2175515 := bstep (se 1 (by rfl) ⟨1631636, by rfl⟩ : syracuseStep 2175515 = 3263273) B3263273
theorem B2175695 : Blo 964590 2175695 := bstep (se 1 (by rfl) ⟨1631771, by rfl⟩ : syracuseStep 2175695 = 3263543) B3263543
theorem B1225631 : Blo 964590 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B3093871 : Blo 964590 3093871 := bstep (se 1 (by rfl) ⟨2320403, by rfl⟩ : syracuseStep 3093871 = 4640807) B4640807
theorem B2176487 : Blo 964590 2176487 := bstep (se 1 (by rfl) ⟨1632365, by rfl⟩ : syracuseStep 2176487 = 3264731) B3264731
theorem B3094127 : Blo 964590 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B2176667 : Blo 964590 2176667 := bstep (se 1 (by rfl) ⟨1632500, by rfl⟩ : syracuseStep 2176667 = 3265001) B3265001
theorem B2176865 : Blo 964590 2176865 := bstep (se 2 (by rfl) ⟨816324, by rfl⟩ : syracuseStep 2176865 = 1632649) B1632649
theorem B6600571 : Blo 964590 6600571 := bstep (se 1 (by rfl) ⟨4950428, by rfl⟩ : syracuseStep 6600571 = 9900857) B9900857
theorem B3258251 : Blo 964590 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B16529345 : Blo 964590 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B964671 : Blo 964590 964671 := bstep (se 1 (by rfl) ⟨723503, by rfl⟩ : syracuseStep 964671 = 1447007) B1447007
theorem B964711 : Blo 964590 964711 := bstep (se 1 (by rfl) ⟨723533, by rfl⟩ : syracuseStep 964711 = 1447067) B1447067
theorem B5880023 : Blo 964590 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B965167 : Blo 964590 965167 := bstep (se 1 (by rfl) ⟨723875, by rfl⟩ : syracuseStep 965167 = 1447751) B1447751
theorem B965567 : Blo 964590 965567 := bstep (se 1 (by rfl) ⟨724175, by rfl⟩ : syracuseStep 965567 = 1448351) B1448351
theorem B965615 : Blo 964590 965615 := bstep (se 1 (by rfl) ⟨724211, by rfl⟩ : syracuseStep 965615 = 1448423) B1448423
theorem B4898231 : Blo 964590 4898231 := bstep (se 1 (by rfl) ⟨3673673, by rfl⟩ : syracuseStep 4898231 = 7347347) B7347347
theorem B3259871 : Blo 964590 3259871 := bstep (se 1 (by rfl) ⟨2444903, by rfl⟩ : syracuseStep 3259871 = 4889807) B4889807
theorem B966111 : Blo 964590 966111 := bstep (se 1 (by rfl) ⟨724583, by rfl⟩ : syracuseStep 966111 = 1449167) B1449167
theorem B22887947 : Blo 964590 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B1392175 : Blo 964590 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B966191 : Blo 964590 966191 := bstep (se 1 (by rfl) ⟨724643, by rfl⟩ : syracuseStep 966191 = 1449287) B1449287
theorem B966299 : Blo 964590 966299 := bstep (se 1 (by rfl) ⟨724724, by rfl⟩ : syracuseStep 966299 = 1449449) B1449449
theorem B966395 : Blo 964590 966395 := bstep (se 1 (by rfl) ⟨724796, by rfl⟩ : syracuseStep 966395 = 1449593) B1449593
theorem B1654523 : Blo 964590 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B966559 : Blo 964590 966559 := bstep (se 1 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 966559 = 1449839) B1449839
theorem B2179169 : Blo 964590 2179169 := bstep (se 2 (by rfl) ⟨817188, by rfl⟩ : syracuseStep 2179169 = 1634377) B1634377
theorem B2179241 : Blo 964590 2179241 := bstep (se 2 (by rfl) ⟨817215, by rfl⟩ : syracuseStep 2179241 = 1634431) B1634431
theorem B3260681 : Blo 964590 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B3719471 : Blo 964590 3719471 := bstep (se 1 (by rfl) ⟨2789603, by rfl⟩ : syracuseStep 3719471 = 5579207) B5579207
theorem B967015 : Blo 964590 967015 := bstep (se 1 (by rfl) ⟨725261, by rfl⟩ : syracuseStep 967015 = 1450523) B1450523
theorem B967135 : Blo 964590 967135 := bstep (se 1 (by rfl) ⟨725351, by rfl⟩ : syracuseStep 967135 = 1450703) B1450703
theorem B967143 : Blo 964590 967143 := bstep (se 1 (by rfl) ⟨725357, by rfl⟩ : syracuseStep 967143 = 1450715) B1450715
theorem B2441947 : Blo 964590 2441947 := bstep (se 1 (by rfl) ⟨1831460, by rfl⟩ : syracuseStep 2441947 = 3662921) B3662921
theorem B967419 : Blo 964590 967419 := bstep (se 1 (by rfl) ⟨725564, by rfl⟩ : syracuseStep 967419 = 1451129) B1451129
theorem B967999 : Blo 964590 967999 := bstep (se 1 (by rfl) ⟨725999, by rfl⟩ : syracuseStep 967999 = 1451999) B1451999
theorem B968007 : Blo 964590 968007 := bstep (se 1 (by rfl) ⟨726005, by rfl⟩ : syracuseStep 968007 = 1452011) B1452011
theorem B968039 : Blo 964590 968039 := bstep (se 1 (by rfl) ⟨726029, by rfl⟩ : syracuseStep 968039 = 1452059) B1452059
theorem B968283 : Blo 964590 968283 := bstep (se 1 (by rfl) ⟨726212, by rfl⟩ : syracuseStep 968283 = 1452425) B1452425
theorem B3262247 : Blo 964590 3262247 := bstep (se 1 (by rfl) ⟨2446685, by rfl⟩ : syracuseStep 3262247 = 4893371) B4893371
theorem B11028311 : Blo 964590 11028311 := bstep (se 1 (by rfl) ⟨8271233, by rfl⟩ : syracuseStep 11028311 = 16542467) B16542467
theorem B2934767 : Blo 964590 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2443385 : Blo 964590 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B3262625 : Blo 964590 3262625 := bstep (se 2 (by rfl) ⟨1223484, by rfl⟩ : syracuseStep 3262625 = 2446969) B2446969
theorem B22333907 : Blo 964590 22333907 := bstep (se 1 (by rfl) ⟨16750430, by rfl⟩ : syracuseStep 22333907 = 33500861) B33500861
theorem B10439219 : Blo 964590 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B2443871 : Blo 964590 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B5294909 : Blo 964590 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B7326935 : Blo 964590 7326935 := bstep (se 1 (by rfl) ⟨5495201, by rfl⟩ : syracuseStep 7326935 = 10990403) B10990403
theorem B11029769 : Blo 964590 11029769 := bstep (se 2 (by rfl) ⟨4136163, by rfl⟩ : syracuseStep 11029769 = 8272327) B8272327
theorem B48976265 : Blo 964590 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B9916985 : Blo 964590 9916985 := bstep (se 2 (by rfl) ⟨3718869, by rfl⟩ : syracuseStep 9916985 = 7437739) B7437739
theorem B6181541 : Blo 964590 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B3265595 : Blo 964590 3265595 := bstep (se 1 (by rfl) ⟨2449196, by rfl⟩ : syracuseStep 3265595 = 4898393) B4898393
theorem B10999151 : Blo 964590 10999151 := bstep (se 1 (by rfl) ⟨8249363, by rfl⟩ : syracuseStep 10999151 = 16498727) B16498727
theorem B27907577 : Blo 964590 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B1627823 : Blo 964590 1627823 := bstep (se 1 (by rfl) ⟨1220867, by rfl⟩ : syracuseStep 1627823 = 2441735) B2441735
theorem B2447081 : Blo 964590 2447081 := bstep (se 2 (by rfl) ⟨917655, by rfl⟩ : syracuseStep 2447081 = 1835311) B1835311
theorem B7329851 : Blo 964590 7329851 := bstep (se 1 (by rfl) ⟨5497388, by rfl⟩ : syracuseStep 7329851 = 10994777) B10994777
theorem B1628383 : Blo 964590 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B3266783 : Blo 964590 3266783 := bstep (se 1 (by rfl) ⟨2450087, by rfl⟩ : syracuseStep 3266783 = 4900175) B4900175
theorem B14899621 : Blo 964590 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B18569681 : Blo 964590 18569681 := bstep (se 2 (by rfl) ⟨6963630, by rfl⟩ : syracuseStep 18569681 = 13927261) B13927261
theorem B6969833 : Blo 964590 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B13916771 : Blo 964590 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B1628815 : Blo 964590 1628815 := bstep (se 1 (by rfl) ⟨1221611, by rfl⟩ : syracuseStep 1628815 = 2443223) B2443223
theorem B9296527 : Blo 964590 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B3267215 : Blo 964590 3267215 := bstep (se 1 (by rfl) ⟨2450411, by rfl⟩ : syracuseStep 3267215 = 4900823) B4900823
theorem B1629065 : Blo 964590 1629065 := bstep (se 2 (by rfl) ⟨610899, by rfl⟩ : syracuseStep 1629065 = 1221799) B1221799
theorem B7330823 : Blo 964590 7330823 := bstep (se 1 (by rfl) ⟨5498117, by rfl⟩ : syracuseStep 7330823 = 10996235) B10996235
theorem B11755019 : Blo 964590 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B12574885 : Blo 964590 12574885 := bstep (se 4 (by rfl) ⟨1178895, by rfl⟩ : syracuseStep 12574885 = 2357791) B2357791
theorem B4121711 : Blo 964590 4121711 := bstep (se 1 (by rfl) ⟨3091283, by rfl⟩ : syracuseStep 4121711 = 6182567) B6182567
theorem B7333253 : Blo 964590 7333253 := bstep (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) B1374985
theorem B2450857 : Blo 964590 2450857 := bstep (se 2 (by rfl) ⟨919071, by rfl⟩ : syracuseStep 2450857 = 1838143) B1838143
theorem B2320211 : Blo 964590 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B7333739 : Blo 964590 7333739 := bstep (se 1 (by rfl) ⟨5500304, by rfl⟩ : syracuseStep 7333739 = 11000609) B11000609
theorem B2451323 : Blo 964590 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B2615969 : Blo 964590 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B6351839 : Blo 964590 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B3664865 : Blo 964590 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B1305595 : Blo 964590 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B1567855 : Blo 964590 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B3665033 : Blo 964590 3665033 := bstep (se 2 (by rfl) ⟨1374387, by rfl⟩ : syracuseStep 3665033 = 2748775) B2748775
theorem B4649015 : Blo 964590 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B1470619 : Blo 964590 1470619 := bstep (se 1 (by rfl) ⟨1102964, by rfl⟩ : syracuseStep 1470619 = 2205929) B2205929
theorem B2945267 : Blo 964590 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B2093407 : Blo 964590 2093407 := bstep (se 1 (by rfl) ⟨1570055, by rfl⟩ : syracuseStep 2093407 = 3140111) B3140111
theorem B4714939 : Blo 964590 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B12579259 : Blo 964590 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B1831643 : Blo 964590 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B3666991 : Blo 964590 3666991 := bstep (se 1 (by rfl) ⟨2750243, by rfl⟩ : syracuseStep 3666991 = 5500487) B5500487
theorem B4126049 : Blo 964590 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B1832615 : Blo 964590 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B1374023 : Blo 964590 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B3667963 : Blo 964590 3667963 := bstep (se 1 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 3667963 = 5501945) B5501945
theorem B2062675 : Blo 964590 2062675 := bstep (se 1 (by rfl) ⟨1547006, by rfl⟩ : syracuseStep 2062675 = 3094013) B3094013
theorem B5503585 : Blo 964590 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B7339085 : Blo 964590 7339085 := bstep (se 3 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 7339085 = 2752157) B2752157
theorem B1375327 : Blo 964590 1375327 := bstep (se 1 (by rfl) ⟨1031495, by rfl⟩ : syracuseStep 1375327 = 2062991) B2062991
theorem B29817953 : Blo 964590 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B20905775 : Blo 964590 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B1835561 : Blo 964590 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B62587565 : Blo 964590 62587565 := bstep (se 3 (by rfl) ⟨11735168, by rfl⟩ : syracuseStep 62587565 = 23470337) B23470337
theorem B4884623 : Blo 964590 4884623 := bstep (se 1 (by rfl) ⟨3663467, by rfl⟩ : syracuseStep 4884623 = 7326935) B7326935
theorem B11012273 : Blo 964590 11012273 := bstep (se 2 (by rfl) ⟨4129602, by rfl⟩ : syracuseStep 11012273 = 8259205) B8259205
theorem B1837991 : Blo 964590 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B3673097 : Blo 964590 3673097 := bstep (se 2 (by rfl) ⟨1377411, by rfl⟩ : syracuseStep 3673097 = 2754823) B2754823
theorem B1085215 : Blo 964590 1085215 := bstep (se 1 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 1085215 = 1627823) B1627823
theorem B7343945 : Blo 964590 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B1740793 : Blo 964590 1740793 := bstep (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) B1305595
theorem B4886567 : Blo 964590 4886567 := bstep (se 1 (by rfl) ⟨3664925, by rfl⟩ : syracuseStep 4886567 = 7329851) B7329851
theorem B9277847 : Blo 964590 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B1086043 : Blo 964590 1086043 := bstep (se 1 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 1086043 = 1629065) B1629065
theorem B4887215 : Blo 964590 4887215 := bstep (se 1 (by rfl) ⟨3665411, by rfl⟩ : syracuseStep 4887215 = 7330823) B7330823
theorem B4133551 : Blo 964590 4133551 := bstep (se 1 (by rfl) ⟨3100163, by rfl⟩ : syracuseStep 4133551 = 6200327) B6200327
theorem B4133567 : Blo 964590 4133567 := bstep (se 1 (by rfl) ⟨3100175, by rfl⟩ : syracuseStep 4133567 = 6200351) B6200351
theorem B7836679 : Blo 964590 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B1447655 : Blo 964590 1447655 := bstep (se 1 (by rfl) ⟨1085741, by rfl⟩ : syracuseStep 1447655 = 2171483) B2171483
theorem B1448039 : Blo 964590 1448039 := bstep (se 1 (by rfl) ⟨1086029, by rfl⟩ : syracuseStep 1448039 = 2172059) B2172059
theorem B4888835 : Blo 964590 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B4889159 : Blo 964590 4889159 := bstep (se 1 (by rfl) ⟨3666869, by rfl⟩ : syracuseStep 4889159 = 7333739) B7333739
theorem B4135549 : Blo 964590 4135549 := bstep (se 3 (by rfl) ⟨775415, by rfl⟩ : syracuseStep 4135549 = 1550831) B1550831
theorem B4889321 : Blo 964590 4889321 := bstep (se 2 (by rfl) ⟨1833495, by rfl⟩ : syracuseStep 4889321 = 3666991) B3666991
theorem B1448807 : Blo 964590 1448807 := bstep (se 1 (by rfl) ⟨1086605, by rfl⟩ : syracuseStep 1448807 = 2173211) B2173211
theorem B1448873 : Blo 964590 1448873 := bstep (se 2 (by rfl) ⟨543327, by rfl⟩ : syracuseStep 1448873 = 1086655) B1086655
theorem B1449065 : Blo 964590 1449065 := bstep (se 2 (by rfl) ⟨543399, by rfl⟩ : syracuseStep 1449065 = 1086799) B1086799
theorem B1743979 : Blo 964590 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B1449257 : Blo 964590 1449257 := bstep (se 2 (by rfl) ⟨543471, by rfl⟩ : syracuseStep 1449257 = 1086943) B1086943
theorem B4234559 : Blo 964590 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B4890617 : Blo 964590 4890617 := bstep (se 2 (by rfl) ⟨1833981, by rfl⟩ : syracuseStep 4890617 = 3667963) B3667963
theorem B1450025 : Blo 964590 1450025 := bstep (se 2 (by rfl) ⟨543759, by rfl⟩ : syracuseStep 1450025 = 1087519) B1087519
theorem B1450091 : Blo 964590 1450091 := bstep (se 1 (by rfl) ⟨1087568, by rfl⟩ : syracuseStep 1450091 = 2175137) B2175137
theorem B2171177 : Blo 964590 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B1450343 : Blo 964590 1450343 := bstep (se 1 (by rfl) ⟨1087757, by rfl⟩ : syracuseStep 1450343 = 2175515) B2175515
theorem B1450463 : Blo 964590 1450463 := bstep (se 1 (by rfl) ⟨1087847, by rfl⟩ : syracuseStep 1450463 = 2175695) B2175695
theorem B1221095 : Blo 964590 1221095 := bstep (se 1 (by rfl) ⟨915821, by rfl⟩ : syracuseStep 1221095 = 1831643) B1831643
theorem B19866161 : Blo 964590 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B2171753 : Blo 964590 2171753 := bstep (se 2 (by rfl) ⟨814407, by rfl⟩ : syracuseStep 2171753 = 1628815) B1628815
theorem B12395369 : Blo 964590 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B1450991 : Blo 964590 1450991 := bstep (se 1 (by rfl) ⟨1088243, by rfl⟩ : syracuseStep 1450991 = 2176487) B2176487
theorem B1451111 : Blo 964590 1451111 := bstep (se 1 (by rfl) ⟨1088333, by rfl⟩ : syracuseStep 1451111 = 2176667) B2176667
theorem B1221743 : Blo 964590 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B1451243 : Blo 964590 1451243 := bstep (se 1 (by rfl) ⟨1088432, by rfl⟩ : syracuseStep 1451243 = 2176865) B2176865
theorem B2172167 : Blo 964590 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B11019563 : Blo 964590 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B35203045 : Blo 964590 35203045 := bstep (se 4 (by rfl) ⟨3300285, by rfl⟩ : syracuseStep 35203045 = 6600571) B6600571
theorem B4892723 : Blo 964590 4892723 := bstep (se 1 (by rfl) ⟨3669542, by rfl⟩ : syracuseStep 4892723 = 7339085) B7339085
theorem B2173247 : Blo 964590 2173247 := bstep (se 1 (by rfl) ⟨1629935, by rfl⟩ : syracuseStep 2173247 = 3259871) B3259871
theorem B9283997 : Blo 964590 9283997 := bstep (se 3 (by rfl) ⟨1740749, by rfl⟩ : syracuseStep 9283997 = 3481499) B3481499
theorem B13937183 : Blo 964590 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B1452779 : Blo 964590 1452779 := bstep (se 1 (by rfl) ⟨1089584, by rfl⟩ : syracuseStep 1452779 = 2179169) B2179169
theorem B1452827 : Blo 964590 1452827 := bstep (se 1 (by rfl) ⟨1089620, by rfl⟩ : syracuseStep 1452827 = 2179241) B2179241
theorem B12397373 : Blo 964590 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B2173787 : Blo 964590 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B7843301 : Blo 964590 7843301 := bstep (se 4 (by rfl) ⟨735309, by rfl⟩ : syracuseStep 7843301 = 1470619) B1470619
theorem B3255929 : Blo 964590 3255929 := bstep (se 2 (by rfl) ⟨1220973, by rfl⟩ : syracuseStep 3255929 = 2441947) B2441947
theorem B2174831 : Blo 964590 2174831 := bstep (se 1 (by rfl) ⟨1631123, by rfl⟩ : syracuseStep 2174831 = 3262247) B3262247
theorem B7352207 : Blo 964590 7352207 := bstep (se 1 (by rfl) ⟨5514155, by rfl⟩ : syracuseStep 7352207 = 11028311) B11028311
theorem B2175083 : Blo 964590 2175083 := bstep (se 1 (by rfl) ⟨1631312, by rfl⟩ : syracuseStep 2175083 = 3262625) B3262625
theorem B14889271 : Blo 964590 14889271 := bstep (se 1 (by rfl) ⟨11166953, by rfl⟩ : syracuseStep 14889271 = 22333907) B22333907
theorem B1225039 : Blo 964590 1225039 := bstep (se 1 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 1225039 = 1837559) B1837559
theorem B6959479 : Blo 964590 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B3257063 : Blo 964590 3257063 := bstep (se 1 (by rfl) ⟨2442797, by rfl⟩ : syracuseStep 3257063 = 4885595) B4885595
theorem B7353179 : Blo 964590 7353179 := bstep (se 1 (by rfl) ⟨5514884, by rfl⟩ : syracuseStep 7353179 = 11029769) B11029769
theorem B15905747 : Blo 964590 15905747 := bstep (se 1 (by rfl) ⟨11929310, by rfl⟩ : syracuseStep 15905747 = 23858621) B23858621
theorem B5879051 : Blo 964590 5879051 := bstep (se 1 (by rfl) ⟨4409288, by rfl⟩ : syracuseStep 5879051 = 8818577) B8818577
theorem B7452157 : Blo 964590 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B964603 : Blo 964590 964603 := bstep (se 1 (by rfl) ⟨723452, by rfl⟩ : syracuseStep 964603 = 1446905) B1446905
theorem B2177063 : Blo 964590 2177063 := bstep (se 1 (by rfl) ⟨1632797, by rfl⟩ : syracuseStep 2177063 = 3265595) B3265595
theorem B964735 : Blo 964590 964735 := bstep (se 1 (by rfl) ⟨723551, by rfl⟩ : syracuseStep 964735 = 1447103) B1447103
theorem B964831 : Blo 964590 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B964891 : Blo 964590 964891 := bstep (se 1 (by rfl) ⟨723668, by rfl⟩ : syracuseStep 964891 = 1447337) B1447337
theorem B964927 : Blo 964590 964927 := bstep (se 1 (by rfl) ⟨723695, by rfl⟩ : syracuseStep 964927 = 1447391) B1447391
theorem B964991 : Blo 964590 964991 := bstep (se 1 (by rfl) ⟨723743, by rfl⟩ : syracuseStep 964991 = 1447487) B1447487
theorem B4897259 : Blo 964590 4897259 := bstep (se 1 (by rfl) ⟨3672944, by rfl⟩ : syracuseStep 4897259 = 7345889) B7345889
theorem B965311 : Blo 964590 965311 := bstep (se 1 (by rfl) ⟨723983, by rfl⟩ : syracuseStep 965311 = 1447967) B1447967
theorem B2177855 : Blo 964590 2177855 := bstep (se 1 (by rfl) ⟨1633391, by rfl⟩ : syracuseStep 2177855 = 3266783) B3266783
theorem B965599 : Blo 964590 965599 := bstep (se 1 (by rfl) ⟨724199, by rfl⟩ : syracuseStep 965599 = 1448399) B1448399
theorem B965659 : Blo 964590 965659 := bstep (se 1 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 965659 = 1448489) B1448489
theorem B2178143 : Blo 964590 2178143 := bstep (se 1 (by rfl) ⟨1633607, by rfl⟩ : syracuseStep 2178143 = 3267215) B3267215
theorem B7847059 : Blo 964590 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B965799 : Blo 964590 965799 := bstep (se 1 (by rfl) ⟨724349, by rfl⟩ : syracuseStep 965799 = 1448699) B1448699
theorem B13417655 : Blo 964590 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B965883 : Blo 964590 965883 := bstep (se 1 (by rfl) ⟨724412, by rfl⟩ : syracuseStep 965883 = 1448825) B1448825
theorem B966383 : Blo 964590 966383 := bstep (se 1 (by rfl) ⟨724787, by rfl⟩ : syracuseStep 966383 = 1449575) B1449575
theorem B4898555 : Blo 964590 4898555 := bstep (se 1 (by rfl) ⟨3673916, by rfl⟩ : syracuseStep 4898555 = 7347833) B7347833
theorem B966491 : Blo 964590 966491 := bstep (se 1 (by rfl) ⟨724868, by rfl⟩ : syracuseStep 966491 = 1449737) B1449737
theorem B966639 : Blo 964590 966639 := bstep (se 1 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 966639 = 1449959) B1449959
theorem B966719 : Blo 964590 966719 := bstep (se 1 (by rfl) ⟨725039, by rfl⟩ : syracuseStep 966719 = 1450079) B1450079
theorem B966759 : Blo 964590 966759 := bstep (se 1 (by rfl) ⟨725069, by rfl⟩ : syracuseStep 966759 = 1450139) B1450139
theorem B966815 : Blo 964590 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B967067 : Blo 964590 967067 := bstep (se 1 (by rfl) ⟨725300, by rfl⟩ : syracuseStep 967067 = 1450601) B1450601
theorem B967071 : Blo 964590 967071 := bstep (se 1 (by rfl) ⟨725303, by rfl⟩ : syracuseStep 967071 = 1450607) B1450607
theorem B3260843 : Blo 964590 3260843 := bstep (se 1 (by rfl) ⟨2445632, by rfl⟩ : syracuseStep 3260843 = 4891265) B4891265
theorem B967487 : Blo 964590 967487 := bstep (se 1 (by rfl) ⟨725615, by rfl⟩ : syracuseStep 967487 = 1451231) B1451231
theorem B1033183 : Blo 964590 1033183 := bstep (se 1 (by rfl) ⟨774887, by rfl⟩ : syracuseStep 1033183 = 1549775) B1549775
theorem B967647 : Blo 964590 967647 := bstep (se 1 (by rfl) ⟨725735, by rfl⟩ : syracuseStep 967647 = 1451471) B1451471
theorem B3261437 : Blo 964590 3261437 := bstep (se 3 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 3261437 = 1223039) B1223039
theorem B967771 : Blo 964590 967771 := bstep (se 1 (by rfl) ⟨725828, by rfl⟩ : syracuseStep 967771 = 1451657) B1451657
theorem B967807 : Blo 964590 967807 := bstep (se 1 (by rfl) ⟨725855, by rfl⟩ : syracuseStep 967807 = 1451711) B1451711
theorem B12371129 : Blo 964590 12371129 := bstep (se 2 (by rfl) ⟨4639173, by rfl⟩ : syracuseStep 12371129 = 9278347) B9278347
theorem B967911 : Blo 964590 967911 := bstep (se 1 (by rfl) ⟨725933, by rfl⟩ : syracuseStep 967911 = 1451867) B1451867
theorem B19842515 : Blo 964590 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B968167 : Blo 964590 968167 := bstep (se 1 (by rfl) ⟨726125, by rfl⟩ : syracuseStep 968167 = 1452251) B1452251
theorem B968347 : Blo 964590 968347 := bstep (se 1 (by rfl) ⟨726260, by rfl⟩ : syracuseStep 968347 = 1452521) B1452521
theorem B968351 : Blo 964590 968351 := bstep (se 1 (by rfl) ⟨726263, by rfl⟩ : syracuseStep 968351 = 1452527) B1452527
theorem B968559 : Blo 964590 968559 := bstep (se 1 (by rfl) ⟨726419, by rfl⟩ : syracuseStep 968559 = 1452839) B1452839
theorem B2443243 : Blo 964590 2443243 := bstep (se 1 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 2443243 = 3664865) B3664865
theorem B2443355 : Blo 964590 2443355 := bstep (se 1 (by rfl) ⟨1832516, by rfl⟩ : syracuseStep 2443355 = 3665033) B3665033
theorem B1100027 : Blo 964590 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B4901147 : Blo 964590 4901147 := bstep (se 1 (by rfl) ⟨3675860, by rfl⟩ : syracuseStep 4901147 = 7351721) B7351721
theorem B20892275 : Blo 964590 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B3920015 : Blo 964590 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B1856233 : Blo 964590 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B19878635 : Blo 964590 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B3265487 : Blo 964590 3265487 := bstep (se 1 (by rfl) ⟨2449115, by rfl⟩ : syracuseStep 3265487 = 4898231) B4898231
theorem B15258631 : Blo 964590 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B1103015 : Blo 964590 1103015 := bstep (se 1 (by rfl) ⟨827261, by rfl⟩ : syracuseStep 1103015 = 1654523) B1654523
theorem B16766513 : Blo 964590 16766513 := bstep (se 2 (by rfl) ⟨6287442, by rfl⟩ : syracuseStep 16766513 = 12574885) B12574885
theorem B1628201 : Blo 964590 1628201 := bstep (se 2 (by rfl) ⟨610575, by rfl⟩ : syracuseStep 1628201 = 1221151) B1221151
theorem B3102943 : Blo 964590 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B130603373 : Blo 964590 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B11753855 : Blo 964590 11753855 := bstep (se 1 (by rfl) ⟨8815391, by rfl⟩ : syracuseStep 11753855 = 17630783) B17630783
theorem B1956511 : Blo 964590 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1628923 : Blo 964590 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B7428871 : Blo 964590 7428871 := bstep (se 1 (by rfl) ⟨5571653, by rfl⟩ : syracuseStep 7428871 = 11143307) B11143307
theorem B1629247 : Blo 964590 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B11164837 : Blo 964590 11164837 := bstep (se 4 (by rfl) ⟨1046703, by rfl⟩ : syracuseStep 11164837 = 2093407) B2093407
theorem B3529939 : Blo 964590 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B3267809 : Blo 964590 3267809 := bstep (se 2 (by rfl) ⟨1225428, by rfl⟩ : syracuseStep 3267809 = 2450857) B2450857
theorem B3268349 : Blo 964590 3268349 := bstep (se 3 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 3268349 = 1225631) B1225631
theorem B6971359 : Blo 964590 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B2449399 : Blo 964590 2449399 := bstep (se 1 (by rfl) ⟨1837049, by rfl⟩ : syracuseStep 2449399 = 3674099) B3674099
theorem B6611323 : Blo 964590 6611323 := bstep (se 1 (by rfl) ⟨4958492, by rfl⟩ : syracuseStep 6611323 = 9916985) B9916985
theorem B2449835 : Blo 964590 2449835 := bstep (se 1 (by rfl) ⟨1837376, by rfl⟩ : syracuseStep 2449835 = 3674753) B3674753
theorem B4121027 : Blo 964590 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B39674357 : Blo 964590 39674357 := bstep (se 5 (by rfl) ⟨1859735, by rfl⟩ : syracuseStep 39674357 = 3719471) B3719471
theorem B7332767 : Blo 964590 7332767 := bstep (se 1 (by rfl) ⟨5499575, by rfl⟩ : syracuseStep 7332767 = 10999151) B10999151
theorem B18605051 : Blo 964590 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B1631387 : Blo 964590 1631387 := bstep (se 1 (by rfl) ⟨1223540, by rfl⟩ : syracuseStep 1631387 = 2447081) B2447081
theorem B1631657 : Blo 964590 1631657 := bstep (se 2 (by rfl) ⟨611871, by rfl⟩ : syracuseStep 1631657 = 1223743) B1223743
theorem B2090473 : Blo 964590 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B2450999 : Blo 964590 2450999 := bstep (se 1 (by rfl) ⟨1838249, by rfl⟩ : syracuseStep 2450999 = 3676499) B3676499
theorem B12379787 : Blo 964590 12379787 := bstep (se 1 (by rfl) ⟨9284840, by rfl⟩ : syracuseStep 12379787 = 18569681) B18569681
theorem B4646555 : Blo 964590 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B3664061 : Blo 964590 3664061 := bstep (se 3 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 3664061 = 1374023) B1374023
theorem B6187229 : Blo 964590 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B2583143 : Blo 964590 2583143 := bstep (se 1 (by rfl) ⟨1937357, by rfl⟩ : syracuseStep 2583143 = 3874715) B3874715
theorem B6187691 : Blo 964590 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1633081 : Blo 964590 1633081 := bstep (se 2 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 1633081 = 1224811) B1224811
theorem B13593689 : Blo 964590 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B6286585 : Blo 964590 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B16772345 : Blo 964590 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B2747807 : Blo 964590 2747807 := bstep (se 1 (by rfl) ⟨2060855, by rfl⟩ : syracuseStep 2747807 = 4121711) B4121711
theorem B344289041 : Blo 964590 344289041 := bstep (se 2 (by rfl) ⟨129108390, by rfl⟩ : syracuseStep 344289041 = 258216781) B258216781
theorem B2322287 : Blo 964590 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B1634215 : Blo 964590 1634215 := bstep (se 1 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 1634215 = 2451323) B2451323
theorem B4125161 : Blo 964590 4125161 := bstep (se 2 (by rfl) ⟨1546935, by rfl⟩ : syracuseStep 4125161 = 3093871) B3093871
theorem B1963511 : Blo 964590 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B2061931 : Blo 964590 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B2750233 : Blo 964590 2750233 := bstep (se 2 (by rfl) ⟨1031337, by rfl⟩ : syracuseStep 2750233 = 2062675) B2062675
theorem B7338113 : Blo 964590 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B2750699 : Blo 964590 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B2062751 : Blo 964590 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B1833769 : Blo 964590 1833769 := bstep (se 2 (by rfl) ⟨687663, by rfl⟩ : syracuseStep 1833769 = 1375327) B1375327
theorem B8815097 : Blo 964590 8815097 := bstep (se 2 (by rfl) ⟨3305661, by rfl⟩ : syracuseStep 8815097 = 6611323) B6611323
theorem B1377577 : Blo 964590 1377577 := bstep (se 2 (by rfl) ⟨516591, by rfl⟩ : syracuseStep 1377577 = 1033183) B1033183
theorem B7341515 : Blo 964590 7341515 := bstep (se 1 (by rfl) ⟨5506136, by rfl⟩ : syracuseStep 7341515 = 11012273) B11012273
theorem B13928183 : Blo 964590 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B2755711 : Blo 964590 2755711 := bstep (se 1 (by rfl) ⟨2066783, by rfl⟩ : syracuseStep 2755711 = 4133567) B4133567
theorem B11177675 : Blo 964590 11177675 := bstep (se 1 (by rfl) ⟨8383256, by rfl⟩ : syracuseStep 11177675 = 16766513) B16766513
theorem B1085467 : Blo 964590 1085467 := bstep (se 1 (by rfl) ⟨814100, by rfl⟩ : syracuseStep 1085467 = 1628201) B1628201
theorem B87068915 : Blo 964590 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B7835903 : Blo 964590 7835903 := bstep (se 1 (by rfl) ⟨5876927, by rfl⟩ : syracuseStep 7835903 = 11753855) B11753855
theorem B1446953 : Blo 964590 1446953 := bstep (se 2 (by rfl) ⟨542607, by rfl⟩ : syracuseStep 1446953 = 1085215) B1085215
theorem B1447451 : Blo 964590 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B26449571 : Blo 964590 26449571 := bstep (se 1 (by rfl) ⟨19837178, by rfl⟩ : syracuseStep 26449571 = 39674357) B39674357
theorem B13244107 : Blo 964590 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B9279305 : Blo 964590 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B1447835 : Blo 964590 1447835 := bstep (se 1 (by rfl) ⟨1085876, by rfl⟩ : syracuseStep 1447835 = 2171753) B2171753
theorem B8263579 : Blo 964590 8263579 := bstep (se 1 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 8263579 = 12395369) B12395369
theorem B4888511 : Blo 964590 4888511 := bstep (se 1 (by rfl) ⟨3666383, by rfl⟩ : syracuseStep 4888511 = 7332767) B7332767
theorem B1087591 : Blo 964590 1087591 := bstep (se 1 (by rfl) ⟨815693, by rfl⟩ : syracuseStep 1087591 = 1631387) B1631387
theorem B1448057 : Blo 964590 1448057 := bstep (se 2 (by rfl) ⟨543021, by rfl⟩ : syracuseStep 1448057 = 1086043) B1086043
theorem B1448111 : Blo 964590 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B7346375 : Blo 964590 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B5511401 : Blo 964590 5511401 := bstep (se 2 (by rfl) ⟨2066775, by rfl⟩ : syracuseStep 5511401 = 4133551) B4133551
theorem B1087771 : Blo 964590 1087771 := bstep (se 1 (by rfl) ⟨815828, by rfl⟩ : syracuseStep 1087771 = 1631657) B1631657
theorem B1448831 : Blo 964590 1448831 := bstep (se 1 (by rfl) ⟨1086623, by rfl⟩ : syracuseStep 1448831 = 2173247) B2173247
theorem B8264915 : Blo 964590 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B1449191 : Blo 964590 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B9936209 : Blo 964590 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B11181563 : Blo 964590 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B2170619 : Blo 964590 2170619 := bstep (se 1 (by rfl) ⟨1627964, by rfl⟩ : syracuseStep 2170619 = 3255929) B3255929
theorem B1548191 : Blo 964590 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B1449887 : Blo 964590 1449887 := bstep (se 1 (by rfl) ⟨1087415, by rfl⟩ : syracuseStep 1449887 = 2174831) B2174831
theorem B1450055 : Blo 964590 1450055 := bstep (se 1 (by rfl) ⟨1087541, by rfl⟩ : syracuseStep 1450055 = 2175083) B2175083
theorem B4137257 : Blo 964590 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B2171375 : Blo 964590 2171375 := bstep (se 1 (by rfl) ⟨1628531, by rfl⟩ : syracuseStep 2171375 = 3257063) B3257063
theorem B5514065 : Blo 964590 5514065 := bstep (se 2 (by rfl) ⟨2067774, by rfl⟩ : syracuseStep 5514065 = 4135549) B4135549
theorem B2171897 : Blo 964590 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B9905161 : Blo 964590 9905161 := bstep (se 2 (by rfl) ⟨3714435, by rfl⟩ : syracuseStep 9905161 = 7428871) B7428871
theorem B1451375 : Blo 964590 1451375 := bstep (se 1 (by rfl) ⟨1088531, by rfl⟩ : syracuseStep 1451375 = 2177063) B2177063
theorem B2172329 : Blo 964590 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B4892075 : Blo 964590 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B10462745 : Blo 964590 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B14886449 : Blo 964590 14886449 := bstep (se 2 (by rfl) ⟨5582418, by rfl⟩ : syracuseStep 14886449 = 11164837) B11164837
theorem B1451903 : Blo 964590 1451903 := bstep (se 1 (by rfl) ⟨1088927, by rfl⟩ : syracuseStep 1451903 = 2177855) B2177855
theorem B1452095 : Blo 964590 1452095 := bstep (se 1 (by rfl) ⟨1089071, by rfl⟩ : syracuseStep 1452095 = 2178143) B2178143
theorem B2173895 : Blo 964590 2173895 := bstep (se 1 (by rfl) ⟨1630421, by rfl⟩ : syracuseStep 2173895 = 3260843) B3260843
theorem B41725043 : Blo 964590 41725043 := bstep (se 1 (by rfl) ⟨31293782, by rfl⟩ : syracuseStep 41725043 = 62587565) B62587565
theorem B2174291 : Blo 964590 2174291 := bstep (se 1 (by rfl) ⟨1630718, by rfl⟩ : syracuseStep 2174291 = 3261437) B3261437
theorem B3256253 : Blo 964590 3256253 := bstep (se 3 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 3256253 = 1221095) B1221095
theorem B3256415 : Blo 964590 3256415 := bstep (se 1 (by rfl) ⟨2442311, by rfl⟩ : syracuseStep 3256415 = 4884623) B4884623
theorem B4894829 : Blo 964590 4894829 := bstep (se 3 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 4894829 = 1835561) B1835561
theorem B4895963 : Blo 964590 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B46937393 : Blo 964590 46937393 := bstep (se 2 (by rfl) ⟨17601522, by rfl⟩ : syracuseStep 46937393 = 35203045) B35203045
theorem B3257657 : Blo 964590 3257657 := bstep (se 2 (by rfl) ⟨1221621, by rfl⟩ : syracuseStep 3257657 = 2443243) B2443243
theorem B3257711 : Blo 964590 3257711 := bstep (se 1 (by rfl) ⟨2443283, by rfl⟩ : syracuseStep 3257711 = 4886567) B4886567
theorem B3257981 : Blo 964590 3257981 := bstep (se 3 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 3257981 = 1221743) B1221743
theorem B3258143 : Blo 964590 3258143 := bstep (se 1 (by rfl) ⟨2443607, by rfl⟩ : syracuseStep 3258143 = 4887215) B4887215
theorem B13252423 : Blo 964590 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B2176991 : Blo 964590 2176991 := bstep (se 1 (by rfl) ⟨1632743, by rfl⟩ : syracuseStep 2176991 = 3265487) B3265487
theorem B2177441 : Blo 964590 2177441 := bstep (se 2 (by rfl) ⟨816540, by rfl⟩ : syracuseStep 2177441 = 1633081) B1633081
theorem B965103 : Blo 964590 965103 := bstep (se 1 (by rfl) ⟨723827, by rfl⟩ : syracuseStep 965103 = 1447655) B1447655
theorem B965359 : Blo 964590 965359 := bstep (se 1 (by rfl) ⟨724019, by rfl⟩ : syracuseStep 965359 = 1448039) B1448039
theorem B3259223 : Blo 964590 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B3259439 : Blo 964590 3259439 := bstep (se 1 (by rfl) ⟨2444579, by rfl⟩ : syracuseStep 3259439 = 4889159) B4889159
theorem B3259547 : Blo 964590 3259547 := bstep (se 1 (by rfl) ⟨2444660, by rfl⟩ : syracuseStep 3259547 = 4889321) B4889321
theorem B965871 : Blo 964590 965871 := bstep (se 1 (by rfl) ⟨724403, by rfl⟩ : syracuseStep 965871 = 1448807) B1448807
theorem B965915 : Blo 964590 965915 := bstep (se 1 (by rfl) ⟨724436, by rfl⟩ : syracuseStep 965915 = 1448873) B1448873
theorem B966043 : Blo 964590 966043 := bstep (se 1 (by rfl) ⟨724532, by rfl⟩ : syracuseStep 966043 = 1449065) B1449065
theorem B2178539 : Blo 964590 2178539 := bstep (se 1 (by rfl) ⟨1633904, by rfl⟩ : syracuseStep 2178539 = 3267809) B3267809
theorem B966171 : Blo 964590 966171 := bstep (se 1 (by rfl) ⟨724628, by rfl⟩ : syracuseStep 966171 = 1449257) B1449257
theorem B2178899 : Blo 964590 2178899 := bstep (se 1 (by rfl) ⟨1634174, by rfl⟩ : syracuseStep 2178899 = 3268349) B3268349
theorem B2178953 : Blo 964590 2178953 := bstep (se 2 (by rfl) ⟨817107, by rfl⟩ : syracuseStep 2178953 = 1634215) B1634215
theorem B3260411 : Blo 964590 3260411 := bstep (se 1 (by rfl) ⟨2445308, by rfl⟩ : syracuseStep 3260411 = 4890617) B4890617
theorem B966683 : Blo 964590 966683 := bstep (se 1 (by rfl) ⟨725012, by rfl⟩ : syracuseStep 966683 = 1450025) B1450025
theorem B41795621 : Blo 964590 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B966727 : Blo 964590 966727 := bstep (se 1 (by rfl) ⟨725045, by rfl⟩ : syracuseStep 966727 = 1450091) B1450091
theorem B966895 : Blo 964590 966895 := bstep (se 1 (by rfl) ⟨725171, by rfl⟩ : syracuseStep 966895 = 1450343) B1450343
theorem B966975 : Blo 964590 966975 := bstep (se 1 (by rfl) ⟨725231, by rfl⟩ : syracuseStep 966975 = 1450463) B1450463
theorem B2933405 : Blo 964590 2933405 := bstep (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) B1100027
theorem B967327 : Blo 964590 967327 := bstep (se 1 (by rfl) ⟨725495, by rfl⟩ : syracuseStep 967327 = 1450991) B1450991
theorem B12403367 : Blo 964590 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B967407 : Blo 964590 967407 := bstep (se 1 (by rfl) ⟨725555, by rfl⟩ : syracuseStep 967407 = 1451111) B1451111
theorem B967495 : Blo 964590 967495 := bstep (se 1 (by rfl) ⟨725621, by rfl⟩ : syracuseStep 967495 = 1451243) B1451243
theorem B2474977 : Blo 964590 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B3097703 : Blo 964590 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B3261815 : Blo 964590 3261815 := bstep (se 1 (by rfl) ⟨2446361, by rfl⟩ : syracuseStep 3261815 = 4892723) B4892723
theorem B2442707 : Blo 964590 2442707 := bstep (se 1 (by rfl) ⟨1832030, by rfl⟩ : syracuseStep 2442707 = 3664061) B3664061
theorem B9291455 : Blo 964590 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B1722095 : Blo 964590 1722095 := bstep (se 1 (by rfl) ⟨1291571, by rfl⟩ : syracuseStep 1722095 = 2583143) B2583143
theorem B968519 : Blo 964590 968519 := bstep (se 1 (by rfl) ⟨726389, by rfl⟩ : syracuseStep 968519 = 1452779) B1452779
theorem B968551 : Blo 964590 968551 := bstep (se 1 (by rfl) ⟨726413, by rfl⟩ : syracuseStep 968551 = 1452827) B1452827
theorem B9062459 : Blo 964590 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B5228867 : Blo 964590 5228867 := bstep (se 1 (by rfl) ⟨3921650, by rfl⟩ : syracuseStep 5228867 = 7843301) B7843301
theorem B4901309 : Blo 964590 4901309 := bstep (se 3 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 4901309 = 1837991) B1837991
theorem B229526027 : Blo 964590 229526027 := bstep (se 1 (by rfl) ⟨172144520, by rfl⟩ : syracuseStep 229526027 = 344289041) B344289041
theorem B4901471 : Blo 964590 4901471 := bstep (se 1 (by rfl) ⟨3676103, by rfl⟩ : syracuseStep 4901471 = 7352207) B7352207
theorem B4902119 : Blo 964590 4902119 := bstep (se 1 (by rfl) ⟨3676589, by rfl⟩ : syracuseStep 4902119 = 7353179) B7353179
theorem B10603831 : Blo 964590 10603831 := bstep (se 1 (by rfl) ⟨7952873, by rfl⟩ : syracuseStep 10603831 = 15905747) B15905747
theorem B11292157 : Blo 964590 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B3919367 : Blo 964590 3919367 := bstep (se 1 (by rfl) ⟨2939525, by rfl⟩ : syracuseStep 3919367 = 5879051) B5879051
theorem B2608681 : Blo 964590 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B2445025 : Blo 964590 2445025 := bstep (se 2 (by rfl) ⟨916884, by rfl⟩ : syracuseStep 2445025 = 1833769) B1833769
theorem B4706585 : Blo 964590 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B3264839 : Blo 964590 3264839 := bstep (se 1 (by rfl) ⟨2448629, by rfl⟩ : syracuseStep 3264839 = 4897259) B4897259
theorem B3265703 : Blo 964590 3265703 := bstep (se 1 (by rfl) ⟨2449277, by rfl⟩ : syracuseStep 3265703 = 4898555) B4898555
theorem B9295145 : Blo 964590 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B3265865 : Blo 964590 3265865 := bstep (se 2 (by rfl) ⟨1224699, by rfl⟩ : syracuseStep 3265865 = 2449399) B2449399
theorem B8247419 : Blo 964590 8247419 := bstep (se 1 (by rfl) ⟨6185564, by rfl⟩ : syracuseStep 8247419 = 12371129) B12371129
theorem B13228343 : Blo 964590 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B1628903 : Blo 964590 1628903 := bstep (se 1 (by rfl) ⟨1221677, by rfl⟩ : syracuseStep 1628903 = 2443355) B2443355
theorem B3267431 : Blo 964590 3267431 := bstep (se 1 (by rfl) ⟨2450573, by rfl⟩ : syracuseStep 3267431 = 4901147) B4901147
theorem B2448731 : Blo 964590 2448731 := bstep (se 1 (by rfl) ⟨1836548, by rfl⟩ : syracuseStep 2448731 = 3673097) B3673097
theorem B2613343 : Blo 964590 2613343 := bstep (se 1 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 2613343 = 3920015) B3920015
theorem B6185231 : Blo 964590 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B2941373 : Blo 964590 2941373 := bstep (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) B1103015
theorem B8382113 : Blo 964590 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B2321057 : Blo 964590 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B1633223 : Blo 964590 1633223 := bstep (se 1 (by rfl) ⟨1224917, by rfl⟩ : syracuseStep 1633223 = 2449835) B2449835
theorem B2747351 : Blo 964590 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B19852361 : Blo 964590 19852361 := bstep (se 2 (by rfl) ⟨7444635, by rfl⟩ : syracuseStep 19852361 = 14889271) B14889271
theorem B1633385 : Blo 964590 1633385 := bstep (se 2 (by rfl) ⟨612519, by rfl⟩ : syracuseStep 1633385 = 1225039) B1225039
theorem B7335197 : Blo 964590 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B1633999 : Blo 964590 1633999 := bstep (se 1 (by rfl) ⟨1225499, by rfl⟩ : syracuseStep 1633999 = 2450999) B2450999
theorem B5500669 : Blo 964590 5500669 := bstep (se 3 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 5500669 = 2062751) B2062751
theorem B8253191 : Blo 964590 8253191 := bstep (se 1 (by rfl) ⟨6189893, by rfl⟩ : syracuseStep 8253191 = 12379787) B12379787
theorem B20344841 : Blo 964590 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B4124819 : Blo 964590 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B6189331 : Blo 964590 6189331 := bstep (se 1 (by rfl) ⟨4641998, by rfl⟩ : syracuseStep 6189331 = 9283997) B9283997
theorem B4125127 : Blo 964590 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B2749241 : Blo 964590 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B1831871 : Blo 964590 1831871 := bstep (se 1 (by rfl) ⟨1373903, by rfl⟩ : syracuseStep 1831871 = 2747807) B2747807
theorem B3666977 : Blo 964590 3666977 := bstep (se 2 (by rfl) ⟨1375116, by rfl⟩ : syracuseStep 3666977 = 2750233) B2750233
theorem B2750107 : Blo 964590 2750107 := bstep (se 1 (by rfl) ⟨2062580, by rfl⟩ : syracuseStep 2750107 = 4125161) B4125161
theorem B35780413 : Blo 964590 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B1309007 : Blo 964590 1309007 := bstep (se 1 (by rfl) ⟨981755, by rfl⟩ : syracuseStep 1309007 = 1963511) B1963511
theorem B2325305 : Blo 964590 2325305 := bstep (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) B1743979
theorem B44596757 : Blo 964590 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B6194303 : Blo 964590 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B1148063 : Blo 964590 1148063 := bstep (se 1 (by rfl) ⟨861047, by rfl⟩ : syracuseStep 1148063 = 1722095) B1722095
theorem B13206881 : Blo 964590 13206881 := bstep (se 2 (by rfl) ⟨4952580, by rfl⟩ : syracuseStep 13206881 = 9905161) B9905161
theorem B1836769 : Blo 964590 1836769 := bstep (se 2 (by rfl) ⟨688788, by rfl⟩ : syracuseStep 1836769 = 1377577) B1377577
theorem B8260541 : Blo 964590 8260541 := bstep (se 3 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 8260541 = 3097703) B3097703
theorem B6196763 : Blo 964590 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B17633047 : Blo 964590 17633047 := bstep (se 1 (by rfl) ⟨13224785, by rfl⟩ : syracuseStep 17633047 = 26449571) B26449571
theorem B3674267 : Blo 964590 3674267 := bstep (se 1 (by rfl) ⟨2755700, by rfl⟩ : syracuseStep 3674267 = 5511401) B5511401
theorem B3674281 : Blo 964590 3674281 := bstep (se 2 (by rfl) ⟨1377855, by rfl⟩ : syracuseStep 3674281 = 2755711) B2755711
theorem B8818895 : Blo 964590 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B1085935 : Blo 964590 1085935 := bstep (se 1 (by rfl) ⟨814451, by rfl⟩ : syracuseStep 1085935 = 1628903) B1628903
theorem B3478241 : Blo 964590 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B5509943 : Blo 964590 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B6624139 : Blo 964590 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B1447079 : Blo 964590 1447079 := bstep (se 1 (by rfl) ⟨1085309, by rfl⟩ : syracuseStep 1447079 = 2170619) B2170619
theorem B1447289 : Blo 964590 1447289 := bstep (se 2 (by rfl) ⟨542733, by rfl⟩ : syracuseStep 1447289 = 1085467) B1085467
theorem B1447583 : Blo 964590 1447583 := bstep (se 1 (by rfl) ⟨1085687, by rfl⟩ : syracuseStep 1447583 = 2171375) B2171375
theorem B3676043 : Blo 964590 3676043 := bstep (se 1 (by rfl) ⟨2757032, by rfl⟩ : syracuseStep 3676043 = 5514065) B5514065
theorem B1447931 : Blo 964590 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B1448219 : Blo 964590 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B1547371 : Blo 964590 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B1449263 : Blo 964590 1449263 := bstep (se 1 (by rfl) ⟨1086947, by rfl⟩ : syracuseStep 1449263 = 2173895) B2173895
theorem B1088815 : Blo 964590 1088815 := bstep (se 1 (by rfl) ⟨816611, by rfl⟩ : syracuseStep 1088815 = 1633223) B1633223
theorem B1088923 : Blo 964590 1088923 := bstep (se 1 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 1088923 = 1633385) B1633385
theorem B6200813 : Blo 964590 6200813 := bstep (se 3 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 6200813 = 2325305) B2325305
theorem B4890131 : Blo 964590 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B1449527 : Blo 964590 1449527 := bstep (se 1 (by rfl) ⟨1087145, by rfl⟩ : syracuseStep 1449527 = 2174291) B2174291
theorem B17669897 : Blo 964590 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B11018105 : Blo 964590 11018105 := bstep (se 2 (by rfl) ⟨4131789, by rfl⟩ : syracuseStep 11018105 = 8263579) B8263579
theorem B2170835 : Blo 964590 2170835 := bstep (se 1 (by rfl) ⟨1628126, by rfl⟩ : syracuseStep 2170835 = 3256253) B3256253
theorem B2170943 : Blo 964590 2170943 := bstep (se 1 (by rfl) ⟨1628207, by rfl⟩ : syracuseStep 2170943 = 3256415) B3256415
theorem B1450121 : Blo 964590 1450121 := bstep (se 2 (by rfl) ⟨543795, by rfl⟩ : syracuseStep 1450121 = 1087591) B1087591
theorem B1450361 : Blo 964590 1450361 := bstep (se 2 (by rfl) ⟨543885, by rfl⟩ : syracuseStep 1450361 = 1087771) B1087771
theorem B1221247 : Blo 964590 1221247 := bstep (se 1 (by rfl) ⟨915935, by rfl⟩ : syracuseStep 1221247 = 1831871) B1831871
theorem B2171771 : Blo 964590 2171771 := bstep (se 1 (by rfl) ⟨1628828, by rfl⟩ : syracuseStep 2171771 = 3257657) B3257657
theorem B2171807 : Blo 964590 2171807 := bstep (se 1 (by rfl) ⟨1628855, by rfl⟩ : syracuseStep 2171807 = 3257711) B3257711
theorem B2171987 : Blo 964590 2171987 := bstep (se 1 (by rfl) ⟨1628990, by rfl⟩ : syracuseStep 2171987 = 3257981) B3257981
theorem B2172095 : Blo 964590 2172095 := bstep (se 1 (by rfl) ⟨1629071, by rfl⟩ : syracuseStep 2172095 = 3258143) B3258143
theorem B1451327 : Blo 964590 1451327 := bstep (se 1 (by rfl) ⟨1088495, by rfl⟩ : syracuseStep 1451327 = 2176991) B2176991
theorem B1451627 : Blo 964590 1451627 := bstep (se 1 (by rfl) ⟨1088720, by rfl⟩ : syracuseStep 1451627 = 2177441) B2177441
theorem B2172815 : Blo 964590 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B2172959 : Blo 964590 2172959 := bstep (se 1 (by rfl) ⟨1629719, by rfl⟩ : syracuseStep 2172959 = 3259439) B3259439
theorem B2173031 : Blo 964590 2173031 := bstep (se 1 (by rfl) ⟨1629773, by rfl⟩ : syracuseStep 2173031 = 3259547) B3259547
theorem B1452359 : Blo 964590 1452359 := bstep (se 1 (by rfl) ⟨1089269, by rfl⟩ : syracuseStep 1452359 = 2178539) B2178539
theorem B29731171 : Blo 964590 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B1452599 : Blo 964590 1452599 := bstep (se 1 (by rfl) ⟨1089449, by rfl⟩ : syracuseStep 1452599 = 2178899) B2178899
theorem B1452635 : Blo 964590 1452635 := bstep (se 1 (by rfl) ⟨1089476, by rfl⟩ : syracuseStep 1452635 = 2178953) B2178953
theorem B2173607 : Blo 964590 2173607 := bstep (se 1 (by rfl) ⟨1630205, by rfl⟩ : syracuseStep 2173607 = 3260411) B3260411
theorem B27863747 : Blo 964590 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B3484457 : Blo 964590 3484457 := bstep (se 2 (by rfl) ⟨1306671, by rfl⟩ : syracuseStep 3484457 = 2613343) B2613343
theorem B5876731 : Blo 964590 5876731 := bstep (se 1 (by rfl) ⟨4407548, by rfl⟩ : syracuseStep 5876731 = 8815097) B8815097
theorem B8268911 : Blo 964590 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B2174543 : Blo 964590 2174543 := bstep (se 1 (by rfl) ⟨1630907, by rfl⟩ : syracuseStep 2174543 = 3261815) B3261815
theorem B4894343 : Blo 964590 4894343 := bstep (se 1 (by rfl) ⟨3670757, by rfl⟩ : syracuseStep 4894343 = 7341515) B7341515
theorem B7843661 : Blo 964590 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B9285455 : Blo 964590 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B6041639 : Blo 964590 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B3485911 : Blo 964590 3485911 := bstep (se 1 (by rfl) ⟨2614433, by rfl⟩ : syracuseStep 3485911 = 5228867) B5228867
theorem B7451783 : Blo 964590 7451783 := bstep (se 1 (by rfl) ⟨5588837, by rfl⟩ : syracuseStep 7451783 = 11177675) B11177675
theorem B58045943 : Blo 964590 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B5223935 : Blo 964590 5223935 := bstep (se 1 (by rfl) ⟨3917951, by rfl⟩ : syracuseStep 5223935 = 7835903) B7835903
theorem B2176559 : Blo 964590 2176559 := bstep (se 1 (by rfl) ⟨1632419, by rfl⟩ : syracuseStep 2176559 = 3264839) B3264839
theorem B964635 : Blo 964590 964635 := bstep (se 1 (by rfl) ⟨723476, by rfl⟩ : syracuseStep 964635 = 1446953) B1446953
theorem B2177135 : Blo 964590 2177135 := bstep (se 1 (by rfl) ⟨1632851, by rfl⟩ : syracuseStep 2177135 = 3265703) B3265703
theorem B2177243 : Blo 964590 2177243 := bstep (se 1 (by rfl) ⟨1632932, by rfl⟩ : syracuseStep 2177243 = 3265865) B3265865
theorem B964967 : Blo 964590 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B965223 : Blo 964590 965223 := bstep (se 1 (by rfl) ⟨723917, by rfl⟩ : syracuseStep 965223 = 1447835) B1447835
theorem B3259007 : Blo 964590 3259007 := bstep (se 1 (by rfl) ⟨2444255, by rfl⟩ : syracuseStep 3259007 = 4888511) B4888511
theorem B965371 : Blo 964590 965371 := bstep (se 1 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 965371 = 1448057) B1448057
theorem B965407 : Blo 964590 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B4897583 : Blo 964590 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B14138441 : Blo 964590 14138441 := bstep (se 2 (by rfl) ⟨5301915, by rfl⟩ : syracuseStep 14138441 = 10603831) B10603831
theorem B2178287 : Blo 964590 2178287 := bstep (se 1 (by rfl) ⟨1633715, by rfl⟩ : syracuseStep 2178287 = 3267431) B3267431
theorem B965887 : Blo 964590 965887 := bstep (se 1 (by rfl) ⟨724415, by rfl⟩ : syracuseStep 965887 = 1448831) B1448831
theorem B15056209 : Blo 964590 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B966127 : Blo 964590 966127 := bstep (se 1 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 966127 = 1449191) B1449191
theorem B2178665 : Blo 964590 2178665 := bstep (se 2 (by rfl) ⟨816999, by rfl⟩ : syracuseStep 2178665 = 1633999) B1633999
theorem B3260033 : Blo 964590 3260033 := bstep (se 2 (by rfl) ⟨1222512, by rfl⟩ : syracuseStep 3260033 = 2445025) B2445025
theorem B7454375 : Blo 964590 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B966591 : Blo 964590 966591 := bstep (se 1 (by rfl) ⟨724943, by rfl⟩ : syracuseStep 966591 = 1449887) B1449887
theorem B966703 : Blo 964590 966703 := bstep (se 1 (by rfl) ⟨725027, by rfl⟩ : syracuseStep 966703 = 1450055) B1450055
theorem B3490685 : Blo 964590 3490685 := bstep (se 3 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 3490685 = 1309007) B1309007
theorem B967583 : Blo 964590 967583 := bstep (se 1 (by rfl) ⟨725687, by rfl⟩ : syracuseStep 967583 = 1451375) B1451375
theorem B3261383 : Blo 964590 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B5588075 : Blo 964590 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B967935 : Blo 964590 967935 := bstep (se 1 (by rfl) ⟨725951, by rfl⟩ : syracuseStep 967935 = 1451903) B1451903
theorem B968063 : Blo 964590 968063 := bstep (se 1 (by rfl) ⟨726047, by rfl⟩ : syracuseStep 968063 = 1452095) B1452095
theorem B3263219 : Blo 964590 3263219 := bstep (se 1 (by rfl) ⟨2447414, by rfl⟩ : syracuseStep 3263219 = 4894829) B4894829
theorem B2444651 : Blo 964590 2444651 := bstep (se 1 (by rfl) ⟨1833488, by rfl⟩ : syracuseStep 2444651 = 3666977) B3666977
theorem B3263975 : Blo 964590 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B1955603 : Blo 964590 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B11032685 : Blo 964590 11032685 := bstep (se 3 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 11032685 = 4137257) B4137257
theorem B1628471 : Blo 964590 1628471 := bstep (se 1 (by rfl) ⟨1221353, by rfl⟩ : syracuseStep 1628471 = 2442707) B2442707
theorem B3299969 : Blo 964590 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B3267539 : Blo 964590 3267539 := bstep (se 1 (by rfl) ⟨2450654, by rfl⟩ : syracuseStep 3267539 = 4901309) B4901309
theorem B153017351 : Blo 964590 153017351 := bstep (se 1 (by rfl) ⟨114763013, by rfl⟩ : syracuseStep 153017351 = 229526027) B229526027
theorem B3267647 : Blo 964590 3267647 := bstep (se 1 (by rfl) ⟨2450735, by rfl⟩ : syracuseStep 3267647 = 4901471) B4901471
theorem B7331309 : Blo 964590 7331309 := bstep (se 3 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 7331309 = 2749241) B2749241
theorem B3268079 : Blo 964590 3268079 := bstep (se 1 (by rfl) ⟨2451059, by rfl⟩ : syracuseStep 3268079 = 4902119) B4902119
theorem B2612911 : Blo 964590 2612911 := bstep (se 1 (by rfl) ⟨1959683, by rfl⟩ : syracuseStep 2612911 = 3919367) B3919367
theorem B3137723 : Blo 964590 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B6186203 : Blo 964590 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B5498279 : Blo 964590 5498279 := bstep (se 1 (by rfl) ⟨4123709, by rfl⟩ : syracuseStep 5498279 = 8247419) B8247419
theorem B1632487 : Blo 964590 1632487 := bstep (se 1 (by rfl) ⟨1224365, by rfl⟩ : syracuseStep 1632487 = 2448731) B2448731
theorem B7334225 : Blo 964590 7334225 := bstep (se 2 (by rfl) ⟨2750334, by rfl⟩ : syracuseStep 7334225 = 5500669) B5500669
theorem B4123487 : Blo 964590 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B8252441 : Blo 964590 8252441 := bstep (se 2 (by rfl) ⟨3094665, by rfl⟩ : syracuseStep 8252441 = 6189331) B6189331
theorem B5500169 : Blo 964590 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B6975163 : Blo 964590 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B9924299 : Blo 964590 9924299 := bstep (se 1 (by rfl) ⟨7443224, by rfl⟩ : syracuseStep 9924299 = 14886449) B14886449
theorem B1831567 : Blo 964590 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B13234907 : Blo 964590 13234907 := bstep (se 1 (by rfl) ⟨9926180, by rfl⟩ : syracuseStep 13234907 = 19852361) B19852361
theorem B27816695 : Blo 964590 27816695 := bstep (se 1 (by rfl) ⟨20862521, by rfl⟩ : syracuseStep 27816695 = 41725043) B41725043
theorem B3666809 : Blo 964590 3666809 := bstep (se 2 (by rfl) ⟨1375053, by rfl⟩ : syracuseStep 3666809 = 2750107) B2750107
theorem B17658809 : Blo 964590 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B47707217 : Blo 964590 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B5502127 : Blo 964590 5502127 := bstep (se 1 (by rfl) ⟨4126595, by rfl⟩ : syracuseStep 5502127 = 8253191) B8253191
theorem B13563227 : Blo 964590 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B2749879 : Blo 964590 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B31291595 : Blo 964590 31291595 := bstep (se 1 (by rfl) ⟨23468696, by rfl⟩ : syracuseStep 31291595 = 46937393) B46937393
theorem B4128509 : Blo 964590 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B2327123 : Blo 964590 2327123 := bstep (se 1 (by rfl) ⟨1745342, by rfl⟩ : syracuseStep 2327123 = 3490685) B3490685
theorem B4129535 : Blo 964590 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B9275309 : Blo 964590 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B5507027 : Blo 964590 5507027 := bstep (se 1 (by rfl) ⟨4130270, by rfl⟩ : syracuseStep 5507027 = 8260541) B8260541
theorem B4131175 : Blo 964590 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B3673295 : Blo 964590 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B1085647 : Blo 964590 1085647 := bstep (se 1 (by rfl) ⟨814235, by rfl⟩ : syracuseStep 1085647 = 1628471) B1628471
theorem B2199979 : Blo 964590 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B102011567 : Blo 964590 102011567 := bstep (se 1 (by rfl) ⟨76508675, by rfl⟩ : syracuseStep 102011567 = 153017351) B153017351
theorem B5214941 : Blo 964590 5214941 := bstep (se 3 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 5214941 = 1955603) B1955603
theorem B4887539 : Blo 964590 4887539 := bstep (se 1 (by rfl) ⟨3665654, by rfl⟩ : syracuseStep 4887539 = 7331309) B7331309
theorem B4133875 : Blo 964590 4133875 := bstep (se 1 (by rfl) ⟨3100406, by rfl⟩ : syracuseStep 4133875 = 6200813) B6200813
theorem B7345403 : Blo 964590 7345403 := bstep (se 1 (by rfl) ⟨5509052, by rfl⟩ : syracuseStep 7345403 = 11018105) B11018105
theorem B1447223 : Blo 964590 1447223 := bstep (se 1 (by rfl) ⟨1085417, by rfl⟩ : syracuseStep 1447223 = 2170835) B2170835
theorem B1447295 : Blo 964590 1447295 := bstep (se 1 (by rfl) ⟨1085471, by rfl⟩ : syracuseStep 1447295 = 2170943) B2170943
theorem B1447847 : Blo 964590 1447847 := bstep (se 1 (by rfl) ⟨1085885, by rfl⟩ : syracuseStep 1447847 = 2171771) B2171771
theorem B1447871 : Blo 964590 1447871 := bstep (se 1 (by rfl) ⟨1085903, by rfl⟩ : syracuseStep 1447871 = 2171807) B2171807
theorem B1447913 : Blo 964590 1447913 := bstep (se 2 (by rfl) ⟨542967, by rfl⟩ : syracuseStep 1447913 = 1085935) B1085935
theorem B1447991 : Blo 964590 1447991 := bstep (se 1 (by rfl) ⟨1085993, by rfl⟩ : syracuseStep 1447991 = 2171987) B2171987
theorem B1448063 : Blo 964590 1448063 := bstep (se 1 (by rfl) ⟨1086047, by rfl⟩ : syracuseStep 1448063 = 2172095) B2172095
theorem B1448543 : Blo 964590 1448543 := bstep (se 1 (by rfl) ⟨1086407, by rfl⟩ : syracuseStep 1448543 = 2172815) B2172815
theorem B1448639 : Blo 964590 1448639 := bstep (se 1 (by rfl) ⟨1086479, by rfl⟩ : syracuseStep 1448639 = 2172959) B2172959
theorem B1448687 : Blo 964590 1448687 := bstep (se 1 (by rfl) ⟨1086515, by rfl⟩ : syracuseStep 1448687 = 2173031) B2173031
theorem B4889483 : Blo 964590 4889483 := bstep (se 1 (by rfl) ⟨3667112, by rfl⟩ : syracuseStep 4889483 = 7334225) B7334225
theorem B1449071 : Blo 964590 1449071 := bstep (se 1 (by rfl) ⟨1086803, by rfl⟩ : syracuseStep 1449071 = 2173607) B2173607
theorem B5512607 : Blo 964590 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B1449695 : Blo 964590 1449695 := bstep (se 1 (by rfl) ⟨1087271, by rfl⟩ : syracuseStep 1449695 = 2174543) B2174543
theorem B8823271 : Blo 964590 8823271 := bstep (se 1 (by rfl) ⟨6617453, by rfl⟩ : syracuseStep 8823271 = 13234907) B13234907
theorem B11772539 : Blo 964590 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B37200869 : Blo 964590 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B3482623 : Blo 964590 3482623 := bstep (se 1 (by rfl) ⟨2611967, by rfl⟩ : syracuseStep 3482623 = 5223935) B5223935
theorem B1451039 : Blo 964590 1451039 := bstep (se 1 (by rfl) ⟨1088279, by rfl⟩ : syracuseStep 1451039 = 2176559) B2176559
theorem B1451423 : Blo 964590 1451423 := bstep (se 1 (by rfl) ⟨1088567, by rfl⟩ : syracuseStep 1451423 = 2177135) B2177135
theorem B1451495 : Blo 964590 1451495 := bstep (se 1 (by rfl) ⟨1088621, by rfl⟩ : syracuseStep 1451495 = 2177243) B2177243
theorem B1451753 : Blo 964590 1451753 := bstep (se 2 (by rfl) ⟨544407, by rfl⟩ : syracuseStep 1451753 = 1088815) B1088815
theorem B2172671 : Blo 964590 2172671 := bstep (se 1 (by rfl) ⟨1629503, by rfl⟩ : syracuseStep 2172671 = 3259007) B3259007
theorem B1451897 : Blo 964590 1451897 := bstep (se 2 (by rfl) ⟨544461, by rfl⟩ : syracuseStep 1451897 = 1088923) B1088923
theorem B1452191 : Blo 964590 1452191 := bstep (se 1 (by rfl) ⟨1089143, by rfl⟩ : syracuseStep 1452191 = 2178287) B2178287
theorem B3483881 : Blo 964590 3483881 := bstep (se 2 (by rfl) ⟨1306455, by rfl⟩ : syracuseStep 3483881 = 2612911) B2612911
theorem B1452443 : Blo 964590 1452443 := bstep (se 1 (by rfl) ⟨1089332, by rfl⟩ : syracuseStep 1452443 = 2178665) B2178665
theorem B2173355 : Blo 964590 2173355 := bstep (se 1 (by rfl) ⟨1630016, by rfl⟩ : syracuseStep 2173355 = 3260033) B3260033
theorem B2174255 : Blo 964590 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B2175479 : Blo 964590 2175479 := bstep (se 1 (by rfl) ⟨1631609, by rfl⟩ : syracuseStep 2175479 = 3263219) B3263219
theorem B2175983 : Blo 964590 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B2176649 : Blo 964590 2176649 := bstep (se 2 (by rfl) ⟨816243, by rfl⟩ : syracuseStep 2176649 = 1632487) B1632487
theorem B964719 : Blo 964590 964719 := bstep (se 1 (by rfl) ⟨723539, by rfl⟩ : syracuseStep 964719 = 1447079) B1447079
theorem B964859 : Blo 964590 964859 := bstep (se 1 (by rfl) ⟨723644, by rfl⟩ : syracuseStep 964859 = 1447289) B1447289
theorem B965055 : Blo 964590 965055 := bstep (se 1 (by rfl) ⟨723791, by rfl⟩ : syracuseStep 965055 = 1447583) B1447583
theorem B965287 : Blo 964590 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B7355123 : Blo 964590 7355123 := bstep (se 1 (by rfl) ⟨5516342, by rfl⟩ : syracuseStep 7355123 = 11032685) B11032685
theorem B965479 : Blo 964590 965479 := bstep (se 1 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 965479 = 1448219) B1448219
theorem B2178359 : Blo 964590 2178359 := bstep (se 1 (by rfl) ⟨1633769, by rfl⟩ : syracuseStep 2178359 = 3267539) B3267539
theorem B2178431 : Blo 964590 2178431 := bstep (se 1 (by rfl) ⟨1633823, by rfl⟩ : syracuseStep 2178431 = 3267647) B3267647
theorem B966175 : Blo 964590 966175 := bstep (se 1 (by rfl) ⟨724631, by rfl⟩ : syracuseStep 966175 = 1449263) B1449263
theorem B2178719 : Blo 964590 2178719 := bstep (se 1 (by rfl) ⟨1634039, by rfl⟩ : syracuseStep 2178719 = 3268079) B3268079
theorem B3260087 : Blo 964590 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B23510729 : Blo 964590 23510729 := bstep (se 2 (by rfl) ⟨8816523, by rfl⟩ : syracuseStep 23510729 = 17633047) B17633047
theorem B966351 : Blo 964590 966351 := bstep (se 1 (by rfl) ⟨724763, by rfl⟩ : syracuseStep 966351 = 1449527) B1449527
theorem B11779931 : Blo 964590 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B31342565 : Blo 964590 31342565 := bstep (se 4 (by rfl) ⟨2938365, by rfl⟩ : syracuseStep 31342565 = 5876731) B5876731
theorem B966747 : Blo 964590 966747 := bstep (se 1 (by rfl) ⟨725060, by rfl⟩ : syracuseStep 966747 = 1450121) B1450121
theorem B4899041 : Blo 964590 4899041 := bstep (se 2 (by rfl) ⟨1837140, by rfl⟩ : syracuseStep 4899041 = 3674281) B3674281
theorem B966907 : Blo 964590 966907 := bstep (se 1 (by rfl) ⟨725180, by rfl⟩ : syracuseStep 966907 = 1450361) B1450361
theorem B2442089 : Blo 964590 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B967551 : Blo 964590 967551 := bstep (se 1 (by rfl) ⟨725663, by rfl⟩ : syracuseStep 967551 = 1451327) B1451327
theorem B967751 : Blo 964590 967751 := bstep (se 1 (by rfl) ⟨725813, by rfl⟩ : syracuseStep 967751 = 1451627) B1451627
theorem B8832185 : Blo 964590 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B968239 : Blo 964590 968239 := bstep (se 1 (by rfl) ⟨726179, by rfl⟩ : syracuseStep 968239 = 1452359) B1452359
theorem B968399 : Blo 964590 968399 := bstep (se 1 (by rfl) ⟨726299, by rfl⟩ : syracuseStep 968399 = 1452599) B1452599
theorem B968423 : Blo 964590 968423 := bstep (se 1 (by rfl) ⟨726317, by rfl⟩ : syracuseStep 968423 = 1452635) B1452635
theorem B80299781 : Blo 964590 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B3262895 : Blo 964590 3262895 := bstep (se 1 (by rfl) ⟨2447171, by rfl⟩ : syracuseStep 3262895 = 4894343) B4894343
theorem B5229107 : Blo 964590 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B2444539 : Blo 964590 2444539 := bstep (se 1 (by rfl) ⟨1833404, by rfl⟩ : syracuseStep 2444539 = 3666809) B3666809
theorem B31804811 : Blo 964590 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B4967855 : Blo 964590 4967855 := bstep (se 1 (by rfl) ⟨3725891, by rfl⟩ : syracuseStep 4967855 = 7451783) B7451783
theorem B20861063 : Blo 964590 20861063 := bstep (se 1 (by rfl) ⟨15645797, by rfl⟩ : syracuseStep 20861063 = 31291595) B31291595
theorem B3265055 : Blo 964590 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B9425627 : Blo 964590 9425627 := bstep (se 1 (by rfl) ⟨7069220, by rfl⟩ : syracuseStep 9425627 = 14138441) B14138441
theorem B24761213 : Blo 964590 24761213 := bstep (se 3 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 24761213 = 9285455) B9285455
theorem B4969583 : Blo 964590 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B16111037 : Blo 964590 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B23517053 : Blo 964590 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B3725383 : Blo 964590 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B1628329 : Blo 964590 1628329 := bstep (se 2 (by rfl) ⟨610623, by rfl⟩ : syracuseStep 1628329 = 1221247) B1221247
theorem B8804587 : Blo 964590 8804587 := bstep (se 1 (by rfl) ⟨6603440, by rfl⟩ : syracuseStep 8804587 = 13206881) B13206881
theorem B12246005 : Blo 964590 12246005 := bstep (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) B1148063
theorem B1629767 : Blo 964590 1629767 := bstep (se 1 (by rfl) ⟨1222325, by rfl⟩ : syracuseStep 1629767 = 2444651) B2444651
theorem B2449025 : Blo 964590 2449025 := bstep (se 2 (by rfl) ⟨918384, by rfl⟩ : syracuseStep 2449025 = 1836769) B1836769
theorem B2449511 : Blo 964590 2449511 := bstep (se 1 (by rfl) ⟨1837133, by rfl⟩ : syracuseStep 2449511 = 3674267) B3674267
theorem B39641561 : Blo 964590 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B2450695 : Blo 964590 2450695 := bstep (se 1 (by rfl) ⟨1838021, by rfl⟩ : syracuseStep 2450695 = 3676043) B3676043
theorem B154789181 : Blo 964590 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B2091815 : Blo 964590 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B4647881 : Blo 964590 4647881 := bstep (se 2 (by rfl) ⟨1742955, by rfl⟩ : syracuseStep 4647881 = 3485911) B3485911
theorem B4124135 : Blo 964590 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B3665519 : Blo 964590 3665519 := bstep (se 1 (by rfl) ⟨2749139, by rfl⟩ : syracuseStep 3665519 = 5498279) B5498279
theorem B7336169 : Blo 964590 7336169 := bstep (se 2 (by rfl) ⟨2751063, by rfl⟩ : syracuseStep 7336169 = 5502127) B5502127
theorem B18575831 : Blo 964590 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B2322971 : Blo 964590 2322971 := bstep (se 1 (by rfl) ⟨1742228, by rfl⟩ : syracuseStep 2322971 = 3484457) B3484457
theorem B2748991 : Blo 964590 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B3666505 : Blo 964590 3666505 := bstep (se 2 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 3666505 = 2749879) B2749879
theorem B5501627 : Blo 964590 5501627 := bstep (se 1 (by rfl) ⟨4126220, by rfl⟩ : syracuseStep 5501627 = 8252441) B8252441
theorem B3666779 : Blo 964590 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B6616199 : Blo 964590 6616199 := bstep (se 1 (by rfl) ⟨4962149, by rfl⟩ : syracuseStep 6616199 = 9924299) B9924299
theorem B18544463 : Blo 964590 18544463 := bstep (se 1 (by rfl) ⟨13908347, by rfl⟩ : syracuseStep 18544463 = 27816695) B27816695
theorem B9042151 : Blo 964590 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B2063161 : Blo 964590 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B11009357 : Blo 964590 11009357 := bstep (se 3 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 11009357 = 4128509) B4128509
theorem B2753023 : Blo 964590 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B11764361 : Blo 964590 11764361 := bstep (se 2 (by rfl) ⟨4411635, by rfl⟩ : syracuseStep 11764361 = 8823271) B8823271
theorem B3671351 : Blo 964590 3671351 := bstep (se 1 (by rfl) ⟨2753513, by rfl⟩ : syracuseStep 3671351 = 5507027) B5507027
theorem B11733221 : Blo 964590 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B21203207 : Blo 964590 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B3311903 : Blo 964590 3311903 := bstep (se 1 (by rfl) ⟨2483927, by rfl⟩ : syracuseStep 3311903 = 4967855) B4967855
theorem B5508233 : Blo 964590 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B3476627 : Blo 964590 3476627 := bstep (se 1 (by rfl) ⟨2607470, by rfl⟩ : syracuseStep 3476627 = 5214941) B5214941
theorem B3313055 : Blo 964590 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B8164003 : Blo 964590 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B3675071 : Blo 964590 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B1086511 : Blo 964590 1086511 := bstep (se 1 (by rfl) ⟨814883, by rfl⟩ : syracuseStep 1086511 = 1629767) B1629767
theorem B1447529 : Blo 964590 1447529 := bstep (se 2 (by rfl) ⟨542823, by rfl⟩ : syracuseStep 1447529 = 1085647) B1085647
theorem B4888673 : Blo 964590 4888673 := bstep (se 2 (by rfl) ⟨1833252, by rfl⟩ : syracuseStep 4888673 = 3666505) B3666505
theorem B103192787 : Blo 964590 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B1448447 : Blo 964590 1448447 := bstep (se 1 (by rfl) ⟨1086335, by rfl⟩ : syracuseStep 1448447 = 2172671) B2172671
theorem B5511833 : Blo 964590 5511833 := bstep (se 2 (by rfl) ⟨2066937, by rfl⟩ : syracuseStep 5511833 = 4133875) B4133875
theorem B1448903 : Blo 964590 1448903 := bstep (se 1 (by rfl) ⟨1086677, by rfl⟩ : syracuseStep 1448903 = 2173355) B2173355
theorem B1449503 : Blo 964590 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B4890779 : Blo 964590 4890779 := bstep (se 1 (by rfl) ⟨3668084, by rfl⟩ : syracuseStep 4890779 = 7336169) B7336169
theorem B2171105 : Blo 964590 2171105 := bstep (se 2 (by rfl) ⟨814164, by rfl⟩ : syracuseStep 2171105 = 1628329) B1628329
theorem B11739449 : Blo 964590 11739449 := bstep (se 2 (by rfl) ⟨4402293, by rfl⟩ : syracuseStep 11739449 = 8804587) B8804587
theorem B1450319 : Blo 964590 1450319 := bstep (se 1 (by rfl) ⟨1087739, by rfl⟩ : syracuseStep 1450319 = 2175479) B2175479
theorem B1548647 : Blo 964590 1548647 := bstep (se 1 (by rfl) ⟨1161485, by rfl⟩ : syracuseStep 1548647 = 2322971) B2322971
theorem B1450655 : Blo 964590 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B1451099 : Blo 964590 1451099 := bstep (se 1 (by rfl) ⟨1088324, by rfl⟩ : syracuseStep 1451099 = 2176649) B2176649
theorem B12362975 : Blo 964590 12362975 := bstep (se 1 (by rfl) ⟨9272231, by rfl⟩ : syracuseStep 12362975 = 18544463) B18544463
theorem B1452239 : Blo 964590 1452239 := bstep (se 1 (by rfl) ⟨1089179, by rfl⟩ : syracuseStep 1452239 = 2178359) B2178359
theorem B1452287 : Blo 964590 1452287 := bstep (se 1 (by rfl) ⟨1089215, by rfl⟩ : syracuseStep 1452287 = 2178431) B2178431
theorem B1452479 : Blo 964590 1452479 := bstep (se 1 (by rfl) ⟨1089359, by rfl⟩ : syracuseStep 1452479 = 2178719) B2178719
theorem B2173391 : Blo 964590 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B15673819 : Blo 964590 15673819 := bstep (se 1 (by rfl) ⟨11755364, by rfl⟩ : syracuseStep 15673819 = 23510729) B23510729
theorem B1551415 : Blo 964590 1551415 := bstep (se 1 (by rfl) ⟨1163561, by rfl⟩ : syracuseStep 1551415 = 2327123) B2327123
theorem B2175263 : Blo 964590 2175263 := bstep (se 1 (by rfl) ⟨1631447, by rfl⟩ : syracuseStep 2175263 = 3262895) B3262895
theorem B3486071 : Blo 964590 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B13907375 : Blo 964590 13907375 := bstep (se 1 (by rfl) ⟨10430531, by rfl⟩ : syracuseStep 13907375 = 20861063) B20861063
theorem B17643197 : Blo 964590 17643197 := bstep (se 3 (by rfl) ⟨3308099, by rfl⟩ : syracuseStep 17643197 = 6616199) B6616199
theorem B2176703 : Blo 964590 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B3258359 : Blo 964590 3258359 := bstep (se 1 (by rfl) ⟨2443769, by rfl⟩ : syracuseStep 3258359 = 4887539) B4887539
theorem B4896935 : Blo 964590 4896935 := bstep (se 1 (by rfl) ⟨3672701, by rfl⟩ : syracuseStep 4896935 = 7345403) B7345403
theorem B964815 : Blo 964590 964815 := bstep (se 1 (by rfl) ⟨723611, by rfl⟩ : syracuseStep 964815 = 1447223) B1447223
theorem B964863 : Blo 964590 964863 := bstep (se 1 (by rfl) ⟨723647, by rfl⟩ : syracuseStep 964863 = 1447295) B1447295
theorem B15678035 : Blo 964590 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B965231 : Blo 964590 965231 := bstep (se 1 (by rfl) ⟨723923, by rfl⟩ : syracuseStep 965231 = 1447847) B1447847
theorem B965247 : Blo 964590 965247 := bstep (se 1 (by rfl) ⟨723935, by rfl⟩ : syracuseStep 965247 = 1447871) B1447871
theorem B965275 : Blo 964590 965275 := bstep (se 1 (by rfl) ⟨723956, by rfl⟩ : syracuseStep 965275 = 1447913) B1447913
theorem B965327 : Blo 964590 965327 := bstep (se 1 (by rfl) ⟨723995, by rfl⟩ : syracuseStep 965327 = 1447991) B1447991
theorem B965375 : Blo 964590 965375 := bstep (se 1 (by rfl) ⟨724031, by rfl⟩ : syracuseStep 965375 = 1448063) B1448063
theorem B3259385 : Blo 964590 3259385 := bstep (se 2 (by rfl) ⟨1222269, by rfl⟩ : syracuseStep 3259385 = 2444539) B2444539
theorem B965695 : Blo 964590 965695 := bstep (se 1 (by rfl) ⟨724271, by rfl⟩ : syracuseStep 965695 = 1448543) B1448543
theorem B965759 : Blo 964590 965759 := bstep (se 1 (by rfl) ⟨724319, by rfl⟩ : syracuseStep 965759 = 1448639) B1448639
theorem B965791 : Blo 964590 965791 := bstep (se 1 (by rfl) ⟨724343, by rfl⟩ : syracuseStep 965791 = 1448687) B1448687
theorem B3259655 : Blo 964590 3259655 := bstep (se 1 (by rfl) ⟨2444741, by rfl⟩ : syracuseStep 3259655 = 4889483) B4889483
theorem B966047 : Blo 964590 966047 := bstep (se 1 (by rfl) ⟨724535, by rfl⟩ : syracuseStep 966047 = 1449071) B1449071
theorem B966463 : Blo 964590 966463 := bstep (se 1 (by rfl) ⟨724847, by rfl⟩ : syracuseStep 966463 = 1449695) B1449695
theorem B26427707 : Blo 964590 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B7848359 : Blo 964590 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B967359 : Blo 964590 967359 := bstep (se 1 (by rfl) ⟨725519, by rfl⟩ : syracuseStep 967359 = 1451039) B1451039
theorem B967615 : Blo 964590 967615 := bstep (se 1 (by rfl) ⟨725711, by rfl⟩ : syracuseStep 967615 = 1451423) B1451423
theorem B967663 : Blo 964590 967663 := bstep (se 1 (by rfl) ⟨725747, by rfl⟩ : syracuseStep 967663 = 1451495) B1451495
theorem B967835 : Blo 964590 967835 := bstep (se 1 (by rfl) ⟨725876, by rfl⟩ : syracuseStep 967835 = 1451753) B1451753
theorem B967931 : Blo 964590 967931 := bstep (se 1 (by rfl) ⟨725948, by rfl⟩ : syracuseStep 967931 = 1451897) B1451897
theorem B968127 : Blo 964590 968127 := bstep (se 1 (by rfl) ⟨726095, by rfl⟩ : syracuseStep 968127 = 1452191) B1452191
theorem B968295 : Blo 964590 968295 := bstep (se 1 (by rfl) ⟨726221, by rfl⟩ : syracuseStep 968295 = 1452443) B1452443
theorem B1394543 : Blo 964590 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B3098587 : Blo 964590 3098587 := bstep (se 1 (by rfl) ⟨2323940, by rfl⟩ : syracuseStep 3098587 = 4647881) B4647881
theorem B2443679 : Blo 964590 2443679 := bstep (se 1 (by rfl) ⟨1832759, by rfl⟩ : syracuseStep 2443679 = 3665519) B3665519
theorem B4967177 : Blo 964590 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B2444519 : Blo 964590 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B10997693 : Blo 964590 10997693 := bstep (se 3 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 10997693 = 4124135) B4124135
theorem B4903415 : Blo 964590 4903415 := bstep (se 1 (by rfl) ⟨3677561, by rfl⟩ : syracuseStep 4903415 = 7355123) B7355123
theorem B7853287 : Blo 964590 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B20895043 : Blo 964590 20895043 := bstep (se 1 (by rfl) ⟨15671282, by rfl⟩ : syracuseStep 20895043 = 31342565) B31342565
theorem B3266027 : Blo 964590 3266027 := bstep (se 1 (by rfl) ⟨2449520, by rfl⟩ : syracuseStep 3266027 = 4899041) B4899041
theorem B1628059 : Blo 964590 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B5888123 : Blo 964590 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B53533187 : Blo 964590 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B6183539 : Blo 964590 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B4643497 : Blo 964590 4643497 := bstep (se 2 (by rfl) ⟨1741311, by rfl⟩ : syracuseStep 4643497 = 3482623) B3482623
theorem B3267593 : Blo 964590 3267593 := bstep (se 2 (by rfl) ⟨1225347, by rfl⟩ : syracuseStep 3267593 = 2450695) B2450695
theorem B272030845 : Blo 964590 272030845 := bstep (se 3 (by rfl) ⟨51005783, by rfl⟩ : syracuseStep 272030845 = 102011567) B102011567
theorem B2448863 : Blo 964590 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B6283751 : Blo 964590 6283751 := bstep (se 1 (by rfl) ⟨4712813, by rfl⟩ : syracuseStep 6283751 = 9425627) B9425627
theorem B16507475 : Blo 964590 16507475 := bstep (se 1 (by rfl) ⟨12380606, by rfl⟩ : syracuseStep 16507475 = 24761213) B24761213
theorem B10740691 : Blo 964590 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B11003525 : Blo 964590 11003525 := bstep (se 4 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 11003525 = 2063161) B2063161
theorem B1632683 : Blo 964590 1632683 := bstep (se 1 (by rfl) ⟨1224512, by rfl⟩ : syracuseStep 1632683 = 2449025) B2449025
theorem B1633007 : Blo 964590 1633007 := bstep (se 1 (by rfl) ⟨1224755, by rfl⟩ : syracuseStep 1633007 = 2449511) B2449511
theorem B24800579 : Blo 964590 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B3665321 : Blo 964590 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B2322587 : Blo 964590 2322587 := bstep (se 1 (by rfl) ⟨1741940, by rfl⟩ : syracuseStep 2322587 = 3483881) B3483881
theorem B12056201 : Blo 964590 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B12383887 : Blo 964590 12383887 := bstep (se 1 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 12383887 = 18575831) B18575831
theorem B3667751 : Blo 964590 3667751 := bstep (se 1 (by rfl) ⟨2750813, by rfl⟩ : syracuseStep 3667751 = 5501627) B5501627
theorem B7339571 : Blo 964590 7339571 := bstep (se 1 (by rfl) ⟨5504678, by rfl⟩ : syracuseStep 7339571 = 11009357) B11009357
theorem B3670697 : Blo 964590 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B14320921 : Blo 964590 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B3672155 : Blo 964590 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B4131449 : Blo 964590 4131449 := bstep (se 2 (by rfl) ⟨1549293, by rfl⟩ : syracuseStep 4131449 = 3098587) B3098587
theorem B2068553 : Blo 964590 2068553 := bstep (se 2 (by rfl) ⟨775707, by rfl⟩ : syracuseStep 2068553 = 1551415) B1551415
theorem B35688791 : Blo 964590 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B3674555 : Blo 964590 3674555 := bstep (se 1 (by rfl) ⟨2755916, by rfl⟩ : syracuseStep 3674555 = 5511833) B5511833
theorem B1447403 : Blo 964590 1447403 := bstep (se 1 (by rfl) ⟨1085552, by rfl⟩ : syracuseStep 1447403 = 2171105) B2171105
theorem B10885337 : Blo 964590 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B1448681 : Blo 964590 1448681 := bstep (se 2 (by rfl) ⟨543255, by rfl⟩ : syracuseStep 1448681 = 1086511) B1086511
theorem B1088455 : Blo 964590 1088455 := bstep (se 1 (by rfl) ⟨816341, by rfl⟩ : syracuseStep 1088455 = 1632683) B1632683
theorem B1448927 : Blo 964590 1448927 := bstep (se 1 (by rfl) ⟨1086695, by rfl⟩ : syracuseStep 1448927 = 2173391) B2173391
theorem B27860057 : Blo 964590 27860057 := bstep (se 2 (by rfl) ⟨10447521, by rfl⟩ : syracuseStep 27860057 = 20895043) B20895043
theorem B1088671 : Blo 964590 1088671 := bstep (se 1 (by rfl) ⟨816503, by rfl⟩ : syracuseStep 1088671 = 1633007) B1633007
theorem B13245805 : Blo 964590 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B2170745 : Blo 964590 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B1548391 : Blo 964590 1548391 := bstep (se 1 (by rfl) ⟨1161293, by rfl⟩ : syracuseStep 1548391 = 2322587) B2322587
theorem B1450175 : Blo 964590 1450175 := bstep (se 1 (by rfl) ⟨1087631, by rfl⟩ : syracuseStep 1450175 = 2175263) B2175263
theorem B8037467 : Blo 964590 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B1451135 : Blo 964590 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B2172239 : Blo 964590 2172239 := bstep (se 1 (by rfl) ⟨1629179, by rfl⟩ : syracuseStep 2172239 = 3258359) B3258359
theorem B2172923 : Blo 964590 2172923 := bstep (se 1 (by rfl) ⟨1629692, by rfl⟩ : syracuseStep 2172923 = 3259385) B3259385
theorem B2173103 : Blo 964590 2173103 := bstep (se 1 (by rfl) ⟨1629827, by rfl⟩ : syracuseStep 2173103 = 3259655) B3259655
theorem B4893047 : Blo 964590 4893047 := bstep (se 1 (by rfl) ⟨3669785, by rfl⟩ : syracuseStep 4893047 = 7339571) B7339571
theorem B7842907 : Blo 964590 7842907 := bstep (se 1 (by rfl) ⟨5882180, by rfl⟩ : syracuseStep 7842907 = 11764361) B11764361
theorem B31305197 : Blo 964590 31305197 := bstep (se 3 (by rfl) ⟨5869724, by rfl⟩ : syracuseStep 31305197 = 11739449) B11739449
theorem B16756669 : Blo 964590 16756669 := bstep (se 3 (by rfl) ⟨3141875, by rfl⟩ : syracuseStep 16756669 = 6283751) B6283751
theorem B14135471 : Blo 964590 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B2207935 : Blo 964590 2207935 := bstep (se 1 (by rfl) ⟨1655951, by rfl⟩ : syracuseStep 2207935 = 3311903) B3311903
theorem B2208703 : Blo 964590 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B2177351 : Blo 964590 2177351 := bstep (se 1 (by rfl) ⟨1633013, by rfl⟩ : syracuseStep 2177351 = 3266027) B3266027
theorem B965019 : Blo 964590 965019 := bstep (se 1 (by rfl) ⟨723764, by rfl⟩ : syracuseStep 965019 = 1447529) B1447529
theorem B3259115 : Blo 964590 3259115 := bstep (se 1 (by rfl) ⟨2444336, by rfl⟩ : syracuseStep 3259115 = 4888673) B4888673
theorem B68795191 : Blo 964590 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B965631 : Blo 964590 965631 := bstep (se 1 (by rfl) ⟨724223, by rfl⟩ : syracuseStep 965631 = 1448447) B1448447
theorem B965935 : Blo 964590 965935 := bstep (se 1 (by rfl) ⟨724451, by rfl⟩ : syracuseStep 965935 = 1448903) B1448903
theorem B2178395 : Blo 964590 2178395 := bstep (se 1 (by rfl) ⟨1633796, by rfl⟩ : syracuseStep 2178395 = 3267593) B3267593
theorem B3718781 : Blo 964590 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B966335 : Blo 964590 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B3260519 : Blo 964590 3260519 := bstep (se 1 (by rfl) ⟨2445389, by rfl⟩ : syracuseStep 3260519 = 4890779) B4890779
theorem B966879 : Blo 964590 966879 := bstep (se 1 (by rfl) ⟨725159, by rfl⟩ : syracuseStep 966879 = 1450319) B1450319
theorem B1032431 : Blo 964590 1032431 := bstep (se 1 (by rfl) ⟨774323, by rfl⟩ : syracuseStep 1032431 = 1548647) B1548647
theorem B967103 : Blo 964590 967103 := bstep (se 1 (by rfl) ⟨725327, by rfl⟩ : syracuseStep 967103 = 1450655) B1450655
theorem B967399 : Blo 964590 967399 := bstep (se 1 (by rfl) ⟨725549, by rfl⟩ : syracuseStep 967399 = 1451099) B1451099
theorem B8241983 : Blo 964590 8241983 := bstep (se 1 (by rfl) ⟨6181487, by rfl⟩ : syracuseStep 8241983 = 12362975) B12362975
theorem B968159 : Blo 964590 968159 := bstep (se 1 (by rfl) ⟨726119, by rfl⟩ : syracuseStep 968159 = 1452239) B1452239
theorem B968191 : Blo 964590 968191 := bstep (se 1 (by rfl) ⟨726143, by rfl⟩ : syracuseStep 968191 = 1452287) B1452287
theorem B968319 : Blo 964590 968319 := bstep (se 1 (by rfl) ⟨726239, by rfl⟩ : syracuseStep 968319 = 1452479) B1452479
theorem B10471049 : Blo 964590 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B16533719 : Blo 964590 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B2443547 : Blo 964590 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B2445167 : Blo 964590 2445167 := bstep (se 1 (by rfl) ⟨1833875, by rfl⟩ : syracuseStep 2445167 = 3667751) B3667751
theorem B3264623 : Blo 964590 3264623 := bstep (se 1 (by rfl) ⟨2448467, by rfl⟩ : syracuseStep 3264623 = 4896935) B4896935
theorem B17618471 : Blo 964590 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B5232239 : Blo 964590 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B2447567 : Blo 964590 2447567 := bstep (se 1 (by rfl) ⟨1835675, by rfl⟩ : syracuseStep 2447567 = 3671351) B3671351
theorem B1629119 : Blo 964590 1629119 := bstep (se 1 (by rfl) ⟨1221839, by rfl⟩ : syracuseStep 1629119 = 2443679) B2443679
theorem B2317751 : Blo 964590 2317751 := bstep (se 1 (by rfl) ⟨1738313, by rfl⟩ : syracuseStep 2317751 = 3476627) B3476627
theorem B1629679 : Blo 964590 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B7331795 : Blo 964590 7331795 := bstep (se 1 (by rfl) ⟨5498846, by rfl⟩ : syracuseStep 7331795 = 10997693) B10997693
theorem B3268943 : Blo 964590 3268943 := bstep (se 1 (by rfl) ⟨2451707, by rfl⟩ : syracuseStep 3268943 = 4903415) B4903415
theorem B20898425 : Blo 964590 20898425 := bstep (se 2 (by rfl) ⟨7836909, by rfl⟩ : syracuseStep 20898425 = 15673819) B15673819
theorem B2450047 : Blo 964590 2450047 := bstep (se 1 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 2450047 = 3675071) B3675071
theorem B3925415 : Blo 964590 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B4122359 : Blo 964590 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B1632575 : Blo 964590 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B11004983 : Blo 964590 11004983 := bstep (se 1 (by rfl) ⟨8253737, by rfl⟩ : syracuseStep 11004983 = 16507475) B16507475
theorem B31288589 : Blo 964590 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B7335683 : Blo 964590 7335683 := bstep (se 1 (by rfl) ⟨5501762, by rfl⟩ : syracuseStep 7335683 = 11003525) B11003525
theorem B16511849 : Blo 964590 16511849 := bstep (se 2 (by rfl) ⟨6191943, by rfl⟩ : syracuseStep 16511849 = 12383887) B12383887
theorem B2324047 : Blo 964590 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B6191329 : Blo 964590 6191329 := bstep (se 2 (by rfl) ⟨2321748, by rfl⟩ : syracuseStep 6191329 = 4643497) B4643497
theorem B9271583 : Blo 964590 9271583 := bstep (se 1 (by rfl) ⟨6953687, by rfl⟩ : syracuseStep 9271583 = 13907375) B13907375
theorem B11762131 : Blo 964590 11762131 := bstep (se 1 (by rfl) ⟨8821598, by rfl⟩ : syracuseStep 11762131 = 17643197) B17643197
theorem B362707793 : Blo 964590 362707793 := bstep (se 2 (by rfl) ⟨136015422, by rfl⟩ : syracuseStep 362707793 = 272030845) B272030845
theorem B10452023 : Blo 964590 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B2064521 : Blo 964590 2064521 := bstep (se 2 (by rfl) ⟨774195, by rfl⟩ : syracuseStep 2064521 = 1548391) B1548391
theorem B2753149 : Blo 964590 2753149 := bstep (se 3 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 2753149 = 1032431) B1032431
theorem B6980699 : Blo 964590 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B2754299 : Blo 964590 2754299 := bstep (se 1 (by rfl) ⟨2065724, by rfl⟩ : syracuseStep 2754299 = 4131449) B4131449
theorem B1379035 : Blo 964590 1379035 := bstep (se 1 (by rfl) ⟨1034276, by rfl⟩ : syracuseStep 1379035 = 2068553) B2068553
theorem B23792527 : Blo 964590 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B10457209 : Blo 964590 10457209 := bstep (se 2 (by rfl) ⟨3921453, by rfl⟩ : syracuseStep 10457209 = 7842907) B7842907
theorem B1086079 : Blo 964590 1086079 := bstep (se 1 (by rfl) ⟨814559, by rfl⟩ : syracuseStep 1086079 = 1629119) B1629119
theorem B1545167 : Blo 964590 1545167 := bstep (se 1 (by rfl) ⟨1158875, by rfl⟩ : syracuseStep 1545167 = 2317751) B2317751
theorem B1447163 : Blo 964590 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B4887863 : Blo 964590 4887863 := bstep (se 1 (by rfl) ⟨3665897, by rfl⟩ : syracuseStep 4887863 = 7331795) B7331795
theorem B13932283 : Blo 964590 13932283 := bstep (se 1 (by rfl) ⟨10449212, by rfl⟩ : syracuseStep 13932283 = 20898425) B20898425
theorem B1448159 : Blo 964590 1448159 := bstep (se 1 (by rfl) ⟨1086119, by rfl⟩ : syracuseStep 1448159 = 2172239) B2172239
theorem B1448615 : Blo 964590 1448615 := bstep (se 1 (by rfl) ⟨1086461, by rfl⟩ : syracuseStep 1448615 = 2172923) B2172923
theorem B1448735 : Blo 964590 1448735 := bstep (se 1 (by rfl) ⟨1086551, by rfl⟩ : syracuseStep 1448735 = 2173103) B2173103
theorem B1088383 : Blo 964590 1088383 := bstep (se 1 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 1088383 = 1632575) B1632575
theorem B4890455 : Blo 964590 4890455 := bstep (se 1 (by rfl) ⟨3667841, by rfl⟩ : syracuseStep 4890455 = 7335683) B7335683
theorem B91726921 : Blo 964590 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B1451273 : Blo 964590 1451273 := bstep (se 2 (by rfl) ⟨544227, by rfl⟩ : syracuseStep 1451273 = 1088455) B1088455
theorem B1451561 : Blo 964590 1451561 := bstep (se 2 (by rfl) ⟨544335, by rfl⟩ : syracuseStep 1451561 = 1088671) B1088671
theorem B1451567 : Blo 964590 1451567 := bstep (se 1 (by rfl) ⟨1088675, by rfl⟩ : syracuseStep 1451567 = 2177351) B2177351
theorem B2172743 : Blo 964590 2172743 := bstep (se 1 (by rfl) ⟨1629557, by rfl⟩ : syracuseStep 2172743 = 3259115) B3259115
theorem B241805195 : Blo 964590 241805195 := bstep (se 1 (by rfl) ⟨181353896, by rfl⟩ : syracuseStep 241805195 = 362707793) B362707793
theorem B2172905 : Blo 964590 2172905 := bstep (se 2 (by rfl) ⟨814839, by rfl⟩ : syracuseStep 2172905 = 1629679) B1629679
theorem B1452263 : Blo 964590 1452263 := bstep (se 1 (by rfl) ⟨1089197, by rfl⟩ : syracuseStep 1452263 = 2178395) B2178395
theorem B2173679 : Blo 964590 2173679 := bstep (se 1 (by rfl) ⟨1630259, by rfl⟩ : syracuseStep 2173679 = 3260519) B3260519
theorem B11022479 : Blo 964590 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B2176415 : Blo 964590 2176415 := bstep (se 1 (by rfl) ⟨1632311, by rfl⟩ : syracuseStep 2176415 = 3264623) B3264623
theorem B964935 : Blo 964590 964935 := bstep (se 1 (by rfl) ⟨723701, by rfl⟩ : syracuseStep 964935 = 1447403) B1447403
theorem B11745647 : Blo 964590 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B3488159 : Blo 964590 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B7256891 : Blo 964590 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B965787 : Blo 964590 965787 := bstep (se 1 (by rfl) ⟨724340, by rfl⟩ : syracuseStep 965787 = 1448681) B1448681
theorem B965951 : Blo 964590 965951 := bstep (se 1 (by rfl) ⟨724463, by rfl⟩ : syracuseStep 965951 = 1448927) B1448927
theorem B966783 : Blo 964590 966783 := bstep (se 1 (by rfl) ⟨725087, by rfl⟩ : syracuseStep 966783 = 1450175) B1450175
theorem B2179295 : Blo 964590 2179295 := bstep (se 1 (by rfl) ⟨1634471, by rfl⟩ : syracuseStep 2179295 = 3268943) B3268943
theorem B5358311 : Blo 964590 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B967423 : Blo 964590 967423 := bstep (se 1 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 967423 = 1451135) B1451135
theorem B3262031 : Blo 964590 3262031 := bstep (se 1 (by rfl) ⟨2446523, by rfl⟩ : syracuseStep 3262031 = 4893047) B4893047
theorem B3098729 : Blo 964590 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B20859059 : Blo 964590 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B9423647 : Blo 964590 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B15682841 : Blo 964590 15682841 := bstep (se 2 (by rfl) ⟨5881065, by rfl⟩ : syracuseStep 15682841 = 11762131) B11762131
theorem B6181055 : Blo 964590 6181055 := bstep (se 1 (by rfl) ⟨4635791, by rfl⟩ : syracuseStep 6181055 = 9271583) B9271583
theorem B6968015 : Blo 964590 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B2479187 : Blo 964590 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B2447131 : Blo 964590 2447131 := bstep (se 1 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 2447131 = 3670697) B3670697
theorem B5494655 : Blo 964590 5494655 := bstep (se 1 (by rfl) ⟨4120991, by rfl⟩ : syracuseStep 5494655 = 8241983) B8241983
theorem B3266729 : Blo 964590 3266729 := bstep (se 2 (by rfl) ⟨1225023, by rfl⟩ : syracuseStep 3266729 = 2450047) B2450047
theorem B2448103 : Blo 964590 2448103 := bstep (se 1 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 2448103 = 3672155) B3672155
theorem B1629031 : Blo 964590 1629031 := bstep (se 1 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 1629031 = 2443547) B2443547
theorem B19094561 : Blo 964590 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B1630111 : Blo 964590 1630111 := bstep (se 1 (by rfl) ⟨1222583, by rfl⟩ : syracuseStep 1630111 = 2445167) B2445167
theorem B2449703 : Blo 964590 2449703 := bstep (se 1 (by rfl) ⟨1837277, by rfl⟩ : syracuseStep 2449703 = 3674555) B3674555
theorem B1631711 : Blo 964590 1631711 := bstep (se 1 (by rfl) ⟨1223783, by rfl⟩ : syracuseStep 1631711 = 2447567) B2447567
theorem B18573371 : Blo 964590 18573371 := bstep (se 1 (by rfl) ⟨13930028, by rfl⟩ : syracuseStep 18573371 = 27860057) B27860057
theorem B22342225 : Blo 964590 22342225 := bstep (se 2 (by rfl) ⟨8378334, by rfl⟩ : syracuseStep 22342225 = 16756669) B16756669
theorem B2943913 : Blo 964590 2943913 := bstep (se 2 (by rfl) ⟨1103967, by rfl⟩ : syracuseStep 2943913 = 2207935) B2207935
theorem B2616943 : Blo 964590 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B2748239 : Blo 964590 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B2944937 : Blo 964590 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B7336655 : Blo 964590 7336655 := bstep (se 1 (by rfl) ⟨5502491, by rfl⟩ : syracuseStep 7336655 = 11004983) B11004983
theorem B20870131 : Blo 964590 20870131 := bstep (se 1 (by rfl) ⟨15652598, by rfl⟩ : syracuseStep 20870131 = 31305197) B31305197
theorem B8255105 : Blo 964590 8255105 := bstep (se 2 (by rfl) ⟨3095664, by rfl⟩ : syracuseStep 8255105 = 6191329) B6191329
theorem B11007899 : Blo 964590 11007899 := bstep (se 1 (by rfl) ⟨8255924, by rfl⟩ : syracuseStep 11007899 = 16511849) B16511849
theorem B17661073 : Blo 964590 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B1376347 : Blo 964590 1376347 := bstep (se 1 (by rfl) ⟨1032260, by rfl⟩ : syracuseStep 1376347 = 2064521) B2064521
theorem B3572207 : Blo 964590 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B3670865 : Blo 964590 3670865 := bstep (se 2 (by rfl) ⟨1376574, by rfl⟩ : syracuseStep 3670865 = 2753149) B2753149
theorem B1836199 : Blo 964590 1836199 := bstep (se 1 (by rfl) ⟨1377149, by rfl⟩ : syracuseStep 1836199 = 2754299) B2754299
theorem B2065819 : Blo 964590 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B10455227 : Blo 964590 10455227 := bstep (se 1 (by rfl) ⟨7841420, by rfl⟩ : syracuseStep 10455227 = 15682841) B15682841
theorem B18615197 : Blo 964590 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B29789633 : Blo 964590 29789633 := bstep (se 2 (by rfl) ⟨11171112, by rfl⟩ : syracuseStep 29789633 = 22342225) B22342225
theorem B1838713 : Blo 964590 1838713 := bstep (se 2 (by rfl) ⟨689517, by rfl⟩ : syracuseStep 1838713 = 1379035) B1379035
theorem B31723369 : Blo 964590 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B1448105 : Blo 964590 1448105 := bstep (se 2 (by rfl) ⟨543039, by rfl⟩ : syracuseStep 1448105 = 1086079) B1086079
theorem B1087807 : Blo 964590 1087807 := bstep (se 1 (by rfl) ⟨815855, by rfl⟩ : syracuseStep 1087807 = 1631711) B1631711
theorem B1448495 : Blo 964590 1448495 := bstep (se 1 (by rfl) ⟨1086371, by rfl⟩ : syracuseStep 1448495 = 2172743) B2172743
theorem B27826841 : Blo 964590 27826841 := bstep (se 2 (by rfl) ⟨10435065, by rfl⟩ : syracuseStep 27826841 = 20870131) B20870131
theorem B1448603 : Blo 964590 1448603 := bstep (se 1 (by rfl) ⟨1086452, by rfl⟩ : syracuseStep 1448603 = 2172905) B2172905
theorem B1449119 : Blo 964590 1449119 := bstep (se 1 (by rfl) ⟨1086839, by rfl⟩ : syracuseStep 1449119 = 2173679) B2173679
theorem B7348319 : Blo 964590 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B4891103 : Blo 964590 4891103 := bstep (se 1 (by rfl) ⟨3668327, by rfl⟩ : syracuseStep 4891103 = 7336655) B7336655
theorem B1450943 : Blo 964590 1450943 := bstep (se 1 (by rfl) ⟨1088207, by rfl⟩ : syracuseStep 1450943 = 2176415) B2176415
theorem B2172041 : Blo 964590 2172041 := bstep (se 2 (by rfl) ⟨814515, by rfl⟩ : syracuseStep 2172041 = 1629031) B1629031
theorem B1451177 : Blo 964590 1451177 := bstep (se 2 (by rfl) ⟨544191, by rfl⟩ : syracuseStep 1451177 = 1088383) B1088383
theorem B2173481 : Blo 964590 2173481 := bstep (se 2 (by rfl) ⟨815055, by rfl⟩ : syracuseStep 2173481 = 1630111) B1630111
theorem B1452863 : Blo 964590 1452863 := bstep (se 1 (by rfl) ⟨1089647, by rfl⟩ : syracuseStep 1452863 = 2179295) B2179295
theorem B2174687 : Blo 964590 2174687 := bstep (se 1 (by rfl) ⟨1631015, by rfl⟩ : syracuseStep 2174687 = 3262031) B3262031
theorem B122302561 : Blo 964590 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B964775 : Blo 964590 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B3258575 : Blo 964590 3258575 := bstep (se 1 (by rfl) ⟨2443931, by rfl⟩ : syracuseStep 3258575 = 4887863) B4887863
theorem B2177819 : Blo 964590 2177819 := bstep (se 1 (by rfl) ⟨1633364, by rfl⟩ : syracuseStep 2177819 = 3266729) B3266729
theorem B965439 : Blo 964590 965439 := bstep (se 1 (by rfl) ⟨724079, by rfl⟩ : syracuseStep 965439 = 1448159) B1448159
theorem B965743 : Blo 964590 965743 := bstep (se 1 (by rfl) ⟨724307, by rfl⟩ : syracuseStep 965743 = 1448615) B1448615
theorem B965823 : Blo 964590 965823 := bstep (se 1 (by rfl) ⟨724367, by rfl⟩ : syracuseStep 965823 = 1448735) B1448735
theorem B12729707 : Blo 964590 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B3489257 : Blo 964590 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B3260303 : Blo 964590 3260303 := bstep (se 1 (by rfl) ⟨2445227, by rfl⟩ : syracuseStep 3260303 = 4890455) B4890455
theorem B13942945 : Blo 964590 13942945 := bstep (se 2 (by rfl) ⟨5228604, by rfl⟩ : syracuseStep 13942945 = 10457209) B10457209
theorem B55624157 : Blo 964590 55624157 := bstep (se 3 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 55624157 = 20859059) B20859059
theorem B967515 : Blo 964590 967515 := bstep (se 1 (by rfl) ⟨725636, by rfl⟩ : syracuseStep 967515 = 1451273) B1451273
theorem B967707 : Blo 964590 967707 := bstep (se 1 (by rfl) ⟨725780, by rfl⟩ : syracuseStep 967707 = 1451561) B1451561
theorem B967711 : Blo 964590 967711 := bstep (se 1 (by rfl) ⟨725783, by rfl⟩ : syracuseStep 967711 = 1451567) B1451567
theorem B161203463 : Blo 964590 161203463 := bstep (se 1 (by rfl) ⟨120902597, by rfl⟩ : syracuseStep 161203463 = 241805195) B241805195
theorem B968175 : Blo 964590 968175 := bstep (se 1 (by rfl) ⟨726131, by rfl⟩ : syracuseStep 968175 = 1452263) B1452263
theorem B3262841 : Blo 964590 3262841 := bstep (se 2 (by rfl) ⟨1223565, by rfl⟩ : syracuseStep 3262841 = 2447131) B2447131
theorem B3264137 : Blo 964590 3264137 := bstep (se 2 (by rfl) ⟨1224051, by rfl⟩ : syracuseStep 3264137 = 2448103) B2448103
theorem B23548097 : Blo 964590 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B4837927 : Blo 964590 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B6282431 : Blo 964590 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B4120445 : Blo 964590 4120445 := bstep (se 3 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 4120445 = 1545167) B1545167
theorem B4120703 : Blo 964590 4120703 := bstep (se 1 (by rfl) ⟨3090527, by rfl⟩ : syracuseStep 4120703 = 6181055) B6181055
theorem B6611165 : Blo 964590 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B4645343 : Blo 964590 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B3925217 : Blo 964590 3925217 := bstep (se 2 (by rfl) ⟨1471956, by rfl⟩ : syracuseStep 3925217 = 2943913) B2943913
theorem B3663103 : Blo 964590 3663103 := bstep (se 1 (by rfl) ⟨2747327, by rfl⟩ : syracuseStep 3663103 = 5494655) B5494655
theorem B1633135 : Blo 964590 1633135 := bstep (se 1 (by rfl) ⟨1224851, by rfl⟩ : syracuseStep 1633135 = 2449703) B2449703
theorem B12382247 : Blo 964590 12382247 := bstep (se 1 (by rfl) ⟨9286685, by rfl⟩ : syracuseStep 12382247 = 18573371) B18573371
theorem B18576377 : Blo 964590 18576377 := bstep (se 2 (by rfl) ⟨6966141, by rfl⟩ : syracuseStep 18576377 = 13932283) B13932283
theorem B1832159 : Blo 964590 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B1963291 : Blo 964590 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B5503403 : Blo 964590 5503403 := bstep (se 1 (by rfl) ⟨4127552, by rfl⟩ : syracuseStep 5503403 = 8255105) B8255105
theorem B7338599 : Blo 964590 7338599 := bstep (se 1 (by rfl) ⟨5503949, by rfl⟩ : syracuseStep 7338599 = 11007899) B11007899
theorem B7830431 : Blo 964590 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B2325439 : Blo 964590 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B1835129 : Blo 964590 1835129 := bstep (se 2 (by rfl) ⟨688173, by rfl⟩ : syracuseStep 1835129 = 1376347) B1376347
theorem B4884137 : Blo 964590 4884137 := bstep (se 2 (by rfl) ⟨1831551, by rfl⟩ : syracuseStep 4884137 = 3663103) B3663103
theorem B2754425 : Blo 964590 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B19859755 : Blo 964590 19859755 := bstep (se 1 (by rfl) ⟨14894816, by rfl⟩ : syracuseStep 19859755 = 29789633) B29789633
theorem B15698731 : Blo 964590 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B4885757 : Blo 964590 4885757 := bstep (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) B1832159
theorem B18551227 : Blo 964590 18551227 := bstep (se 1 (by rfl) ⟨13913420, by rfl⟩ : syracuseStep 18551227 = 27826841) B27826841
theorem B1448027 : Blo 964590 1448027 := bstep (se 1 (by rfl) ⟨1086020, by rfl⟩ : syracuseStep 1448027 = 2172041) B2172041
theorem B1448987 : Blo 964590 1448987 := bstep (se 1 (by rfl) ⟨1086740, by rfl⟩ : syracuseStep 1448987 = 2173481) B2173481
theorem B676765205 : Blo 964590 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B1449791 : Blo 964590 1449791 := bstep (se 1 (by rfl) ⟨1087343, by rfl⟩ : syracuseStep 1449791 = 2174687) B2174687
theorem B1450409 : Blo 964590 1450409 := bstep (se 2 (by rfl) ⟨543903, by rfl⟩ : syracuseStep 1450409 = 1087807) B1087807
theorem B2172383 : Blo 964590 2172383 := bstep (se 1 (by rfl) ⟨1629287, by rfl⟩ : syracuseStep 2172383 = 3258575) B3258575
theorem B4892399 : Blo 964590 4892399 := bstep (se 1 (by rfl) ⟨3669299, by rfl⟩ : syracuseStep 4892399 = 7338599) B7338599
theorem B1451879 : Blo 964590 1451879 := bstep (se 1 (by rfl) ⟨1088909, by rfl⟩ : syracuseStep 1451879 = 2177819) B2177819
theorem B5220287 : Blo 964590 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B2173535 : Blo 964590 2173535 := bstep (se 1 (by rfl) ⟨1630151, by rfl⟩ : syracuseStep 2173535 = 3260303) B3260303
theorem B18590593 : Blo 964590 18590593 := bstep (se 2 (by rfl) ⟨6971472, by rfl⟩ : syracuseStep 18590593 = 13942945) B13942945
theorem B2175227 : Blo 964590 2175227 := bstep (se 1 (by rfl) ⟨1631420, by rfl⟩ : syracuseStep 2175227 = 3262841) B3262841
theorem B2176091 : Blo 964590 2176091 := bstep (se 1 (by rfl) ⟨1632068, by rfl⟩ : syracuseStep 2176091 = 3264137) B3264137
theorem B10467245 : Blo 964590 10467245 := bstep (se 3 (by rfl) ⟨1962608, by rfl⟩ : syracuseStep 10467245 = 3925217) B3925217
theorem B2177513 : Blo 964590 2177513 := bstep (se 2 (by rfl) ⟨816567, by rfl⟩ : syracuseStep 2177513 = 1633135) B1633135
theorem B965403 : Blo 964590 965403 := bstep (se 1 (by rfl) ⟨724052, by rfl⟩ : syracuseStep 965403 = 1448105) B1448105
theorem B965663 : Blo 964590 965663 := bstep (se 1 (by rfl) ⟨724247, by rfl⟩ : syracuseStep 965663 = 1448495) B1448495
theorem B965735 : Blo 964590 965735 := bstep (se 1 (by rfl) ⟨724301, by rfl⟩ : syracuseStep 965735 = 1448603) B1448603
theorem B966079 : Blo 964590 966079 := bstep (se 1 (by rfl) ⟨724559, by rfl⟩ : syracuseStep 966079 = 1449119) B1449119
theorem B12402341 : Blo 964590 12402341 := bstep (se 4 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 12402341 = 2325439) B2325439
theorem B4898879 : Blo 964590 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B163070081 : Blo 964590 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B4407443 : Blo 964590 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B3260735 : Blo 964590 3260735 := bstep (se 1 (by rfl) ⟨2445551, by rfl⟩ : syracuseStep 3260735 = 4891103) B4891103
theorem B3096895 : Blo 964590 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B967295 : Blo 964590 967295 := bstep (se 1 (by rfl) ⟨725471, by rfl⟩ : syracuseStep 967295 = 1450943) B1450943
theorem B967451 : Blo 964590 967451 := bstep (se 1 (by rfl) ⟨725588, by rfl⟩ : syracuseStep 967451 = 1451177) B1451177
theorem B968575 : Blo 964590 968575 := bstep (se 1 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 968575 = 1452863) B1452863
theorem B37082771 : Blo 964590 37082771 := bstep (se 1 (by rfl) ⟨27812078, by rfl⟩ : syracuseStep 37082771 = 55624157) B55624157
theorem B2381471 : Blo 964590 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B2447243 : Blo 964590 2447243 := bstep (se 1 (by rfl) ⟨1835432, by rfl⟩ : syracuseStep 2447243 = 3670865) B3670865
theorem B107468975 : Blo 964590 107468975 := bstep (se 1 (by rfl) ⟨80601731, by rfl⟩ : syracuseStep 107468975 = 161203463) B161203463
theorem B6970151 : Blo 964590 6970151 := bstep (se 1 (by rfl) ⟨5227613, by rfl⟩ : syracuseStep 6970151 = 10455227) B10455227
theorem B2448265 : Blo 964590 2448265 := bstep (se 2 (by rfl) ⟨918099, by rfl⟩ : syracuseStep 2448265 = 1836199) B1836199
theorem B12410131 : Blo 964590 12410131 := bstep (se 1 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 12410131 = 18615197) B18615197
theorem B4188287 : Blo 964590 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B2451617 : Blo 964590 2451617 := bstep (se 2 (by rfl) ⟨919356, by rfl⟩ : syracuseStep 2451617 = 1838713) B1838713
theorem B2746963 : Blo 964590 2746963 := bstep (se 1 (by rfl) ⟨2060222, by rfl⟩ : syracuseStep 2746963 = 4120445) B4120445
theorem B2747135 : Blo 964590 2747135 := bstep (se 1 (by rfl) ⟨2060351, by rfl⟩ : syracuseStep 2747135 = 4120703) B4120703
theorem B6450569 : Blo 964590 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B2617721 : Blo 964590 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B8254831 : Blo 964590 8254831 := bstep (se 1 (by rfl) ⟨6191123, by rfl⟩ : syracuseStep 8254831 = 12382247) B12382247
theorem B12384251 : Blo 964590 12384251 := bstep (se 1 (by rfl) ⟨9288188, by rfl⟩ : syracuseStep 12384251 = 18576377) B18576377
theorem B3668935 : Blo 964590 3668935 := bstep (se 1 (by rfl) ⟨2751701, by rfl⟩ : syracuseStep 3668935 = 5503403) B5503403
theorem B8486471 : Blo 964590 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B2326171 : Blo 964590 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B4129193 : Blo 964590 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B1836283 : Blo 964590 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B26479673 : Blo 964590 26479673 := bstep (se 2 (by rfl) ⟨9929877, by rfl⟩ : syracuseStep 26479673 = 19859755) B19859755
theorem B1448255 : Blo 964590 1448255 := bstep (se 1 (by rfl) ⟨1086191, by rfl⟩ : syracuseStep 1448255 = 2172383) B2172383
theorem B3480191 : Blo 964590 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B1449023 : Blo 964590 1449023 := bstep (se 1 (by rfl) ⟨1086767, by rfl⟩ : syracuseStep 1449023 = 2173535) B2173535
theorem B4300379 : Blo 964590 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B1450151 : Blo 964590 1450151 := bstep (se 1 (by rfl) ⟨1087613, by rfl⟩ : syracuseStep 1450151 = 2175227) B2175227
theorem B1745147 : Blo 964590 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B1450727 : Blo 964590 1450727 := bstep (se 1 (by rfl) ⟨1088045, by rfl⟩ : syracuseStep 1450727 = 2176091) B2176091
theorem B4891913 : Blo 964590 4891913 := bstep (se 2 (by rfl) ⟨1834467, by rfl⟩ : syracuseStep 4891913 = 3668935) B3668935
theorem B1451675 : Blo 964590 1451675 := bstep (se 1 (by rfl) ⟨1088756, by rfl⟩ : syracuseStep 1451675 = 2177513) B2177513
theorem B8268227 : Blo 964590 8268227 := bstep (se 1 (by rfl) ⟨6201170, by rfl⟩ : syracuseStep 8268227 = 12402341) B12402341
theorem B1223419 : Blo 964590 1223419 := bstep (se 1 (by rfl) ⟨917564, by rfl⟩ : syracuseStep 1223419 = 1835129) B1835129
theorem B2173823 : Blo 964590 2173823 := bstep (se 1 (by rfl) ⟨1630367, by rfl⟩ : syracuseStep 2173823 = 3260735) B3260735
theorem B3256091 : Blo 964590 3256091 := bstep (se 1 (by rfl) ⟨2442068, by rfl⟩ : syracuseStep 3256091 = 4884137) B4884137
theorem B3257171 : Blo 964590 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B24721847 : Blo 964590 24721847 := bstep (se 1 (by rfl) ⟨18541385, by rfl⟩ : syracuseStep 24721847 = 37082771) B37082771
theorem B1587647 : Blo 964590 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B24787457 : Blo 964590 24787457 := bstep (se 2 (by rfl) ⟨9295296, by rfl⟩ : syracuseStep 24787457 = 18590593) B18590593
theorem B965351 : Blo 964590 965351 := bstep (se 1 (by rfl) ⟨724013, by rfl⟩ : syracuseStep 965351 = 1448027) B1448027
theorem B965991 : Blo 964590 965991 := bstep (se 1 (by rfl) ⟨724493, by rfl⟩ : syracuseStep 965991 = 1448987) B1448987
theorem B966527 : Blo 964590 966527 := bstep (se 1 (by rfl) ⟨724895, by rfl⟩ : syracuseStep 966527 = 1449791) B1449791
theorem B966939 : Blo 964590 966939 := bstep (se 1 (by rfl) ⟨725204, by rfl⟩ : syracuseStep 966939 = 1450409) B1450409
theorem B3261599 : Blo 964590 3261599 := bstep (se 1 (by rfl) ⟨2446199, by rfl⟩ : syracuseStep 3261599 = 4892399) B4892399
theorem B967919 : Blo 964590 967919 := bstep (se 1 (by rfl) ⟨725939, by rfl⟩ : syracuseStep 967919 = 1451879) B1451879
theorem B3264353 : Blo 964590 3264353 := bstep (se 2 (by rfl) ⟨1224132, by rfl⟩ : syracuseStep 3264353 = 2448265) B2448265
theorem B3101561 : Blo 964590 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B5657647 : Blo 964590 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B3265919 : Blo 964590 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B108713387 : Blo 964590 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B2938295 : Blo 964590 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B3662617 : Blo 964590 3662617 := bstep (se 2 (by rfl) ⟨1373481, by rfl⟩ : syracuseStep 3662617 = 2746963) B2746963
theorem B20931641 : Blo 964590 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B1631495 : Blo 964590 1631495 := bstep (se 1 (by rfl) ⟨1223621, by rfl⟩ : syracuseStep 1631495 = 2447243) B2447243
theorem B4646767 : Blo 964590 4646767 := bstep (se 1 (by rfl) ⟨3485075, by rfl⟩ : syracuseStep 4646767 = 6970151) B6970151
theorem B451176803 : Blo 964590 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B11168765 : Blo 964590 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B286583933 : Blo 964590 286583933 := bstep (se 3 (by rfl) ⟨53734487, by rfl⟩ : syracuseStep 286583933 = 107468975) B107468975
theorem B24734969 : Blo 964590 24734969 := bstep (se 2 (by rfl) ⟨9275613, by rfl⟩ : syracuseStep 24734969 = 18551227) B18551227
theorem B1634411 : Blo 964590 1634411 := bstep (se 1 (by rfl) ⟨1225808, by rfl⟩ : syracuseStep 1634411 = 2451617) B2451617
theorem B11006441 : Blo 964590 11006441 := bstep (se 2 (by rfl) ⟨4127415, by rfl⟩ : syracuseStep 11006441 = 8254831) B8254831
theorem B1831423 : Blo 964590 1831423 := bstep (se 1 (by rfl) ⟨1373567, by rfl⟩ : syracuseStep 1831423 = 2747135) B2747135
theorem B6978163 : Blo 964590 6978163 := bstep (se 1 (by rfl) ⟨5233622, by rfl⟩ : syracuseStep 6978163 = 10467245) B10467245
theorem B8256167 : Blo 964590 8256167 := bstep (se 1 (by rfl) ⟨6192125, by rfl⟩ : syracuseStep 8256167 = 12384251) B12384251
theorem B16546841 : Blo 964590 16546841 := bstep (se 2 (by rfl) ⟨6205065, by rfl⟩ : syracuseStep 16546841 = 12410131) B12410131
theorem B2752795 : Blo 964590 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B4883489 : Blo 964590 4883489 := bstep (se 2 (by rfl) ⟨1831308, by rfl⟩ : syracuseStep 4883489 = 3662617) B3662617
theorem B6195689 : Blo 964590 6195689 := bstep (se 2 (by rfl) ⟨2323383, by rfl⟩ : syracuseStep 6195689 = 4646767) B4646767
theorem B2067707 : Blo 964590 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B289902365 : Blo 964590 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B7835453 : Blo 964590 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B1087663 : Blo 964590 1087663 := bstep (se 1 (by rfl) ⟨815747, by rfl⟩ : syracuseStep 1087663 = 1631495) B1631495
theorem B4233725 : Blo 964590 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B7543529 : Blo 964590 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B300784535 : Blo 964590 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B5512151 : Blo 964590 5512151 := bstep (se 1 (by rfl) ⟨4134113, by rfl⟩ : syracuseStep 5512151 = 8268227) B8268227
theorem B1449215 : Blo 964590 1449215 := bstep (se 1 (by rfl) ⟨1086911, by rfl⟩ : syracuseStep 1449215 = 2173823) B2173823
theorem B7445843 : Blo 964590 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B16489979 : Blo 964590 16489979 := bstep (se 1 (by rfl) ⟨12367484, by rfl⟩ : syracuseStep 16489979 = 24734969) B24734969
theorem B2170727 : Blo 964590 2170727 := bstep (se 1 (by rfl) ⟨1628045, by rfl⟩ : syracuseStep 2170727 = 3256091) B3256091
theorem B1089607 : Blo 964590 1089607 := bstep (se 1 (by rfl) ⟨817205, by rfl⟩ : syracuseStep 1089607 = 1634411) B1634411
theorem B2171447 : Blo 964590 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B16524971 : Blo 964590 16524971 := bstep (se 1 (by rfl) ⟨12393728, by rfl⟩ : syracuseStep 16524971 = 24787457) B24787457
theorem B2174399 : Blo 964590 2174399 := bstep (se 1 (by rfl) ⟨1630799, by rfl⟩ : syracuseStep 2174399 = 3261599) B3261599
theorem B2176235 : Blo 964590 2176235 := bstep (se 1 (by rfl) ⟨1632176, by rfl⟩ : syracuseStep 2176235 = 3264353) B3264353
theorem B2177279 : Blo 964590 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B965503 : Blo 964590 965503 := bstep (se 1 (by rfl) ⟨724127, by rfl⟩ : syracuseStep 965503 = 1448255) B1448255
theorem B966015 : Blo 964590 966015 := bstep (se 1 (by rfl) ⟨724511, by rfl⟩ : syracuseStep 966015 = 1449023) B1449023
theorem B2866919 : Blo 964590 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B966767 : Blo 964590 966767 := bstep (se 1 (by rfl) ⟨725075, by rfl⟩ : syracuseStep 966767 = 1450151) B1450151
theorem B1163431 : Blo 964590 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B967151 : Blo 964590 967151 := bstep (se 1 (by rfl) ⟨725363, by rfl⟩ : syracuseStep 967151 = 1450727) B1450727
theorem B2441897 : Blo 964590 2441897 := bstep (se 2 (by rfl) ⟨915711, by rfl⟩ : syracuseStep 2441897 = 1831423) B1831423
theorem B3261275 : Blo 964590 3261275 := bstep (se 1 (by rfl) ⟨2445956, by rfl⟩ : syracuseStep 3261275 = 4891913) B4891913
theorem B967783 : Blo 964590 967783 := bstep (se 1 (by rfl) ⟨725837, by rfl⟩ : syracuseStep 967783 = 1451675) B1451675
theorem B191055955 : Blo 964590 191055955 := bstep (se 1 (by rfl) ⟨143291966, by rfl⟩ : syracuseStep 191055955 = 286583933) B286583933
theorem B11031227 : Blo 964590 11031227 := bstep (se 1 (by rfl) ⟨8273420, by rfl⟩ : syracuseStep 11031227 = 16546841) B16546841
theorem B2448377 : Blo 964590 2448377 := bstep (se 2 (by rfl) ⟨918141, by rfl⟩ : syracuseStep 2448377 = 1836283) B1836283
theorem B17653115 : Blo 964590 17653115 := bstep (se 1 (by rfl) ⟨13239836, by rfl⟩ : syracuseStep 17653115 = 26479673) B26479673
theorem B1631225 : Blo 964590 1631225 := bstep (se 2 (by rfl) ⟨611709, by rfl⟩ : syracuseStep 1631225 = 1223419) B1223419
theorem B2320127 : Blo 964590 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B13954427 : Blo 964590 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B7337627 : Blo 964590 7337627 := bstep (se 1 (by rfl) ⟨5503220, by rfl⟩ : syracuseStep 7337627 = 11006441) B11006441
theorem B9304217 : Blo 964590 9304217 := bstep (se 2 (by rfl) ⟨3489081, by rfl⟩ : syracuseStep 9304217 = 6978163) B6978163
theorem B16481231 : Blo 964590 16481231 := bstep (se 1 (by rfl) ⟨12360923, by rfl⟩ : syracuseStep 16481231 = 24721847) B24721847
theorem B5504111 : Blo 964590 5504111 := bstep (se 1 (by rfl) ⟨4128083, by rfl⟩ : syracuseStep 5504111 = 8256167) B8256167
theorem B3670393 : Blo 964590 3670393 := bstep (se 2 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 3670393 = 2752795) B2752795
theorem B4130459 : Blo 964590 4130459 := bstep (se 1 (by rfl) ⟨3097844, by rfl⟩ : syracuseStep 4130459 = 6195689) B6195689
theorem B1378471 : Blo 964590 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B193268243 : Blo 964590 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B254741273 : Blo 964590 254741273 := bstep (se 2 (by rfl) ⟨95527977, by rfl⟩ : syracuseStep 254741273 = 191055955) B191055955
theorem B2822483 : Blo 964590 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B3674767 : Blo 964590 3674767 := bstep (se 1 (by rfl) ⟨2756075, by rfl⟩ : syracuseStep 3674767 = 5512151) B5512151
theorem B11768743 : Blo 964590 11768743 := bstep (se 1 (by rfl) ⟨8826557, by rfl⟩ : syracuseStep 11768743 = 17653115) B17653115
theorem B1447151 : Blo 964590 1447151 := bstep (se 1 (by rfl) ⟨1085363, by rfl⟩ : syracuseStep 1447151 = 2170727) B2170727
theorem B1447631 : Blo 964590 1447631 := bstep (se 1 (by rfl) ⟨1085723, by rfl⟩ : syracuseStep 1447631 = 2171447) B2171447
theorem B1087483 : Blo 964590 1087483 := bstep (se 1 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 1087483 = 1631225) B1631225
theorem B11016647 : Blo 964590 11016647 := bstep (se 1 (by rfl) ⟨8262485, by rfl⟩ : syracuseStep 11016647 = 16524971) B16524971
theorem B1546751 : Blo 964590 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B1449599 : Blo 964590 1449599 := bstep (se 1 (by rfl) ⟨1087199, by rfl⟩ : syracuseStep 1449599 = 2174399) B2174399
theorem B1450217 : Blo 964590 1450217 := bstep (se 2 (by rfl) ⟨543831, by rfl⟩ : syracuseStep 1450217 = 1087663) B1087663
theorem B1450823 : Blo 964590 1450823 := bstep (se 1 (by rfl) ⟨1088117, by rfl⟩ : syracuseStep 1450823 = 2176235) B2176235
theorem B4891751 : Blo 964590 4891751 := bstep (se 1 (by rfl) ⟨3668813, by rfl⟩ : syracuseStep 4891751 = 7337627) B7337627
theorem B6202811 : Blo 964590 6202811 := bstep (se 1 (by rfl) ⟨4652108, by rfl⟩ : syracuseStep 6202811 = 9304217) B9304217
theorem B1451519 : Blo 964590 1451519 := bstep (se 1 (by rfl) ⟨1088639, by rfl⟩ : syracuseStep 1451519 = 2177279) B2177279
theorem B7645117 : Blo 964590 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B10987487 : Blo 964590 10987487 := bstep (se 1 (by rfl) ⟨8240615, by rfl⟩ : syracuseStep 10987487 = 16481231) B16481231
theorem B1452809 : Blo 964590 1452809 := bstep (se 2 (by rfl) ⟨544803, by rfl⟩ : syracuseStep 1452809 = 1089607) B1089607
theorem B1551241 : Blo 964590 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B2174183 : Blo 964590 2174183 := bstep (se 1 (by rfl) ⟨1630637, by rfl⟩ : syracuseStep 2174183 = 3261275) B3261275
theorem B3255659 : Blo 964590 3255659 := bstep (se 1 (by rfl) ⟨2441744, by rfl⟩ : syracuseStep 3255659 = 4883489) B4883489
theorem B5223635 : Blo 964590 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B7354151 : Blo 964590 7354151 := bstep (se 1 (by rfl) ⟨5515613, by rfl⟩ : syracuseStep 7354151 = 11031227) B11031227
theorem B5029019 : Blo 964590 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B200523023 : Blo 964590 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B966143 : Blo 964590 966143 := bstep (se 1 (by rfl) ⟨724607, by rfl⟩ : syracuseStep 966143 = 1449215) B1449215
theorem B4963895 : Blo 964590 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B10993319 : Blo 964590 10993319 := bstep (se 1 (by rfl) ⟨8244989, by rfl⟩ : syracuseStep 10993319 = 16489979) B16489979
theorem B1627931 : Blo 964590 1627931 := bstep (se 1 (by rfl) ⟨1220948, by rfl⟩ : syracuseStep 1627931 = 2441897) B2441897
theorem B1632251 : Blo 964590 1632251 := bstep (se 1 (by rfl) ⟨1224188, by rfl⟩ : syracuseStep 1632251 = 2448377) B2448377
theorem B9302951 : Blo 964590 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B3669407 : Blo 964590 3669407 := bstep (se 1 (by rfl) ⟨2752055, by rfl⟩ : syracuseStep 3669407 = 5504111) B5504111
theorem B2753639 : Blo 964590 2753639 := bstep (se 1 (by rfl) ⟨2065229, by rfl⟩ : syracuseStep 2753639 = 4130459) B4130459
theorem B128845495 : Blo 964590 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B10193489 : Blo 964590 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B1837961 : Blo 964590 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B1085287 : Blo 964590 1085287 := bstep (se 1 (by rfl) ⟨813965, by rfl⟩ : syracuseStep 1085287 = 1627931) B1627931
theorem B7344431 : Blo 964590 7344431 := bstep (se 1 (by rfl) ⟨5508323, by rfl⟩ : syracuseStep 7344431 = 11016647) B11016647
theorem B4135207 : Blo 964590 4135207 := bstep (se 1 (by rfl) ⟨3101405, by rfl⟩ : syracuseStep 4135207 = 6202811) B6202811
theorem B1088167 : Blo 964590 1088167 := bstep (se 1 (by rfl) ⟨816125, by rfl⟩ : syracuseStep 1088167 = 1632251) B1632251
theorem B1449455 : Blo 964590 1449455 := bstep (se 1 (by rfl) ⟨1087091, by rfl⟩ : syracuseStep 1449455 = 2174183) B2174183
theorem B2170439 : Blo 964590 2170439 := bstep (se 1 (by rfl) ⟨1627829, by rfl⟩ : syracuseStep 2170439 = 3255659) B3255659
theorem B1449977 : Blo 964590 1449977 := bstep (se 2 (by rfl) ⟨543741, by rfl⟩ : syracuseStep 1449977 = 1087483) B1087483
theorem B6201967 : Blo 964590 6201967 := bstep (se 1 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 6201967 = 9302951) B9302951
theorem B3482423 : Blo 964590 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B3352679 : Blo 964590 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B4893857 : Blo 964590 4893857 := bstep (se 2 (by rfl) ⟨1835196, by rfl⟩ : syracuseStep 4893857 = 3670393) B3670393
theorem B964767 : Blo 964590 964767 := bstep (se 1 (by rfl) ⟨723575, by rfl⟩ : syracuseStep 964767 = 1447151) B1447151
theorem B965087 : Blo 964590 965087 := bstep (se 1 (by rfl) ⟨723815, by rfl⟩ : syracuseStep 965087 = 1447631) B1447631
theorem B1031167 : Blo 964590 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B8273285 : Blo 964590 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B966399 : Blo 964590 966399 := bstep (se 1 (by rfl) ⟨724799, by rfl⟩ : syracuseStep 966399 = 1449599) B1449599
theorem B966811 : Blo 964590 966811 := bstep (se 1 (by rfl) ⟨725108, by rfl⟩ : syracuseStep 966811 = 1450217) B1450217
theorem B967215 : Blo 964590 967215 := bstep (se 1 (by rfl) ⟨725411, by rfl⟩ : syracuseStep 967215 = 1450823) B1450823
theorem B3261167 : Blo 964590 3261167 := bstep (se 1 (by rfl) ⟨2445875, by rfl⟩ : syracuseStep 3261167 = 4891751) B4891751
theorem B4899689 : Blo 964590 4899689 := bstep (se 2 (by rfl) ⟨1837383, by rfl⟩ : syracuseStep 4899689 = 3674767) B3674767
theorem B967679 : Blo 964590 967679 := bstep (se 1 (by rfl) ⟨725759, by rfl⟩ : syracuseStep 967679 = 1451519) B1451519
theorem B7324991 : Blo 964590 7324991 := bstep (se 1 (by rfl) ⟨5493743, by rfl⟩ : syracuseStep 7324991 = 10987487) B10987487
theorem B968539 : Blo 964590 968539 := bstep (se 1 (by rfl) ⟨726404, by rfl⟩ : syracuseStep 968539 = 1452809) B1452809
theorem B4902767 : Blo 964590 4902767 := bstep (se 1 (by rfl) ⟨3677075, by rfl⟩ : syracuseStep 4902767 = 7354151) B7354151
theorem B133682015 : Blo 964590 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B2446271 : Blo 964590 2446271 := bstep (se 1 (by rfl) ⟨1834703, by rfl⟩ : syracuseStep 2446271 = 3669407) B3669407
theorem B7328879 : Blo 964590 7328879 := bstep (se 1 (by rfl) ⟨5496659, by rfl⟩ : syracuseStep 7328879 = 10993319) B10993319
theorem B7526621 : Blo 964590 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B169827515 : Blo 964590 169827515 := bstep (se 1 (by rfl) ⟨127370636, by rfl⟩ : syracuseStep 169827515 = 254741273) B254741273
theorem B15691657 : Blo 964590 15691657 := bstep (se 2 (by rfl) ⟨5884371, by rfl⟩ : syracuseStep 15691657 = 11768743) B11768743
theorem B3309263 : Blo 964590 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B1835759 : Blo 964590 1835759 := bstep (se 1 (by rfl) ⟨1376819, by rfl⟩ : syracuseStep 1835759 = 2753639) B2753639
theorem B4883327 : Blo 964590 4883327 := bstep (se 1 (by rfl) ⟨3662495, by rfl⟩ : syracuseStep 4883327 = 7324991) B7324991
theorem B4885919 : Blo 964590 4885919 := bstep (se 1 (by rfl) ⟨3664439, by rfl⟩ : syracuseStep 4885919 = 7328879) B7328879
theorem B113218343 : Blo 964590 113218343 := bstep (se 1 (by rfl) ⟨84913757, by rfl⟩ : syracuseStep 113218343 = 169827515) B169827515
theorem B1446959 : Blo 964590 1446959 := bstep (se 1 (by rfl) ⟨1085219, by rfl⟩ : syracuseStep 1446959 = 2170439) B2170439
theorem B1447049 : Blo 964590 1447049 := bstep (se 2 (by rfl) ⟨542643, by rfl⟩ : syracuseStep 1447049 = 1085287) B1085287
theorem B2235119 : Blo 964590 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B5513609 : Blo 964590 5513609 := bstep (se 2 (by rfl) ⟨2067603, by rfl⟩ : syracuseStep 5513609 = 4135207) B4135207
theorem B1450889 : Blo 964590 1450889 := bstep (se 2 (by rfl) ⟨544083, by rfl⟩ : syracuseStep 1450889 = 1088167) B1088167
theorem B5515523 : Blo 964590 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B2206175 : Blo 964590 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B2174111 : Blo 964590 2174111 := bstep (se 1 (by rfl) ⟨1630583, by rfl⟩ : syracuseStep 2174111 = 3261167) B3261167
theorem B8269289 : Blo 964590 8269289 := bstep (se 2 (by rfl) ⟨3100983, by rfl⟩ : syracuseStep 8269289 = 6201967) B6201967
theorem B6795659 : Blo 964590 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B1225307 : Blo 964590 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B4896287 : Blo 964590 4896287 := bstep (se 1 (by rfl) ⟨3672215, by rfl⟩ : syracuseStep 4896287 = 7344431) B7344431
theorem B966303 : Blo 964590 966303 := bstep (se 1 (by rfl) ⟨724727, by rfl⟩ : syracuseStep 966303 = 1449455) B1449455
theorem B20922209 : Blo 964590 20922209 := bstep (se 2 (by rfl) ⟨7845828, by rfl⟩ : syracuseStep 20922209 = 15691657) B15691657
theorem B966651 : Blo 964590 966651 := bstep (se 1 (by rfl) ⟨724988, by rfl⟩ : syracuseStep 966651 = 1449977) B1449977
theorem B20070989 : Blo 964590 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3262571 : Blo 964590 3262571 := bstep (se 1 (by rfl) ⟨2446928, by rfl⟩ : syracuseStep 3262571 = 4893857) B4893857
theorem B3266459 : Blo 964590 3266459 := bstep (se 1 (by rfl) ⟨2449844, by rfl⟩ : syracuseStep 3266459 = 4899689) B4899689
theorem B3268511 : Blo 964590 3268511 := bstep (se 1 (by rfl) ⟨2451383, by rfl⟩ : syracuseStep 3268511 = 4902767) B4902767
theorem B89121343 : Blo 964590 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B1630847 : Blo 964590 1630847 := bstep (se 1 (by rfl) ⟨1223135, by rfl⟩ : syracuseStep 1630847 = 2446271) B2446271
theorem B2321615 : Blo 964590 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B687175973 : Blo 964590 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B1374889 : Blo 964590 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B3675739 : Blo 964590 3675739 := bstep (se 1 (by rfl) ⟨2756804, by rfl⟩ : syracuseStep 3675739 = 5513609) B5513609
theorem B1087231 : Blo 964590 1087231 := bstep (se 1 (by rfl) ⟨815423, by rfl⟩ : syracuseStep 1087231 = 1630847) B1630847
theorem B3677015 : Blo 964590 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B1449407 : Blo 964590 1449407 := bstep (se 1 (by rfl) ⟨1087055, by rfl⟩ : syracuseStep 1449407 = 2174111) B2174111
theorem B1547743 : Blo 964590 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B5512859 : Blo 964590 5512859 := bstep (se 1 (by rfl) ⟨4134644, by rfl⟩ : syracuseStep 5512859 = 8269289) B8269289
theorem B4530439 : Blo 964590 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B13380659 : Blo 964590 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B1223839 : Blo 964590 1223839 := bstep (se 1 (by rfl) ⟨917879, by rfl⟩ : syracuseStep 1223839 = 1835759) B1835759
theorem B3255551 : Blo 964590 3255551 := bstep (se 1 (by rfl) ⟨2441663, by rfl⟩ : syracuseStep 3255551 = 4883327) B4883327
theorem B118828457 : Blo 964590 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B2175047 : Blo 964590 2175047 := bstep (se 1 (by rfl) ⟨1631285, by rfl⟩ : syracuseStep 2175047 = 3262571) B3262571
theorem B3257279 : Blo 964590 3257279 := bstep (se 1 (by rfl) ⟨2442959, by rfl⟩ : syracuseStep 3257279 = 4885919) B4885919
theorem B75478895 : Blo 964590 75478895 := bstep (se 1 (by rfl) ⟨56609171, by rfl⟩ : syracuseStep 75478895 = 113218343) B113218343
theorem B964639 : Blo 964590 964639 := bstep (se 1 (by rfl) ⟨723479, by rfl⟩ : syracuseStep 964639 = 1446959) B1446959
theorem B964699 : Blo 964590 964699 := bstep (se 1 (by rfl) ⟨723524, by rfl⟩ : syracuseStep 964699 = 1447049) B1447049
theorem B2177639 : Blo 964590 2177639 := bstep (se 1 (by rfl) ⟨1633229, by rfl⟩ : syracuseStep 2177639 = 3266459) B3266459
theorem B2179007 : Blo 964590 2179007 := bstep (se 1 (by rfl) ⟨1634255, by rfl⟩ : syracuseStep 2179007 = 3268511) B3268511
theorem B967259 : Blo 964590 967259 := bstep (se 1 (by rfl) ⟨725444, by rfl⟩ : syracuseStep 967259 = 1450889) B1450889
theorem B5883133 : Blo 964590 5883133 := bstep (se 3 (by rfl) ⟨1103087, by rfl⟩ : syracuseStep 5883133 = 2206175) B2206175
theorem B3264191 : Blo 964590 3264191 := bstep (se 1 (by rfl) ⟨2448143, by rfl⟩ : syracuseStep 3264191 = 4896287) B4896287
theorem B458117315 : Blo 964590 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B13948139 : Blo 964590 13948139 := bstep (se 1 (by rfl) ⟨10461104, by rfl⟩ : syracuseStep 13948139 = 20922209) B20922209
theorem B3267485 : Blo 964590 3267485 := bstep (se 3 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 3267485 = 1225307) B1225307
theorem B5960317 : Blo 964590 5960317 := bstep (se 3 (by rfl) ⟨1117559, by rfl⟩ : syracuseStep 5960317 = 2235119) B2235119
theorem B1833185 : Blo 964590 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B3675239 : Blo 964590 3675239 := bstep (se 1 (by rfl) ⟨2756429, by rfl⟩ : syracuseStep 3675239 = 5512859) B5512859
theorem B8920439 : Blo 964590 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B2170367 : Blo 964590 2170367 := bstep (se 1 (by rfl) ⟨1627775, by rfl⟩ : syracuseStep 2170367 = 3255551) B3255551
theorem B1449641 : Blo 964590 1449641 := bstep (se 2 (by rfl) ⟨543615, by rfl⟩ : syracuseStep 1449641 = 1087231) B1087231
theorem B1450031 : Blo 964590 1450031 := bstep (se 1 (by rfl) ⟨1087523, by rfl⟩ : syracuseStep 1450031 = 2175047) B2175047
theorem B2171519 : Blo 964590 2171519 := bstep (se 1 (by rfl) ⟨1628639, by rfl⟩ : syracuseStep 2171519 = 3257279) B3257279
theorem B1222123 : Blo 964590 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1451759 : Blo 964590 1451759 := bstep (se 1 (by rfl) ⟨1088819, by rfl⟩ : syracuseStep 1451759 = 2177639) B2177639
theorem B1452671 : Blo 964590 1452671 := bstep (se 1 (by rfl) ⟨1089503, by rfl⟩ : syracuseStep 1452671 = 2179007) B2179007
theorem B6040585 : Blo 964590 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B7844177 : Blo 964590 7844177 := bstep (se 2 (by rfl) ⟨2941566, by rfl⟩ : syracuseStep 7844177 = 5883133) B5883133
theorem B2176127 : Blo 964590 2176127 := bstep (se 1 (by rfl) ⟨1632095, by rfl⟩ : syracuseStep 2176127 = 3264191) B3264191
theorem B305411543 : Blo 964590 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B2178323 : Blo 964590 2178323 := bstep (se 1 (by rfl) ⟨1633742, by rfl⟩ : syracuseStep 2178323 = 3267485) B3267485
theorem B966271 : Blo 964590 966271 := bstep (se 1 (by rfl) ⟨724703, by rfl⟩ : syracuseStep 966271 = 1449407) B1449407
theorem B7947089 : Blo 964590 7947089 := bstep (se 2 (by rfl) ⟨2980158, by rfl⟩ : syracuseStep 7947089 = 5960317) B5960317
theorem B4900985 : Blo 964590 4900985 := bstep (se 2 (by rfl) ⟨1837869, by rfl⟩ : syracuseStep 4900985 = 3675739) B3675739
theorem B79218971 : Blo 964590 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B50319263 : Blo 964590 50319263 := bstep (se 1 (by rfl) ⟨37739447, by rfl⟩ : syracuseStep 50319263 = 75478895) B75478895
theorem B9298759 : Blo 964590 9298759 := bstep (se 1 (by rfl) ⟨6974069, by rfl⟩ : syracuseStep 9298759 = 13948139) B13948139
theorem B1631785 : Blo 964590 1631785 := bstep (se 2 (by rfl) ⟨611919, by rfl⟩ : syracuseStep 1631785 = 1223839) B1223839
theorem B2451343 : Blo 964590 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B2063657 : Blo 964590 2063657 := bstep (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) B1547743
theorem B1446911 : Blo 964590 1446911 := bstep (se 1 (by rfl) ⟨1085183, by rfl⟩ : syracuseStep 1446911 = 2170367) B2170367
theorem B32216453 : Blo 964590 32216453 := bstep (se 4 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 32216453 = 6040585) B6040585
theorem B1447679 : Blo 964590 1447679 := bstep (se 1 (by rfl) ⟨1085759, by rfl⟩ : syracuseStep 1447679 = 2171519) B2171519
theorem B1450751 : Blo 964590 1450751 := bstep (se 1 (by rfl) ⟨1088063, by rfl⟩ : syracuseStep 1450751 = 2176127) B2176127
theorem B1452215 : Blo 964590 1452215 := bstep (se 1 (by rfl) ⟨1089161, by rfl⟩ : syracuseStep 1452215 = 2178323) B2178323
theorem B12398345 : Blo 964590 12398345 := bstep (se 2 (by rfl) ⟨4649379, by rfl⟩ : syracuseStep 12398345 = 9298759) B9298759
theorem B2175713 : Blo 964590 2175713 := bstep (se 2 (by rfl) ⟨815892, by rfl⟩ : syracuseStep 2175713 = 1631785) B1631785
theorem B5946959 : Blo 964590 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B966427 : Blo 964590 966427 := bstep (se 1 (by rfl) ⟨724820, by rfl⟩ : syracuseStep 966427 = 1449641) B1449641
theorem B966687 : Blo 964590 966687 := bstep (se 1 (by rfl) ⟨725015, by rfl⟩ : syracuseStep 966687 = 1450031) B1450031
theorem B967839 : Blo 964590 967839 := bstep (se 1 (by rfl) ⟨725879, by rfl⟩ : syracuseStep 967839 = 1451759) B1451759
theorem B968447 : Blo 964590 968447 := bstep (se 1 (by rfl) ⟨726335, by rfl⟩ : syracuseStep 968447 = 1452671) B1452671
theorem B5229451 : Blo 964590 5229451 := bstep (se 1 (by rfl) ⟨3922088, by rfl⟩ : syracuseStep 5229451 = 7844177) B7844177
theorem B203607695 : Blo 964590 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B5298059 : Blo 964590 5298059 := bstep (se 1 (by rfl) ⟨3973544, by rfl⟩ : syracuseStep 5298059 = 7947089) B7947089
theorem B3267323 : Blo 964590 3267323 := bstep (se 1 (by rfl) ⟨2450492, by rfl⟩ : syracuseStep 3267323 = 4900985) B4900985
theorem B52812647 : Blo 964590 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B1629497 : Blo 964590 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B3268457 : Blo 964590 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B2450159 : Blo 964590 2450159 := bstep (se 1 (by rfl) ⟨1837619, by rfl⟩ : syracuseStep 2450159 = 3675239) B3675239
theorem B5503085 : Blo 964590 5503085 := bstep (se 3 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 5503085 = 2063657) B2063657
theorem B134184701 : Blo 964590 134184701 := bstep (se 3 (by rfl) ⟨25159631, by rfl⟩ : syracuseStep 134184701 = 50319263) B50319263
theorem B1086331 : Blo 964590 1086331 := bstep (se 1 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 1086331 = 1629497) B1629497
theorem B14128157 : Blo 964590 14128157 := bstep (se 3 (by rfl) ⟨2649029, by rfl⟩ : syracuseStep 14128157 = 5298059) B5298059
theorem B8265563 : Blo 964590 8265563 := bstep (se 1 (by rfl) ⟨6199172, by rfl⟩ : syracuseStep 8265563 = 12398345) B12398345
theorem B1450475 : Blo 964590 1450475 := bstep (se 1 (by rfl) ⟨1087856, by rfl⟩ : syracuseStep 1450475 = 2175713) B2175713
theorem B135738463 : Blo 964590 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B964607 : Blo 964590 964607 := bstep (se 1 (by rfl) ⟨723455, by rfl⟩ : syracuseStep 964607 = 1446911) B1446911
theorem B21477635 : Blo 964590 21477635 := bstep (se 1 (by rfl) ⟨16108226, by rfl⟩ : syracuseStep 21477635 = 32216453) B32216453
theorem B965119 : Blo 964590 965119 := bstep (se 1 (by rfl) ⟨723839, by rfl⟩ : syracuseStep 965119 = 1447679) B1447679
theorem B2178215 : Blo 964590 2178215 := bstep (se 1 (by rfl) ⟨1633661, by rfl⟩ : syracuseStep 2178215 = 3267323) B3267323
theorem B35208431 : Blo 964590 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B2178971 : Blo 964590 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B967167 : Blo 964590 967167 := bstep (se 1 (by rfl) ⟨725375, by rfl⟩ : syracuseStep 967167 = 1450751) B1450751
theorem B968143 : Blo 964590 968143 := bstep (se 1 (by rfl) ⟨726107, by rfl⟩ : syracuseStep 968143 = 1452215) B1452215
theorem B6972601 : Blo 964590 6972601 := bstep (se 2 (by rfl) ⟨2614725, by rfl⟩ : syracuseStep 6972601 = 5229451) B5229451
theorem B1633439 : Blo 964590 1633439 := bstep (se 1 (by rfl) ⟨1225079, by rfl⟩ : syracuseStep 1633439 = 2450159) B2450159
theorem B3668723 : Blo 964590 3668723 := bstep (se 1 (by rfl) ⟨2751542, by rfl⟩ : syracuseStep 3668723 = 5503085) B5503085
theorem B357825869 : Blo 964590 357825869 := bstep (se 3 (by rfl) ⟨67092350, by rfl⟩ : syracuseStep 357825869 = 134184701) B134184701
theorem B3964639 : Blo 964590 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B5510375 : Blo 964590 5510375 := bstep (se 1 (by rfl) ⟨4132781, by rfl⟩ : syracuseStep 5510375 = 8265563) B8265563
theorem B1448441 : Blo 964590 1448441 := bstep (se 2 (by rfl) ⟨543165, by rfl⟩ : syracuseStep 1448441 = 1086331) B1086331
theorem B180984617 : Blo 964590 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B1088959 : Blo 964590 1088959 := bstep (se 1 (by rfl) ⟨816719, by rfl⟩ : syracuseStep 1088959 = 1633439) B1633439
theorem B1452143 : Blo 964590 1452143 := bstep (se 1 (by rfl) ⟨1089107, by rfl⟩ : syracuseStep 1452143 = 2178215) B2178215
theorem B23472287 : Blo 964590 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B5286185 : Blo 964590 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B1452647 : Blo 964590 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B9418771 : Blo 964590 9418771 := bstep (se 1 (by rfl) ⟨7064078, by rfl⟩ : syracuseStep 9418771 = 14128157) B14128157
theorem B966983 : Blo 964590 966983 := bstep (se 1 (by rfl) ⟨725237, by rfl⟩ : syracuseStep 966983 = 1450475) B1450475
theorem B2445815 : Blo 964590 2445815 := bstep (se 1 (by rfl) ⟨1834361, by rfl⟩ : syracuseStep 2445815 = 3668723) B3668723
theorem B9296801 : Blo 964590 9296801 := bstep (se 2 (by rfl) ⟨3486300, by rfl⟩ : syracuseStep 9296801 = 6972601) B6972601
theorem B14318423 : Blo 964590 14318423 := bstep (se 1 (by rfl) ⟨10738817, by rfl⟩ : syracuseStep 14318423 = 21477635) B21477635
theorem B238550579 : Blo 964590 238550579 := bstep (se 1 (by rfl) ⟨178912934, by rfl⟩ : syracuseStep 238550579 = 357825869) B357825869
theorem B50233445 : Blo 964590 50233445 := bstep (se 4 (by rfl) ⟨4709385, by rfl⟩ : syracuseStep 50233445 = 9418771) B9418771
theorem B3673583 : Blo 964590 3673583 := bstep (se 1 (by rfl) ⟨2755187, by rfl⟩ : syracuseStep 3673583 = 5510375) B5510375
theorem B120656411 : Blo 964590 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B6197867 : Blo 964590 6197867 := bstep (se 1 (by rfl) ⟨4648400, by rfl⟩ : syracuseStep 6197867 = 9296801) B9296801
theorem B9545615 : Blo 964590 9545615 := bstep (se 1 (by rfl) ⟨7159211, by rfl⟩ : syracuseStep 9545615 = 14318423) B14318423
theorem B1451945 : Blo 964590 1451945 := bstep (se 2 (by rfl) ⟨544479, by rfl⟩ : syracuseStep 1451945 = 1088959) B1088959
theorem B159033719 : Blo 964590 159033719 := bstep (se 1 (by rfl) ⟨119275289, by rfl⟩ : syracuseStep 159033719 = 238550579) B238550579
theorem B965627 : Blo 964590 965627 := bstep (se 1 (by rfl) ⟨724220, by rfl⟩ : syracuseStep 965627 = 1448441) B1448441
theorem B968095 : Blo 964590 968095 := bstep (se 1 (by rfl) ⟨726071, by rfl⟩ : syracuseStep 968095 = 1452143) B1452143
theorem B15648191 : Blo 964590 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B3524123 : Blo 964590 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B968431 : Blo 964590 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B1630543 : Blo 964590 1630543 := bstep (se 1 (by rfl) ⟨1222907, by rfl⟩ : syracuseStep 1630543 = 2445815) B2445815
theorem B33488963 : Blo 964590 33488963 := bstep (se 1 (by rfl) ⟨25116722, by rfl⟩ : syracuseStep 33488963 = 50233445) B50233445
theorem B4131911 : Blo 964590 4131911 := bstep (se 1 (by rfl) ⟨3098933, by rfl⟩ : syracuseStep 4131911 = 6197867) B6197867
theorem B6363743 : Blo 964590 6363743 := bstep (se 1 (by rfl) ⟨4772807, by rfl⟩ : syracuseStep 6363743 = 9545615) B9545615
theorem B2174057 : Blo 964590 2174057 := bstep (se 2 (by rfl) ⟨815271, by rfl⟩ : syracuseStep 2174057 = 1630543) B1630543
theorem B10432127 : Blo 964590 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B967963 : Blo 964590 967963 := bstep (se 1 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 967963 = 1451945) B1451945
theorem B106022479 : Blo 964590 106022479 := bstep (se 1 (by rfl) ⟨79516859, by rfl⟩ : syracuseStep 106022479 = 159033719) B159033719
theorem B2349415 : Blo 964590 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B2449055 : Blo 964590 2449055 := bstep (se 1 (by rfl) ⟨1836791, by rfl⟩ : syracuseStep 2449055 = 3673583) B3673583
theorem B80437607 : Blo 964590 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B2754607 : Blo 964590 2754607 := bstep (se 1 (by rfl) ⟨2065955, by rfl⟩ : syracuseStep 2754607 = 4131911) B4131911
theorem B141363305 : Blo 964590 141363305 := bstep (se 2 (by rfl) ⟨53011239, by rfl⟩ : syracuseStep 141363305 = 106022479) B106022479
theorem B1449371 : Blo 964590 1449371 := bstep (se 1 (by rfl) ⟨1087028, by rfl⟩ : syracuseStep 1449371 = 2174057) B2174057
theorem B6954751 : Blo 964590 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B22325975 : Blo 964590 22325975 := bstep (se 1 (by rfl) ⟨16744481, by rfl⟩ : syracuseStep 22325975 = 33488963) B33488963
theorem B12530213 : Blo 964590 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B53625071 : Blo 964590 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B1632703 : Blo 964590 1632703 := bstep (se 1 (by rfl) ⟨1224527, by rfl⟩ : syracuseStep 1632703 = 2449055) B2449055
theorem B16969981 : Blo 964590 16969981 := bstep (se 3 (by rfl) ⟨3181871, by rfl⟩ : syracuseStep 16969981 = 6363743) B6363743
theorem B35750047 : Blo 964590 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B94242203 : Blo 964590 94242203 := bstep (se 1 (by rfl) ⟨70681652, by rfl⟩ : syracuseStep 94242203 = 141363305) B141363305
theorem B3672809 : Blo 964590 3672809 := bstep (se 2 (by rfl) ⟨1377303, by rfl⟩ : syracuseStep 3672809 = 2754607) B2754607
theorem B14883983 : Blo 964590 14883983 := bstep (se 1 (by rfl) ⟨11162987, by rfl⟩ : syracuseStep 14883983 = 22325975) B22325975
theorem B2176937 : Blo 964590 2176937 := bstep (se 2 (by rfl) ⟨816351, by rfl⟩ : syracuseStep 2176937 = 1632703) B1632703
theorem B966247 : Blo 964590 966247 := bstep (se 1 (by rfl) ⟨724685, by rfl⟩ : syracuseStep 966247 = 1449371) B1449371
theorem B22626641 : Blo 964590 22626641 := bstep (se 2 (by rfl) ⟨8484990, by rfl⟩ : syracuseStep 22626641 = 16969981) B16969981
theorem B8353475 : Blo 964590 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B9273001 : Blo 964590 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B1451291 : Blo 964590 1451291 := bstep (se 1 (by rfl) ⟨1088468, by rfl⟩ : syracuseStep 1451291 = 2176937) B2176937
theorem B12364001 : Blo 964590 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B15084427 : Blo 964590 15084427 := bstep (se 1 (by rfl) ⟨11313320, by rfl⟩ : syracuseStep 15084427 = 22626641) B22626641
theorem B62828135 : Blo 964590 62828135 := bstep (se 1 (by rfl) ⟨47121101, by rfl⟩ : syracuseStep 62828135 = 94242203) B94242203
theorem B47666729 : Blo 964590 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B2448539 : Blo 964590 2448539 := bstep (se 1 (by rfl) ⟨1836404, by rfl⟩ : syracuseStep 2448539 = 3672809) B3672809
theorem B9922655 : Blo 964590 9922655 := bstep (se 1 (by rfl) ⟨7441991, by rfl⟩ : syracuseStep 9922655 = 14883983) B14883983
theorem B5568983 : Blo 964590 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B127111277 : Blo 964590 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B41885423 : Blo 964590 41885423 := bstep (se 1 (by rfl) ⟨31414067, by rfl⟩ : syracuseStep 41885423 = 62828135) B62828135
theorem B3712655 : Blo 964590 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B967527 : Blo 964590 967527 := bstep (se 1 (by rfl) ⟨725645, by rfl⟩ : syracuseStep 967527 = 1451291) B1451291
theorem B8242667 : Blo 964590 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B20112569 : Blo 964590 20112569 := bstep (se 2 (by rfl) ⟨7542213, by rfl⟩ : syracuseStep 20112569 = 15084427) B15084427
theorem B1632359 : Blo 964590 1632359 := bstep (se 1 (by rfl) ⟨1224269, by rfl⟩ : syracuseStep 1632359 = 2448539) B2448539
theorem B6615103 : Blo 964590 6615103 := bstep (se 1 (by rfl) ⟨4961327, by rfl⟩ : syracuseStep 6615103 = 9922655) B9922655
theorem B84740851 : Blo 964590 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B9900413 : Blo 964590 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B27923615 : Blo 964590 27923615 := bstep (se 1 (by rfl) ⟨20942711, by rfl⟩ : syracuseStep 27923615 = 41885423) B41885423
theorem B8820137 : Blo 964590 8820137 := bstep (se 2 (by rfl) ⟨3307551, by rfl⟩ : syracuseStep 8820137 = 6615103) B6615103
theorem B13408379 : Blo 964590 13408379 := bstep (se 1 (by rfl) ⟨10056284, by rfl⟩ : syracuseStep 13408379 = 20112569) B20112569
theorem B1088239 : Blo 964590 1088239 := bstep (se 1 (by rfl) ⟨816179, by rfl⟩ : syracuseStep 1088239 = 1632359) B1632359
theorem B5495111 : Blo 964590 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B18615743 : Blo 964590 18615743 := bstep (se 1 (by rfl) ⟨13961807, by rfl⟩ : syracuseStep 18615743 = 27923615) B27923615
theorem B112987801 : Blo 964590 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B1450985 : Blo 964590 1450985 := bstep (se 2 (by rfl) ⟨544119, by rfl⟩ : syracuseStep 1450985 = 1088239) B1088239
theorem B6600275 : Blo 964590 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B23520365 : Blo 964590 23520365 := bstep (se 3 (by rfl) ⟨4410068, by rfl⟩ : syracuseStep 23520365 = 8820137) B8820137
theorem B8938919 : Blo 964590 8938919 := bstep (se 1 (by rfl) ⟨6704189, by rfl⟩ : syracuseStep 8938919 = 13408379) B13408379
theorem B3663407 : Blo 964590 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B4400183 : Blo 964590 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B150650401 : Blo 964590 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B967323 : Blo 964590 967323 := bstep (se 1 (by rfl) ⟨725492, by rfl⟩ : syracuseStep 967323 = 1450985) B1450985
theorem B15680243 : Blo 964590 15680243 := bstep (se 1 (by rfl) ⟨11760182, by rfl⟩ : syracuseStep 15680243 = 23520365) B23520365
theorem B2442271 : Blo 964590 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B12410495 : Blo 964590 12410495 := bstep (se 1 (by rfl) ⟨9307871, by rfl⟩ : syracuseStep 12410495 = 18615743) B18615743
theorem B5959279 : Blo 964590 5959279 := bstep (se 1 (by rfl) ⟨4469459, by rfl⟩ : syracuseStep 5959279 = 8938919) B8938919
theorem B10453495 : Blo 964590 10453495 := bstep (se 1 (by rfl) ⟨7840121, by rfl⟩ : syracuseStep 10453495 = 15680243) B15680243
theorem B3256361 : Blo 964590 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B7945705 : Blo 964590 7945705 := bstep (se 2 (by rfl) ⟨2979639, by rfl⟩ : syracuseStep 7945705 = 5959279) B5959279
theorem B8273663 : Blo 964590 8273663 := bstep (se 1 (by rfl) ⟨6205247, by rfl⟩ : syracuseStep 8273663 = 12410495) B12410495
theorem B2933455 : Blo 964590 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B200867201 : Blo 964590 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B2170907 : Blo 964590 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B10594273 : Blo 964590 10594273 := bstep (se 2 (by rfl) ⟨3972852, by rfl⟩ : syracuseStep 10594273 = 7945705) B7945705
theorem B5515775 : Blo 964590 5515775 := bstep (se 1 (by rfl) ⟨4136831, by rfl⟩ : syracuseStep 5515775 = 8273663) B8273663
theorem B13937993 : Blo 964590 13937993 := bstep (se 2 (by rfl) ⟨5226747, by rfl⟩ : syracuseStep 13937993 = 10453495) B10453495
theorem B3911273 : Blo 964590 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B133911467 : Blo 964590 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B14125697 : Blo 964590 14125697 := bstep (se 2 (by rfl) ⟨5297136, by rfl⟩ : syracuseStep 14125697 = 10594273) B10594273
theorem B1447271 : Blo 964590 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B3677183 : Blo 964590 3677183 := bstep (se 1 (by rfl) ⟨2757887, by rfl⟩ : syracuseStep 3677183 = 5515775) B5515775
theorem B89274311 : Blo 964590 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B9291995 : Blo 964590 9291995 := bstep (se 1 (by rfl) ⟨6968996, by rfl⟩ : syracuseStep 9291995 = 13937993) B13937993
theorem B2607515 : Blo 964590 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B6194663 : Blo 964590 6194663 := bstep (se 1 (by rfl) ⟨4645997, by rfl⟩ : syracuseStep 6194663 = 9291995) B9291995
theorem B1738343 : Blo 964590 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B59516207 : Blo 964590 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B9417131 : Blo 964590 9417131 := bstep (se 1 (by rfl) ⟨7062848, by rfl⟩ : syracuseStep 9417131 = 14125697) B14125697
theorem B964847 : Blo 964590 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B2451455 : Blo 964590 2451455 := bstep (se 1 (by rfl) ⟨1838591, by rfl⟩ : syracuseStep 2451455 = 3677183) B3677183
theorem B4129775 : Blo 964590 4129775 := bstep (se 1 (by rfl) ⟨3097331, by rfl⟩ : syracuseStep 4129775 = 6194663) B6194663
theorem B1158895 : Blo 964590 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B6278087 : Blo 964590 6278087 := bstep (se 1 (by rfl) ⟨4708565, by rfl⟩ : syracuseStep 6278087 = 9417131) B9417131
theorem B39677471 : Blo 964590 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B1634303 : Blo 964590 1634303 := bstep (se 1 (by rfl) ⟨1225727, by rfl⟩ : syracuseStep 1634303 = 2451455) B2451455
theorem B2753183 : Blo 964590 2753183 := bstep (se 1 (by rfl) ⟨2064887, by rfl⟩ : syracuseStep 2753183 = 4129775) B4129775
theorem B1545193 : Blo 964590 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B26451647 : Blo 964590 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B1089535 : Blo 964590 1089535 := bstep (se 1 (by rfl) ⟨817151, by rfl⟩ : syracuseStep 1089535 = 1634303) B1634303
theorem B4185391 : Blo 964590 4185391 := bstep (se 1 (by rfl) ⟨3139043, by rfl⟩ : syracuseStep 4185391 = 6278087) B6278087
theorem B1835455 : Blo 964590 1835455 := bstep (se 1 (by rfl) ⟨1376591, by rfl⟩ : syracuseStep 1835455 = 2753183) B2753183
theorem B17634431 : Blo 964590 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B5580521 : Blo 964590 5580521 := bstep (se 2 (by rfl) ⟨2092695, by rfl⟩ : syracuseStep 5580521 = 4185391) B4185391
theorem B1452713 : Blo 964590 1452713 := bstep (se 2 (by rfl) ⟨544767, by rfl⟩ : syracuseStep 1452713 = 1089535) B1089535
theorem B2060257 : Blo 964590 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B3720347 : Blo 964590 3720347 := bstep (se 1 (by rfl) ⟨2790260, by rfl⟩ : syracuseStep 3720347 = 5580521) B5580521
theorem B968475 : Blo 964590 968475 := bstep (se 1 (by rfl) ⟨726356, by rfl⟩ : syracuseStep 968475 = 1452713) B1452713
theorem B2447273 : Blo 964590 2447273 := bstep (se 2 (by rfl) ⟨917727, by rfl⟩ : syracuseStep 2447273 = 1835455) B1835455
theorem B11756287 : Blo 964590 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B2747009 : Blo 964590 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B15675049 : Blo 964590 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B2480231 : Blo 964590 2480231 := bstep (se 1 (by rfl) ⟨1860173, by rfl⟩ : syracuseStep 2480231 = 3720347) B3720347
theorem B1631515 : Blo 964590 1631515 := bstep (se 1 (by rfl) ⟨1223636, by rfl⟩ : syracuseStep 1631515 = 2447273) B2447273
theorem B1831339 : Blo 964590 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B2175353 : Blo 964590 2175353 := bstep (se 2 (by rfl) ⟨815757, by rfl⟩ : syracuseStep 2175353 = 1631515) B1631515
theorem B105823189 : Blo 964590 105823189 := bstep (se 7 (by rfl) ⟨1240115, by rfl⟩ : syracuseStep 105823189 = 2480231) B2480231
theorem B2441785 : Blo 964590 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B20900065 : Blo 964590 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B1450235 : Blo 964590 1450235 := bstep (se 1 (by rfl) ⟨1087676, by rfl⟩ : syracuseStep 1450235 = 2175353) B2175353
theorem B3255713 : Blo 964590 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B27866753 : Blo 964590 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B141097585 : Blo 964590 141097585 := bstep (se 2 (by rfl) ⟨52911594, by rfl⟩ : syracuseStep 141097585 = 105823189) B105823189
theorem B2170475 : Blo 964590 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B188130113 : Blo 964590 188130113 := bstep (se 2 (by rfl) ⟨70548792, by rfl⟩ : syracuseStep 188130113 = 141097585) B141097585
theorem B966823 : Blo 964590 966823 := bstep (se 1 (by rfl) ⟨725117, by rfl⟩ : syracuseStep 966823 = 1450235) B1450235
theorem B18577835 : Blo 964590 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B1446983 : Blo 964590 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B125420075 : Blo 964590 125420075 := bstep (se 1 (by rfl) ⟨94065056, by rfl⟩ : syracuseStep 125420075 = 188130113) B188130113
theorem B12385223 : Blo 964590 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B964655 : Blo 964590 964655 := bstep (se 1 (by rfl) ⟨723491, by rfl⟩ : syracuseStep 964655 = 1446983) B1446983
theorem B83613383 : Blo 964590 83613383 := bstep (se 1 (by rfl) ⟨62710037, by rfl⟩ : syracuseStep 83613383 = 125420075) B125420075
theorem B8256815 : Blo 964590 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B55742255 : Blo 964590 55742255 := bstep (se 1 (by rfl) ⟨41806691, by rfl⟩ : syracuseStep 55742255 = 83613383) B83613383
theorem B5504543 : Blo 964590 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B37161503 : Blo 964590 37161503 := bstep (se 1 (by rfl) ⟨27871127, by rfl⟩ : syracuseStep 37161503 = 55742255) B55742255
theorem B3669695 : Blo 964590 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B24774335 : Blo 964590 24774335 := bstep (se 1 (by rfl) ⟨18580751, by rfl⟩ : syracuseStep 24774335 = 37161503) B37161503
theorem B2446463 : Blo 964590 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B16516223 : Blo 964590 16516223 := bstep (se 1 (by rfl) ⟨12387167, by rfl⟩ : syracuseStep 16516223 = 24774335) B24774335
theorem B1630975 : Blo 964590 1630975 := bstep (se 1 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 1630975 = 2446463) B2446463
theorem B11010815 : Blo 964590 11010815 := bstep (se 1 (by rfl) ⟨8258111, by rfl⟩ : syracuseStep 11010815 = 16516223) B16516223
theorem B2174633 : Blo 964590 2174633 := bstep (se 2 (by rfl) ⟨815487, by rfl⟩ : syracuseStep 2174633 = 1630975) B1630975
theorem B7340543 : Blo 964590 7340543 := bstep (se 1 (by rfl) ⟨5505407, by rfl⟩ : syracuseStep 7340543 = 11010815) B11010815
theorem B1449755 : Blo 964590 1449755 := bstep (se 1 (by rfl) ⟨1087316, by rfl⟩ : syracuseStep 1449755 = 2174633) B2174633
theorem B4893695 : Blo 964590 4893695 := bstep (se 1 (by rfl) ⟨3670271, by rfl⟩ : syracuseStep 4893695 = 7340543) B7340543
theorem B966503 : Blo 964590 966503 := bstep (se 1 (by rfl) ⟨724877, by rfl⟩ : syracuseStep 966503 = 1449755) B1449755
theorem B3262463 : Blo 964590 3262463 := bstep (se 1 (by rfl) ⟨2446847, by rfl⟩ : syracuseStep 3262463 = 4893695) B4893695
theorem B2174975 : Blo 964590 2174975 := bstep (se 1 (by rfl) ⟨1631231, by rfl⟩ : syracuseStep 2174975 = 3262463) B3262463
theorem B1449983 : Blo 964590 1449983 := bstep (se 1 (by rfl) ⟨1087487, by rfl⟩ : syracuseStep 1449983 = 2174975) B2174975
theorem B966655 : Blo 964590 966655 := bstep (se 1 (by rfl) ⟨724991, by rfl⟩ : syracuseStep 966655 = 1449983) B1449983

theorem C0 (j : ℕ) (h1 : 241147 ≤ j) (h2 : j ≤ 241846) : Blo 964590 (4 * j + 3) := by
  interval_cases j
  · exact B964591
  · exact B964595
  · exact B964599
  · exact B964603
  · exact B964607
  · exact B964611
  · exact B964615
  · exact B964619
  · exact B964623
  · exact B964627
  · exact B964631
  · exact B964635
  · exact B964639
  · exact B964643
  · exact B964647
  · exact B964651
  · exact B964655
  · exact B964659
  · exact B964663
  · exact B964667
  · exact B964671
  · exact B964675
  · exact B964679
  · exact B964683
  · exact B964687
  · exact B964691
  · exact B964695
  · exact B964699
  · exact B964703
  · exact B964707
  · exact B964711
  · exact B964715
  · exact B964719
  · exact B964723
  · exact B964727
  · exact B964731
  · exact B964735
  · exact B964739
  · exact B964743
  · exact B964747
  · exact B964751
  · exact B964755
  · exact B964759
  · exact B964763
  · exact B964767
  · exact B964771
  · exact B964775
  · exact B964779
  · exact B964783
  · exact B964787
  · exact B964791
  · exact B964795
  · exact B964799
  · exact B964803
  · exact B964807
  · exact B964811
  · exact B964815
  · exact B964819
  · exact B964823
  · exact B964827
  · exact B964831
  · exact B964835
  · exact B964839
  · exact B964843
  · exact B964847
  · exact B964851
  · exact B964855
  · exact B964859
  · exact B964863
  · exact B964867
  · exact B964871
  · exact B964875
  · exact B964879
  · exact B964883
  · exact B964887
  · exact B964891
  · exact B964895
  · exact B964899
  · exact B964903
  · exact B964907
  · exact B964911
  · exact B964915
  · exact B964919
  · exact B964923
  · exact B964927
  · exact B964931
  · exact B964935
  · exact B964939
  · exact B964943
  · exact B964947
  · exact B964951
  · exact B964955
  · exact B964959
  · exact B964963
  · exact B964967
  · exact B964971
  · exact B964975
  · exact B964979
  · exact B964983
  · exact B964987
  · exact B964991
  · exact B964995
  · exact B964999
  · exact B965003
  · exact B965007
  · exact B965011
  · exact B965015
  · exact B965019
  · exact B965023
  · exact B965027
  · exact B965031
  · exact B965035
  · exact B965039
  · exact B965043
  · exact B965047
  · exact B965051
  · exact B965055
  · exact B965059
  · exact B965063
  · exact B965067
  · exact B965071
  · exact B965075
  · exact B965079
  · exact B965083
  · exact B965087
  · exact B965091
  · exact B965095
  · exact B965099
  · exact B965103
  · exact B965107
  · exact B965111
  · exact B965115
  · exact B965119
  · exact B965123
  · exact B965127
  · exact B965131
  · exact B965135
  · exact B965139
  · exact B965143
  · exact B965147
  · exact B965151
  · exact B965155
  · exact B965159
  · exact B965163
  · exact B965167
  · exact B965171
  · exact B965175
  · exact B965179
  · exact B965183
  · exact B965187
  · exact B965191
  · exact B965195
  · exact B965199
  · exact B965203
  · exact B965207
  · exact B965211
  · exact B965215
  · exact B965219
  · exact B965223
  · exact B965227
  · exact B965231
  · exact B965235
  · exact B965239
  · exact B965243
  · exact B965247
  · exact B965251
  · exact B965255
  · exact B965259
  · exact B965263
  · exact B965267
  · exact B965271
  · exact B965275
  · exact B965279
  · exact B965283
  · exact B965287
  · exact B965291
  · exact B965295
  · exact B965299
  · exact B965303
  · exact B965307
  · exact B965311
  · exact B965315
  · exact B965319
  · exact B965323
  · exact B965327
  · exact B965331
  · exact B965335
  · exact B965339
  · exact B965343
  · exact B965347
  · exact B965351
  · exact B965355
  · exact B965359
  · exact B965363
  · exact B965367
  · exact B965371
  · exact B965375
  · exact B965379
  · exact B965383
  · exact B965387
  · exact B965391
  · exact B965395
  · exact B965399
  · exact B965403
  · exact B965407
  · exact B965411
  · exact B965415
  · exact B965419
  · exact B965423
  · exact B965427
  · exact B965431
  · exact B965435
  · exact B965439
  · exact B965443
  · exact B965447
  · exact B965451
  · exact B965455
  · exact B965459
  · exact B965463
  · exact B965467
  · exact B965471
  · exact B965475
  · exact B965479
  · exact B965483
  · exact B965487
  · exact B965491
  · exact B965495
  · exact B965499
  · exact B965503
  · exact B965507
  · exact B965511
  · exact B965515
  · exact B965519
  · exact B965523
  · exact B965527
  · exact B965531
  · exact B965535
  · exact B965539
  · exact B965543
  · exact B965547
  · exact B965551
  · exact B965555
  · exact B965559
  · exact B965563
  · exact B965567
  · exact B965571
  · exact B965575
  · exact B965579
  · exact B965583
  · exact B965587
  · exact B965591
  · exact B965595
  · exact B965599
  · exact B965603
  · exact B965607
  · exact B965611
  · exact B965615
  · exact B965619
  · exact B965623
  · exact B965627
  · exact B965631
  · exact B965635
  · exact B965639
  · exact B965643
  · exact B965647
  · exact B965651
  · exact B965655
  · exact B965659
  · exact B965663
  · exact B965667
  · exact B965671
  · exact B965675
  · exact B965679
  · exact B965683
  · exact B965687
  · exact B965691
  · exact B965695
  · exact B965699
  · exact B965703
  · exact B965707
  · exact B965711
  · exact B965715
  · exact B965719
  · exact B965723
  · exact B965727
  · exact B965731
  · exact B965735
  · exact B965739
  · exact B965743
  · exact B965747
  · exact B965751
  · exact B965755
  · exact B965759
  · exact B965763
  · exact B965767
  · exact B965771
  · exact B965775
  · exact B965779
  · exact B965783
  · exact B965787
  · exact B965791
  · exact B965795
  · exact B965799
  · exact B965803
  · exact B965807
  · exact B965811
  · exact B965815
  · exact B965819
  · exact B965823
  · exact B965827
  · exact B965831
  · exact B965835
  · exact B965839
  · exact B965843
  · exact B965847
  · exact B965851
  · exact B965855
  · exact B965859
  · exact B965863
  · exact B965867
  · exact B965871
  · exact B965875
  · exact B965879
  · exact B965883
  · exact B965887
  · exact B965891
  · exact B965895
  · exact B965899
  · exact B965903
  · exact B965907
  · exact B965911
  · exact B965915
  · exact B965919
  · exact B965923
  · exact B965927
  · exact B965931
  · exact B965935
  · exact B965939
  · exact B965943
  · exact B965947
  · exact B965951
  · exact B965955
  · exact B965959
  · exact B965963
  · exact B965967
  · exact B965971
  · exact B965975
  · exact B965979
  · exact B965983
  · exact B965987
  · exact B965991
  · exact B965995
  · exact B965999
  · exact B966003
  · exact B966007
  · exact B966011
  · exact B966015
  · exact B966019
  · exact B966023
  · exact B966027
  · exact B966031
  · exact B966035
  · exact B966039
  · exact B966043
  · exact B966047
  · exact B966051
  · exact B966055
  · exact B966059
  · exact B966063
  · exact B966067
  · exact B966071
  · exact B966075
  · exact B966079
  · exact B966083
  · exact B966087
  · exact B966091
  · exact B966095
  · exact B966099
  · exact B966103
  · exact B966107
  · exact B966111
  · exact B966115
  · exact B966119
  · exact B966123
  · exact B966127
  · exact B966131
  · exact B966135
  · exact B966139
  · exact B966143
  · exact B966147
  · exact B966151
  · exact B966155
  · exact B966159
  · exact B966163
  · exact B966167
  · exact B966171
  · exact B966175
  · exact B966179
  · exact B966183
  · exact B966187
  · exact B966191
  · exact B966195
  · exact B966199
  · exact B966203
  · exact B966207
  · exact B966211
  · exact B966215
  · exact B966219
  · exact B966223
  · exact B966227
  · exact B966231
  · exact B966235
  · exact B966239
  · exact B966243
  · exact B966247
  · exact B966251
  · exact B966255
  · exact B966259
  · exact B966263
  · exact B966267
  · exact B966271
  · exact B966275
  · exact B966279
  · exact B966283
  · exact B966287
  · exact B966291
  · exact B966295
  · exact B966299
  · exact B966303
  · exact B966307
  · exact B966311
  · exact B966315
  · exact B966319
  · exact B966323
  · exact B966327
  · exact B966331
  · exact B966335
  · exact B966339
  · exact B966343
  · exact B966347
  · exact B966351
  · exact B966355
  · exact B966359
  · exact B966363
  · exact B966367
  · exact B966371
  · exact B966375
  · exact B966379
  · exact B966383
  · exact B966387
  · exact B966391
  · exact B966395
  · exact B966399
  · exact B966403
  · exact B966407
  · exact B966411
  · exact B966415
  · exact B966419
  · exact B966423
  · exact B966427
  · exact B966431
  · exact B966435
  · exact B966439
  · exact B966443
  · exact B966447
  · exact B966451
  · exact B966455
  · exact B966459
  · exact B966463
  · exact B966467
  · exact B966471
  · exact B966475
  · exact B966479
  · exact B966483
  · exact B966487
  · exact B966491
  · exact B966495
  · exact B966499
  · exact B966503
  · exact B966507
  · exact B966511
  · exact B966515
  · exact B966519
  · exact B966523
  · exact B966527
  · exact B966531
  · exact B966535
  · exact B966539
  · exact B966543
  · exact B966547
  · exact B966551
  · exact B966555
  · exact B966559
  · exact B966563
  · exact B966567
  · exact B966571
  · exact B966575
  · exact B966579
  · exact B966583
  · exact B966587
  · exact B966591
  · exact B966595
  · exact B966599
  · exact B966603
  · exact B966607
  · exact B966611
  · exact B966615
  · exact B966619
  · exact B966623
  · exact B966627
  · exact B966631
  · exact B966635
  · exact B966639
  · exact B966643
  · exact B966647
  · exact B966651
  · exact B966655
  · exact B966659
  · exact B966663
  · exact B966667
  · exact B966671
  · exact B966675
  · exact B966679
  · exact B966683
  · exact B966687
  · exact B966691
  · exact B966695
  · exact B966699
  · exact B966703
  · exact B966707
  · exact B966711
  · exact B966715
  · exact B966719
  · exact B966723
  · exact B966727
  · exact B966731
  · exact B966735
  · exact B966739
  · exact B966743
  · exact B966747
  · exact B966751
  · exact B966755
  · exact B966759
  · exact B966763
  · exact B966767
  · exact B966771
  · exact B966775
  · exact B966779
  · exact B966783
  · exact B966787
  · exact B966791
  · exact B966795
  · exact B966799
  · exact B966803
  · exact B966807
  · exact B966811
  · exact B966815
  · exact B966819
  · exact B966823
  · exact B966827
  · exact B966831
  · exact B966835
  · exact B966839
  · exact B966843
  · exact B966847
  · exact B966851
  · exact B966855
  · exact B966859
  · exact B966863
  · exact B966867
  · exact B966871
  · exact B966875
  · exact B966879
  · exact B966883
  · exact B966887
  · exact B966891
  · exact B966895
  · exact B966899
  · exact B966903
  · exact B966907
  · exact B966911
  · exact B966915
  · exact B966919
  · exact B966923
  · exact B966927
  · exact B966931
  · exact B966935
  · exact B966939
  · exact B966943
  · exact B966947
  · exact B966951
  · exact B966955
  · exact B966959
  · exact B966963
  · exact B966967
  · exact B966971
  · exact B966975
  · exact B966979
  · exact B966983
  · exact B966987
  · exact B966991
  · exact B966995
  · exact B966999
  · exact B967003
  · exact B967007
  · exact B967011
  · exact B967015
  · exact B967019
  · exact B967023
  · exact B967027
  · exact B967031
  · exact B967035
  · exact B967039
  · exact B967043
  · exact B967047
  · exact B967051
  · exact B967055
  · exact B967059
  · exact B967063
  · exact B967067
  · exact B967071
  · exact B967075
  · exact B967079
  · exact B967083
  · exact B967087
  · exact B967091
  · exact B967095
  · exact B967099
  · exact B967103
  · exact B967107
  · exact B967111
  · exact B967115
  · exact B967119
  · exact B967123
  · exact B967127
  · exact B967131
  · exact B967135
  · exact B967139
  · exact B967143
  · exact B967147
  · exact B967151
  · exact B967155
  · exact B967159
  · exact B967163
  · exact B967167
  · exact B967171
  · exact B967175
  · exact B967179
  · exact B967183
  · exact B967187
  · exact B967191
  · exact B967195
  · exact B967199
  · exact B967203
  · exact B967207
  · exact B967211
  · exact B967215
  · exact B967219
  · exact B967223
  · exact B967227
  · exact B967231
  · exact B967235
  · exact B967239
  · exact B967243
  · exact B967247
  · exact B967251
  · exact B967255
  · exact B967259
  · exact B967263
  · exact B967267
  · exact B967271
  · exact B967275
  · exact B967279
  · exact B967283
  · exact B967287
  · exact B967291
  · exact B967295
  · exact B967299
  · exact B967303
  · exact B967307
  · exact B967311
  · exact B967315
  · exact B967319
  · exact B967323
  · exact B967327
  · exact B967331
  · exact B967335
  · exact B967339
  · exact B967343
  · exact B967347
  · exact B967351
  · exact B967355
  · exact B967359
  · exact B967363
  · exact B967367
  · exact B967371
  · exact B967375
  · exact B967379
  · exact B967383
  · exact B967387

theorem C1 (j : ℕ) (h1 : 241847 ≤ j) (h2 : j ≤ 242146) : Blo 964590 (4 * j + 3) := by
  interval_cases j
  · exact B967391
  · exact B967395
  · exact B967399
  · exact B967403
  · exact B967407
  · exact B967411
  · exact B967415
  · exact B967419
  · exact B967423
  · exact B967427
  · exact B967431
  · exact B967435
  · exact B967439
  · exact B967443
  · exact B967447
  · exact B967451
  · exact B967455
  · exact B967459
  · exact B967463
  · exact B967467
  · exact B967471
  · exact B967475
  · exact B967479
  · exact B967483
  · exact B967487
  · exact B967491
  · exact B967495
  · exact B967499
  · exact B967503
  · exact B967507
  · exact B967511
  · exact B967515
  · exact B967519
  · exact B967523
  · exact B967527
  · exact B967531
  · exact B967535
  · exact B967539
  · exact B967543
  · exact B967547
  · exact B967551
  · exact B967555
  · exact B967559
  · exact B967563
  · exact B967567
  · exact B967571
  · exact B967575
  · exact B967579
  · exact B967583
  · exact B967587
  · exact B967591
  · exact B967595
  · exact B967599
  · exact B967603
  · exact B967607
  · exact B967611
  · exact B967615
  · exact B967619
  · exact B967623
  · exact B967627
  · exact B967631
  · exact B967635
  · exact B967639
  · exact B967643
  · exact B967647
  · exact B967651
  · exact B967655
  · exact B967659
  · exact B967663
  · exact B967667
  · exact B967671
  · exact B967675
  · exact B967679
  · exact B967683
  · exact B967687
  · exact B967691
  · exact B967695
  · exact B967699
  · exact B967703
  · exact B967707
  · exact B967711
  · exact B967715
  · exact B967719
  · exact B967723
  · exact B967727
  · exact B967731
  · exact B967735
  · exact B967739
  · exact B967743
  · exact B967747
  · exact B967751
  · exact B967755
  · exact B967759
  · exact B967763
  · exact B967767
  · exact B967771
  · exact B967775
  · exact B967779
  · exact B967783
  · exact B967787
  · exact B967791
  · exact B967795
  · exact B967799
  · exact B967803
  · exact B967807
  · exact B967811
  · exact B967815
  · exact B967819
  · exact B967823
  · exact B967827
  · exact B967831
  · exact B967835
  · exact B967839
  · exact B967843
  · exact B967847
  · exact B967851
  · exact B967855
  · exact B967859
  · exact B967863
  · exact B967867
  · exact B967871
  · exact B967875
  · exact B967879
  · exact B967883
  · exact B967887
  · exact B967891
  · exact B967895
  · exact B967899
  · exact B967903
  · exact B967907
  · exact B967911
  · exact B967915
  · exact B967919
  · exact B967923
  · exact B967927
  · exact B967931
  · exact B967935
  · exact B967939
  · exact B967943
  · exact B967947
  · exact B967951
  · exact B967955
  · exact B967959
  · exact B967963
  · exact B967967
  · exact B967971
  · exact B967975
  · exact B967979
  · exact B967983
  · exact B967987
  · exact B967991
  · exact B967995
  · exact B967999
  · exact B968003
  · exact B968007
  · exact B968011
  · exact B968015
  · exact B968019
  · exact B968023
  · exact B968027
  · exact B968031
  · exact B968035
  · exact B968039
  · exact B968043
  · exact B968047
  · exact B968051
  · exact B968055
  · exact B968059
  · exact B968063
  · exact B968067
  · exact B968071
  · exact B968075
  · exact B968079
  · exact B968083
  · exact B968087
  · exact B968091
  · exact B968095
  · exact B968099
  · exact B968103
  · exact B968107
  · exact B968111
  · exact B968115
  · exact B968119
  · exact B968123
  · exact B968127
  · exact B968131
  · exact B968135
  · exact B968139
  · exact B968143
  · exact B968147
  · exact B968151
  · exact B968155
  · exact B968159
  · exact B968163
  · exact B968167
  · exact B968171
  · exact B968175
  · exact B968179
  · exact B968183
  · exact B968187
  · exact B968191
  · exact B968195
  · exact B968199
  · exact B968203
  · exact B968207
  · exact B968211
  · exact B968215
  · exact B968219
  · exact B968223
  · exact B968227
  · exact B968231
  · exact B968235
  · exact B968239
  · exact B968243
  · exact B968247
  · exact B968251
  · exact B968255
  · exact B968259
  · exact B968263
  · exact B968267
  · exact B968271
  · exact B968275
  · exact B968279
  · exact B968283
  · exact B968287
  · exact B968291
  · exact B968295
  · exact B968299
  · exact B968303
  · exact B968307
  · exact B968311
  · exact B968315
  · exact B968319
  · exact B968323
  · exact B968327
  · exact B968331
  · exact B968335
  · exact B968339
  · exact B968343
  · exact B968347
  · exact B968351
  · exact B968355
  · exact B968359
  · exact B968363
  · exact B968367
  · exact B968371
  · exact B968375
  · exact B968379
  · exact B968383
  · exact B968387
  · exact B968391
  · exact B968395
  · exact B968399
  · exact B968403
  · exact B968407
  · exact B968411
  · exact B968415
  · exact B968419
  · exact B968423
  · exact B968427
  · exact B968431
  · exact B968435
  · exact B968439
  · exact B968443
  · exact B968447
  · exact B968451
  · exact B968455
  · exact B968459
  · exact B968463
  · exact B968467
  · exact B968471
  · exact B968475
  · exact B968479
  · exact B968483
  · exact B968487
  · exact B968491
  · exact B968495
  · exact B968499
  · exact B968503
  · exact B968507
  · exact B968511
  · exact B968515
  · exact B968519
  · exact B968523
  · exact B968527
  · exact B968531
  · exact B968535
  · exact B968539
  · exact B968543
  · exact B968547
  · exact B968551
  · exact B968555
  · exact B968559
  · exact B968563
  · exact B968567
  · exact B968571
  · exact B968575
  · exact B968579
  · exact B968583
  · exact B968587

theorem solution (m : ℕ) (hlo : 964590 ≤ m) (hhi : m ≤ 968590) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 241147 ≤ j := by omega
    have hj2 : j ≤ 242146 := by omega
    have hb : Blo 964590 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 241847 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
