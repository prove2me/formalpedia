-- Prove2me | solution 1 for syracuse_descends_range_159796_163796
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:41.920883+00:00
-- url     : https://prove2.me/submissions/9daf3bc7-e368-4925-b4ba-bb84a0db238c

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


theorem B360485 : Blo 159796 360485 := bbase (se 4 (by rfl) ⟨33795, by rfl⟩ : syracuseStep 360485 = 67591) (by norm_num)
theorem B524357 : Blo 159796 524357 := bbase (se 4 (by rfl) ⟨49158, by rfl⟩ : syracuseStep 524357 = 98317) (by norm_num)
theorem B360557 : Blo 159796 360557 := bbase (se 3 (by rfl) ⟨67604, by rfl⟩ : syracuseStep 360557 = 135209) (by norm_num)
theorem B229493 : Blo 159796 229493 := bbase (se 5 (by rfl) ⟨10757, by rfl⟩ : syracuseStep 229493 = 21515) (by norm_num)
theorem B360629 : Blo 159796 360629 := bbase (se 5 (by rfl) ⟨16904, by rfl⟩ : syracuseStep 360629 = 33809) (by norm_num)
theorem B524485 : Blo 159796 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B360701 : Blo 159796 360701 := bbase (se 3 (by rfl) ⟨67631, by rfl⟩ : syracuseStep 360701 = 135263) (by norm_num)
theorem B360773 : Blo 159796 360773 := bbase (se 4 (by rfl) ⟨33822, by rfl⟩ : syracuseStep 360773 = 67645) (by norm_num)
theorem B819557 : Blo 159796 819557 := bbase (se 4 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 819557 = 153667) (by norm_num)
theorem B360845 : Blo 159796 360845 := bbase (se 3 (by rfl) ⟨67658, by rfl⟩ : syracuseStep 360845 = 135317) (by norm_num)
theorem B360917 : Blo 159796 360917 := bbase (se 7 (by rfl) ⟨4229, by rfl⟩ : syracuseStep 360917 = 8459) (by norm_num)
theorem B360989 : Blo 159796 360989 := bbase (se 3 (by rfl) ⟨67685, by rfl⟩ : syracuseStep 360989 = 135371) (by norm_num)
theorem B787013 : Blo 159796 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B361061 : Blo 159796 361061 := bbase (se 4 (by rfl) ⟨33849, by rfl⟩ : syracuseStep 361061 = 67699) (by norm_num)
theorem B230045 : Blo 159796 230045 := bbase (se 3 (by rfl) ⟨43133, by rfl⟩ : syracuseStep 230045 = 86267) (by norm_num)
theorem B361133 : Blo 159796 361133 := bbase (se 3 (by rfl) ⟨67712, by rfl⟩ : syracuseStep 361133 = 135425) (by norm_num)
theorem B688837 : Blo 159796 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B361205 : Blo 159796 361205 := bbase (se 5 (by rfl) ⟨16931, by rfl⟩ : syracuseStep 361205 = 33863) (by norm_num)
theorem B361277 : Blo 159796 361277 := bbase (se 3 (by rfl) ⟨67739, by rfl⟩ : syracuseStep 361277 = 135479) (by norm_num)
theorem B459589 : Blo 159796 459589 := bbase (se 4 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 459589 = 86173) (by norm_num)
theorem B492389 : Blo 159796 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B361349 : Blo 159796 361349 := bbase (se 4 (by rfl) ⟨33876, by rfl⟩ : syracuseStep 361349 = 67753) (by norm_num)
theorem B656261 : Blo 159796 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B361421 : Blo 159796 361421 := bbase (se 3 (by rfl) ⟨67766, by rfl⟩ : syracuseStep 361421 = 135533) (by norm_num)
theorem B459749 : Blo 159796 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B361493 : Blo 159796 361493 := bbase (se 6 (by rfl) ⟨8472, by rfl⟩ : syracuseStep 361493 = 16945) (by norm_num)
theorem B394301 : Blo 159796 394301 := bbase (se 3 (by rfl) ⟨73931, by rfl⟩ : syracuseStep 394301 = 147863) (by norm_num)
theorem B361565 : Blo 159796 361565 := bbase (se 3 (by rfl) ⟨67793, by rfl⟩ : syracuseStep 361565 = 135587) (by norm_num)
theorem B361637 : Blo 159796 361637 := bbase (se 4 (by rfl) ⟨33903, by rfl⟩ : syracuseStep 361637 = 67807) (by norm_num)
theorem B459989 : Blo 159796 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B361709 : Blo 159796 361709 := bbase (se 3 (by rfl) ⟨67820, by rfl⟩ : syracuseStep 361709 = 135641) (by norm_num)
theorem B329005 : Blo 159796 329005 := bbase (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) (by norm_num)
theorem B361781 : Blo 159796 361781 := bbase (se 5 (by rfl) ⟨16958, by rfl⟩ : syracuseStep 361781 = 33917) (by norm_num)
theorem B361853 : Blo 159796 361853 := bbase (se 3 (by rfl) ⟨67847, by rfl⟩ : syracuseStep 361853 = 135695) (by norm_num)
theorem B230797 : Blo 159796 230797 := bbase (se 3 (by rfl) ⟨43274, by rfl⟩ : syracuseStep 230797 = 86549) (by norm_num)
theorem B460181 : Blo 159796 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B165281 : Blo 159796 165281 := bbase (se 2 (by rfl) ⟨61980, by rfl⟩ : syracuseStep 165281 = 123961) (by norm_num)
theorem B689573 : Blo 159796 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B361925 : Blo 159796 361925 := bbase (se 4 (by rfl) ⟨33930, by rfl⟩ : syracuseStep 361925 = 67861) (by norm_num)
theorem B361997 : Blo 159796 361997 := bbase (se 3 (by rfl) ⟨67874, by rfl⟩ : syracuseStep 361997 = 135749) (by norm_num)
theorem B362069 : Blo 159796 362069 := bbase (se 8 (by rfl) ⟨2121, by rfl⟩ : syracuseStep 362069 = 4243) (by norm_num)
theorem B820853 : Blo 159796 820853 := bbase (se 5 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 820853 = 76955) (by norm_num)
theorem B362141 : Blo 159796 362141 := bbase (se 3 (by rfl) ⟨67901, by rfl⟩ : syracuseStep 362141 = 135803) (by norm_num)
theorem B362213 : Blo 159796 362213 := bbase (se 4 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 362213 = 67915) (by norm_num)
theorem B362285 : Blo 159796 362285 := bbase (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) (by norm_num)
theorem B362357 : Blo 159796 362357 := bbase (se 5 (by rfl) ⟨16985, by rfl⟩ : syracuseStep 362357 = 33971) (by norm_num)
theorem B198577 : Blo 159796 198577 := bbase (se 2 (by rfl) ⟨74466, by rfl⟩ : syracuseStep 198577 = 148933) (by norm_num)
theorem B362429 : Blo 159796 362429 := bbase (se 3 (by rfl) ⟨67955, by rfl⟩ : syracuseStep 362429 = 135911) (by norm_num)
theorem B264149 : Blo 159796 264149 := bbase (se 7 (by rfl) ⟨3095, by rfl⟩ : syracuseStep 264149 = 6191) (by norm_num)
theorem B264173 : Blo 159796 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B362501 : Blo 159796 362501 := bbase (se 4 (by rfl) ⟨33984, by rfl⟩ : syracuseStep 362501 = 67969) (by norm_num)
theorem B395293 : Blo 159796 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B362573 : Blo 159796 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B821381 : Blo 159796 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B362645 : Blo 159796 362645 := bbase (se 6 (by rfl) ⟨8499, by rfl⟩ : syracuseStep 362645 = 16999) (by norm_num)
theorem B231589 : Blo 159796 231589 := bbase (se 4 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 231589 = 43423) (by norm_num)
theorem B362717 : Blo 159796 362717 := bbase (se 3 (by rfl) ⟨68009, by rfl⟩ : syracuseStep 362717 = 136019) (by norm_num)
theorem B362789 : Blo 159796 362789 := bbase (se 4 (by rfl) ⟨34011, by rfl⟩ : syracuseStep 362789 = 68023) (by norm_num)
theorem B559445 : Blo 159796 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B362861 : Blo 159796 362861 := bbase (se 3 (by rfl) ⟨68036, by rfl⟩ : syracuseStep 362861 = 136073) (by norm_num)
theorem B461173 : Blo 159796 461173 := bbase (se 5 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 461173 = 43235) (by norm_num)
theorem B362933 : Blo 159796 362933 := bbase (se 5 (by rfl) ⟨17012, by rfl⟩ : syracuseStep 362933 = 34025) (by norm_num)
theorem B231925 : Blo 159796 231925 := bbase (se 5 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 231925 = 21743) (by norm_num)
theorem B363005 : Blo 159796 363005 := bbase (se 3 (by rfl) ⟨68063, by rfl⟩ : syracuseStep 363005 = 136127) (by norm_num)
theorem B363077 : Blo 159796 363077 := bbase (se 4 (by rfl) ⟨34038, by rfl⟩ : syracuseStep 363077 = 68077) (by norm_num)
theorem B363149 : Blo 159796 363149 := bbase (se 3 (by rfl) ⟨68090, by rfl⟩ : syracuseStep 363149 = 136181) (by norm_num)
theorem B232141 : Blo 159796 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B363221 : Blo 159796 363221 := bbase (se 7 (by rfl) ⟨4256, by rfl⟩ : syracuseStep 363221 = 8513) (by norm_num)
theorem B363293 : Blo 159796 363293 := bbase (se 3 (by rfl) ⟨68117, by rfl⟩ : syracuseStep 363293 = 136235) (by norm_num)
theorem B363365 : Blo 159796 363365 := bbase (se 4 (by rfl) ⟨34065, by rfl⟩ : syracuseStep 363365 = 68131) (by norm_num)
theorem B822149 : Blo 159796 822149 := bbase (se 4 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 822149 = 154153) (by norm_num)
theorem B363437 : Blo 159796 363437 := bbase (se 3 (by rfl) ⟨68144, by rfl⟩ : syracuseStep 363437 = 136289) (by norm_num)
theorem B330725 : Blo 159796 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B363509 : Blo 159796 363509 := bbase (se 5 (by rfl) ⟨17039, by rfl⟩ : syracuseStep 363509 = 34079) (by norm_num)
theorem B363581 : Blo 159796 363581 := bbase (se 3 (by rfl) ⟨68171, by rfl⟩ : syracuseStep 363581 = 136343) (by norm_num)
theorem B232517 : Blo 159796 232517 := bbase (se 4 (by rfl) ⟨21798, by rfl⟩ : syracuseStep 232517 = 43597) (by norm_num)
theorem B363653 : Blo 159796 363653 := bbase (se 4 (by rfl) ⟨34092, by rfl⟩ : syracuseStep 363653 = 68185) (by norm_num)
theorem B363725 : Blo 159796 363725 := bbase (se 3 (by rfl) ⟨68198, by rfl⟩ : syracuseStep 363725 = 136397) (by norm_num)
theorem B363797 : Blo 159796 363797 := bbase (se 6 (by rfl) ⟨8526, by rfl⟩ : syracuseStep 363797 = 17053) (by norm_num)
theorem B658709 : Blo 159796 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B363869 : Blo 159796 363869 := bbase (se 3 (by rfl) ⟨68225, by rfl⟩ : syracuseStep 363869 = 136451) (by norm_num)
theorem B363941 : Blo 159796 363941 := bbase (se 4 (by rfl) ⟨34119, by rfl⟩ : syracuseStep 363941 = 68239) (by norm_num)
theorem B462277 : Blo 159796 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B364013 : Blo 159796 364013 := bbase (se 3 (by rfl) ⟨68252, by rfl⟩ : syracuseStep 364013 = 136505) (by norm_num)
theorem B1379861 : Blo 159796 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B364085 : Blo 159796 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B1248821 : Blo 159796 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B364157 : Blo 159796 364157 := bbase (se 3 (by rfl) ⟨68279, by rfl⟩ : syracuseStep 364157 = 136559) (by norm_num)
theorem B364229 : Blo 159796 364229 := bbase (se 4 (by rfl) ⟨34146, by rfl⟩ : syracuseStep 364229 = 68293) (by norm_num)
theorem B691973 : Blo 159796 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B167689 : Blo 159796 167689 := bbase (se 2 (by rfl) ⟨62883, by rfl⟩ : syracuseStep 167689 = 125767) (by norm_num)
theorem B364301 : Blo 159796 364301 := bbase (se 3 (by rfl) ⟨68306, by rfl⟩ : syracuseStep 364301 = 136613) (by norm_num)
theorem B921365 : Blo 159796 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B364373 : Blo 159796 364373 := bbase (se 9 (by rfl) ⟨1067, by rfl⟩ : syracuseStep 364373 = 2135) (by norm_num)
theorem B15109973 : Blo 159796 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B364445 : Blo 159796 364445 := bbase (se 3 (by rfl) ⟨68333, by rfl⟩ : syracuseStep 364445 = 136667) (by norm_num)
theorem B2625493 : Blo 159796 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B364517 : Blo 159796 364517 := bbase (se 4 (by rfl) ⟨34173, by rfl⟩ : syracuseStep 364517 = 68347) (by norm_num)
theorem B364589 : Blo 159796 364589 := bbase (se 3 (by rfl) ⟨68360, by rfl⟩ : syracuseStep 364589 = 136721) (by norm_num)
theorem B364661 : Blo 159796 364661 := bbase (se 5 (by rfl) ⟨17093, by rfl⟩ : syracuseStep 364661 = 34187) (by norm_num)
theorem B823445 : Blo 159796 823445 := bbase (se 6 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 823445 = 38599) (by norm_num)
theorem B364733 : Blo 159796 364733 := bbase (se 3 (by rfl) ⟨68387, by rfl⟩ : syracuseStep 364733 = 136775) (by norm_num)
theorem B364805 : Blo 159796 364805 := bbase (se 4 (by rfl) ⟨34200, by rfl⟩ : syracuseStep 364805 = 68401) (by norm_num)
theorem B1544501 : Blo 159796 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B364877 : Blo 159796 364877 := bbase (se 3 (by rfl) ⟨68414, by rfl⟩ : syracuseStep 364877 = 136829) (by norm_num)
theorem B627029 : Blo 159796 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B364949 : Blo 159796 364949 := bbase (se 6 (by rfl) ⟨8553, by rfl⟩ : syracuseStep 364949 = 17107) (by norm_num)
theorem B365021 : Blo 159796 365021 := bbase (se 3 (by rfl) ⟨68441, by rfl⟩ : syracuseStep 365021 = 136883) (by norm_num)
theorem B365093 : Blo 159796 365093 := bbase (se 4 (by rfl) ⟨34227, by rfl⟩ : syracuseStep 365093 = 68455) (by norm_num)
theorem B365165 : Blo 159796 365165 := bbase (se 3 (by rfl) ⟨68468, by rfl⟩ : syracuseStep 365165 = 136937) (by norm_num)
theorem B692869 : Blo 159796 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B365237 : Blo 159796 365237 := bbase (se 5 (by rfl) ⟨17120, by rfl⟩ : syracuseStep 365237 = 34241) (by norm_num)
theorem B365309 : Blo 159796 365309 := bbase (se 3 (by rfl) ⟨68495, by rfl⟩ : syracuseStep 365309 = 136991) (by norm_num)
theorem B365381 : Blo 159796 365381 := bbase (se 4 (by rfl) ⟨34254, by rfl⟩ : syracuseStep 365381 = 68509) (by norm_num)
theorem B529237 : Blo 159796 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B365453 : Blo 159796 365453 := bbase (se 3 (by rfl) ⟨68522, by rfl⟩ : syracuseStep 365453 = 137045) (by norm_num)
theorem B1217429 : Blo 159796 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B463781 : Blo 159796 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B922549 : Blo 159796 922549 := bbase (se 5 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 922549 = 86489) (by norm_num)
theorem B365525 : Blo 159796 365525 := bbase (se 7 (by rfl) ⟨4283, by rfl⟩ : syracuseStep 365525 = 8567) (by norm_num)
theorem B365597 : Blo 159796 365597 := bbase (se 3 (by rfl) ⟨68549, by rfl⟩ : syracuseStep 365597 = 137099) (by norm_num)
theorem B365669 : Blo 159796 365669 := bbase (se 4 (by rfl) ⟨34281, by rfl⟩ : syracuseStep 365669 = 68563) (by norm_num)
theorem B365741 : Blo 159796 365741 := bbase (se 3 (by rfl) ⟨68576, by rfl⟩ : syracuseStep 365741 = 137153) (by norm_num)
theorem B365789 : Blo 159796 365789 := bbase (se 3 (by rfl) ⟨68585, by rfl⟩ : syracuseStep 365789 = 137171) (by norm_num)
theorem B365813 : Blo 159796 365813 := bbase (se 5 (by rfl) ⟨17147, by rfl⟩ : syracuseStep 365813 = 34295) (by norm_num)
theorem B365885 : Blo 159796 365885 := bbase (se 3 (by rfl) ⟨68603, by rfl⟩ : syracuseStep 365885 = 137207) (by norm_num)
theorem B365957 : Blo 159796 365957 := bbase (se 4 (by rfl) ⟨34308, by rfl⟩ : syracuseStep 365957 = 68617) (by norm_num)
theorem B824741 : Blo 159796 824741 := bbase (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) (by norm_num)
theorem B366029 : Blo 159796 366029 := bbase (se 3 (by rfl) ⟨68630, by rfl⟩ : syracuseStep 366029 = 137261) (by norm_num)
theorem B366101 : Blo 159796 366101 := bbase (se 6 (by rfl) ⟨8580, by rfl⟩ : syracuseStep 366101 = 17161) (by norm_num)
theorem B202277 : Blo 159796 202277 := bbase (se 4 (by rfl) ⟨18963, by rfl⟩ : syracuseStep 202277 = 37927) (by norm_num)
theorem B202333 : Blo 159796 202333 := bbase (se 3 (by rfl) ⟨37937, by rfl⟩ : syracuseStep 202333 = 75875) (by norm_num)
theorem B366173 : Blo 159796 366173 := bbase (se 3 (by rfl) ⟨68657, by rfl⟩ : syracuseStep 366173 = 137315) (by norm_num)
theorem B366245 : Blo 159796 366245 := bbase (se 4 (by rfl) ⟨34335, by rfl⟩ : syracuseStep 366245 = 68671) (by norm_num)
theorem B202429 : Blo 159796 202429 := bbase (se 3 (by rfl) ⟨37955, by rfl⟩ : syracuseStep 202429 = 75911) (by norm_num)
theorem B235229 : Blo 159796 235229 := bbase (se 3 (by rfl) ⟨44105, by rfl⟩ : syracuseStep 235229 = 88211) (by norm_num)
theorem B366317 : Blo 159796 366317 := bbase (se 3 (by rfl) ⟨68684, by rfl⟩ : syracuseStep 366317 = 137369) (by norm_num)
theorem B890677 : Blo 159796 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B366389 : Blo 159796 366389 := bbase (se 5 (by rfl) ⟨17174, by rfl⟩ : syracuseStep 366389 = 34349) (by norm_num)
theorem B202601 : Blo 159796 202601 := bbase (se 2 (by rfl) ⟨75975, by rfl⟩ : syracuseStep 202601 = 151951) (by norm_num)
theorem B366461 : Blo 159796 366461 := bbase (se 3 (by rfl) ⟨68711, by rfl⟩ : syracuseStep 366461 = 137423) (by norm_num)
theorem B202657 : Blo 159796 202657 := bbase (se 2 (by rfl) ⟨75996, by rfl⟩ : syracuseStep 202657 = 151993) (by norm_num)
theorem B366533 : Blo 159796 366533 := bbase (se 4 (by rfl) ⟨34362, by rfl⟩ : syracuseStep 366533 = 68725) (by norm_num)
theorem B202753 : Blo 159796 202753 := bbase (se 2 (by rfl) ⟨76032, by rfl⟩ : syracuseStep 202753 = 152065) (by norm_num)
theorem B366605 : Blo 159796 366605 := bbase (se 3 (by rfl) ⟨68738, by rfl⟩ : syracuseStep 366605 = 137477) (by norm_num)
theorem B563221 : Blo 159796 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B366677 : Blo 159796 366677 := bbase (se 8 (by rfl) ⟨2148, by rfl⟩ : syracuseStep 366677 = 4297) (by norm_num)
theorem B366749 : Blo 159796 366749 := bbase (se 3 (by rfl) ⟨68765, by rfl⟩ : syracuseStep 366749 = 137531) (by norm_num)
theorem B202925 : Blo 159796 202925 := bbase (se 3 (by rfl) ⟨38048, by rfl⟩ : syracuseStep 202925 = 76097) (by norm_num)
theorem B202981 : Blo 159796 202981 := bbase (se 4 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 202981 = 38059) (by norm_num)
theorem B366821 : Blo 159796 366821 := bbase (se 4 (by rfl) ⟨34389, by rfl⟩ : syracuseStep 366821 = 68779) (by norm_num)
theorem B366893 : Blo 159796 366893 := bbase (se 3 (by rfl) ⟨68792, by rfl⟩ : syracuseStep 366893 = 137585) (by norm_num)
theorem B203077 : Blo 159796 203077 := bbase (se 4 (by rfl) ⟨19038, by rfl⟩ : syracuseStep 203077 = 38077) (by norm_num)
theorem B366965 : Blo 159796 366965 := bbase (se 5 (by rfl) ⟨17201, by rfl⟩ : syracuseStep 366965 = 34403) (by norm_num)
theorem B367037 : Blo 159796 367037 := bbase (se 3 (by rfl) ⟨68819, by rfl⟩ : syracuseStep 367037 = 137639) (by norm_num)
theorem B465365 : Blo 159796 465365 := bbase (se 7 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 465365 = 10907) (by norm_num)
theorem B203249 : Blo 159796 203249 := bbase (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) (by norm_num)
theorem B367109 : Blo 159796 367109 := bbase (se 4 (by rfl) ⟨34416, by rfl⟩ : syracuseStep 367109 = 68833) (by norm_num)
theorem B203305 : Blo 159796 203305 := bbase (se 2 (by rfl) ⟨76239, by rfl⟩ : syracuseStep 203305 = 152479) (by norm_num)
theorem B367181 : Blo 159796 367181 := bbase (se 3 (by rfl) ⟨68846, by rfl⟩ : syracuseStep 367181 = 137693) (by norm_num)
theorem B203401 : Blo 159796 203401 := bbase (se 2 (by rfl) ⟨76275, by rfl⟩ : syracuseStep 203401 = 152551) (by norm_num)
theorem B367253 : Blo 159796 367253 := bbase (se 6 (by rfl) ⟨8607, by rfl⟩ : syracuseStep 367253 = 17215) (by norm_num)
theorem B826037 : Blo 159796 826037 := bbase (se 5 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 826037 = 77441) (by norm_num)
theorem B367325 : Blo 159796 367325 := bbase (se 3 (by rfl) ⟨68873, by rfl⟩ : syracuseStep 367325 = 137747) (by norm_num)
theorem B170753 : Blo 159796 170753 := bbase (se 2 (by rfl) ⟨64032, by rfl⟩ : syracuseStep 170753 = 128065) (by norm_num)
theorem B367397 : Blo 159796 367397 := bbase (se 4 (by rfl) ⟨34443, by rfl⟩ : syracuseStep 367397 = 68887) (by norm_num)
theorem B203573 : Blo 159796 203573 := bbase (se 5 (by rfl) ⟨9542, by rfl⟩ : syracuseStep 203573 = 19085) (by norm_num)
theorem B662357 : Blo 159796 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B203629 : Blo 159796 203629 := bbase (se 3 (by rfl) ⟨38180, by rfl⟩ : syracuseStep 203629 = 76361) (by norm_num)
theorem B367469 : Blo 159796 367469 := bbase (se 3 (by rfl) ⟨68900, by rfl⟩ : syracuseStep 367469 = 137801) (by norm_num)
theorem B924533 : Blo 159796 924533 := bbase (se 5 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 924533 = 86675) (by norm_num)
theorem B1579925 : Blo 159796 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B367541 : Blo 159796 367541 := bbase (se 5 (by rfl) ⟨17228, by rfl⟩ : syracuseStep 367541 = 34457) (by norm_num)
theorem B203725 : Blo 159796 203725 := bbase (se 3 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 203725 = 76397) (by norm_num)
theorem B367613 : Blo 159796 367613 := bbase (se 3 (by rfl) ⟨68927, by rfl⟩ : syracuseStep 367613 = 137855) (by norm_num)
theorem B662581 : Blo 159796 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B367685 : Blo 159796 367685 := bbase (se 4 (by rfl) ⟨34470, by rfl⟩ : syracuseStep 367685 = 68941) (by norm_num)
theorem B826453 : Blo 159796 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B466037 : Blo 159796 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B203897 : Blo 159796 203897 := bbase (se 2 (by rfl) ⟨76461, by rfl⟩ : syracuseStep 203897 = 152923) (by norm_num)
theorem B367757 : Blo 159796 367757 := bbase (se 3 (by rfl) ⟨68954, by rfl⟩ : syracuseStep 367757 = 137909) (by norm_num)
theorem B203953 : Blo 159796 203953 := bbase (se 2 (by rfl) ⟨76482, by rfl⟩ : syracuseStep 203953 = 152965) (by norm_num)
theorem B367829 : Blo 159796 367829 := bbase (se 7 (by rfl) ⟨4310, by rfl⟩ : syracuseStep 367829 = 8621) (by norm_num)
theorem B204049 : Blo 159796 204049 := bbase (se 2 (by rfl) ⟨76518, by rfl⟩ : syracuseStep 204049 = 153037) (by norm_num)
theorem B367901 : Blo 159796 367901 := bbase (se 3 (by rfl) ⟨68981, by rfl⟩ : syracuseStep 367901 = 137963) (by norm_num)
theorem B269669 : Blo 159796 269669 := bbase (se 4 (by rfl) ⟨25281, by rfl⟩ : syracuseStep 269669 = 50563) (by norm_num)
theorem B367973 : Blo 159796 367973 := bbase (se 4 (by rfl) ⟨34497, by rfl⟩ : syracuseStep 367973 = 68995) (by norm_num)
theorem B368045 : Blo 159796 368045 := bbase (se 3 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 368045 = 138017) (by norm_num)
theorem B204221 : Blo 159796 204221 := bbase (se 3 (by rfl) ⟨38291, by rfl⟩ : syracuseStep 204221 = 76583) (by norm_num)
theorem B269797 : Blo 159796 269797 := bbase (se 4 (by rfl) ⟨25293, by rfl⟩ : syracuseStep 269797 = 50587) (by norm_num)
theorem B433637 : Blo 159796 433637 := bbase (se 4 (by rfl) ⟨40653, by rfl⟩ : syracuseStep 433637 = 81307) (by norm_num)
theorem B171505 : Blo 159796 171505 := bbase (se 2 (by rfl) ⟨64314, by rfl⟩ : syracuseStep 171505 = 128629) (by norm_num)
theorem B204277 : Blo 159796 204277 := bbase (se 5 (by rfl) ⟨9575, by rfl⟩ : syracuseStep 204277 = 19151) (by norm_num)
theorem B368117 : Blo 159796 368117 := bbase (se 5 (by rfl) ⟨17255, by rfl⟩ : syracuseStep 368117 = 34511) (by norm_num)
theorem B695861 : Blo 159796 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B171577 : Blo 159796 171577 := bbase (se 2 (by rfl) ⟨64341, by rfl⟩ : syracuseStep 171577 = 128683) (by norm_num)
theorem B269885 : Blo 159796 269885 := bbase (se 3 (by rfl) ⟨50603, by rfl⟩ : syracuseStep 269885 = 101207) (by norm_num)
theorem B368189 : Blo 159796 368189 := bbase (se 3 (by rfl) ⟨69035, by rfl⟩ : syracuseStep 368189 = 138071) (by norm_num)
theorem B204373 : Blo 159796 204373 := bbase (se 8 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 204373 = 2395) (by norm_num)
theorem B368261 : Blo 159796 368261 := bbase (se 4 (by rfl) ⟨34524, by rfl⟩ : syracuseStep 368261 = 69049) (by norm_num)
theorem B1482421 : Blo 159796 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B270013 : Blo 159796 270013 := bbase (se 3 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 270013 = 101255) (by norm_num)
theorem B368333 : Blo 159796 368333 := bbase (se 3 (by rfl) ⟨69062, by rfl⟩ : syracuseStep 368333 = 138125) (by norm_num)
theorem B171757 : Blo 159796 171757 := bbase (se 3 (by rfl) ⟨32204, by rfl⟩ : syracuseStep 171757 = 64409) (by norm_num)
theorem B204545 : Blo 159796 204545 := bbase (se 2 (by rfl) ⟨76704, by rfl⟩ : syracuseStep 204545 = 153409) (by norm_num)
theorem B270101 : Blo 159796 270101 := bbase (se 6 (by rfl) ⟨6330, by rfl⟩ : syracuseStep 270101 = 12661) (by norm_num)
theorem B368405 : Blo 159796 368405 := bbase (se 6 (by rfl) ⟨8634, by rfl⟩ : syracuseStep 368405 = 17269) (by norm_num)
theorem B204601 : Blo 159796 204601 := bbase (se 2 (by rfl) ⟨76725, by rfl⟩ : syracuseStep 204601 = 153451) (by norm_num)
theorem B368477 : Blo 159796 368477 := bbase (se 3 (by rfl) ⟨69089, by rfl⟩ : syracuseStep 368477 = 138179) (by norm_num)
theorem B270229 : Blo 159796 270229 := bbase (se 6 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 270229 = 12667) (by norm_num)
theorem B434069 : Blo 159796 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B204697 : Blo 159796 204697 := bbase (se 2 (by rfl) ⟨76761, by rfl⟩ : syracuseStep 204697 = 153523) (by norm_num)
theorem B827333 : Blo 159796 827333 := bbase (se 4 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 827333 = 155125) (by norm_num)
theorem B270317 : Blo 159796 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B204869 : Blo 159796 204869 := bbase (se 4 (by rfl) ⟨19206, by rfl⟩ : syracuseStep 204869 = 38413) (by norm_num)
theorem B270445 : Blo 159796 270445 := bbase (se 3 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 270445 = 101417) (by norm_num)
theorem B204925 : Blo 159796 204925 := bbase (se 3 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 204925 = 76847) (by norm_num)
theorem B172201 : Blo 159796 172201 := bbase (se 2 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 172201 = 129151) (by norm_num)
theorem B270533 : Blo 159796 270533 := bbase (se 4 (by rfl) ⟨25362, by rfl⟩ : syracuseStep 270533 = 50725) (by norm_num)
theorem B205021 : Blo 159796 205021 := bbase (se 3 (by rfl) ⟨38441, by rfl⟩ : syracuseStep 205021 = 76883) (by norm_num)
theorem B172325 : Blo 159796 172325 := bbase (se 4 (by rfl) ⟨16155, by rfl⟩ : syracuseStep 172325 = 32311) (by norm_num)
theorem B270661 : Blo 159796 270661 := bbase (se 4 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 270661 = 50749) (by norm_num)
theorem B205193 : Blo 159796 205193 := bbase (se 2 (by rfl) ⟨76947, by rfl⟩ : syracuseStep 205193 = 153895) (by norm_num)
theorem B270749 : Blo 159796 270749 := bbase (se 3 (by rfl) ⟨50765, by rfl⟩ : syracuseStep 270749 = 101531) (by norm_num)
theorem B205249 : Blo 159796 205249 := bbase (se 2 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 205249 = 153937) (by norm_num)
theorem B205301 : Blo 159796 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B270877 : Blo 159796 270877 := bbase (se 3 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 270877 = 101579) (by norm_num)
theorem B172577 : Blo 159796 172577 := bbase (se 2 (by rfl) ⟨64716, by rfl⟩ : syracuseStep 172577 = 129433) (by norm_num)
theorem B205345 : Blo 159796 205345 := bbase (se 2 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 205345 = 154009) (by norm_num)
theorem B696869 : Blo 159796 696869 := bbase (se 4 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 696869 = 130663) (by norm_num)
theorem B1679957 : Blo 159796 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B270965 : Blo 159796 270965 := bbase (se 5 (by rfl) ⟨12701, by rfl⟩ : syracuseStep 270965 = 25403) (by norm_num)
theorem B205517 : Blo 159796 205517 := bbase (se 3 (by rfl) ⟨38534, by rfl⟩ : syracuseStep 205517 = 77069) (by norm_num)
theorem B271093 : Blo 159796 271093 := bbase (se 5 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 271093 = 25415) (by norm_num)
theorem B205573 : Blo 159796 205573 := bbase (se 4 (by rfl) ⟨19272, by rfl⟩ : syracuseStep 205573 = 38545) (by norm_num)
theorem B303925 : Blo 159796 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B271181 : Blo 159796 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B205669 : Blo 159796 205669 := bbase (se 4 (by rfl) ⟨19281, by rfl⟩ : syracuseStep 205669 = 38563) (by norm_num)
theorem B304069 : Blo 159796 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B271309 : Blo 159796 271309 := bbase (se 3 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 271309 = 101741) (by norm_num)
theorem B173021 : Blo 159796 173021 := bbase (se 3 (by rfl) ⟨32441, by rfl⟩ : syracuseStep 173021 = 64883) (by norm_num)
theorem B205841 : Blo 159796 205841 := bbase (se 2 (by rfl) ⟨77190, by rfl⟩ : syracuseStep 205841 = 154381) (by norm_num)
theorem B926741 : Blo 159796 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B271397 : Blo 159796 271397 := bbase (se 4 (by rfl) ⟨25443, by rfl⟩ : syracuseStep 271397 = 50887) (by norm_num)
theorem B205897 : Blo 159796 205897 := bbase (se 2 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 205897 = 154423) (by norm_num)
theorem B1647701 : Blo 159796 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B304229 : Blo 159796 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B271525 : Blo 159796 271525 := bbase (se 4 (by rfl) ⟨25455, by rfl⟩ : syracuseStep 271525 = 50911) (by norm_num)
theorem B205993 : Blo 159796 205993 := bbase (se 2 (by rfl) ⟨77247, by rfl⟩ : syracuseStep 205993 = 154495) (by norm_num)
theorem B173269 : Blo 159796 173269 := bbase (se 7 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 173269 = 4061) (by norm_num)
theorem B828629 : Blo 159796 828629 := bbase (se 7 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 828629 = 19421) (by norm_num)
theorem B304373 : Blo 159796 304373 := bbase (se 5 (by rfl) ⟨14267, by rfl⟩ : syracuseStep 304373 = 28535) (by norm_num)
theorem B271613 : Blo 159796 271613 := bbase (se 3 (by rfl) ⟨50927, by rfl⟩ : syracuseStep 271613 = 101855) (by norm_num)
theorem B206165 : Blo 159796 206165 := bbase (se 12 (by rfl) ⟨75, by rfl⟩ : syracuseStep 206165 = 151) (by norm_num)
theorem B664949 : Blo 159796 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B271741 : Blo 159796 271741 := bbase (se 3 (by rfl) ⟨50951, by rfl⟩ : syracuseStep 271741 = 101903) (by norm_num)
theorem B206221 : Blo 159796 206221 := bbase (se 3 (by rfl) ⟨38666, by rfl⟩ : syracuseStep 206221 = 77333) (by norm_num)
theorem B271829 : Blo 159796 271829 := bbase (se 7 (by rfl) ⟨3185, by rfl⟩ : syracuseStep 271829 = 6371) (by norm_num)
theorem B206317 : Blo 159796 206317 := bbase (se 3 (by rfl) ⟨38684, by rfl⟩ : syracuseStep 206317 = 77369) (by norm_num)
theorem B304661 : Blo 159796 304661 := bbase (se 6 (by rfl) ⟨7140, by rfl⟩ : syracuseStep 304661 = 14281) (by norm_num)
theorem B1025621 : Blo 159796 1025621 := bbase (se 8 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 1025621 = 12019) (by norm_num)
theorem B271957 : Blo 159796 271957 := bbase (se 8 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 271957 = 3187) (by norm_num)
theorem B173713 : Blo 159796 173713 := bbase (se 2 (by rfl) ⟨65142, by rfl⟩ : syracuseStep 173713 = 130285) (by norm_num)
theorem B206489 : Blo 159796 206489 := bbase (se 2 (by rfl) ⟨77433, by rfl⟩ : syracuseStep 206489 = 154867) (by norm_num)
theorem B304813 : Blo 159796 304813 := bbase (se 3 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 304813 = 114305) (by norm_num)
theorem B272045 : Blo 159796 272045 := bbase (se 3 (by rfl) ⟨51008, by rfl⟩ : syracuseStep 272045 = 102017) (by norm_num)
theorem B173773 : Blo 159796 173773 := bbase (se 3 (by rfl) ⟨32582, by rfl⟩ : syracuseStep 173773 = 65165) (by norm_num)
theorem B206545 : Blo 159796 206545 := bbase (se 2 (by rfl) ⟨77454, by rfl⟩ : syracuseStep 206545 = 154909) (by norm_num)
theorem B272173 : Blo 159796 272173 := bbase (se 3 (by rfl) ⟨51032, by rfl⟩ : syracuseStep 272173 = 102065) (by norm_num)
theorem B206641 : Blo 159796 206641 := bbase (se 2 (by rfl) ⟨77490, by rfl⟩ : syracuseStep 206641 = 154981) (by norm_num)
theorem B272261 : Blo 159796 272261 := bbase (se 4 (by rfl) ⟨25524, by rfl⟩ : syracuseStep 272261 = 51049) (by norm_num)
theorem B305117 : Blo 159796 305117 := bbase (se 3 (by rfl) ⟨57209, by rfl⟩ : syracuseStep 305117 = 114419) (by norm_num)
theorem B206813 : Blo 159796 206813 := bbase (se 3 (by rfl) ⟨38777, by rfl⟩ : syracuseStep 206813 = 77555) (by norm_num)
theorem B272389 : Blo 159796 272389 := bbase (se 4 (by rfl) ⟨25536, by rfl⟩ : syracuseStep 272389 = 51073) (by norm_num)
theorem B174089 : Blo 159796 174089 := bbase (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) (by norm_num)
theorem B206869 : Blo 159796 206869 := bbase (se 6 (by rfl) ⟨4848, by rfl⟩ : syracuseStep 206869 = 9697) (by norm_num)
theorem B272477 : Blo 159796 272477 := bbase (se 3 (by rfl) ⟨51089, by rfl⟩ : syracuseStep 272477 = 102179) (by norm_num)
theorem B239717 : Blo 159796 239717 := bbase (se 4 (by rfl) ⟨22473, by rfl⟩ : syracuseStep 239717 = 44947) (by norm_num)
theorem B206965 : Blo 159796 206965 := bbase (se 5 (by rfl) ⟨9701, by rfl⟩ : syracuseStep 206965 = 19403) (by norm_num)
theorem B239741 : Blo 159796 239741 := bbase (se 3 (by rfl) ⟨44951, by rfl⟩ : syracuseStep 239741 = 89903) (by norm_num)
theorem B239765 : Blo 159796 239765 := bbase (se 6 (by rfl) ⟨5619, by rfl⟩ : syracuseStep 239765 = 11239) (by norm_num)
theorem B239789 : Blo 159796 239789 := bbase (se 3 (by rfl) ⟨44960, by rfl⟩ : syracuseStep 239789 = 89921) (by norm_num)
theorem B239813 : Blo 159796 239813 := bbase (se 4 (by rfl) ⟨22482, by rfl⟩ : syracuseStep 239813 = 44965) (by norm_num)
theorem B239837 : Blo 159796 239837 := bbase (se 3 (by rfl) ⟨44969, by rfl⟩ : syracuseStep 239837 = 89939) (by norm_num)
theorem B272605 : Blo 159796 272605 := bbase (se 3 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 272605 = 102227) (by norm_num)
theorem B239861 : Blo 159796 239861 := bbase (se 5 (by rfl) ⟨11243, by rfl⟩ : syracuseStep 239861 = 22487) (by norm_num)
theorem B239885 : Blo 159796 239885 := bbase (se 3 (by rfl) ⟨44978, by rfl⟩ : syracuseStep 239885 = 89957) (by norm_num)
theorem B698645 : Blo 159796 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B207137 : Blo 159796 207137 := bbase (se 2 (by rfl) ⟨77676, by rfl⟩ : syracuseStep 207137 = 155353) (by norm_num)
theorem B239909 : Blo 159796 239909 := bbase (se 4 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 239909 = 44983) (by norm_num)
theorem B272693 : Blo 159796 272693 := bbase (se 5 (by rfl) ⟨12782, by rfl⟩ : syracuseStep 272693 = 25565) (by norm_num)
theorem B239933 : Blo 159796 239933 := bbase (se 3 (by rfl) ⟨44987, by rfl⟩ : syracuseStep 239933 = 89975) (by norm_num)
theorem B239957 : Blo 159796 239957 := bbase (se 10 (by rfl) ⟨351, by rfl⟩ : syracuseStep 239957 = 703) (by norm_num)
theorem B207193 : Blo 159796 207193 := bbase (se 2 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 207193 = 155395) (by norm_num)
theorem B239981 : Blo 159796 239981 := bbase (se 3 (by rfl) ⟨44996, by rfl⟩ : syracuseStep 239981 = 89993) (by norm_num)
theorem B240005 : Blo 159796 240005 := bbase (se 4 (by rfl) ⟨22500, by rfl⟩ : syracuseStep 240005 = 45001) (by norm_num)
theorem B2337173 : Blo 159796 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B240029 : Blo 159796 240029 := bbase (se 3 (by rfl) ⟨45005, by rfl⟩ : syracuseStep 240029 = 90011) (by norm_num)
theorem B240053 : Blo 159796 240053 := bbase (se 5 (by rfl) ⟨11252, by rfl⟩ : syracuseStep 240053 = 22505) (by norm_num)
theorem B272821 : Blo 159796 272821 := bbase (se 5 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 272821 = 25577) (by norm_num)
theorem B207289 : Blo 159796 207289 := bbase (se 2 (by rfl) ⟨77733, by rfl⟩ : syracuseStep 207289 = 155467) (by norm_num)
theorem B174533 : Blo 159796 174533 := bbase (se 4 (by rfl) ⟨16362, by rfl⟩ : syracuseStep 174533 = 32725) (by norm_num)
theorem B240077 : Blo 159796 240077 := bbase (se 3 (by rfl) ⟨45014, by rfl⟩ : syracuseStep 240077 = 90029) (by norm_num)
theorem B240101 : Blo 159796 240101 := bbase (se 4 (by rfl) ⟨22509, by rfl⟩ : syracuseStep 240101 = 45019) (by norm_num)
theorem B240125 : Blo 159796 240125 := bbase (se 3 (by rfl) ⟨45023, by rfl⟩ : syracuseStep 240125 = 90047) (by norm_num)
theorem B174593 : Blo 159796 174593 := bbase (se 2 (by rfl) ⟨65472, by rfl⟩ : syracuseStep 174593 = 130945) (by norm_num)
theorem B272909 : Blo 159796 272909 := bbase (se 3 (by rfl) ⟨51170, by rfl⟩ : syracuseStep 272909 = 102341) (by norm_num)
theorem B240149 : Blo 159796 240149 := bbase (se 6 (by rfl) ⟨5628, by rfl⟩ : syracuseStep 240149 = 11257) (by norm_num)
theorem B240173 : Blo 159796 240173 := bbase (se 3 (by rfl) ⟨45032, by rfl⟩ : syracuseStep 240173 = 90065) (by norm_num)
theorem B240197 : Blo 159796 240197 := bbase (se 4 (by rfl) ⟨22518, by rfl⟩ : syracuseStep 240197 = 45037) (by norm_num)
theorem B240221 : Blo 159796 240221 := bbase (se 3 (by rfl) ⟨45041, by rfl⟩ : syracuseStep 240221 = 90083) (by norm_num)
theorem B240245 : Blo 159796 240245 := bbase (se 5 (by rfl) ⟨11261, by rfl⟩ : syracuseStep 240245 = 22523) (by norm_num)
theorem B371317 : Blo 159796 371317 := bbase (se 5 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 371317 = 34811) (by norm_num)
theorem B174721 : Blo 159796 174721 := bbase (se 2 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 174721 = 131041) (by norm_num)
theorem B240269 : Blo 159796 240269 := bbase (se 3 (by rfl) ⟨45050, by rfl⟩ : syracuseStep 240269 = 90101) (by norm_num)
theorem B273037 : Blo 159796 273037 := bbase (se 3 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 273037 = 102389) (by norm_num)
theorem B240293 : Blo 159796 240293 := bbase (se 4 (by rfl) ⟨22527, by rfl⟩ : syracuseStep 240293 = 45055) (by norm_num)
theorem B240317 : Blo 159796 240317 := bbase (se 3 (by rfl) ⟨45059, by rfl⟩ : syracuseStep 240317 = 90119) (by norm_num)
theorem B404165 : Blo 159796 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B305869 : Blo 159796 305869 := bbase (se 3 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 305869 = 114701) (by norm_num)
theorem B240341 : Blo 159796 240341 := bbase (se 7 (by rfl) ⟨2816, by rfl⟩ : syracuseStep 240341 = 5633) (by norm_num)
theorem B273125 : Blo 159796 273125 := bbase (se 4 (by rfl) ⟨25605, by rfl⟩ : syracuseStep 273125 = 51211) (by norm_num)
theorem B240365 : Blo 159796 240365 := bbase (se 3 (by rfl) ⟨45068, by rfl⟩ : syracuseStep 240365 = 90137) (by norm_num)
theorem B240389 : Blo 159796 240389 := bbase (se 4 (by rfl) ⟨22536, by rfl⟩ : syracuseStep 240389 = 45073) (by norm_num)
theorem B240413 : Blo 159796 240413 := bbase (se 3 (by rfl) ⟨45077, by rfl⟩ : syracuseStep 240413 = 90155) (by norm_num)
theorem B240437 : Blo 159796 240437 := bbase (se 5 (by rfl) ⟨11270, by rfl⟩ : syracuseStep 240437 = 22541) (by norm_num)
theorem B240461 : Blo 159796 240461 := bbase (se 3 (by rfl) ⟨45086, by rfl⟩ : syracuseStep 240461 = 90173) (by norm_num)
theorem B306013 : Blo 159796 306013 := bbase (se 3 (by rfl) ⟨57377, by rfl⟩ : syracuseStep 306013 = 114755) (by norm_num)
theorem B240485 : Blo 159796 240485 := bbase (se 4 (by rfl) ⟨22545, by rfl⟩ : syracuseStep 240485 = 45091) (by norm_num)
theorem B273253 : Blo 159796 273253 := bbase (se 4 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 273253 = 51235) (by norm_num)
theorem B240509 : Blo 159796 240509 := bbase (se 3 (by rfl) ⟨45095, by rfl⟩ : syracuseStep 240509 = 90191) (by norm_num)
theorem B240533 : Blo 159796 240533 := bbase (se 6 (by rfl) ⟨5637, by rfl⟩ : syracuseStep 240533 = 11275) (by norm_num)
theorem B732053 : Blo 159796 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B240557 : Blo 159796 240557 := bbase (se 3 (by rfl) ⟨45104, by rfl⟩ : syracuseStep 240557 = 90209) (by norm_num)
theorem B273341 : Blo 159796 273341 := bbase (se 3 (by rfl) ⟨51251, by rfl⟩ : syracuseStep 273341 = 102503) (by norm_num)
theorem B240581 : Blo 159796 240581 := bbase (se 4 (by rfl) ⟨22554, by rfl⟩ : syracuseStep 240581 = 45109) (by norm_num)
theorem B240605 : Blo 159796 240605 := bbase (se 3 (by rfl) ⟨45113, by rfl⟩ : syracuseStep 240605 = 90227) (by norm_num)
theorem B240629 : Blo 159796 240629 := bbase (se 5 (by rfl) ⟨11279, by rfl⟩ : syracuseStep 240629 = 22559) (by norm_num)
theorem B306173 : Blo 159796 306173 := bbase (se 3 (by rfl) ⟨57407, by rfl⟩ : syracuseStep 306173 = 114815) (by norm_num)
theorem B240653 : Blo 159796 240653 := bbase (se 3 (by rfl) ⟨45122, by rfl⟩ : syracuseStep 240653 = 90245) (by norm_num)
theorem B240677 : Blo 159796 240677 := bbase (se 4 (by rfl) ⟨22563, by rfl⟩ : syracuseStep 240677 = 45127) (by norm_num)
theorem B240701 : Blo 159796 240701 := bbase (se 3 (by rfl) ⟨45131, by rfl⟩ : syracuseStep 240701 = 90263) (by norm_num)
theorem B273469 : Blo 159796 273469 := bbase (se 3 (by rfl) ⟨51275, by rfl⟩ : syracuseStep 273469 = 102551) (by norm_num)
theorem B371773 : Blo 159796 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B240725 : Blo 159796 240725 := bbase (se 8 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 240725 = 2821) (by norm_num)
theorem B207973 : Blo 159796 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B240749 : Blo 159796 240749 := bbase (se 3 (by rfl) ⟨45140, by rfl⟩ : syracuseStep 240749 = 90281) (by norm_num)
theorem B240773 : Blo 159796 240773 := bbase (se 4 (by rfl) ⟨22572, by rfl⟩ : syracuseStep 240773 = 45145) (by norm_num)
theorem B306317 : Blo 159796 306317 := bbase (se 3 (by rfl) ⟨57434, by rfl⟩ : syracuseStep 306317 = 114869) (by norm_num)
theorem B273557 : Blo 159796 273557 := bbase (se 6 (by rfl) ⟨6411, by rfl⟩ : syracuseStep 273557 = 12823) (by norm_num)
theorem B240797 : Blo 159796 240797 := bbase (se 3 (by rfl) ⟨45149, by rfl⟩ : syracuseStep 240797 = 90299) (by norm_num)
theorem B240821 : Blo 159796 240821 := bbase (se 5 (by rfl) ⟨11288, by rfl⟩ : syracuseStep 240821 = 22577) (by norm_num)
theorem B240845 : Blo 159796 240845 := bbase (se 3 (by rfl) ⟨45158, by rfl⟩ : syracuseStep 240845 = 90317) (by norm_num)
theorem B240869 : Blo 159796 240869 := bbase (se 4 (by rfl) ⟨22581, by rfl⟩ : syracuseStep 240869 = 45163) (by norm_num)
theorem B240893 : Blo 159796 240893 := bbase (se 3 (by rfl) ⟨45167, by rfl⟩ : syracuseStep 240893 = 90335) (by norm_num)
theorem B240917 : Blo 159796 240917 := bbase (se 6 (by rfl) ⟨5646, by rfl⟩ : syracuseStep 240917 = 11293) (by norm_num)
theorem B273685 : Blo 159796 273685 := bbase (se 6 (by rfl) ⟨6414, by rfl⟩ : syracuseStep 273685 = 12829) (by norm_num)
theorem B240941 : Blo 159796 240941 := bbase (se 3 (by rfl) ⟨45176, by rfl⟩ : syracuseStep 240941 = 90353) (by norm_num)
theorem B404797 : Blo 159796 404797 := bbase (se 3 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 404797 = 151799) (by norm_num)
theorem B240965 : Blo 159796 240965 := bbase (se 4 (by rfl) ⟨22590, by rfl⟩ : syracuseStep 240965 = 45181) (by norm_num)
theorem B240989 : Blo 159796 240989 := bbase (se 3 (by rfl) ⟨45185, by rfl⟩ : syracuseStep 240989 = 90371) (by norm_num)
theorem B273773 : Blo 159796 273773 := bbase (se 3 (by rfl) ⟨51332, by rfl⟩ : syracuseStep 273773 = 102665) (by norm_num)
theorem B241013 : Blo 159796 241013 := bbase (se 5 (by rfl) ⟨11297, by rfl⟩ : syracuseStep 241013 = 22595) (by norm_num)
theorem B241037 : Blo 159796 241037 := bbase (se 3 (by rfl) ⟨45194, by rfl⟩ : syracuseStep 241037 = 90389) (by norm_num)
theorem B1387925 : Blo 159796 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B241061 : Blo 159796 241061 := bbase (se 4 (by rfl) ⟨22599, by rfl⟩ : syracuseStep 241061 = 45199) (by norm_num)
theorem B404909 : Blo 159796 404909 := bbase (se 3 (by rfl) ⟨75920, by rfl⟩ : syracuseStep 404909 = 151841) (by norm_num)
theorem B306605 : Blo 159796 306605 := bbase (se 3 (by rfl) ⟨57488, by rfl⟩ : syracuseStep 306605 = 114977) (by norm_num)
theorem B241085 : Blo 159796 241085 := bbase (se 3 (by rfl) ⟨45203, by rfl⟩ : syracuseStep 241085 = 90407) (by norm_num)
theorem B241109 : Blo 159796 241109 := bbase (se 7 (by rfl) ⟨2825, by rfl⟩ : syracuseStep 241109 = 5651) (by norm_num)
theorem B241133 : Blo 159796 241133 := bbase (se 3 (by rfl) ⟨45212, by rfl⟩ : syracuseStep 241133 = 90425) (by norm_num)
theorem B273901 : Blo 159796 273901 := bbase (se 3 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 273901 = 102713) (by norm_num)
theorem B241157 : Blo 159796 241157 := bbase (se 4 (by rfl) ⟨22608, by rfl⟩ : syracuseStep 241157 = 45217) (by norm_num)
theorem B241181 : Blo 159796 241181 := bbase (se 3 (by rfl) ⟨45221, by rfl⟩ : syracuseStep 241181 = 90443) (by norm_num)
theorem B241205 : Blo 159796 241205 := bbase (se 5 (by rfl) ⟨11306, by rfl⟩ : syracuseStep 241205 = 22613) (by norm_num)
theorem B306757 : Blo 159796 306757 := bbase (se 4 (by rfl) ⟨28758, by rfl⟩ : syracuseStep 306757 = 57517) (by norm_num)
theorem B273989 : Blo 159796 273989 := bbase (se 4 (by rfl) ⟨25686, by rfl⟩ : syracuseStep 273989 = 51373) (by norm_num)
theorem B241229 : Blo 159796 241229 := bbase (se 3 (by rfl) ⟨45230, by rfl⟩ : syracuseStep 241229 = 90461) (by norm_num)
theorem B536149 : Blo 159796 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B241253 : Blo 159796 241253 := bbase (se 4 (by rfl) ⟨22617, by rfl⟩ : syracuseStep 241253 = 45235) (by norm_num)
theorem B405101 : Blo 159796 405101 := bbase (se 3 (by rfl) ⟨75956, by rfl⟩ : syracuseStep 405101 = 151913) (by norm_num)
theorem B241277 : Blo 159796 241277 := bbase (se 3 (by rfl) ⟨45239, by rfl⟩ : syracuseStep 241277 = 90479) (by norm_num)
theorem B241301 : Blo 159796 241301 := bbase (se 6 (by rfl) ⟨5655, by rfl⟩ : syracuseStep 241301 = 11311) (by norm_num)
theorem B241325 : Blo 159796 241325 := bbase (se 3 (by rfl) ⟨45248, by rfl⟩ : syracuseStep 241325 = 90497) (by norm_num)
theorem B241349 : Blo 159796 241349 := bbase (se 4 (by rfl) ⟨22626, by rfl⟩ : syracuseStep 241349 = 45253) (by norm_num)
theorem B274117 : Blo 159796 274117 := bbase (se 4 (by rfl) ⟨25698, by rfl⟩ : syracuseStep 274117 = 51397) (by norm_num)
theorem B241373 : Blo 159796 241373 := bbase (se 3 (by rfl) ⟨45257, by rfl⟩ : syracuseStep 241373 = 90515) (by norm_num)
theorem B241397 : Blo 159796 241397 := bbase (se 5 (by rfl) ⟨11315, by rfl⟩ : syracuseStep 241397 = 22631) (by norm_num)
theorem B241421 : Blo 159796 241421 := bbase (se 3 (by rfl) ⟨45266, by rfl⟩ : syracuseStep 241421 = 90533) (by norm_num)
theorem B274205 : Blo 159796 274205 := bbase (se 3 (by rfl) ⟨51413, by rfl⟩ : syracuseStep 274205 = 102827) (by norm_num)
theorem B241445 : Blo 159796 241445 := bbase (se 4 (by rfl) ⟨22635, by rfl⟩ : syracuseStep 241445 = 45271) (by norm_num)
theorem B241469 : Blo 159796 241469 := bbase (se 3 (by rfl) ⟨45275, by rfl⟩ : syracuseStep 241469 = 90551) (by norm_num)
theorem B175937 : Blo 159796 175937 := bbase (se 2 (by rfl) ⟨65976, by rfl⟩ : syracuseStep 175937 = 131953) (by norm_num)
theorem B241493 : Blo 159796 241493 := bbase (se 9 (by rfl) ⟨707, by rfl⟩ : syracuseStep 241493 = 1415) (by norm_num)
theorem B241517 : Blo 159796 241517 := bbase (se 3 (by rfl) ⟨45284, by rfl⟩ : syracuseStep 241517 = 90569) (by norm_num)
theorem B307061 : Blo 159796 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B241541 : Blo 159796 241541 := bbase (se 4 (by rfl) ⟨22644, by rfl⟩ : syracuseStep 241541 = 45289) (by norm_num)
theorem B241565 : Blo 159796 241565 := bbase (se 3 (by rfl) ⟨45293, by rfl⟩ : syracuseStep 241565 = 90587) (by norm_num)
theorem B274333 : Blo 159796 274333 := bbase (se 3 (by rfl) ⟨51437, by rfl⟩ : syracuseStep 274333 = 102875) (by norm_num)
theorem B241589 : Blo 159796 241589 := bbase (se 5 (by rfl) ⟨11324, by rfl⟩ : syracuseStep 241589 = 22649) (by norm_num)
theorem B405445 : Blo 159796 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B241613 : Blo 159796 241613 := bbase (se 3 (by rfl) ⟨45302, by rfl⟩ : syracuseStep 241613 = 90605) (by norm_num)
theorem B241637 : Blo 159796 241637 := bbase (se 4 (by rfl) ⟨22653, by rfl⟩ : syracuseStep 241637 = 45307) (by norm_num)
theorem B1093621 : Blo 159796 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B274421 : Blo 159796 274421 := bbase (se 5 (by rfl) ⟨12863, by rfl⟩ : syracuseStep 274421 = 25727) (by norm_num)
theorem B241661 : Blo 159796 241661 := bbase (se 3 (by rfl) ⟨45311, by rfl⟩ : syracuseStep 241661 = 90623) (by norm_num)
theorem B241685 : Blo 159796 241685 := bbase (se 6 (by rfl) ⟨5664, by rfl⟩ : syracuseStep 241685 = 11329) (by norm_num)
theorem B241709 : Blo 159796 241709 := bbase (se 3 (by rfl) ⟨45320, by rfl⟩ : syracuseStep 241709 = 90641) (by norm_num)
theorem B405557 : Blo 159796 405557 := bbase (se 5 (by rfl) ⟨19010, by rfl⟩ : syracuseStep 405557 = 38021) (by norm_num)
theorem B241733 : Blo 159796 241733 := bbase (se 4 (by rfl) ⟨22662, by rfl⟩ : syracuseStep 241733 = 45325) (by norm_num)
theorem B241757 : Blo 159796 241757 := bbase (se 3 (by rfl) ⟨45329, by rfl⟩ : syracuseStep 241757 = 90659) (by norm_num)
theorem B241781 : Blo 159796 241781 := bbase (se 5 (by rfl) ⟨11333, by rfl⟩ : syracuseStep 241781 = 22667) (by norm_num)
theorem B274549 : Blo 159796 274549 := bbase (se 5 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 274549 = 25739) (by norm_num)
theorem B176257 : Blo 159796 176257 := bbase (se 2 (by rfl) ⟨66096, by rfl⟩ : syracuseStep 176257 = 132193) (by norm_num)
theorem B372869 : Blo 159796 372869 := bbase (se 4 (by rfl) ⟨34956, by rfl⟩ : syracuseStep 372869 = 69913) (by norm_num)
theorem B241805 : Blo 159796 241805 := bbase (se 3 (by rfl) ⟨45338, by rfl⟩ : syracuseStep 241805 = 90677) (by norm_num)
theorem B241829 : Blo 159796 241829 := bbase (se 4 (by rfl) ⟨22671, by rfl⟩ : syracuseStep 241829 = 45343) (by norm_num)
theorem B241853 : Blo 159796 241853 := bbase (se 3 (by rfl) ⟨45347, by rfl⟩ : syracuseStep 241853 = 90695) (by norm_num)
theorem B274637 : Blo 159796 274637 := bbase (se 3 (by rfl) ⟨51494, by rfl⟩ : syracuseStep 274637 = 102989) (by norm_num)
theorem B372941 : Blo 159796 372941 := bbase (se 3 (by rfl) ⟨69926, by rfl⟩ : syracuseStep 372941 = 139853) (by norm_num)
theorem B241877 : Blo 159796 241877 := bbase (se 7 (by rfl) ⟨2834, by rfl⟩ : syracuseStep 241877 = 5669) (by norm_num)
theorem B241901 : Blo 159796 241901 := bbase (se 3 (by rfl) ⟨45356, by rfl⟩ : syracuseStep 241901 = 90713) (by norm_num)
theorem B405749 : Blo 159796 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B241925 : Blo 159796 241925 := bbase (se 4 (by rfl) ⟨22680, by rfl⟩ : syracuseStep 241925 = 45361) (by norm_num)
theorem B241949 : Blo 159796 241949 := bbase (se 3 (by rfl) ⟨45365, by rfl⟩ : syracuseStep 241949 = 90731) (by norm_num)
theorem B241973 : Blo 159796 241973 := bbase (se 5 (by rfl) ⟨11342, by rfl⟩ : syracuseStep 241973 = 22685) (by norm_num)
theorem B241997 : Blo 159796 241997 := bbase (se 3 (by rfl) ⟨45374, by rfl⟩ : syracuseStep 241997 = 90749) (by norm_num)
theorem B274765 : Blo 159796 274765 := bbase (se 3 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 274765 = 103037) (by norm_num)
theorem B242021 : Blo 159796 242021 := bbase (se 4 (by rfl) ⟨22689, by rfl⟩ : syracuseStep 242021 = 45379) (by norm_num)
theorem B242045 : Blo 159796 242045 := bbase (se 3 (by rfl) ⟨45383, by rfl⟩ : syracuseStep 242045 = 90767) (by norm_num)
theorem B242069 : Blo 159796 242069 := bbase (se 6 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 242069 = 11347) (by norm_num)
theorem B274853 : Blo 159796 274853 := bbase (se 4 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 274853 = 51535) (by norm_num)
theorem B242093 : Blo 159796 242093 := bbase (se 3 (by rfl) ⟨45392, by rfl⟩ : syracuseStep 242093 = 90785) (by norm_num)
theorem B176569 : Blo 159796 176569 := bbase (se 2 (by rfl) ⟨66213, by rfl⟩ : syracuseStep 176569 = 132427) (by norm_num)
theorem B242117 : Blo 159796 242117 := bbase (se 4 (by rfl) ⟨22698, by rfl⟩ : syracuseStep 242117 = 45397) (by norm_num)
theorem B242141 : Blo 159796 242141 := bbase (se 3 (by rfl) ⟨45401, by rfl⟩ : syracuseStep 242141 = 90803) (by norm_num)
theorem B1225205 : Blo 159796 1225205 := bbase (se 5 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 1225205 = 114863) (by norm_num)
theorem B242165 : Blo 159796 242165 := bbase (se 5 (by rfl) ⟨11351, by rfl⟩ : syracuseStep 242165 = 22703) (by norm_num)
theorem B242189 : Blo 159796 242189 := bbase (se 3 (by rfl) ⟨45410, by rfl⟩ : syracuseStep 242189 = 90821) (by norm_num)
theorem B242213 : Blo 159796 242213 := bbase (se 4 (by rfl) ⟨22707, by rfl⟩ : syracuseStep 242213 = 45415) (by norm_num)
theorem B274981 : Blo 159796 274981 := bbase (se 4 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 274981 = 51559) (by norm_num)
theorem B242237 : Blo 159796 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B406093 : Blo 159796 406093 := bbase (se 3 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 406093 = 152285) (by norm_num)
theorem B242261 : Blo 159796 242261 := bbase (se 8 (by rfl) ⟨1419, by rfl⟩ : syracuseStep 242261 = 2839) (by norm_num)
theorem B307813 : Blo 159796 307813 := bbase (se 4 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 307813 = 57715) (by norm_num)
theorem B242285 : Blo 159796 242285 := bbase (se 3 (by rfl) ⟨45428, by rfl⟩ : syracuseStep 242285 = 90857) (by norm_num)
theorem B209533 : Blo 159796 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B275069 : Blo 159796 275069 := bbase (se 3 (by rfl) ⟨51575, by rfl⟩ : syracuseStep 275069 = 103151) (by norm_num)
theorem B242309 : Blo 159796 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B242333 : Blo 159796 242333 := bbase (se 3 (by rfl) ⟨45437, by rfl⟩ : syracuseStep 242333 = 90875) (by norm_num)
theorem B242357 : Blo 159796 242357 := bbase (se 5 (by rfl) ⟨11360, by rfl⟩ : syracuseStep 242357 = 22721) (by norm_num)
theorem B406205 : Blo 159796 406205 := bbase (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) (by norm_num)
theorem B242381 : Blo 159796 242381 := bbase (se 3 (by rfl) ⟨45446, by rfl⟩ : syracuseStep 242381 = 90893) (by norm_num)
theorem B242405 : Blo 159796 242405 := bbase (se 4 (by rfl) ⟨22725, by rfl⟩ : syracuseStep 242405 = 45451) (by norm_num)
theorem B307957 : Blo 159796 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B242429 : Blo 159796 242429 := bbase (se 3 (by rfl) ⟨45455, by rfl⟩ : syracuseStep 242429 = 90911) (by norm_num)
theorem B275197 : Blo 159796 275197 := bbase (se 3 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 275197 = 103199) (by norm_num)
theorem B242453 : Blo 159796 242453 := bbase (se 6 (by rfl) ⟨5682, by rfl⟩ : syracuseStep 242453 = 11365) (by norm_num)
theorem B242477 : Blo 159796 242477 := bbase (se 3 (by rfl) ⟨45464, by rfl⟩ : syracuseStep 242477 = 90929) (by norm_num)
theorem B242501 : Blo 159796 242501 := bbase (se 4 (by rfl) ⟨22734, by rfl⟩ : syracuseStep 242501 = 45469) (by norm_num)
theorem B340805 : Blo 159796 340805 := bbase (se 4 (by rfl) ⟨31950, by rfl⟩ : syracuseStep 340805 = 63901) (by norm_num)
theorem B8926037 : Blo 159796 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B275285 : Blo 159796 275285 := bbase (se 9 (by rfl) ⟨806, by rfl⟩ : syracuseStep 275285 = 1613) (by norm_num)
theorem B242525 : Blo 159796 242525 := bbase (se 3 (by rfl) ⟨45473, by rfl⟩ : syracuseStep 242525 = 90947) (by norm_num)
theorem B242549 : Blo 159796 242549 := bbase (se 5 (by rfl) ⟨11369, by rfl⟩ : syracuseStep 242549 = 22739) (by norm_num)
theorem B406397 : Blo 159796 406397 := bbase (se 3 (by rfl) ⟨76199, by rfl⟩ : syracuseStep 406397 = 152399) (by norm_num)
theorem B242573 : Blo 159796 242573 := bbase (se 3 (by rfl) ⟨45482, by rfl⟩ : syracuseStep 242573 = 90965) (by norm_num)
theorem B308117 : Blo 159796 308117 := bbase (se 6 (by rfl) ⟨7221, by rfl⟩ : syracuseStep 308117 = 14443) (by norm_num)
theorem B242597 : Blo 159796 242597 := bbase (se 4 (by rfl) ⟨22743, by rfl⟩ : syracuseStep 242597 = 45487) (by norm_num)
theorem B242621 : Blo 159796 242621 := bbase (se 3 (by rfl) ⟨45491, by rfl⟩ : syracuseStep 242621 = 90983) (by norm_num)
theorem B242645 : Blo 159796 242645 := bbase (se 7 (by rfl) ⟨2843, by rfl⟩ : syracuseStep 242645 = 5687) (by norm_num)
theorem B275413 : Blo 159796 275413 := bbase (se 7 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 275413 = 6455) (by norm_num)
theorem B275437 : Blo 159796 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B242669 : Blo 159796 242669 := bbase (se 3 (by rfl) ⟨45500, by rfl⟩ : syracuseStep 242669 = 91001) (by norm_num)
theorem B242693 : Blo 159796 242693 := bbase (se 4 (by rfl) ⟨22752, by rfl⟩ : syracuseStep 242693 = 45505) (by norm_num)
theorem B242717 : Blo 159796 242717 := bbase (se 3 (by rfl) ⟨45509, by rfl⟩ : syracuseStep 242717 = 91019) (by norm_num)
theorem B308261 : Blo 159796 308261 := bbase (se 4 (by rfl) ⟨28899, by rfl⟩ : syracuseStep 308261 = 57799) (by norm_num)
theorem B275501 : Blo 159796 275501 := bbase (se 3 (by rfl) ⟨51656, by rfl⟩ : syracuseStep 275501 = 103313) (by norm_num)
theorem B242741 : Blo 159796 242741 := bbase (se 5 (by rfl) ⟨11378, by rfl⟩ : syracuseStep 242741 = 22757) (by norm_num)
theorem B242765 : Blo 159796 242765 := bbase (se 3 (by rfl) ⟨45518, by rfl⟩ : syracuseStep 242765 = 91037) (by norm_num)
theorem B242789 : Blo 159796 242789 := bbase (se 4 (by rfl) ⟨22761, by rfl⟩ : syracuseStep 242789 = 45523) (by norm_num)
theorem B242813 : Blo 159796 242813 := bbase (se 3 (by rfl) ⟨45527, by rfl⟩ : syracuseStep 242813 = 91055) (by norm_num)
theorem B242837 : Blo 159796 242837 := bbase (se 6 (by rfl) ⟨5691, by rfl⟩ : syracuseStep 242837 = 11383) (by norm_num)
theorem B242861 : Blo 159796 242861 := bbase (se 3 (by rfl) ⟨45536, by rfl⟩ : syracuseStep 242861 = 91073) (by norm_num)
theorem B275629 : Blo 159796 275629 := bbase (se 3 (by rfl) ⟨51680, by rfl⟩ : syracuseStep 275629 = 103361) (by norm_num)
theorem B242885 : Blo 159796 242885 := bbase (se 4 (by rfl) ⟨22770, by rfl⟩ : syracuseStep 242885 = 45541) (by norm_num)
theorem B406741 : Blo 159796 406741 := bbase (se 7 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 406741 = 9533) (by norm_num)
theorem B242909 : Blo 159796 242909 := bbase (se 3 (by rfl) ⟨45545, by rfl⟩ : syracuseStep 242909 = 91091) (by norm_num)
theorem B242933 : Blo 159796 242933 := bbase (se 5 (by rfl) ⟨11387, by rfl⟩ : syracuseStep 242933 = 22775) (by norm_num)
theorem B275717 : Blo 159796 275717 := bbase (se 4 (by rfl) ⟨25848, by rfl⟩ : syracuseStep 275717 = 51697) (by norm_num)
theorem B242957 : Blo 159796 242957 := bbase (se 3 (by rfl) ⟨45554, by rfl⟩ : syracuseStep 242957 = 91109) (by norm_num)
theorem B242981 : Blo 159796 242981 := bbase (se 4 (by rfl) ⟨22779, by rfl⟩ : syracuseStep 242981 = 45559) (by norm_num)
theorem B341309 : Blo 159796 341309 := bbase (se 3 (by rfl) ⟨63995, by rfl⟩ : syracuseStep 341309 = 127991) (by norm_num)
theorem B243005 : Blo 159796 243005 := bbase (se 3 (by rfl) ⟨45563, by rfl⟩ : syracuseStep 243005 = 91127) (by norm_num)
theorem B406853 : Blo 159796 406853 := bbase (se 4 (by rfl) ⟨38142, by rfl⟩ : syracuseStep 406853 = 76285) (by norm_num)
theorem B308549 : Blo 159796 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B243029 : Blo 159796 243029 := bbase (se 13 (by rfl) ⟨44, by rfl⟩ : syracuseStep 243029 = 89) (by norm_num)
theorem B243053 : Blo 159796 243053 := bbase (se 3 (by rfl) ⟨45572, by rfl⟩ : syracuseStep 243053 = 91145) (by norm_num)
theorem B308605 : Blo 159796 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B243077 : Blo 159796 243077 := bbase (se 4 (by rfl) ⟨22788, by rfl⟩ : syracuseStep 243077 = 45577) (by norm_num)
theorem B275845 : Blo 159796 275845 := bbase (se 4 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 275845 = 51721) (by norm_num)
theorem B243101 : Blo 159796 243101 := bbase (se 3 (by rfl) ⟨45581, by rfl⟩ : syracuseStep 243101 = 91163) (by norm_num)
theorem B243125 : Blo 159796 243125 := bbase (se 5 (by rfl) ⟨11396, by rfl⟩ : syracuseStep 243125 = 22793) (by norm_num)
theorem B243149 : Blo 159796 243149 := bbase (se 3 (by rfl) ⟨45590, by rfl⟩ : syracuseStep 243149 = 91181) (by norm_num)
theorem B308701 : Blo 159796 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B275933 : Blo 159796 275933 := bbase (se 3 (by rfl) ⟨51737, by rfl⟩ : syracuseStep 275933 = 103475) (by norm_num)
theorem B243173 : Blo 159796 243173 := bbase (se 4 (by rfl) ⟨22797, by rfl⟩ : syracuseStep 243173 = 45595) (by norm_num)
theorem B243197 : Blo 159796 243197 := bbase (se 3 (by rfl) ⟨45599, by rfl⟩ : syracuseStep 243197 = 91199) (by norm_num)
theorem B407045 : Blo 159796 407045 := bbase (se 4 (by rfl) ⟨38160, by rfl⟩ : syracuseStep 407045 = 76321) (by norm_num)
theorem B243221 : Blo 159796 243221 := bbase (se 6 (by rfl) ⟨5700, by rfl⟩ : syracuseStep 243221 = 11401) (by norm_num)
theorem B243245 : Blo 159796 243245 := bbase (se 3 (by rfl) ⟨45608, by rfl⟩ : syracuseStep 243245 = 91217) (by norm_num)
theorem B243269 : Blo 159796 243269 := bbase (se 4 (by rfl) ⟨22806, by rfl⟩ : syracuseStep 243269 = 45613) (by norm_num)
theorem B243293 : Blo 159796 243293 := bbase (se 3 (by rfl) ⟨45617, by rfl⟩ : syracuseStep 243293 = 91235) (by norm_num)
theorem B276061 : Blo 159796 276061 := bbase (se 3 (by rfl) ⟨51761, by rfl⟩ : syracuseStep 276061 = 103523) (by norm_num)
theorem B243317 : Blo 159796 243317 := bbase (se 5 (by rfl) ⟨11405, by rfl⟩ : syracuseStep 243317 = 22811) (by norm_num)
theorem B243341 : Blo 159796 243341 := bbase (se 3 (by rfl) ⟨45626, by rfl⟩ : syracuseStep 243341 = 91253) (by norm_num)
theorem B243365 : Blo 159796 243365 := bbase (se 4 (by rfl) ⟨22815, by rfl⟩ : syracuseStep 243365 = 45631) (by norm_num)
theorem B276149 : Blo 159796 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B243389 : Blo 159796 243389 := bbase (se 3 (by rfl) ⟨45635, by rfl⟩ : syracuseStep 243389 = 91271) (by norm_num)
theorem B243413 : Blo 159796 243413 := bbase (se 7 (by rfl) ⟨2852, by rfl⟩ : syracuseStep 243413 = 5705) (by norm_num)
theorem B243437 : Blo 159796 243437 := bbase (se 3 (by rfl) ⟨45644, by rfl⟩ : syracuseStep 243437 = 91289) (by norm_num)
theorem B243461 : Blo 159796 243461 := bbase (se 4 (by rfl) ⟨22824, by rfl⟩ : syracuseStep 243461 = 45649) (by norm_num)
theorem B309005 : Blo 159796 309005 := bbase (se 3 (by rfl) ⟨57938, by rfl⟩ : syracuseStep 309005 = 115877) (by norm_num)
theorem B243485 : Blo 159796 243485 := bbase (se 3 (by rfl) ⟨45653, by rfl⟩ : syracuseStep 243485 = 91307) (by norm_num)
theorem B243509 : Blo 159796 243509 := bbase (se 5 (by rfl) ⟨11414, by rfl⟩ : syracuseStep 243509 = 22829) (by norm_num)
theorem B276277 : Blo 159796 276277 := bbase (se 5 (by rfl) ⟨12950, by rfl⟩ : syracuseStep 276277 = 25901) (by norm_num)
theorem B243533 : Blo 159796 243533 := bbase (se 3 (by rfl) ⟨45662, by rfl⟩ : syracuseStep 243533 = 91325) (by norm_num)
theorem B1718101 : Blo 159796 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B407389 : Blo 159796 407389 := bbase (se 3 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 407389 = 152771) (by norm_num)
theorem B243557 : Blo 159796 243557 := bbase (se 4 (by rfl) ⟨22833, by rfl⟩ : syracuseStep 243557 = 45667) (by norm_num)
theorem B243581 : Blo 159796 243581 := bbase (se 3 (by rfl) ⟨45671, by rfl⟩ : syracuseStep 243581 = 91343) (by norm_num)
theorem B276365 : Blo 159796 276365 := bbase (se 3 (by rfl) ⟨51818, by rfl⟩ : syracuseStep 276365 = 103637) (by norm_num)
theorem B243605 : Blo 159796 243605 := bbase (se 6 (by rfl) ⟨5709, by rfl⟩ : syracuseStep 243605 = 11419) (by norm_num)
theorem B243629 : Blo 159796 243629 := bbase (se 3 (by rfl) ⟨45680, by rfl⟩ : syracuseStep 243629 = 91361) (by norm_num)
theorem B243653 : Blo 159796 243653 := bbase (se 4 (by rfl) ⟨22842, by rfl⟩ : syracuseStep 243653 = 45685) (by norm_num)
theorem B407501 : Blo 159796 407501 := bbase (se 3 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 407501 = 152813) (by norm_num)
theorem B243677 : Blo 159796 243677 := bbase (se 3 (by rfl) ⟨45689, by rfl⟩ : syracuseStep 243677 = 91379) (by norm_num)
theorem B243701 : Blo 159796 243701 := bbase (se 5 (by rfl) ⟨11423, by rfl⟩ : syracuseStep 243701 = 22847) (by norm_num)
theorem B243725 : Blo 159796 243725 := bbase (se 3 (by rfl) ⟨45698, by rfl⟩ : syracuseStep 243725 = 91397) (by norm_num)
theorem B342053 : Blo 159796 342053 := bbase (se 4 (by rfl) ⟨32067, by rfl⟩ : syracuseStep 342053 = 64135) (by norm_num)
theorem B243749 : Blo 159796 243749 := bbase (se 4 (by rfl) ⟨22851, by rfl⟩ : syracuseStep 243749 = 45703) (by norm_num)
theorem B243773 : Blo 159796 243773 := bbase (se 3 (by rfl) ⟨45707, by rfl⟩ : syracuseStep 243773 = 91415) (by norm_num)
theorem B243797 : Blo 159796 243797 := bbase (se 8 (by rfl) ⟨1428, by rfl⟩ : syracuseStep 243797 = 2857) (by norm_num)
theorem B243821 : Blo 159796 243821 := bbase (se 3 (by rfl) ⟨45716, by rfl⟩ : syracuseStep 243821 = 91433) (by norm_num)
theorem B243845 : Blo 159796 243845 := bbase (se 4 (by rfl) ⟨22860, by rfl⟩ : syracuseStep 243845 = 45721) (by norm_num)
theorem B407693 : Blo 159796 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B243869 : Blo 159796 243869 := bbase (se 3 (by rfl) ⟨45725, by rfl⟩ : syracuseStep 243869 = 91451) (by norm_num)
theorem B243893 : Blo 159796 243893 := bbase (se 5 (by rfl) ⟨11432, by rfl⟩ : syracuseStep 243893 = 22865) (by norm_num)
theorem B243917 : Blo 159796 243917 := bbase (se 3 (by rfl) ⟨45734, by rfl⟩ : syracuseStep 243917 = 91469) (by norm_num)
theorem B243941 : Blo 159796 243941 := bbase (se 4 (by rfl) ⟨22869, by rfl⟩ : syracuseStep 243941 = 45739) (by norm_num)
theorem B243965 : Blo 159796 243965 := bbase (se 3 (by rfl) ⟨45743, by rfl⟩ : syracuseStep 243965 = 91487) (by norm_num)
theorem B243989 : Blo 159796 243989 := bbase (se 6 (by rfl) ⟨5718, by rfl⟩ : syracuseStep 243989 = 11437) (by norm_num)
theorem B244013 : Blo 159796 244013 := bbase (se 3 (by rfl) ⟨45752, by rfl⟩ : syracuseStep 244013 = 91505) (by norm_num)
theorem B244037 : Blo 159796 244037 := bbase (se 4 (by rfl) ⟨22878, by rfl⟩ : syracuseStep 244037 = 45757) (by norm_num)
theorem B244061 : Blo 159796 244061 := bbase (se 3 (by rfl) ⟨45761, by rfl⟩ : syracuseStep 244061 = 91523) (by norm_num)
theorem B244085 : Blo 159796 244085 := bbase (se 5 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 244085 = 22883) (by norm_num)
theorem B244109 : Blo 159796 244109 := bbase (se 3 (by rfl) ⟨45770, by rfl⟩ : syracuseStep 244109 = 91541) (by norm_num)
theorem B244133 : Blo 159796 244133 := bbase (se 4 (by rfl) ⟨22887, by rfl⟩ : syracuseStep 244133 = 45775) (by norm_num)
theorem B244157 : Blo 159796 244157 := bbase (se 3 (by rfl) ⟨45779, by rfl⟩ : syracuseStep 244157 = 91559) (by norm_num)
theorem B244181 : Blo 159796 244181 := bbase (se 7 (by rfl) ⟨2861, by rfl⟩ : syracuseStep 244181 = 5723) (by norm_num)
theorem B408037 : Blo 159796 408037 := bbase (se 4 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 408037 = 76507) (by norm_num)
theorem B244205 : Blo 159796 244205 := bbase (se 3 (by rfl) ⟨45788, by rfl⟩ : syracuseStep 244205 = 91577) (by norm_num)
theorem B309757 : Blo 159796 309757 := bbase (se 3 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 309757 = 116159) (by norm_num)
theorem B244229 : Blo 159796 244229 := bbase (se 4 (by rfl) ⟨22896, by rfl⟩ : syracuseStep 244229 = 45793) (by norm_num)
theorem B244253 : Blo 159796 244253 := bbase (se 3 (by rfl) ⟨45797, by rfl⟩ : syracuseStep 244253 = 91595) (by norm_num)
theorem B440869 : Blo 159796 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B244277 : Blo 159796 244277 := bbase (se 5 (by rfl) ⟨11450, by rfl⟩ : syracuseStep 244277 = 22901) (by norm_num)
theorem B244301 : Blo 159796 244301 := bbase (se 3 (by rfl) ⟨45806, by rfl⟩ : syracuseStep 244301 = 91613) (by norm_num)
theorem B408149 : Blo 159796 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B244325 : Blo 159796 244325 := bbase (se 4 (by rfl) ⟨22905, by rfl⟩ : syracuseStep 244325 = 45811) (by norm_num)
theorem B244349 : Blo 159796 244349 := bbase (se 3 (by rfl) ⟨45815, by rfl⟩ : syracuseStep 244349 = 91631) (by norm_num)
theorem B309901 : Blo 159796 309901 := bbase (se 3 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 309901 = 116213) (by norm_num)
theorem B244373 : Blo 159796 244373 := bbase (se 6 (by rfl) ⟨5727, by rfl⟩ : syracuseStep 244373 = 11455) (by norm_num)
theorem B244397 : Blo 159796 244397 := bbase (se 3 (by rfl) ⟨45824, by rfl⟩ : syracuseStep 244397 = 91649) (by norm_num)
theorem B244421 : Blo 159796 244421 := bbase (se 4 (by rfl) ⟨22914, by rfl⟩ : syracuseStep 244421 = 45829) (by norm_num)
theorem B244445 : Blo 159796 244445 := bbase (se 3 (by rfl) ⟨45833, by rfl⟩ : syracuseStep 244445 = 91667) (by norm_num)
theorem B244469 : Blo 159796 244469 := bbase (se 5 (by rfl) ⟨11459, by rfl⟩ : syracuseStep 244469 = 22919) (by norm_num)
theorem B244493 : Blo 159796 244493 := bbase (se 3 (by rfl) ⟨45842, by rfl⟩ : syracuseStep 244493 = 91685) (by norm_num)
theorem B342805 : Blo 159796 342805 := bbase (se 6 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 342805 = 16069) (by norm_num)
theorem B408341 : Blo 159796 408341 := bbase (se 6 (by rfl) ⟨9570, by rfl⟩ : syracuseStep 408341 = 19141) (by norm_num)
theorem B244517 : Blo 159796 244517 := bbase (se 4 (by rfl) ⟨22923, by rfl⟩ : syracuseStep 244517 = 45847) (by norm_num)
theorem B310061 : Blo 159796 310061 := bbase (se 3 (by rfl) ⟨58136, by rfl⟩ : syracuseStep 310061 = 116273) (by norm_num)
theorem B244541 : Blo 159796 244541 := bbase (se 3 (by rfl) ⟨45851, by rfl⟩ : syracuseStep 244541 = 91703) (by norm_num)
theorem B244565 : Blo 159796 244565 := bbase (se 9 (by rfl) ⟨716, by rfl⟩ : syracuseStep 244565 = 1433) (by norm_num)
theorem B244589 : Blo 159796 244589 := bbase (se 3 (by rfl) ⟨45860, by rfl⟩ : syracuseStep 244589 = 91721) (by norm_num)
theorem B244613 : Blo 159796 244613 := bbase (se 4 (by rfl) ⟨22932, by rfl⟩ : syracuseStep 244613 = 45865) (by norm_num)
theorem B244637 : Blo 159796 244637 := bbase (se 3 (by rfl) ⟨45869, by rfl⟩ : syracuseStep 244637 = 91739) (by norm_num)
theorem B342949 : Blo 159796 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B244661 : Blo 159796 244661 := bbase (se 5 (by rfl) ⟨11468, by rfl⟩ : syracuseStep 244661 = 22937) (by norm_num)
theorem B310205 : Blo 159796 310205 := bbase (se 3 (by rfl) ⟨58163, by rfl⟩ : syracuseStep 310205 = 116327) (by norm_num)
theorem B244685 : Blo 159796 244685 := bbase (se 3 (by rfl) ⟨45878, by rfl⟩ : syracuseStep 244685 = 91757) (by norm_num)
theorem B539621 : Blo 159796 539621 := bbase (se 4 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 539621 = 101179) (by norm_num)
theorem B244709 : Blo 159796 244709 := bbase (se 4 (by rfl) ⟨22941, by rfl⟩ : syracuseStep 244709 = 45883) (by norm_num)
theorem B244733 : Blo 159796 244733 := bbase (se 3 (by rfl) ⟨45887, by rfl⟩ : syracuseStep 244733 = 91775) (by norm_num)
theorem B244757 : Blo 159796 244757 := bbase (se 6 (by rfl) ⟨5736, by rfl⟩ : syracuseStep 244757 = 11473) (by norm_num)
theorem B244781 : Blo 159796 244781 := bbase (se 3 (by rfl) ⟨45896, by rfl⟩ : syracuseStep 244781 = 91793) (by norm_num)
theorem B244805 : Blo 159796 244805 := bbase (se 4 (by rfl) ⟨22950, by rfl⟩ : syracuseStep 244805 = 45901) (by norm_num)
theorem B244829 : Blo 159796 244829 := bbase (se 3 (by rfl) ⟨45905, by rfl⟩ : syracuseStep 244829 = 91811) (by norm_num)
theorem B408685 : Blo 159796 408685 := bbase (se 3 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 408685 = 153257) (by norm_num)
theorem B244853 : Blo 159796 244853 := bbase (se 5 (by rfl) ⟨11477, by rfl⟩ : syracuseStep 244853 = 22955) (by norm_num)
theorem B244877 : Blo 159796 244877 := bbase (se 3 (by rfl) ⟨45914, by rfl⟩ : syracuseStep 244877 = 91829) (by norm_num)
theorem B244901 : Blo 159796 244901 := bbase (se 4 (by rfl) ⟨22959, by rfl⟩ : syracuseStep 244901 = 45919) (by norm_num)
theorem B244925 : Blo 159796 244925 := bbase (se 3 (by rfl) ⟨45923, by rfl⟩ : syracuseStep 244925 = 91847) (by norm_num)
theorem B244949 : Blo 159796 244949 := bbase (se 7 (by rfl) ⟨2870, by rfl⟩ : syracuseStep 244949 = 5741) (by norm_num)
theorem B408797 : Blo 159796 408797 := bbase (se 3 (by rfl) ⟨76649, by rfl⟩ : syracuseStep 408797 = 153299) (by norm_num)
theorem B310493 : Blo 159796 310493 := bbase (se 3 (by rfl) ⟨58217, by rfl⟩ : syracuseStep 310493 = 116435) (by norm_num)
theorem B244973 : Blo 159796 244973 := bbase (se 3 (by rfl) ⟨45932, by rfl⟩ : syracuseStep 244973 = 91865) (by norm_num)
theorem B244997 : Blo 159796 244997 := bbase (se 4 (by rfl) ⟨22968, by rfl⟩ : syracuseStep 244997 = 45937) (by norm_num)
theorem B343325 : Blo 159796 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B245021 : Blo 159796 245021 := bbase (se 3 (by rfl) ⟨45941, by rfl⟩ : syracuseStep 245021 = 91883) (by norm_num)
theorem B245045 : Blo 159796 245045 := bbase (se 5 (by rfl) ⟨11486, by rfl⟩ : syracuseStep 245045 = 22973) (by norm_num)
theorem B245069 : Blo 159796 245069 := bbase (se 3 (by rfl) ⟨45950, by rfl⟩ : syracuseStep 245069 = 91901) (by norm_num)
theorem B245093 : Blo 159796 245093 := bbase (se 4 (by rfl) ⟨22977, by rfl⟩ : syracuseStep 245093 = 45955) (by norm_num)
theorem B310645 : Blo 159796 310645 := bbase (se 5 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 310645 = 29123) (by norm_num)
theorem B245117 : Blo 159796 245117 := bbase (se 3 (by rfl) ⟨45959, by rfl⟩ : syracuseStep 245117 = 91919) (by norm_num)
theorem B540053 : Blo 159796 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B245141 : Blo 159796 245141 := bbase (se 6 (by rfl) ⟨5745, by rfl⟩ : syracuseStep 245141 = 11491) (by norm_num)
theorem B245149 : Blo 159796 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B408989 : Blo 159796 408989 := bbase (se 3 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 408989 = 153371) (by norm_num)
theorem B245165 : Blo 159796 245165 := bbase (se 3 (by rfl) ⟨45968, by rfl⟩ : syracuseStep 245165 = 91937) (by norm_num)
theorem B245189 : Blo 159796 245189 := bbase (se 4 (by rfl) ⟨22986, by rfl⟩ : syracuseStep 245189 = 45973) (by norm_num)
theorem B245213 : Blo 159796 245213 := bbase (se 3 (by rfl) ⟨45977, by rfl⟩ : syracuseStep 245213 = 91955) (by norm_num)
theorem B245237 : Blo 159796 245237 := bbase (se 5 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 245237 = 22991) (by norm_num)
theorem B245261 : Blo 159796 245261 := bbase (se 3 (by rfl) ⟨45986, by rfl⟩ : syracuseStep 245261 = 91973) (by norm_num)
theorem B245285 : Blo 159796 245285 := bbase (se 4 (by rfl) ⟨22995, by rfl⟩ : syracuseStep 245285 = 45991) (by norm_num)
theorem B245309 : Blo 159796 245309 := bbase (se 3 (by rfl) ⟨45995, by rfl⟩ : syracuseStep 245309 = 91991) (by norm_num)
theorem B179797 : Blo 159796 179797 := bbase (se 8 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 179797 = 2107) (by norm_num)
theorem B245333 : Blo 159796 245333 := bbase (se 8 (by rfl) ⟨1437, by rfl⟩ : syracuseStep 245333 = 2875) (by norm_num)
theorem B769637 : Blo 159796 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B245357 : Blo 159796 245357 := bbase (se 3 (by rfl) ⟨46004, by rfl⟩ : syracuseStep 245357 = 92009) (by norm_num)
theorem B179833 : Blo 159796 179833 := bbase (se 2 (by rfl) ⟨67437, by rfl⟩ : syracuseStep 179833 = 134875) (by norm_num)
theorem B245381 : Blo 159796 245381 := bbase (se 4 (by rfl) ⟨23004, by rfl⟩ : syracuseStep 245381 = 46009) (by norm_num)
theorem B343693 : Blo 159796 343693 := bbase (se 3 (by rfl) ⟨64442, by rfl⟩ : syracuseStep 343693 = 128885) (by norm_num)
theorem B179869 : Blo 159796 179869 := bbase (se 3 (by rfl) ⟨33725, by rfl⟩ : syracuseStep 179869 = 67451) (by norm_num)
theorem B245405 : Blo 159796 245405 := bbase (se 3 (by rfl) ⟨46013, by rfl⟩ : syracuseStep 245405 = 92027) (by norm_num)
theorem B310949 : Blo 159796 310949 := bbase (se 4 (by rfl) ⟨29151, by rfl⟩ : syracuseStep 310949 = 58303) (by norm_num)
theorem B245429 : Blo 159796 245429 := bbase (se 5 (by rfl) ⟨11504, by rfl⟩ : syracuseStep 245429 = 23009) (by norm_num)
theorem B179905 : Blo 159796 179905 := bbase (se 2 (by rfl) ⟨67464, by rfl⟩ : syracuseStep 179905 = 134929) (by norm_num)
theorem B245453 : Blo 159796 245453 := bbase (se 3 (by rfl) ⟨46022, by rfl⟩ : syracuseStep 245453 = 92045) (by norm_num)
theorem B179941 : Blo 159796 179941 := bbase (se 4 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 179941 = 33739) (by norm_num)
theorem B245477 : Blo 159796 245477 := bbase (se 4 (by rfl) ⟨23013, by rfl⟩ : syracuseStep 245477 = 46027) (by norm_num)
theorem B409333 : Blo 159796 409333 := bbase (se 5 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 409333 = 38375) (by norm_num)
theorem B245501 : Blo 159796 245501 := bbase (se 3 (by rfl) ⟨46031, by rfl⟩ : syracuseStep 245501 = 92063) (by norm_num)
theorem B179977 : Blo 159796 179977 := bbase (se 2 (by rfl) ⟨67491, by rfl⟩ : syracuseStep 179977 = 134983) (by norm_num)
theorem B245525 : Blo 159796 245525 := bbase (se 6 (by rfl) ⟨5754, by rfl⟩ : syracuseStep 245525 = 11509) (by norm_num)
theorem B180013 : Blo 159796 180013 := bbase (se 3 (by rfl) ⟨33752, by rfl⟩ : syracuseStep 180013 = 67505) (by norm_num)
theorem B245549 : Blo 159796 245549 := bbase (se 3 (by rfl) ⟨46040, by rfl⟩ : syracuseStep 245549 = 92081) (by norm_num)
theorem B540485 : Blo 159796 540485 := bbase (se 4 (by rfl) ⟨50670, by rfl⟩ : syracuseStep 540485 = 101341) (by norm_num)
theorem B245573 : Blo 159796 245573 := bbase (se 4 (by rfl) ⟨23022, by rfl⟩ : syracuseStep 245573 = 46045) (by norm_num)
theorem B180049 : Blo 159796 180049 := bbase (se 2 (by rfl) ⟨67518, by rfl⟩ : syracuseStep 180049 = 135037) (by norm_num)
theorem B245597 : Blo 159796 245597 := bbase (se 3 (by rfl) ⟨46049, by rfl⟩ : syracuseStep 245597 = 92099) (by norm_num)
theorem B409445 : Blo 159796 409445 := bbase (se 4 (by rfl) ⟨38385, by rfl⟩ : syracuseStep 409445 = 76771) (by norm_num)
theorem B180085 : Blo 159796 180085 := bbase (se 5 (by rfl) ⟨8441, by rfl⟩ : syracuseStep 180085 = 16883) (by norm_num)
theorem B245621 : Blo 159796 245621 := bbase (se 5 (by rfl) ⟨11513, by rfl⟩ : syracuseStep 245621 = 23027) (by norm_num)
theorem B245645 : Blo 159796 245645 := bbase (se 3 (by rfl) ⟨46058, by rfl⟩ : syracuseStep 245645 = 92117) (by norm_num)
theorem B180121 : Blo 159796 180121 := bbase (se 2 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 180121 = 135091) (by norm_num)
theorem B376741 : Blo 159796 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B245669 : Blo 159796 245669 := bbase (se 4 (by rfl) ⟨23031, by rfl⟩ : syracuseStep 245669 = 46063) (by norm_num)
theorem B180157 : Blo 159796 180157 := bbase (se 3 (by rfl) ⟨33779, by rfl⟩ : syracuseStep 180157 = 67559) (by norm_num)
theorem B245693 : Blo 159796 245693 := bbase (se 3 (by rfl) ⟨46067, by rfl⟩ : syracuseStep 245693 = 92135) (by norm_num)
theorem B180193 : Blo 159796 180193 := bbase (se 2 (by rfl) ⟨67572, by rfl⟩ : syracuseStep 180193 = 135145) (by norm_num)
theorem B180229 : Blo 159796 180229 := bbase (se 4 (by rfl) ⟨16896, by rfl⟩ : syracuseStep 180229 = 33793) (by norm_num)
theorem B409637 : Blo 159796 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B180265 : Blo 159796 180265 := bbase (se 2 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 180265 = 135199) (by norm_num)
theorem B180301 : Blo 159796 180301 := bbase (se 3 (by rfl) ⟨33806, by rfl⟩ : syracuseStep 180301 = 67613) (by norm_num)
theorem B180337 : Blo 159796 180337 := bbase (se 2 (by rfl) ⟨67626, by rfl⟩ : syracuseStep 180337 = 135253) (by norm_num)
theorem B180373 : Blo 159796 180373 := bbase (se 6 (by rfl) ⟨4227, by rfl⟩ : syracuseStep 180373 = 8455) (by norm_num)
theorem B180409 : Blo 159796 180409 := bbase (se 2 (by rfl) ⟨67653, by rfl⟩ : syracuseStep 180409 = 135307) (by norm_num)
theorem B180445 : Blo 159796 180445 := bbase (se 3 (by rfl) ⟨33833, by rfl⟩ : syracuseStep 180445 = 67667) (by norm_num)
theorem B540917 : Blo 159796 540917 := bbase (se 5 (by rfl) ⟨25355, by rfl⟩ : syracuseStep 540917 = 50711) (by norm_num)
theorem B180481 : Blo 159796 180481 := bbase (se 2 (by rfl) ⟨67680, by rfl⟩ : syracuseStep 180481 = 135361) (by norm_num)
theorem B180517 : Blo 159796 180517 := bbase (se 4 (by rfl) ⟨16923, by rfl⟩ : syracuseStep 180517 = 33847) (by norm_num)
theorem B180553 : Blo 159796 180553 := bbase (se 2 (by rfl) ⟨67707, by rfl⟩ : syracuseStep 180553 = 135415) (by norm_num)
theorem B180589 : Blo 159796 180589 := bbase (se 3 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 180589 = 67721) (by norm_num)
theorem B409981 : Blo 159796 409981 := bbase (se 3 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 409981 = 153743) (by norm_num)
theorem B180625 : Blo 159796 180625 := bbase (se 2 (by rfl) ⟨67734, by rfl⟩ : syracuseStep 180625 = 135469) (by norm_num)
theorem B180661 : Blo 159796 180661 := bbase (se 5 (by rfl) ⟨8468, by rfl⟩ : syracuseStep 180661 = 16937) (by norm_num)
theorem B180697 : Blo 159796 180697 := bbase (se 2 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 180697 = 135523) (by norm_num)
theorem B410093 : Blo 159796 410093 := bbase (se 3 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 410093 = 153785) (by norm_num)
theorem B279029 : Blo 159796 279029 := bbase (se 5 (by rfl) ⟨13079, by rfl⟩ : syracuseStep 279029 = 26159) (by norm_num)
theorem B180733 : Blo 159796 180733 := bbase (se 3 (by rfl) ⟨33887, by rfl⟩ : syracuseStep 180733 = 67775) (by norm_num)
theorem B180769 : Blo 159796 180769 := bbase (se 2 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 180769 = 135577) (by norm_num)
theorem B180805 : Blo 159796 180805 := bbase (se 4 (by rfl) ⟨16950, by rfl⟩ : syracuseStep 180805 = 33901) (by norm_num)
theorem B1458773 : Blo 159796 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B246365 : Blo 159796 246365 := bbase (se 3 (by rfl) ⟨46193, by rfl⟩ : syracuseStep 246365 = 92387) (by norm_num)
theorem B180841 : Blo 159796 180841 := bbase (se 2 (by rfl) ⟨67815, by rfl⟩ : syracuseStep 180841 = 135631) (by norm_num)
theorem B180877 : Blo 159796 180877 := bbase (se 3 (by rfl) ⟨33914, by rfl⟩ : syracuseStep 180877 = 67829) (by norm_num)
theorem B541349 : Blo 159796 541349 := bbase (se 4 (by rfl) ⟨50751, by rfl⟩ : syracuseStep 541349 = 101503) (by norm_num)
theorem B410285 : Blo 159796 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B180913 : Blo 159796 180913 := bbase (se 2 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 180913 = 135685) (by norm_num)
theorem B180949 : Blo 159796 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B180985 : Blo 159796 180985 := bbase (se 2 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 180985 = 135739) (by norm_num)
theorem B181021 : Blo 159796 181021 := bbase (se 3 (by rfl) ⟨33941, by rfl⟩ : syracuseStep 181021 = 67883) (by norm_num)
theorem B181057 : Blo 159796 181057 := bbase (se 2 (by rfl) ⟨67896, by rfl⟩ : syracuseStep 181057 = 135793) (by norm_num)
theorem B181093 : Blo 159796 181093 := bbase (se 4 (by rfl) ⟨16977, by rfl⟩ : syracuseStep 181093 = 33955) (by norm_num)
theorem B181129 : Blo 159796 181129 := bbase (se 2 (by rfl) ⟨67923, by rfl⟩ : syracuseStep 181129 = 135847) (by norm_num)
theorem B181165 : Blo 159796 181165 := bbase (se 3 (by rfl) ⟨33968, by rfl⟩ : syracuseStep 181165 = 67937) (by norm_num)
theorem B181201 : Blo 159796 181201 := bbase (se 2 (by rfl) ⟨67950, by rfl⟩ : syracuseStep 181201 = 135901) (by norm_num)
theorem B181237 : Blo 159796 181237 := bbase (se 5 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 181237 = 16991) (by norm_num)
theorem B410629 : Blo 159796 410629 := bbase (se 4 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 410629 = 76993) (by norm_num)
theorem B181273 : Blo 159796 181273 := bbase (se 2 (by rfl) ⟨67977, by rfl⟩ : syracuseStep 181273 = 135955) (by norm_num)
theorem B181309 : Blo 159796 181309 := bbase (se 3 (by rfl) ⟨33995, by rfl⟩ : syracuseStep 181309 = 67991) (by norm_num)
theorem B541781 : Blo 159796 541781 := bbase (se 8 (by rfl) ⟨3174, by rfl⟩ : syracuseStep 541781 = 6349) (by norm_num)
theorem B181345 : Blo 159796 181345 := bbase (se 2 (by rfl) ⟨68004, by rfl⟩ : syracuseStep 181345 = 136009) (by norm_num)
theorem B345197 : Blo 159796 345197 := bbase (se 3 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 345197 = 129449) (by norm_num)
theorem B410741 : Blo 159796 410741 := bbase (se 5 (by rfl) ⟨19253, by rfl⟩ : syracuseStep 410741 = 38507) (by norm_num)
theorem B181381 : Blo 159796 181381 := bbase (se 4 (by rfl) ⟨17004, by rfl⟩ : syracuseStep 181381 = 34009) (by norm_num)
theorem B181417 : Blo 159796 181417 := bbase (se 2 (by rfl) ⟨68031, by rfl⟩ : syracuseStep 181417 = 136063) (by norm_num)
theorem B181453 : Blo 159796 181453 := bbase (se 3 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 181453 = 68045) (by norm_num)
theorem B181489 : Blo 159796 181489 := bbase (se 2 (by rfl) ⟨68058, by rfl⟩ : syracuseStep 181489 = 136117) (by norm_num)
theorem B345341 : Blo 159796 345341 := bbase (se 3 (by rfl) ⟨64751, by rfl⟩ : syracuseStep 345341 = 129503) (by norm_num)
theorem B181525 : Blo 159796 181525 := bbase (se 6 (by rfl) ⟨4254, by rfl⟩ : syracuseStep 181525 = 8509) (by norm_num)
theorem B410933 : Blo 159796 410933 := bbase (se 5 (by rfl) ⟨19262, by rfl⟩ : syracuseStep 410933 = 38525) (by norm_num)
theorem B181561 : Blo 159796 181561 := bbase (se 2 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 181561 = 136171) (by norm_num)
theorem B181597 : Blo 159796 181597 := bbase (se 3 (by rfl) ⟨34049, by rfl⟩ : syracuseStep 181597 = 68099) (by norm_num)
theorem B181633 : Blo 159796 181633 := bbase (se 2 (by rfl) ⟨68112, by rfl⟩ : syracuseStep 181633 = 136225) (by norm_num)
theorem B607621 : Blo 159796 607621 := bbase (se 4 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 607621 = 113929) (by norm_num)
theorem B181669 : Blo 159796 181669 := bbase (se 4 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 181669 = 34063) (by norm_num)
theorem B181705 : Blo 159796 181705 := bbase (se 2 (by rfl) ⟨68139, by rfl⟩ : syracuseStep 181705 = 136279) (by norm_num)
theorem B181741 : Blo 159796 181741 := bbase (se 3 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 181741 = 68153) (by norm_num)
theorem B542213 : Blo 159796 542213 := bbase (se 4 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 542213 = 101665) (by norm_num)
theorem B181777 : Blo 159796 181777 := bbase (se 2 (by rfl) ⟨68166, by rfl⟩ : syracuseStep 181777 = 136333) (by norm_num)
theorem B181813 : Blo 159796 181813 := bbase (se 5 (by rfl) ⟨8522, by rfl⟩ : syracuseStep 181813 = 17045) (by norm_num)
theorem B181849 : Blo 159796 181849 := bbase (se 2 (by rfl) ⟨68193, by rfl⟩ : syracuseStep 181849 = 136387) (by norm_num)
theorem B345701 : Blo 159796 345701 := bbase (se 4 (by rfl) ⟨32409, by rfl⟩ : syracuseStep 345701 = 64819) (by norm_num)
theorem B181885 : Blo 159796 181885 := bbase (se 3 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 181885 = 68207) (by norm_num)
theorem B411277 : Blo 159796 411277 := bbase (se 3 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 411277 = 154229) (by norm_num)
theorem B181921 : Blo 159796 181921 := bbase (se 2 (by rfl) ⟨68220, by rfl⟩ : syracuseStep 181921 = 136441) (by norm_num)
theorem B607925 : Blo 159796 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B181957 : Blo 159796 181957 := bbase (se 4 (by rfl) ⟨17058, by rfl⟩ : syracuseStep 181957 = 34117) (by norm_num)
theorem B181993 : Blo 159796 181993 := bbase (se 2 (by rfl) ⟨68247, by rfl⟩ : syracuseStep 181993 = 136495) (by norm_num)
theorem B411389 : Blo 159796 411389 := bbase (se 3 (by rfl) ⟨77135, by rfl⟩ : syracuseStep 411389 = 154271) (by norm_num)
theorem B182029 : Blo 159796 182029 := bbase (se 3 (by rfl) ⟨34130, by rfl⟩ : syracuseStep 182029 = 68261) (by norm_num)
theorem B182065 : Blo 159796 182065 := bbase (se 2 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 182065 = 136549) (by norm_num)
theorem B182101 : Blo 159796 182101 := bbase (se 9 (by rfl) ⟨533, by rfl⟩ : syracuseStep 182101 = 1067) (by norm_num)
theorem B182137 : Blo 159796 182137 := bbase (se 2 (by rfl) ⟨68301, by rfl⟩ : syracuseStep 182137 = 136603) (by norm_num)
theorem B182173 : Blo 159796 182173 := bbase (se 3 (by rfl) ⟨34157, by rfl⟩ : syracuseStep 182173 = 68315) (by norm_num)
theorem B542645 : Blo 159796 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B411581 : Blo 159796 411581 := bbase (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) (by norm_num)
theorem B182209 : Blo 159796 182209 := bbase (se 2 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 182209 = 136657) (by norm_num)
theorem B182245 : Blo 159796 182245 := bbase (se 4 (by rfl) ⟨17085, by rfl⟩ : syracuseStep 182245 = 34171) (by norm_num)
theorem B182281 : Blo 159796 182281 := bbase (se 2 (by rfl) ⟨68355, by rfl⟩ : syracuseStep 182281 = 136711) (by norm_num)
theorem B182317 : Blo 159796 182317 := bbase (se 3 (by rfl) ⟨34184, by rfl⟩ : syracuseStep 182317 = 68369) (by norm_num)
theorem B182353 : Blo 159796 182353 := bbase (se 2 (by rfl) ⟨68382, by rfl⟩ : syracuseStep 182353 = 136765) (by norm_num)
theorem B182389 : Blo 159796 182389 := bbase (se 5 (by rfl) ⟨8549, by rfl⟩ : syracuseStep 182389 = 17099) (by norm_num)
theorem B182425 : Blo 159796 182425 := bbase (se 2 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 182425 = 136819) (by norm_num)
theorem B182461 : Blo 159796 182461 := bbase (se 3 (by rfl) ⟨34211, by rfl⟩ : syracuseStep 182461 = 68423) (by norm_num)
theorem B182497 : Blo 159796 182497 := bbase (se 2 (by rfl) ⟨68436, by rfl⟩ : syracuseStep 182497 = 136873) (by norm_num)
theorem B182533 : Blo 159796 182533 := bbase (se 4 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 182533 = 34225) (by norm_num)
theorem B1165589 : Blo 159796 1165589 := bbase (se 6 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 1165589 = 54637) (by norm_num)
theorem B411925 : Blo 159796 411925 := bbase (se 6 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 411925 = 19309) (by norm_num)
theorem B182569 : Blo 159796 182569 := bbase (se 2 (by rfl) ⟨68463, by rfl⟩ : syracuseStep 182569 = 136927) (by norm_num)
theorem B182605 : Blo 159796 182605 := bbase (se 3 (by rfl) ⟨34238, by rfl⟩ : syracuseStep 182605 = 68477) (by norm_num)
theorem B248141 : Blo 159796 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B543077 : Blo 159796 543077 := bbase (se 4 (by rfl) ⟨50913, by rfl⟩ : syracuseStep 543077 = 101827) (by norm_num)
theorem B182641 : Blo 159796 182641 := bbase (se 2 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 182641 = 136981) (by norm_num)
theorem B248189 : Blo 159796 248189 := bbase (se 3 (by rfl) ⟨46535, by rfl⟩ : syracuseStep 248189 = 93071) (by norm_num)
theorem B412037 : Blo 159796 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B182677 : Blo 159796 182677 := bbase (se 6 (by rfl) ⟨4281, by rfl⟩ : syracuseStep 182677 = 8563) (by norm_num)
theorem B1100213 : Blo 159796 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B182713 : Blo 159796 182713 := bbase (se 2 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 182713 = 137035) (by norm_num)
theorem B346589 : Blo 159796 346589 := bbase (se 3 (by rfl) ⟨64985, by rfl⟩ : syracuseStep 346589 = 129971) (by norm_num)
theorem B182749 : Blo 159796 182749 := bbase (se 3 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 182749 = 68531) (by norm_num)
theorem B182785 : Blo 159796 182785 := bbase (se 2 (by rfl) ⟨68544, by rfl⟩ : syracuseStep 182785 = 137089) (by norm_num)
theorem B182821 : Blo 159796 182821 := bbase (se 4 (by rfl) ⟨17139, by rfl⟩ : syracuseStep 182821 = 34279) (by norm_num)
theorem B412229 : Blo 159796 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B182857 : Blo 159796 182857 := bbase (se 2 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 182857 = 137143) (by norm_num)
theorem B182893 : Blo 159796 182893 := bbase (se 3 (by rfl) ⟨34292, by rfl⟩ : syracuseStep 182893 = 68585) (by norm_num)
theorem B182929 : Blo 159796 182929 := bbase (se 2 (by rfl) ⟨68598, by rfl⟩ : syracuseStep 182929 = 137197) (by norm_num)
theorem B182965 : Blo 159796 182965 := bbase (se 5 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 182965 = 17153) (by norm_num)
theorem B346837 : Blo 159796 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B183001 : Blo 159796 183001 := bbase (se 2 (by rfl) ⟨68625, by rfl⟩ : syracuseStep 183001 = 137251) (by norm_num)
theorem B183037 : Blo 159796 183037 := bbase (se 3 (by rfl) ⟨34319, by rfl⟩ : syracuseStep 183037 = 68639) (by norm_num)
theorem B543509 : Blo 159796 543509 := bbase (se 6 (by rfl) ⟨12738, by rfl⟩ : syracuseStep 543509 = 25477) (by norm_num)
theorem B183073 : Blo 159796 183073 := bbase (se 2 (by rfl) ⟨68652, by rfl⟩ : syracuseStep 183073 = 137305) (by norm_num)
theorem B183109 : Blo 159796 183109 := bbase (se 4 (by rfl) ⟨17166, by rfl⟩ : syracuseStep 183109 = 34333) (by norm_num)
theorem B183145 : Blo 159796 183145 := bbase (se 2 (by rfl) ⟨68679, by rfl⟩ : syracuseStep 183145 = 137359) (by norm_num)
theorem B183181 : Blo 159796 183181 := bbase (se 3 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 183181 = 68693) (by norm_num)
theorem B412573 : Blo 159796 412573 := bbase (se 3 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 412573 = 154715) (by norm_num)
theorem B183217 : Blo 159796 183217 := bbase (se 2 (by rfl) ⟨68706, by rfl⟩ : syracuseStep 183217 = 137413) (by norm_num)
theorem B183253 : Blo 159796 183253 := bbase (se 7 (by rfl) ⟨2147, by rfl⟩ : syracuseStep 183253 = 4295) (by norm_num)
theorem B183289 : Blo 159796 183289 := bbase (se 2 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 183289 = 137467) (by norm_num)
theorem B412685 : Blo 159796 412685 := bbase (se 3 (by rfl) ⟨77378, by rfl⟩ : syracuseStep 412685 = 154757) (by norm_num)
theorem B1559573 : Blo 159796 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B183325 : Blo 159796 183325 := bbase (se 3 (by rfl) ⟨34373, by rfl⟩ : syracuseStep 183325 = 68747) (by norm_num)
theorem B773173 : Blo 159796 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B183361 : Blo 159796 183361 := bbase (se 2 (by rfl) ⟨68760, by rfl⟩ : syracuseStep 183361 = 137521) (by norm_num)
theorem B183397 : Blo 159796 183397 := bbase (se 4 (by rfl) ⟨17193, by rfl⟩ : syracuseStep 183397 = 34387) (by norm_num)
theorem B314501 : Blo 159796 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B183433 : Blo 159796 183433 := bbase (se 2 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 183433 = 137575) (by norm_num)
theorem B183469 : Blo 159796 183469 := bbase (se 3 (by rfl) ⟨34400, by rfl⟩ : syracuseStep 183469 = 68801) (by norm_num)
theorem B543941 : Blo 159796 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B347341 : Blo 159796 347341 := bbase (se 3 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 347341 = 130253) (by norm_num)
theorem B412877 : Blo 159796 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B183505 : Blo 159796 183505 := bbase (se 2 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 183505 = 137629) (by norm_num)
theorem B183541 : Blo 159796 183541 := bbase (se 5 (by rfl) ⟨8603, by rfl⟩ : syracuseStep 183541 = 17207) (by norm_num)
theorem B183577 : Blo 159796 183577 := bbase (se 2 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 183577 = 137683) (by norm_num)
theorem B183613 : Blo 159796 183613 := bbase (se 3 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 183613 = 68855) (by norm_num)
theorem B183649 : Blo 159796 183649 := bbase (se 2 (by rfl) ⟨68868, by rfl⟩ : syracuseStep 183649 = 137737) (by norm_num)
theorem B183685 : Blo 159796 183685 := bbase (se 4 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 183685 = 34441) (by norm_num)
theorem B183721 : Blo 159796 183721 := bbase (se 2 (by rfl) ⟨68895, by rfl⟩ : syracuseStep 183721 = 137791) (by norm_num)
theorem B183757 : Blo 159796 183757 := bbase (se 3 (by rfl) ⟨34454, by rfl⟩ : syracuseStep 183757 = 68909) (by norm_num)
theorem B183793 : Blo 159796 183793 := bbase (se 2 (by rfl) ⟨68922, by rfl⟩ : syracuseStep 183793 = 137845) (by norm_num)
theorem B183829 : Blo 159796 183829 := bbase (se 6 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 183829 = 8617) (by norm_num)
theorem B413221 : Blo 159796 413221 := bbase (se 4 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 413221 = 77479) (by norm_num)
theorem B183865 : Blo 159796 183865 := bbase (se 2 (by rfl) ⟨68949, by rfl⟩ : syracuseStep 183865 = 137899) (by norm_num)
theorem B183901 : Blo 159796 183901 := bbase (se 3 (by rfl) ⟨34481, by rfl⟩ : syracuseStep 183901 = 68963) (by norm_num)
theorem B544373 : Blo 159796 544373 := bbase (se 5 (by rfl) ⟨25517, by rfl⟩ : syracuseStep 544373 = 51035) (by norm_num)
theorem B183937 : Blo 159796 183937 := bbase (se 2 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 183937 = 137953) (by norm_num)
theorem B413333 : Blo 159796 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B183973 : Blo 159796 183973 := bbase (se 4 (by rfl) ⟨17247, by rfl⟩ : syracuseStep 183973 = 34495) (by norm_num)
theorem B184009 : Blo 159796 184009 := bbase (se 2 (by rfl) ⟨69003, by rfl⟩ : syracuseStep 184009 = 138007) (by norm_num)
theorem B184045 : Blo 159796 184045 := bbase (se 3 (by rfl) ⟨34508, by rfl⟩ : syracuseStep 184045 = 69017) (by norm_num)
theorem B610037 : Blo 159796 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B184081 : Blo 159796 184081 := bbase (se 2 (by rfl) ⟨69030, by rfl⟩ : syracuseStep 184081 = 138061) (by norm_num)
theorem B184117 : Blo 159796 184117 := bbase (se 5 (by rfl) ⟨8630, by rfl⟩ : syracuseStep 184117 = 17261) (by norm_num)
theorem B413525 : Blo 159796 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B5820245 : Blo 159796 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B184153 : Blo 159796 184153 := bbase (se 2 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 184153 = 138115) (by norm_num)
theorem B184189 : Blo 159796 184189 := bbase (se 3 (by rfl) ⟨34535, by rfl⟩ : syracuseStep 184189 = 69071) (by norm_num)
theorem B184225 : Blo 159796 184225 := bbase (se 2 (by rfl) ⟨69084, by rfl⟩ : syracuseStep 184225 = 138169) (by norm_num)
theorem B184261 : Blo 159796 184261 := bbase (se 4 (by rfl) ⟨17274, by rfl⟩ : syracuseStep 184261 = 34549) (by norm_num)
theorem B610325 : Blo 159796 610325 := bbase (se 6 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 610325 = 28609) (by norm_num)
theorem B577573 : Blo 159796 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B544805 : Blo 159796 544805 := bbase (se 4 (by rfl) ⟨51075, by rfl⟩ : syracuseStep 544805 = 102151) (by norm_num)
theorem B348229 : Blo 159796 348229 := bbase (se 4 (by rfl) ⟨32646, by rfl⟩ : syracuseStep 348229 = 65293) (by norm_num)
theorem B1232981 : Blo 159796 1232981 := bbase (se 8 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 1232981 = 14449) (by norm_num)
theorem B413869 : Blo 159796 413869 := bbase (se 3 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 413869 = 155201) (by norm_num)
theorem B413981 : Blo 159796 413981 := bbase (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) (by norm_num)
theorem B741797 : Blo 159796 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B545237 : Blo 159796 545237 := bbase (se 7 (by rfl) ⟨6389, by rfl⟩ : syracuseStep 545237 = 12779) (by norm_num)
theorem B414173 : Blo 159796 414173 := bbase (se 3 (by rfl) ⟨77657, by rfl⟩ : syracuseStep 414173 = 155315) (by norm_num)
theorem B283133 : Blo 159796 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B348725 : Blo 159796 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B414517 : Blo 159796 414517 := bbase (se 5 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 414517 = 38861) (by norm_num)
theorem B545669 : Blo 159796 545669 := bbase (se 4 (by rfl) ⟨51156, by rfl⟩ : syracuseStep 545669 = 102313) (by norm_num)
theorem B611509 : Blo 159796 611509 := bbase (se 5 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 611509 = 57329) (by norm_num)
theorem B1823957 : Blo 159796 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B546101 : Blo 159796 546101 := bbase (se 5 (by rfl) ⟨25598, by rfl⟩ : syracuseStep 546101 = 51197) (by norm_num)
theorem B185665 : Blo 159796 185665 := bbase (se 2 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 185665 = 139249) (by norm_num)
theorem B218461 : Blo 159796 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B1037717 : Blo 159796 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B349613 : Blo 159796 349613 := bbase (se 3 (by rfl) ⟨65552, by rfl⟩ : syracuseStep 349613 = 131105) (by norm_num)
theorem B611813 : Blo 159796 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B349733 : Blo 159796 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B546533 : Blo 159796 546533 := bbase (se 4 (by rfl) ⟨51237, by rfl⟩ : syracuseStep 546533 = 102475) (by norm_num)
theorem B1365781 : Blo 159796 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B186397 : Blo 159796 186397 := bbase (se 3 (by rfl) ⟨34949, by rfl⟩ : syracuseStep 186397 = 69899) (by norm_num)
theorem B546965 : Blo 159796 546965 := bbase (se 6 (by rfl) ⟨12819, by rfl⟩ : syracuseStep 546965 = 25639) (by norm_num)
theorem B809189 : Blo 159796 809189 := bbase (se 4 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 809189 = 151723) (by norm_num)
theorem B1038581 : Blo 159796 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B547397 : Blo 159796 547397 := bbase (se 4 (by rfl) ⟨51318, by rfl⟩ : syracuseStep 547397 = 102637) (by norm_num)
theorem B973397 : Blo 159796 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B776789 : Blo 159796 776789 := bbase (se 8 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 776789 = 9103) (by norm_num)
theorem B580229 : Blo 159796 580229 := bbase (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) (by norm_num)
theorem B219845 : Blo 159796 219845 := bbase (se 4 (by rfl) ⟨20610, by rfl⟩ : syracuseStep 219845 = 41221) (by norm_num)
theorem B219877 : Blo 159796 219877 := bbase (se 4 (by rfl) ⟨20613, by rfl⟩ : syracuseStep 219877 = 41227) (by norm_num)
theorem B187301 : Blo 159796 187301 := bbase (se 4 (by rfl) ⟨17559, by rfl⟩ : syracuseStep 187301 = 35119) (by norm_num)
theorem B580517 : Blo 159796 580517 := bbase (se 4 (by rfl) ⟨54423, by rfl⟩ : syracuseStep 580517 = 108847) (by norm_num)
theorem B547829 : Blo 159796 547829 := bbase (se 5 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 547829 = 51359) (by norm_num)
theorem B220205 : Blo 159796 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B843061 : Blo 159796 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B548261 : Blo 159796 548261 := bbase (se 4 (by rfl) ⟨51399, by rfl⟩ : syracuseStep 548261 = 102799) (by norm_num)
theorem B810485 : Blo 159796 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B613925 : Blo 159796 613925 := bbase (se 4 (by rfl) ⟨57555, by rfl⟩ : syracuseStep 613925 = 115111) (by norm_num)
theorem B1367765 : Blo 159796 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B581381 : Blo 159796 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B614213 : Blo 159796 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B548693 : Blo 159796 548693 := bbase (se 9 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 548693 = 3215) (by norm_num)
theorem B319405 : Blo 159796 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B385165 : Blo 159796 385165 := bbase (se 3 (by rfl) ⟨72218, by rfl⟩ : syracuseStep 385165 = 144437) (by norm_num)
theorem B549125 : Blo 159796 549125 := bbase (se 4 (by rfl) ⟨51480, by rfl⟩ : syracuseStep 549125 = 102961) (by norm_num)
theorem B581957 : Blo 159796 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B778693 : Blo 159796 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B778709 : Blo 159796 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B352757 : Blo 159796 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B746101 : Blo 159796 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B221869 : Blo 159796 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B549557 : Blo 159796 549557 := bbase (se 5 (by rfl) ⟨25760, by rfl⟩ : syracuseStep 549557 = 51521) (by norm_num)
theorem B811781 : Blo 159796 811781 := bbase (se 4 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 811781 = 152209) (by norm_num)
theorem B517013 : Blo 159796 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B615397 : Blo 159796 615397 := bbase (se 4 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 615397 = 115387) (by norm_num)
theorem B353261 : Blo 159796 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B2057237 : Blo 159796 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B549989 : Blo 159796 549989 := bbase (se 4 (by rfl) ⟨51561, by rfl⟩ : syracuseStep 549989 = 103123) (by norm_num)
theorem B615701 : Blo 159796 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B386549 : Blo 159796 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B288269 : Blo 159796 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B550421 : Blo 159796 550421 := bbase (se 6 (by rfl) ⟨12900, by rfl⟩ : syracuseStep 550421 = 25801) (by norm_num)
theorem B386741 : Blo 159796 386741 := bbase (se 5 (by rfl) ⟨18128, by rfl⟩ : syracuseStep 386741 = 36257) (by norm_num)
theorem B517909 : Blo 159796 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B419717 : Blo 159796 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B550853 : Blo 159796 550853 := bbase (se 4 (by rfl) ⟨51642, by rfl⟩ : syracuseStep 550853 = 103285) (by norm_num)
theorem B813077 : Blo 159796 813077 := bbase (se 6 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 813077 = 38113) (by norm_num)
theorem B518309 : Blo 159796 518309 := bbase (se 4 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 518309 = 97183) (by norm_num)
theorem B583861 : Blo 159796 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B256213 : Blo 159796 256213 := bbase (se 7 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 256213 = 6005) (by norm_num)
theorem B190769 : Blo 159796 190769 := bbase (se 2 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 190769 = 143077) (by norm_num)
theorem B551285 : Blo 159796 551285 := bbase (se 5 (by rfl) ⟨25841, by rfl⟩ : syracuseStep 551285 = 51683) (by norm_num)
theorem B387509 : Blo 159796 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B616901 : Blo 159796 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B682789 : Blo 159796 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B781093 : Blo 159796 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B551717 : Blo 159796 551717 := bbase (se 4 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 551717 = 103447) (by norm_num)
theorem B584597 : Blo 159796 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B1043381 : Blo 159796 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B650405 : Blo 159796 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B552149 : Blo 159796 552149 := bbase (se 7 (by rfl) ⟨6470, by rfl⟩ : syracuseStep 552149 = 12941) (by norm_num)
theorem B814373 : Blo 159796 814373 := bbase (se 4 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 814373 = 152695) (by norm_num)
theorem B650549 : Blo 159796 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B617813 : Blo 159796 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B421373 : Blo 159796 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B257597 : Blo 159796 257597 := bbase (se 3 (by rfl) ⟨48299, by rfl⟩ : syracuseStep 257597 = 96599) (by norm_num)
theorem B618101 : Blo 159796 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B552581 : Blo 159796 552581 := bbase (se 4 (by rfl) ⟨51804, by rfl⟩ : syracuseStep 552581 = 103609) (by norm_num)
theorem B1240757 : Blo 159796 1240757 := bbase (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) (by norm_num)
theorem B192217 : Blo 159796 192217 := bbase (se 2 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 192217 = 144163) (by norm_num)
theorem B257789 : Blo 159796 257789 := bbase (se 3 (by rfl) ⟨48335, by rfl⟩ : syracuseStep 257789 = 96671) (by norm_num)
theorem B913301 : Blo 159796 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B585877 : Blo 159796 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B520501 : Blo 159796 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B389605 : Blo 159796 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B815669 : Blo 159796 815669 := bbase (se 5 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 815669 = 76469) (by norm_num)
theorem B619285 : Blo 159796 619285 := bbase (se 6 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 619285 = 29029) (by norm_num)
theorem B291613 : Blo 159796 291613 := bbase (se 3 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 291613 = 109355) (by norm_num)
theorem B455557 : Blo 159796 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B291757 : Blo 159796 291757 := bbase (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) (by norm_num)
theorem B390149 : Blo 159796 390149 := bbase (se 4 (by rfl) ⟨36576, by rfl⟩ : syracuseStep 390149 = 73153) (by norm_num)
theorem B259109 : Blo 159796 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B193601 : Blo 159796 193601 := bbase (se 2 (by rfl) ⟨72600, by rfl⟩ : syracuseStep 193601 = 145201) (by norm_num)
theorem B619589 : Blo 159796 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B390221 : Blo 159796 390221 := bbase (se 3 (by rfl) ⟨73166, by rfl⟩ : syracuseStep 390221 = 146333) (by norm_num)
theorem B259205 : Blo 159796 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B390277 : Blo 159796 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B259237 : Blo 159796 259237 := bbase (se 4 (by rfl) ⟨24303, by rfl⟩ : syracuseStep 259237 = 48607) (by norm_num)
theorem B324821 : Blo 159796 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B324853 : Blo 159796 324853 := bbase (se 5 (by rfl) ⟨15227, by rfl⟩ : syracuseStep 324853 = 30455) (by norm_num)
theorem B193789 : Blo 159796 193789 := bbase (se 3 (by rfl) ⟨36335, by rfl⟩ : syracuseStep 193789 = 72671) (by norm_num)
theorem B194005 : Blo 159796 194005 := bbase (se 7 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 194005 = 4547) (by norm_num)
theorem B652789 : Blo 159796 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B325309 : Blo 159796 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B259781 : Blo 159796 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B980693 : Blo 159796 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B292565 : Blo 159796 292565 := bbase (se 7 (by rfl) ⟨3428, by rfl⟩ : syracuseStep 292565 = 6857) (by norm_num)
theorem B194293 : Blo 159796 194293 := bbase (se 5 (by rfl) ⟨9107, by rfl⟩ : syracuseStep 194293 = 18215) (by norm_num)
theorem B816965 : Blo 159796 816965 := bbase (se 4 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 816965 = 153181) (by norm_num)
theorem B522101 : Blo 159796 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B292781 : Blo 159796 292781 := bbase (se 3 (by rfl) ⟨54896, by rfl⟩ : syracuseStep 292781 = 109793) (by norm_num)
theorem B292853 : Blo 159796 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B292933 : Blo 159796 292933 := bbase (se 4 (by rfl) ⟨27462, by rfl⟩ : syracuseStep 292933 = 54925) (by norm_num)
theorem B391277 : Blo 159796 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B292997 : Blo 159796 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B325981 : Blo 159796 325981 := bbase (se 3 (by rfl) ⟨61121, by rfl⟩ : syracuseStep 325981 = 122243) (by norm_num)
theorem B293285 : Blo 159796 293285 := bbase (se 4 (by rfl) ⟨27495, by rfl⟩ : syracuseStep 293285 = 54991) (by norm_num)
theorem B784997 : Blo 159796 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B260749 : Blo 159796 260749 := bbase (se 3 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 260749 = 97781) (by norm_num)
theorem B228109 : Blo 159796 228109 := bbase (se 3 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 228109 = 85541) (by norm_num)
theorem B162605 : Blo 159796 162605 := bbase (se 3 (by rfl) ⟨30488, by rfl⟩ : syracuseStep 162605 = 60977) (by norm_num)
theorem B523189 : Blo 159796 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B195581 : Blo 159796 195581 := bbase (se 3 (by rfl) ⟨36671, by rfl⟩ : syracuseStep 195581 = 73343) (by norm_num)
theorem B818261 : Blo 159796 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B359549 : Blo 159796 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B621701 : Blo 159796 621701 := bbase (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) (by norm_num)
theorem B359621 : Blo 159796 359621 := bbase (se 4 (by rfl) ⟨33714, by rfl⟩ : syracuseStep 359621 = 67429) (by norm_num)
theorem B359693 : Blo 159796 359693 := bbase (se 3 (by rfl) ⟨67442, by rfl⟩ : syracuseStep 359693 = 134885) (by norm_num)
theorem B359765 : Blo 159796 359765 := bbase (se 11 (by rfl) ⟨263, by rfl⟩ : syracuseStep 359765 = 527) (by norm_num)
theorem B261461 : Blo 159796 261461 := bbase (se 11 (by rfl) ⟨191, by rfl⟩ : syracuseStep 261461 = 383) (by norm_num)
theorem B228701 : Blo 159796 228701 := bbase (se 3 (by rfl) ⟨42881, by rfl⟩ : syracuseStep 228701 = 85763) (by norm_num)
theorem B359837 : Blo 159796 359837 := bbase (se 3 (by rfl) ⟨67469, by rfl⟩ : syracuseStep 359837 = 134939) (by norm_num)
theorem B228781 : Blo 159796 228781 := bbase (se 3 (by rfl) ⟨42896, by rfl⟩ : syracuseStep 228781 = 85793) (by norm_num)
theorem B359909 : Blo 159796 359909 := bbase (se 4 (by rfl) ⟨33741, by rfl⟩ : syracuseStep 359909 = 67483) (by norm_num)
theorem B228901 : Blo 159796 228901 := bbase (se 4 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 228901 = 42919) (by norm_num)
theorem B359981 : Blo 159796 359981 := bbase (se 3 (by rfl) ⟨67496, by rfl⟩ : syracuseStep 359981 = 134993) (by norm_num)
theorem B327221 : Blo 159796 327221 := bbase (se 5 (by rfl) ⟨15338, by rfl⟩ : syracuseStep 327221 = 30677) (by norm_num)
theorem B196177 : Blo 159796 196177 := bbase (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) (by norm_num)
theorem B982613 : Blo 159796 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B360053 : Blo 159796 360053 := bbase (se 5 (by rfl) ⟨16877, by rfl⟩ : syracuseStep 360053 = 33755) (by norm_num)
theorem B1638005 : Blo 159796 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B228997 : Blo 159796 228997 := bbase (se 4 (by rfl) ⟨21468, by rfl⟩ : syracuseStep 228997 = 42937) (by norm_num)
theorem B458405 : Blo 159796 458405 := bbase (se 4 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 458405 = 85951) (by norm_num)
theorem B196273 : Blo 159796 196273 := bbase (se 2 (by rfl) ⟨73602, by rfl⟩ : syracuseStep 196273 = 147205) (by norm_num)
theorem B687797 : Blo 159796 687797 := bbase (se 5 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 687797 = 64481) (by norm_num)
theorem B360125 : Blo 159796 360125 := bbase (se 3 (by rfl) ⟨67523, by rfl⟩ : syracuseStep 360125 = 135047) (by norm_num)
theorem B294605 : Blo 159796 294605 := bbase (se 3 (by rfl) ⟨55238, by rfl⟩ : syracuseStep 294605 = 110477) (by norm_num)
theorem B360197 : Blo 159796 360197 := bbase (se 4 (by rfl) ⟨33768, by rfl⟩ : syracuseStep 360197 = 67537) (by norm_num)
theorem B360269 : Blo 159796 360269 := bbase (se 3 (by rfl) ⟨67550, by rfl⟩ : syracuseStep 360269 = 135101) (by norm_num)
theorem B3211093 : Blo 159796 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B360341 : Blo 159796 360341 := bbase (se 6 (by rfl) ⟨8445, by rfl⟩ : syracuseStep 360341 = 16891) (by norm_num)
theorem B196549 : Blo 159796 196549 := bbase (se 4 (by rfl) ⟨18426, by rfl⟩ : syracuseStep 196549 = 36853) (by norm_num)
theorem B688085 : Blo 159796 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B360413 : Blo 159796 360413 := bbase (se 3 (by rfl) ⟨67577, by rfl⟩ : syracuseStep 360413 = 135155) (by norm_num)
theorem B262133 : Blo 159796 262133 := bbase (se 5 (by rfl) ⟨12287, by rfl⟩ : syracuseStep 262133 = 24575) (by norm_num)
theorem B360593 : Blo 159796 360593 := bstep (se 2 (by rfl) ⟨135222, by rfl⟩ : syracuseStep 360593 = 270445) B270445
theorem B360611 : Blo 159796 360611 := bstep (se 1 (by rfl) ⟨270458, by rfl⟩ : syracuseStep 360611 = 540917) B540917
theorem B3080389 : Blo 159796 3080389 := bstep (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) B577573
theorem B229601 : Blo 159796 229601 := bstep (se 2 (by rfl) ⟨86100, by rfl⟩ : syracuseStep 229601 = 172201) B172201
theorem B524675 : Blo 159796 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B164243 : Blo 159796 164243 := bstep (se 1 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 164243 = 246365) B246365
theorem B360881 : Blo 159796 360881 := bstep (se 2 (by rfl) ⟨135330, by rfl⟩ : syracuseStep 360881 = 270661) B270661
theorem B360899 : Blo 159796 360899 := bstep (se 1 (by rfl) ⟨270674, by rfl⟩ : syracuseStep 360899 = 541349) B541349
theorem B328259 : Blo 159796 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B361169 : Blo 159796 361169 := bstep (se 2 (by rfl) ⟨135438, by rfl⟩ : syracuseStep 361169 = 270877) B270877
theorem B262867 : Blo 159796 262867 := bstep (se 1 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 262867 = 394301) B394301
theorem B361187 : Blo 159796 361187 := bstep (se 1 (by rfl) ⟨270890, by rfl⟩ : syracuseStep 361187 = 541781) B541781
theorem B230131 : Blo 159796 230131 := bstep (se 1 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 230131 = 345197) B345197
theorem B459533 : Blo 159796 459533 := bstep (se 3 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 459533 = 172325) B172325
theorem B295825 : Blo 159796 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B918449 : Blo 159796 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B459715 : Blo 159796 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B361457 : Blo 159796 361457 := bstep (se 2 (by rfl) ⟨135546, by rfl⟩ : syracuseStep 361457 = 271093) B271093
theorem B361475 : Blo 159796 361475 := bstep (se 1 (by rfl) ⟨271106, by rfl⟩ : syracuseStep 361475 = 542213) B542213
theorem B230467 : Blo 159796 230467 := bstep (se 1 (by rfl) ⟨172850, by rfl⟩ : syracuseStep 230467 = 345701) B345701
theorem B361745 : Blo 159796 361745 := bstep (se 2 (by rfl) ⟨135654, by rfl⟩ : syracuseStep 361745 = 271309) B271309
theorem B361763 : Blo 159796 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B820529 : Blo 159796 820529 := bstep (se 2 (by rfl) ⟨307698, by rfl⟩ : syracuseStep 820529 = 615397) B615397
theorem B755021 : Blo 159796 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B460205 : Blo 159796 460205 := bstep (se 3 (by rfl) ⟨86288, by rfl⟩ : syracuseStep 460205 = 172577) B172577
theorem B362033 : Blo 159796 362033 := bstep (se 2 (by rfl) ⟨135762, by rfl⟩ : syracuseStep 362033 = 271525) B271525
theorem B362051 : Blo 159796 362051 := bstep (se 1 (by rfl) ⟨271538, by rfl⟩ : syracuseStep 362051 = 543077) B543077
theorem B231025 : Blo 159796 231025 := bstep (se 2 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 231025 = 173269) B173269
theorem B231059 : Blo 159796 231059 := bstep (se 1 (by rfl) ⟨173294, by rfl⟩ : syracuseStep 231059 = 346589) B346589
theorem B362321 : Blo 159796 362321 := bstep (se 2 (by rfl) ⟨135870, by rfl⟩ : syracuseStep 362321 = 271741) B271741
theorem B362339 : Blo 159796 362339 := bstep (se 1 (by rfl) ⟨271754, by rfl⟩ : syracuseStep 362339 = 543509) B543509
theorem B362609 : Blo 159796 362609 := bstep (se 2 (by rfl) ⟨135978, by rfl⟩ : syracuseStep 362609 = 271957) B271957
theorem B362627 : Blo 159796 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B231617 : Blo 159796 231617 := bstep (se 2 (by rfl) ⟨86856, by rfl⟩ : syracuseStep 231617 = 173713) B173713
theorem B231697 : Blo 159796 231697 := bstep (se 2 (by rfl) ⟨86886, by rfl⟩ : syracuseStep 231697 = 173773) B173773
theorem B919907 : Blo 159796 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B690545 : Blo 159796 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B362897 : Blo 159796 362897 := bstep (se 2 (by rfl) ⟨136086, by rfl⟩ : syracuseStep 362897 = 272173) B272173
theorem B362915 : Blo 159796 362915 := bstep (se 1 (by rfl) ⟨272186, by rfl⟩ : syracuseStep 362915 = 544373) B544373
theorem B461315 : Blo 159796 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B461389 : Blo 159796 461389 := bstep (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) B173021
theorem B363185 : Blo 159796 363185 := bstep (se 2 (by rfl) ⟨136194, by rfl⟩ : syracuseStep 363185 = 272389) B272389
theorem B363203 : Blo 159796 363203 := bstep (se 1 (by rfl) ⟨272402, by rfl⟩ : syracuseStep 363203 = 544805) B544805
theorem B527057 : Blo 159796 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B821987 : Blo 159796 821987 := bstep (se 1 (by rfl) ⟨616490, by rfl⟩ : syracuseStep 821987 = 1232981) B1232981
theorem B494531 : Blo 159796 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B363473 : Blo 159796 363473 := bstep (se 2 (by rfl) ⟨136302, by rfl⟩ : syracuseStep 363473 = 272605) B272605
theorem B363491 : Blo 159796 363491 := bstep (se 1 (by rfl) ⟨272618, by rfl⟩ : syracuseStep 363491 = 545237) B545237
theorem B691213 : Blo 159796 691213 := bstep (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) B259205
theorem B232483 : Blo 159796 232483 := bstep (se 1 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 232483 = 348725) B348725
theorem B363761 : Blo 159796 363761 := bstep (se 2 (by rfl) ⟨136410, by rfl⟩ : syracuseStep 363761 = 272821) B272821
theorem B363779 : Blo 159796 363779 := bstep (se 1 (by rfl) ⟨272834, by rfl⟩ : syracuseStep 363779 = 545669) B545669
theorem B920909 : Blo 159796 920909 := bstep (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) B345341
theorem B1215971 : Blo 159796 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B495089 : Blo 159796 495089 := bstep (se 2 (by rfl) ⟨185658, by rfl⟩ : syracuseStep 495089 = 371317) B371317
theorem B232961 : Blo 159796 232961 := bstep (se 2 (by rfl) ⟨87360, by rfl⟩ : syracuseStep 232961 = 174721) B174721
theorem B822797 : Blo 159796 822797 := bstep (se 3 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 822797 = 308549) B308549
theorem B364049 : Blo 159796 364049 := bstep (se 2 (by rfl) ⟨136518, by rfl⟩ : syracuseStep 364049 = 273037) B273037
theorem B364067 : Blo 159796 364067 := bstep (se 1 (by rfl) ⟨273050, by rfl⟩ : syracuseStep 364067 = 546101) B546101
theorem B691811 : Blo 159796 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B462449 : Blo 159796 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B233075 : Blo 159796 233075 := bstep (se 1 (by rfl) ⟨174806, by rfl⟩ : syracuseStep 233075 = 349613) B349613
theorem B1773197 : Blo 159796 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B233155 : Blo 159796 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B364337 : Blo 159796 364337 := bstep (se 2 (by rfl) ⟨136626, by rfl⟩ : syracuseStep 364337 = 273253) B273253
theorem B364355 : Blo 159796 364355 := bstep (se 1 (by rfl) ⟨273266, by rfl⟩ : syracuseStep 364355 = 546533) B546533
theorem B364625 : Blo 159796 364625 := bstep (se 2 (by rfl) ⟨136734, by rfl⟩ : syracuseStep 364625 = 273469) B273469
theorem B364643 : Blo 159796 364643 := bstep (se 1 (by rfl) ⟨273482, by rfl⟩ : syracuseStep 364643 = 546965) B546965
theorem B692387 : Blo 159796 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B463121 : Blo 159796 463121 := bstep (se 2 (by rfl) ⟨173670, by rfl⟩ : syracuseStep 463121 = 347341) B347341
theorem B364913 : Blo 159796 364913 := bstep (se 2 (by rfl) ⟨136842, by rfl⟩ : syracuseStep 364913 = 273685) B273685
theorem B364931 : Blo 159796 364931 := bstep (se 1 (by rfl) ⟨273698, by rfl⟩ : syracuseStep 364931 = 547397) B547397
theorem B2822597 : Blo 159796 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B692749 : Blo 159796 692749 := bstep (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) B259781
theorem B4133429 : Blo 159796 4133429 := bstep (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) B387509
theorem B627277 : Blo 159796 627277 := bstep (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) B235229
theorem B1053283 : Blo 159796 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B365201 : Blo 159796 365201 := bstep (se 2 (by rfl) ⟨136950, by rfl⟩ : syracuseStep 365201 = 273901) B273901
theorem B365219 : Blo 159796 365219 := bstep (se 1 (by rfl) ⟨273914, by rfl⟩ : syracuseStep 365219 = 547829) B547829
theorem B365489 : Blo 159796 365489 := bstep (se 2 (by rfl) ⟨137058, by rfl⟩ : syracuseStep 365489 = 274117) B274117
theorem B365507 : Blo 159796 365507 := bstep (se 1 (by rfl) ⟨274130, by rfl⟩ : syracuseStep 365507 = 548261) B548261
theorem B463907 : Blo 159796 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B365777 : Blo 159796 365777 := bstep (se 2 (by rfl) ⟨137166, by rfl⟩ : syracuseStep 365777 = 274333) B274333
theorem B365795 : Blo 159796 365795 := bstep (se 1 (by rfl) ⟨274346, by rfl⟩ : syracuseStep 365795 = 548693) B548693
theorem B464237 : Blo 159796 464237 := bstep (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) B174089
theorem B464305 : Blo 159796 464305 := bstep (se 2 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 464305 = 348229) B348229
theorem B366065 : Blo 159796 366065 := bstep (se 2 (by rfl) ⟨137274, by rfl⟩ : syracuseStep 366065 = 274549) B274549
theorem B235009 : Blo 159796 235009 := bstep (se 2 (by rfl) ⟨88128, by rfl⟩ : syracuseStep 235009 = 176257) B176257
theorem B366083 : Blo 159796 366083 := bstep (se 1 (by rfl) ⟨274562, by rfl⟩ : syracuseStep 366083 = 549125) B549125
theorem B235171 : Blo 159796 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B464579 : Blo 159796 464579 := bstep (se 1 (by rfl) ⟨348434, by rfl⟩ : syracuseStep 464579 = 696869) B696869
theorem B1119971 : Blo 159796 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B694001 : Blo 159796 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B366353 : Blo 159796 366353 := bstep (se 2 (by rfl) ⟨137382, by rfl⟩ : syracuseStep 366353 = 274765) B274765
theorem B366371 : Blo 159796 366371 := bstep (se 1 (by rfl) ⟨274778, by rfl⟩ : syracuseStep 366371 = 549557) B549557
theorem B366641 : Blo 159796 366641 := bstep (se 2 (by rfl) ⟨137490, by rfl⟩ : syracuseStep 366641 = 274981) B274981
theorem B202819 : Blo 159796 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B366659 : Blo 159796 366659 := bstep (se 1 (by rfl) ⟨274994, by rfl⟩ : syracuseStep 366659 = 549989) B549989
theorem B202915 : Blo 159796 202915 := bstep (se 1 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 202915 = 304373) B304373
theorem B923825 : Blo 159796 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B661709 : Blo 159796 661709 := bstep (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) B248141
theorem B366929 : Blo 159796 366929 := bstep (se 2 (by rfl) ⟨137598, by rfl⟩ : syracuseStep 366929 = 275197) B275197
theorem B366947 : Blo 159796 366947 := bstep (se 1 (by rfl) ⟨275210, by rfl⟩ : syracuseStep 366947 = 550421) B550421
theorem B825713 : Blo 159796 825713 := bstep (se 2 (by rfl) ⟨309642, by rfl⟩ : syracuseStep 825713 = 619285) B619285
theorem B1645069 : Blo 159796 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B465421 : Blo 159796 465421 := bstep (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) B174533
theorem B367217 : Blo 159796 367217 := bstep (se 2 (by rfl) ⟨137706, by rfl⟩ : syracuseStep 367217 = 275413) B275413
theorem B367235 : Blo 159796 367235 := bstep (se 1 (by rfl) ⟨275426, by rfl⟩ : syracuseStep 367235 = 550853) B550853
theorem B367249 : Blo 159796 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B203411 : Blo 159796 203411 := bstep (se 1 (by rfl) ⟨152558, by rfl⟩ : syracuseStep 203411 = 305117) B305117
theorem B465581 : Blo 159796 465581 := bstep (se 3 (by rfl) ⟨87296, by rfl⟩ : syracuseStep 465581 = 174593) B174593
theorem B465763 : Blo 159796 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B367505 : Blo 159796 367505 := bstep (se 2 (by rfl) ⟨137814, by rfl⟩ : syracuseStep 367505 = 275629) B275629
theorem B367523 : Blo 159796 367523 := bstep (se 1 (by rfl) ⟨275642, by rfl⟩ : syracuseStep 367523 = 551285) B551285
theorem B269443 : Blo 159796 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B367793 : Blo 159796 367793 := bstep (se 2 (by rfl) ⟨137922, by rfl⟩ : syracuseStep 367793 = 275845) B275845
theorem B367811 : Blo 159796 367811 := bstep (se 1 (by rfl) ⟨275858, by rfl⟩ : syracuseStep 367811 = 551717) B551717
theorem B695587 : Blo 159796 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B204115 : Blo 159796 204115 := bstep (se 1 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 204115 = 306173) B306173
theorem B204211 : Blo 159796 204211 := bstep (se 1 (by rfl) ⟨153158, by rfl⟩ : syracuseStep 204211 = 306317) B306317
theorem B433603 : Blo 159796 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B433613 : Blo 159796 433613 := bstep (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) B162605
theorem B269777 : Blo 159796 269777 := bstep (se 2 (by rfl) ⟨101166, by rfl⟩ : syracuseStep 269777 = 202333) B202333
theorem B368081 : Blo 159796 368081 := bstep (se 2 (by rfl) ⟨138030, by rfl⟩ : syracuseStep 368081 = 276061) B276061
theorem B368099 : Blo 159796 368099 := bstep (se 1 (by rfl) ⟨276074, by rfl⟩ : syracuseStep 368099 = 552149) B552149
theorem B269905 : Blo 159796 269905 := bstep (se 2 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 269905 = 202429) B202429
theorem B433745 : Blo 159796 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B925283 : Blo 159796 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B269939 : Blo 159796 269939 := bstep (se 1 (by rfl) ⟨202454, by rfl⟩ : syracuseStep 269939 = 404909) B404909
theorem B171731 : Blo 159796 171731 := bstep (se 1 (by rfl) ⟨128798, by rfl⟩ : syracuseStep 171731 = 257597) B257597
theorem B1187569 : Blo 159796 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B368369 : Blo 159796 368369 := bstep (se 2 (by rfl) ⟨138138, by rfl⟩ : syracuseStep 368369 = 276277) B276277
theorem B270067 : Blo 159796 270067 := bstep (se 1 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 270067 = 405101) B405101
theorem B368387 : Blo 159796 368387 := bstep (se 1 (by rfl) ⟨276290, by rfl⟩ : syracuseStep 368387 = 552581) B552581
theorem B499469 : Blo 159796 499469 := bstep (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) B187301
theorem B827171 : Blo 159796 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B270209 : Blo 159796 270209 := bstep (se 2 (by rfl) ⟨101328, by rfl⟩ : syracuseStep 270209 = 202657) B202657
theorem B204707 : Blo 159796 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B270337 : Blo 159796 270337 := bstep (se 2 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 270337 = 202753) B202753
theorem B270371 : Blo 159796 270371 := bstep (se 1 (by rfl) ⟨202778, by rfl⟩ : syracuseStep 270371 = 405557) B405557
theorem B270499 : Blo 159796 270499 := bstep (se 1 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 270499 = 405749) B405749
theorem B270641 : Blo 159796 270641 := bstep (se 2 (by rfl) ⟨101490, by rfl⟩ : syracuseStep 270641 = 202981) B202981
theorem B270769 : Blo 159796 270769 := bstep (se 2 (by rfl) ⟨101538, by rfl⟩ : syracuseStep 270769 = 203077) B203077
theorem B434641 : Blo 159796 434641 := bstep (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) B325981
theorem B270803 : Blo 159796 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B827981 : Blo 159796 827981 := bstep (se 3 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 827981 = 310493) B310493
theorem B270931 : Blo 159796 270931 := bstep (se 1 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 270931 = 406397) B406397
theorem B205411 : Blo 159796 205411 := bstep (se 1 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 205411 = 308117) B308117
theorem B172739 : Blo 159796 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B205507 : Blo 159796 205507 := bstep (se 1 (by rfl) ⟨154130, by rfl⟩ : syracuseStep 205507 = 308261) B308261
theorem B1221317 : Blo 159796 1221317 := bstep (se 4 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 1221317 = 228997) B228997
theorem B271073 : Blo 159796 271073 := bstep (se 2 (by rfl) ⟨101652, by rfl⟩ : syracuseStep 271073 = 203305) B203305
theorem B271201 : Blo 159796 271201 := bstep (se 2 (by rfl) ⟨101700, by rfl⟩ : syracuseStep 271201 = 203401) B203401
theorem B271235 : Blo 159796 271235 := bstep (se 1 (by rfl) ⟨203426, by rfl⟩ : syracuseStep 271235 = 406853) B406853
theorem B271363 : Blo 159796 271363 := bstep (se 1 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 271363 = 407045) B407045
theorem B304145 : Blo 159796 304145 := bstep (se 2 (by rfl) ⟨114054, by rfl⟩ : syracuseStep 304145 = 228109) B228109
theorem B271505 : Blo 159796 271505 := bstep (se 2 (by rfl) ⟨101814, by rfl⟩ : syracuseStep 271505 = 203629) B203629
theorem B206003 : Blo 159796 206003 := bstep (se 1 (by rfl) ⟨154502, by rfl⟩ : syracuseStep 206003 = 309005) B309005
theorem B697585 : Blo 159796 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B271633 : Blo 159796 271633 := bstep (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) B203725
theorem B271667 : Blo 159796 271667 := bstep (se 1 (by rfl) ⟨203750, by rfl⟩ : syracuseStep 271667 = 407501) B407501
theorem B1123661 : Blo 159796 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B271795 : Blo 159796 271795 := bstep (se 1 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 271795 = 407693) B407693
theorem B271937 : Blo 159796 271937 := bstep (se 2 (by rfl) ⟨101976, by rfl⟩ : syracuseStep 271937 = 203953) B203953
theorem B4368013 : Blo 159796 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B272065 : Blo 159796 272065 := bstep (se 2 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 272065 = 204049) B204049
theorem B272099 : Blo 159796 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B1124081 : Blo 159796 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B272227 : Blo 159796 272227 := bstep (se 1 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 272227 = 408341) B408341
theorem B206707 : Blo 159796 206707 := bstep (se 1 (by rfl) ⟨155030, by rfl⟩ : syracuseStep 206707 = 310061) B310061
theorem B305041 : Blo 159796 305041 := bstep (se 2 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 305041 = 228781) B228781
theorem B206803 : Blo 159796 206803 := bstep (se 1 (by rfl) ⟨155102, by rfl⟩ : syracuseStep 206803 = 310205) B310205
theorem B272369 : Blo 159796 272369 := bstep (se 2 (by rfl) ⟨102138, by rfl⟩ : syracuseStep 272369 = 204277) B204277
theorem B305201 : Blo 159796 305201 := bstep (se 2 (by rfl) ⟨114450, by rfl⟩ : syracuseStep 305201 = 228901) B228901
theorem B239699 : Blo 159796 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B239729 : Blo 159796 239729 := bstep (se 2 (by rfl) ⟨89898, by rfl⟩ : syracuseStep 239729 = 179797) B179797
theorem B272497 : Blo 159796 272497 := bstep (se 2 (by rfl) ⟨102186, by rfl⟩ : syracuseStep 272497 = 204373) B204373
theorem B239747 : Blo 159796 239747 := bstep (se 1 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 239747 = 359621) B359621
theorem B272531 : Blo 159796 272531 := bstep (se 1 (by rfl) ⟨204398, by rfl⟩ : syracuseStep 272531 = 408797) B408797
theorem B239777 : Blo 159796 239777 := bstep (se 2 (by rfl) ⟨89916, by rfl⟩ : syracuseStep 239777 = 179833) B179833
theorem B469165 : Blo 159796 469165 := bstep (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) B175937
theorem B239795 : Blo 159796 239795 := bstep (se 1 (by rfl) ⟨179846, by rfl⟩ : syracuseStep 239795 = 359693) B359693
theorem B2009285 : Blo 159796 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B239825 : Blo 159796 239825 := bstep (se 2 (by rfl) ⟨89934, by rfl⟩ : syracuseStep 239825 = 179869) B179869
theorem B239843 : Blo 159796 239843 := bstep (se 1 (by rfl) ⟨179882, by rfl⟩ : syracuseStep 239843 = 359765) B359765
theorem B174307 : Blo 159796 174307 := bstep (se 1 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 174307 = 261461) B261461
theorem B1976561 : Blo 159796 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B239873 : Blo 159796 239873 := bstep (se 2 (by rfl) ⟨89952, by rfl⟩ : syracuseStep 239873 = 179905) B179905
theorem B1059077 : Blo 159796 1059077 := bstep (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) B198577
theorem B239891 : Blo 159796 239891 := bstep (se 1 (by rfl) ⟨179918, by rfl⟩ : syracuseStep 239891 = 359837) B359837
theorem B272659 : Blo 159796 272659 := bstep (se 1 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 272659 = 408989) B408989
theorem B239921 : Blo 159796 239921 := bstep (se 2 (by rfl) ⟨89970, by rfl⟩ : syracuseStep 239921 = 179941) B179941
theorem B239939 : Blo 159796 239939 := bstep (se 1 (by rfl) ⟨179954, by rfl⟩ : syracuseStep 239939 = 359909) B359909
theorem B239969 : Blo 159796 239969 := bstep (se 2 (by rfl) ⟨89988, by rfl⟩ : syracuseStep 239969 = 179977) B179977
theorem B239987 : Blo 159796 239987 := bstep (se 1 (by rfl) ⟨179990, by rfl⟩ : syracuseStep 239987 = 359981) B359981
theorem B240017 : Blo 159796 240017 := bstep (se 2 (by rfl) ⟨90006, by rfl⟩ : syracuseStep 240017 = 180013) B180013
theorem B272801 : Blo 159796 272801 := bstep (se 2 (by rfl) ⟨102300, by rfl⟩ : syracuseStep 272801 = 204601) B204601
theorem B240035 : Blo 159796 240035 := bstep (se 1 (by rfl) ⟨180026, by rfl⟩ : syracuseStep 240035 = 360053) B360053
theorem B240065 : Blo 159796 240065 := bstep (se 2 (by rfl) ⟨90024, by rfl⟩ : syracuseStep 240065 = 180049) B180049
theorem B305603 : Blo 159796 305603 := bstep (se 1 (by rfl) ⟨229202, by rfl⟩ : syracuseStep 305603 = 458405) B458405
theorem B207299 : Blo 159796 207299 := bstep (se 1 (by rfl) ⟨155474, by rfl⟩ : syracuseStep 207299 = 310949) B310949
theorem B240083 : Blo 159796 240083 := bstep (se 1 (by rfl) ⟨180062, by rfl⟩ : syracuseStep 240083 = 360125) B360125
theorem B240113 : Blo 159796 240113 := bstep (se 2 (by rfl) ⟨90042, by rfl⟩ : syracuseStep 240113 = 180085) B180085
theorem B240131 : Blo 159796 240131 := bstep (se 1 (by rfl) ⟨180098, by rfl⟩ : syracuseStep 240131 = 360197) B360197
theorem B240161 : Blo 159796 240161 := bstep (se 2 (by rfl) ⟨90060, by rfl⟩ : syracuseStep 240161 = 180121) B180121
theorem B272929 : Blo 159796 272929 := bstep (se 2 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 272929 = 204697) B204697
theorem B240179 : Blo 159796 240179 := bstep (se 1 (by rfl) ⟨180134, by rfl⟩ : syracuseStep 240179 = 360269) B360269
theorem B272963 : Blo 159796 272963 := bstep (se 1 (by rfl) ⟨204722, by rfl⟩ : syracuseStep 272963 = 409445) B409445
theorem B240209 : Blo 159796 240209 := bstep (se 2 (by rfl) ⟨90078, by rfl⟩ : syracuseStep 240209 = 180157) B180157
theorem B240227 : Blo 159796 240227 := bstep (se 1 (by rfl) ⟨180170, by rfl⟩ : syracuseStep 240227 = 360341) B360341
theorem B240257 : Blo 159796 240257 := bstep (se 2 (by rfl) ⟨90096, by rfl⟩ : syracuseStep 240257 = 180193) B180193
theorem B240275 : Blo 159796 240275 := bstep (se 1 (by rfl) ⟨180206, by rfl⟩ : syracuseStep 240275 = 360413) B360413
theorem B174755 : Blo 159796 174755 := bstep (se 1 (by rfl) ⟨131066, by rfl⟩ : syracuseStep 174755 = 262133) B262133
theorem B240305 : Blo 159796 240305 := bstep (se 2 (by rfl) ⟨90114, by rfl⟩ : syracuseStep 240305 = 180229) B180229
theorem B240323 : Blo 159796 240323 := bstep (se 1 (by rfl) ⟨180242, by rfl⟩ : syracuseStep 240323 = 360485) B360485
theorem B273091 : Blo 159796 273091 := bstep (se 1 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 273091 = 409637) B409637
theorem B240353 : Blo 159796 240353 := bstep (se 2 (by rfl) ⟨90132, by rfl⟩ : syracuseStep 240353 = 180265) B180265
theorem B240371 : Blo 159796 240371 := bstep (se 1 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 240371 = 360557) B360557
theorem B240401 : Blo 159796 240401 := bstep (se 2 (by rfl) ⟨90150, by rfl⟩ : syracuseStep 240401 = 180301) B180301
theorem B240419 : Blo 159796 240419 := bstep (se 1 (by rfl) ⟨180314, by rfl⟩ : syracuseStep 240419 = 360629) B360629
theorem B240449 : Blo 159796 240449 := bstep (se 2 (by rfl) ⟨90168, by rfl⟩ : syracuseStep 240449 = 180337) B180337
theorem B994117 : Blo 159796 994117 := bstep (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) B186397
theorem B273233 : Blo 159796 273233 := bstep (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) B204925
theorem B240467 : Blo 159796 240467 := bstep (se 1 (by rfl) ⟨180350, by rfl⟩ : syracuseStep 240467 = 360701) B360701
theorem B240497 : Blo 159796 240497 := bstep (se 2 (by rfl) ⟨90186, by rfl⟩ : syracuseStep 240497 = 180373) B180373
theorem B240515 : Blo 159796 240515 := bstep (se 1 (by rfl) ⟨180386, by rfl⟩ : syracuseStep 240515 = 360773) B360773
theorem B240545 : Blo 159796 240545 := bstep (se 2 (by rfl) ⟨90204, by rfl⟩ : syracuseStep 240545 = 180409) B180409
theorem B699313 : Blo 159796 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B240563 : Blo 159796 240563 := bstep (se 1 (by rfl) ⟨180422, by rfl⟩ : syracuseStep 240563 = 360845) B360845
theorem B240593 : Blo 159796 240593 := bstep (se 2 (by rfl) ⟨90222, by rfl⟩ : syracuseStep 240593 = 180445) B180445
theorem B273361 : Blo 159796 273361 := bstep (se 2 (by rfl) ⟨102510, by rfl⟩ : syracuseStep 273361 = 205021) B205021
theorem B240611 : Blo 159796 240611 := bstep (se 1 (by rfl) ⟨180458, by rfl⟩ : syracuseStep 240611 = 360917) B360917
theorem B273395 : Blo 159796 273395 := bstep (se 1 (by rfl) ⟨205046, by rfl⟩ : syracuseStep 273395 = 410093) B410093
theorem B240641 : Blo 159796 240641 := bstep (se 2 (by rfl) ⟨90240, by rfl⟩ : syracuseStep 240641 = 180481) B180481
theorem B240659 : Blo 159796 240659 := bstep (se 1 (by rfl) ⟨180494, by rfl⟩ : syracuseStep 240659 = 360989) B360989
theorem B240689 : Blo 159796 240689 := bstep (se 2 (by rfl) ⟨90258, by rfl⟩ : syracuseStep 240689 = 180517) B180517
theorem B240707 : Blo 159796 240707 := bstep (se 1 (by rfl) ⟨180530, by rfl⟩ : syracuseStep 240707 = 361061) B361061
theorem B240737 : Blo 159796 240737 := bstep (se 2 (by rfl) ⟨90276, by rfl⟩ : syracuseStep 240737 = 180553) B180553
theorem B240755 : Blo 159796 240755 := bstep (se 1 (by rfl) ⟨180566, by rfl⟩ : syracuseStep 240755 = 361133) B361133
theorem B273523 : Blo 159796 273523 := bstep (se 1 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 273523 = 410285) B410285
theorem B240785 : Blo 159796 240785 := bstep (se 2 (by rfl) ⟨90294, by rfl⟩ : syracuseStep 240785 = 180589) B180589
theorem B240803 : Blo 159796 240803 := bstep (se 1 (by rfl) ⟨180602, by rfl⟩ : syracuseStep 240803 = 361205) B361205
theorem B240833 : Blo 159796 240833 := bstep (se 2 (by rfl) ⟨90312, by rfl⟩ : syracuseStep 240833 = 180625) B180625
theorem B240851 : Blo 159796 240851 := bstep (se 1 (by rfl) ⟨180638, by rfl⟩ : syracuseStep 240851 = 361277) B361277
theorem B240881 : Blo 159796 240881 := bstep (se 2 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 240881 = 180661) B180661
theorem B273665 : Blo 159796 273665 := bstep (se 2 (by rfl) ⟨102624, by rfl⟩ : syracuseStep 273665 = 205249) B205249
theorem B240899 : Blo 159796 240899 := bstep (se 1 (by rfl) ⟨180674, by rfl⟩ : syracuseStep 240899 = 361349) B361349
theorem B437507 : Blo 159796 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B240929 : Blo 159796 240929 := bstep (se 2 (by rfl) ⟨90348, by rfl⟩ : syracuseStep 240929 = 180697) B180697
theorem B240947 : Blo 159796 240947 := bstep (se 1 (by rfl) ⟨180710, by rfl⟩ : syracuseStep 240947 = 361421) B361421
theorem B306499 : Blo 159796 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B240977 : Blo 159796 240977 := bstep (se 2 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 240977 = 180733) B180733
theorem B240995 : Blo 159796 240995 := bstep (se 1 (by rfl) ⟨180746, by rfl⟩ : syracuseStep 240995 = 361493) B361493
theorem B241025 : Blo 159796 241025 := bstep (se 2 (by rfl) ⟨90384, by rfl⟩ : syracuseStep 241025 = 180769) B180769
theorem B273793 : Blo 159796 273793 := bstep (se 2 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 273793 = 205345) B205345
theorem B241043 : Blo 159796 241043 := bstep (se 1 (by rfl) ⟨180782, by rfl⟩ : syracuseStep 241043 = 361565) B361565
theorem B273827 : Blo 159796 273827 := bstep (se 1 (by rfl) ⟨205370, by rfl⟩ : syracuseStep 273827 = 410741) B410741
theorem B241073 : Blo 159796 241073 := bstep (se 2 (by rfl) ⟨90402, by rfl⟩ : syracuseStep 241073 = 180805) B180805
theorem B241091 : Blo 159796 241091 := bstep (se 1 (by rfl) ⟨180818, by rfl⟩ : syracuseStep 241091 = 361637) B361637
theorem B241121 : Blo 159796 241121 := bstep (se 2 (by rfl) ⟨90420, by rfl⟩ : syracuseStep 241121 = 180841) B180841
theorem B306659 : Blo 159796 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B994801 : Blo 159796 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B241139 : Blo 159796 241139 := bstep (se 1 (by rfl) ⟨180854, by rfl⟩ : syracuseStep 241139 = 361709) B361709
theorem B241169 : Blo 159796 241169 := bstep (se 2 (by rfl) ⟨90438, by rfl⟩ : syracuseStep 241169 = 180877) B180877
theorem B241187 : Blo 159796 241187 := bstep (se 1 (by rfl) ⟨180890, by rfl⟩ : syracuseStep 241187 = 361781) B361781
theorem B273955 : Blo 159796 273955 := bstep (se 1 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 273955 = 410933) B410933
theorem B241217 : Blo 159796 241217 := bstep (se 2 (by rfl) ⟨90456, by rfl⟩ : syracuseStep 241217 = 180913) B180913
theorem B241235 : Blo 159796 241235 := bstep (se 1 (by rfl) ⟨180926, by rfl⟩ : syracuseStep 241235 = 361853) B361853
theorem B241265 : Blo 159796 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B241283 : Blo 159796 241283 := bstep (se 1 (by rfl) ⟨180962, by rfl⟩ : syracuseStep 241283 = 361925) B361925
theorem B241313 : Blo 159796 241313 := bstep (se 2 (by rfl) ⟨90492, by rfl⟩ : syracuseStep 241313 = 180985) B180985
theorem B274097 : Blo 159796 274097 := bstep (se 2 (by rfl) ⟨102786, by rfl⟩ : syracuseStep 274097 = 205573) B205573
theorem B241331 : Blo 159796 241331 := bstep (se 1 (by rfl) ⟨180998, by rfl⟩ : syracuseStep 241331 = 361997) B361997
theorem B241361 : Blo 159796 241361 := bstep (se 2 (by rfl) ⟨90510, by rfl⟩ : syracuseStep 241361 = 181021) B181021
theorem B241379 : Blo 159796 241379 := bstep (se 1 (by rfl) ⟨181034, by rfl⟩ : syracuseStep 241379 = 362069) B362069
theorem B405233 : Blo 159796 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B241409 : Blo 159796 241409 := bstep (se 2 (by rfl) ⟨90528, by rfl⟩ : syracuseStep 241409 = 181057) B181057
theorem B241427 : Blo 159796 241427 := bstep (se 1 (by rfl) ⟨181070, by rfl⟩ : syracuseStep 241427 = 362141) B362141
theorem B405283 : Blo 159796 405283 := bstep (se 1 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 405283 = 607925) B607925
theorem B241457 : Blo 159796 241457 := bstep (se 2 (by rfl) ⟨90546, by rfl⟩ : syracuseStep 241457 = 181093) B181093
theorem B274225 : Blo 159796 274225 := bstep (se 2 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 274225 = 205669) B205669
theorem B241475 : Blo 159796 241475 := bstep (se 1 (by rfl) ⟨181106, by rfl⟩ : syracuseStep 241475 = 362213) B362213
theorem B274259 : Blo 159796 274259 := bstep (se 1 (by rfl) ⟨205694, by rfl⟩ : syracuseStep 274259 = 411389) B411389
theorem B241505 : Blo 159796 241505 := bstep (se 2 (by rfl) ⟨90564, by rfl⟩ : syracuseStep 241505 = 181129) B181129
theorem B241523 : Blo 159796 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B241553 : Blo 159796 241553 := bstep (se 2 (by rfl) ⟨90582, by rfl⟩ : syracuseStep 241553 = 181165) B181165
theorem B241571 : Blo 159796 241571 := bstep (se 1 (by rfl) ⟨181178, by rfl⟩ : syracuseStep 241571 = 362357) B362357
theorem B405425 : Blo 159796 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B241601 : Blo 159796 241601 := bstep (se 2 (by rfl) ⟨90600, by rfl⟩ : syracuseStep 241601 = 181201) B181201
theorem B241619 : Blo 159796 241619 := bstep (se 1 (by rfl) ⟨181214, by rfl⟩ : syracuseStep 241619 = 362429) B362429
theorem B274387 : Blo 159796 274387 := bstep (se 1 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 274387 = 411581) B411581
theorem B176099 : Blo 159796 176099 := bstep (se 1 (by rfl) ⟨132074, by rfl⟩ : syracuseStep 176099 = 264149) B264149
theorem B241649 : Blo 159796 241649 := bstep (se 2 (by rfl) ⟨90618, by rfl⟩ : syracuseStep 241649 = 181237) B181237
theorem B241667 : Blo 159796 241667 := bstep (se 1 (by rfl) ⟨181250, by rfl⟩ : syracuseStep 241667 = 362501) B362501
theorem B241697 : Blo 159796 241697 := bstep (se 2 (by rfl) ⟨90636, by rfl⟩ : syracuseStep 241697 = 181273) B181273
theorem B241715 : Blo 159796 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B241745 : Blo 159796 241745 := bstep (se 2 (by rfl) ⟨90654, by rfl⟩ : syracuseStep 241745 = 181309) B181309
theorem B274529 : Blo 159796 274529 := bstep (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) B205897
theorem B241763 : Blo 159796 241763 := bstep (se 1 (by rfl) ⟨181322, by rfl⟩ : syracuseStep 241763 = 362645) B362645
theorem B241793 : Blo 159796 241793 := bstep (se 2 (by rfl) ⟨90672, by rfl⟩ : syracuseStep 241793 = 181345) B181345
theorem B241811 : Blo 159796 241811 := bstep (se 1 (by rfl) ⟨181358, by rfl⟩ : syracuseStep 241811 = 362717) B362717
theorem B241841 : Blo 159796 241841 := bstep (se 2 (by rfl) ⟨90690, by rfl⟩ : syracuseStep 241841 = 181381) B181381
theorem B241859 : Blo 159796 241859 := bstep (se 1 (by rfl) ⟨181394, by rfl⟩ : syracuseStep 241859 = 362789) B362789
theorem B241889 : Blo 159796 241889 := bstep (se 2 (by rfl) ⟨90708, by rfl⟩ : syracuseStep 241889 = 181417) B181417
theorem B274657 : Blo 159796 274657 := bstep (se 2 (by rfl) ⟨102996, by rfl⟩ : syracuseStep 274657 = 205993) B205993
theorem B241907 : Blo 159796 241907 := bstep (se 1 (by rfl) ⟨181430, by rfl⟩ : syracuseStep 241907 = 362861) B362861
theorem B274691 : Blo 159796 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B241937 : Blo 159796 241937 := bstep (se 2 (by rfl) ⟨90726, by rfl⟩ : syracuseStep 241937 = 181453) B181453
theorem B733475 : Blo 159796 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B241955 : Blo 159796 241955 := bstep (se 1 (by rfl) ⟨181466, by rfl⟩ : syracuseStep 241955 = 362933) B362933
theorem B241985 : Blo 159796 241985 := bstep (se 2 (by rfl) ⟨90744, by rfl⟩ : syracuseStep 241985 = 181489) B181489
theorem B242003 : Blo 159796 242003 := bstep (se 1 (by rfl) ⟨181502, by rfl⟩ : syracuseStep 242003 = 363005) B363005
theorem B242033 : Blo 159796 242033 := bstep (se 2 (by rfl) ⟨90762, by rfl⟩ : syracuseStep 242033 = 181525) B181525
theorem B242051 : Blo 159796 242051 := bstep (se 1 (by rfl) ⟨181538, by rfl⟩ : syracuseStep 242051 = 363077) B363077
theorem B274819 : Blo 159796 274819 := bstep (se 1 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 274819 = 412229) B412229
theorem B242081 : Blo 159796 242081 := bstep (se 2 (by rfl) ⟨90780, by rfl⟩ : syracuseStep 242081 = 181561) B181561
theorem B242099 : Blo 159796 242099 := bstep (se 1 (by rfl) ⟨181574, by rfl⟩ : syracuseStep 242099 = 363149) B363149
theorem B242129 : Blo 159796 242129 := bstep (se 2 (by rfl) ⟨90798, by rfl⟩ : syracuseStep 242129 = 181597) B181597
theorem B242147 : Blo 159796 242147 := bstep (se 1 (by rfl) ⟨181610, by rfl⟩ : syracuseStep 242147 = 363221) B363221
theorem B242177 : Blo 159796 242177 := bstep (se 2 (by rfl) ⟨90816, by rfl⟩ : syracuseStep 242177 = 181633) B181633
theorem B307729 : Blo 159796 307729 := bstep (se 2 (by rfl) ⟨115398, by rfl⟩ : syracuseStep 307729 = 230797) B230797
theorem B274961 : Blo 159796 274961 := bstep (se 2 (by rfl) ⟨103110, by rfl⟩ : syracuseStep 274961 = 206221) B206221
theorem B242195 : Blo 159796 242195 := bstep (se 1 (by rfl) ⟨181646, by rfl⟩ : syracuseStep 242195 = 363293) B363293
theorem B242225 : Blo 159796 242225 := bstep (se 2 (by rfl) ⟨90834, by rfl⟩ : syracuseStep 242225 = 181669) B181669
theorem B242243 : Blo 159796 242243 := bstep (se 1 (by rfl) ⟨181682, by rfl⟩ : syracuseStep 242243 = 363365) B363365
theorem B242273 : Blo 159796 242273 := bstep (se 2 (by rfl) ⟨90852, by rfl⟩ : syracuseStep 242273 = 181705) B181705
theorem B242291 : Blo 159796 242291 := bstep (se 1 (by rfl) ⟨181718, by rfl⟩ : syracuseStep 242291 = 363437) B363437
theorem B242321 : Blo 159796 242321 := bstep (se 2 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 242321 = 181741) B181741
theorem B275089 : Blo 159796 275089 := bstep (se 2 (by rfl) ⟨103158, by rfl⟩ : syracuseStep 275089 = 206317) B206317
theorem B242339 : Blo 159796 242339 := bstep (se 1 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 242339 = 363509) B363509
theorem B275123 : Blo 159796 275123 := bstep (se 1 (by rfl) ⟨206342, by rfl⟩ : syracuseStep 275123 = 412685) B412685
theorem B242369 : Blo 159796 242369 := bstep (se 2 (by rfl) ⟨90888, by rfl⟩ : syracuseStep 242369 = 181777) B181777
theorem B242387 : Blo 159796 242387 := bstep (se 1 (by rfl) ⟨181790, by rfl⟩ : syracuseStep 242387 = 363581) B363581
theorem B242417 : Blo 159796 242417 := bstep (se 2 (by rfl) ⟨90906, by rfl⟩ : syracuseStep 242417 = 181813) B181813
theorem B242435 : Blo 159796 242435 := bstep (se 1 (by rfl) ⟨181826, by rfl⟩ : syracuseStep 242435 = 363653) B363653
theorem B242465 : Blo 159796 242465 := bstep (se 2 (by rfl) ⟨90924, by rfl⟩ : syracuseStep 242465 = 181849) B181849
theorem B242483 : Blo 159796 242483 := bstep (se 1 (by rfl) ⟨181862, by rfl⟩ : syracuseStep 242483 = 363725) B363725
theorem B275251 : Blo 159796 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B242513 : Blo 159796 242513 := bstep (se 2 (by rfl) ⟨90942, by rfl⟩ : syracuseStep 242513 = 181885) B181885
theorem B242531 : Blo 159796 242531 := bstep (se 1 (by rfl) ⟨181898, by rfl⟩ : syracuseStep 242531 = 363797) B363797
theorem B439139 : Blo 159796 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B242561 : Blo 159796 242561 := bstep (se 2 (by rfl) ⟨90960, by rfl⟩ : syracuseStep 242561 = 181921) B181921
theorem B406417 : Blo 159796 406417 := bstep (se 2 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 406417 = 304813) B304813
theorem B242579 : Blo 159796 242579 := bstep (se 1 (by rfl) ⟨181934, by rfl⟩ : syracuseStep 242579 = 363869) B363869
theorem B242609 : Blo 159796 242609 := bstep (se 2 (by rfl) ⟨90978, by rfl⟩ : syracuseStep 242609 = 181957) B181957
theorem B275393 : Blo 159796 275393 := bstep (se 2 (by rfl) ⟨103272, by rfl⟩ : syracuseStep 275393 = 206545) B206545
theorem B242627 : Blo 159796 242627 := bstep (se 1 (by rfl) ⟨181970, by rfl⟩ : syracuseStep 242627 = 363941) B363941
theorem B242657 : Blo 159796 242657 := bstep (se 2 (by rfl) ⟨90996, by rfl⟩ : syracuseStep 242657 = 181993) B181993
theorem B242675 : Blo 159796 242675 := bstep (se 1 (by rfl) ⟨182006, by rfl⟩ : syracuseStep 242675 = 364013) B364013
theorem B242705 : Blo 159796 242705 := bstep (se 2 (by rfl) ⟨91014, by rfl⟩ : syracuseStep 242705 = 182029) B182029
theorem B242723 : Blo 159796 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B832547 : Blo 159796 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B242753 : Blo 159796 242753 := bstep (se 2 (by rfl) ⟨91032, by rfl⟩ : syracuseStep 242753 = 182065) B182065
theorem B275521 : Blo 159796 275521 := bstep (se 2 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 275521 = 206641) B206641
theorem B242771 : Blo 159796 242771 := bstep (se 1 (by rfl) ⟨182078, by rfl⟩ : syracuseStep 242771 = 364157) B364157
theorem B275555 : Blo 159796 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B242801 : Blo 159796 242801 := bstep (se 2 (by rfl) ⟨91050, by rfl⟩ : syracuseStep 242801 = 182101) B182101
theorem B242819 : Blo 159796 242819 := bstep (se 1 (by rfl) ⟨182114, by rfl⟩ : syracuseStep 242819 = 364229) B364229
theorem B242849 : Blo 159796 242849 := bstep (se 2 (by rfl) ⟨91068, by rfl⟩ : syracuseStep 242849 = 182137) B182137
theorem B406691 : Blo 159796 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B242867 : Blo 159796 242867 := bstep (se 1 (by rfl) ⟨182150, by rfl⟩ : syracuseStep 242867 = 364301) B364301
theorem B242897 : Blo 159796 242897 := bstep (se 2 (by rfl) ⟨91086, by rfl⟩ : syracuseStep 242897 = 182173) B182173
theorem B242915 : Blo 159796 242915 := bstep (se 1 (by rfl) ⟨182186, by rfl⟩ : syracuseStep 242915 = 364373) B364373
theorem B275683 : Blo 159796 275683 := bstep (se 1 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 275683 = 413525) B413525
theorem B3880163 : Blo 159796 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B10073315 : Blo 159796 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B242945 : Blo 159796 242945 := bstep (se 2 (by rfl) ⟨91104, by rfl⟩ : syracuseStep 242945 = 182209) B182209
theorem B242963 : Blo 159796 242963 := bstep (se 1 (by rfl) ⟨182222, by rfl⟩ : syracuseStep 242963 = 364445) B364445
theorem B242993 : Blo 159796 242993 := bstep (se 2 (by rfl) ⟨91122, by rfl⟩ : syracuseStep 242993 = 182245) B182245
theorem B243011 : Blo 159796 243011 := bstep (se 1 (by rfl) ⟨182258, by rfl⟩ : syracuseStep 243011 = 364517) B364517
theorem B243041 : Blo 159796 243041 := bstep (se 2 (by rfl) ⟨91140, by rfl⟩ : syracuseStep 243041 = 182281) B182281
theorem B406883 : Blo 159796 406883 := bstep (se 1 (by rfl) ⟨305162, by rfl⟩ : syracuseStep 406883 = 610325) B610325
theorem B275825 : Blo 159796 275825 := bstep (se 2 (by rfl) ⟨103434, by rfl⟩ : syracuseStep 275825 = 206869) B206869
theorem B243059 : Blo 159796 243059 := bstep (se 1 (by rfl) ⟨182294, by rfl⟩ : syracuseStep 243059 = 364589) B364589
theorem B243089 : Blo 159796 243089 := bstep (se 2 (by rfl) ⟨91158, by rfl⟩ : syracuseStep 243089 = 182317) B182317
theorem B243107 : Blo 159796 243107 := bstep (se 1 (by rfl) ⟨182330, by rfl⟩ : syracuseStep 243107 = 364661) B364661
theorem B243137 : Blo 159796 243137 := bstep (se 2 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 243137 = 182353) B182353
theorem B243155 : Blo 159796 243155 := bstep (se 1 (by rfl) ⟨182366, by rfl⟩ : syracuseStep 243155 = 364733) B364733
theorem B243185 : Blo 159796 243185 := bstep (se 2 (by rfl) ⟨91194, by rfl⟩ : syracuseStep 243185 = 182389) B182389
theorem B275953 : Blo 159796 275953 := bstep (se 2 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 275953 = 206965) B206965
theorem B243203 : Blo 159796 243203 := bstep (se 1 (by rfl) ⟨182402, by rfl⟩ : syracuseStep 243203 = 364805) B364805
theorem B275987 : Blo 159796 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B243233 : Blo 159796 243233 := bstep (se 2 (by rfl) ⟨91212, by rfl⟩ : syracuseStep 243233 = 182425) B182425
theorem B1029667 : Blo 159796 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B308785 : Blo 159796 308785 := bstep (se 2 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 308785 = 231589) B231589
theorem B243251 : Blo 159796 243251 := bstep (se 1 (by rfl) ⟨182438, by rfl⟩ : syracuseStep 243251 = 364877) B364877
theorem B243281 : Blo 159796 243281 := bstep (se 2 (by rfl) ⟨91230, by rfl⟩ : syracuseStep 243281 = 182461) B182461
theorem B243299 : Blo 159796 243299 := bstep (se 1 (by rfl) ⟨182474, by rfl⟩ : syracuseStep 243299 = 364949) B364949
theorem B341617 : Blo 159796 341617 := bstep (se 2 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 341617 = 256213) B256213
theorem B243329 : Blo 159796 243329 := bstep (se 2 (by rfl) ⟨91248, by rfl⟩ : syracuseStep 243329 = 182497) B182497
theorem B243347 : Blo 159796 243347 := bstep (se 1 (by rfl) ⟨182510, by rfl⟩ : syracuseStep 243347 = 365021) B365021
theorem B276115 : Blo 159796 276115 := bstep (se 1 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 276115 = 414173) B414173
theorem B243377 : Blo 159796 243377 := bstep (se 2 (by rfl) ⟨91266, by rfl⟩ : syracuseStep 243377 = 182533) B182533
theorem B243395 : Blo 159796 243395 := bstep (se 1 (by rfl) ⟨182546, by rfl⟩ : syracuseStep 243395 = 365093) B365093
theorem B243425 : Blo 159796 243425 := bstep (se 2 (by rfl) ⟨91284, by rfl⟩ : syracuseStep 243425 = 182569) B182569
theorem B243443 : Blo 159796 243443 := bstep (se 1 (by rfl) ⟨182582, by rfl⟩ : syracuseStep 243443 = 365165) B365165
theorem B243473 : Blo 159796 243473 := bstep (se 2 (by rfl) ⟨91302, by rfl⟩ : syracuseStep 243473 = 182605) B182605
theorem B276257 : Blo 159796 276257 := bstep (se 2 (by rfl) ⟨103596, by rfl⟩ : syracuseStep 276257 = 207193) B207193
theorem B243491 : Blo 159796 243491 := bstep (se 1 (by rfl) ⟨182618, by rfl⟩ : syracuseStep 243491 = 365237) B365237
theorem B243521 : Blo 159796 243521 := bstep (se 2 (by rfl) ⟨91320, by rfl⟩ : syracuseStep 243521 = 182641) B182641
theorem B243539 : Blo 159796 243539 := bstep (se 1 (by rfl) ⟨182654, by rfl⟩ : syracuseStep 243539 = 365309) B365309
theorem B243569 : Blo 159796 243569 := bstep (se 2 (by rfl) ⟨91338, by rfl⟩ : syracuseStep 243569 = 182677) B182677
theorem B243587 : Blo 159796 243587 := bstep (se 1 (by rfl) ⟨182690, by rfl⟩ : syracuseStep 243587 = 365381) B365381
theorem B866189 : Blo 159796 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B243617 : Blo 159796 243617 := bstep (se 2 (by rfl) ⟨91356, by rfl⟩ : syracuseStep 243617 = 182713) B182713
theorem B276385 : Blo 159796 276385 := bstep (se 2 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 276385 = 207289) B207289
theorem B243635 : Blo 159796 243635 := bstep (se 1 (by rfl) ⟨182726, by rfl⟩ : syracuseStep 243635 = 365453) B365453
theorem B309187 : Blo 159796 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B243665 : Blo 159796 243665 := bstep (se 2 (by rfl) ⟨91374, by rfl⟩ : syracuseStep 243665 = 182749) B182749
theorem B243683 : Blo 159796 243683 := bstep (se 1 (by rfl) ⟨182762, by rfl⟩ : syracuseStep 243683 = 365525) B365525
theorem B309233 : Blo 159796 309233 := bstep (se 2 (by rfl) ⟨115962, by rfl⟩ : syracuseStep 309233 = 231925) B231925
theorem B243713 : Blo 159796 243713 := bstep (se 2 (by rfl) ⟨91392, by rfl⟩ : syracuseStep 243713 = 182785) B182785
theorem B243731 : Blo 159796 243731 := bstep (se 1 (by rfl) ⟨182798, by rfl⟩ : syracuseStep 243731 = 365597) B365597
theorem B243761 : Blo 159796 243761 := bstep (se 2 (by rfl) ⟨91410, by rfl⟩ : syracuseStep 243761 = 182821) B182821
theorem B243779 : Blo 159796 243779 := bstep (se 1 (by rfl) ⟨182834, by rfl⟩ : syracuseStep 243779 = 365669) B365669
theorem B243809 : Blo 159796 243809 := bstep (se 2 (by rfl) ⟨91428, by rfl⟩ : syracuseStep 243809 = 182857) B182857
theorem B243827 : Blo 159796 243827 := bstep (se 1 (by rfl) ⟨182870, by rfl⟩ : syracuseStep 243827 = 365741) B365741
theorem B243857 : Blo 159796 243857 := bstep (se 2 (by rfl) ⟨91446, by rfl⟩ : syracuseStep 243857 = 182893) B182893
theorem B243859 : Blo 159796 243859 := bstep (se 1 (by rfl) ⟨182894, by rfl⟩ : syracuseStep 243859 = 365789) B365789
theorem B243875 : Blo 159796 243875 := bstep (se 1 (by rfl) ⟨182906, by rfl⟩ : syracuseStep 243875 = 365813) B365813
theorem B243905 : Blo 159796 243905 := bstep (se 2 (by rfl) ⟨91464, by rfl⟩ : syracuseStep 243905 = 182929) B182929
theorem B243923 : Blo 159796 243923 := bstep (se 1 (by rfl) ⟨182942, by rfl⟩ : syracuseStep 243923 = 365885) B365885
theorem B243953 : Blo 159796 243953 := bstep (se 2 (by rfl) ⟨91482, by rfl⟩ : syracuseStep 243953 = 182965) B182965
theorem B243971 : Blo 159796 243971 := bstep (se 1 (by rfl) ⟨182978, by rfl⟩ : syracuseStep 243971 = 365957) B365957
theorem B407825 : Blo 159796 407825 := bstep (se 2 (by rfl) ⟨152934, by rfl⟩ : syracuseStep 407825 = 305869) B305869
theorem B309521 : Blo 159796 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B244001 : Blo 159796 244001 := bstep (se 2 (by rfl) ⟨91500, by rfl⟩ : syracuseStep 244001 = 183001) B183001
theorem B244019 : Blo 159796 244019 := bstep (se 1 (by rfl) ⟨183014, by rfl⟩ : syracuseStep 244019 = 366029) B366029
theorem B407875 : Blo 159796 407875 := bstep (se 1 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 407875 = 611813) B611813
theorem B244049 : Blo 159796 244049 := bstep (se 2 (by rfl) ⟨91518, by rfl⟩ : syracuseStep 244049 = 183037) B183037
theorem B244067 : Blo 159796 244067 := bstep (se 1 (by rfl) ⟨183050, by rfl⟩ : syracuseStep 244067 = 366101) B366101
theorem B244097 : Blo 159796 244097 := bstep (se 2 (by rfl) ⟨91536, by rfl⟩ : syracuseStep 244097 = 183073) B183073
theorem B1227149 : Blo 159796 1227149 := bstep (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) B460181
theorem B244115 : Blo 159796 244115 := bstep (se 1 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 244115 = 366173) B366173
theorem B440749 : Blo 159796 440749 := bstep (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) B165281
theorem B244145 : Blo 159796 244145 := bstep (se 2 (by rfl) ⟨91554, by rfl⟩ : syracuseStep 244145 = 183109) B183109
theorem B244163 : Blo 159796 244163 := bstep (se 1 (by rfl) ⟨183122, by rfl⟩ : syracuseStep 244163 = 366245) B366245
theorem B408017 : Blo 159796 408017 := bstep (se 2 (by rfl) ⟨153006, by rfl⟩ : syracuseStep 408017 = 306013) B306013
theorem B244193 : Blo 159796 244193 := bstep (se 2 (by rfl) ⟨91572, by rfl⟩ : syracuseStep 244193 = 183145) B183145
theorem B244211 : Blo 159796 244211 := bstep (se 1 (by rfl) ⟨183158, by rfl⟩ : syracuseStep 244211 = 366317) B366317
theorem B244241 : Blo 159796 244241 := bstep (se 2 (by rfl) ⟨91590, by rfl⟩ : syracuseStep 244241 = 183181) B183181
theorem B244259 : Blo 159796 244259 := bstep (se 1 (by rfl) ⟨183194, by rfl⟩ : syracuseStep 244259 = 366389) B366389
theorem B244289 : Blo 159796 244289 := bstep (se 2 (by rfl) ⟨91608, by rfl⟩ : syracuseStep 244289 = 183217) B183217
theorem B244307 : Blo 159796 244307 := bstep (se 1 (by rfl) ⟨183230, by rfl⟩ : syracuseStep 244307 = 366461) B366461
theorem B244337 : Blo 159796 244337 := bstep (se 2 (by rfl) ⟨91626, by rfl⟩ : syracuseStep 244337 = 183253) B183253
theorem B244355 : Blo 159796 244355 := bstep (se 1 (by rfl) ⟨183266, by rfl⟩ : syracuseStep 244355 = 366533) B366533
theorem B244385 : Blo 159796 244385 := bstep (se 2 (by rfl) ⟨91644, by rfl⟩ : syracuseStep 244385 = 183289) B183289
theorem B244403 : Blo 159796 244403 := bstep (se 1 (by rfl) ⟨183302, by rfl⟩ : syracuseStep 244403 = 366605) B366605
theorem B244433 : Blo 159796 244433 := bstep (se 2 (by rfl) ⟨91662, by rfl⟩ : syracuseStep 244433 = 183325) B183325
theorem B244451 : Blo 159796 244451 := bstep (se 1 (by rfl) ⟨183338, by rfl⟩ : syracuseStep 244451 = 366677) B366677
theorem B1030897 : Blo 159796 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B244481 : Blo 159796 244481 := bstep (se 2 (by rfl) ⟨91680, by rfl⟩ : syracuseStep 244481 = 183361) B183361
theorem B539405 : Blo 159796 539405 := bstep (se 3 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 539405 = 202277) B202277
theorem B244499 : Blo 159796 244499 := bstep (se 1 (by rfl) ⟨183374, by rfl⟩ : syracuseStep 244499 = 366749) B366749
theorem B244529 : Blo 159796 244529 := bstep (se 2 (by rfl) ⟨91698, by rfl⟩ : syracuseStep 244529 = 183397) B183397
theorem B539459 : Blo 159796 539459 := bstep (se 1 (by rfl) ⟨404594, by rfl⟩ : syracuseStep 539459 = 809189) B809189
theorem B244547 : Blo 159796 244547 := bstep (se 1 (by rfl) ⟨183410, by rfl⟩ : syracuseStep 244547 = 366821) B366821
theorem B244577 : Blo 159796 244577 := bstep (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) B183433
theorem B244595 : Blo 159796 244595 := bstep (se 1 (by rfl) ⟨183446, by rfl⟩ : syracuseStep 244595 = 366893) B366893
theorem B244625 : Blo 159796 244625 := bstep (se 2 (by rfl) ⟨91734, by rfl⟩ : syracuseStep 244625 = 183469) B183469
theorem B244643 : Blo 159796 244643 := bstep (se 1 (by rfl) ⟨183482, by rfl⟩ : syracuseStep 244643 = 366965) B366965
theorem B244673 : Blo 159796 244673 := bstep (se 2 (by rfl) ⟨91752, by rfl⟩ : syracuseStep 244673 = 183505) B183505
theorem B244691 : Blo 159796 244691 := bstep (se 1 (by rfl) ⟨183518, by rfl⟩ : syracuseStep 244691 = 367037) B367037
theorem B310243 : Blo 159796 310243 := bstep (se 1 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 310243 = 465365) B465365
theorem B244721 : Blo 159796 244721 := bstep (se 2 (by rfl) ⟨91770, by rfl⟩ : syracuseStep 244721 = 183541) B183541
theorem B244739 : Blo 159796 244739 := bstep (se 1 (by rfl) ⟨183554, by rfl⟩ : syracuseStep 244739 = 367109) B367109
theorem B244769 : Blo 159796 244769 := bstep (se 2 (by rfl) ⟨91788, by rfl⟩ : syracuseStep 244769 = 183577) B183577
theorem B244787 : Blo 159796 244787 := bstep (se 1 (by rfl) ⟨183590, by rfl⟩ : syracuseStep 244787 = 367181) B367181
theorem B539729 : Blo 159796 539729 := bstep (se 2 (by rfl) ⟨202398, by rfl⟩ : syracuseStep 539729 = 404797) B404797
theorem B244817 : Blo 159796 244817 := bstep (se 2 (by rfl) ⟨91806, by rfl⟩ : syracuseStep 244817 = 183613) B183613
theorem B244835 : Blo 159796 244835 := bstep (se 1 (by rfl) ⟨183626, by rfl⟩ : syracuseStep 244835 = 367253) B367253
theorem B244865 : Blo 159796 244865 := bstep (se 2 (by rfl) ⟨91824, by rfl⟩ : syracuseStep 244865 = 183649) B183649
theorem B244883 : Blo 159796 244883 := bstep (se 1 (by rfl) ⟨183662, by rfl⟩ : syracuseStep 244883 = 367325) B367325
theorem B244913 : Blo 159796 244913 := bstep (se 2 (by rfl) ⟨91842, by rfl⟩ : syracuseStep 244913 = 183685) B183685
theorem B244931 : Blo 159796 244931 := bstep (se 1 (by rfl) ⟨183698, by rfl⟩ : syracuseStep 244931 = 367397) B367397
theorem B244961 : Blo 159796 244961 := bstep (se 2 (by rfl) ⟨91860, by rfl⟩ : syracuseStep 244961 = 183721) B183721
theorem B244979 : Blo 159796 244979 := bstep (se 1 (by rfl) ⟨183734, by rfl⟩ : syracuseStep 244979 = 367469) B367469
theorem B245009 : Blo 159796 245009 := bstep (se 2 (by rfl) ⟨91878, by rfl⟩ : syracuseStep 245009 = 183757) B183757
theorem B245027 : Blo 159796 245027 := bstep (se 1 (by rfl) ⟨183770, by rfl⟩ : syracuseStep 245027 = 367541) B367541
theorem B245057 : Blo 159796 245057 := bstep (se 2 (by rfl) ⟨91896, by rfl⟩ : syracuseStep 245057 = 183793) B183793
theorem B245075 : Blo 159796 245075 := bstep (se 1 (by rfl) ⟨183806, by rfl⟩ : syracuseStep 245075 = 367613) B367613
theorem B245105 : Blo 159796 245105 := bstep (se 2 (by rfl) ⟨91914, by rfl⟩ : syracuseStep 245105 = 183829) B183829
theorem B245123 : Blo 159796 245123 := bstep (se 1 (by rfl) ⟨183842, by rfl⟩ : syracuseStep 245123 = 367685) B367685
theorem B245153 : Blo 159796 245153 := bstep (se 2 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 245153 = 183865) B183865
theorem B310691 : Blo 159796 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B409009 : Blo 159796 409009 := bstep (se 2 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 409009 = 306757) B306757
theorem B245171 : Blo 159796 245171 := bstep (se 1 (by rfl) ⟨183878, by rfl⟩ : syracuseStep 245171 = 367757) B367757
theorem B245201 : Blo 159796 245201 := bstep (se 2 (by rfl) ⟨91950, by rfl⟩ : syracuseStep 245201 = 183901) B183901
theorem B245219 : Blo 159796 245219 := bstep (se 1 (by rfl) ⟨183914, by rfl⟩ : syracuseStep 245219 = 367829) B367829
theorem B245249 : Blo 159796 245249 := bstep (se 2 (by rfl) ⟨91968, by rfl⟩ : syracuseStep 245249 = 183937) B183937
theorem B245267 : Blo 159796 245267 := bstep (se 1 (by rfl) ⟨183950, by rfl⟩ : syracuseStep 245267 = 367901) B367901
theorem B245297 : Blo 159796 245297 := bstep (se 2 (by rfl) ⟨91986, by rfl⟩ : syracuseStep 245297 = 183973) B183973
theorem B179779 : Blo 159796 179779 := bstep (se 1 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 179779 = 269669) B269669
theorem B245315 : Blo 159796 245315 := bstep (se 1 (by rfl) ⟨183986, by rfl⟩ : syracuseStep 245315 = 367973) B367973
theorem B245345 : Blo 159796 245345 := bstep (se 2 (by rfl) ⟨92004, by rfl⟩ : syracuseStep 245345 = 184009) B184009
theorem B540269 : Blo 159796 540269 := bstep (se 3 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 540269 = 202601) B202601
theorem B245363 : Blo 159796 245363 := bstep (se 1 (by rfl) ⟨184022, by rfl⟩ : syracuseStep 245363 = 368045) B368045
theorem B245393 : Blo 159796 245393 := bstep (se 2 (by rfl) ⟨92022, by rfl⟩ : syracuseStep 245393 = 184045) B184045
theorem B540323 : Blo 159796 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B245411 : Blo 159796 245411 := bstep (se 1 (by rfl) ⟨184058, by rfl⟩ : syracuseStep 245411 = 368117) B368117
theorem B245441 : Blo 159796 245441 := bstep (se 2 (by rfl) ⟨92040, by rfl⟩ : syracuseStep 245441 = 184081) B184081
theorem B409283 : Blo 159796 409283 := bstep (se 1 (by rfl) ⟨306962, by rfl⟩ : syracuseStep 409283 = 613925) B613925
theorem B179923 : Blo 159796 179923 := bstep (se 1 (by rfl) ⟨134942, by rfl⟩ : syracuseStep 179923 = 269885) B269885
theorem B245459 : Blo 159796 245459 := bstep (se 1 (by rfl) ⟨184094, by rfl⟩ : syracuseStep 245459 = 368189) B368189
theorem B245489 : Blo 159796 245489 := bstep (se 2 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 245489 = 184117) B184117
theorem B245507 : Blo 159796 245507 := bstep (se 1 (by rfl) ⟨184130, by rfl⟩ : syracuseStep 245507 = 368261) B368261
theorem B245537 : Blo 159796 245537 := bstep (se 2 (by rfl) ⟨92076, by rfl⟩ : syracuseStep 245537 = 184153) B184153
theorem B245555 : Blo 159796 245555 := bstep (se 1 (by rfl) ⟨184166, by rfl⟩ : syracuseStep 245555 = 368333) B368333
theorem B245585 : Blo 159796 245585 := bstep (se 2 (by rfl) ⟨92094, by rfl⟩ : syracuseStep 245585 = 184189) B184189
theorem B180067 : Blo 159796 180067 := bstep (se 1 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 180067 = 270101) B270101
theorem B245603 : Blo 159796 245603 := bstep (se 1 (by rfl) ⟨184202, by rfl⟩ : syracuseStep 245603 = 368405) B368405
theorem B245633 : Blo 159796 245633 := bstep (se 2 (by rfl) ⟨92112, by rfl⟩ : syracuseStep 245633 = 184225) B184225
theorem B409475 : Blo 159796 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B245651 : Blo 159796 245651 := bstep (se 1 (by rfl) ⟨184238, by rfl⟩ : syracuseStep 245651 = 368477) B368477
theorem B540593 : Blo 159796 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B245681 : Blo 159796 245681 := bstep (se 2 (by rfl) ⟨92130, by rfl⟩ : syracuseStep 245681 = 184261) B184261
theorem B1458161 : Blo 159796 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B180211 : Blo 159796 180211 := bstep (se 1 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 180211 = 270317) B270317
theorem B180355 : Blo 159796 180355 := bstep (se 1 (by rfl) ⟨135266, by rfl⟩ : syracuseStep 180355 = 270533) B270533
theorem B180499 : Blo 159796 180499 := bstep (se 1 (by rfl) ⟨135374, by rfl⟩ : syracuseStep 180499 = 270749) B270749
theorem B1982789 : Blo 159796 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B180643 : Blo 159796 180643 := bstep (se 1 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 180643 = 270965) B270965
theorem B541133 : Blo 159796 541133 := bstep (se 3 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 541133 = 202925) B202925
theorem B541187 : Blo 159796 541187 := bstep (se 1 (by rfl) ⟨405890, by rfl⟩ : syracuseStep 541187 = 811781) B811781
theorem B180787 : Blo 159796 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B344675 : Blo 159796 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B180931 : Blo 159796 180931 := bstep (se 1 (by rfl) ⟨135698, by rfl⟩ : syracuseStep 180931 = 271397) B271397
theorem B2081477 : Blo 159796 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B1098467 : Blo 159796 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B541457 : Blo 159796 541457 := bstep (se 2 (by rfl) ⟨203046, by rfl⟩ : syracuseStep 541457 = 406093) B406093
theorem B508717 : Blo 159796 508717 := bstep (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) B190769
theorem B410417 : Blo 159796 410417 := bstep (se 2 (by rfl) ⟨153906, by rfl⟩ : syracuseStep 410417 = 307813) B307813
theorem B279377 : Blo 159796 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B181075 : Blo 159796 181075 := bstep (se 1 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 181075 = 271613) B271613
theorem B410467 : Blo 159796 410467 := bstep (se 1 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 410467 = 615701) B615701
theorem B1491853 : Blo 159796 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B181219 : Blo 159796 181219 := bstep (se 1 (by rfl) ⟨135914, by rfl⟩ : syracuseStep 181219 = 271829) B271829
theorem B410609 : Blo 159796 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B181363 : Blo 159796 181363 := bstep (se 1 (by rfl) ⟨136022, by rfl⟩ : syracuseStep 181363 = 272045) B272045
theorem B607409 : Blo 159796 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B1230065 : Blo 159796 1230065 := bstep (se 2 (by rfl) ⟨461274, by rfl⟩ : syracuseStep 1230065 = 922549) B922549
theorem B181507 : Blo 159796 181507 := bstep (se 1 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 181507 = 272261) B272261
theorem B279811 : Blo 159796 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B541997 : Blo 159796 541997 := bstep (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) B203249
theorem B542051 : Blo 159796 542051 := bstep (se 1 (by rfl) ⟨406538, by rfl⟩ : syracuseStep 542051 = 813077) B813077
theorem B181651 : Blo 159796 181651 := bstep (se 1 (by rfl) ⟨136238, by rfl⟩ : syracuseStep 181651 = 272477) B272477
theorem B345539 : Blo 159796 345539 := bstep (se 1 (by rfl) ⟨259154, by rfl⟩ : syracuseStep 345539 = 518309) B518309
theorem B181795 : Blo 159796 181795 := bstep (se 1 (by rfl) ⟨136346, by rfl⟩ : syracuseStep 181795 = 272693) B272693
theorem B345649 : Blo 159796 345649 := bstep (se 2 (by rfl) ⟨129618, by rfl⟩ : syracuseStep 345649 = 259237) B259237
theorem B1754693 : Blo 159796 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B1558115 : Blo 159796 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B542321 : Blo 159796 542321 := bstep (se 2 (by rfl) ⟨203370, by rfl⟩ : syracuseStep 542321 = 406741) B406741
theorem B181939 : Blo 159796 181939 := bstep (se 1 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 181939 = 272909) B272909
theorem B247553 : Blo 159796 247553 := bstep (se 2 (by rfl) ⟨92832, by rfl⟩ : syracuseStep 247553 = 185665) B185665
theorem B182083 : Blo 159796 182083 := bstep (se 1 (by rfl) ⟨136562, by rfl⟩ : syracuseStep 182083 = 273125) B273125
theorem B411473 : Blo 159796 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B411601 : Blo 159796 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B182227 : Blo 159796 182227 := bstep (se 1 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 182227 = 273341) B273341
theorem B870385 : Blo 159796 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B182371 : Blo 159796 182371 := bstep (se 1 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 182371 = 273557) B273557
theorem B542861 : Blo 159796 542861 := bstep (se 3 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 542861 = 203573) B203573
theorem B542915 : Blo 159796 542915 := bstep (se 1 (by rfl) ⟨407186, by rfl⟩ : syracuseStep 542915 = 814373) B814373
theorem B411875 : Blo 159796 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B182515 : Blo 159796 182515 := bstep (se 1 (by rfl) ⟨136886, by rfl⟩ : syracuseStep 182515 = 273773) B273773
theorem B1821041 : Blo 159796 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B182659 : Blo 159796 182659 := bstep (se 1 (by rfl) ⟨136994, by rfl⟩ : syracuseStep 182659 = 273989) B273989
theorem B412067 : Blo 159796 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B1034693 : Blo 159796 1034693 := bstep (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) B194005
theorem B543185 : Blo 159796 543185 := bstep (se 2 (by rfl) ⟨203694, by rfl⟩ : syracuseStep 543185 = 407389) B407389
theorem B182803 : Blo 159796 182803 := bstep (se 1 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 182803 = 274205) B274205
theorem B608867 : Blo 159796 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B182947 : Blo 159796 182947 := bstep (se 1 (by rfl) ⟨137210, by rfl⟩ : syracuseStep 182947 = 274421) B274421
theorem B248579 : Blo 159796 248579 := bstep (se 1 (by rfl) ⟨186434, by rfl⟩ : syracuseStep 248579 = 372869) B372869
theorem B183091 : Blo 159796 183091 := bstep (se 1 (by rfl) ⟨137318, by rfl⟩ : syracuseStep 183091 = 274637) B274637
theorem B248627 : Blo 159796 248627 := bstep (se 1 (by rfl) ⟨186470, by rfl⟩ : syracuseStep 248627 = 372941) B372941
theorem B183235 : Blo 159796 183235 := bstep (se 1 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 183235 = 274853) B274853
theorem B543725 : Blo 159796 543725 := bstep (se 3 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 543725 = 203897) B203897
theorem B838669 : Blo 159796 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B543779 : Blo 159796 543779 := bstep (se 1 (by rfl) ⟨407834, by rfl⟩ : syracuseStep 543779 = 815669) B815669
theorem B183379 : Blo 159796 183379 := bstep (se 1 (by rfl) ⟨137534, by rfl⟩ : syracuseStep 183379 = 275069) B275069
theorem B5950691 : Blo 159796 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B183523 : Blo 159796 183523 := bstep (se 1 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 183523 = 275285) B275285
theorem B544049 : Blo 159796 544049 := bstep (se 2 (by rfl) ⟨204018, by rfl⟩ : syracuseStep 544049 = 408037) B408037
theorem B413009 : Blo 159796 413009 := bstep (se 2 (by rfl) ⟨154878, by rfl⟩ : syracuseStep 413009 = 309757) B309757
theorem B183667 : Blo 159796 183667 := bstep (se 1 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 183667 = 275501) B275501
theorem B413059 : Blo 159796 413059 := bstep (se 1 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 413059 = 619589) B619589
theorem B183811 : Blo 159796 183811 := bstep (se 1 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 183811 = 275717) B275717
theorem B347665 : Blo 159796 347665 := bstep (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) B260749
theorem B413201 : Blo 159796 413201 := bstep (se 2 (by rfl) ⟨154950, by rfl⟩ : syracuseStep 413201 = 309901) B309901
theorem B609869 : Blo 159796 609869 := bstep (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) B228701
theorem B183955 : Blo 159796 183955 := bstep (se 1 (by rfl) ⟨137966, by rfl⟩ : syracuseStep 183955 = 275933) B275933
theorem B184099 : Blo 159796 184099 := bstep (se 1 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 184099 = 276149) B276149
theorem B544589 : Blo 159796 544589 := bstep (se 3 (by rfl) ⟨102110, by rfl⟩ : syracuseStep 544589 = 204221) B204221
theorem B544643 : Blo 159796 544643 := bstep (se 1 (by rfl) ⟨408482, by rfl⟩ : syracuseStep 544643 = 816965) B816965
theorem B348067 : Blo 159796 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B184243 : Blo 159796 184243 := bstep (se 1 (by rfl) ⟨138182, by rfl⟩ : syracuseStep 184243 = 276365) B276365
theorem B1101937 : Blo 159796 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B544913 : Blo 159796 544913 := bstep (se 2 (by rfl) ⟨204342, by rfl⟩ : syracuseStep 544913 = 408685) B408685
theorem B17125829 : Blo 159796 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B414193 : Blo 159796 414193 := bstep (se 2 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 414193 = 310645) B310645
theorem B545453 : Blo 159796 545453 := bstep (se 3 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 545453 = 204545) B204545
theorem B545507 : Blo 159796 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B414467 : Blo 159796 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B545777 : Blo 159796 545777 := bstep (se 2 (by rfl) ⟨204666, by rfl⟩ : syracuseStep 545777 = 409333) B409333
theorem B218147 : Blo 159796 218147 := bstep (se 1 (by rfl) ⟨163610, by rfl⟩ : syracuseStep 218147 = 327221) B327221
theorem B513091 : Blo 159796 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B349571 : Blo 159796 349571 := bstep (se 1 (by rfl) ⟨262178, by rfl⟩ : syracuseStep 349571 = 524357) B524357
theorem B546317 : Blo 159796 546317 := bstep (se 3 (by rfl) ⟨102434, by rfl⟩ : syracuseStep 546317 = 204869) B204869
theorem B513553 : Blo 159796 513553 := bstep (se 2 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 513553 = 385165) B385165
theorem B546371 : Blo 159796 546371 := bstep (se 1 (by rfl) ⟨409778, by rfl⟩ : syracuseStep 546371 = 819557) B819557
theorem B611981 : Blo 159796 611981 := bstep (se 3 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 611981 = 229493) B229493
theorem B186019 : Blo 159796 186019 := bstep (se 1 (by rfl) ⟨139514, by rfl⟩ : syracuseStep 186019 = 279029) B279029
theorem B972515 : Blo 159796 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B546641 : Blo 159796 546641 := bstep (se 2 (by rfl) ⟨204990, by rfl⟩ : syracuseStep 546641 = 409981) B409981
theorem B1038257 : Blo 159796 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B547181 : Blo 159796 547181 := bstep (se 3 (by rfl) ⟨102596, by rfl⟩ : syracuseStep 547181 = 205193) B205193
theorem B547235 : Blo 159796 547235 := bstep (se 1 (by rfl) ⟨410426, by rfl⟩ : syracuseStep 547235 = 820853) B820853
theorem B612785 : Blo 159796 612785 := bstep (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) B459589
theorem B547469 : Blo 159796 547469 := bstep (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) B205301
theorem B547505 : Blo 159796 547505 := bstep (se 2 (by rfl) ⟨205314, by rfl⟩ : syracuseStep 547505 = 410629) B410629
theorem B777059 : Blo 159796 777059 := bstep (se 1 (by rfl) ⟨582794, by rfl⟩ : syracuseStep 777059 = 1165589) B1165589
theorem B613453 : Blo 159796 613453 := bstep (se 3 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 613453 = 230045) B230045
theorem B810161 : Blo 159796 810161 := bstep (se 2 (by rfl) ⟨303810, by rfl⟩ : syracuseStep 810161 = 607621) B607621
theorem B548045 : Blo 159796 548045 := bstep (se 3 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 548045 = 205517) B205517
theorem B548099 : Blo 159796 548099 := bstep (se 1 (by rfl) ⟨411074, by rfl⟩ : syracuseStep 548099 = 822149) B822149
theorem B220483 : Blo 159796 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B1039715 : Blo 159796 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B908813 : Blo 159796 908813 := bstep (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) B340805
theorem B548369 : Blo 159796 548369 := bstep (se 2 (by rfl) ⟨205638, by rfl⟩ : syracuseStep 548369 = 411277) B411277
theorem B941701 : Blo 159796 941701 := bstep (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) B176569
theorem B614243 : Blo 159796 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B942029 : Blo 159796 942029 := bstep (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) B353261
theorem B548909 : Blo 159796 548909 := bstep (se 3 (by rfl) ⟨102920, by rfl⟩ : syracuseStep 548909 = 205841) B205841
theorem B548963 : Blo 159796 548963 := bstep (se 1 (by rfl) ⟨411722, by rfl⟩ : syracuseStep 548963 = 823445) B823445
theorem B516269 : Blo 159796 516269 := bstep (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) B193601
theorem B418019 : Blo 159796 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B778481 : Blo 159796 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B549233 : Blo 159796 549233 := bstep (se 2 (by rfl) ⟨205962, by rfl⟩ : syracuseStep 549233 = 411925) B411925
theorem B614897 : Blo 159796 614897 := bstep (se 2 (by rfl) ⟨230586, by rfl⟩ : syracuseStep 614897 = 461173) B461173
theorem B811619 : Blo 159796 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B549773 : Blo 159796 549773 := bstep (se 3 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 549773 = 206165) B206165
theorem B549827 : Blo 159796 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B910385 : Blo 159796 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B1041457 : Blo 159796 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B1172677 : Blo 159796 1172677 := bstep (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) B219877
theorem B550097 : Blo 159796 550097 := bstep (se 2 (by rfl) ⟨206286, by rfl⟩ : syracuseStep 550097 = 412573) B412573
theorem B2647349 : Blo 159796 2647349 := bstep (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) B248189
theorem B812429 : Blo 159796 812429 := bstep (se 3 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 812429 = 304661) B304661
theorem B648931 : Blo 159796 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B517859 : Blo 159796 517859 := bstep (se 1 (by rfl) ⟨388394, by rfl⟩ : syracuseStep 517859 = 776789) B776789
theorem B550637 : Blo 159796 550637 := bstep (se 3 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 550637 = 206489) B206489
theorem B386819 : Blo 159796 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B550691 : Blo 159796 550691 := bstep (se 1 (by rfl) ⟨413018, by rfl⟩ : syracuseStep 550691 = 826037) B826037
theorem B616355 : Blo 159796 616355 := bstep (se 1 (by rfl) ⟨462266, by rfl⟩ : syracuseStep 616355 = 924533) B924533
theorem B616369 : Blo 159796 616369 := bstep (se 2 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 616369 = 462277) B462277
theorem B387011 : Blo 159796 387011 := bstep (se 1 (by rfl) ⟨290258, by rfl⟩ : syracuseStep 387011 = 580517) B580517
theorem B550961 : Blo 159796 550961 := bstep (se 2 (by rfl) ⟨206610, by rfl⟩ : syracuseStep 550961 = 413221) B413221
theorem B714865 : Blo 159796 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B256289 : Blo 159796 256289 := bstep (se 2 (by rfl) ⟨96108, by rfl⟩ : syracuseStep 256289 = 192217) B192217
theorem B289091 : Blo 159796 289091 := bstep (se 1 (by rfl) ⟨216818, by rfl⟩ : syracuseStep 289091 = 433637) B433637
theorem B223585 : Blo 159796 223585 := bstep (se 2 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 223585 = 167689) B167689
theorem B780749 : Blo 159796 780749 := bstep (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) B292781
theorem B911843 : Blo 159796 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B387587 : Blo 159796 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B551501 : Blo 159796 551501 := bstep (se 3 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 551501 = 206813) B206813
theorem B289379 : Blo 159796 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B3500657 : Blo 159796 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B551555 : Blo 159796 551555 := bstep (se 1 (by rfl) ⟨413666, by rfl⟩ : syracuseStep 551555 = 827333) B827333
theorem B780941 : Blo 159796 780941 := bstep (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) B292853
theorem B781169 : Blo 159796 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B387971 : Blo 159796 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B551825 : Blo 159796 551825 := bstep (se 2 (by rfl) ⟨206934, by rfl⟩ : syracuseStep 551825 = 413869) B413869
theorem B3533765 : Blo 159796 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B1043405 : Blo 159796 1043405 := bstep (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) B391277
theorem B519139 : Blo 159796 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B2190349 : Blo 159796 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B781325 : Blo 159796 781325 := bstep (se 3 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 781325 = 292997) B292997
theorem B1109189 : Blo 159796 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B519473 : Blo 159796 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B1371491 : Blo 159796 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B617827 : Blo 159796 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B552365 : Blo 159796 552365 := bstep (se 3 (by rfl) ⟨103568, by rfl⟩ : syracuseStep 552365 = 207137) B207137
theorem B552419 : Blo 159796 552419 := bstep (se 1 (by rfl) ⟨414314, by rfl⟩ : syracuseStep 552419 = 828629) B828629
theorem B257699 : Blo 159796 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B192179 : Blo 159796 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B388817 : Blo 159796 388817 := bstep (se 2 (by rfl) ⟨145806, by rfl⟩ : syracuseStep 388817 = 291613) B291613
theorem B683747 : Blo 159796 683747 := bstep (se 1 (by rfl) ⟨512810, by rfl⟩ : syracuseStep 683747 = 1025621) B1025621
theorem B552689 : Blo 159796 552689 := bstep (se 2 (by rfl) ⟨207258, by rfl⟩ : syracuseStep 552689 = 414517) B414517
theorem B257827 : Blo 159796 257827 := bstep (se 1 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 257827 = 386741) B386741
theorem B389009 : Blo 159796 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B1732549 : Blo 159796 1732549 := bstep (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) B324853
theorem B159811 : Blo 159796 159811 := bstep (se 1 (by rfl) ⟨119858, by rfl⟩ : syracuseStep 159811 = 239717) B239717
theorem B159827 : Blo 159796 159827 := bstep (se 1 (by rfl) ⟨119870, by rfl⟩ : syracuseStep 159827 = 239741) B239741
theorem B159843 : Blo 159796 159843 := bstep (se 1 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 159843 = 239765) B239765
theorem B159859 : Blo 159796 159859 := bstep (se 1 (by rfl) ⟨119894, by rfl⟩ : syracuseStep 159859 = 239789) B239789
theorem B159875 : Blo 159796 159875 := bstep (se 1 (by rfl) ⟨119906, by rfl⟩ : syracuseStep 159875 = 239813) B239813
theorem B159891 : Blo 159796 159891 := bstep (se 1 (by rfl) ⟨119918, by rfl⟩ : syracuseStep 159891 = 239837) B239837
theorem B159907 : Blo 159796 159907 := bstep (se 1 (by rfl) ⟨119930, by rfl⟩ : syracuseStep 159907 = 239861) B239861
theorem B159923 : Blo 159796 159923 := bstep (se 1 (by rfl) ⟨119942, by rfl⟩ : syracuseStep 159923 = 239885) B239885
theorem B159939 : Blo 159796 159939 := bstep (se 1 (by rfl) ⟨119954, by rfl⟩ : syracuseStep 159939 = 239909) B239909
theorem B159955 : Blo 159796 159955 := bstep (se 1 (by rfl) ⟨119966, by rfl⟩ : syracuseStep 159955 = 239933) B239933
theorem B159971 : Blo 159796 159971 := bstep (se 1 (by rfl) ⟨119978, by rfl⟩ : syracuseStep 159971 = 239957) B239957
theorem B815345 : Blo 159796 815345 := bstep (se 2 (by rfl) ⟨305754, by rfl⟩ : syracuseStep 815345 = 611509) B611509
theorem B159987 : Blo 159796 159987 := bstep (se 1 (by rfl) ⟨119990, by rfl⟩ : syracuseStep 159987 = 239981) B239981
theorem B160003 : Blo 159796 160003 := bstep (se 1 (by rfl) ⟨120002, by rfl⟩ : syracuseStep 160003 = 240005) B240005
theorem B160019 : Blo 159796 160019 := bstep (se 1 (by rfl) ⟨120014, by rfl⟩ : syracuseStep 160019 = 240029) B240029
theorem B160035 : Blo 159796 160035 := bstep (se 1 (by rfl) ⟨120026, by rfl⟩ : syracuseStep 160035 = 240053) B240053
theorem B160051 : Blo 159796 160051 := bstep (se 1 (by rfl) ⟨120038, by rfl⟩ : syracuseStep 160051 = 240077) B240077
theorem B160067 : Blo 159796 160067 := bstep (se 1 (by rfl) ⟨120050, by rfl⟩ : syracuseStep 160067 = 240101) B240101
theorem B258385 : Blo 159796 258385 := bstep (se 2 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 258385 = 193789) B193789
theorem B160083 : Blo 159796 160083 := bstep (se 1 (by rfl) ⟨120062, by rfl⟩ : syracuseStep 160083 = 240125) B240125
theorem B160099 : Blo 159796 160099 := bstep (se 1 (by rfl) ⟨120074, by rfl⟩ : syracuseStep 160099 = 240149) B240149
theorem B160115 : Blo 159796 160115 := bstep (se 1 (by rfl) ⟨120086, by rfl⟩ : syracuseStep 160115 = 240173) B240173
theorem B160131 : Blo 159796 160131 := bstep (se 1 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 160131 = 240197) B240197
theorem B160147 : Blo 159796 160147 := bstep (se 1 (by rfl) ⟨120110, by rfl⟩ : syracuseStep 160147 = 240221) B240221
theorem B160163 : Blo 159796 160163 := bstep (se 1 (by rfl) ⟨120122, by rfl⟩ : syracuseStep 160163 = 240245) B240245
theorem B160179 : Blo 159796 160179 := bstep (se 1 (by rfl) ⟨120134, by rfl⟩ : syracuseStep 160179 = 240269) B240269
theorem B160195 : Blo 159796 160195 := bstep (se 1 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 160195 = 240293) B240293
theorem B291281 : Blo 159796 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B160211 : Blo 159796 160211 := bstep (se 1 (by rfl) ⟨120158, by rfl⟩ : syracuseStep 160211 = 240317) B240317
theorem B160227 : Blo 159796 160227 := bstep (se 1 (by rfl) ⟨120170, by rfl⟩ : syracuseStep 160227 = 240341) B240341
theorem B160243 : Blo 159796 160243 := bstep (se 1 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 160243 = 240365) B240365
theorem B160259 : Blo 159796 160259 := bstep (se 1 (by rfl) ⟨120194, by rfl⟩ : syracuseStep 160259 = 240389) B240389
theorem B586253 : Blo 159796 586253 := bstep (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) B219845
theorem B160275 : Blo 159796 160275 := bstep (se 1 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 160275 = 240413) B240413
theorem B160291 : Blo 159796 160291 := bstep (se 1 (by rfl) ⟨120218, by rfl⟩ : syracuseStep 160291 = 240437) B240437
theorem B160307 : Blo 159796 160307 := bstep (se 1 (by rfl) ⟨120230, by rfl⟩ : syracuseStep 160307 = 240461) B240461
theorem B160323 : Blo 159796 160323 := bstep (se 1 (by rfl) ⟨120242, by rfl⟩ : syracuseStep 160323 = 240485) B240485
theorem B160339 : Blo 159796 160339 := bstep (se 1 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 160339 = 240509) B240509
theorem B160355 : Blo 159796 160355 := bstep (se 1 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 160355 = 240533) B240533
theorem B488035 : Blo 159796 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B389731 : Blo 159796 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B160371 : Blo 159796 160371 := bstep (se 1 (by rfl) ⟨120278, by rfl⟩ : syracuseStep 160371 = 240557) B240557
theorem B160387 : Blo 159796 160387 := bstep (se 1 (by rfl) ⟨120290, by rfl⟩ : syracuseStep 160387 = 240581) B240581
theorem B160403 : Blo 159796 160403 := bstep (se 1 (by rfl) ⟨120302, by rfl⟩ : syracuseStep 160403 = 240605) B240605
theorem B160419 : Blo 159796 160419 := bstep (se 1 (by rfl) ⟨120314, by rfl⟩ : syracuseStep 160419 = 240629) B240629
theorem B455341 : Blo 159796 455341 := bstep (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) B170753
theorem B160435 : Blo 159796 160435 := bstep (se 1 (by rfl) ⟨120326, by rfl⟩ : syracuseStep 160435 = 240653) B240653
theorem B160451 : Blo 159796 160451 := bstep (se 1 (by rfl) ⟨120338, by rfl⟩ : syracuseStep 160451 = 240677) B240677
theorem B160467 : Blo 159796 160467 := bstep (se 1 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 160467 = 240701) B240701
theorem B160483 : Blo 159796 160483 := bstep (se 1 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 160483 = 240725) B240725
theorem B160499 : Blo 159796 160499 := bstep (se 1 (by rfl) ⟨120374, by rfl⟩ : syracuseStep 160499 = 240749) B240749
theorem B160515 : Blo 159796 160515 := bstep (se 1 (by rfl) ⟨120386, by rfl⟩ : syracuseStep 160515 = 240773) B240773
theorem B160531 : Blo 159796 160531 := bstep (se 1 (by rfl) ⟨120398, by rfl⟩ : syracuseStep 160531 = 240797) B240797
theorem B160547 : Blo 159796 160547 := bstep (se 1 (by rfl) ⟨120410, by rfl⟩ : syracuseStep 160547 = 240821) B240821
theorem B160563 : Blo 159796 160563 := bstep (se 1 (by rfl) ⟨120422, by rfl⟩ : syracuseStep 160563 = 240845) B240845
theorem B160579 : Blo 159796 160579 := bstep (se 1 (by rfl) ⟨120434, by rfl⟩ : syracuseStep 160579 = 240869) B240869
theorem B1307461 : Blo 159796 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B160595 : Blo 159796 160595 := bstep (se 1 (by rfl) ⟨120446, by rfl⟩ : syracuseStep 160595 = 240893) B240893
theorem B160611 : Blo 159796 160611 := bstep (se 1 (by rfl) ⟨120458, by rfl⟩ : syracuseStep 160611 = 240917) B240917
theorem B160627 : Blo 159796 160627 := bstep (se 1 (by rfl) ⟨120470, by rfl⟩ : syracuseStep 160627 = 240941) B240941
theorem B160643 : Blo 159796 160643 := bstep (se 1 (by rfl) ⟨120482, by rfl⟩ : syracuseStep 160643 = 240965) B240965
theorem B1766285 : Blo 159796 1766285 := bstep (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) B662357
theorem B160659 : Blo 159796 160659 := bstep (se 1 (by rfl) ⟨120494, by rfl⟩ : syracuseStep 160659 = 240989) B240989
theorem B160675 : Blo 159796 160675 := bstep (se 1 (by rfl) ⟨120506, by rfl⟩ : syracuseStep 160675 = 241013) B241013
theorem B160691 : Blo 159796 160691 := bstep (se 1 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 160691 = 241037) B241037
theorem B160707 : Blo 159796 160707 := bstep (se 1 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 160707 = 241061) B241061
theorem B160723 : Blo 159796 160723 := bstep (se 1 (by rfl) ⟨120542, by rfl⟩ : syracuseStep 160723 = 241085) B241085
theorem B160739 : Blo 159796 160739 := bstep (se 1 (by rfl) ⟨120554, by rfl⟩ : syracuseStep 160739 = 241109) B241109
theorem B259057 : Blo 159796 259057 := bstep (se 2 (by rfl) ⟨97146, by rfl⟩ : syracuseStep 259057 = 194293) B194293
theorem B160755 : Blo 159796 160755 := bstep (se 1 (by rfl) ⟨120566, by rfl⟩ : syracuseStep 160755 = 241133) B241133
theorem B160771 : Blo 159796 160771 := bstep (se 1 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 160771 = 241157) B241157
theorem B160787 : Blo 159796 160787 := bstep (se 1 (by rfl) ⟨120590, by rfl⟩ : syracuseStep 160787 = 241181) B241181
theorem B160803 : Blo 159796 160803 := bstep (se 1 (by rfl) ⟨120602, by rfl⟩ : syracuseStep 160803 = 241205) B241205
theorem B160819 : Blo 159796 160819 := bstep (se 1 (by rfl) ⟨120614, by rfl⟩ : syracuseStep 160819 = 241229) B241229
theorem B160835 : Blo 159796 160835 := bstep (se 1 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 160835 = 241253) B241253
theorem B160851 : Blo 159796 160851 := bstep (se 1 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 160851 = 241277) B241277
theorem B160867 : Blo 159796 160867 := bstep (se 1 (by rfl) ⟨120650, by rfl⟩ : syracuseStep 160867 = 241301) B241301
theorem B2290801 : Blo 159796 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B160883 : Blo 159796 160883 := bstep (se 1 (by rfl) ⟨120662, by rfl⟩ : syracuseStep 160883 = 241325) B241325
theorem B160899 : Blo 159796 160899 := bstep (se 1 (by rfl) ⟨120674, by rfl⟩ : syracuseStep 160899 = 241349) B241349
theorem B160915 : Blo 159796 160915 := bstep (se 1 (by rfl) ⟨120686, by rfl⟩ : syracuseStep 160915 = 241373) B241373
theorem B160931 : Blo 159796 160931 := bstep (se 1 (by rfl) ⟨120698, by rfl⟩ : syracuseStep 160931 = 241397) B241397
theorem B160947 : Blo 159796 160947 := bstep (se 1 (by rfl) ⟨120710, by rfl⟩ : syracuseStep 160947 = 241421) B241421
theorem B160963 : Blo 159796 160963 := bstep (se 1 (by rfl) ⟨120722, by rfl⟩ : syracuseStep 160963 = 241445) B241445
theorem B160979 : Blo 159796 160979 := bstep (se 1 (by rfl) ⟨120734, by rfl⟩ : syracuseStep 160979 = 241469) B241469
theorem B160995 : Blo 159796 160995 := bstep (se 1 (by rfl) ⟨120746, by rfl⟩ : syracuseStep 160995 = 241493) B241493
theorem B161011 : Blo 159796 161011 := bstep (se 1 (by rfl) ⟨120758, by rfl⟩ : syracuseStep 161011 = 241517) B241517
theorem B161027 : Blo 159796 161027 := bstep (se 1 (by rfl) ⟨120770, by rfl⟩ : syracuseStep 161027 = 241541) B241541
theorem B161043 : Blo 159796 161043 := bstep (se 1 (by rfl) ⟨120782, by rfl⟩ : syracuseStep 161043 = 241565) B241565
theorem B161059 : Blo 159796 161059 := bstep (se 1 (by rfl) ⟨120794, by rfl⟩ : syracuseStep 161059 = 241589) B241589
theorem B161075 : Blo 159796 161075 := bstep (se 1 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 161075 = 241613) B241613
theorem B161091 : Blo 159796 161091 := bstep (se 1 (by rfl) ⟨120818, by rfl⟩ : syracuseStep 161091 = 241637) B241637
theorem B521549 : Blo 159796 521549 := bstep (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) B195581
theorem B161107 : Blo 159796 161107 := bstep (se 1 (by rfl) ⟨120830, by rfl⟩ : syracuseStep 161107 = 241661) B241661
theorem B161123 : Blo 159796 161123 := bstep (se 1 (by rfl) ⟨120842, by rfl⟩ : syracuseStep 161123 = 241685) B241685
theorem B750961 : Blo 159796 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B161139 : Blo 159796 161139 := bstep (se 1 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 161139 = 241709) B241709
theorem B161155 : Blo 159796 161155 := bstep (se 1 (by rfl) ⟨120866, by rfl⟩ : syracuseStep 161155 = 241733) B241733
theorem B161171 : Blo 159796 161171 := bstep (se 1 (by rfl) ⟨120878, by rfl⟩ : syracuseStep 161171 = 241757) B241757
theorem B161187 : Blo 159796 161187 := bstep (se 1 (by rfl) ⟨120890, by rfl⟩ : syracuseStep 161187 = 241781) B241781
theorem B390577 : Blo 159796 390577 := bstep (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) B292933
theorem B161203 : Blo 159796 161203 := bstep (se 1 (by rfl) ⟨120902, by rfl⟩ : syracuseStep 161203 = 241805) B241805
theorem B161219 : Blo 159796 161219 := bstep (se 1 (by rfl) ⟨120914, by rfl⟩ : syracuseStep 161219 = 241829) B241829
theorem B587213 : Blo 159796 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B161235 : Blo 159796 161235 := bstep (se 1 (by rfl) ⟨120926, by rfl⟩ : syracuseStep 161235 = 241853) B241853
theorem B161251 : Blo 159796 161251 := bstep (se 1 (by rfl) ⟨120938, by rfl⟩ : syracuseStep 161251 = 241877) B241877
theorem B161267 : Blo 159796 161267 := bstep (se 1 (by rfl) ⟨120950, by rfl⟩ : syracuseStep 161267 = 241901) B241901
theorem B161283 : Blo 159796 161283 := bstep (se 1 (by rfl) ⟨120962, by rfl⟩ : syracuseStep 161283 = 241925) B241925
theorem B620045 : Blo 159796 620045 := bstep (se 3 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 620045 = 232517) B232517
theorem B161299 : Blo 159796 161299 := bstep (se 1 (by rfl) ⟨120974, by rfl⟩ : syracuseStep 161299 = 241949) B241949
theorem B161315 : Blo 159796 161315 := bstep (se 1 (by rfl) ⟨120986, by rfl⟩ : syracuseStep 161315 = 241973) B241973
theorem B161331 : Blo 159796 161331 := bstep (se 1 (by rfl) ⟨120998, by rfl⟩ : syracuseStep 161331 = 241997) B241997
theorem B161347 : Blo 159796 161347 := bstep (se 1 (by rfl) ⟨121010, by rfl⟩ : syracuseStep 161347 = 242021) B242021
theorem B161363 : Blo 159796 161363 := bstep (se 1 (by rfl) ⟨121022, by rfl⟩ : syracuseStep 161363 = 242045) B242045
theorem B161379 : Blo 159796 161379 := bstep (se 1 (by rfl) ⟨121034, by rfl⟩ : syracuseStep 161379 = 242069) B242069
theorem B161395 : Blo 159796 161395 := bstep (se 1 (by rfl) ⟨121046, by rfl⟩ : syracuseStep 161395 = 242093) B242093
theorem B161411 : Blo 159796 161411 := bstep (se 1 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 161411 = 242117) B242117
theorem B915077 : Blo 159796 915077 := bstep (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) B171577
theorem B161427 : Blo 159796 161427 := bstep (se 1 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 161427 = 242141) B242141
theorem B816803 : Blo 159796 816803 := bstep (se 1 (by rfl) ⟨612602, by rfl⟩ : syracuseStep 816803 = 1225205) B1225205
theorem B161443 : Blo 159796 161443 := bstep (se 1 (by rfl) ⟨121082, by rfl⟩ : syracuseStep 161443 = 242165) B242165
theorem B161459 : Blo 159796 161459 := bstep (se 1 (by rfl) ⟨121094, by rfl⟩ : syracuseStep 161459 = 242189) B242189
theorem B161475 : Blo 159796 161475 := bstep (se 1 (by rfl) ⟨121106, by rfl⟩ : syracuseStep 161475 = 242213) B242213
theorem B161491 : Blo 159796 161491 := bstep (se 1 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 161491 = 242237) B242237
theorem B161507 : Blo 159796 161507 := bstep (se 1 (by rfl) ⟨121130, by rfl⟩ : syracuseStep 161507 = 242261) B242261
theorem B161523 : Blo 159796 161523 := bstep (se 1 (by rfl) ⟨121142, by rfl⟩ : syracuseStep 161523 = 242285) B242285
theorem B161539 : Blo 159796 161539 := bstep (se 1 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 161539 = 242309) B242309
theorem B161555 : Blo 159796 161555 := bstep (se 1 (by rfl) ⟨121166, by rfl⟩ : syracuseStep 161555 = 242333) B242333
theorem B161571 : Blo 159796 161571 := bstep (se 1 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 161571 = 242357) B242357
theorem B161587 : Blo 159796 161587 := bstep (se 1 (by rfl) ⟨121190, by rfl⟩ : syracuseStep 161587 = 242381) B242381
theorem B161603 : Blo 159796 161603 := bstep (se 1 (by rfl) ⟨121202, by rfl⟩ : syracuseStep 161603 = 242405) B242405
theorem B161619 : Blo 159796 161619 := bstep (se 1 (by rfl) ⟨121214, by rfl⟩ : syracuseStep 161619 = 242429) B242429
theorem B161635 : Blo 159796 161635 := bstep (se 1 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 161635 = 242453) B242453
theorem B161651 : Blo 159796 161651 := bstep (se 1 (by rfl) ⟨121238, by rfl⟩ : syracuseStep 161651 = 242477) B242477
theorem B161667 : Blo 159796 161667 := bstep (se 1 (by rfl) ⟨121250, by rfl⟩ : syracuseStep 161667 = 242501) B242501
theorem B161683 : Blo 159796 161683 := bstep (se 1 (by rfl) ⟨121262, by rfl⟩ : syracuseStep 161683 = 242525) B242525
theorem B161699 : Blo 159796 161699 := bstep (se 1 (by rfl) ⟨121274, by rfl⟩ : syracuseStep 161699 = 242549) B242549
theorem B161715 : Blo 159796 161715 := bstep (se 1 (by rfl) ⟨121286, by rfl⟩ : syracuseStep 161715 = 242573) B242573
theorem B161731 : Blo 159796 161731 := bstep (se 1 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 161731 = 242597) B242597
theorem B161747 : Blo 159796 161747 := bstep (se 1 (by rfl) ⟨121310, by rfl⟩ : syracuseStep 161747 = 242621) B242621
theorem B161763 : Blo 159796 161763 := bstep (se 1 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 161763 = 242645) B242645
theorem B161779 : Blo 159796 161779 := bstep (se 1 (by rfl) ⟨121334, by rfl⟩ : syracuseStep 161779 = 242669) B242669
theorem B260099 : Blo 159796 260099 := bstep (se 1 (by rfl) ⟨195074, by rfl⟩ : syracuseStep 260099 = 390149) B390149
theorem B161795 : Blo 159796 161795 := bstep (se 1 (by rfl) ⟨121346, by rfl⟩ : syracuseStep 161795 = 242693) B242693
theorem B161811 : Blo 159796 161811 := bstep (se 1 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 161811 = 242717) B242717
theorem B161827 : Blo 159796 161827 := bstep (se 1 (by rfl) ⟨121370, by rfl⟩ : syracuseStep 161827 = 242741) B242741
theorem B587825 : Blo 159796 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B161843 : Blo 159796 161843 := bstep (se 1 (by rfl) ⟨121382, by rfl⟩ : syracuseStep 161843 = 242765) B242765
theorem B260147 : Blo 159796 260147 := bstep (se 1 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 260147 = 390221) B390221
theorem B161859 : Blo 159796 161859 := bstep (se 1 (by rfl) ⟨121394, by rfl⟩ : syracuseStep 161859 = 242789) B242789
theorem B915533 : Blo 159796 915533 := bstep (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) B343325
theorem B161875 : Blo 159796 161875 := bstep (se 1 (by rfl) ⟨121406, by rfl⟩ : syracuseStep 161875 = 242813) B242813
theorem B161891 : Blo 159796 161891 := bstep (se 1 (by rfl) ⟨121418, by rfl⟩ : syracuseStep 161891 = 242837) B242837
theorem B161907 : Blo 159796 161907 := bstep (se 1 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 161907 = 242861) B242861
theorem B161923 : Blo 159796 161923 := bstep (se 1 (by rfl) ⟨121442, by rfl⟩ : syracuseStep 161923 = 242885) B242885
theorem B1734797 : Blo 159796 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B161939 : Blo 159796 161939 := bstep (se 1 (by rfl) ⟨121454, by rfl⟩ : syracuseStep 161939 = 242909) B242909
theorem B161955 : Blo 159796 161955 := bstep (se 1 (by rfl) ⟨121466, by rfl⟩ : syracuseStep 161955 = 242933) B242933
theorem B161971 : Blo 159796 161971 := bstep (se 1 (by rfl) ⟨121478, by rfl⟩ : syracuseStep 161971 = 242957) B242957
theorem B161987 : Blo 159796 161987 := bstep (se 1 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 161987 = 242981) B242981
theorem B227539 : Blo 159796 227539 := bstep (se 1 (by rfl) ⟨170654, by rfl⟩ : syracuseStep 227539 = 341309) B341309
theorem B162003 : Blo 159796 162003 := bstep (se 1 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 162003 = 243005) B243005
theorem B162019 : Blo 159796 162019 := bstep (se 1 (by rfl) ⟨121514, by rfl⟩ : syracuseStep 162019 = 243029) B243029
theorem B162035 : Blo 159796 162035 := bstep (se 1 (by rfl) ⟨121526, by rfl⟩ : syracuseStep 162035 = 243053) B243053
theorem B162051 : Blo 159796 162051 := bstep (se 1 (by rfl) ⟨121538, by rfl⟩ : syracuseStep 162051 = 243077) B243077
theorem B1046789 : Blo 159796 1046789 := bstep (se 4 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 1046789 = 196273) B196273
theorem B162067 : Blo 159796 162067 := bstep (se 1 (by rfl) ⟨121550, by rfl⟩ : syracuseStep 162067 = 243101) B243101
theorem B162083 : Blo 159796 162083 := bstep (se 1 (by rfl) ⟨121562, by rfl⟩ : syracuseStep 162083 = 243125) B243125
theorem B162099 : Blo 159796 162099 := bstep (se 1 (by rfl) ⟨121574, by rfl⟩ : syracuseStep 162099 = 243149) B243149
theorem B162115 : Blo 159796 162115 := bstep (se 1 (by rfl) ⟨121586, by rfl⟩ : syracuseStep 162115 = 243173) B243173
theorem B162131 : Blo 159796 162131 := bstep (se 1 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 162131 = 243197) B243197
theorem B162147 : Blo 159796 162147 := bstep (se 1 (by rfl) ⟨121610, by rfl⟩ : syracuseStep 162147 = 243221) B243221
theorem B457073 : Blo 159796 457073 := bstep (se 2 (by rfl) ⟨171402, by rfl⟩ : syracuseStep 457073 = 342805) B342805
theorem B162163 : Blo 159796 162163 := bstep (se 1 (by rfl) ⟨121622, by rfl⟩ : syracuseStep 162163 = 243245) B243245
theorem B162179 : Blo 159796 162179 := bstep (se 1 (by rfl) ⟨121634, by rfl⟩ : syracuseStep 162179 = 243269) B243269
theorem B162195 : Blo 159796 162195 := bstep (se 1 (by rfl) ⟨121646, by rfl⟩ : syracuseStep 162195 = 243293) B243293
theorem B162211 : Blo 159796 162211 := bstep (se 1 (by rfl) ⟨121658, by rfl⟩ : syracuseStep 162211 = 243317) B243317
theorem B162227 : Blo 159796 162227 := bstep (se 1 (by rfl) ⟨121670, by rfl⟩ : syracuseStep 162227 = 243341) B243341
theorem B162243 : Blo 159796 162243 := bstep (se 1 (by rfl) ⟨121682, by rfl⟩ : syracuseStep 162243 = 243365) B243365
theorem B817613 : Blo 159796 817613 := bstep (se 3 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 817613 = 306605) B306605
theorem B162259 : Blo 159796 162259 := bstep (se 1 (by rfl) ⟨121694, by rfl⟩ : syracuseStep 162259 = 243389) B243389
theorem B653795 : Blo 159796 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B162275 : Blo 159796 162275 := bstep (se 1 (by rfl) ⟨121706, by rfl⟩ : syracuseStep 162275 = 243413) B243413
theorem B195043 : Blo 159796 195043 := bstep (se 1 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 195043 = 292565) B292565
theorem B162291 : Blo 159796 162291 := bstep (se 1 (by rfl) ⟨121718, by rfl⟩ : syracuseStep 162291 = 243437) B243437
theorem B162307 : Blo 159796 162307 := bstep (se 1 (by rfl) ⟨121730, by rfl⟩ : syracuseStep 162307 = 243461) B243461
theorem B162323 : Blo 159796 162323 := bstep (se 1 (by rfl) ⟨121742, by rfl⟩ : syracuseStep 162323 = 243485) B243485
theorem B162339 : Blo 159796 162339 := bstep (se 1 (by rfl) ⟨121754, by rfl⟩ : syracuseStep 162339 = 243509) B243509
theorem B457265 : Blo 159796 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B162355 : Blo 159796 162355 := bstep (se 1 (by rfl) ⟨121766, by rfl⟩ : syracuseStep 162355 = 243533) B243533
theorem B162371 : Blo 159796 162371 := bstep (se 1 (by rfl) ⟨121778, by rfl⟩ : syracuseStep 162371 = 243557) B243557
theorem B162387 : Blo 159796 162387 := bstep (se 1 (by rfl) ⟨121790, by rfl⟩ : syracuseStep 162387 = 243581) B243581
theorem B162403 : Blo 159796 162403 := bstep (se 1 (by rfl) ⟨121802, by rfl⟩ : syracuseStep 162403 = 243605) B243605
theorem B162419 : Blo 159796 162419 := bstep (se 1 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 162419 = 243629) B243629
theorem B162435 : Blo 159796 162435 := bstep (se 1 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 162435 = 243653) B243653
theorem B162451 : Blo 159796 162451 := bstep (se 1 (by rfl) ⟨121838, by rfl⟩ : syracuseStep 162451 = 243677) B243677
theorem B162467 : Blo 159796 162467 := bstep (se 1 (by rfl) ⟨121850, by rfl⟩ : syracuseStep 162467 = 243701) B243701
theorem B162483 : Blo 159796 162483 := bstep (se 1 (by rfl) ⟨121862, by rfl⟩ : syracuseStep 162483 = 243725) B243725
theorem B228035 : Blo 159796 228035 := bstep (se 1 (by rfl) ⟨171026, by rfl⟩ : syracuseStep 228035 = 342053) B342053
theorem B162499 : Blo 159796 162499 := bstep (se 1 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 162499 = 243749) B243749
theorem B162515 : Blo 159796 162515 := bstep (se 1 (by rfl) ⟨121886, by rfl⟩ : syracuseStep 162515 = 243773) B243773
theorem B162531 : Blo 159796 162531 := bstep (se 1 (by rfl) ⟨121898, by rfl⟩ : syracuseStep 162531 = 243797) B243797
theorem B162547 : Blo 159796 162547 := bstep (se 1 (by rfl) ⟨121910, by rfl⟩ : syracuseStep 162547 = 243821) B243821
theorem B162563 : Blo 159796 162563 := bstep (se 1 (by rfl) ⟨121922, by rfl⟩ : syracuseStep 162563 = 243845) B243845
theorem B162579 : Blo 159796 162579 := bstep (se 1 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 162579 = 243869) B243869
theorem B4193045 : Blo 159796 4193045 := bstep (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) B196549
theorem B162595 : Blo 159796 162595 := bstep (se 1 (by rfl) ⟨121946, by rfl⟩ : syracuseStep 162595 = 243893) B243893
theorem B162611 : Blo 159796 162611 := bstep (se 1 (by rfl) ⟨121958, by rfl⟩ : syracuseStep 162611 = 243917) B243917
theorem B162627 : Blo 159796 162627 := bstep (se 1 (by rfl) ⟨121970, by rfl⟩ : syracuseStep 162627 = 243941) B243941
theorem B162643 : Blo 159796 162643 := bstep (se 1 (by rfl) ⟨121982, by rfl⟩ : syracuseStep 162643 = 243965) B243965
theorem B162659 : Blo 159796 162659 := bstep (se 1 (by rfl) ⟨121994, by rfl⟩ : syracuseStep 162659 = 243989) B243989
theorem B162675 : Blo 159796 162675 := bstep (se 1 (by rfl) ⟨122006, by rfl⟩ : syracuseStep 162675 = 244013) B244013
theorem B162691 : Blo 159796 162691 := bstep (se 1 (by rfl) ⟨122018, by rfl⟩ : syracuseStep 162691 = 244037) B244037
theorem B162707 : Blo 159796 162707 := bstep (se 1 (by rfl) ⟨122030, by rfl⟩ : syracuseStep 162707 = 244061) B244061
theorem B162723 : Blo 159796 162723 := bstep (se 1 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 162723 = 244085) B244085
theorem B162739 : Blo 159796 162739 := bstep (se 1 (by rfl) ⟨122054, by rfl⟩ : syracuseStep 162739 = 244109) B244109
theorem B195523 : Blo 159796 195523 := bstep (se 1 (by rfl) ⟨146642, by rfl⟩ : syracuseStep 195523 = 293285) B293285
theorem B162755 : Blo 159796 162755 := bstep (se 1 (by rfl) ⟨122066, by rfl⟩ : syracuseStep 162755 = 244133) B244133
theorem B162771 : Blo 159796 162771 := bstep (se 1 (by rfl) ⟨122078, by rfl⟩ : syracuseStep 162771 = 244157) B244157
theorem B162787 : Blo 159796 162787 := bstep (se 1 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 162787 = 244181) B244181
theorem B162803 : Blo 159796 162803 := bstep (se 1 (by rfl) ⟨122102, by rfl⟩ : syracuseStep 162803 = 244205) B244205
theorem B162819 : Blo 159796 162819 := bstep (se 1 (by rfl) ⟨122114, by rfl⟩ : syracuseStep 162819 = 244229) B244229
theorem B162835 : Blo 159796 162835 := bstep (se 1 (by rfl) ⟨122126, by rfl⟩ : syracuseStep 162835 = 244253) B244253
theorem B162851 : Blo 159796 162851 := bstep (se 1 (by rfl) ⟨122138, by rfl⟩ : syracuseStep 162851 = 244277) B244277
theorem B162867 : Blo 159796 162867 := bstep (se 1 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 162867 = 244301) B244301
theorem B162883 : Blo 159796 162883 := bstep (se 1 (by rfl) ⟨122162, by rfl⟩ : syracuseStep 162883 = 244325) B244325
theorem B523331 : Blo 159796 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B162899 : Blo 159796 162899 := bstep (se 1 (by rfl) ⟨122174, by rfl⟩ : syracuseStep 162899 = 244349) B244349
theorem B162915 : Blo 159796 162915 := bstep (se 1 (by rfl) ⟨122186, by rfl⟩ : syracuseStep 162915 = 244373) B244373
theorem B162931 : Blo 159796 162931 := bstep (se 1 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 162931 = 244397) B244397
theorem B162947 : Blo 159796 162947 := bstep (se 1 (by rfl) ⟨122210, by rfl⟩ : syracuseStep 162947 = 244421) B244421
theorem B162963 : Blo 159796 162963 := bstep (se 1 (by rfl) ⟨122222, by rfl⟩ : syracuseStep 162963 = 244445) B244445
theorem B162979 : Blo 159796 162979 := bstep (se 1 (by rfl) ⟨122234, by rfl⟩ : syracuseStep 162979 = 244469) B244469
theorem B162995 : Blo 159796 162995 := bstep (se 1 (by rfl) ⟨122246, by rfl⟩ : syracuseStep 162995 = 244493) B244493
theorem B163011 : Blo 159796 163011 := bstep (se 1 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 163011 = 244517) B244517
theorem B163027 : Blo 159796 163027 := bstep (se 1 (by rfl) ⟨122270, by rfl⟩ : syracuseStep 163027 = 244541) B244541
theorem B163043 : Blo 159796 163043 := bstep (se 1 (by rfl) ⟨122282, by rfl⟩ : syracuseStep 163043 = 244565) B244565
theorem B163059 : Blo 159796 163059 := bstep (se 1 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 163059 = 244589) B244589
theorem B163075 : Blo 159796 163075 := bstep (se 1 (by rfl) ⟨122306, by rfl⟩ : syracuseStep 163075 = 244613) B244613
theorem B163091 : Blo 159796 163091 := bstep (se 1 (by rfl) ⟨122318, by rfl⟩ : syracuseStep 163091 = 244637) B244637
theorem B163107 : Blo 159796 163107 := bstep (se 1 (by rfl) ⟨122330, by rfl⟩ : syracuseStep 163107 = 244661) B244661
theorem B359729 : Blo 159796 359729 := bstep (se 2 (by rfl) ⟨134898, by rfl⟩ : syracuseStep 359729 = 269797) B269797
theorem B163123 : Blo 159796 163123 := bstep (se 1 (by rfl) ⟨122342, by rfl⟩ : syracuseStep 163123 = 244685) B244685
theorem B228673 : Blo 159796 228673 := bstep (se 2 (by rfl) ⟨85752, by rfl⟩ : syracuseStep 228673 = 171505) B171505
theorem B359747 : Blo 159796 359747 := bstep (se 1 (by rfl) ⟨269810, by rfl⟩ : syracuseStep 359747 = 539621) B539621
theorem B163139 : Blo 159796 163139 := bstep (se 1 (by rfl) ⟨122354, by rfl⟩ : syracuseStep 163139 = 244709) B244709
theorem B687437 : Blo 159796 687437 := bstep (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) B257789
theorem B163155 : Blo 159796 163155 := bstep (se 1 (by rfl) ⟨122366, by rfl⟩ : syracuseStep 163155 = 244733) B244733
theorem B163171 : Blo 159796 163171 := bstep (se 1 (by rfl) ⟨122378, by rfl⟩ : syracuseStep 163171 = 244757) B244757
theorem B163187 : Blo 159796 163187 := bstep (se 1 (by rfl) ⟨122390, by rfl⟩ : syracuseStep 163187 = 244781) B244781
theorem B163203 : Blo 159796 163203 := bstep (se 1 (by rfl) ⟨122402, by rfl⟩ : syracuseStep 163203 = 244805) B244805
theorem B163219 : Blo 159796 163219 := bstep (se 1 (by rfl) ⟨122414, by rfl⟩ : syracuseStep 163219 = 244829) B244829
theorem B163235 : Blo 159796 163235 := bstep (se 1 (by rfl) ⟨122426, by rfl⟩ : syracuseStep 163235 = 244853) B244853
theorem B163251 : Blo 159796 163251 := bstep (se 1 (by rfl) ⟨122438, by rfl⟩ : syracuseStep 163251 = 244877) B244877
theorem B261569 : Blo 159796 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B163267 : Blo 159796 163267 := bstep (se 1 (by rfl) ⟨122450, by rfl⟩ : syracuseStep 163267 = 244901) B244901
theorem B163283 : Blo 159796 163283 := bstep (se 1 (by rfl) ⟨122462, by rfl⟩ : syracuseStep 163283 = 244925) B244925
theorem B163299 : Blo 159796 163299 := bstep (se 1 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 163299 = 244949) B244949
theorem B163315 : Blo 159796 163315 := bstep (se 1 (by rfl) ⟨122486, by rfl⟩ : syracuseStep 163315 = 244973) B244973
theorem B163331 : Blo 159796 163331 := bstep (se 1 (by rfl) ⟨122498, by rfl⟩ : syracuseStep 163331 = 244997) B244997
theorem B458257 : Blo 159796 458257 := bstep (se 2 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 458257 = 343693) B343693
theorem B163347 : Blo 159796 163347 := bstep (se 1 (by rfl) ⟨122510, by rfl⟩ : syracuseStep 163347 = 245021) B245021
theorem B163363 : Blo 159796 163363 := bstep (se 1 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 163363 = 245045) B245045
theorem B163379 : Blo 159796 163379 := bstep (se 1 (by rfl) ⟨122534, by rfl⟩ : syracuseStep 163379 = 245069) B245069
theorem B163395 : Blo 159796 163395 := bstep (se 1 (by rfl) ⟨122546, by rfl⟩ : syracuseStep 163395 = 245093) B245093
theorem B360017 : Blo 159796 360017 := bstep (se 2 (by rfl) ⟨135006, by rfl⟩ : syracuseStep 360017 = 270013) B270013
theorem B163411 : Blo 159796 163411 := bstep (se 1 (by rfl) ⟨122558, by rfl⟩ : syracuseStep 163411 = 245117) B245117
theorem B360035 : Blo 159796 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B163427 : Blo 159796 163427 := bstep (se 1 (by rfl) ⟨122570, by rfl⟩ : syracuseStep 163427 = 245141) B245141
theorem B163443 : Blo 159796 163443 := bstep (se 1 (by rfl) ⟨122582, by rfl⟩ : syracuseStep 163443 = 245165) B245165
theorem B163459 : Blo 159796 163459 := bstep (se 1 (by rfl) ⟨122594, by rfl⟩ : syracuseStep 163459 = 245189) B245189
theorem B229009 : Blo 159796 229009 := bstep (se 2 (by rfl) ⟨85878, by rfl⟩ : syracuseStep 229009 = 171757) B171757
theorem B163475 : Blo 159796 163475 := bstep (se 1 (by rfl) ⟨122606, by rfl⟩ : syracuseStep 163475 = 245213) B245213
theorem B163491 : Blo 159796 163491 := bstep (se 1 (by rfl) ⟨122618, by rfl⟩ : syracuseStep 163491 = 245237) B245237
theorem B163507 : Blo 159796 163507 := bstep (se 1 (by rfl) ⟨122630, by rfl⟩ : syracuseStep 163507 = 245261) B245261
theorem B163523 : Blo 159796 163523 := bstep (se 1 (by rfl) ⟨122642, by rfl⟩ : syracuseStep 163523 = 245285) B245285
theorem B163539 : Blo 159796 163539 := bstep (se 1 (by rfl) ⟨122654, by rfl⟩ : syracuseStep 163539 = 245309) B245309
theorem B655075 : Blo 159796 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B163555 : Blo 159796 163555 := bstep (se 1 (by rfl) ⟨122666, by rfl⟩ : syracuseStep 163555 = 245333) B245333
theorem B163571 : Blo 159796 163571 := bstep (se 1 (by rfl) ⟨122678, by rfl⟩ : syracuseStep 163571 = 245357) B245357
theorem B163587 : Blo 159796 163587 := bstep (se 1 (by rfl) ⟨122690, by rfl⟩ : syracuseStep 163587 = 245381) B245381
theorem B163603 : Blo 159796 163603 := bstep (se 1 (by rfl) ⟨122702, by rfl⟩ : syracuseStep 163603 = 245405) B245405
theorem B458531 : Blo 159796 458531 := bstep (se 1 (by rfl) ⟨343898, by rfl⟩ : syracuseStep 458531 = 687797) B687797
theorem B163619 : Blo 159796 163619 := bstep (se 1 (by rfl) ⟨122714, by rfl⟩ : syracuseStep 163619 = 245429) B245429
theorem B196403 : Blo 159796 196403 := bstep (se 1 (by rfl) ⟨147302, by rfl⟩ : syracuseStep 196403 = 294605) B294605
theorem B163635 : Blo 159796 163635 := bstep (se 1 (by rfl) ⟨122726, by rfl⟩ : syracuseStep 163635 = 245453) B245453
theorem B2817845 : Blo 159796 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B163651 : Blo 159796 163651 := bstep (se 1 (by rfl) ⟨122738, by rfl⟩ : syracuseStep 163651 = 245477) B245477
theorem B163667 : Blo 159796 163667 := bstep (se 1 (by rfl) ⟨122750, by rfl⟩ : syracuseStep 163667 = 245501) B245501
theorem B163683 : Blo 159796 163683 := bstep (se 1 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 163683 = 245525) B245525
theorem B360305 : Blo 159796 360305 := bstep (se 2 (by rfl) ⟨135114, by rfl⟩ : syracuseStep 360305 = 270229) B270229
theorem B163699 : Blo 159796 163699 := bstep (se 1 (by rfl) ⟨122774, by rfl⟩ : syracuseStep 163699 = 245549) B245549
theorem B360323 : Blo 159796 360323 := bstep (se 1 (by rfl) ⟨270242, by rfl⟩ : syracuseStep 360323 = 540485) B540485
theorem B163715 : Blo 159796 163715 := bstep (se 1 (by rfl) ⟨122786, by rfl⟩ : syracuseStep 163715 = 245573) B245573
theorem B425873 : Blo 159796 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B163731 : Blo 159796 163731 := bstep (se 1 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 163731 = 245597) B245597
theorem B163747 : Blo 159796 163747 := bstep (se 1 (by rfl) ⟨122810, by rfl⟩ : syracuseStep 163747 = 245621) B245621
theorem B163763 : Blo 159796 163763 := bstep (se 1 (by rfl) ⟨122822, by rfl⟩ : syracuseStep 163763 = 245645) B245645
theorem B163779 : Blo 159796 163779 := bstep (se 1 (by rfl) ⟨122834, by rfl⟩ : syracuseStep 163779 = 245669) B245669
theorem B163795 : Blo 159796 163795 := bstep (se 1 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 163795 = 245693) B245693
theorem B458723 : Blo 159796 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B360449 : Blo 159796 360449 := bstep (se 2 (by rfl) ⟨135168, by rfl⟩ : syracuseStep 360449 = 270337) B270337
theorem B360665 : Blo 159796 360665 := bstep (se 2 (by rfl) ⟨135249, by rfl⟩ : syracuseStep 360665 = 270499) B270499
theorem B360755 : Blo 159796 360755 := bstep (se 1 (by rfl) ⟨270566, by rfl⟩ : syracuseStep 360755 = 541133) B541133
theorem B360791 : Blo 159796 360791 := bstep (se 1 (by rfl) ⟨270593, by rfl⟩ : syracuseStep 360791 = 541187) B541187
theorem B360971 : Blo 159796 360971 := bstep (se 1 (by rfl) ⟨270728, by rfl⟩ : syracuseStep 360971 = 541457) B541457
theorem B361025 : Blo 159796 361025 := bstep (se 2 (by rfl) ⟨135384, by rfl⟩ : syracuseStep 361025 = 270769) B270769
theorem B1114717 : Blo 159796 1114717 := bstep (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) B418019
theorem B361241 : Blo 159796 361241 := bstep (se 2 (by rfl) ⟨135465, by rfl⟩ : syracuseStep 361241 = 270931) B270931
theorem B820043 : Blo 159796 820043 := bstep (se 1 (by rfl) ⟨615032, by rfl⟩ : syracuseStep 820043 = 1230065) B1230065
theorem B361331 : Blo 159796 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B361367 : Blo 159796 361367 := bstep (se 1 (by rfl) ⟨271025, by rfl⟩ : syracuseStep 361367 = 542051) B542051
theorem B230359 : Blo 159796 230359 := bstep (se 1 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 230359 = 345539) B345539
theorem B361547 : Blo 159796 361547 := bstep (se 1 (by rfl) ⟨271160, by rfl⟩ : syracuseStep 361547 = 542321) B542321
theorem B1213541 : Blo 159796 1213541 := bstep (se 4 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 1213541 = 227539) B227539
theorem B361601 : Blo 159796 361601 := bstep (se 2 (by rfl) ⟨135600, by rfl⟩ : syracuseStep 361601 = 271201) B271201
theorem B165035 : Blo 159796 165035 := bstep (se 1 (by rfl) ⟨123776, by rfl⟩ : syracuseStep 165035 = 247553) B247553
theorem B394433 : Blo 159796 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B361817 : Blo 159796 361817 := bstep (se 2 (by rfl) ⟨135681, by rfl⟩ : syracuseStep 361817 = 271363) B271363
theorem B361907 : Blo 159796 361907 := bstep (se 1 (by rfl) ⟨271430, by rfl⟩ : syracuseStep 361907 = 542861) B542861
theorem B361943 : Blo 159796 361943 := bstep (se 1 (by rfl) ⟨271457, by rfl⟩ : syracuseStep 361943 = 542915) B542915
theorem B1214027 : Blo 159796 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B919133 : Blo 159796 919133 := bstep (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) B344675
theorem B689795 : Blo 159796 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B362123 : Blo 159796 362123 := bstep (se 1 (by rfl) ⟨271592, by rfl⟩ : syracuseStep 362123 = 543185) B543185
theorem B362177 : Blo 159796 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B165719 : Blo 159796 165719 := bstep (se 1 (by rfl) ⟨124289, by rfl⟩ : syracuseStep 165719 = 248579) B248579
theorem B460637 : Blo 159796 460637 := bstep (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) B172739
theorem B362393 : Blo 159796 362393 := bstep (se 2 (by rfl) ⟨135897, by rfl⟩ : syracuseStep 362393 = 271795) B271795
theorem B329687 : Blo 159796 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B362483 : Blo 159796 362483 := bstep (se 1 (by rfl) ⟨271862, by rfl⟩ : syracuseStep 362483 = 543725) B543725
theorem B362519 : Blo 159796 362519 := bstep (se 1 (by rfl) ⟨271889, by rfl⟩ : syracuseStep 362519 = 543779) B543779
theorem B460865 : Blo 159796 460865 := bstep (se 2 (by rfl) ⟨172824, by rfl⟩ : syracuseStep 460865 = 345649) B345649
theorem B3967127 : Blo 159796 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B362699 : Blo 159796 362699 := bstep (se 1 (by rfl) ⟨272024, by rfl⟩ : syracuseStep 362699 = 544049) B544049
theorem B362753 : Blo 159796 362753 := bstep (se 2 (by rfl) ⟨136032, by rfl⟩ : syracuseStep 362753 = 272065) B272065
theorem B330059 : Blo 159796 330059 := bstep (se 1 (by rfl) ⟨247544, by rfl⟩ : syracuseStep 330059 = 495089) B495089
theorem B461207 : Blo 159796 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B1182131 : Blo 159796 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B362969 : Blo 159796 362969 := bstep (se 2 (by rfl) ⟨136113, by rfl⟩ : syracuseStep 362969 = 272227) B272227
theorem B363059 : Blo 159796 363059 := bstep (se 1 (by rfl) ⟨272294, by rfl⟩ : syracuseStep 363059 = 544589) B544589
theorem B821825 : Blo 159796 821825 := bstep (se 2 (by rfl) ⟨308184, by rfl⟩ : syracuseStep 821825 = 616369) B616369
theorem B363095 : Blo 159796 363095 := bstep (se 1 (by rfl) ⟨272321, by rfl⟩ : syracuseStep 363095 = 544643) B544643
theorem B363275 : Blo 159796 363275 := bstep (se 1 (by rfl) ⟨272456, by rfl⟩ : syracuseStep 363275 = 544913) B544913
theorem B461591 : Blo 159796 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B363329 : Blo 159796 363329 := bstep (se 2 (by rfl) ⟨136248, by rfl⟩ : syracuseStep 363329 = 272497) B272497
theorem B953153 : Blo 159796 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B625553 : Blo 159796 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B232409 : Blo 159796 232409 := bstep (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) B174307
theorem B363545 : Blo 159796 363545 := bstep (se 2 (by rfl) ⟨136329, by rfl⟩ : syracuseStep 363545 = 272659) B272659
theorem B2755619 : Blo 159796 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B363635 : Blo 159796 363635 := bstep (se 1 (by rfl) ⟨272726, by rfl⟩ : syracuseStep 363635 = 545453) B545453
theorem B363671 : Blo 159796 363671 := bstep (se 1 (by rfl) ⟨272753, by rfl⟩ : syracuseStep 363671 = 545507) B545507
theorem B363851 : Blo 159796 363851 := bstep (se 1 (by rfl) ⟨272888, by rfl⟩ : syracuseStep 363851 = 545777) B545777
theorem B363905 : Blo 159796 363905 := bstep (se 2 (by rfl) ⟨136464, by rfl⟩ : syracuseStep 363905 = 272929) B272929
theorem B233047 : Blo 159796 233047 := bstep (se 1 (by rfl) ⟨174785, by rfl⟩ : syracuseStep 233047 = 349571) B349571
theorem B364121 : Blo 159796 364121 := bstep (se 2 (by rfl) ⟨136545, by rfl⟩ : syracuseStep 364121 = 273091) B273091
theorem B364211 : Blo 159796 364211 := bstep (se 1 (by rfl) ⟨273158, by rfl⟩ : syracuseStep 364211 = 546317) B546317
theorem B364247 : Blo 159796 364247 := bstep (se 1 (by rfl) ⟨273185, by rfl⟩ : syracuseStep 364247 = 546371) B546371
theorem B462667 : Blo 159796 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B364427 : Blo 159796 364427 := bstep (se 1 (by rfl) ⟨273320, by rfl⟩ : syracuseStep 364427 = 546641) B546641
theorem B364481 : Blo 159796 364481 := bstep (se 2 (by rfl) ⟨136680, by rfl⟩ : syracuseStep 364481 = 273361) B273361
theorem B692171 : Blo 159796 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B2920465 : Blo 159796 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B921617 : Blo 159796 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B1118225 : Blo 159796 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B364697 : Blo 159796 364697 := bstep (se 2 (by rfl) ⟨136761, by rfl⟩ : syracuseStep 364697 = 273523) B273523
theorem B364787 : Blo 159796 364787 := bstep (se 1 (by rfl) ⟨273590, by rfl⟩ : syracuseStep 364787 = 547181) B547181
theorem B364823 : Blo 159796 364823 := bstep (se 1 (by rfl) ⟨273617, by rfl⟩ : syracuseStep 364823 = 547235) B547235
theorem B364979 : Blo 159796 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B365003 : Blo 159796 365003 := bstep (se 1 (by rfl) ⟨273752, by rfl⟩ : syracuseStep 365003 = 547505) B547505
theorem B823769 : Blo 159796 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B365057 : Blo 159796 365057 := bstep (se 2 (by rfl) ⟨136896, by rfl⟩ : syracuseStep 365057 = 273793) B273793
theorem B463553 : Blo 159796 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B365273 : Blo 159796 365273 := bstep (se 2 (by rfl) ⟨136977, by rfl⟩ : syracuseStep 365273 = 273955) B273955
theorem B365363 : Blo 159796 365363 := bstep (se 1 (by rfl) ⟨274022, by rfl⟩ : syracuseStep 365363 = 548045) B548045
theorem B365399 : Blo 159796 365399 := bstep (se 1 (by rfl) ⟨274049, by rfl⟩ : syracuseStep 365399 = 548099) B548099
theorem B693143 : Blo 159796 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B365579 : Blo 159796 365579 := bstep (se 1 (by rfl) ⟨274184, by rfl⟩ : syracuseStep 365579 = 548369) B548369
theorem B365633 : Blo 159796 365633 := bstep (se 2 (by rfl) ⟨137112, by rfl⟩ : syracuseStep 365633 = 274225) B274225
theorem B464089 : Blo 159796 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B1381637 : Blo 159796 1381637 := bstep (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) B259057
theorem B365849 : Blo 159796 365849 := bstep (se 2 (by rfl) ⟨137193, by rfl⟩ : syracuseStep 365849 = 274387) B274387
theorem B628019 : Blo 159796 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B365939 : Blo 159796 365939 := bstep (se 1 (by rfl) ⟨274454, by rfl⟩ : syracuseStep 365939 = 548909) B548909
theorem B365975 : Blo 159796 365975 := bstep (se 1 (by rfl) ⟨274481, by rfl⟩ : syracuseStep 365975 = 548963) B548963
theorem B366155 : Blo 159796 366155 := bstep (se 1 (by rfl) ⟨274616, by rfl⟩ : syracuseStep 366155 = 549233) B549233
theorem B366209 : Blo 159796 366209 := bstep (se 2 (by rfl) ⟨137328, by rfl⟩ : syracuseStep 366209 = 274657) B274657
theorem B366425 : Blo 159796 366425 := bstep (se 2 (by rfl) ⟨137409, by rfl⟩ : syracuseStep 366425 = 274819) B274819
theorem B366515 : Blo 159796 366515 := bstep (se 1 (by rfl) ⟨274886, by rfl⟩ : syracuseStep 366515 = 549773) B549773
theorem B366551 : Blo 159796 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B202763 : Blo 159796 202763 := bstep (se 1 (by rfl) ⟨152072, by rfl⟩ : syracuseStep 202763 = 304145) B304145
theorem B923665 : Blo 159796 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B825389 : Blo 159796 825389 := bstep (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) B309521
theorem B366731 : Blo 159796 366731 := bstep (se 1 (by rfl) ⟨275048, by rfl⟩ : syracuseStep 366731 = 550097) B550097
theorem B366785 : Blo 159796 366785 := bstep (se 2 (by rfl) ⟨137544, by rfl⟩ : syracuseStep 366785 = 275089) B275089
theorem B1841453 : Blo 159796 1841453 := bstep (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) B690545
theorem B367001 : Blo 159796 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B1743281 : Blo 159796 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B367091 : Blo 159796 367091 := bstep (se 1 (by rfl) ⟨275318, by rfl⟩ : syracuseStep 367091 = 550637) B550637
theorem B367127 : Blo 159796 367127 := bstep (se 1 (by rfl) ⟨275345, by rfl⟩ : syracuseStep 367127 = 550691) B550691
theorem B203467 : Blo 159796 203467 := bstep (se 1 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 203467 = 305201) B305201
theorem B367307 : Blo 159796 367307 := bstep (se 1 (by rfl) ⟨275480, by rfl⟩ : syracuseStep 367307 = 550961) B550961
theorem B367361 : Blo 159796 367361 := bstep (se 2 (by rfl) ⟨137760, by rfl⟩ : syracuseStep 367361 = 275521) B275521
theorem B1219373 : Blo 159796 1219373 := bstep (se 3 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 1219373 = 457265) B457265
theorem B3054401 : Blo 159796 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B1317707 : Blo 159796 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B203735 : Blo 159796 203735 := bstep (se 1 (by rfl) ⟨152801, by rfl⟩ : syracuseStep 203735 = 305603) B305603
theorem B367577 : Blo 159796 367577 := bstep (se 2 (by rfl) ⟨137841, by rfl⟩ : syracuseStep 367577 = 275683) B275683
theorem B433117 : Blo 159796 433117 := bstep (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) B162419
theorem B367667 : Blo 159796 367667 := bstep (se 1 (by rfl) ⟨275750, by rfl⟩ : syracuseStep 367667 = 551501) B551501
theorem B2333771 : Blo 159796 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B367703 : Blo 159796 367703 := bstep (se 1 (by rfl) ⟨275777, by rfl⟩ : syracuseStep 367703 = 551555) B551555
theorem B466013 : Blo 159796 466013 := bstep (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) B174755
theorem B367883 : Blo 159796 367883 := bstep (se 1 (by rfl) ⟨275912, by rfl⟩ : syracuseStep 367883 = 551825) B551825
theorem B695603 : Blo 159796 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B367937 : Blo 159796 367937 := bstep (se 2 (by rfl) ⟨137976, by rfl⟩ : syracuseStep 367937 = 275953) B275953
theorem B663005 : Blo 159796 663005 := bstep (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) B248627
theorem B368153 : Blo 159796 368153 := bstep (se 2 (by rfl) ⟨138057, by rfl⟩ : syracuseStep 368153 = 276115) B276115
theorem B368243 : Blo 159796 368243 := bstep (se 1 (by rfl) ⟨276182, by rfl⟩ : syracuseStep 368243 = 552365) B552365
theorem B204439 : Blo 159796 204439 := bstep (se 1 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 204439 = 306659) B306659
theorem B368279 : Blo 159796 368279 := bstep (se 1 (by rfl) ⟨276209, by rfl⟩ : syracuseStep 368279 = 552419) B552419
theorem B270155 : Blo 159796 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B368459 : Blo 159796 368459 := bstep (se 1 (by rfl) ⟨276344, by rfl⟩ : syracuseStep 368459 = 552689) B552689
theorem B368513 : Blo 159796 368513 := bstep (se 2 (by rfl) ⟨138192, by rfl⟩ : syracuseStep 368513 = 276385) B276385
theorem B270283 : Blo 159796 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B270425 : Blo 159796 270425 := bstep (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) B202819
theorem B270553 : Blo 159796 270553 := bstep (se 2 (by rfl) ⟨101457, by rfl⟩ : syracuseStep 270553 = 202915) B202915
theorem B271127 : Blo 159796 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B1385261 : Blo 159796 1385261 := bstep (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) B519473
theorem B992101 : Blo 159796 992101 := bstep (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) B186019
theorem B271255 : Blo 159796 271255 := bstep (se 1 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 271255 = 406883) B406883
theorem B697517 : Blo 159796 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B1156301 : Blo 159796 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B206155 : Blo 159796 206155 := bstep (se 1 (by rfl) ⟨154616, by rfl⟩ : syracuseStep 206155 = 309233) B309233
theorem B173399 : Blo 159796 173399 := bstep (se 1 (by rfl) ⟨130049, by rfl⟩ : syracuseStep 173399 = 260099) B260099
theorem B173431 : Blo 159796 173431 := bstep (se 1 (by rfl) ⟨130073, by rfl⟩ : syracuseStep 173431 = 260147) B260147
theorem B1156531 : Blo 159796 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B697859 : Blo 159796 697859 := bstep (se 1 (by rfl) ⟨523394, by rfl⟩ : syracuseStep 697859 = 1046789) B1046789
theorem B271883 : Blo 159796 271883 := bstep (se 1 (by rfl) ⟨203912, by rfl⟩ : syracuseStep 271883 = 407825) B407825
theorem B304715 : Blo 159796 304715 := bstep (se 1 (by rfl) ⟨228536, by rfl⟩ : syracuseStep 304715 = 457073) B457073
theorem B272011 : Blo 159796 272011 := bstep (se 1 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 272011 = 408017) B408017
theorem B435863 : Blo 159796 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B927449 : Blo 159796 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B304897 : Blo 159796 304897 := bstep (se 2 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 304897 = 228673) B228673
theorem B272153 : Blo 159796 272153 := bstep (se 2 (by rfl) ⟨102057, by rfl⟩ : syracuseStep 272153 = 204115) B204115
theorem B2795363 : Blo 159796 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B272281 : Blo 159796 272281 := bstep (se 2 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 272281 = 204211) B204211
theorem B239705 : Blo 159796 239705 := bstep (se 2 (by rfl) ⟨89889, by rfl⟩ : syracuseStep 239705 = 179779) B179779
theorem B1255601 : Blo 159796 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B305345 : Blo 159796 305345 := bstep (se 2 (by rfl) ⟨114504, by rfl⟩ : syracuseStep 305345 = 229009) B229009
theorem B239819 : Blo 159796 239819 := bstep (se 1 (by rfl) ⟨179864, by rfl⟩ : syracuseStep 239819 = 359729) B359729
theorem B239831 : Blo 159796 239831 := bstep (se 1 (by rfl) ⟨179873, by rfl⟩ : syracuseStep 239831 = 359747) B359747
theorem B207127 : Blo 159796 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B239897 : Blo 159796 239897 := bstep (se 2 (by rfl) ⟨89961, by rfl⟩ : syracuseStep 239897 = 179923) B179923
theorem B1583425 : Blo 159796 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B240011 : Blo 159796 240011 := bstep (se 1 (by rfl) ⟨180008, by rfl⟩ : syracuseStep 240011 = 360017) B360017
theorem B240023 : Blo 159796 240023 := bstep (se 1 (by rfl) ⟨180017, by rfl⟩ : syracuseStep 240023 = 360035) B360035
theorem B272855 : Blo 159796 272855 := bstep (se 1 (by rfl) ⟨204641, by rfl⟩ : syracuseStep 272855 = 409283) B409283
theorem B240089 : Blo 159796 240089 := bstep (se 2 (by rfl) ⟨90033, by rfl⟩ : syracuseStep 240089 = 180067) B180067
theorem B305687 : Blo 159796 305687 := bstep (se 1 (by rfl) ⟨229265, by rfl⟩ : syracuseStep 305687 = 458531) B458531
theorem B1878563 : Blo 159796 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B240203 : Blo 159796 240203 := bstep (se 1 (by rfl) ⟨180152, by rfl⟩ : syracuseStep 240203 = 360305) B360305
theorem B240215 : Blo 159796 240215 := bstep (se 1 (by rfl) ⟨180161, by rfl⟩ : syracuseStep 240215 = 360323) B360323
theorem B272983 : Blo 159796 272983 := bstep (se 1 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 272983 = 409475) B409475
theorem B469597 : Blo 159796 469597 := bstep (se 3 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 469597 = 176099) B176099
theorem B1223261 : Blo 159796 1223261 := bstep (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) B458723
theorem B240281 : Blo 159796 240281 := bstep (se 2 (by rfl) ⟨90105, by rfl⟩ : syracuseStep 240281 = 180211) B180211
theorem B240395 : Blo 159796 240395 := bstep (se 1 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 240395 = 360593) B360593
theorem B240407 : Blo 159796 240407 := bstep (se 1 (by rfl) ⟨180305, by rfl⟩ : syracuseStep 240407 = 360611) B360611
theorem B240473 : Blo 159796 240473 := bstep (se 2 (by rfl) ⟨90177, by rfl⟩ : syracuseStep 240473 = 180355) B180355
theorem B1321859 : Blo 159796 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B4107185 : Blo 159796 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B240587 : Blo 159796 240587 := bstep (se 1 (by rfl) ⟨180440, by rfl⟩ : syracuseStep 240587 = 360881) B360881
theorem B240599 : Blo 159796 240599 := bstep (se 1 (by rfl) ⟨180449, by rfl⟩ : syracuseStep 240599 = 360899) B360899
theorem B240665 : Blo 159796 240665 := bstep (se 2 (by rfl) ⟨90249, by rfl⟩ : syracuseStep 240665 = 180499) B180499
theorem B1387651 : Blo 159796 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B240779 : Blo 159796 240779 := bstep (se 1 (by rfl) ⟨180584, by rfl⟩ : syracuseStep 240779 = 361169) B361169
theorem B240791 : Blo 159796 240791 := bstep (se 1 (by rfl) ⟨180593, by rfl⟩ : syracuseStep 240791 = 361187) B361187
theorem B732311 : Blo 159796 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B306355 : Blo 159796 306355 := bstep (se 1 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 306355 = 459533) B459533
theorem B273611 : Blo 159796 273611 := bstep (se 1 (by rfl) ⟨205208, by rfl⟩ : syracuseStep 273611 = 410417) B410417
theorem B240857 : Blo 159796 240857 := bstep (se 2 (by rfl) ⟨90321, by rfl⟩ : syracuseStep 240857 = 180643) B180643
theorem B240971 : Blo 159796 240971 := bstep (se 1 (by rfl) ⟨180728, by rfl⟩ : syracuseStep 240971 = 361457) B361457
theorem B273739 : Blo 159796 273739 := bstep (se 1 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 273739 = 410609) B410609
theorem B240983 : Blo 159796 240983 := bstep (se 1 (by rfl) ⟨180737, by rfl⟩ : syracuseStep 240983 = 361475) B361475
theorem B241049 : Blo 159796 241049 := bstep (se 2 (by rfl) ⟨90393, by rfl⟩ : syracuseStep 241049 = 180787) B180787
theorem B404939 : Blo 159796 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B273881 : Blo 159796 273881 := bstep (se 2 (by rfl) ⟨102705, by rfl⟩ : syracuseStep 273881 = 205411) B205411
theorem B241163 : Blo 159796 241163 := bstep (se 1 (by rfl) ⟨180872, by rfl⟩ : syracuseStep 241163 = 361745) B361745
theorem B241175 : Blo 159796 241175 := bstep (se 1 (by rfl) ⟨180881, by rfl⟩ : syracuseStep 241175 = 361763) B361763
theorem B503347 : Blo 159796 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B241241 : Blo 159796 241241 := bstep (se 2 (by rfl) ⟨90465, by rfl⟩ : syracuseStep 241241 = 180931) B180931
theorem B274009 : Blo 159796 274009 := bstep (se 2 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 274009 = 205507) B205507
theorem B306803 : Blo 159796 306803 := bstep (se 1 (by rfl) ⟨230102, by rfl⟩ : syracuseStep 306803 = 460205) B460205
theorem B306841 : Blo 159796 306841 := bstep (se 2 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 306841 = 230131) B230131
theorem B241355 : Blo 159796 241355 := bstep (se 1 (by rfl) ⟨181016, by rfl⟩ : syracuseStep 241355 = 362033) B362033
theorem B241367 : Blo 159796 241367 := bstep (se 1 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 241367 = 362051) B362051
theorem B437981 : Blo 159796 437981 := bstep (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) B164243
theorem B241433 : Blo 159796 241433 := bstep (se 2 (by rfl) ⟨90537, by rfl⟩ : syracuseStep 241433 = 181075) B181075
theorem B274315 : Blo 159796 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B241547 : Blo 159796 241547 := bstep (se 1 (by rfl) ⟨181160, by rfl⟩ : syracuseStep 241547 = 362321) B362321
theorem B241559 : Blo 159796 241559 := bstep (se 1 (by rfl) ⟨181169, by rfl⟩ : syracuseStep 241559 = 362339) B362339
theorem B241625 : Blo 159796 241625 := bstep (se 2 (by rfl) ⟨90609, by rfl⟩ : syracuseStep 241625 = 181219) B181219
theorem B1388609 : Blo 159796 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B241739 : Blo 159796 241739 := bstep (se 1 (by rfl) ⟨181304, by rfl⟩ : syracuseStep 241739 = 362609) B362609
theorem B241751 : Blo 159796 241751 := bstep (se 1 (by rfl) ⟨181313, by rfl⟩ : syracuseStep 241751 = 362627) B362627
theorem B307289 : Blo 159796 307289 := bstep (se 2 (by rfl) ⟨115233, by rfl⟩ : syracuseStep 307289 = 230467) B230467
theorem B274583 : Blo 159796 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B241817 : Blo 159796 241817 := bstep (se 2 (by rfl) ⟨90681, by rfl⟩ : syracuseStep 241817 = 181363) B181363
theorem B241931 : Blo 159796 241931 := bstep (se 1 (by rfl) ⟨181448, by rfl⟩ : syracuseStep 241931 = 362897) B362897
theorem B241943 : Blo 159796 241943 := bstep (se 1 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 241943 = 362915) B362915
theorem B274711 : Blo 159796 274711 := bstep (se 1 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 274711 = 412067) B412067
theorem B930113 : Blo 159796 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B242009 : Blo 159796 242009 := bstep (se 2 (by rfl) ⟨90753, by rfl⟩ : syracuseStep 242009 = 181507) B181507
theorem B373081 : Blo 159796 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B405911 : Blo 159796 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B242123 : Blo 159796 242123 := bstep (se 1 (by rfl) ⟨181592, by rfl⟩ : syracuseStep 242123 = 363185) B363185
theorem B242135 : Blo 159796 242135 := bstep (se 1 (by rfl) ⟨181601, by rfl⟩ : syracuseStep 242135 = 363203) B363203
theorem B242201 : Blo 159796 242201 := bstep (se 2 (by rfl) ⟨90825, by rfl⟩ : syracuseStep 242201 = 181651) B181651
theorem B242315 : Blo 159796 242315 := bstep (se 1 (by rfl) ⟨181736, by rfl⟩ : syracuseStep 242315 = 363473) B363473
theorem B242327 : Blo 159796 242327 := bstep (se 1 (by rfl) ⟨181745, by rfl⟩ : syracuseStep 242327 = 363491) B363491
theorem B242393 : Blo 159796 242393 := bstep (se 2 (by rfl) ⟨90897, by rfl⟩ : syracuseStep 242393 = 181795) B181795
theorem B308033 : Blo 159796 308033 := bstep (se 2 (by rfl) ⟨115512, by rfl⟩ : syracuseStep 308033 = 231025) B231025
theorem B242507 : Blo 159796 242507 := bstep (se 1 (by rfl) ⟨181880, by rfl⟩ : syracuseStep 242507 = 363761) B363761
theorem B242519 : Blo 159796 242519 := bstep (se 1 (by rfl) ⟨181889, by rfl⟩ : syracuseStep 242519 = 363779) B363779
theorem B275339 : Blo 159796 275339 := bstep (se 1 (by rfl) ⟨206504, by rfl⟩ : syracuseStep 275339 = 413009) B413009
theorem B242585 : Blo 159796 242585 := bstep (se 2 (by rfl) ⟨90969, by rfl⟩ : syracuseStep 242585 = 181939) B181939
theorem B865241 : Blo 159796 865241 := bstep (se 2 (by rfl) ⟨324465, by rfl⟩ : syracuseStep 865241 = 648931) B648931
theorem B242699 : Blo 159796 242699 := bstep (se 1 (by rfl) ⟨182024, by rfl⟩ : syracuseStep 242699 = 364049) B364049
theorem B275467 : Blo 159796 275467 := bstep (se 1 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 275467 = 413201) B413201
theorem B242711 : Blo 159796 242711 := bstep (se 1 (by rfl) ⟨182033, by rfl⟩ : syracuseStep 242711 = 364067) B364067
theorem B406579 : Blo 159796 406579 := bstep (se 1 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 406579 = 609869) B609869
theorem B308299 : Blo 159796 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B242777 : Blo 159796 242777 := bstep (se 2 (by rfl) ⟨91041, by rfl⟩ : syracuseStep 242777 = 182083) B182083
theorem B275609 : Blo 159796 275609 := bstep (se 2 (by rfl) ⟨103353, by rfl⟩ : syracuseStep 275609 = 206707) B206707
theorem B406721 : Blo 159796 406721 := bstep (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) B305041
theorem B242891 : Blo 159796 242891 := bstep (se 1 (by rfl) ⟨182168, by rfl⟩ : syracuseStep 242891 = 364337) B364337
theorem B242903 : Blo 159796 242903 := bstep (se 1 (by rfl) ⟨182177, by rfl⟩ : syracuseStep 242903 = 364355) B364355
theorem B242969 : Blo 159796 242969 := bstep (se 2 (by rfl) ⟨91113, by rfl⟩ : syracuseStep 242969 = 182227) B182227
theorem B275737 : Blo 159796 275737 := bstep (se 2 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 275737 = 206803) B206803
theorem B1160513 : Blo 159796 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B243083 : Blo 159796 243083 := bstep (se 1 (by rfl) ⟨182312, by rfl⟩ : syracuseStep 243083 = 364625) B364625
theorem B243095 : Blo 159796 243095 := bstep (se 1 (by rfl) ⟨182321, by rfl⟩ : syracuseStep 243095 = 364643) B364643
theorem B243161 : Blo 159796 243161 := bstep (se 2 (by rfl) ⟨91185, by rfl⟩ : syracuseStep 243161 = 182371) B182371
theorem B308747 : Blo 159796 308747 := bstep (se 1 (by rfl) ⟨231560, by rfl⟩ : syracuseStep 308747 = 463121) B463121
theorem B243275 : Blo 159796 243275 := bstep (se 1 (by rfl) ⟨182456, by rfl⟩ : syracuseStep 243275 = 364913) B364913
theorem B243287 : Blo 159796 243287 := bstep (se 1 (by rfl) ⟨182465, by rfl⟩ : syracuseStep 243287 = 364931) B364931
theorem B11417219 : Blo 159796 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1881731 : Blo 159796 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B243353 : Blo 159796 243353 := bstep (se 2 (by rfl) ⟨91257, by rfl⟩ : syracuseStep 243353 = 182515) B182515
theorem B2733749 : Blo 159796 2733749 := bstep (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) B256289
theorem B308929 : Blo 159796 308929 := bstep (se 2 (by rfl) ⟨115848, by rfl⟩ : syracuseStep 308929 = 231697) B231697
theorem B243467 : Blo 159796 243467 := bstep (se 1 (by rfl) ⟨182600, by rfl⟩ : syracuseStep 243467 = 365201) B365201
theorem B243479 : Blo 159796 243479 := bstep (se 1 (by rfl) ⟨182609, by rfl⟩ : syracuseStep 243479 = 365219) B365219
theorem B276311 : Blo 159796 276311 := bstep (se 1 (by rfl) ⟨207233, by rfl⟩ : syracuseStep 276311 = 414467) B414467
theorem B243545 : Blo 159796 243545 := bstep (se 2 (by rfl) ⟨91329, by rfl⟩ : syracuseStep 243545 = 182659) B182659
theorem B243659 : Blo 159796 243659 := bstep (se 1 (by rfl) ⟨182744, by rfl⟩ : syracuseStep 243659 = 365489) B365489
theorem B243671 : Blo 159796 243671 := bstep (se 1 (by rfl) ⟨182753, by rfl⟩ : syracuseStep 243671 = 365507) B365507
theorem B309271 : Blo 159796 309271 := bstep (se 1 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 309271 = 463907) B463907
theorem B243737 : Blo 159796 243737 := bstep (se 2 (by rfl) ⟨91401, by rfl⟩ : syracuseStep 243737 = 182803) B182803
theorem B243851 : Blo 159796 243851 := bstep (se 1 (by rfl) ⟨182888, by rfl⟩ : syracuseStep 243851 = 365777) B365777
theorem B243863 : Blo 159796 243863 := bstep (se 1 (by rfl) ⟨182897, by rfl⟩ : syracuseStep 243863 = 365795) B365795
theorem B243929 : Blo 159796 243929 := bstep (se 2 (by rfl) ⟨91473, by rfl⟩ : syracuseStep 243929 = 182947) B182947
theorem B309491 : Blo 159796 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B244043 : Blo 159796 244043 := bstep (se 1 (by rfl) ⟨183032, by rfl⟩ : syracuseStep 244043 = 366065) B366065
theorem B244055 : Blo 159796 244055 := bstep (se 1 (by rfl) ⟨183041, by rfl⟩ : syracuseStep 244055 = 366083) B366083
theorem B244121 : Blo 159796 244121 := bstep (se 2 (by rfl) ⟨91545, by rfl⟩ : syracuseStep 244121 = 183091) B183091
theorem B1325489 : Blo 159796 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B407987 : Blo 159796 407987 := bstep (se 1 (by rfl) ⟨305990, by rfl⟩ : syracuseStep 407987 = 611981) B611981
theorem B309719 : Blo 159796 309719 := bstep (se 1 (by rfl) ⟨232289, by rfl⟩ : syracuseStep 309719 = 464579) B464579
theorem B244235 : Blo 159796 244235 := bstep (se 1 (by rfl) ⟨183176, by rfl⟩ : syracuseStep 244235 = 366353) B366353
theorem B244247 : Blo 159796 244247 := bstep (se 1 (by rfl) ⟨183185, by rfl⟩ : syracuseStep 244247 = 366371) B366371
theorem B932417 : Blo 159796 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B244313 : Blo 159796 244313 := bstep (se 2 (by rfl) ⟨91617, by rfl⟩ : syracuseStep 244313 = 183235) B183235
theorem B244427 : Blo 159796 244427 := bstep (se 1 (by rfl) ⟨183320, by rfl⟩ : syracuseStep 244427 = 366641) B366641
theorem B244439 : Blo 159796 244439 := bstep (se 1 (by rfl) ⟨183329, by rfl⟩ : syracuseStep 244439 = 366659) B366659
theorem B309977 : Blo 159796 309977 := bstep (se 2 (by rfl) ⟨116241, by rfl⟩ : syracuseStep 309977 = 232483) B232483
theorem B244505 : Blo 159796 244505 := bstep (se 2 (by rfl) ⟨91689, by rfl⟩ : syracuseStep 244505 = 183379) B183379
theorem B441139 : Blo 159796 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B244619 : Blo 159796 244619 := bstep (se 1 (by rfl) ⟨183464, by rfl⟩ : syracuseStep 244619 = 366929) B366929
theorem B244631 : Blo 159796 244631 := bstep (se 1 (by rfl) ⟨183473, by rfl⟩ : syracuseStep 244631 = 366947) B366947
theorem B408523 : Blo 159796 408523 := bstep (se 1 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 408523 = 612785) B612785
theorem B244697 : Blo 159796 244697 := bstep (se 2 (by rfl) ⟨91761, by rfl⟩ : syracuseStep 244697 = 183523) B183523
theorem B244811 : Blo 159796 244811 := bstep (se 1 (by rfl) ⟨183608, by rfl⟩ : syracuseStep 244811 = 367217) B367217
theorem B244823 : Blo 159796 244823 := bstep (se 1 (by rfl) ⟨183617, by rfl⟩ : syracuseStep 244823 = 367235) B367235
theorem B408665 : Blo 159796 408665 := bstep (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) B306499
theorem B310387 : Blo 159796 310387 := bstep (se 1 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 310387 = 465581) B465581
theorem B244889 : Blo 159796 244889 := bstep (se 2 (by rfl) ⟨91833, by rfl⟩ : syracuseStep 244889 = 183667) B183667
theorem B245003 : Blo 159796 245003 := bstep (se 1 (by rfl) ⟨183752, by rfl⟩ : syracuseStep 245003 = 367505) B367505
theorem B245015 : Blo 159796 245015 := bstep (se 1 (by rfl) ⟨183761, by rfl⟩ : syracuseStep 245015 = 367523) B367523
theorem B1326401 : Blo 159796 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B245081 : Blo 159796 245081 := bstep (se 2 (by rfl) ⟨91905, by rfl⟩ : syracuseStep 245081 = 183811) B183811
theorem B540107 : Blo 159796 540107 := bstep (se 1 (by rfl) ⟨405080, by rfl⟩ : syracuseStep 540107 = 810161) B810161
theorem B245195 : Blo 159796 245195 := bstep (se 1 (by rfl) ⟨183896, by rfl⟩ : syracuseStep 245195 = 367793) B367793
theorem B245207 : Blo 159796 245207 := bstep (se 1 (by rfl) ⟨183905, by rfl⟩ : syracuseStep 245207 = 367811) B367811
theorem B245273 : Blo 159796 245273 := bstep (se 2 (by rfl) ⟨91977, by rfl⟩ : syracuseStep 245273 = 183955) B183955
theorem B310873 : Blo 159796 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B179851 : Blo 159796 179851 := bstep (se 1 (by rfl) ⟨134888, by rfl⟩ : syracuseStep 179851 = 269777) B269777
theorem B245387 : Blo 159796 245387 := bstep (se 1 (by rfl) ⟨184040, by rfl⟩ : syracuseStep 245387 = 368081) B368081
theorem B245399 : Blo 159796 245399 := bstep (se 1 (by rfl) ⟨184049, by rfl⟩ : syracuseStep 245399 = 368099) B368099
theorem B605875 : Blo 159796 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B540377 : Blo 159796 540377 := bstep (se 2 (by rfl) ⟨202641, by rfl⟩ : syracuseStep 540377 = 405283) B405283
theorem B343769 : Blo 159796 343769 := bstep (se 2 (by rfl) ⟨128913, by rfl⟩ : syracuseStep 343769 = 257827) B257827
theorem B245465 : Blo 159796 245465 := bstep (se 2 (by rfl) ⟨92049, by rfl⟩ : syracuseStep 245465 = 184099) B184099
theorem B179959 : Blo 159796 179959 := bstep (se 1 (by rfl) ⟨134969, by rfl⟩ : syracuseStep 179959 = 269939) B269939
theorem B245579 : Blo 159796 245579 := bstep (se 1 (by rfl) ⟨184184, by rfl⟩ : syracuseStep 245579 = 368369) B368369
theorem B245591 : Blo 159796 245591 := bstep (se 1 (by rfl) ⟨184193, by rfl⟩ : syracuseStep 245591 = 368387) B368387
theorem B2768741 : Blo 159796 2768741 := bstep (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) B519139
theorem B409495 : Blo 159796 409495 := bstep (se 1 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 409495 = 614243) B614243
theorem B245657 : Blo 159796 245657 := bstep (se 2 (by rfl) ⟨92121, by rfl⟩ : syracuseStep 245657 = 184243) B184243
theorem B180139 : Blo 159796 180139 := bstep (se 1 (by rfl) ⟨135104, by rfl⟩ : syracuseStep 180139 = 270209) B270209
theorem B2310065 : Blo 159796 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B180247 : Blo 159796 180247 := bstep (se 1 (by rfl) ⟨135185, by rfl⟩ : syracuseStep 180247 = 270371) B270371
theorem B344179 : Blo 159796 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B180427 : Blo 159796 180427 := bstep (se 1 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 180427 = 270641) B270641
theorem B180535 : Blo 159796 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B409931 : Blo 159796 409931 := bstep (se 1 (by rfl) ⟨307448, by rfl⟩ : syracuseStep 409931 = 614897) B614897
theorem B541079 : Blo 159796 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B344513 : Blo 159796 344513 := bstep (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) B258385
theorem B180715 : Blo 159796 180715 := bstep (se 1 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 180715 = 271073) B271073
theorem B180823 : Blo 159796 180823 := bstep (se 1 (by rfl) ⟨135617, by rfl⟩ : syracuseStep 180823 = 271235) B271235
theorem B410305 : Blo 159796 410305 := bstep (se 2 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 410305 = 307729) B307729
theorem B606923 : Blo 159796 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B181003 : Blo 159796 181003 := bstep (se 1 (by rfl) ⟨135752, by rfl⟩ : syracuseStep 181003 = 271505) B271505
theorem B836369 : Blo 159796 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B181111 : Blo 159796 181111 := bstep (se 1 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 181111 = 271667) B271667
theorem B607121 : Blo 159796 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B541619 : Blo 159796 541619 := bstep (se 1 (by rfl) ⟨406214, by rfl⟩ : syracuseStep 541619 = 812429) B812429
theorem B181291 : Blo 159796 181291 := bstep (se 1 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 181291 = 271937) B271937
theorem B181399 : Blo 159796 181399 := bstep (se 1 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 181399 = 272099) B272099
theorem B345239 : Blo 159796 345239 := bstep (se 1 (by rfl) ⟨258929, by rfl⟩ : syracuseStep 345239 = 517859) B517859
theorem B541889 : Blo 159796 541889 := bstep (se 2 (by rfl) ⟨203208, by rfl⟩ : syracuseStep 541889 = 406417) B406417
theorem B410903 : Blo 159796 410903 := bstep (se 1 (by rfl) ⟨308177, by rfl⟩ : syracuseStep 410903 = 616355) B616355
theorem B181579 : Blo 159796 181579 := bstep (se 1 (by rfl) ⟨136184, by rfl⟩ : syracuseStep 181579 = 272369) B272369
theorem B1230173 : Blo 159796 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B181687 : Blo 159796 181687 := bstep (se 1 (by rfl) ⟨136265, by rfl⟩ : syracuseStep 181687 = 272531) B272531
theorem B706051 : Blo 159796 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B771677 : Blo 159796 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B181867 : Blo 159796 181867 := bstep (se 1 (by rfl) ⟨136400, by rfl⟩ : syracuseStep 181867 = 272801) B272801
theorem B607895 : Blo 159796 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B181975 : Blo 159796 181975 := bstep (se 1 (by rfl) ⟨136481, by rfl⟩ : syracuseStep 181975 = 272963) B272963
theorem B542429 : Blo 159796 542429 := bstep (se 3 (by rfl) ⟨101705, by rfl⟩ : syracuseStep 542429 = 203411) B203411
theorem B1001281 : Blo 159796 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B608093 : Blo 159796 608093 := bstep (se 3 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 608093 = 228035) B228035
theorem B182155 : Blo 159796 182155 := bstep (se 1 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 182155 = 273233) B273233
theorem B182263 : Blo 159796 182263 := bstep (se 1 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 182263 = 273395) B273395
theorem B313345 : Blo 159796 313345 := bstep (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) B235009
theorem B4769813 : Blo 159796 4769813 := bstep (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) B223585
theorem B411713 : Blo 159796 411713 := bstep (se 2 (by rfl) ⟨154392, by rfl⟩ : syracuseStep 411713 = 308785) B308785
theorem B739459 : Blo 159796 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B182443 : Blo 159796 182443 := bstep (se 1 (by rfl) ⟨136832, by rfl⟩ : syracuseStep 182443 = 273665) B273665
theorem B313561 : Blo 159796 313561 := bstep (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) B235171
theorem B182551 : Blo 159796 182551 := bstep (se 1 (by rfl) ⟨136913, by rfl⟩ : syracuseStep 182551 = 273827) B273827
theorem B2083117 : Blo 159796 2083117 := bstep (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) B781169
theorem B2312549 : Blo 159796 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B182731 : Blo 159796 182731 := bstep (se 1 (by rfl) ⟨137048, by rfl⟩ : syracuseStep 182731 = 274097) B274097
theorem B9423373 : Blo 159796 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B182839 : Blo 159796 182839 := bstep (se 1 (by rfl) ⟨137129, by rfl⟩ : syracuseStep 182839 = 274259) B274259
theorem B412249 : Blo 159796 412249 := bstep (se 2 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 412249 = 309187) B309187
theorem B183019 : Blo 159796 183019 := bstep (se 1 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 183019 = 274529) B274529
theorem B215833 : Blo 159796 215833 := bstep (se 2 (by rfl) ⟨80937, by rfl⟩ : syracuseStep 215833 = 161875) B161875
theorem B5327669 : Blo 159796 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B543563 : Blo 159796 543563 := bstep (se 1 (by rfl) ⟨407672, by rfl⟩ : syracuseStep 543563 = 815345) B815345
theorem B183127 : Blo 159796 183127 := bstep (se 1 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 183127 = 274691) B274691
theorem B183307 : Blo 159796 183307 := bstep (se 1 (by rfl) ⟨137480, by rfl⟩ : syracuseStep 183307 = 274961) B274961
theorem B543833 : Blo 159796 543833 := bstep (se 2 (by rfl) ⟨203937, by rfl⟩ : syracuseStep 543833 = 407875) B407875
theorem B183415 : Blo 159796 183415 := bstep (se 1 (by rfl) ⟨137561, by rfl⟩ : syracuseStep 183415 = 275123) B275123
theorem B183595 : Blo 159796 183595 := bstep (se 1 (by rfl) ⟨137696, by rfl⟩ : syracuseStep 183595 = 275393) B275393
theorem B183703 : Blo 159796 183703 := bstep (se 1 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 183703 = 275555) B275555
theorem B347699 : Blo 159796 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B183883 : Blo 159796 183883 := bstep (se 1 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 183883 = 275825) B275825
theorem B413363 : Blo 159796 413363 := bstep (se 1 (by rfl) ⟨310022, by rfl⟩ : syracuseStep 413363 = 620045) B620045
theorem B183991 : Blo 159796 183991 := bstep (se 1 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 183991 = 275987) B275987
theorem B610051 : Blo 159796 610051 := bstep (se 1 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 610051 = 915077) B915077
theorem B544535 : Blo 159796 544535 := bstep (se 1 (by rfl) ⟨408401, by rfl⟩ : syracuseStep 544535 = 816803) B816803
theorem B184171 : Blo 159796 184171 := bstep (se 1 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 184171 = 276257) B276257
theorem B577459 : Blo 159796 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B413657 : Blo 159796 413657 := bstep (se 2 (by rfl) ⟨155121, by rfl⟩ : syracuseStep 413657 = 310243) B310243
theorem B610355 : Blo 159796 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B545075 : Blo 159796 545075 := bstep (se 1 (by rfl) ⟨408806, by rfl⟩ : syracuseStep 545075 = 817613) B817613
theorem B512477 : Blo 159796 512477 := bstep (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) B192179
theorem B545345 : Blo 159796 545345 := bstep (se 2 (by rfl) ⟨204504, by rfl⟩ : syracuseStep 545345 = 409009) B409009
theorem B611009 : Blo 159796 611009 := bstep (se 2 (by rfl) ⟨229128, by rfl⟩ : syracuseStep 611009 = 458257) B458257
theorem B348887 : Blo 159796 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B873433 : Blo 159796 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B1037357 : Blo 159796 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B545885 : Blo 159796 545885 := bstep (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) B204707
theorem B283915 : Blo 159796 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B972107 : Blo 159796 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B186251 : Blo 159796 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B612269 : Blo 159796 612269 := bstep (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) B229601
theorem B579521 : Blo 159796 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B612299 : Blo 159796 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B547019 : Blo 159796 547019 := bstep (se 1 (by rfl) ⟨410264, by rfl⟩ : syracuseStep 547019 = 820529) B820529
theorem B350489 : Blo 159796 350489 := bstep (se 2 (by rfl) ⟨131433, by rfl⟩ : syracuseStep 350489 = 262867) B262867
theorem B1399133 : Blo 159796 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B1169795 : Blo 159796 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B678289 : Blo 159796 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B1038743 : Blo 159796 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B547289 : Blo 159796 547289 := bstep (se 2 (by rfl) ⟨205233, by rfl⟩ : syracuseStep 547289 = 410467) B410467
theorem B1989137 : Blo 159796 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B612953 : Blo 159796 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B875357 : Blo 159796 875357 := bstep (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) B328259
theorem B613271 : Blo 159796 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B1563569 : Blo 159796 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B351371 : Blo 159796 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B547991 : Blo 159796 547991 := bstep (se 1 (by rfl) ⟨410993, by rfl⟩ : syracuseStep 547991 = 821987) B821987
theorem B613939 : Blo 159796 613939 := bstep (se 1 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 613939 = 920909) B920909
theorem B1171037 : Blo 159796 1171037 := bstep (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) B439139
theorem B810647 : Blo 159796 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B548531 : Blo 159796 548531 := bstep (se 1 (by rfl) ⟨411398, by rfl⟩ : syracuseStep 548531 = 822797) B822797
theorem B548801 : Blo 159796 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B581725 : Blo 159796 581725 := bstep (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) B218147
theorem B93184277 : Blo 159796 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B549341 : Blo 159796 549341 := bstep (se 3 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 549341 = 206003) B206003
theorem B615185 : Blo 159796 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B2614133 : Blo 159796 2614133 := bstep (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) B245075
theorem B648343 : Blo 159796 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B746647 : Blo 159796 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B615883 : Blo 159796 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B550475 : Blo 159796 550475 := bstep (se 1 (by rfl) ⟨412856, by rfl⟩ : syracuseStep 550475 = 825713) B825713
theorem B616157 : Blo 159796 616157 := bstep (se 3 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 616157 = 231059) B231059
theorem B550745 : Blo 159796 550745 := bstep (se 2 (by rfl) ⟨206529, by rfl⟩ : syracuseStep 550745 = 413059) B413059
theorem B518039 : Blo 159796 518039 := bstep (se 1 (by rfl) ⟨388529, by rfl⟩ : syracuseStep 518039 = 777059) B777059
theorem B3106997 : Blo 159796 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B1042789 : Blo 159796 1042789 := bstep (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) B195523
theorem B289163 : Blo 159796 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B616855 : Blo 159796 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B551447 : Blo 159796 551447 := bstep (se 1 (by rfl) ⟨413585, by rfl⟩ : syracuseStep 551447 = 827171) B827171
theorem B1469249 : Blo 159796 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B518987 : Blo 159796 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B551987 : Blo 159796 551987 := bstep (se 1 (by rfl) ⟨413990, by rfl⟩ : syracuseStep 551987 = 827981) B827981
theorem B814211 : Blo 159796 814211 := bstep (se 1 (by rfl) ⟨610658, by rfl⟩ : syracuseStep 814211 = 1221317) B1221317
theorem B617645 : Blo 159796 617645 := bstep (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) B231617
theorem B552257 : Blo 159796 552257 := bstep (se 2 (by rfl) ⟨207096, by rfl⟩ : syracuseStep 552257 = 414193) B414193
theorem B650713 : Blo 159796 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B1404377 : Blo 159796 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B519641 : Blo 159796 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B1764899 : Blo 159796 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B749107 : Blo 159796 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B749387 : Blo 159796 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B257879 : Blo 159796 257879 := bstep (se 1 (by rfl) ⟨193409, by rfl⟩ : syracuseStep 257879 = 386819) B386819
theorem B552797 : Blo 159796 552797 := bstep (se 3 (by rfl) ⟨103649, by rfl⟩ : syracuseStep 552797 = 207299) B207299
theorem B258007 : Blo 159796 258007 := bstep (se 1 (by rfl) ⟨193505, by rfl⟩ : syracuseStep 258007 = 387011) B387011
theorem B159799 : Blo 159796 159799 := bstep (se 1 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 159799 = 239699) B239699
theorem B159819 : Blo 159796 159819 := bstep (se 1 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 159819 = 239729) B239729
theorem B159831 : Blo 159796 159831 := bstep (se 1 (by rfl) ⟨119873, by rfl⟩ : syracuseStep 159831 = 239747) B239747
theorem B684121 : Blo 159796 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B159851 : Blo 159796 159851 := bstep (se 1 (by rfl) ⟨119888, by rfl⟩ : syracuseStep 159851 = 239777) B239777
theorem B159863 : Blo 159796 159863 := bstep (se 1 (by rfl) ⟨119897, by rfl⟩ : syracuseStep 159863 = 239795) B239795
theorem B1339523 : Blo 159796 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B159883 : Blo 159796 159883 := bstep (se 1 (by rfl) ⟨119912, by rfl⟩ : syracuseStep 159883 = 239825) B239825
theorem B159895 : Blo 159796 159895 := bstep (se 1 (by rfl) ⟨119921, by rfl⟩ : syracuseStep 159895 = 239843) B239843
theorem B159915 : Blo 159796 159915 := bstep (se 1 (by rfl) ⟨119936, by rfl⟩ : syracuseStep 159915 = 239873) B239873
theorem B159927 : Blo 159796 159927 := bstep (se 1 (by rfl) ⟨119945, by rfl⟩ : syracuseStep 159927 = 239891) B239891
theorem B159947 : Blo 159796 159947 := bstep (se 1 (by rfl) ⟨119960, by rfl⟩ : syracuseStep 159947 = 239921) B239921
theorem B159959 : Blo 159796 159959 := bstep (se 1 (by rfl) ⟨119969, by rfl⟩ : syracuseStep 159959 = 239939) B239939
theorem B192727 : Blo 159796 192727 := bstep (se 1 (by rfl) ⟨144545, by rfl⟩ : syracuseStep 192727 = 289091) B289091
theorem B159979 : Blo 159796 159979 := bstep (se 1 (by rfl) ⟨119984, by rfl⟩ : syracuseStep 159979 = 239969) B239969
theorem B159991 : Blo 159796 159991 := bstep (se 1 (by rfl) ⟨119993, by rfl⟩ : syracuseStep 159991 = 239987) B239987
theorem B160011 : Blo 159796 160011 := bstep (se 1 (by rfl) ⟨120008, by rfl⟩ : syracuseStep 160011 = 240017) B240017
theorem B160023 : Blo 159796 160023 := bstep (se 1 (by rfl) ⟨120017, by rfl⟩ : syracuseStep 160023 = 240035) B240035
theorem B160043 : Blo 159796 160043 := bstep (se 1 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 160043 = 240065) B240065
theorem B520499 : Blo 159796 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B160055 : Blo 159796 160055 := bstep (se 1 (by rfl) ⟨120041, by rfl⟩ : syracuseStep 160055 = 240083) B240083
theorem B160075 : Blo 159796 160075 := bstep (se 1 (by rfl) ⟨120056, by rfl⟩ : syracuseStep 160075 = 240113) B240113
theorem B160087 : Blo 159796 160087 := bstep (se 1 (by rfl) ⟨120065, by rfl⟩ : syracuseStep 160087 = 240131) B240131
theorem B258391 : Blo 159796 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B160107 : Blo 159796 160107 := bstep (se 1 (by rfl) ⟨120080, by rfl⟩ : syracuseStep 160107 = 240161) B240161
theorem B160119 : Blo 159796 160119 := bstep (se 1 (by rfl) ⟨120089, by rfl⟩ : syracuseStep 160119 = 240179) B240179
theorem B160139 : Blo 159796 160139 := bstep (se 1 (by rfl) ⟨120104, by rfl⟩ : syracuseStep 160139 = 240209) B240209
theorem B160151 : Blo 159796 160151 := bstep (se 1 (by rfl) ⟨120113, by rfl⟩ : syracuseStep 160151 = 240227) B240227
theorem B160171 : Blo 159796 160171 := bstep (se 1 (by rfl) ⟨120128, by rfl⟩ : syracuseStep 160171 = 240257) B240257
theorem B520627 : Blo 159796 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B160183 : Blo 159796 160183 := bstep (se 1 (by rfl) ⟨120137, by rfl⟩ : syracuseStep 160183 = 240275) B240275
theorem B160203 : Blo 159796 160203 := bstep (se 1 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 160203 = 240305) B240305
theorem B160215 : Blo 159796 160215 := bstep (se 1 (by rfl) ⟨120161, by rfl⟩ : syracuseStep 160215 = 240323) B240323
theorem B160235 : Blo 159796 160235 := bstep (se 1 (by rfl) ⟨120176, by rfl⟩ : syracuseStep 160235 = 240353) B240353
theorem B160247 : Blo 159796 160247 := bstep (se 1 (by rfl) ⟨120185, by rfl⟩ : syracuseStep 160247 = 240371) B240371
theorem B160267 : Blo 159796 160267 := bstep (se 1 (by rfl) ⟨120200, by rfl⟩ : syracuseStep 160267 = 240401) B240401
theorem B160279 : Blo 159796 160279 := bstep (se 1 (by rfl) ⟨120209, by rfl⟩ : syracuseStep 160279 = 240419) B240419
theorem B160299 : Blo 159796 160299 := bstep (se 1 (by rfl) ⟨120224, by rfl⟩ : syracuseStep 160299 = 240449) B240449
theorem B160311 : Blo 159796 160311 := bstep (se 1 (by rfl) ⟨120233, by rfl⟩ : syracuseStep 160311 = 240467) B240467
theorem B520769 : Blo 159796 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B619073 : Blo 159796 619073 := bstep (se 2 (by rfl) ⟨232152, by rfl⟩ : syracuseStep 619073 = 464305) B464305
theorem B160331 : Blo 159796 160331 := bstep (se 1 (by rfl) ⟨120248, by rfl⟩ : syracuseStep 160331 = 240497) B240497
theorem B160343 : Blo 159796 160343 := bstep (se 1 (by rfl) ⟨120257, by rfl⟩ : syracuseStep 160343 = 240515) B240515
theorem B258647 : Blo 159796 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B160363 : Blo 159796 160363 := bstep (se 1 (by rfl) ⟨120272, by rfl⟩ : syracuseStep 160363 = 240545) B240545
theorem B160375 : Blo 159796 160375 := bstep (se 1 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 160375 = 240563) B240563
theorem B160395 : Blo 159796 160395 := bstep (se 1 (by rfl) ⟨120296, by rfl⟩ : syracuseStep 160395 = 240593) B240593
theorem B160407 : Blo 159796 160407 := bstep (se 1 (by rfl) ⟨120305, by rfl⟩ : syracuseStep 160407 = 240611) B240611
theorem B160427 : Blo 159796 160427 := bstep (se 1 (by rfl) ⟨120320, by rfl⟩ : syracuseStep 160427 = 240641) B240641
theorem B520883 : Blo 159796 520883 := bstep (se 1 (by rfl) ⟨390662, by rfl⟩ : syracuseStep 520883 = 781325) B781325
theorem B160439 : Blo 159796 160439 := bstep (se 1 (by rfl) ⟨120329, by rfl⟩ : syracuseStep 160439 = 240659) B240659
theorem B684737 : Blo 159796 684737 := bstep (se 2 (by rfl) ⟨256776, by rfl⟩ : syracuseStep 684737 = 513553) B513553
theorem B160459 : Blo 159796 160459 := bstep (se 1 (by rfl) ⟨120344, by rfl⟩ : syracuseStep 160459 = 240689) B240689
theorem B160471 : Blo 159796 160471 := bstep (se 1 (by rfl) ⟨120353, by rfl⟩ : syracuseStep 160471 = 240707) B240707
theorem B1372889 : Blo 159796 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B160491 : Blo 159796 160491 := bstep (se 1 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 160491 = 240737) B240737
theorem B160503 : Blo 159796 160503 := bstep (se 1 (by rfl) ⟨120377, by rfl⟩ : syracuseStep 160503 = 240755) B240755
theorem B160523 : Blo 159796 160523 := bstep (se 1 (by rfl) ⟨120392, by rfl⟩ : syracuseStep 160523 = 240785) B240785
theorem B160535 : Blo 159796 160535 := bstep (se 1 (by rfl) ⟨120401, by rfl⟩ : syracuseStep 160535 = 240803) B240803
theorem B160555 : Blo 159796 160555 := bstep (se 1 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 160555 = 240833) B240833
theorem B160567 : Blo 159796 160567 := bstep (se 1 (by rfl) ⟨120425, by rfl⟩ : syracuseStep 160567 = 240851) B240851
theorem B455489 : Blo 159796 455489 := bstep (se 2 (by rfl) ⟨170808, by rfl⟩ : syracuseStep 455489 = 341617) B341617
theorem B160587 : Blo 159796 160587 := bstep (se 1 (by rfl) ⟨120440, by rfl⟩ : syracuseStep 160587 = 240881) B240881
theorem B160599 : Blo 159796 160599 := bstep (se 1 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 160599 = 240899) B240899
theorem B291671 : Blo 159796 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B160619 : Blo 159796 160619 := bstep (se 1 (by rfl) ⟨120464, by rfl⟩ : syracuseStep 160619 = 240929) B240929
theorem B160631 : Blo 159796 160631 := bstep (se 1 (by rfl) ⟨120473, by rfl⟩ : syracuseStep 160631 = 240947) B240947
theorem B160651 : Blo 159796 160651 := bstep (se 1 (by rfl) ⟨120488, by rfl⟩ : syracuseStep 160651 = 240977) B240977
theorem B914327 : Blo 159796 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B160663 : Blo 159796 160663 := bstep (se 1 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 160663 = 240995) B240995
theorem B160683 : Blo 159796 160683 := bstep (se 1 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 160683 = 241025) B241025
theorem B160695 : Blo 159796 160695 := bstep (se 1 (by rfl) ⟨120521, by rfl⟩ : syracuseStep 160695 = 241043) B241043
theorem B160715 : Blo 159796 160715 := bstep (se 1 (by rfl) ⟨120536, by rfl⟩ : syracuseStep 160715 = 241073) B241073
theorem B160727 : Blo 159796 160727 := bstep (se 1 (by rfl) ⟨120545, by rfl⟩ : syracuseStep 160727 = 241091) B241091
theorem B160747 : Blo 159796 160747 := bstep (se 1 (by rfl) ⟨120560, by rfl⟩ : syracuseStep 160747 = 241121) B241121
theorem B160759 : Blo 159796 160759 := bstep (se 1 (by rfl) ⟨120569, by rfl⟩ : syracuseStep 160759 = 241139) B241139
theorem B160779 : Blo 159796 160779 := bstep (se 1 (by rfl) ⟨120584, by rfl⟩ : syracuseStep 160779 = 241169) B241169
theorem B160791 : Blo 159796 160791 := bstep (se 1 (by rfl) ⟨120593, by rfl⟩ : syracuseStep 160791 = 241187) B241187
theorem B160811 : Blo 159796 160811 := bstep (se 1 (by rfl) ⟨120608, by rfl⟩ : syracuseStep 160811 = 241217) B241217
theorem B160823 : Blo 159796 160823 := bstep (se 1 (by rfl) ⟨120617, by rfl⟩ : syracuseStep 160823 = 241235) B241235
theorem B160843 : Blo 159796 160843 := bstep (se 1 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 160843 = 241265) B241265
theorem B160855 : Blo 159796 160855 := bstep (se 1 (by rfl) ⟨120641, by rfl⟩ : syracuseStep 160855 = 241283) B241283
theorem B160875 : Blo 159796 160875 := bstep (se 1 (by rfl) ⟨120656, by rfl⟩ : syracuseStep 160875 = 241313) B241313
theorem B160887 : Blo 159796 160887 := bstep (se 1 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 160887 = 241331) B241331
theorem B160907 : Blo 159796 160907 := bstep (se 1 (by rfl) ⟨120680, by rfl⟩ : syracuseStep 160907 = 241361) B241361
theorem B259211 : Blo 159796 259211 := bstep (se 1 (by rfl) ⟨194408, by rfl⟩ : syracuseStep 259211 = 388817) B388817
theorem B455831 : Blo 159796 455831 := bstep (se 1 (by rfl) ⟨341873, by rfl⟩ : syracuseStep 455831 = 683747) B683747
theorem B160919 : Blo 159796 160919 := bstep (se 1 (by rfl) ⟨120689, by rfl⟩ : syracuseStep 160919 = 241379) B241379
theorem B160939 : Blo 159796 160939 := bstep (se 1 (by rfl) ⟨120704, by rfl⟩ : syracuseStep 160939 = 241409) B241409
theorem B160951 : Blo 159796 160951 := bstep (se 1 (by rfl) ⟨120713, by rfl⟩ : syracuseStep 160951 = 241427) B241427
theorem B160971 : Blo 159796 160971 := bstep (se 1 (by rfl) ⟨120728, by rfl⟩ : syracuseStep 160971 = 241457) B241457
theorem B160983 : Blo 159796 160983 := bstep (se 1 (by rfl) ⟨120737, by rfl⟩ : syracuseStep 160983 = 241475) B241475
theorem B161003 : Blo 159796 161003 := bstep (se 1 (by rfl) ⟨120752, by rfl⟩ : syracuseStep 161003 = 241505) B241505
theorem B161015 : Blo 159796 161015 := bstep (se 1 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 161015 = 241523) B241523
theorem B161035 : Blo 159796 161035 := bstep (se 1 (by rfl) ⟨120776, by rfl⟩ : syracuseStep 161035 = 241553) B241553
theorem B161047 : Blo 159796 161047 := bstep (se 1 (by rfl) ⟨120785, by rfl⟩ : syracuseStep 161047 = 241571) B241571
theorem B161067 : Blo 159796 161067 := bstep (se 1 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 161067 = 241601) B241601
theorem B161079 : Blo 159796 161079 := bstep (se 1 (by rfl) ⟨120809, by rfl⟩ : syracuseStep 161079 = 241619) B241619
theorem B161099 : Blo 159796 161099 := bstep (se 1 (by rfl) ⟨120824, by rfl⟩ : syracuseStep 161099 = 241649) B241649
theorem B161111 : Blo 159796 161111 := bstep (se 1 (by rfl) ⟨120833, by rfl⟩ : syracuseStep 161111 = 241667) B241667
theorem B161131 : Blo 159796 161131 := bstep (se 1 (by rfl) ⟨120848, by rfl⟩ : syracuseStep 161131 = 241697) B241697
theorem B161143 : Blo 159796 161143 := bstep (se 1 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 161143 = 241715) B241715
theorem B161163 : Blo 159796 161163 := bstep (se 1 (by rfl) ⟨120872, by rfl⟩ : syracuseStep 161163 = 241745) B241745
theorem B161175 : Blo 159796 161175 := bstep (se 1 (by rfl) ⟨120881, by rfl⟩ : syracuseStep 161175 = 241763) B241763
theorem B161195 : Blo 159796 161195 := bstep (se 1 (by rfl) ⟨120896, by rfl⟩ : syracuseStep 161195 = 241793) B241793
theorem B161207 : Blo 159796 161207 := bstep (se 1 (by rfl) ⟨120905, by rfl⟩ : syracuseStep 161207 = 241811) B241811
theorem B161227 : Blo 159796 161227 := bstep (se 1 (by rfl) ⟨120920, by rfl⟩ : syracuseStep 161227 = 241841) B241841
theorem B161239 : Blo 159796 161239 := bstep (se 1 (by rfl) ⟨120929, by rfl⟩ : syracuseStep 161239 = 241859) B241859
theorem B161259 : Blo 159796 161259 := bstep (se 1 (by rfl) ⟨120944, by rfl⟩ : syracuseStep 161259 = 241889) B241889
theorem B161271 : Blo 159796 161271 := bstep (se 1 (by rfl) ⟨120953, by rfl⟩ : syracuseStep 161271 = 241907) B241907
theorem B161291 : Blo 159796 161291 := bstep (se 1 (by rfl) ⟨120968, by rfl⟩ : syracuseStep 161291 = 241937) B241937
theorem B488983 : Blo 159796 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B161303 : Blo 159796 161303 := bstep (se 1 (by rfl) ⟨120977, by rfl⟩ : syracuseStep 161303 = 241955) B241955
theorem B325145 : Blo 159796 325145 := bstep (se 2 (by rfl) ⟨121929, by rfl⟩ : syracuseStep 325145 = 243859) B243859
theorem B161323 : Blo 159796 161323 := bstep (se 1 (by rfl) ⟨120992, by rfl⟩ : syracuseStep 161323 = 241985) B241985
theorem B161335 : Blo 159796 161335 := bstep (se 1 (by rfl) ⟨121001, by rfl⟩ : syracuseStep 161335 = 242003) B242003
theorem B161355 : Blo 159796 161355 := bstep (se 1 (by rfl) ⟨121016, by rfl⟩ : syracuseStep 161355 = 242033) B242033
theorem B161367 : Blo 159796 161367 := bstep (se 1 (by rfl) ⟨121025, by rfl⟩ : syracuseStep 161367 = 242051) B242051
theorem B161387 : Blo 159796 161387 := bstep (se 1 (by rfl) ⟨121040, by rfl⟩ : syracuseStep 161387 = 242081) B242081
theorem B161399 : Blo 159796 161399 := bstep (se 1 (by rfl) ⟨121049, by rfl⟩ : syracuseStep 161399 = 242099) B242099
theorem B161419 : Blo 159796 161419 := bstep (se 1 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 161419 = 242129) B242129
theorem B161431 : Blo 159796 161431 := bstep (se 1 (by rfl) ⟨121073, by rfl⟩ : syracuseStep 161431 = 242147) B242147
theorem B161451 : Blo 159796 161451 := bstep (se 1 (by rfl) ⟨121088, by rfl⟩ : syracuseStep 161451 = 242177) B242177
theorem B390835 : Blo 159796 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B161463 : Blo 159796 161463 := bstep (se 1 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 161463 = 242195) B242195
theorem B161483 : Blo 159796 161483 := bstep (se 1 (by rfl) ⟨121112, by rfl⟩ : syracuseStep 161483 = 242225) B242225
theorem B161495 : Blo 159796 161495 := bstep (se 1 (by rfl) ⟨121121, by rfl⟩ : syracuseStep 161495 = 242243) B242243
theorem B161515 : Blo 159796 161515 := bstep (se 1 (by rfl) ⟨121136, by rfl⟩ : syracuseStep 161515 = 242273) B242273
theorem B161527 : Blo 159796 161527 := bstep (se 1 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 161527 = 242291) B242291
theorem B161547 : Blo 159796 161547 := bstep (se 1 (by rfl) ⟨121160, by rfl⟩ : syracuseStep 161547 = 242321) B242321
theorem B161559 : Blo 159796 161559 := bstep (se 1 (by rfl) ⟨121169, by rfl⟩ : syracuseStep 161559 = 242339) B242339
theorem B161579 : Blo 159796 161579 := bstep (se 1 (by rfl) ⟨121184, by rfl⟩ : syracuseStep 161579 = 242369) B242369
theorem B161591 : Blo 159796 161591 := bstep (se 1 (by rfl) ⟨121193, by rfl⟩ : syracuseStep 161591 = 242387) B242387
theorem B161611 : Blo 159796 161611 := bstep (se 1 (by rfl) ⟨121208, by rfl⟩ : syracuseStep 161611 = 242417) B242417
theorem B161623 : Blo 159796 161623 := bstep (se 1 (by rfl) ⟨121217, by rfl⟩ : syracuseStep 161623 = 242435) B242435
theorem B161643 : Blo 159796 161643 := bstep (se 1 (by rfl) ⟨121232, by rfl⟩ : syracuseStep 161643 = 242465) B242465
theorem B161655 : Blo 159796 161655 := bstep (se 1 (by rfl) ⟨121241, by rfl⟩ : syracuseStep 161655 = 242483) B242483
theorem B161675 : Blo 159796 161675 := bstep (se 1 (by rfl) ⟨121256, by rfl⟩ : syracuseStep 161675 = 242513) B242513
theorem B587665 : Blo 159796 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B161687 : Blo 159796 161687 := bstep (se 1 (by rfl) ⟨121265, by rfl⟩ : syracuseStep 161687 = 242531) B242531
theorem B161707 : Blo 159796 161707 := bstep (se 1 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 161707 = 242561) B242561
theorem B1177523 : Blo 159796 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B161719 : Blo 159796 161719 := bstep (se 1 (by rfl) ⟨121289, by rfl⟩ : syracuseStep 161719 = 242579) B242579
theorem B161739 : Blo 159796 161739 := bstep (se 1 (by rfl) ⟨121304, by rfl⟩ : syracuseStep 161739 = 242609) B242609
theorem B161751 : Blo 159796 161751 := bstep (se 1 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 161751 = 242627) B242627
theorem B260057 : Blo 159796 260057 := bstep (se 2 (by rfl) ⟨97521, by rfl⟩ : syracuseStep 260057 = 195043) B195043
theorem B161771 : Blo 159796 161771 := bstep (se 1 (by rfl) ⟨121328, by rfl⟩ : syracuseStep 161771 = 242657) B242657
theorem B161783 : Blo 159796 161783 := bstep (se 1 (by rfl) ⟨121337, by rfl⟩ : syracuseStep 161783 = 242675) B242675
theorem B161803 : Blo 159796 161803 := bstep (se 1 (by rfl) ⟨121352, by rfl⟩ : syracuseStep 161803 = 242705) B242705
theorem B2193425 : Blo 159796 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B620561 : Blo 159796 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B161815 : Blo 159796 161815 := bstep (se 1 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 161815 = 242723) B242723
theorem B555031 : Blo 159796 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B161835 : Blo 159796 161835 := bstep (se 1 (by rfl) ⟨121376, by rfl⟩ : syracuseStep 161835 = 242753) B242753
theorem B161847 : Blo 159796 161847 := bstep (se 1 (by rfl) ⟨121385, by rfl⟩ : syracuseStep 161847 = 242771) B242771
theorem B161867 : Blo 159796 161867 := bstep (se 1 (by rfl) ⟨121400, by rfl⟩ : syracuseStep 161867 = 242801) B242801
theorem B161879 : Blo 159796 161879 := bstep (se 1 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 161879 = 242819) B242819
theorem B161899 : Blo 159796 161899 := bstep (se 1 (by rfl) ⟨121424, by rfl⟩ : syracuseStep 161899 = 242849) B242849
theorem B161911 : Blo 159796 161911 := bstep (se 1 (by rfl) ⟨121433, by rfl⟩ : syracuseStep 161911 = 242867) B242867
theorem B161931 : Blo 159796 161931 := bstep (se 1 (by rfl) ⟨121448, by rfl⟩ : syracuseStep 161931 = 242897) B242897
theorem B161943 : Blo 159796 161943 := bstep (se 1 (by rfl) ⟨121457, by rfl⟩ : syracuseStep 161943 = 242915) B242915
theorem B2586775 : Blo 159796 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B6715543 : Blo 159796 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B161963 : Blo 159796 161963 := bstep (se 1 (by rfl) ⟨121472, by rfl⟩ : syracuseStep 161963 = 242945) B242945
theorem B161975 : Blo 159796 161975 := bstep (se 1 (by rfl) ⟨121481, by rfl⟩ : syracuseStep 161975 = 242963) B242963
theorem B489665 : Blo 159796 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B161995 : Blo 159796 161995 := bstep (se 1 (by rfl) ⟨121496, by rfl⟩ : syracuseStep 161995 = 242993) B242993
theorem B162007 : Blo 159796 162007 := bstep (se 1 (by rfl) ⟨121505, by rfl⟩ : syracuseStep 162007 = 243011) B243011
theorem B162027 : Blo 159796 162027 := bstep (se 1 (by rfl) ⟨121520, by rfl⟩ : syracuseStep 162027 = 243041) B243041
theorem B162039 : Blo 159796 162039 := bstep (se 1 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 162039 = 243059) B243059
theorem B162059 : Blo 159796 162059 := bstep (se 1 (by rfl) ⟨121544, by rfl⟩ : syracuseStep 162059 = 243089) B243089
theorem B162071 : Blo 159796 162071 := bstep (se 1 (by rfl) ⟨121553, by rfl⟩ : syracuseStep 162071 = 243107) B243107
theorem B162091 : Blo 159796 162091 := bstep (se 1 (by rfl) ⟨121568, by rfl⟩ : syracuseStep 162091 = 243137) B243137
theorem B391475 : Blo 159796 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B162103 : Blo 159796 162103 := bstep (se 1 (by rfl) ⟨121577, by rfl⟩ : syracuseStep 162103 = 243155) B243155
theorem B1374529 : Blo 159796 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B162123 : Blo 159796 162123 := bstep (se 1 (by rfl) ⟨121592, by rfl⟩ : syracuseStep 162123 = 243185) B243185
theorem B162135 : Blo 159796 162135 := bstep (se 1 (by rfl) ⟨121601, by rfl⟩ : syracuseStep 162135 = 243203) B243203
theorem B162155 : Blo 159796 162155 := bstep (se 1 (by rfl) ⟨121616, by rfl⟩ : syracuseStep 162155 = 243233) B243233
theorem B162167 : Blo 159796 162167 := bstep (se 1 (by rfl) ⟨121625, by rfl⟩ : syracuseStep 162167 = 243251) B243251
theorem B162187 : Blo 159796 162187 := bstep (se 1 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 162187 = 243281) B243281
theorem B162199 : Blo 159796 162199 := bstep (se 1 (by rfl) ⟨121649, by rfl⟩ : syracuseStep 162199 = 243299) B243299
theorem B162219 : Blo 159796 162219 := bstep (se 1 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 162219 = 243329) B243329
theorem B162231 : Blo 159796 162231 := bstep (se 1 (by rfl) ⟨121673, by rfl⟩ : syracuseStep 162231 = 243347) B243347
theorem B162251 : Blo 159796 162251 := bstep (se 1 (by rfl) ⟨121688, by rfl⟩ : syracuseStep 162251 = 243377) B243377
theorem B162263 : Blo 159796 162263 := bstep (se 1 (by rfl) ⟨121697, by rfl⟩ : syracuseStep 162263 = 243395) B243395
theorem B621017 : Blo 159796 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B162283 : Blo 159796 162283 := bstep (se 1 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 162283 = 243425) B243425
theorem B162295 : Blo 159796 162295 := bstep (se 1 (by rfl) ⟨121721, by rfl⟩ : syracuseStep 162295 = 243443) B243443
theorem B162315 : Blo 159796 162315 := bstep (se 1 (by rfl) ⟨121736, by rfl⟩ : syracuseStep 162315 = 243473) B243473
theorem B162327 : Blo 159796 162327 := bstep (se 1 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 162327 = 243491) B243491
theorem B162347 : Blo 159796 162347 := bstep (se 1 (by rfl) ⟨121760, by rfl⟩ : syracuseStep 162347 = 243521) B243521
theorem B162359 : Blo 159796 162359 := bstep (se 1 (by rfl) ⟨121769, by rfl⟩ : syracuseStep 162359 = 243539) B243539
theorem B162379 : Blo 159796 162379 := bstep (se 1 (by rfl) ⟨121784, by rfl⟩ : syracuseStep 162379 = 243569) B243569
theorem B162391 : Blo 159796 162391 := bstep (se 1 (by rfl) ⟨121793, by rfl⟩ : syracuseStep 162391 = 243587) B243587
theorem B162411 : Blo 159796 162411 := bstep (se 1 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 162411 = 243617) B243617
theorem B162423 : Blo 159796 162423 := bstep (se 1 (by rfl) ⟨121817, by rfl⟩ : syracuseStep 162423 = 243635) B243635
theorem B162443 : Blo 159796 162443 := bstep (se 1 (by rfl) ⟨121832, by rfl⟩ : syracuseStep 162443 = 243665) B243665
theorem B162455 : Blo 159796 162455 := bstep (se 1 (by rfl) ⟨121841, by rfl⟩ : syracuseStep 162455 = 243683) B243683
theorem B162475 : Blo 159796 162475 := bstep (se 1 (by rfl) ⟨121856, by rfl⟩ : syracuseStep 162475 = 243713) B243713
theorem B621229 : Blo 159796 621229 := bstep (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) B232961
theorem B162487 : Blo 159796 162487 := bstep (se 1 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 162487 = 243731) B243731
theorem B162507 : Blo 159796 162507 := bstep (se 1 (by rfl) ⟨121880, by rfl⟩ : syracuseStep 162507 = 243761) B243761
theorem B391883 : Blo 159796 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B162519 : Blo 159796 162519 := bstep (se 1 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 162519 = 243779) B243779
theorem B162539 : Blo 159796 162539 := bstep (se 1 (by rfl) ⟨121904, by rfl⟩ : syracuseStep 162539 = 243809) B243809
theorem B162551 : Blo 159796 162551 := bstep (se 1 (by rfl) ⟨121913, by rfl⟩ : syracuseStep 162551 = 243827) B243827
theorem B162571 : Blo 159796 162571 := bstep (se 1 (by rfl) ⟨121928, by rfl⟩ : syracuseStep 162571 = 243857) B243857
theorem B817937 : Blo 159796 817937 := bstep (se 2 (by rfl) ⟨306726, by rfl⟩ : syracuseStep 817937 = 613453) B613453
theorem B162583 : Blo 159796 162583 := bstep (se 1 (by rfl) ⟨121937, by rfl⟩ : syracuseStep 162583 = 243875) B243875
theorem B162603 : Blo 159796 162603 := bstep (se 1 (by rfl) ⟨121952, by rfl⟩ : syracuseStep 162603 = 243905) B243905
theorem B162615 : Blo 159796 162615 := bstep (se 1 (by rfl) ⟨121961, by rfl⟩ : syracuseStep 162615 = 243923) B243923
theorem B162635 : Blo 159796 162635 := bstep (se 1 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 162635 = 243953) B243953
theorem B162647 : Blo 159796 162647 := bstep (se 1 (by rfl) ⟨121985, by rfl⟩ : syracuseStep 162647 = 243971) B243971
theorem B359257 : Blo 159796 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B162667 : Blo 159796 162667 := bstep (se 1 (by rfl) ⟨122000, by rfl⟩ : syracuseStep 162667 = 244001) B244001
theorem B162679 : Blo 159796 162679 := bstep (se 1 (by rfl) ⟨122009, by rfl⟩ : syracuseStep 162679 = 244019) B244019
theorem B162699 : Blo 159796 162699 := bstep (se 1 (by rfl) ⟨122024, by rfl⟩ : syracuseStep 162699 = 244049) B244049
theorem B162711 : Blo 159796 162711 := bstep (se 1 (by rfl) ⟨122033, by rfl⟩ : syracuseStep 162711 = 244067) B244067
theorem B162731 : Blo 159796 162731 := bstep (se 1 (by rfl) ⟨122048, by rfl⟩ : syracuseStep 162731 = 244097) B244097
theorem B818099 : Blo 159796 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B162743 : Blo 159796 162743 := bstep (se 1 (by rfl) ⟨122057, by rfl⟩ : syracuseStep 162743 = 244115) B244115
theorem B162763 : Blo 159796 162763 := bstep (se 1 (by rfl) ⟨122072, by rfl⟩ : syracuseStep 162763 = 244145) B244145
theorem B162775 : Blo 159796 162775 := bstep (se 1 (by rfl) ⟨122081, by rfl⟩ : syracuseStep 162775 = 244163) B244163
theorem B621533 : Blo 159796 621533 := bstep (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) B233075
theorem B162795 : Blo 159796 162795 := bstep (se 1 (by rfl) ⟨122096, by rfl⟩ : syracuseStep 162795 = 244193) B244193
theorem B162807 : Blo 159796 162807 := bstep (se 1 (by rfl) ⟨122105, by rfl⟩ : syracuseStep 162807 = 244211) B244211
theorem B162827 : Blo 159796 162827 := bstep (se 1 (by rfl) ⟨122120, by rfl⟩ : syracuseStep 162827 = 244241) B244241
theorem B162839 : Blo 159796 162839 := bstep (se 1 (by rfl) ⟨122129, by rfl⟩ : syracuseStep 162839 = 244259) B244259
theorem B162859 : Blo 159796 162859 := bstep (se 1 (by rfl) ⟨122144, by rfl⟩ : syracuseStep 162859 = 244289) B244289
theorem B162871 : Blo 159796 162871 := bstep (se 1 (by rfl) ⟨122153, by rfl⟩ : syracuseStep 162871 = 244307) B244307
theorem B162891 : Blo 159796 162891 := bstep (se 1 (by rfl) ⟨122168, by rfl⟩ : syracuseStep 162891 = 244337) B244337
theorem B162903 : Blo 159796 162903 := bstep (se 1 (by rfl) ⟨122177, by rfl⟩ : syracuseStep 162903 = 244355) B244355
theorem B293977 : Blo 159796 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B687197 : Blo 159796 687197 := bstep (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) B257699
theorem B162923 : Blo 159796 162923 := bstep (se 1 (by rfl) ⟨122192, by rfl⟩ : syracuseStep 162923 = 244385) B244385
theorem B162935 : Blo 159796 162935 := bstep (se 1 (by rfl) ⟨122201, by rfl⟩ : syracuseStep 162935 = 244403) B244403
theorem B162955 : Blo 159796 162955 := bstep (se 1 (by rfl) ⟨122216, by rfl⟩ : syracuseStep 162955 = 244433) B244433
theorem B162967 : Blo 159796 162967 := bstep (se 1 (by rfl) ⟨122225, by rfl⟩ : syracuseStep 162967 = 244451) B244451
theorem B162987 : Blo 159796 162987 := bstep (se 1 (by rfl) ⟨122240, by rfl⟩ : syracuseStep 162987 = 244481) B244481
theorem B359603 : Blo 159796 359603 := bstep (se 1 (by rfl) ⟨269702, by rfl⟩ : syracuseStep 359603 = 539405) B539405
theorem B162999 : Blo 159796 162999 := bstep (se 1 (by rfl) ⟨122249, by rfl⟩ : syracuseStep 162999 = 244499) B244499
theorem B163019 : Blo 159796 163019 := bstep (se 1 (by rfl) ⟨122264, by rfl⟩ : syracuseStep 163019 = 244529) B244529
theorem B359639 : Blo 159796 359639 := bstep (se 1 (by rfl) ⟨269729, by rfl⟩ : syracuseStep 359639 = 539459) B539459
theorem B163031 : Blo 159796 163031 := bstep (se 1 (by rfl) ⟨122273, by rfl⟩ : syracuseStep 163031 = 244547) B244547
theorem B457949 : Blo 159796 457949 := bstep (se 3 (by rfl) ⟨85865, by rfl⟩ : syracuseStep 457949 = 171731) B171731
theorem B163051 : Blo 159796 163051 := bstep (se 1 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 163051 = 244577) B244577
theorem B163063 : Blo 159796 163063 := bstep (se 1 (by rfl) ⟨122297, by rfl⟩ : syracuseStep 163063 = 244595) B244595
theorem B163083 : Blo 159796 163083 := bstep (se 1 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 163083 = 244625) B244625
theorem B163095 : Blo 159796 163095 := bstep (se 1 (by rfl) ⟨122321, by rfl⟩ : syracuseStep 163095 = 244643) B244643
theorem B163115 : Blo 159796 163115 := bstep (se 1 (by rfl) ⟨122336, by rfl⟩ : syracuseStep 163115 = 244673) B244673
theorem B163127 : Blo 159796 163127 := bstep (se 1 (by rfl) ⟨122345, by rfl⟩ : syracuseStep 163127 = 244691) B244691
theorem B163147 : Blo 159796 163147 := bstep (se 1 (by rfl) ⟨122360, by rfl⟩ : syracuseStep 163147 = 244721) B244721
theorem B163159 : Blo 159796 163159 := bstep (se 1 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 163159 = 244739) B244739
theorem B163179 : Blo 159796 163179 := bstep (se 1 (by rfl) ⟨122384, by rfl⟩ : syracuseStep 163179 = 244769) B244769
theorem B163191 : Blo 159796 163191 := bstep (se 1 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 163191 = 244787) B244787
theorem B359819 : Blo 159796 359819 := bstep (se 1 (by rfl) ⟨269864, by rfl⟩ : syracuseStep 359819 = 539729) B539729
theorem B163211 : Blo 159796 163211 := bstep (se 1 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 163211 = 244817) B244817
theorem B163223 : Blo 159796 163223 := bstep (se 1 (by rfl) ⟨122417, by rfl⟩ : syracuseStep 163223 = 244835) B244835
theorem B163243 : Blo 159796 163243 := bstep (se 1 (by rfl) ⟨122432, by rfl⟩ : syracuseStep 163243 = 244865) B244865
theorem B163255 : Blo 159796 163255 := bstep (se 1 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 163255 = 244883) B244883
theorem B359873 : Blo 159796 359873 := bstep (se 2 (by rfl) ⟨134952, by rfl⟩ : syracuseStep 359873 = 269905) B269905
theorem B163275 : Blo 159796 163275 := bstep (se 1 (by rfl) ⟨122456, by rfl⟩ : syracuseStep 163275 = 244913) B244913
theorem B163287 : Blo 159796 163287 := bstep (se 1 (by rfl) ⟨122465, by rfl⟩ : syracuseStep 163287 = 244931) B244931
theorem B523741 : Blo 159796 523741 := bstep (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) B196403
theorem B163307 : Blo 159796 163307 := bstep (se 1 (by rfl) ⟨122480, by rfl⟩ : syracuseStep 163307 = 244961) B244961
theorem B163319 : Blo 159796 163319 := bstep (se 1 (by rfl) ⟨122489, by rfl⟩ : syracuseStep 163319 = 244979) B244979
theorem B163339 : Blo 159796 163339 := bstep (se 1 (by rfl) ⟨122504, by rfl⟩ : syracuseStep 163339 = 245009) B245009
theorem B163351 : Blo 159796 163351 := bstep (se 1 (by rfl) ⟨122513, by rfl⟩ : syracuseStep 163351 = 245027) B245027
theorem B163371 : Blo 159796 163371 := bstep (se 1 (by rfl) ⟨122528, by rfl⟩ : syracuseStep 163371 = 245057) B245057
theorem B458291 : Blo 159796 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B163383 : Blo 159796 163383 := bstep (se 1 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 163383 = 245075) B245075
theorem B163403 : Blo 159796 163403 := bstep (se 1 (by rfl) ⟨122552, by rfl⟩ : syracuseStep 163403 = 245105) B245105
theorem B163415 : Blo 159796 163415 := bstep (se 1 (by rfl) ⟨122561, by rfl⟩ : syracuseStep 163415 = 245123) B245123
theorem B163435 : Blo 159796 163435 := bstep (se 1 (by rfl) ⟨122576, by rfl⟩ : syracuseStep 163435 = 245153) B245153
theorem B163447 : Blo 159796 163447 := bstep (se 1 (by rfl) ⟨122585, by rfl⟩ : syracuseStep 163447 = 245171) B245171
theorem B163467 : Blo 159796 163467 := bstep (se 1 (by rfl) ⟨122600, by rfl⟩ : syracuseStep 163467 = 245201) B245201
theorem B163479 : Blo 159796 163479 := bstep (se 1 (by rfl) ⟨122609, by rfl⟩ : syracuseStep 163479 = 245219) B245219
theorem B360089 : Blo 159796 360089 := bstep (se 2 (by rfl) ⟨135033, by rfl⟩ : syracuseStep 360089 = 270067) B270067
theorem B163499 : Blo 159796 163499 := bstep (se 1 (by rfl) ⟨122624, by rfl⟩ : syracuseStep 163499 = 245249) B245249
theorem B163511 : Blo 159796 163511 := bstep (se 1 (by rfl) ⟨122633, by rfl⟩ : syracuseStep 163511 = 245267) B245267
theorem B163531 : Blo 159796 163531 := bstep (se 1 (by rfl) ⟨122648, by rfl⟩ : syracuseStep 163531 = 245297) B245297
theorem B163543 : Blo 159796 163543 := bstep (se 1 (by rfl) ⟨122657, by rfl⟩ : syracuseStep 163543 = 245315) B245315
theorem B163563 : Blo 159796 163563 := bstep (se 1 (by rfl) ⟨122672, by rfl⟩ : syracuseStep 163563 = 245345) B245345
theorem B360179 : Blo 159796 360179 := bstep (se 1 (by rfl) ⟨270134, by rfl⟩ : syracuseStep 360179 = 540269) B540269
theorem B163575 : Blo 159796 163575 := bstep (se 1 (by rfl) ⟨122681, by rfl⟩ : syracuseStep 163575 = 245363) B245363
theorem B163595 : Blo 159796 163595 := bstep (se 1 (by rfl) ⟨122696, by rfl⟩ : syracuseStep 163595 = 245393) B245393
theorem B360215 : Blo 159796 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B163607 : Blo 159796 163607 := bstep (se 1 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 163607 = 245411) B245411
theorem B163627 : Blo 159796 163627 := bstep (se 1 (by rfl) ⟨122720, by rfl⟩ : syracuseStep 163627 = 245441) B245441
theorem B163639 : Blo 159796 163639 := bstep (se 1 (by rfl) ⟨122729, by rfl⟩ : syracuseStep 163639 = 245459) B245459
theorem B163659 : Blo 159796 163659 := bstep (se 1 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 163659 = 245489) B245489
theorem B163671 : Blo 159796 163671 := bstep (se 1 (by rfl) ⟨122753, by rfl⟩ : syracuseStep 163671 = 245507) B245507
theorem B163691 : Blo 159796 163691 := bstep (se 1 (by rfl) ⟨122768, by rfl⟩ : syracuseStep 163691 = 245537) B245537
theorem B163703 : Blo 159796 163703 := bstep (se 1 (by rfl) ⟨122777, by rfl⟩ : syracuseStep 163703 = 245555) B245555
theorem B163723 : Blo 159796 163723 := bstep (se 1 (by rfl) ⟨122792, by rfl⟩ : syracuseStep 163723 = 245585) B245585
theorem B163735 : Blo 159796 163735 := bstep (se 1 (by rfl) ⟨122801, by rfl⟩ : syracuseStep 163735 = 245603) B245603
theorem B163755 : Blo 159796 163755 := bstep (se 1 (by rfl) ⟨122816, by rfl⟩ : syracuseStep 163755 = 245633) B245633
theorem B163767 : Blo 159796 163767 := bstep (se 1 (by rfl) ⟨122825, by rfl⟩ : syracuseStep 163767 = 245651) B245651
theorem B360395 : Blo 159796 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B163787 : Blo 159796 163787 := bstep (se 1 (by rfl) ⟨122840, by rfl⟩ : syracuseStep 163787 = 245681) B245681
theorem B360719 : Blo 159796 360719 := bstep (se 1 (by rfl) ⟨270539, by rfl⟩ : syracuseStep 360719 = 541079) B541079
theorem B360737 : Blo 159796 360737 := bstep (se 2 (by rfl) ⟨135276, by rfl⟩ : syracuseStep 360737 = 270553) B270553
theorem B557579 : Blo 159796 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B1835621 : Blo 159796 1835621 := bstep (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) B344179
theorem B361079 : Blo 159796 361079 := bstep (se 1 (by rfl) ⟨270809, by rfl⟩ : syracuseStep 361079 = 541619) B541619
theorem B230159 : Blo 159796 230159 := bstep (se 1 (by rfl) ⟨172619, by rfl⟩ : syracuseStep 230159 = 345239) B345239
theorem B361259 : Blo 159796 361259 := bstep (se 1 (by rfl) ⟨270944, by rfl⟩ : syracuseStep 361259 = 541889) B541889
theorem B820115 : Blo 159796 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B459863 : Blo 159796 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B1672325 : Blo 159796 1672325 := bstep (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) B313561
theorem B361619 : Blo 159796 361619 := bstep (se 1 (by rfl) ⟨271214, by rfl⟩ : syracuseStep 361619 = 542429) B542429
theorem B918701 : Blo 159796 918701 := bstep (se 3 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 918701 = 344513) B344513
theorem B361673 : Blo 159796 361673 := bstep (se 2 (by rfl) ⟨135627, by rfl⟩ : syracuseStep 361673 = 271255) B271255
theorem B689725 : Blo 159796 689725 := bstep (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) B258647
theorem B1541699 : Blo 159796 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B788087 : Blo 159796 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B362375 : Blo 159796 362375 := bstep (se 1 (by rfl) ⟨271781, by rfl⟩ : syracuseStep 362375 = 543563) B543563
theorem B1542041 : Blo 159796 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B821177 : Blo 159796 821177 := bstep (se 2 (by rfl) ⟨307941, by rfl⟩ : syracuseStep 821177 = 615883) B615883
theorem B1837079 : Blo 159796 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B362555 : Blo 159796 362555 := bstep (se 1 (by rfl) ⟨271916, by rfl⟩ : syracuseStep 362555 = 543833) B543833
theorem B362681 : Blo 159796 362681 := bstep (se 2 (by rfl) ⟨136005, by rfl⟩ : syracuseStep 362681 = 272011) B272011
theorem B363023 : Blo 159796 363023 := bstep (se 1 (by rfl) ⟨272267, by rfl⟩ : syracuseStep 363023 = 544535) B544535
theorem B363041 : Blo 159796 363041 := bstep (se 2 (by rfl) ⟨136140, by rfl⟩ : syracuseStep 363041 = 272281) B272281
theorem B461447 : Blo 159796 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B985945 : Blo 159796 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B363383 : Blo 159796 363383 := bstep (se 1 (by rfl) ⟨272537, by rfl⟩ : syracuseStep 363383 = 545075) B545075
theorem B691229 : Blo 159796 691229 := bstep (se 3 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 691229 = 259211) B259211
theorem B363563 : Blo 159796 363563 := bstep (se 1 (by rfl) ⟨272672, by rfl⟩ : syracuseStep 363563 = 545345) B545345
theorem B822473 : Blo 159796 822473 := bstep (se 2 (by rfl) ⟨308427, by rfl⟩ : syracuseStep 822473 = 616855) B616855
theorem B462095 : Blo 159796 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B691571 : Blo 159796 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B363923 : Blo 159796 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B363977 : Blo 159796 363977 := bstep (se 2 (by rfl) ⟨136491, by rfl⟩ : syracuseStep 363977 = 272983) B272983
theorem B626129 : Blo 159796 626129 := bstep (se 2 (by rfl) ⟨234798, by rfl⟩ : syracuseStep 626129 = 469597) B469597
theorem B921091 : Blo 159796 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B462397 : Blo 159796 462397 := bstep (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) B173399
theorem B364679 : Blo 159796 364679 := bstep (se 1 (by rfl) ⟨273509, by rfl⟩ : syracuseStep 364679 = 547019) B547019
theorem B233659 : Blo 159796 233659 := bstep (se 1 (by rfl) ⟨175244, by rfl⟩ : syracuseStep 233659 = 350489) B350489
theorem B692495 : Blo 159796 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B364859 : Blo 159796 364859 := bstep (se 1 (by rfl) ⟨273644, by rfl⟩ : syracuseStep 364859 = 547289) B547289
theorem B5017949 : Blo 159796 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B364985 : Blo 159796 364985 := bstep (se 2 (by rfl) ⟨136869, by rfl⟩ : syracuseStep 364985 = 273739) B273739
theorem B2036267 : Blo 159796 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B234247 : Blo 159796 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B365327 : Blo 159796 365327 := bstep (se 1 (by rfl) ⟨273995, by rfl⟩ : syracuseStep 365327 = 547991) B547991
theorem B365345 : Blo 159796 365345 := bstep (se 2 (by rfl) ⟨137004, by rfl⟩ : syracuseStep 365345 = 274009) B274009
theorem B463735 : Blo 159796 463735 := bstep (se 1 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 463735 = 695603) B695603
theorem B365687 : Blo 159796 365687 := bstep (se 1 (by rfl) ⟨274265, by rfl⟩ : syracuseStep 365687 = 548531) B548531
theorem B4658309 : Blo 159796 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B1545389 : Blo 159796 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B365753 : Blo 159796 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B693485 : Blo 159796 693485 := bstep (se 3 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 693485 = 260057) B260057
theorem B365867 : Blo 159796 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B12719501 : Blo 159796 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B366227 : Blo 159796 366227 := bstep (se 1 (by rfl) ⟨274670, by rfl⟩ : syracuseStep 366227 = 549341) B549341
theorem B366281 : Blo 159796 366281 := bstep (se 2 (by rfl) ⟨137355, by rfl⟩ : syracuseStep 366281 = 274711) B274711
theorem B497441 : Blo 159796 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B923507 : Blo 159796 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B694169 : Blo 159796 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B1742755 : Blo 159796 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B465011 : Blo 159796 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B465239 : Blo 159796 465239 := bstep (se 1 (by rfl) ⟨348929, by rfl⟩ : syracuseStep 465239 = 697859) B697859
theorem B203143 : Blo 159796 203143 := bstep (se 1 (by rfl) ⟨152357, by rfl⟩ : syracuseStep 203143 = 304715) B304715
theorem B366983 : Blo 159796 366983 := bstep (se 1 (by rfl) ⟨275237, by rfl⟩ : syracuseStep 366983 = 550475) B550475
theorem B367163 : Blo 159796 367163 := bstep (se 1 (by rfl) ⟨275372, by rfl⟩ : syracuseStep 367163 = 550745) B550745
theorem B367289 : Blo 159796 367289 := bstep (se 2 (by rfl) ⟨137733, by rfl⟩ : syracuseStep 367289 = 275467) B275467
theorem B2071331 : Blo 159796 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B203563 : Blo 159796 203563 := bstep (se 1 (by rfl) ⟨152672, by rfl⟩ : syracuseStep 203563 = 305345) B305345
theorem B203791 : Blo 159796 203791 := bstep (se 1 (by rfl) ⟨152843, by rfl⟩ : syracuseStep 203791 = 305687) B305687
theorem B367631 : Blo 159796 367631 := bstep (se 1 (by rfl) ⟨275723, by rfl⟩ : syracuseStep 367631 = 551447) B551447
theorem B367649 : Blo 159796 367649 := bstep (se 2 (by rfl) ⟨137868, by rfl⟩ : syracuseStep 367649 = 275737) B275737
theorem B924965 : Blo 159796 924965 := bstep (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) B173431
theorem B367991 : Blo 159796 367991 := bstep (se 1 (by rfl) ⟨275993, by rfl⟩ : syracuseStep 367991 = 551987) B551987
theorem B368171 : Blo 159796 368171 := bstep (se 1 (by rfl) ⟨276128, by rfl⟩ : syracuseStep 368171 = 552257) B552257
theorem B269959 : Blo 159796 269959 := bstep (se 1 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 269959 = 404939) B404939
theorem B204535 : Blo 159796 204535 := bstep (se 1 (by rfl) ⟨153401, by rfl⟩ : syracuseStep 204535 = 306803) B306803
theorem B499591 : Blo 159796 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B171919 : Blo 159796 171919 := bstep (se 1 (by rfl) ⟨128939, by rfl⟩ : syracuseStep 171919 = 257879) B257879
theorem B368531 : Blo 159796 368531 := bstep (se 1 (by rfl) ⟨276398, by rfl⟩ : syracuseStep 368531 = 552797) B552797
theorem B925739 : Blo 159796 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B204859 : Blo 159796 204859 := bstep (se 1 (by rfl) ⟨153644, by rfl⟩ : syracuseStep 204859 = 307289) B307289
theorem B893015 : Blo 159796 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B3449033 : Blo 159796 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B8954057 : Blo 159796 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B270607 : Blo 159796 270607 := bstep (se 1 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 270607 = 405911) B405911
theorem B303659 : Blo 159796 303659 := bstep (se 1 (by rfl) ⟨227744, by rfl⟩ : syracuseStep 303659 = 455489) B455489
theorem B205355 : Blo 159796 205355 := bstep (se 1 (by rfl) ⟨154016, by rfl⟩ : syracuseStep 205355 = 308033) B308033
theorem B303887 : Blo 159796 303887 := bstep (se 1 (by rfl) ⟨227915, by rfl⟩ : syracuseStep 303887 = 455831) B455831
theorem B271147 : Blo 159796 271147 := bstep (se 1 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 271147 = 406721) B406721
theorem B828305 : Blo 159796 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B271289 : Blo 159796 271289 := bstep (se 2 (by rfl) ⟨101733, by rfl⟩ : syracuseStep 271289 = 203467) B203467
theorem B205831 : Blo 159796 205831 := bstep (se 1 (by rfl) ⟨154373, by rfl⟩ : syracuseStep 205831 = 308747) B308747
theorem B7611479 : Blo 159796 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B927197 : Blo 159796 927197 := bstep (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) B347699
theorem B206327 : Blo 159796 206327 := bstep (se 1 (by rfl) ⟨154745, by rfl⟩ : syracuseStep 206327 = 309491) B309491
theorem B271991 : Blo 159796 271991 := bstep (se 1 (by rfl) ⟨203993, by rfl⟩ : syracuseStep 271991 = 407987) B407987
theorem B206479 : Blo 159796 206479 := bstep (se 1 (by rfl) ⟨154859, by rfl⟩ : syracuseStep 206479 = 309719) B309719
theorem B206651 : Blo 159796 206651 := bstep (se 1 (by rfl) ⟨154988, by rfl⟩ : syracuseStep 206651 = 309977) B309977
theorem B698321 : Blo 159796 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B272443 : Blo 159796 272443 := bstep (se 1 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 272443 = 408665) B408665
theorem B239735 : Blo 159796 239735 := bstep (se 1 (by rfl) ⟨179801, by rfl⟩ : syracuseStep 239735 = 359603) B359603
theorem B239759 : Blo 159796 239759 := bstep (se 1 (by rfl) ⟨179819, by rfl⟩ : syracuseStep 239759 = 359639) B359639
theorem B305299 : Blo 159796 305299 := bstep (se 1 (by rfl) ⟨228974, by rfl⟩ : syracuseStep 305299 = 457949) B457949
theorem B239801 : Blo 159796 239801 := bstep (se 2 (by rfl) ⟨89925, by rfl⟩ : syracuseStep 239801 = 179851) B179851
theorem B272585 : Blo 159796 272585 := bstep (se 2 (by rfl) ⟨102219, by rfl⟩ : syracuseStep 272585 = 204439) B204439
theorem B239879 : Blo 159796 239879 := bstep (se 1 (by rfl) ⟨179909, by rfl⟩ : syracuseStep 239879 = 359819) B359819
theorem B239915 : Blo 159796 239915 := bstep (se 1 (by rfl) ⟨179936, by rfl⟩ : syracuseStep 239915 = 359873) B359873
theorem B239945 : Blo 159796 239945 := bstep (se 2 (by rfl) ⟨89979, by rfl⟩ : syracuseStep 239945 = 179959) B179959
theorem B305527 : Blo 159796 305527 := bstep (se 1 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 305527 = 458291) B458291
theorem B240059 : Blo 159796 240059 := bstep (se 1 (by rfl) ⟨180044, by rfl⟩ : syracuseStep 240059 = 360089) B360089
theorem B240119 : Blo 159796 240119 := bstep (se 1 (by rfl) ⟨180089, by rfl⟩ : syracuseStep 240119 = 360179) B360179
theorem B240143 : Blo 159796 240143 := bstep (se 1 (by rfl) ⟨180107, by rfl⟩ : syracuseStep 240143 = 360215) B360215
theorem B240185 : Blo 159796 240185 := bstep (se 2 (by rfl) ⟨90069, by rfl⟩ : syracuseStep 240185 = 180139) B180139
theorem B1845827 : Blo 159796 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B240263 : Blo 159796 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B240299 : Blo 159796 240299 := bstep (se 1 (by rfl) ⟨180224, by rfl⟩ : syracuseStep 240299 = 360449) B360449
theorem B240329 : Blo 159796 240329 := bstep (se 2 (by rfl) ⟨90123, by rfl⟩ : syracuseStep 240329 = 180247) B180247
theorem B2960165 : Blo 159796 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B240443 : Blo 159796 240443 := bstep (se 1 (by rfl) ⟨180332, by rfl⟩ : syracuseStep 240443 = 360665) B360665
theorem B240503 : Blo 159796 240503 := bstep (se 1 (by rfl) ⟨180377, by rfl⟩ : syracuseStep 240503 = 360755) B360755
theorem B273287 : Blo 159796 273287 := bstep (se 1 (by rfl) ⟨204965, by rfl⟩ : syracuseStep 273287 = 409931) B409931
theorem B240527 : Blo 159796 240527 := bstep (se 1 (by rfl) ⟨180395, by rfl⟩ : syracuseStep 240527 = 360791) B360791
theorem B240569 : Blo 159796 240569 := bstep (se 2 (by rfl) ⟨90213, by rfl⟩ : syracuseStep 240569 = 180427) B180427
theorem B240647 : Blo 159796 240647 := bstep (se 1 (by rfl) ⟨180485, by rfl⟩ : syracuseStep 240647 = 360971) B360971
theorem B240683 : Blo 159796 240683 := bstep (se 1 (by rfl) ⟨180512, by rfl⟩ : syracuseStep 240683 = 361025) B361025
theorem B240713 : Blo 159796 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B404615 : Blo 159796 404615 := bstep (se 1 (by rfl) ⟨303461, by rfl⟩ : syracuseStep 404615 = 606923) B606923
theorem B240827 : Blo 159796 240827 := bstep (se 1 (by rfl) ⟨180620, by rfl⟩ : syracuseStep 240827 = 361241) B361241
theorem B240887 : Blo 159796 240887 := bstep (se 1 (by rfl) ⟨180665, by rfl⟩ : syracuseStep 240887 = 361331) B361331
theorem B404747 : Blo 159796 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B240911 : Blo 159796 240911 := bstep (se 1 (by rfl) ⟨180683, by rfl⟩ : syracuseStep 240911 = 361367) B361367
theorem B240953 : Blo 159796 240953 := bstep (se 2 (by rfl) ⟨90357, by rfl⟩ : syracuseStep 240953 = 180715) B180715
theorem B241031 : Blo 159796 241031 := bstep (se 1 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 241031 = 361547) B361547
theorem B248491405 : Blo 159796 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B241067 : Blo 159796 241067 := bstep (se 1 (by rfl) ⟨180800, by rfl⟩ : syracuseStep 241067 = 361601) B361601
theorem B241097 : Blo 159796 241097 := bstep (se 2 (by rfl) ⟨90411, by rfl⟩ : syracuseStep 241097 = 180823) B180823
theorem B1486289 : Blo 159796 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B273935 : Blo 159796 273935 := bstep (se 1 (by rfl) ⟨205451, by rfl⟩ : syracuseStep 273935 = 410903) B410903
theorem B241211 : Blo 159796 241211 := bstep (se 1 (by rfl) ⟨180908, by rfl⟩ : syracuseStep 241211 = 361817) B361817
theorem B241271 : Blo 159796 241271 := bstep (se 1 (by rfl) ⟨180953, by rfl⟩ : syracuseStep 241271 = 361907) B361907
theorem B241295 : Blo 159796 241295 := bstep (se 1 (by rfl) ⟨180971, by rfl⟩ : syracuseStep 241295 = 361943) B361943
theorem B241337 : Blo 159796 241337 := bstep (se 2 (by rfl) ⟨90501, by rfl⟩ : syracuseStep 241337 = 181003) B181003
theorem B241415 : Blo 159796 241415 := bstep (se 1 (by rfl) ⟨181061, by rfl⟩ : syracuseStep 241415 = 362123) B362123
theorem B405263 : Blo 159796 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B241451 : Blo 159796 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B1322801 : Blo 159796 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B241481 : Blo 159796 241481 := bstep (se 2 (by rfl) ⟨90555, by rfl⟩ : syracuseStep 241481 = 181111) B181111
theorem B405395 : Blo 159796 405395 := bstep (se 1 (by rfl) ⟨304046, by rfl⟩ : syracuseStep 405395 = 608093) B608093
theorem B307091 : Blo 159796 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B241595 : Blo 159796 241595 := bstep (se 1 (by rfl) ⟨181196, by rfl⟩ : syracuseStep 241595 = 362393) B362393
theorem B307145 : Blo 159796 307145 := bstep (se 2 (by rfl) ⟨115179, by rfl⟩ : syracuseStep 307145 = 230359) B230359
theorem B241655 : Blo 159796 241655 := bstep (se 1 (by rfl) ⟨181241, by rfl⟩ : syracuseStep 241655 = 362483) B362483
theorem B241679 : Blo 159796 241679 := bstep (se 1 (by rfl) ⟨181259, by rfl⟩ : syracuseStep 241679 = 362519) B362519
theorem B307243 : Blo 159796 307243 := bstep (se 1 (by rfl) ⟨230432, by rfl⟩ : syracuseStep 307243 = 460865) B460865
theorem B274475 : Blo 159796 274475 := bstep (se 1 (by rfl) ⟨205856, by rfl⟩ : syracuseStep 274475 = 411713) B411713
theorem B241721 : Blo 159796 241721 := bstep (se 2 (by rfl) ⟨90645, by rfl⟩ : syracuseStep 241721 = 181291) B181291
theorem B241799 : Blo 159796 241799 := bstep (se 1 (by rfl) ⟨181349, by rfl⟩ : syracuseStep 241799 = 362699) B362699
theorem B241835 : Blo 159796 241835 := bstep (se 1 (by rfl) ⟨181376, by rfl⟩ : syracuseStep 241835 = 362753) B362753
theorem B241865 : Blo 159796 241865 := bstep (se 2 (by rfl) ⟨90699, by rfl⟩ : syracuseStep 241865 = 181399) B181399
theorem B307471 : Blo 159796 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B241979 : Blo 159796 241979 := bstep (se 1 (by rfl) ⟨181484, by rfl⟩ : syracuseStep 241979 = 362969) B362969
theorem B242039 : Blo 159796 242039 := bstep (se 1 (by rfl) ⟨181529, by rfl⟩ : syracuseStep 242039 = 363059) B363059
theorem B242063 : Blo 159796 242063 := bstep (se 1 (by rfl) ⟨181547, by rfl⟩ : syracuseStep 242063 = 363095) B363095
theorem B242105 : Blo 159796 242105 := bstep (se 2 (by rfl) ⟨90789, by rfl⟩ : syracuseStep 242105 = 181579) B181579
theorem B274873 : Blo 159796 274873 := bstep (se 2 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 274873 = 206155) B206155
theorem B242183 : Blo 159796 242183 := bstep (se 1 (by rfl) ⟨181637, by rfl⟩ : syracuseStep 242183 = 363275) B363275
theorem B307727 : Blo 159796 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B3551779 : Blo 159796 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B242219 : Blo 159796 242219 := bstep (se 1 (by rfl) ⟨181664, by rfl⟩ : syracuseStep 242219 = 363329) B363329
theorem B635435 : Blo 159796 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B930365 : Blo 159796 930365 := bstep (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) B348887
theorem B242249 : Blo 159796 242249 := bstep (se 2 (by rfl) ⟨90843, by rfl⟩ : syracuseStep 242249 = 181687) B181687
theorem B4207285 : Blo 159796 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B242363 : Blo 159796 242363 := bstep (se 1 (by rfl) ⟨181772, by rfl⟩ : syracuseStep 242363 = 363545) B363545
theorem B242423 : Blo 159796 242423 := bstep (se 1 (by rfl) ⟨181817, by rfl⟩ : syracuseStep 242423 = 363635) B363635
theorem B242447 : Blo 159796 242447 := bstep (se 1 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 242447 = 363671) B363671
theorem B242489 : Blo 159796 242489 := bstep (se 2 (by rfl) ⟨90933, by rfl⟩ : syracuseStep 242489 = 181867) B181867
theorem B242567 : Blo 159796 242567 := bstep (se 1 (by rfl) ⟨181925, by rfl⟩ : syracuseStep 242567 = 363851) B363851
theorem B242603 : Blo 159796 242603 := bstep (se 1 (by rfl) ⟨181952, by rfl⟩ : syracuseStep 242603 = 363905) B363905
theorem B242633 : Blo 159796 242633 := bstep (se 2 (by rfl) ⟨90987, by rfl⟩ : syracuseStep 242633 = 181975) B181975
theorem B406529 : Blo 159796 406529 := bstep (se 2 (by rfl) ⟨152448, by rfl⟩ : syracuseStep 406529 = 304897) B304897
theorem B242747 : Blo 159796 242747 := bstep (se 1 (by rfl) ⟨182060, by rfl⟩ : syracuseStep 242747 = 364121) B364121
theorem B242807 : Blo 159796 242807 := bstep (se 1 (by rfl) ⟨182105, by rfl⟩ : syracuseStep 242807 = 364211) B364211
theorem B275575 : Blo 159796 275575 := bstep (se 1 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 275575 = 413363) B413363
theorem B242831 : Blo 159796 242831 := bstep (se 1 (by rfl) ⟨182123, by rfl⟩ : syracuseStep 242831 = 364247) B364247
theorem B242873 : Blo 159796 242873 := bstep (se 2 (by rfl) ⟨91077, by rfl⟩ : syracuseStep 242873 = 182155) B182155
theorem B242951 : Blo 159796 242951 := bstep (se 1 (by rfl) ⟨182213, by rfl⟩ : syracuseStep 242951 = 364427) B364427
theorem B242987 : Blo 159796 242987 := bstep (se 1 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 242987 = 364481) B364481
theorem B275771 : Blo 159796 275771 := bstep (se 1 (by rfl) ⟨206828, by rfl⟩ : syracuseStep 275771 = 413657) B413657
theorem B243017 : Blo 159796 243017 := bstep (se 2 (by rfl) ⟨91131, by rfl⟩ : syracuseStep 243017 = 182263) B182263
theorem B406903 : Blo 159796 406903 := bstep (se 1 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 406903 = 610355) B610355
theorem B243131 : Blo 159796 243131 := bstep (se 1 (by rfl) ⟨182348, by rfl⟩ : syracuseStep 243131 = 364697) B364697
theorem B243191 : Blo 159796 243191 := bstep (se 1 (by rfl) ⟨182393, by rfl⟩ : syracuseStep 243191 = 364787) B364787
theorem B243215 : Blo 159796 243215 := bstep (se 1 (by rfl) ⟨182411, by rfl⟩ : syracuseStep 243215 = 364823) B364823
theorem B243257 : Blo 159796 243257 := bstep (se 2 (by rfl) ⟨91221, by rfl⟩ : syracuseStep 243257 = 182443) B182443
theorem B243319 : Blo 159796 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B243335 : Blo 159796 243335 := bstep (se 1 (by rfl) ⟨182501, by rfl⟩ : syracuseStep 243335 = 365003) B365003
theorem B341651 : Blo 159796 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B243371 : Blo 159796 243371 := bstep (se 1 (by rfl) ⟨182528, by rfl⟩ : syracuseStep 243371 = 365057) B365057
theorem B243401 : Blo 159796 243401 := bstep (se 2 (by rfl) ⟨91275, by rfl⟩ : syracuseStep 243401 = 182551) B182551
theorem B276169 : Blo 159796 276169 := bstep (se 2 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 276169 = 207127) B207127
theorem B2111233 : Blo 159796 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B440093 : Blo 159796 440093 := bstep (se 3 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 440093 = 165035) B165035
theorem B407339 : Blo 159796 407339 := bstep (se 1 (by rfl) ⟨305504, by rfl⟩ : syracuseStep 407339 = 611009) B611009
theorem B309035 : Blo 159796 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B1390385 : Blo 159796 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B243515 : Blo 159796 243515 := bstep (se 1 (by rfl) ⟨182636, by rfl⟩ : syracuseStep 243515 = 365273) B365273
theorem B243575 : Blo 159796 243575 := bstep (se 1 (by rfl) ⟨182681, by rfl⟩ : syracuseStep 243575 = 365363) B365363
theorem B243599 : Blo 159796 243599 := bstep (se 1 (by rfl) ⟨182699, by rfl⟩ : syracuseStep 243599 = 365399) B365399
theorem B243641 : Blo 159796 243641 := bstep (se 2 (by rfl) ⟨91365, by rfl⟩ : syracuseStep 243641 = 182731) B182731
theorem B243719 : Blo 159796 243719 := bstep (se 1 (by rfl) ⟨182789, by rfl⟩ : syracuseStep 243719 = 365579) B365579
theorem B12564497 : Blo 159796 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B243755 : Blo 159796 243755 := bstep (se 1 (by rfl) ⟨182816, by rfl⟩ : syracuseStep 243755 = 365633) B365633
theorem B243785 : Blo 159796 243785 := bstep (se 2 (by rfl) ⟨91419, by rfl⟩ : syracuseStep 243785 = 182839) B182839
theorem B243899 : Blo 159796 243899 := bstep (se 1 (by rfl) ⟨182924, by rfl⟩ : syracuseStep 243899 = 365849) B365849
theorem B243959 : Blo 159796 243959 := bstep (se 1 (by rfl) ⟨182969, by rfl⟩ : syracuseStep 243959 = 365939) B365939
theorem B243983 : Blo 159796 243983 := bstep (se 1 (by rfl) ⟨182987, by rfl⟩ : syracuseStep 243983 = 365975) B365975
theorem B244025 : Blo 159796 244025 := bstep (se 2 (by rfl) ⟨91509, by rfl⟩ : syracuseStep 244025 = 183019) B183019
theorem B244103 : Blo 159796 244103 := bstep (se 1 (by rfl) ⟨183077, by rfl⟩ : syracuseStep 244103 = 366155) B366155
theorem B244139 : Blo 159796 244139 := bstep (se 1 (by rfl) ⟨183104, by rfl⟩ : syracuseStep 244139 = 366209) B366209
theorem B244169 : Blo 159796 244169 := bstep (se 2 (by rfl) ⟨91563, by rfl⟩ : syracuseStep 244169 = 183127) B183127
theorem B244283 : Blo 159796 244283 := bstep (se 1 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 244283 = 366425) B366425
theorem B408179 : Blo 159796 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B244343 : Blo 159796 244343 := bstep (se 1 (by rfl) ⟨183257, by rfl⟩ : syracuseStep 244343 = 366515) B366515
theorem B408199 : Blo 159796 408199 := bstep (se 1 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 408199 = 612299) B612299
theorem B244367 : Blo 159796 244367 := bstep (se 1 (by rfl) ⟨183275, by rfl⟩ : syracuseStep 244367 = 366551) B366551
theorem B244409 : Blo 159796 244409 := bstep (se 2 (by rfl) ⟨91653, by rfl⟩ : syracuseStep 244409 = 183307) B183307
theorem B244487 : Blo 159796 244487 := bstep (se 1 (by rfl) ⟨183365, by rfl⟩ : syracuseStep 244487 = 366731) B366731
theorem B244523 : Blo 159796 244523 := bstep (se 1 (by rfl) ⟨183392, by rfl⟩ : syracuseStep 244523 = 366785) B366785
theorem B244553 : Blo 159796 244553 := bstep (se 2 (by rfl) ⟨91707, by rfl⟩ : syracuseStep 244553 = 183415) B183415
theorem B1850201 : Blo 159796 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1227635 : Blo 159796 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B932755 : Blo 159796 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B408473 : Blo 159796 408473 := bstep (se 2 (by rfl) ⟨153177, by rfl⟩ : syracuseStep 408473 = 306355) B306355
theorem B244667 : Blo 159796 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B1162187 : Blo 159796 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B244727 : Blo 159796 244727 := bstep (se 1 (by rfl) ⟨183545, by rfl⟩ : syracuseStep 244727 = 367091) B367091
theorem B244751 : Blo 159796 244751 := bstep (se 1 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 244751 = 367127) B367127
theorem B244793 : Blo 159796 244793 := bstep (se 2 (by rfl) ⟨91797, by rfl⟩ : syracuseStep 244793 = 183595) B183595
theorem B408635 : Blo 159796 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B244871 : Blo 159796 244871 := bstep (se 1 (by rfl) ⟨183653, by rfl⟩ : syracuseStep 244871 = 367307) B367307
theorem B244907 : Blo 159796 244907 := bstep (se 1 (by rfl) ⟨183680, by rfl⟩ : syracuseStep 244907 = 367361) B367361
theorem B244937 : Blo 159796 244937 := bstep (se 2 (by rfl) ⟨91851, by rfl⟩ : syracuseStep 244937 = 183703) B183703
theorem B408847 : Blo 159796 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B867617 : Blo 159796 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B245051 : Blo 159796 245051 := bstep (se 1 (by rfl) ⟨183788, by rfl⟩ : syracuseStep 245051 = 367577) B367577
theorem B245111 : Blo 159796 245111 := bstep (se 1 (by rfl) ⟨183833, by rfl⟩ : syracuseStep 245111 = 367667) B367667
theorem B1555847 : Blo 159796 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B245135 : Blo 159796 245135 := bstep (se 1 (by rfl) ⟨183851, by rfl⟩ : syracuseStep 245135 = 367703) B367703
theorem B671129 : Blo 159796 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B245177 : Blo 159796 245177 := bstep (se 2 (by rfl) ⟨91941, by rfl⟩ : syracuseStep 245177 = 183883) B183883
theorem B310729 : Blo 159796 310729 := bstep (se 2 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 310729 = 233047) B233047
theorem B245255 : Blo 159796 245255 := bstep (se 1 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 245255 = 367883) B367883
theorem B409121 : Blo 159796 409121 := bstep (se 2 (by rfl) ⟨153420, by rfl⟩ : syracuseStep 409121 = 306841) B306841
theorem B245291 : Blo 159796 245291 := bstep (se 1 (by rfl) ⟨183968, by rfl⟩ : syracuseStep 245291 = 367937) B367937
theorem B441917 : Blo 159796 441917 := bstep (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) B165719
theorem B245321 : Blo 159796 245321 := bstep (se 2 (by rfl) ⟨91995, by rfl⟩ : syracuseStep 245321 = 183991) B183991
theorem B245435 : Blo 159796 245435 := bstep (se 1 (by rfl) ⟨184076, by rfl⟩ : syracuseStep 245435 = 368153) B368153
theorem B245495 : Blo 159796 245495 := bstep (se 1 (by rfl) ⟨184121, by rfl⟩ : syracuseStep 245495 = 368243) B368243
theorem B540431 : Blo 159796 540431 := bstep (se 1 (by rfl) ⟨405323, by rfl⟩ : syracuseStep 540431 = 810647) B810647
theorem B245519 : Blo 159796 245519 := bstep (se 1 (by rfl) ⟨184139, by rfl⟩ : syracuseStep 245519 = 368279) B368279
theorem B245561 : Blo 159796 245561 := bstep (se 2 (by rfl) ⟨92085, by rfl⟩ : syracuseStep 245561 = 184171) B184171
theorem B180103 : Blo 159796 180103 := bstep (se 1 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 180103 = 270155) B270155
theorem B245639 : Blo 159796 245639 := bstep (se 1 (by rfl) ⟨184229, by rfl⟩ : syracuseStep 245639 = 368459) B368459
theorem B769945 : Blo 159796 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B245675 : Blo 159796 245675 := bstep (se 1 (by rfl) ⟨184256, by rfl⟩ : syracuseStep 245675 = 368513) B368513
theorem B344009 : Blo 159796 344009 := bstep (se 2 (by rfl) ⟨129003, by rfl⟩ : syracuseStep 344009 = 258007) B258007
theorem B540701 : Blo 159796 540701 := bstep (se 3 (by rfl) ⟨101381, by rfl⟩ : syracuseStep 540701 = 202763) B202763
theorem B180283 : Blo 159796 180283 := bstep (se 1 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 180283 = 270425) B270425
theorem B344521 : Blo 159796 344521 := bstep (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) B258391
theorem B410123 : Blo 159796 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B180751 : Blo 159796 180751 := bstep (se 1 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 180751 = 271127) B271127
theorem B3457829 : Blo 159796 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B3982117 : Blo 159796 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B770867 : Blo 159796 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B181255 : Blo 159796 181255 := bstep (se 1 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 181255 = 271883) B271883
theorem B410771 : Blo 159796 410771 := bstep (se 1 (by rfl) ⟨308078, by rfl⟩ : syracuseStep 410771 = 616157) B616157
theorem B181435 : Blo 159796 181435 := bstep (se 1 (by rfl) ⟨136076, by rfl⟩ : syracuseStep 181435 = 272153) B272153
theorem B345359 : Blo 159796 345359 := bstep (se 1 (by rfl) ⟨259019, by rfl⟩ : syracuseStep 345359 = 518039) B518039
theorem B542105 : Blo 159796 542105 := bstep (se 2 (by rfl) ⟨203289, by rfl⟩ : syracuseStep 542105 = 406579) B406579
theorem B411065 : Blo 159796 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B837067 : Blo 159796 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B181903 : Blo 159796 181903 := bstep (se 1 (by rfl) ⟨136427, by rfl⟩ : syracuseStep 181903 = 272855) B272855
theorem B378553 : Blo 159796 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B345991 : Blo 159796 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B2738123 : Blo 159796 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B542807 : Blo 159796 542807 := bstep (se 1 (by rfl) ⟨407105, by rfl⟩ : syracuseStep 542807 = 814211) B814211
theorem B411763 : Blo 159796 411763 := bstep (se 1 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 411763 = 617645) B617645
theorem B182407 : Blo 159796 182407 := bstep (se 1 (by rfl) ⟨136805, by rfl⟩ : syracuseStep 182407 = 273611) B273611
theorem B411905 : Blo 159796 411905 := bstep (se 2 (by rfl) ⟨154464, by rfl⟩ : syracuseStep 411905 = 308929) B308929
theorem B936251 : Blo 159796 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B346427 : Blo 159796 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B182587 : Blo 159796 182587 := bstep (se 1 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 182587 = 273881) B273881
theorem B543293 : Blo 159796 543293 := bstep (se 3 (by rfl) ⟨101867, by rfl⟩ : syracuseStep 543293 = 203735) B203735
theorem B1231553 : Blo 159796 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B412361 : Blo 159796 412361 := bstep (se 2 (by rfl) ⟨154635, by rfl⟩ : syracuseStep 412361 = 309271) B309271
theorem B183055 : Blo 159796 183055 := bstep (se 1 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 183055 = 274583) B274583
theorem B346999 : Blo 159796 346999 := bstep (se 1 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 346999 = 520499) B520499
theorem B347179 : Blo 159796 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B412715 : Blo 159796 412715 := bstep (se 1 (by rfl) ⟨309536, by rfl⟩ : syracuseStep 412715 = 619073) B619073
theorem B347255 : Blo 159796 347255 := bstep (se 1 (by rfl) ⟨260441, by rfl⟩ : syracuseStep 347255 = 520883) B520883
theorem B904385 : Blo 159796 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B183559 : Blo 159796 183559 := bstep (se 1 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 183559 = 275339) B275339
theorem B609551 : Blo 159796 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B576827 : Blo 159796 576827 := bstep (se 1 (by rfl) ⟨432620, by rfl⟩ : syracuseStep 576827 = 865241) B865241
theorem B183739 : Blo 159796 183739 := bstep (se 1 (by rfl) ⟨137804, by rfl⟩ : syracuseStep 183739 = 275609) B275609
theorem B773675 : Blo 159796 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B2084453 : Blo 159796 2084453 := bstep (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) B390835
theorem B216763 : Blo 159796 216763 := bstep (se 1 (by rfl) ⟨162572, by rfl⟩ : syracuseStep 216763 = 325145) B325145
theorem B479009 : Blo 159796 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B1822499 : Blo 159796 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B184207 : Blo 159796 184207 := bstep (se 1 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 184207 = 276311) B276311
theorem B544697 : Blo 159796 544697 := bstep (se 2 (by rfl) ⟨204261, by rfl⟩ : syracuseStep 544697 = 408523) B408523
theorem B577489 : Blo 159796 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B1462283 : Blo 159796 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B413707 : Blo 159796 413707 := bstep (se 1 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 413707 = 620561) B620561
theorem B1986677 : Blo 159796 1986677 := bstep (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) B186251
theorem B413849 : Blo 159796 413849 := bstep (se 2 (by rfl) ⟨155193, by rfl⟩ : syracuseStep 413849 = 310387) B310387
theorem B414011 : Blo 159796 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B545291 : Blo 159796 545291 := bstep (se 1 (by rfl) ⟨408968, by rfl⟩ : syracuseStep 545291 = 817937) B817937
theorem B1167949 : Blo 159796 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B545399 : Blo 159796 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B414355 : Blo 159796 414355 := bstep (se 1 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 414355 = 621533) B621533
theorem B3134213 : Blo 159796 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B414497 : Blo 159796 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B807833 : Blo 159796 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B545993 : Blo 159796 545993 := bstep (se 2 (by rfl) ⟨204747, by rfl⟩ : syracuseStep 545993 = 409495) B409495
theorem B3102533 : Blo 159796 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B546695 : Blo 159796 546695 := bstep (se 1 (by rfl) ⟨410021, by rfl⟩ : syracuseStep 546695 = 820043) B820043
theorem B809027 : Blo 159796 809027 := bstep (se 1 (by rfl) ⟨606770, by rfl⟩ : syracuseStep 809027 = 1213541) B1213541
theorem B547073 : Blo 159796 547073 := bstep (se 2 (by rfl) ⟨205152, by rfl⟩ : syracuseStep 547073 = 410305) B410305
theorem B809351 : Blo 159796 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B514451 : Blo 159796 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B612755 : Blo 159796 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B219791 : Blo 159796 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B2644751 : Blo 159796 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B220039 : Blo 159796 220039 := bstep (se 1 (by rfl) ⟨165029, by rfl⟩ : syracuseStep 220039 = 330059) B330059
theorem B547883 : Blo 159796 547883 := bstep (se 1 (by rfl) ⟨410912, by rfl⟩ : syracuseStep 547883 = 821825) B821825
theorem B417035 : Blo 159796 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B941401 : Blo 159796 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B1335041 : Blo 159796 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B417793 : Blo 159796 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B614411 : Blo 159796 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B745483 : Blo 159796 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B549179 : Blo 159796 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B2777489 : Blo 159796 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B549665 : Blo 159796 549665 := bstep (se 2 (by rfl) ⟨206124, by rfl⟩ : syracuseStep 549665 = 412249) B412249
theorem B418679 : Blo 159796 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B648071 : Blo 159796 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B287777 : Blo 159796 287777 := bstep (se 2 (by rfl) ⟨107916, by rfl⟩ : syracuseStep 287777 = 215833) B215833
theorem B1729781 : Blo 159796 1729781 := bstep (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) B162167
theorem B550259 : Blo 159796 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B779863 : Blo 159796 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B812915 : Blo 159796 812915 := bstep (se 1 (by rfl) ⟨609686, by rfl⟩ : syracuseStep 812915 = 1219373) B1219373
theorem B878471 : Blo 159796 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B583571 : Blo 159796 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B1042379 : Blo 159796 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B813401 : Blo 159796 813401 := bstep (se 2 (by rfl) ⟨305025, by rfl⟩ : syracuseStep 813401 = 610051) B610051
theorem B780691 : Blo 159796 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B616889 : Blo 159796 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B3893953 : Blo 159796 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B912161 : Blo 159796 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B256969 : Blo 159796 256969 := bstep (se 2 (by rfl) ⟨96363, by rfl⟩ : syracuseStep 256969 = 192727) B192727
theorem B290575 : Blo 159796 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B3534637 : Blo 159796 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B618299 : Blo 159796 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B1863575 : Blo 159796 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B5304365 : Blo 159796 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B159803 : Blo 159796 159803 := bstep (se 1 (by rfl) ⟨119852, by rfl⟩ : syracuseStep 159803 = 239705) B239705
theorem B5009501 : Blo 159796 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B159879 : Blo 159796 159879 := bstep (se 1 (by rfl) ⟨119909, by rfl⟩ : syracuseStep 159879 = 239819) B239819
theorem B159887 : Blo 159796 159887 := bstep (se 1 (by rfl) ⟨119915, by rfl⟩ : syracuseStep 159887 = 239831) B239831
theorem B159931 : Blo 159796 159931 := bstep (se 1 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 159931 = 239897) B239897
theorem B160007 : Blo 159796 160007 := bstep (se 1 (by rfl) ⟨120005, by rfl⟩ : syracuseStep 160007 = 240011) B240011
theorem B192775 : Blo 159796 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B160015 : Blo 159796 160015 := bstep (se 1 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 160015 = 240023) B240023
theorem B618785 : Blo 159796 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B160059 : Blo 159796 160059 := bstep (se 1 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 160059 = 240089) B240089
theorem B160135 : Blo 159796 160135 := bstep (se 1 (by rfl) ⟨120101, by rfl⟩ : syracuseStep 160135 = 240203) B240203
theorem B160143 : Blo 159796 160143 := bstep (se 1 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 160143 = 240215) B240215
theorem B815507 : Blo 159796 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B160187 : Blo 159796 160187 := bstep (se 1 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 160187 = 240281) B240281
theorem B160263 : Blo 159796 160263 := bstep (se 1 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 160263 = 240395) B240395
theorem B160271 : Blo 159796 160271 := bstep (se 1 (by rfl) ⟨120203, by rfl⟩ : syracuseStep 160271 = 240407) B240407
theorem B1045021 : Blo 159796 1045021 := bstep (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) B391883
theorem B979499 : Blo 159796 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B160315 : Blo 159796 160315 := bstep (se 1 (by rfl) ⟨120236, by rfl⟩ : syracuseStep 160315 = 240473) B240473
theorem B881239 : Blo 159796 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B160391 : Blo 159796 160391 := bstep (se 1 (by rfl) ⟨120293, by rfl⟩ : syracuseStep 160391 = 240587) B240587
theorem B160399 : Blo 159796 160399 := bstep (se 1 (by rfl) ⟨120299, by rfl⟩ : syracuseStep 160399 = 240599) B240599
theorem B160443 : Blo 159796 160443 := bstep (se 1 (by rfl) ⟨120332, by rfl⟩ : syracuseStep 160443 = 240665) B240665
theorem B651977 : Blo 159796 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B160519 : Blo 159796 160519 := bstep (se 1 (by rfl) ⟨120389, by rfl⟩ : syracuseStep 160519 = 240779) B240779
theorem B160527 : Blo 159796 160527 := bstep (se 1 (by rfl) ⟨120395, by rfl⟩ : syracuseStep 160527 = 240791) B240791
theorem B488207 : Blo 159796 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B160571 : Blo 159796 160571 := bstep (se 1 (by rfl) ⟨120428, by rfl⟩ : syracuseStep 160571 = 240857) B240857
theorem B160647 : Blo 159796 160647 := bstep (se 1 (by rfl) ⟨120485, by rfl⟩ : syracuseStep 160647 = 240971) B240971
theorem B160655 : Blo 159796 160655 := bstep (se 1 (by rfl) ⟨120491, by rfl⟩ : syracuseStep 160655 = 240983) B240983
theorem B160699 : Blo 159796 160699 := bstep (se 1 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 160699 = 241049) B241049
theorem B160775 : Blo 159796 160775 := bstep (se 1 (by rfl) ⟨120581, by rfl⟩ : syracuseStep 160775 = 241163) B241163
theorem B160783 : Blo 159796 160783 := bstep (se 1 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 160783 = 241175) B241175
theorem B1176599 : Blo 159796 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B160827 : Blo 159796 160827 := bstep (se 1 (by rfl) ⟨120620, by rfl⟩ : syracuseStep 160827 = 241241) B241241
theorem B160903 : Blo 159796 160903 := bstep (se 1 (by rfl) ⟨120677, by rfl⟩ : syracuseStep 160903 = 241355) B241355
theorem B160911 : Blo 159796 160911 := bstep (se 1 (by rfl) ⟨120683, by rfl⟩ : syracuseStep 160911 = 241367) B241367
theorem B160955 : Blo 159796 160955 := bstep (se 1 (by rfl) ⟨120716, by rfl⟩ : syracuseStep 160955 = 241433) B241433
theorem B619757 : Blo 159796 619757 := bstep (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) B232409
theorem B161031 : Blo 159796 161031 := bstep (se 1 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 161031 = 241547) B241547
theorem B161039 : Blo 159796 161039 := bstep (se 1 (by rfl) ⟨120779, by rfl⟩ : syracuseStep 161039 = 241559) B241559
theorem B161083 : Blo 159796 161083 := bstep (se 1 (by rfl) ⟨120812, by rfl⟩ : syracuseStep 161083 = 241625) B241625
theorem B161159 : Blo 159796 161159 := bstep (se 1 (by rfl) ⟨120869, by rfl⟩ : syracuseStep 161159 = 241739) B241739
theorem B161167 : Blo 159796 161167 := bstep (se 1 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 161167 = 241751) B241751
theorem B161211 : Blo 159796 161211 := bstep (se 1 (by rfl) ⟨120908, by rfl⟩ : syracuseStep 161211 = 241817) B241817
theorem B161287 : Blo 159796 161287 := bstep (se 1 (by rfl) ⟨120965, by rfl⟩ : syracuseStep 161287 = 241931) B241931
theorem B161295 : Blo 159796 161295 := bstep (se 1 (by rfl) ⟨120971, by rfl⟩ : syracuseStep 161295 = 241943) B241943
theorem B620075 : Blo 159796 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B161339 : Blo 159796 161339 := bstep (se 1 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 161339 = 242009) B242009
theorem B1242701 : Blo 159796 1242701 := bstep (se 3 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 1242701 = 466013) B466013
theorem B3995237 : Blo 159796 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B161415 : Blo 159796 161415 := bstep (se 1 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 161415 = 242123) B242123
theorem B161423 : Blo 159796 161423 := bstep (se 1 (by rfl) ⟨121067, by rfl⟩ : syracuseStep 161423 = 242135) B242135
theorem B161467 : Blo 159796 161467 := bstep (se 1 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 161467 = 242201) B242201
theorem B1832705 : Blo 159796 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B161543 : Blo 159796 161543 := bstep (se 1 (by rfl) ⟨121157, by rfl⟩ : syracuseStep 161543 = 242315) B242315
theorem B161551 : Blo 159796 161551 := bstep (se 1 (by rfl) ⟨121163, by rfl⟩ : syracuseStep 161551 = 242327) B242327
theorem B456491 : Blo 159796 456491 := bstep (se 1 (by rfl) ⟨342368, by rfl⟩ : syracuseStep 456491 = 684737) B684737
theorem B915259 : Blo 159796 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B161595 : Blo 159796 161595 := bstep (se 1 (by rfl) ⟨121196, by rfl⟩ : syracuseStep 161595 = 242393) B242393
theorem B161671 : Blo 159796 161671 := bstep (se 1 (by rfl) ⟨121253, by rfl⟩ : syracuseStep 161671 = 242507) B242507
theorem B161679 : Blo 159796 161679 := bstep (se 1 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 161679 = 242519) B242519
theorem B194447 : Blo 159796 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B161723 : Blo 159796 161723 := bstep (se 1 (by rfl) ⟨121292, by rfl⟩ : syracuseStep 161723 = 242585) B242585
theorem B161799 : Blo 159796 161799 := bstep (se 1 (by rfl) ⟨121349, by rfl⟩ : syracuseStep 161799 = 242699) B242699
theorem B161807 : Blo 159796 161807 := bstep (se 1 (by rfl) ⟨121355, by rfl⟩ : syracuseStep 161807 = 242711) B242711
theorem B161851 : Blo 159796 161851 := bstep (se 1 (by rfl) ⟨121388, by rfl⟩ : syracuseStep 161851 = 242777) B242777
theorem B161927 : Blo 159796 161927 := bstep (se 1 (by rfl) ⟨121445, by rfl⟩ : syracuseStep 161927 = 242891) B242891
theorem B161935 : Blo 159796 161935 := bstep (se 1 (by rfl) ⟨121451, by rfl⟩ : syracuseStep 161935 = 242903) B242903
theorem B161979 : Blo 159796 161979 := bstep (se 1 (by rfl) ⟨121484, by rfl⟩ : syracuseStep 161979 = 242969) B242969
theorem B162055 : Blo 159796 162055 := bstep (se 1 (by rfl) ⟨121541, by rfl⟩ : syracuseStep 162055 = 243083) B243083
theorem B162063 : Blo 159796 162063 := bstep (se 1 (by rfl) ⟨121547, by rfl⟩ : syracuseStep 162063 = 243095) B243095
theorem B162107 : Blo 159796 162107 := bstep (se 1 (by rfl) ⟨121580, by rfl⟩ : syracuseStep 162107 = 243161) B243161
theorem B162183 : Blo 159796 162183 := bstep (se 1 (by rfl) ⟨121637, by rfl⟩ : syracuseStep 162183 = 243275) B243275
theorem B162191 : Blo 159796 162191 := bstep (se 1 (by rfl) ⟨121643, by rfl⟩ : syracuseStep 162191 = 243287) B243287
theorem B588185 : Blo 159796 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B162235 : Blo 159796 162235 := bstep (se 1 (by rfl) ⟨121676, by rfl⟩ : syracuseStep 162235 = 243353) B243353
theorem B162311 : Blo 159796 162311 := bstep (se 1 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 162311 = 243467) B243467
theorem B162319 : Blo 159796 162319 := bstep (se 1 (by rfl) ⟨121739, by rfl⟩ : syracuseStep 162319 = 243479) B243479
theorem B162363 : Blo 159796 162363 := bstep (se 1 (by rfl) ⟨121772, by rfl⟩ : syracuseStep 162363 = 243545) B243545
theorem B1768013 : Blo 159796 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B785015 : Blo 159796 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B162439 : Blo 159796 162439 := bstep (se 1 (by rfl) ⟨121829, by rfl⟩ : syracuseStep 162439 = 243659) B243659
theorem B162447 : Blo 159796 162447 := bstep (se 1 (by rfl) ⟨121835, by rfl⟩ : syracuseStep 162447 = 243671) B243671
theorem B162491 : Blo 159796 162491 := bstep (se 1 (by rfl) ⟨121868, by rfl⟩ : syracuseStep 162491 = 243737) B243737
theorem B162567 : Blo 159796 162567 := bstep (se 1 (by rfl) ⟨121925, by rfl⟩ : syracuseStep 162567 = 243851) B243851
theorem B162575 : Blo 159796 162575 := bstep (se 1 (by rfl) ⟨121931, by rfl⟩ : syracuseStep 162575 = 243863) B243863
theorem B391969 : Blo 159796 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B326443 : Blo 159796 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B162619 : Blo 159796 162619 := bstep (se 1 (by rfl) ⟨121964, by rfl⟩ : syracuseStep 162619 = 243929) B243929
theorem B260983 : Blo 159796 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B162695 : Blo 159796 162695 := bstep (se 1 (by rfl) ⟨122021, by rfl⟩ : syracuseStep 162695 = 244043) B244043
theorem B162703 : Blo 159796 162703 := bstep (se 1 (by rfl) ⟨122027, by rfl⟩ : syracuseStep 162703 = 244055) B244055
theorem B162747 : Blo 159796 162747 := bstep (se 1 (by rfl) ⟨122060, by rfl⟩ : syracuseStep 162747 = 244121) B244121
theorem B162823 : Blo 159796 162823 := bstep (se 1 (by rfl) ⟨122117, by rfl⟩ : syracuseStep 162823 = 244235) B244235
theorem B162831 : Blo 159796 162831 := bstep (se 1 (by rfl) ⟨122123, by rfl⟩ : syracuseStep 162831 = 244247) B244247
theorem B621611 : Blo 159796 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B162875 : Blo 159796 162875 := bstep (se 1 (by rfl) ⟨122156, by rfl⟩ : syracuseStep 162875 = 244313) B244313
theorem B162951 : Blo 159796 162951 := bstep (se 1 (by rfl) ⟨122213, by rfl⟩ : syracuseStep 162951 = 244427) B244427
theorem B162959 : Blo 159796 162959 := bstep (se 1 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 162959 = 244439) B244439
theorem B163003 : Blo 159796 163003 := bstep (se 1 (by rfl) ⟨122252, by rfl⟩ : syracuseStep 163003 = 244505) B244505
theorem B916717 : Blo 159796 916717 := bstep (se 3 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 916717 = 343769) B343769
theorem B163079 : Blo 159796 163079 := bstep (se 1 (by rfl) ⟨122309, by rfl⟩ : syracuseStep 163079 = 244619) B244619
theorem B163087 : Blo 159796 163087 := bstep (se 1 (by rfl) ⟨122315, by rfl⟩ : syracuseStep 163087 = 244631) B244631
theorem B163131 : Blo 159796 163131 := bstep (se 1 (by rfl) ⟨122348, by rfl⟩ : syracuseStep 163131 = 244697) B244697
theorem B163207 : Blo 159796 163207 := bstep (se 1 (by rfl) ⟨122405, by rfl⟩ : syracuseStep 163207 = 244811) B244811
theorem B163215 : Blo 159796 163215 := bstep (se 1 (by rfl) ⟨122411, by rfl⟩ : syracuseStep 163215 = 244823) B244823
theorem B458131 : Blo 159796 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B818585 : Blo 159796 818585 := bstep (se 2 (by rfl) ⟨306969, by rfl⟩ : syracuseStep 818585 = 613939) B613939
theorem B163259 : Blo 159796 163259 := bstep (se 1 (by rfl) ⟨122444, by rfl⟩ : syracuseStep 163259 = 244889) B244889
theorem B163335 : Blo 159796 163335 := bstep (se 1 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 163335 = 245003) B245003
theorem B163343 : Blo 159796 163343 := bstep (se 1 (by rfl) ⟨122507, by rfl⟩ : syracuseStep 163343 = 245015) B245015
theorem B884267 : Blo 159796 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B163387 : Blo 159796 163387 := bstep (se 1 (by rfl) ⟨122540, by rfl⟩ : syracuseStep 163387 = 245081) B245081
theorem B360071 : Blo 159796 360071 := bstep (se 1 (by rfl) ⟨270053, by rfl⟩ : syracuseStep 360071 = 540107) B540107
theorem B163463 : Blo 159796 163463 := bstep (se 1 (by rfl) ⟨122597, by rfl⟩ : syracuseStep 163463 = 245195) B245195
theorem B163471 : Blo 159796 163471 := bstep (se 1 (by rfl) ⟨122603, by rfl⟩ : syracuseStep 163471 = 245207) B245207
theorem B163515 : Blo 159796 163515 := bstep (se 1 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 163515 = 245273) B245273
theorem B163591 : Blo 159796 163591 := bstep (se 1 (by rfl) ⟨122693, by rfl⟩ : syracuseStep 163591 = 245387) B245387
theorem B163599 : Blo 159796 163599 := bstep (se 1 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 163599 = 245399) B245399
theorem B360251 : Blo 159796 360251 := bstep (se 1 (by rfl) ⟨270188, by rfl⟩ : syracuseStep 360251 = 540377) B540377
theorem B163643 : Blo 159796 163643 := bstep (se 1 (by rfl) ⟨122732, by rfl⟩ : syracuseStep 163643 = 245465) B245465
theorem B163719 : Blo 159796 163719 := bstep (se 1 (by rfl) ⟨122789, by rfl⟩ : syracuseStep 163719 = 245579) B245579
theorem B163727 : Blo 159796 163727 := bstep (se 1 (by rfl) ⟨122795, by rfl⟩ : syracuseStep 163727 = 245591) B245591
theorem B360377 : Blo 159796 360377 := bstep (se 2 (by rfl) ⟨135141, by rfl⟩ : syracuseStep 360377 = 270283) B270283
theorem B163771 : Blo 159796 163771 := bstep (se 1 (by rfl) ⟨122828, by rfl⟩ : syracuseStep 163771 = 245657) B245657
theorem B1540043 : Blo 159796 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B557057 : Blo 159796 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B360467 : Blo 159796 360467 := bstep (se 1 (by rfl) ⟨270350, by rfl⟩ : syracuseStep 360467 = 540701) B540701
theorem B360809 : Blo 159796 360809 := bstep (se 2 (by rfl) ⟨135303, by rfl⟩ : syracuseStep 360809 = 270607) B270607
theorem B459361 : Blo 159796 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B1114883 : Blo 159796 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B230239 : Blo 159796 230239 := bstep (se 1 (by rfl) ⟨172679, by rfl⟩ : syracuseStep 230239 = 345359) B345359
theorem B361403 : Blo 159796 361403 := bstep (se 1 (by rfl) ⟨271052, by rfl⟩ : syracuseStep 361403 = 542105) B542105
theorem B5309489 : Blo 159796 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B361529 : Blo 159796 361529 := bstep (se 2 (by rfl) ⟨135573, by rfl⟩ : syracuseStep 361529 = 271147) B271147
theorem B361871 : Blo 159796 361871 := bstep (se 1 (by rfl) ⟨271403, by rfl⟩ : syracuseStep 361871 = 542807) B542807
theorem B624167 : Blo 159796 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B230951 : Blo 159796 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B362195 : Blo 159796 362195 := bstep (se 1 (by rfl) ⟨271646, by rfl⟩ : syracuseStep 362195 = 543293) B543293
theorem B821035 : Blo 159796 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B1116089 : Blo 159796 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B460819 : Blo 159796 460819 := bstep (se 1 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 460819 = 691229) B691229
theorem B231503 : Blo 159796 231503 := bstep (se 1 (by rfl) ⟨173627, by rfl⟩ : syracuseStep 231503 = 347255) B347255
theorem B919633 : Blo 159796 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B461047 : Blo 159796 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B461321 : Blo 159796 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B1214999 : Blo 159796 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B363131 : Blo 159796 363131 := bstep (se 1 (by rfl) ⟨272348, by rfl⟩ : syracuseStep 363131 = 544697) B544697
theorem B363257 : Blo 159796 363257 := bstep (se 2 (by rfl) ⟨136221, by rfl⟩ : syracuseStep 363257 = 272443) B272443
theorem B461663 : Blo 159796 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B3345299 : Blo 159796 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B363527 : Blo 159796 363527 := bstep (se 1 (by rfl) ⟨272645, by rfl⟩ : syracuseStep 363527 = 545291) B545291
theorem B363599 : Blo 159796 363599 := bstep (se 1 (by rfl) ⟨272699, by rfl⟩ : syracuseStep 363599 = 545399) B545399
theorem B363995 : Blo 159796 363995 := bstep (se 1 (by rfl) ⟨272996, by rfl⟩ : syracuseStep 363995 = 545993) B545993
theorem B462323 : Blo 159796 462323 := bstep (se 1 (by rfl) ⟨346742, by rfl⟩ : syracuseStep 462323 = 693485) B693485
theorem B1314593 : Blo 159796 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B462665 : Blo 159796 462665 := bstep (se 2 (by rfl) ⟨173499, by rfl⟩ : syracuseStep 462665 = 346999) B346999
theorem B331627 : Blo 159796 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B2068355 : Blo 159796 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B364463 : Blo 159796 364463 := bstep (se 1 (by rfl) ⟨273347, by rfl⟩ : syracuseStep 364463 = 546695) B546695
theorem B462779 : Blo 159796 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B462905 : Blo 159796 462905 := bstep (se 2 (by rfl) ⟨173589, by rfl⟩ : syracuseStep 462905 = 347179) B347179
theorem B364715 : Blo 159796 364715 := bstep (se 1 (by rfl) ⟨273536, by rfl⟩ : syracuseStep 364715 = 547073) B547073
theorem B2101565 : Blo 159796 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B331321873 : Blo 159796 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B1380887 : Blo 159796 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B365255 : Blo 159796 365255 := bstep (se 1 (by rfl) ⟨273941, by rfl⟩ : syracuseStep 365255 = 547883) B547883
theorem B824093 : Blo 159796 824093 := bstep (se 3 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 824093 = 309035) B309035
theorem B890027 : Blo 159796 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B595343 : Blo 159796 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B2299355 : Blo 159796 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B5969371 : Blo 159796 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B366119 : Blo 159796 366119 := bstep (se 1 (by rfl) ⟨274589, by rfl⟩ : syracuseStep 366119 = 549179) B549179
theorem B202439 : Blo 159796 202439 := bstep (se 1 (by rfl) ⟨151829, by rfl⟩ : syracuseStep 202439 = 303659) B303659
theorem B202591 : Blo 159796 202591 := bstep (se 1 (by rfl) ⟨151943, by rfl⟩ : syracuseStep 202591 = 303887) B303887
theorem B366443 : Blo 159796 366443 := bstep (se 1 (by rfl) ⟨274832, by rfl⟩ : syracuseStep 366443 = 549665) B549665
theorem B366497 : Blo 159796 366497 := bstep (se 2 (by rfl) ⟨137436, by rfl⟩ : syracuseStep 366497 = 274873) B274873
theorem B432047 : Blo 159796 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B1153187 : Blo 159796 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B366839 : Blo 159796 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B694919 : Blo 159796 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B465547 : Blo 159796 465547 := bstep (se 1 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 465547 = 698321) B698321
theorem B367433 : Blo 159796 367433 := bstep (se 2 (by rfl) ⟨137787, by rfl⟩ : syracuseStep 367433 = 275575) B275575
theorem B5020805 : Blo 159796 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B269743 : Blo 159796 269743 := bstep (se 1 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 269743 = 404615) B404615
theorem B269831 : Blo 159796 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B368225 : Blo 159796 368225 := bstep (se 2 (by rfl) ⟨138084, by rfl⟩ : syracuseStep 368225 = 276169) B276169
theorem B1220345 : Blo 159796 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B270175 : Blo 159796 270175 := bstep (se 1 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 270175 = 405263) B405263
theorem B270263 : Blo 159796 270263 := bstep (se 1 (by rfl) ⟨202697, by rfl⟩ : syracuseStep 270263 = 405395) B405395
theorem B204763 : Blo 159796 204763 := bstep (se 1 (by rfl) ⟨153572, by rfl⟩ : syracuseStep 204763 = 307145) B307145
theorem B205151 : Blo 159796 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B434651 : Blo 159796 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B270857 : Blo 159796 270857 := bstep (se 2 (by rfl) ⟨101571, by rfl⟩ : syracuseStep 270857 = 203143) B203143
theorem B271019 : Blo 159796 271019 := bstep (se 1 (by rfl) ⟨203264, by rfl⟩ : syracuseStep 271019 = 406529) B406529
theorem B1156069 : Blo 159796 1156069 := bstep (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) B216763
theorem B828467 : Blo 159796 828467 := bstep (se 1 (by rfl) ⟨621350, by rfl⟩ : syracuseStep 828467 = 1242701) B1242701
theorem B271417 : Blo 159796 271417 := bstep (se 2 (by rfl) ⟨101781, by rfl⟩ : syracuseStep 271417 = 203563) B203563
theorem B435257 : Blo 159796 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B2663491 : Blo 159796 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B1221803 : Blo 159796 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B304327 : Blo 159796 304327 := bstep (se 1 (by rfl) ⟨228245, by rfl⟩ : syracuseStep 304327 = 456491) B456491
theorem B271559 : Blo 159796 271559 := bstep (se 1 (by rfl) ⟨203669, by rfl⟩ : syracuseStep 271559 = 407339) B407339
theorem B926923 : Blo 159796 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B271721 : Blo 159796 271721 := bstep (se 2 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 271721 = 203791) B203791
theorem B1222289 : Blo 159796 1222289 := bstep (se 2 (by rfl) ⟨458358, by rfl⟩ : syracuseStep 1222289 = 916717) B916717
theorem B272119 : Blo 159796 272119 := bstep (se 1 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 272119 = 408179) B408179
theorem B272315 : Blo 159796 272315 := bstep (se 1 (by rfl) ⟨204236, by rfl⟩ : syracuseStep 272315 = 408473) B408473
theorem B2664485 : Blo 159796 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B272423 : Blo 159796 272423 := bstep (se 1 (by rfl) ⟨204317, by rfl⟩ : syracuseStep 272423 = 408635) B408635
theorem B272713 : Blo 159796 272713 := bstep (se 2 (by rfl) ⟨102267, by rfl⟩ : syracuseStep 272713 = 204535) B204535
theorem B272747 : Blo 159796 272747 := bstep (se 1 (by rfl) ⟨204560, by rfl⟩ : syracuseStep 272747 = 409121) B409121
theorem B240047 : Blo 159796 240047 := bstep (se 1 (by rfl) ⟨180035, by rfl⟩ : syracuseStep 240047 = 360071) B360071
theorem B240137 : Blo 159796 240137 := bstep (se 2 (by rfl) ⟨90051, by rfl⟩ : syracuseStep 240137 = 180103) B180103
theorem B1026593 : Blo 159796 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B240167 : Blo 159796 240167 := bstep (se 1 (by rfl) ⟨180125, by rfl⟩ : syracuseStep 240167 = 360251) B360251
theorem B240251 : Blo 159796 240251 := bstep (se 1 (by rfl) ⟨180188, by rfl⟩ : syracuseStep 240251 = 360377) B360377
theorem B1026695 : Blo 159796 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B993977 : Blo 159796 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B240377 : Blo 159796 240377 := bstep (se 2 (by rfl) ⟨90141, by rfl⟩ : syracuseStep 240377 = 180283) B180283
theorem B273145 : Blo 159796 273145 := bstep (se 2 (by rfl) ⟨102429, by rfl⟩ : syracuseStep 273145 = 204859) B204859
theorem B240479 : Blo 159796 240479 := bstep (se 1 (by rfl) ⟨180359, by rfl⟩ : syracuseStep 240479 = 360719) B360719
theorem B240491 : Blo 159796 240491 := bstep (se 1 (by rfl) ⟨180368, by rfl⟩ : syracuseStep 240491 = 360737) B360737
theorem B273415 : Blo 159796 273415 := bstep (se 1 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 273415 = 410123) B410123
theorem B371719 : Blo 159796 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B1223747 : Blo 159796 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B240719 : Blo 159796 240719 := bstep (se 1 (by rfl) ⟨180539, by rfl⟩ : syracuseStep 240719 = 361079) B361079
theorem B2305219 : Blo 159796 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B240839 : Blo 159796 240839 := bstep (se 1 (by rfl) ⟨180629, by rfl⟩ : syracuseStep 240839 = 361259) B361259
theorem B241001 : Blo 159796 241001 := bstep (se 2 (by rfl) ⟨90375, by rfl⟩ : syracuseStep 241001 = 180751) B180751
theorem B306575 : Blo 159796 306575 := bstep (se 1 (by rfl) ⟨229931, by rfl⟩ : syracuseStep 306575 = 459863) B459863
theorem B241079 : Blo 159796 241079 := bstep (se 1 (by rfl) ⟨180809, by rfl⟩ : syracuseStep 241079 = 361619) B361619
theorem B273847 : Blo 159796 273847 := bstep (se 1 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 273847 = 410771) B410771
theorem B241115 : Blo 159796 241115 := bstep (se 1 (by rfl) ⟨180836, by rfl⟩ : syracuseStep 241115 = 361673) B361673
theorem B274043 : Blo 159796 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B1027799 : Blo 159796 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B241583 : Blo 159796 241583 := bstep (se 1 (by rfl) ⟨181187, by rfl⟩ : syracuseStep 241583 = 362375) B362375
theorem B1028027 : Blo 159796 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B241673 : Blo 159796 241673 := bstep (se 2 (by rfl) ⟨90627, by rfl⟩ : syracuseStep 241673 = 181255) B181255
theorem B274441 : Blo 159796 274441 := bstep (se 2 (by rfl) ⟨102915, by rfl⟩ : syracuseStep 274441 = 205831) B205831
theorem B1224719 : Blo 159796 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B241703 : Blo 159796 241703 := bstep (se 1 (by rfl) ⟨181277, by rfl⟩ : syracuseStep 241703 = 362555) B362555
theorem B241787 : Blo 159796 241787 := bstep (se 1 (by rfl) ⟨181340, by rfl⟩ : syracuseStep 241787 = 362681) B362681
theorem B274603 : Blo 159796 274603 := bstep (se 1 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 274603 = 411905) B411905
theorem B241913 : Blo 159796 241913 := bstep (se 2 (by rfl) ⟨90717, by rfl⟩ : syracuseStep 241913 = 181435) B181435
theorem B242015 : Blo 159796 242015 := bstep (se 1 (by rfl) ⟨181511, by rfl⟩ : syracuseStep 242015 = 363023) B363023
theorem B242027 : Blo 159796 242027 := bstep (se 1 (by rfl) ⟨181520, by rfl⟩ : syracuseStep 242027 = 363041) B363041
theorem B307631 : Blo 159796 307631 := bstep (se 1 (by rfl) ⟨230723, by rfl⟩ : syracuseStep 307631 = 461447) B461447
theorem B274907 : Blo 159796 274907 := bstep (se 1 (by rfl) ⟨206180, by rfl⟩ : syracuseStep 274907 = 412361) B412361
theorem B242255 : Blo 159796 242255 := bstep (se 1 (by rfl) ⟨181691, by rfl⟩ : syracuseStep 242255 = 363383) B363383
theorem B242375 : Blo 159796 242375 := bstep (se 1 (by rfl) ⟨181781, by rfl⟩ : syracuseStep 242375 = 363563) B363563
theorem B275143 : Blo 159796 275143 := bstep (se 1 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 275143 = 412715) B412715
theorem B406367 : Blo 159796 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B308063 : Blo 159796 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B242537 : Blo 159796 242537 := bstep (se 2 (by rfl) ⟨90951, by rfl⟩ : syracuseStep 242537 = 181903) B181903
theorem B275305 : Blo 159796 275305 := bstep (se 2 (by rfl) ⟨103239, by rfl⟩ : syracuseStep 275305 = 206479) B206479
theorem B504737 : Blo 159796 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B242615 : Blo 159796 242615 := bstep (se 1 (by rfl) ⟨181961, by rfl⟩ : syracuseStep 242615 = 363923) B363923
theorem B242651 : Blo 159796 242651 := bstep (se 1 (by rfl) ⟨181988, by rfl⟩ : syracuseStep 242651 = 363977) B363977
theorem B1389635 : Blo 159796 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B1324451 : Blo 159796 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B243119 : Blo 159796 243119 := bstep (se 1 (by rfl) ⟨182339, by rfl⟩ : syracuseStep 243119 = 364679) B364679
theorem B275899 : Blo 159796 275899 := bstep (se 1 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 275899 = 413849) B413849
theorem B243209 : Blo 159796 243209 := bstep (se 2 (by rfl) ⟨91203, by rfl⟩ : syracuseStep 243209 = 182407) B182407
theorem B407065 : Blo 159796 407065 := bstep (se 2 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 407065 = 305299) B305299
theorem B243239 : Blo 159796 243239 := bstep (se 1 (by rfl) ⟨182429, by rfl⟩ : syracuseStep 243239 = 364859) B364859
theorem B276007 : Blo 159796 276007 := bstep (se 1 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 276007 = 414011) B414011
theorem B243323 : Blo 159796 243323 := bstep (se 1 (by rfl) ⟨182492, by rfl⟩ : syracuseStep 243323 = 364985) B364985
theorem B1357511 : Blo 159796 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B243449 : Blo 159796 243449 := bstep (se 2 (by rfl) ⟨91293, by rfl⟩ : syracuseStep 243449 = 182587) B182587
theorem B407369 : Blo 159796 407369 := bstep (se 2 (by rfl) ⟨152763, by rfl⟩ : syracuseStep 407369 = 305527) B305527
theorem B243551 : Blo 159796 243551 := bstep (se 1 (by rfl) ⟨182663, by rfl⟩ : syracuseStep 243551 = 365327) B365327
theorem B243563 : Blo 159796 243563 := bstep (se 1 (by rfl) ⟨182672, by rfl⟩ : syracuseStep 243563 = 365345) B365345
theorem B276331 : Blo 159796 276331 := bstep (se 1 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 276331 = 414497) B414497
theorem B538555 : Blo 159796 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B243791 : Blo 159796 243791 := bstep (se 1 (by rfl) ⟨182843, by rfl⟩ : syracuseStep 243791 = 365687) B365687
theorem B1030259 : Blo 159796 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B243911 : Blo 159796 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B5191937 : Blo 159796 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B244073 : Blo 159796 244073 := bstep (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) B183055
theorem B244151 : Blo 159796 244151 := bstep (se 1 (by rfl) ⟨183113, by rfl⟩ : syracuseStep 244151 = 366227) B366227
theorem B244187 : Blo 159796 244187 := bstep (se 1 (by rfl) ⟨183140, by rfl⟩ : syracuseStep 244187 = 366281) B366281
theorem B342625 : Blo 159796 342625 := bstep (se 2 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 342625 = 256969) B256969
theorem B539351 : Blo 159796 539351 := bstep (se 1 (by rfl) ⟨404513, by rfl⟩ : syracuseStep 539351 = 809027) B809027
theorem B310007 : Blo 159796 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B310159 : Blo 159796 310159 := bstep (se 1 (by rfl) ⟨232619, by rfl⟩ : syracuseStep 310159 = 465239) B465239
theorem B539567 : Blo 159796 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B244655 : Blo 159796 244655 := bstep (se 1 (by rfl) ⟨183491, by rfl⟩ : syracuseStep 244655 = 366983) B366983
theorem B342967 : Blo 159796 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B408503 : Blo 159796 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B244745 : Blo 159796 244745 := bstep (se 2 (by rfl) ⟨91779, by rfl⟩ : syracuseStep 244745 = 183559) B183559
theorem B244775 : Blo 159796 244775 := bstep (se 1 (by rfl) ⟨183581, by rfl⟩ : syracuseStep 244775 = 367163) B367163
theorem B244859 : Blo 159796 244859 := bstep (se 1 (by rfl) ⟨183644, by rfl⟩ : syracuseStep 244859 = 367289) B367289
theorem B244985 : Blo 159796 244985 := bstep (se 2 (by rfl) ⟨91869, by rfl⟩ : syracuseStep 244985 = 183739) B183739
theorem B1228121 : Blo 159796 1228121 := bstep (se 2 (by rfl) ⟨460545, by rfl⟩ : syracuseStep 1228121 = 921091) B921091
theorem B245087 : Blo 159796 245087 := bstep (se 1 (by rfl) ⟨183815, by rfl⟩ : syracuseStep 245087 = 367631) B367631
theorem B245099 : Blo 159796 245099 := bstep (se 1 (by rfl) ⟨183824, by rfl⟩ : syracuseStep 245099 = 367649) B367649
theorem B245327 : Blo 159796 245327 := bstep (se 1 (by rfl) ⟨183995, by rfl⟩ : syracuseStep 245327 = 367991) B367991
theorem B245447 : Blo 159796 245447 := bstep (se 1 (by rfl) ⟨184085, by rfl⟩ : syracuseStep 245447 = 368171) B368171
theorem B245609 : Blo 159796 245609 := bstep (se 2 (by rfl) ⟨92103, by rfl⟩ : syracuseStep 245609 = 184207) B184207
theorem B245687 : Blo 159796 245687 := bstep (se 1 (by rfl) ⟨184265, by rfl⟩ : syracuseStep 245687 = 368531) B368531
theorem B769985 : Blo 159796 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B409607 : Blo 159796 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B409657 : Blo 159796 409657 := bstep (se 2 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 409657 = 307243) B307243
theorem B311545 : Blo 159796 311545 := bstep (se 2 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 311545 = 233659) B233659
theorem B1851659 : Blo 159796 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B409961 : Blo 159796 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B279119 : Blo 159796 279119 := bstep (se 1 (by rfl) ⟨209339, by rfl⟩ : syracuseStep 279119 = 418679) B418679
theorem B180859 : Blo 159796 180859 := bstep (se 1 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 180859 = 271289) B271289
theorem B1393361 : Blo 159796 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B4735705 : Blo 159796 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B1557265 : Blo 159796 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B312329 : Blo 159796 312329 := bstep (se 2 (by rfl) ⟨117123, by rfl⟩ : syracuseStep 312329 = 234247) B234247
theorem B181327 : Blo 159796 181327 := bstep (se 1 (by rfl) ⟨135995, by rfl⟩ : syracuseStep 181327 = 271991) B271991
theorem B541943 : Blo 159796 541943 := bstep (se 1 (by rfl) ⟨406457, by rfl⟩ : syracuseStep 541943 = 812915) B812915
theorem B181723 : Blo 159796 181723 := bstep (se 1 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 181723 = 272585) B272585
theorem B542267 : Blo 159796 542267 := bstep (se 1 (by rfl) ⟨406700, by rfl⟩ : syracuseStep 542267 = 813401) B813401
theorem B411259 : Blo 159796 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B1230551 : Blo 159796 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B542537 : Blo 159796 542537 := bstep (se 2 (by rfl) ⟨203451, by rfl⟩ : syracuseStep 542537 = 406903) B406903
theorem B608107 : Blo 159796 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B182191 : Blo 159796 182191 := bstep (se 1 (by rfl) ⟨136643, by rfl⟩ : syracuseStep 182191 = 273287) B273287
theorem B182623 : Blo 159796 182623 := bstep (se 1 (by rfl) ⟨136967, by rfl⟩ : syracuseStep 182623 = 273935) B273935
theorem B412199 : Blo 159796 412199 := bstep (se 1 (by rfl) ⟨309149, by rfl⟩ : syracuseStep 412199 = 618299) B618299
theorem B182983 : Blo 159796 182983 := bstep (se 1 (by rfl) ⟨137237, by rfl⟩ : syracuseStep 182983 = 274475) B274475
theorem B412523 : Blo 159796 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B543671 : Blo 159796 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B2411693 : Blo 159796 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B413171 : Blo 159796 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B544265 : Blo 159796 544265 := bstep (se 2 (by rfl) ⟨204099, by rfl⟩ : syracuseStep 544265 = 408199) B408199
theorem B183847 : Blo 159796 183847 := bstep (se 1 (by rfl) ⟨137885, by rfl⟩ : syracuseStep 183847 = 275771) B275771
theorem B413383 : Blo 159796 413383 := bstep (se 1 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 413383 = 620075) B620075
theorem B347977 : Blo 159796 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B8376331 : Blo 159796 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B545129 : Blo 159796 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B610841 : Blo 159796 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B1233467 : Blo 159796 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B414305 : Blo 159796 414305 := bstep (se 2 (by rfl) ⟨155364, by rfl⟩ : syracuseStep 414305 = 310729) B310729
theorem B774791 : Blo 159796 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B414407 : Blo 159796 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B578411 : Blo 159796 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B1037231 : Blo 159796 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B447419 : Blo 159796 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B545723 : Blo 159796 545723 := bstep (se 1 (by rfl) ⟨409292, by rfl⟩ : syracuseStep 545723 = 818585) B818585
theorem B513911 : Blo 159796 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B546743 : Blo 159796 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B612467 : Blo 159796 612467 := bstep (se 1 (by rfl) ⟨459350, by rfl⟩ : syracuseStep 612467 = 918701) B918701
theorem B547451 : Blo 159796 547451 := bstep (se 1 (by rfl) ⟨410588, by rfl⟩ : syracuseStep 547451 = 821177) B821177
theorem B1825415 : Blo 159796 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B2611997 : Blo 159796 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B547613 : Blo 159796 547613 := bstep (se 3 (by rfl) ⟨102677, by rfl⟩ : syracuseStep 547613 = 205355) B205355
theorem B613757 : Blo 159796 613757 := bstep (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) B230159
theorem B1039817 : Blo 159796 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B548315 : Blo 159796 548315 := bstep (se 1 (by rfl) ⟨411236, by rfl⟩ : syracuseStep 548315 = 822473) B822473
theorem B384551 : Blo 159796 384551 := bstep (se 1 (by rfl) ⟨288413, by rfl⟩ : syracuseStep 384551 = 576827) B576827
theorem B417419 : Blo 159796 417419 := bstep (se 1 (by rfl) ⟨313064, by rfl⟩ : syracuseStep 417419 = 626129) B626129
theorem B515783 : Blo 159796 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B319339 : Blo 159796 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B974855 : Blo 159796 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B549017 : Blo 159796 549017 := bstep (se 2 (by rfl) ⟨205881, by rfl⟩ : syracuseStep 549017 = 411763) B411763
theorem B975341 : Blo 159796 975341 := bstep (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) B365753
theorem B2089475 : Blo 159796 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1040921 : Blo 159796 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B3105539 : Blo 159796 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B8479667 : Blo 159796 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B22438853 : Blo 159796 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B615671 : Blo 159796 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B550205 : Blo 159796 550205 := bstep (se 3 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 550205 = 206327) B206327
theorem B1763167 : Blo 159796 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1173541 : Blo 159796 1173541 := bstep (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) B220039
theorem B616529 : Blo 159796 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B551069 : Blo 159796 551069 := bstep (se 3 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 551069 = 206651) B206651
theorem B616643 : Blo 159796 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B387433 : Blo 159796 387433 := bstep (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) B290575
theorem B518525 : Blo 159796 518525 := bstep (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) B194447
theorem B4712849 : Blo 159796 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B551609 : Blo 159796 551609 := bstep (se 2 (by rfl) ⟨206853, by rfl⟩ : syracuseStep 551609 = 413707) B413707
theorem B617159 : Blo 159796 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B257033 : Blo 159796 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B552203 : Blo 159796 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B191851 : Blo 159796 191851 := bstep (se 1 (by rfl) ⟨143888, by rfl⟩ : syracuseStep 191851 = 287777) B287777
theorem B5074319 : Blo 159796 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1174985 : Blo 159796 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B552473 : Blo 159796 552473 := bstep (se 2 (by rfl) ⟨207177, by rfl⟩ : syracuseStep 552473 = 414355) B414355
theorem B618131 : Blo 159796 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B618313 : Blo 159796 618313 := bstep (se 2 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 618313 = 463735) B463735
theorem B585647 : Blo 159796 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B389047 : Blo 159796 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B159823 : Blo 159796 159823 := bstep (se 1 (by rfl) ⟨119867, by rfl⟩ : syracuseStep 159823 = 239735) B239735
theorem B159839 : Blo 159796 159839 := bstep (se 1 (by rfl) ⟨119879, by rfl⟩ : syracuseStep 159839 = 239759) B239759
theorem B159867 : Blo 159796 159867 := bstep (se 1 (by rfl) ⟨119900, by rfl⟩ : syracuseStep 159867 = 239801) B239801
theorem B159919 : Blo 159796 159919 := bstep (se 1 (by rfl) ⟨119939, by rfl⟩ : syracuseStep 159919 = 239879) B239879
theorem B159943 : Blo 159796 159943 := bstep (se 1 (by rfl) ⟨119957, by rfl⟩ : syracuseStep 159943 = 239915) B239915
theorem B159963 : Blo 159796 159963 := bstep (se 1 (by rfl) ⟨119972, by rfl⟩ : syracuseStep 159963 = 239945) B239945
theorem B160039 : Blo 159796 160039 := bstep (se 1 (by rfl) ⟨120029, by rfl⟩ : syracuseStep 160039 = 240059) B240059
theorem B160079 : Blo 159796 160079 := bstep (se 1 (by rfl) ⟨120059, by rfl⟩ : syracuseStep 160079 = 240119) B240119
theorem B160095 : Blo 159796 160095 := bstep (se 1 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 160095 = 240143) B240143
theorem B160123 : Blo 159796 160123 := bstep (se 1 (by rfl) ⟨120092, by rfl⟩ : syracuseStep 160123 = 240185) B240185
theorem B586109 : Blo 159796 586109 := bstep (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) B219791
theorem B160175 : Blo 159796 160175 := bstep (se 1 (by rfl) ⟨120131, by rfl⟩ : syracuseStep 160175 = 240263) B240263
theorem B160199 : Blo 159796 160199 := bstep (se 1 (by rfl) ⟨120149, by rfl⟩ : syracuseStep 160199 = 240299) B240299
theorem B160219 : Blo 159796 160219 := bstep (se 1 (by rfl) ⟨120164, by rfl⟩ : syracuseStep 160219 = 240329) B240329
theorem B160295 : Blo 159796 160295 := bstep (se 1 (by rfl) ⟨120221, by rfl⟩ : syracuseStep 160295 = 240443) B240443
theorem B160335 : Blo 159796 160335 := bstep (se 1 (by rfl) ⟨120251, by rfl⟩ : syracuseStep 160335 = 240503) B240503
theorem B160351 : Blo 159796 160351 := bstep (se 1 (by rfl) ⟨120263, by rfl⟩ : syracuseStep 160351 = 240527) B240527
theorem B160379 : Blo 159796 160379 := bstep (se 1 (by rfl) ⟨120284, by rfl⟩ : syracuseStep 160379 = 240569) B240569
theorem B160431 : Blo 159796 160431 := bstep (se 1 (by rfl) ⟨120323, by rfl⟩ : syracuseStep 160431 = 240647) B240647
theorem B160455 : Blo 159796 160455 := bstep (se 1 (by rfl) ⟨120341, by rfl⟩ : syracuseStep 160455 = 240683) B240683
theorem B160475 : Blo 159796 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B7893773 : Blo 159796 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B160551 : Blo 159796 160551 := bstep (se 1 (by rfl) ⟨120413, by rfl⟩ : syracuseStep 160551 = 240827) B240827
theorem B324425 : Blo 159796 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B160591 : Blo 159796 160591 := bstep (se 1 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 160591 = 240887) B240887
theorem B160607 : Blo 159796 160607 := bstep (se 1 (by rfl) ⟨120455, by rfl⟩ : syracuseStep 160607 = 240911) B240911
theorem B160635 : Blo 159796 160635 := bstep (se 1 (by rfl) ⟨120476, by rfl⟩ : syracuseStep 160635 = 240953) B240953
theorem B160687 : Blo 159796 160687 := bstep (se 1 (by rfl) ⟨120515, by rfl⟩ : syracuseStep 160687 = 241031) B241031
theorem B160711 : Blo 159796 160711 := bstep (se 1 (by rfl) ⟨120533, by rfl⟩ : syracuseStep 160711 = 241067) B241067
theorem B160731 : Blo 159796 160731 := bstep (se 1 (by rfl) ⟨120548, by rfl⟩ : syracuseStep 160731 = 241097) B241097
theorem B2814977 : Blo 159796 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B160807 : Blo 159796 160807 := bstep (se 1 (by rfl) ⟨120605, by rfl⟩ : syracuseStep 160807 = 241211) B241211
theorem B160847 : Blo 159796 160847 := bstep (se 1 (by rfl) ⟨120635, by rfl⟩ : syracuseStep 160847 = 241271) B241271
theorem B160863 : Blo 159796 160863 := bstep (se 1 (by rfl) ⟨120647, by rfl⟩ : syracuseStep 160863 = 241295) B241295
theorem B160891 : Blo 159796 160891 := bstep (se 1 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 160891 = 241337) B241337
theorem B160943 : Blo 159796 160943 := bstep (se 1 (by rfl) ⟨120707, by rfl⟩ : syracuseStep 160943 = 241415) B241415
theorem B160967 : Blo 159796 160967 := bstep (se 1 (by rfl) ⟨120725, by rfl⟩ : syracuseStep 160967 = 241451) B241451
theorem B881867 : Blo 159796 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B2323673 : Blo 159796 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B160987 : Blo 159796 160987 := bstep (se 1 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 160987 = 241481) B241481
theorem B1242383 : Blo 159796 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B161063 : Blo 159796 161063 := bstep (se 1 (by rfl) ⟨120797, by rfl⟩ : syracuseStep 161063 = 241595) B241595
theorem B161103 : Blo 159796 161103 := bstep (se 1 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 161103 = 241655) B241655
theorem B161119 : Blo 159796 161119 := bstep (se 1 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 161119 = 241679) B241679
theorem B3536243 : Blo 159796 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B161147 : Blo 159796 161147 := bstep (se 1 (by rfl) ⟨120860, by rfl⟩ : syracuseStep 161147 = 241721) B241721
theorem B3339667 : Blo 159796 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B161199 : Blo 159796 161199 := bstep (se 1 (by rfl) ⟨120899, by rfl⟩ : syracuseStep 161199 = 241799) B241799
theorem B161223 : Blo 159796 161223 := bstep (se 1 (by rfl) ⟨120917, by rfl⟩ : syracuseStep 161223 = 241835) B241835
theorem B161243 : Blo 159796 161243 := bstep (se 1 (by rfl) ⟨120932, by rfl⟩ : syracuseStep 161243 = 241865) B241865
theorem B161319 : Blo 159796 161319 := bstep (se 1 (by rfl) ⟨120989, by rfl⟩ : syracuseStep 161319 = 241979) B241979
theorem B161359 : Blo 159796 161359 := bstep (se 1 (by rfl) ⟨121019, by rfl⟩ : syracuseStep 161359 = 242039) B242039
theorem B161375 : Blo 159796 161375 := bstep (se 1 (by rfl) ⟨121031, by rfl⟩ : syracuseStep 161375 = 242063) B242063
theorem B161403 : Blo 159796 161403 := bstep (se 1 (by rfl) ⟨121052, by rfl⟩ : syracuseStep 161403 = 242105) B242105
theorem B161455 : Blo 159796 161455 := bstep (se 1 (by rfl) ⟨121091, by rfl⟩ : syracuseStep 161455 = 242183) B242183
theorem B161479 : Blo 159796 161479 := bstep (se 1 (by rfl) ⟨121109, by rfl⟩ : syracuseStep 161479 = 242219) B242219
theorem B423623 : Blo 159796 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B620243 : Blo 159796 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B161499 : Blo 159796 161499 := bstep (se 1 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 161499 = 242249) B242249
theorem B161575 : Blo 159796 161575 := bstep (se 1 (by rfl) ⟨121181, by rfl⟩ : syracuseStep 161575 = 242363) B242363
theorem B161615 : Blo 159796 161615 := bstep (se 1 (by rfl) ⟨121211, by rfl⟩ : syracuseStep 161615 = 242423) B242423
theorem B325471 : Blo 159796 325471 := bstep (se 1 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 325471 = 488207) B488207
theorem B161631 : Blo 159796 161631 := bstep (se 1 (by rfl) ⟨121223, by rfl⟩ : syracuseStep 161631 = 242447) B242447
theorem B161659 : Blo 159796 161659 := bstep (se 1 (by rfl) ⟨121244, by rfl⟩ : syracuseStep 161659 = 242489) B242489
theorem B161711 : Blo 159796 161711 := bstep (se 1 (by rfl) ⟨121283, by rfl⟩ : syracuseStep 161711 = 242567) B242567
theorem B161735 : Blo 159796 161735 := bstep (se 1 (by rfl) ⟨121301, by rfl⟩ : syracuseStep 161735 = 242603) B242603
theorem B161755 : Blo 159796 161755 := bstep (se 1 (by rfl) ⟨121316, by rfl⟩ : syracuseStep 161755 = 242633) B242633
theorem B784399 : Blo 159796 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B1112093 : Blo 159796 1112093 := bstep (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) B417035
theorem B161831 : Blo 159796 161831 := bstep (se 1 (by rfl) ⟨121373, by rfl⟩ : syracuseStep 161831 = 242747) B242747
theorem B161871 : Blo 159796 161871 := bstep (se 1 (by rfl) ⟨121403, by rfl⟩ : syracuseStep 161871 = 242807) B242807
theorem B161887 : Blo 159796 161887 := bstep (se 1 (by rfl) ⟨121415, by rfl⟩ : syracuseStep 161887 = 242831) B242831
theorem B161915 : Blo 159796 161915 := bstep (se 1 (by rfl) ⟨121436, by rfl⟩ : syracuseStep 161915 = 242873) B242873
theorem B161967 : Blo 159796 161967 := bstep (se 1 (by rfl) ⟨121475, by rfl⟩ : syracuseStep 161967 = 242951) B242951
theorem B161991 : Blo 159796 161991 := bstep (se 1 (by rfl) ⟨121493, by rfl⟩ : syracuseStep 161991 = 242987) B242987
theorem B162011 : Blo 159796 162011 := bstep (se 1 (by rfl) ⟨121508, by rfl⟩ : syracuseStep 162011 = 243017) B243017
theorem B162087 : Blo 159796 162087 := bstep (se 1 (by rfl) ⟨121565, by rfl⟩ : syracuseStep 162087 = 243131) B243131
theorem B162127 : Blo 159796 162127 := bstep (se 1 (by rfl) ⟨121595, by rfl⟩ : syracuseStep 162127 = 243191) B243191
theorem B162143 : Blo 159796 162143 := bstep (se 1 (by rfl) ⟨121607, by rfl⟩ : syracuseStep 162143 = 243215) B243215
theorem B162171 : Blo 159796 162171 := bstep (se 1 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 162171 = 243257) B243257
theorem B522625 : Blo 159796 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B162223 : Blo 159796 162223 := bstep (se 1 (by rfl) ⟨121667, by rfl⟩ : syracuseStep 162223 = 243335) B243335
theorem B227767 : Blo 159796 227767 := bstep (se 1 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 227767 = 341651) B341651
theorem B162247 : Blo 159796 162247 := bstep (se 1 (by rfl) ⟨121685, by rfl⟩ : syracuseStep 162247 = 243371) B243371
theorem B162267 : Blo 159796 162267 := bstep (se 1 (by rfl) ⟨121700, by rfl⟩ : syracuseStep 162267 = 243401) B243401
theorem B293395 : Blo 159796 293395 := bstep (se 1 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 293395 = 440093) B440093
theorem B1243673 : Blo 159796 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B162343 : Blo 159796 162343 := bstep (se 1 (by rfl) ⟨121757, by rfl⟩ : syracuseStep 162343 = 243515) B243515
theorem B3963437 : Blo 159796 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B162383 : Blo 159796 162383 := bstep (se 1 (by rfl) ⟨121787, by rfl⟩ : syracuseStep 162383 = 243575) B243575
theorem B162399 : Blo 159796 162399 := bstep (se 1 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 162399 = 243599) B243599
theorem B162427 : Blo 159796 162427 := bstep (se 1 (by rfl) ⟨121820, by rfl⟩ : syracuseStep 162427 = 243641) B243641
theorem B162479 : Blo 159796 162479 := bstep (se 1 (by rfl) ⟨121859, by rfl⟩ : syracuseStep 162479 = 243719) B243719
theorem B162503 : Blo 159796 162503 := bstep (se 1 (by rfl) ⟨121877, by rfl⟩ : syracuseStep 162503 = 243755) B243755
theorem B162523 : Blo 159796 162523 := bstep (se 1 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 162523 = 243785) B243785
theorem B162599 : Blo 159796 162599 := bstep (se 1 (by rfl) ⟨121949, by rfl⟩ : syracuseStep 162599 = 243899) B243899
theorem B162639 : Blo 159796 162639 := bstep (se 1 (by rfl) ⟨121979, by rfl⟩ : syracuseStep 162639 = 243959) B243959
theorem B162655 : Blo 159796 162655 := bstep (se 1 (by rfl) ⟨121991, by rfl⟩ : syracuseStep 162655 = 243983) B243983
theorem B162683 : Blo 159796 162683 := bstep (se 1 (by rfl) ⟨122012, by rfl⟩ : syracuseStep 162683 = 244025) B244025
theorem B162735 : Blo 159796 162735 := bstep (se 1 (by rfl) ⟨122051, by rfl⟩ : syracuseStep 162735 = 244103) B244103
theorem B392123 : Blo 159796 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B162759 : Blo 159796 162759 := bstep (se 1 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 162759 = 244139) B244139
theorem B162779 : Blo 159796 162779 := bstep (se 1 (by rfl) ⟨122084, by rfl⟩ : syracuseStep 162779 = 244169) B244169
theorem B162855 : Blo 159796 162855 := bstep (se 1 (by rfl) ⟨122141, by rfl⟩ : syracuseStep 162855 = 244283) B244283
theorem B1178675 : Blo 159796 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B162895 : Blo 159796 162895 := bstep (se 1 (by rfl) ⟨122171, by rfl⟩ : syracuseStep 162895 = 244343) B244343
theorem B523343 : Blo 159796 523343 := bstep (se 1 (by rfl) ⟨392507, by rfl⟩ : syracuseStep 523343 = 785015) B785015
theorem B162911 : Blo 159796 162911 := bstep (se 1 (by rfl) ⟨122183, by rfl⟩ : syracuseStep 162911 = 244367) B244367
theorem B162939 : Blo 159796 162939 := bstep (se 1 (by rfl) ⟨122204, by rfl⟩ : syracuseStep 162939 = 244409) B244409
theorem B162991 : Blo 159796 162991 := bstep (se 1 (by rfl) ⟨122243, by rfl⟩ : syracuseStep 162991 = 244487) B244487
theorem B163015 : Blo 159796 163015 := bstep (se 1 (by rfl) ⟨122261, by rfl⟩ : syracuseStep 163015 = 244523) B244523
theorem B163035 : Blo 159796 163035 := bstep (se 1 (by rfl) ⟨122276, by rfl⟩ : syracuseStep 163035 = 244553) B244553
theorem B818423 : Blo 159796 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B163111 : Blo 159796 163111 := bstep (se 1 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 163111 = 244667) B244667
theorem B163151 : Blo 159796 163151 := bstep (se 1 (by rfl) ⟨122363, by rfl⟩ : syracuseStep 163151 = 244727) B244727
theorem B163167 : Blo 159796 163167 := bstep (se 1 (by rfl) ⟨122375, by rfl⟩ : syracuseStep 163167 = 244751) B244751
theorem B163195 : Blo 159796 163195 := bstep (se 1 (by rfl) ⟨122396, by rfl⟩ : syracuseStep 163195 = 244793) B244793
theorem B163247 : Blo 159796 163247 := bstep (se 1 (by rfl) ⟨122435, by rfl⟩ : syracuseStep 163247 = 244871) B244871
theorem B163271 : Blo 159796 163271 := bstep (se 1 (by rfl) ⟨122453, by rfl⟩ : syracuseStep 163271 = 244907) B244907
theorem B163291 : Blo 159796 163291 := bstep (se 1 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 163291 = 244937) B244937
theorem B359945 : Blo 159796 359945 := bstep (se 2 (by rfl) ⟨134979, by rfl⟩ : syracuseStep 359945 = 269959) B269959
theorem B163367 : Blo 159796 163367 := bstep (se 1 (by rfl) ⟨122525, by rfl⟩ : syracuseStep 163367 = 245051) B245051
theorem B163407 : Blo 159796 163407 := bstep (se 1 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 163407 = 245111) B245111
theorem B163423 : Blo 159796 163423 := bstep (se 1 (by rfl) ⟨122567, by rfl⟩ : syracuseStep 163423 = 245135) B245135
theorem B163451 : Blo 159796 163451 := bstep (se 1 (by rfl) ⟨122588, by rfl⟩ : syracuseStep 163451 = 245177) B245177
theorem B163503 : Blo 159796 163503 := bstep (se 1 (by rfl) ⟨122627, by rfl⟩ : syracuseStep 163503 = 245255) B245255
theorem B163527 : Blo 159796 163527 := bstep (se 1 (by rfl) ⟨122645, by rfl⟩ : syracuseStep 163527 = 245291) B245291
theorem B589511 : Blo 159796 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B294611 : Blo 159796 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B163547 : Blo 159796 163547 := bstep (se 1 (by rfl) ⟨122660, by rfl⟩ : syracuseStep 163547 = 245321) B245321
theorem B818909 : Blo 159796 818909 := bstep (se 3 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 818909 = 307091) B307091
theorem B163623 : Blo 159796 163623 := bstep (se 1 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 163623 = 245435) B245435
theorem B163663 : Blo 159796 163663 := bstep (se 1 (by rfl) ⟨122747, by rfl⟩ : syracuseStep 163663 = 245495) B245495
theorem B360287 : Blo 159796 360287 := bstep (se 1 (by rfl) ⟨270215, by rfl⟩ : syracuseStep 360287 = 540431) B540431
theorem B163679 : Blo 159796 163679 := bstep (se 1 (by rfl) ⟨122759, by rfl⟩ : syracuseStep 163679 = 245519) B245519
theorem B229225 : Blo 159796 229225 := bstep (se 2 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 229225 = 171919) B171919
theorem B163707 : Blo 159796 163707 := bstep (se 1 (by rfl) ⟨122780, by rfl⟩ : syracuseStep 163707 = 245561) B245561
theorem B163759 : Blo 159796 163759 := bstep (se 1 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 163759 = 245639) B245639
theorem B163783 : Blo 159796 163783 := bstep (se 1 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 163783 = 245675) B245675
theorem B229339 : Blo 159796 229339 := bstep (se 1 (by rfl) ⟨172004, by rfl⟩ : syracuseStep 229339 = 344009) B344009
theorem B3539659 : Blo 159796 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B5604173 : Blo 159796 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B361295 : Blo 159796 361295 := bstep (se 1 (by rfl) ⟨270971, by rfl⟩ : syracuseStep 361295 = 541943) B541943
theorem B361511 : Blo 159796 361511 := bstep (se 1 (by rfl) ⟨271133, by rfl⟩ : syracuseStep 361511 = 542267) B542267
theorem B820367 : Blo 159796 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B361691 : Blo 159796 361691 := bstep (se 1 (by rfl) ⟨271268, by rfl⟩ : syracuseStep 361691 = 542537) B542537
theorem B1541425 : Blo 159796 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B361889 : Blo 159796 361889 := bstep (se 2 (by rfl) ⟨135708, by rfl⟩ : syracuseStep 361889 = 271417) B271417
theorem B2230199 : Blo 159796 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B362447 : Blo 159796 362447 := bstep (se 1 (by rfl) ⟨271835, by rfl⟩ : syracuseStep 362447 = 543671) B543671
theorem B1607795 : Blo 159796 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B821501 : Blo 159796 821501 := bstep (se 3 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 821501 = 308063) B308063
theorem B362825 : Blo 159796 362825 := bstep (se 2 (by rfl) ⟨136059, by rfl⟩ : syracuseStep 362825 = 272119) B272119
theorem B362843 : Blo 159796 362843 := bstep (se 1 (by rfl) ⟨272132, by rfl⟩ : syracuseStep 362843 = 544265) B544265
theorem B1378903 : Blo 159796 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B363419 : Blo 159796 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B920591 : Blo 159796 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B822311 : Blo 159796 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B363617 : Blo 159796 363617 := bstep (se 2 (by rfl) ⟨136356, by rfl⟩ : syracuseStep 363617 = 272713) B272713
theorem B691487 : Blo 159796 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B298279 : Blo 159796 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B363815 : Blo 159796 363815 := bstep (se 1 (by rfl) ⟨272861, by rfl⟩ : syracuseStep 363815 = 545723) B545723
theorem B3313021 : Blo 159796 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B593351 : Blo 159796 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B396895 : Blo 159796 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B364193 : Blo 159796 364193 := bstep (se 2 (by rfl) ⟨136572, by rfl⟩ : syracuseStep 364193 = 273145) B273145
theorem B364495 : Blo 159796 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B364553 : Blo 159796 364553 := bstep (se 2 (by rfl) ⟨136707, by rfl⟩ : syracuseStep 364553 = 273415) B273415
theorem B364967 : Blo 159796 364967 := bstep (se 1 (by rfl) ⟨273725, by rfl⟩ : syracuseStep 364967 = 547451) B547451
theorem B1216943 : Blo 159796 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B1741331 : Blo 159796 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B365075 : Blo 159796 365075 := bstep (se 1 (by rfl) ⟨273806, by rfl⟩ : syracuseStep 365075 = 547613) B547613
theorem B365129 : Blo 159796 365129 := bstep (se 2 (by rfl) ⟨136923, by rfl⟩ : syracuseStep 365129 = 273847) B273847
theorem B3347203 : Blo 159796 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B693211 : Blo 159796 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B365543 : Blo 159796 365543 := bstep (se 1 (by rfl) ⟨274157, by rfl⟩ : syracuseStep 365543 = 548315) B548315
theorem B463969 : Blo 159796 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B824417 : Blo 159796 824417 := bstep (se 2 (by rfl) ⟨309156, by rfl⟩ : syracuseStep 824417 = 618313) B618313
theorem B365921 : Blo 159796 365921 := bstep (se 2 (by rfl) ⟨137220, by rfl⟩ : syracuseStep 365921 = 274441) B274441
theorem B366011 : Blo 159796 366011 := bstep (se 1 (by rfl) ⟨274508, by rfl⟩ : syracuseStep 366011 = 549017) B549017
theorem B1644077 : Blo 159796 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B366137 : Blo 159796 366137 := bstep (se 2 (by rfl) ⟨137301, by rfl⟩ : syracuseStep 366137 = 274603) B274603
theorem B693947 : Blo 159796 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B2070359 : Blo 159796 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B366803 : Blo 159796 366803 := bstep (se 1 (by rfl) ⟨275102, by rfl⟩ : syracuseStep 366803 = 550205) B550205
theorem B366857 : Blo 159796 366857 := bstep (se 2 (by rfl) ⟨137571, by rfl⟩ : syracuseStep 366857 = 275143) B275143
theorem B367073 : Blo 159796 367073 := bstep (se 2 (by rfl) ⟨137652, by rfl⟩ : syracuseStep 367073 = 275305) B275305
theorem B1776323 : Blo 159796 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B367379 : Blo 159796 367379 := bstep (se 1 (by rfl) ⟨275534, by rfl⟩ : syracuseStep 367379 = 551069) B551069
theorem B662651 : Blo 159796 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B367739 : Blo 159796 367739 := bstep (se 1 (by rfl) ⟨275804, by rfl⟩ : syracuseStep 367739 = 551609) B551609
theorem B1023205 : Blo 159796 1023205 := bstep (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) B191851
theorem B367865 : Blo 159796 367865 := bstep (se 2 (by rfl) ⟨137949, by rfl⟩ : syracuseStep 367865 = 275899) B275899
theorem B826685 : Blo 159796 826685 := bstep (se 3 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 826685 = 310007) B310007
theorem B368009 : Blo 159796 368009 := bstep (se 2 (by rfl) ⟨138003, by rfl⟩ : syracuseStep 368009 = 276007) B276007
theorem B368135 : Blo 159796 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B204383 : Blo 159796 204383 := bstep (se 1 (by rfl) ⟨153287, by rfl⟩ : syracuseStep 204383 = 306575) B306575
theorem B3382879 : Blo 159796 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B368315 : Blo 159796 368315 := bstep (se 1 (by rfl) ⟨276236, by rfl⟩ : syracuseStep 368315 = 552473) B552473
theorem B270121 : Blo 159796 270121 := bstep (se 2 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 270121 = 202591) B202591
theorem B433961 : Blo 159796 433961 := bstep (se 2 (by rfl) ⟨162735, by rfl⟩ : syracuseStep 433961 = 325471) B325471
theorem B368441 : Blo 159796 368441 := bstep (se 2 (by rfl) ⟨138165, by rfl⟩ : syracuseStep 368441 = 276331) B276331
theorem B205087 : Blo 159796 205087 := bstep (se 1 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 205087 = 307631) B307631
theorem B696833 : Blo 159796 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B270911 : Blo 159796 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B303689 : Blo 159796 303689 := bstep (se 2 (by rfl) ⟨113883, by rfl⟩ : syracuseStep 303689 = 227767) B227767
theorem B336491 : Blo 159796 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B1876651 : Blo 159796 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B926423 : Blo 159796 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B1549115 : Blo 159796 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B271579 : Blo 159796 271579 := bstep (se 1 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 271579 = 407369) B407369
theorem B829115 : Blo 159796 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B272335 : Blo 159796 272335 := bstep (se 1 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 272335 = 408503) B408503
theorem B239963 : Blo 159796 239963 := bstep (se 1 (by rfl) ⟨179972, by rfl⟩ : syracuseStep 239963 = 359945) B359945
theorem B305633 : Blo 159796 305633 := bstep (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) B229225
theorem B240191 : Blo 159796 240191 := bstep (se 1 (by rfl) ⟨180143, by rfl⟩ : syracuseStep 240191 = 360287) B360287
theorem B305785 : Blo 159796 305785 := bstep (se 2 (by rfl) ⟨114669, by rfl⟩ : syracuseStep 305785 = 229339) B229339
theorem B273017 : Blo 159796 273017 := bstep (se 2 (by rfl) ⟨102381, by rfl⟩ : syracuseStep 273017 = 204763) B204763
theorem B1485485 : Blo 159796 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B273071 : Blo 159796 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B240311 : Blo 159796 240311 := bstep (se 1 (by rfl) ⟨180233, by rfl⟩ : syracuseStep 240311 = 360467) B360467
theorem B240539 : Blo 159796 240539 := bstep (se 1 (by rfl) ⟨180404, by rfl⟩ : syracuseStep 240539 = 360809) B360809
theorem B273307 : Blo 159796 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B928907 : Blo 159796 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B240935 : Blo 159796 240935 := bstep (se 1 (by rfl) ⟨180701, by rfl⟩ : syracuseStep 240935 = 361403) B361403
theorem B208219 : Blo 159796 208219 := bstep (se 1 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 208219 = 312329) B312329
theorem B241019 : Blo 159796 241019 := bstep (se 1 (by rfl) ⟨180764, by rfl⟩ : syracuseStep 241019 = 361529) B361529
theorem B241145 : Blo 159796 241145 := bstep (se 2 (by rfl) ⟨90429, by rfl⟩ : syracuseStep 241145 = 180859) B180859
theorem B241247 : Blo 159796 241247 := bstep (se 1 (by rfl) ⟨180935, by rfl⟩ : syracuseStep 241247 = 361871) B361871
theorem B2076353 : Blo 159796 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B306985 : Blo 159796 306985 := bstep (se 2 (by rfl) ⟨115119, by rfl⟩ : syracuseStep 306985 = 230239) B230239
theorem B241463 : Blo 159796 241463 := bstep (se 1 (by rfl) ⟨181097, by rfl⟩ : syracuseStep 241463 = 362195) B362195
theorem B1159069 : Blo 159796 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B3551321 : Blo 159796 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B241769 : Blo 159796 241769 := bstep (se 2 (by rfl) ⟨90663, by rfl⟩ : syracuseStep 241769 = 181327) B181327
theorem B405769 : Blo 159796 405769 := bstep (se 2 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 405769 = 304327) B304327
theorem B307547 : Blo 159796 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B274799 : Blo 159796 274799 := bstep (se 1 (by rfl) ⟨206099, by rfl⟩ : syracuseStep 274799 = 412199) B412199
theorem B242087 : Blo 159796 242087 := bstep (se 1 (by rfl) ⟨181565, by rfl⟩ : syracuseStep 242087 = 363131) B363131
theorem B242171 : Blo 159796 242171 := bstep (se 1 (by rfl) ⟨181628, by rfl⟩ : syracuseStep 242171 = 363257) B363257
theorem B307775 : Blo 159796 307775 := bstep (se 1 (by rfl) ⟨230831, by rfl⟩ : syracuseStep 307775 = 461663) B461663
theorem B275015 : Blo 159796 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B242297 : Blo 159796 242297 := bstep (se 2 (by rfl) ⟨90861, by rfl⟩ : syracuseStep 242297 = 181723) B181723
theorem B242351 : Blo 159796 242351 := bstep (se 1 (by rfl) ⟨181763, by rfl⟩ : syracuseStep 242351 = 363527) B363527
theorem B242399 : Blo 159796 242399 := bstep (se 1 (by rfl) ⟨181799, by rfl⟩ : syracuseStep 242399 = 363599) B363599
theorem B242663 : Blo 159796 242663 := bstep (se 1 (by rfl) ⟨181997, by rfl⟩ : syracuseStep 242663 = 363995) B363995
theorem B308215 : Blo 159796 308215 := bstep (se 1 (by rfl) ⟨231161, by rfl⟩ : syracuseStep 308215 = 462323) B462323
theorem B275447 : Blo 159796 275447 := bstep (se 1 (by rfl) ⟨206585, by rfl⟩ : syracuseStep 275447 = 413171) B413171
theorem B308443 : Blo 159796 308443 := bstep (se 1 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 308443 = 462665) B462665
theorem B242921 : Blo 159796 242921 := bstep (se 2 (by rfl) ⟨91095, by rfl⟩ : syracuseStep 242921 = 182191) B182191
theorem B242975 : Blo 159796 242975 := bstep (se 1 (by rfl) ⟨182231, by rfl⟩ : syracuseStep 242975 = 364463) B364463
theorem B308519 : Blo 159796 308519 := bstep (se 1 (by rfl) ⟨231389, by rfl⟩ : syracuseStep 308519 = 462779) B462779
theorem B308603 : Blo 159796 308603 := bstep (se 1 (by rfl) ⟨231452, by rfl⟩ : syracuseStep 308603 = 462905) B462905
theorem B1226177 : Blo 159796 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B243143 : Blo 159796 243143 := bstep (se 1 (by rfl) ⟨182357, by rfl⟩ : syracuseStep 243143 = 364715) B364715
theorem B407227 : Blo 159796 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B276203 : Blo 159796 276203 := bstep (se 1 (by rfl) ⟨207152, by rfl⟩ : syracuseStep 276203 = 414305) B414305
theorem B243497 : Blo 159796 243497 := bstep (se 2 (by rfl) ⟨91311, by rfl⟩ : syracuseStep 243497 = 182623) B182623
theorem B243503 : Blo 159796 243503 := bstep (se 1 (by rfl) ⟨182627, by rfl⟩ : syracuseStep 243503 = 365255) B365255
theorem B243977 : Blo 159796 243977 := bstep (se 2 (by rfl) ⟨91491, by rfl⟩ : syracuseStep 243977 = 182983) B182983
theorem B244079 : Blo 159796 244079 := bstep (se 1 (by rfl) ⟨183059, by rfl⟩ : syracuseStep 244079 = 366119) B366119
theorem B244295 : Blo 159796 244295 := bstep (se 1 (by rfl) ⟨183221, by rfl⟩ : syracuseStep 244295 = 366443) B366443
theorem B244331 : Blo 159796 244331 := bstep (se 1 (by rfl) ⟨183248, by rfl⟩ : syracuseStep 244331 = 366497) B366497
theorem B408311 : Blo 159796 408311 := bstep (se 1 (by rfl) ⟨306233, by rfl⟩ : syracuseStep 408311 = 612467) B612467
theorem B768791 : Blo 159796 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B244559 : Blo 159796 244559 := bstep (se 1 (by rfl) ⟨183419, by rfl⟩ : syracuseStep 244559 = 366839) B366839
theorem B539837 : Blo 159796 539837 := bstep (se 3 (by rfl) ⟨101219, by rfl⟩ : syracuseStep 539837 = 202439) B202439
theorem B244955 : Blo 159796 244955 := bstep (se 1 (by rfl) ⟨183716, by rfl⟩ : syracuseStep 244955 = 367433) B367433
theorem B245129 : Blo 159796 245129 := bstep (se 2 (by rfl) ⟨91923, by rfl⟩ : syracuseStep 245129 = 183847) B183847
theorem B409171 : Blo 159796 409171 := bstep (se 1 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 409171 = 613757) B613757
theorem B179887 : Blo 159796 179887 := bstep (se 1 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 179887 = 269831) B269831
theorem B245483 : Blo 159796 245483 := bstep (se 1 (by rfl) ⟨184112, by rfl⟩ : syracuseStep 245483 = 368225) B368225
theorem B278279 : Blo 159796 278279 := bstep (se 1 (by rfl) ⟨208709, by rfl⟩ : syracuseStep 278279 = 417419) B417419
theorem B343855 : Blo 159796 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B442169 : Blo 159796 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B180175 : Blo 159796 180175 := bstep (se 1 (by rfl) ⟨135131, by rfl⟩ : syracuseStep 180175 = 270263) B270263
theorem B1982501 : Blo 159796 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B1392983 : Blo 159796 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B180571 : Blo 159796 180571 := bstep (se 1 (by rfl) ⟨135428, by rfl⟩ : syracuseStep 180571 = 270857) B270857
theorem B180679 : Blo 159796 180679 := bstep (se 1 (by rfl) ⟨135509, by rfl⟩ : syracuseStep 180679 = 271019) B271019
theorem B5653111 : Blo 159796 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B14959235 : Blo 159796 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B441762497 : Blo 159796 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B181039 : Blo 159796 181039 := bstep (se 1 (by rfl) ⟨135779, by rfl⟩ : syracuseStep 181039 = 271559) B271559
theorem B410447 : Blo 159796 410447 := bstep (se 1 (by rfl) ⟨307835, by rfl⟩ : syracuseStep 410447 = 615671) B615671
theorem B181147 : Blo 159796 181147 := bstep (se 1 (by rfl) ⟨135860, by rfl⟩ : syracuseStep 181147 = 271721) B271721
theorem B181543 : Blo 159796 181543 := bstep (se 1 (by rfl) ⟨136157, by rfl⟩ : syracuseStep 181543 = 272315) B272315
theorem B181615 : Blo 159796 181615 := bstep (se 1 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 181615 = 272423) B272423
theorem B411095 : Blo 159796 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B181831 : Blo 159796 181831 := bstep (se 1 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 181831 = 272747) B272747
theorem B345683 : Blo 159796 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B1853117 : Blo 159796 1853117 := bstep (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) B694919
theorem B411439 : Blo 159796 411439 := bstep (se 1 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 411439 = 617159) B617159
theorem B542753 : Blo 159796 542753 := bstep (se 2 (by rfl) ⟨203532, by rfl⟩ : syracuseStep 542753 = 407065) B407065
theorem B182695 : Blo 159796 182695 := bstep (se 1 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 182695 = 274043) B274043
theorem B412087 : Blo 159796 412087 := bstep (se 1 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 412087 = 618131) B618131
theorem B183271 : Blo 159796 183271 := bstep (se 1 (by rfl) ⟨137453, by rfl⟩ : syracuseStep 183271 = 274907) B274907
theorem B5262515 : Blo 159796 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B216283 : Blo 159796 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B282415 : Blo 159796 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B413495 : Blo 159796 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B413545 : Blo 159796 413545 := bstep (se 2 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 413545 = 310159) B310159
theorem B741395 : Blo 159796 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B3461291 : Blo 159796 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B4378853 : Blo 159796 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B2642291 : Blo 159796 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B348895 : Blo 159796 348895 := bstep (se 1 (by rfl) ⟨261671, by rfl⟩ : syracuseStep 348895 = 523343) B523343
theorem B545615 : Blo 159796 545615 := bstep (se 1 (by rfl) ⟨409211, by rfl⟩ : syracuseStep 545615 = 818423) B818423
theorem B545939 : Blo 159796 545939 := bstep (se 1 (by rfl) ⟨409454, by rfl⟩ : syracuseStep 545939 = 818909) B818909
theorem B513323 : Blo 159796 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B546209 : Blo 159796 546209 := bstep (se 2 (by rfl) ⟨204828, by rfl⟩ : syracuseStep 546209 = 409657) B409657
theorem B1234439 : Blo 159796 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B186079 : Blo 159796 186079 := bstep (se 1 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 186079 = 279119) B279119
theorem B743255 : Blo 159796 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B612481 : Blo 159796 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B547069 : Blo 159796 547069 := bstep (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) B205151
theorem B6314273 : Blo 159796 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B416111 : Blo 159796 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B744059 : Blo 159796 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B1661573 : Blo 159796 1661573 := bstep (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) B311545
theorem B1235897 : Blo 159796 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B809999 : Blo 159796 809999 := bstep (se 1 (by rfl) ⟨607499, by rfl⟩ : syracuseStep 809999 = 1214999) B1214999
theorem B1105085 : Blo 159796 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B548345 : Blo 159796 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B2350889 : Blo 159796 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B810809 : Blo 159796 810809 := bstep (se 2 (by rfl) ⟨304053, by rfl⟩ : syracuseStep 810809 = 608107) B608107
theorem B876395 : Blo 159796 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B614425 : Blo 159796 614425 := bstep (se 2 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 614425 = 460819) B460819
theorem B1564721 : Blo 159796 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B614729 : Blo 159796 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B516527 : Blo 159796 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B516577 : Blo 159796 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B549395 : Blo 159796 549395 := bstep (se 1 (by rfl) ⟨412046, by rfl⟩ : syracuseStep 549395 = 824093) B824093
theorem B385607 : Blo 159796 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B1532903 : Blo 159796 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B3531869 : Blo 159796 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B288031 : Blo 159796 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B615869 : Blo 159796 615869 := bstep (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) B230951
theorem B3073625 : Blo 159796 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B551177 : Blo 159796 551177 := bstep (se 2 (by rfl) ⟨206691, by rfl⟩ : syracuseStep 551177 = 413383) B413383
theorem B1370429 : Blo 159796 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B256367 : Blo 159796 256367 := bstep (se 1 (by rfl) ⟨192275, by rfl⟩ : syracuseStep 256367 = 384551) B384551
theorem B813563 : Blo 159796 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B518729 : Blo 159796 518729 := bstep (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) B389047
theorem B649903 : Blo 159796 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B11168441 : Blo 159796 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B617341 : Blo 159796 617341 := bstep (se 3 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 617341 = 231503) B231503
theorem B650227 : Blo 159796 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B552311 : Blo 159796 552311 := bstep (se 1 (by rfl) ⟨414233, by rfl⟩ : syracuseStep 552311 = 828467) B828467
theorem B290171 : Blo 159796 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B814535 : Blo 159796 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B814859 : Blo 159796 814859 := bstep (se 1 (by rfl) ⟨611144, by rfl⟩ : syracuseStep 814859 = 1222289) B1222289
theorem B3141899 : Blo 159796 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B160031 : Blo 159796 160031 := bstep (se 1 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 160031 = 240047) B240047
theorem B160091 : Blo 159796 160091 := bstep (se 1 (by rfl) ⟨120068, by rfl⟩ : syracuseStep 160091 = 240137) B240137
theorem B684395 : Blo 159796 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B160111 : Blo 159796 160111 := bstep (se 1 (by rfl) ⟨120083, by rfl⟩ : syracuseStep 160111 = 240167) B240167
theorem B160167 : Blo 159796 160167 := bstep (se 1 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 160167 = 240251) B240251
theorem B684463 : Blo 159796 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B160251 : Blo 159796 160251 := bstep (se 1 (by rfl) ⟨120188, by rfl⟩ : syracuseStep 160251 = 240377) B240377
theorem B4452889 : Blo 159796 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B160319 : Blo 159796 160319 := bstep (se 1 (by rfl) ⟨120239, by rfl⟩ : syracuseStep 160319 = 240479) B240479
theorem B160327 : Blo 159796 160327 := bstep (se 1 (by rfl) ⟨120245, by rfl⟩ : syracuseStep 160327 = 240491) B240491
theorem B7959161 : Blo 159796 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B815831 : Blo 159796 815831 := bstep (se 1 (by rfl) ⟨611873, by rfl⟩ : syracuseStep 815831 = 1223747) B1223747
theorem B160479 : Blo 159796 160479 := bstep (se 1 (by rfl) ⟨120359, by rfl⟩ : syracuseStep 160479 = 240719) B240719
theorem B14480117 : Blo 159796 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B160559 : Blo 159796 160559 := bstep (se 1 (by rfl) ⟨120419, by rfl⟩ : syracuseStep 160559 = 240839) B240839
theorem B160667 : Blo 159796 160667 := bstep (se 1 (by rfl) ⟨120500, by rfl⟩ : syracuseStep 160667 = 241001) B241001
theorem B160719 : Blo 159796 160719 := bstep (se 1 (by rfl) ⟨120539, by rfl⟩ : syracuseStep 160719 = 241079) B241079
theorem B783323 : Blo 159796 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B160743 : Blo 159796 160743 := bstep (se 1 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 160743 = 241115) B241115
theorem B685199 : Blo 159796 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B718073 : Blo 159796 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B161055 : Blo 159796 161055 := bstep (se 1 (by rfl) ⟨120791, by rfl⟩ : syracuseStep 161055 = 241583) B241583
theorem B390431 : Blo 159796 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B685351 : Blo 159796 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B161115 : Blo 159796 161115 := bstep (se 1 (by rfl) ⟨120836, by rfl⟩ : syracuseStep 161115 = 241673) B241673
theorem B816479 : Blo 159796 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B1045865 : Blo 159796 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B685421 : Blo 159796 685421 := bstep (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) B257033
theorem B161135 : Blo 159796 161135 := bstep (se 1 (by rfl) ⟨120851, by rfl⟩ : syracuseStep 161135 = 241703) B241703
theorem B161191 : Blo 159796 161191 := bstep (se 1 (by rfl) ⟨120893, by rfl⟩ : syracuseStep 161191 = 241787) B241787
theorem B161275 : Blo 159796 161275 := bstep (se 1 (by rfl) ⟨120956, by rfl⟩ : syracuseStep 161275 = 241913) B241913
theorem B161343 : Blo 159796 161343 := bstep (se 1 (by rfl) ⟨121007, by rfl⟩ : syracuseStep 161343 = 242015) B242015
theorem B161351 : Blo 159796 161351 := bstep (se 1 (by rfl) ⟨121013, by rfl⟩ : syracuseStep 161351 = 242027) B242027
theorem B390739 : Blo 159796 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B161503 : Blo 159796 161503 := bstep (se 1 (by rfl) ⟨121127, by rfl⟩ : syracuseStep 161503 = 242255) B242255
theorem B161583 : Blo 159796 161583 := bstep (se 1 (by rfl) ⟨121187, by rfl⟩ : syracuseStep 161583 = 242375) B242375
theorem B161691 : Blo 159796 161691 := bstep (se 1 (by rfl) ⟨121268, by rfl⟩ : syracuseStep 161691 = 242537) B242537
theorem B161743 : Blo 159796 161743 := bstep (se 1 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 161743 = 242615) B242615
theorem B161767 : Blo 159796 161767 := bstep (se 1 (by rfl) ⟨121325, by rfl⟩ : syracuseStep 161767 = 242651) B242651
theorem B391193 : Blo 159796 391193 := bstep (se 2 (by rfl) ⟨146697, by rfl⟩ : syracuseStep 391193 = 293395) B293395
theorem B456833 : Blo 159796 456833 := bstep (se 2 (by rfl) ⟨171312, by rfl⟩ : syracuseStep 456833 = 342625) B342625
theorem B587911 : Blo 159796 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B620729 : Blo 159796 620729 := bstep (se 2 (by rfl) ⟨232773, by rfl⟩ : syracuseStep 620729 = 465547) B465547
theorem B2357495 : Blo 159796 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B162079 : Blo 159796 162079 := bstep (se 1 (by rfl) ⟨121559, by rfl⟩ : syracuseStep 162079 = 243119) B243119
theorem B162139 : Blo 159796 162139 := bstep (se 1 (by rfl) ⟨121604, by rfl⟩ : syracuseStep 162139 = 243209) B243209
theorem B162159 : Blo 159796 162159 := bstep (se 1 (by rfl) ⟨121619, by rfl⟩ : syracuseStep 162159 = 243239) B243239
theorem B162215 : Blo 159796 162215 := bstep (se 1 (by rfl) ⟨121661, by rfl⟩ : syracuseStep 162215 = 243323) B243323
theorem B162299 : Blo 159796 162299 := bstep (se 1 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 162299 = 243449) B243449
theorem B162367 : Blo 159796 162367 := bstep (se 1 (by rfl) ⟨121775, by rfl⟩ : syracuseStep 162367 = 243551) B243551
theorem B162375 : Blo 159796 162375 := bstep (se 1 (by rfl) ⟨121781, by rfl⟩ : syracuseStep 162375 = 243563) B243563
theorem B457289 : Blo 159796 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B162527 : Blo 159796 162527 := bstep (se 1 (by rfl) ⟨121895, by rfl⟩ : syracuseStep 162527 = 243791) B243791
theorem B686839 : Blo 159796 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B162607 : Blo 159796 162607 := bstep (se 1 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 162607 = 243911) B243911
theorem B162715 : Blo 159796 162715 := bstep (se 1 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 162715 = 244073) B244073
theorem B162767 : Blo 159796 162767 := bstep (se 1 (by rfl) ⟨122075, by rfl⟩ : syracuseStep 162767 = 244151) B244151
theorem B162791 : Blo 159796 162791 := bstep (se 1 (by rfl) ⟨122093, by rfl⟩ : syracuseStep 162791 = 244187) B244187
theorem B359567 : Blo 159796 359567 := bstep (se 1 (by rfl) ⟨269675, by rfl⟩ : syracuseStep 359567 = 539351) B539351
theorem B785629 : Blo 159796 785629 := bstep (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) B294611
theorem B359657 : Blo 159796 359657 := bstep (se 2 (by rfl) ⟨134871, by rfl⟩ : syracuseStep 359657 = 269743) B269743
theorem B359711 : Blo 159796 359711 := bstep (se 1 (by rfl) ⟨269783, by rfl⟩ : syracuseStep 359711 = 539567) B539567
theorem B163103 : Blo 159796 163103 := bstep (se 1 (by rfl) ⟨122327, by rfl⟩ : syracuseStep 163103 = 244655) B244655
theorem B261415 : Blo 159796 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B163163 : Blo 159796 163163 := bstep (se 1 (by rfl) ⟨122372, by rfl⟩ : syracuseStep 163163 = 244745) B244745
theorem B163183 : Blo 159796 163183 := bstep (se 1 (by rfl) ⟨122387, by rfl⟩ : syracuseStep 163183 = 244775) B244775
theorem B785783 : Blo 159796 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B163239 : Blo 159796 163239 := bstep (se 1 (by rfl) ⟨122429, by rfl⟩ : syracuseStep 163239 = 244859) B244859
theorem B163323 : Blo 159796 163323 := bstep (se 1 (by rfl) ⟨122492, by rfl⟩ : syracuseStep 163323 = 244985) B244985
theorem B818747 : Blo 159796 818747 := bstep (se 1 (by rfl) ⟨614060, by rfl⟩ : syracuseStep 818747 = 1228121) B1228121
theorem B163391 : Blo 159796 163391 := bstep (se 1 (by rfl) ⟨122543, by rfl⟩ : syracuseStep 163391 = 245087) B245087
theorem B163399 : Blo 159796 163399 := bstep (se 1 (by rfl) ⟨122549, by rfl⟩ : syracuseStep 163399 = 245099) B245099
theorem B163551 : Blo 159796 163551 := bstep (se 1 (by rfl) ⟨122663, by rfl⟩ : syracuseStep 163551 = 245327) B245327
theorem B360233 : Blo 159796 360233 := bstep (se 2 (by rfl) ⟨135087, by rfl⟩ : syracuseStep 360233 = 270175) B270175
theorem B393007 : Blo 159796 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B163631 : Blo 159796 163631 := bstep (se 1 (by rfl) ⟨122723, by rfl⟩ : syracuseStep 163631 = 245447) B245447
theorem B425785 : Blo 159796 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B163739 : Blo 159796 163739 := bstep (se 1 (by rfl) ⟨122804, by rfl⟩ : syracuseStep 163739 = 245609) B245609
theorem B163791 : Blo 159796 163791 := bstep (se 1 (by rfl) ⟨122843, by rfl⟩ : syracuseStep 163791 = 245687) B245687
theorem B819233 : Blo 159796 819233 := bstep (se 2 (by rfl) ⟨307212, by rfl⟩ : syracuseStep 819233 = 614425) B614425
theorem B9470189 : Blo 159796 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B3736115 : Blo 159796 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B688769 : Blo 159796 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B7537481 : Blo 159796 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B4719545 : Blo 159796 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B230455 : Blo 159796 230455 := bstep (se 1 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 230455 = 345683) B345683
theorem B361835 : Blo 159796 361835 := bstep (se 1 (by rfl) ⟨271376, by rfl⟩ : syracuseStep 361835 = 542753) B542753
theorem B362105 : Blo 159796 362105 := bstep (se 2 (by rfl) ⟨135789, by rfl⟩ : syracuseStep 362105 = 271579) B271579
theorem B3508343 : Blo 159796 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B460991 : Blo 159796 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B395567 : Blo 159796 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B363113 : Blo 159796 363113 := bstep (se 2 (by rfl) ⟨136167, by rfl⟩ : syracuseStep 363113 = 272335) B272335
theorem B494263 : Blo 159796 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B2919235 : Blo 159796 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B363743 : Blo 159796 363743 := bstep (se 1 (by rfl) ⟨272807, by rfl⟩ : syracuseStep 363743 = 545615) B545615
theorem B363959 : Blo 159796 363959 := bstep (se 1 (by rfl) ⟨272969, by rfl⟩ : syracuseStep 363959 = 545939) B545939
theorem B1838537 : Blo 159796 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B364139 : Blo 159796 364139 := bstep (se 1 (by rfl) ⟨273104, by rfl⟩ : syracuseStep 364139 = 546209) B546209
theorem B822959 : Blo 159796 822959 := bstep (se 1 (by rfl) ⟨617219, by rfl⟩ : syracuseStep 822959 = 1234439) B1234439
theorem B462631 : Blo 159796 462631 := bstep (se 1 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 462631 = 693947) B693947
theorem B823121 : Blo 159796 823121 := bstep (se 2 (by rfl) ⟨308670, by rfl⟩ : syracuseStep 823121 = 617341) B617341
theorem B364409 : Blo 159796 364409 := bstep (se 2 (by rfl) ⟨136653, by rfl⟩ : syracuseStep 364409 = 273307) B273307
theorem B1380239 : Blo 159796 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B495503 : Blo 159796 495503 := bstep (se 1 (by rfl) ⟨371627, by rfl⟩ : syracuseStep 495503 = 743255) B743255
theorem B496039 : Blo 159796 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B1184215 : Blo 159796 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B823931 : Blo 159796 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B529193 : Blo 159796 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B365563 : Blo 159796 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B1545425 : Blo 159796 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B464555 : Blo 159796 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B366263 : Blo 159796 366263 := bstep (se 1 (by rfl) ⟨274697, by rfl⟩ : syracuseStep 366263 = 549395) B549395
theorem B5937185 : Blo 159796 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B465193 : Blo 159796 465193 := bstep (se 2 (by rfl) ⟨174447, by rfl⟩ : syracuseStep 465193 = 348895) B348895
theorem B4462937 : Blo 159796 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B924281 : Blo 159796 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B367451 : Blo 159796 367451 := bstep (se 1 (by rfl) ⟨275588, by rfl⟩ : syracuseStep 367451 = 551177) B551177
theorem B1383277 : Blo 159796 1383277 := bstep (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) B518729
theorem B170911 : Blo 159796 170911 := bstep (se 1 (by rfl) ⟨128183, by rfl⟩ : syracuseStep 170911 = 256367) B256367
theorem B990323 : Blo 159796 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B7445627 : Blo 159796 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B368207 : Blo 159796 368207 := bstep (se 1 (by rfl) ⟨276155, by rfl⟩ : syracuseStep 368207 = 552311) B552311
theorem B1384235 : Blo 159796 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B205031 : Blo 159796 205031 := bstep (se 1 (by rfl) ⟨153773, by rfl⟩ : syracuseStep 205031 = 307547) B307547
theorem B729425 : Blo 159796 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B205183 : Blo 159796 205183 := bstep (se 1 (by rfl) ⟨153887, by rfl⟩ : syracuseStep 205183 = 307775) B307775
theorem B205679 : Blo 159796 205679 := bstep (se 1 (by rfl) ⟨154259, by rfl⟩ : syracuseStep 205679 = 308519) B308519
theorem B697243 : Blo 159796 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B205735 : Blo 159796 205735 := bstep (se 1 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 205735 = 308603) B308603
theorem B304555 : Blo 159796 304555 := bstep (se 1 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 304555 = 456833) B456833
theorem B304859 : Blo 159796 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B272207 : Blo 159796 272207 := bstep (se 1 (by rfl) ⟨204155, by rfl⟩ : syracuseStep 272207 = 408311) B408311
theorem B239711 : Blo 159796 239711 := bstep (se 1 (by rfl) ⟨179783, by rfl⟩ : syracuseStep 239711 = 359567) B359567
theorem B239771 : Blo 159796 239771 := bstep (se 1 (by rfl) ⟨179828, by rfl⟩ : syracuseStep 239771 = 359657) B359657
theorem B239807 : Blo 159796 239807 := bstep (se 1 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 239807 = 359711) B359711
theorem B239849 : Blo 159796 239849 := bstep (se 2 (by rfl) ⟨89943, by rfl⟩ : syracuseStep 239849 = 179887) B179887
theorem B567713 : Blo 159796 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B240155 : Blo 159796 240155 := bstep (se 1 (by rfl) ⟨180116, by rfl⟩ : syracuseStep 240155 = 360233) B360233
theorem B240233 : Blo 159796 240233 := bstep (se 2 (by rfl) ⟨90087, by rfl⟩ : syracuseStep 240233 = 180175) B180175
theorem B1321667 : Blo 159796 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B928655 : Blo 159796 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B273449 : Blo 159796 273449 := bstep (se 2 (by rfl) ⟨102543, by rfl⟩ : syracuseStep 273449 = 205087) B205087
theorem B9972823 : Blo 159796 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B240761 : Blo 159796 240761 := bstep (se 2 (by rfl) ⟨90285, by rfl⟩ : syracuseStep 240761 = 180571) B180571
theorem B240863 : Blo 159796 240863 := bstep (se 1 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 240863 = 361295) B361295
theorem B273631 : Blo 159796 273631 := bstep (se 1 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 273631 = 410447) B410447
theorem B240905 : Blo 159796 240905 := bstep (se 2 (by rfl) ⟨90339, by rfl⟩ : syracuseStep 240905 = 180679) B180679
theorem B241007 : Blo 159796 241007 := bstep (se 1 (by rfl) ⟨180755, by rfl⟩ : syracuseStep 241007 = 361511) B361511
theorem B241127 : Blo 159796 241127 := bstep (se 1 (by rfl) ⟨180845, by rfl⟩ : syracuseStep 241127 = 361691) B361691
theorem B241259 : Blo 159796 241259 := bstep (se 1 (by rfl) ⟨180944, by rfl⟩ : syracuseStep 241259 = 361889) B361889
theorem B274063 : Blo 159796 274063 := bstep (se 1 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 274063 = 411095) B411095
theorem B241385 : Blo 159796 241385 := bstep (se 2 (by rfl) ⟨90519, by rfl⟩ : syracuseStep 241385 = 181039) B181039
theorem B241529 : Blo 159796 241529 := bstep (se 2 (by rfl) ⟨90573, by rfl⟩ : syracuseStep 241529 = 181147) B181147
theorem B1486799 : Blo 159796 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B241631 : Blo 159796 241631 := bstep (se 1 (by rfl) ⟨181223, by rfl⟩ : syracuseStep 241631 = 362447) B362447
theorem B1028285 : Blo 159796 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B241883 : Blo 159796 241883 := bstep (se 1 (by rfl) ⟨181412, by rfl⟩ : syracuseStep 241883 = 362825) B362825
theorem B241895 : Blo 159796 241895 := bstep (se 1 (by rfl) ⟨181421, by rfl⟩ : syracuseStep 241895 = 362843) B362843
theorem B242057 : Blo 159796 242057 := bstep (se 2 (by rfl) ⟨90771, by rfl⟩ : syracuseStep 242057 = 181543) B181543
theorem B242153 : Blo 159796 242153 := bstep (se 2 (by rfl) ⟨90807, by rfl⟩ : syracuseStep 242153 = 181615) B181615
theorem B242279 : Blo 159796 242279 := bstep (se 1 (by rfl) ⟨181709, by rfl⟩ : syracuseStep 242279 = 363419) B363419
theorem B242411 : Blo 159796 242411 := bstep (se 1 (by rfl) ⟨181808, by rfl⟩ : syracuseStep 242411 = 363617) B363617
theorem B242441 : Blo 159796 242441 := bstep (se 2 (by rfl) ⟨90915, by rfl⟩ : syracuseStep 242441 = 181831) B181831
theorem B242543 : Blo 159796 242543 := bstep (se 1 (by rfl) ⟨181907, by rfl⟩ : syracuseStep 242543 = 363815) B363815
theorem B242795 : Blo 159796 242795 := bstep (se 1 (by rfl) ⟨182096, by rfl⟩ : syracuseStep 242795 = 364193) B364193
theorem B275663 : Blo 159796 275663 := bstep (se 1 (by rfl) ⟨206747, by rfl⟩ : syracuseStep 275663 = 413495) B413495
theorem B243035 : Blo 159796 243035 := bstep (se 1 (by rfl) ⟨182276, by rfl⟩ : syracuseStep 243035 = 364553) B364553
theorem B2307527 : Blo 159796 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B243311 : Blo 159796 243311 := bstep (se 1 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 243311 = 364967) B364967
theorem B1160887 : Blo 159796 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B243383 : Blo 159796 243383 := bstep (se 1 (by rfl) ⟨182537, by rfl⟩ : syracuseStep 243383 = 365075) B365075
theorem B243419 : Blo 159796 243419 := bstep (se 1 (by rfl) ⟨182564, by rfl⟩ : syracuseStep 243419 = 365129) B365129
theorem B243593 : Blo 159796 243593 := bstep (se 2 (by rfl) ⟨91347, by rfl⟩ : syracuseStep 243593 = 182695) B182695
theorem B243695 : Blo 159796 243695 := bstep (se 1 (by rfl) ⟨182771, by rfl⟩ : syracuseStep 243695 = 365543) B365543
theorem B407713 : Blo 159796 407713 := bstep (se 2 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 407713 = 305785) B305785
theorem B342215 : Blo 159796 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B866537 : Blo 159796 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B243947 : Blo 159796 243947 := bstep (se 1 (by rfl) ⟨182960, by rfl⟩ : syracuseStep 243947 = 365921) B365921
theorem B244007 : Blo 159796 244007 := bstep (se 1 (by rfl) ⟨183005, by rfl⟩ : syracuseStep 244007 = 366011) B366011
theorem B244091 : Blo 159796 244091 := bstep (se 1 (by rfl) ⟨183068, by rfl⟩ : syracuseStep 244091 = 366137) B366137
theorem B244361 : Blo 159796 244361 := bstep (se 2 (by rfl) ⟨91635, by rfl⟩ : syracuseStep 244361 = 183271) B183271
theorem B866969 : Blo 159796 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B244535 : Blo 159796 244535 := bstep (se 1 (by rfl) ⟨183401, by rfl⟩ : syracuseStep 244535 = 366803) B366803
theorem B244571 : Blo 159796 244571 := bstep (se 1 (by rfl) ⟨183428, by rfl⟩ : syracuseStep 244571 = 366857) B366857
theorem B4209515 : Blo 159796 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B244715 : Blo 159796 244715 := bstep (se 1 (by rfl) ⟨183536, by rfl⟩ : syracuseStep 244715 = 367073) B367073
theorem B277625 : Blo 159796 277625 := bstep (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) B208219
theorem B244919 : Blo 159796 244919 := bstep (se 1 (by rfl) ⟨183689, by rfl⟩ : syracuseStep 244919 = 367379) B367379
theorem B539999 : Blo 159796 539999 := bstep (se 1 (by rfl) ⟨404999, by rfl⟩ : syracuseStep 539999 = 809999) B809999
theorem B441767 : Blo 159796 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B245159 : Blo 159796 245159 := bstep (se 1 (by rfl) ⟨183869, by rfl⟩ : syracuseStep 245159 = 367739) B367739
theorem B736723 : Blo 159796 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B245243 : Blo 159796 245243 := bstep (se 1 (by rfl) ⟨183932, by rfl⟩ : syracuseStep 245243 = 367865) B367865
theorem B245339 : Blo 159796 245339 := bstep (se 1 (by rfl) ⟨184004, by rfl⟩ : syracuseStep 245339 = 368009) B368009
theorem B245423 : Blo 159796 245423 := bstep (se 1 (by rfl) ⟨184067, by rfl⟩ : syracuseStep 245423 = 368135) B368135
theorem B409313 : Blo 159796 409313 := bstep (se 2 (by rfl) ⟨153492, by rfl⟩ : syracuseStep 409313 = 306985) B306985
theorem B376553 : Blo 159796 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B245543 : Blo 159796 245543 := bstep (se 1 (by rfl) ⟨184157, by rfl⟩ : syracuseStep 245543 = 368315) B368315
theorem B540539 : Blo 159796 540539 := bstep (se 1 (by rfl) ⟨405404, by rfl⟩ : syracuseStep 540539 = 810809) B810809
theorem B245627 : Blo 159796 245627 := bstep (se 1 (by rfl) ⟨184220, by rfl⟩ : syracuseStep 245627 = 368441) B368441
theorem B409819 : Blo 159796 409819 := bstep (se 1 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 409819 = 614729) B614729
theorem B344351 : Blo 159796 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B541025 : Blo 159796 541025 := bstep (se 2 (by rfl) ⟨202884, by rfl⟩ : syracuseStep 541025 = 405769) B405769
theorem B180607 : Blo 159796 180607 := bstep (se 1 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 180607 = 270911) B270911
theorem B1032743 : Blo 159796 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B410579 : Blo 159796 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B2049083 : Blo 159796 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B410953 : Blo 159796 410953 := bstep (se 2 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 410953 = 308215) B308215
theorem B1590821 : Blo 159796 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B411257 : Blo 159796 411257 := bstep (se 2 (by rfl) ⟨154221, by rfl⟩ : syracuseStep 411257 = 308443) B308443
theorem B542375 : Blo 159796 542375 := bstep (se 1 (by rfl) ⟨406781, by rfl⟩ : syracuseStep 542375 = 813563) B813563
theorem B182011 : Blo 159796 182011 := bstep (se 1 (by rfl) ⟨136508, by rfl⟩ : syracuseStep 182011 = 273017) B273017
theorem B182047 : Blo 159796 182047 := bstep (se 1 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 182047 = 273071) B273071
theorem B2050109 : Blo 159796 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B542969 : Blo 159796 542969 := bstep (se 2 (by rfl) ⟨203613, by rfl⟩ : syracuseStep 542969 = 407227) B407227
theorem B248105 : Blo 159796 248105 := bstep (se 2 (by rfl) ⟨93039, by rfl⟩ : syracuseStep 248105 = 186079) B186079
theorem B543023 : Blo 159796 543023 := bstep (se 1 (by rfl) ⟨407267, by rfl⟩ : syracuseStep 543023 = 814535) B814535
theorem B543239 : Blo 159796 543239 := bstep (se 1 (by rfl) ⟨407429, by rfl⟩ : syracuseStep 543239 = 814859) B814859
theorem B183199 : Blo 159796 183199 := bstep (se 1 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 183199 = 274799) B274799
theorem B183343 : Blo 159796 183343 := bstep (se 1 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 183343 = 275015) B275015
theorem B543887 : Blo 159796 543887 := bstep (se 1 (by rfl) ⟨407915, by rfl⟩ : syracuseStep 543887 = 815831) B815831
theorem B9653411 : Blo 159796 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B183631 : Blo 159796 183631 := bstep (se 1 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 183631 = 275447) B275447
theorem B478715 : Blo 159796 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B544319 : Blo 159796 544319 := bstep (se 1 (by rfl) ⟨408239, by rfl⟩ : syracuseStep 544319 = 816479) B816479
theorem B184135 : Blo 159796 184135 := bstep (se 1 (by rfl) ⟨138101, by rfl⟩ : syracuseStep 184135 = 276203) B276203
theorem B413819 : Blo 159796 413819 := bstep (se 1 (by rfl) ⟨310364, by rfl⟩ : syracuseStep 413819 = 620729) B620729
theorem B545021 : Blo 159796 545021 := bstep (se 3 (by rfl) ⟨102191, by rfl⟩ : syracuseStep 545021 = 204383) B204383
theorem B1364273 : Blo 159796 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B348553 : Blo 159796 348553 := bstep (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) B261415
theorem B545561 : Blo 159796 545561 := bstep (se 2 (by rfl) ⟨204585, by rfl⟩ : syracuseStep 545561 = 409171) B409171
theorem B4510505 : Blo 159796 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B545831 : Blo 159796 545831 := bstep (se 1 (by rfl) ⟨409373, by rfl⟩ : syracuseStep 545831 = 818747) B818747
theorem B185519 : Blo 159796 185519 := bstep (se 1 (by rfl) ⟨139139, by rfl⟩ : syracuseStep 185519 = 278279) B278279
theorem B294508331 : Blo 159796 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B546911 : Blo 159796 546911 := bstep (se 1 (by rfl) ⟨410183, by rfl⟩ : syracuseStep 546911 = 820367) B820367
theorem B1235411 : Blo 159796 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B1071863 : Blo 159796 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B547667 : Blo 159796 547667 := bstep (se 1 (by rfl) ⟨410750, by rfl⟩ : syracuseStep 547667 = 821501) B821501
theorem B809837 : Blo 159796 809837 := bstep (se 3 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 809837 = 303689) B303689
theorem B384041 : Blo 159796 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B2055233 : Blo 159796 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B613727 : Blo 159796 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B548207 : Blo 159796 548207 := bstep (se 1 (by rfl) ⟨411155, by rfl⟩ : syracuseStep 548207 = 822311) B822311
theorem B548585 : Blo 159796 548585 := bstep (se 2 (by rfl) ⟨205719, by rfl⟩ : syracuseStep 548585 = 411439) B411439
theorem B4087741 : Blo 159796 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B1761527 : Blo 159796 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B811295 : Blo 159796 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B549449 : Blo 159796 549449 := bstep (se 2 (by rfl) ⟨206043, by rfl⟩ : syracuseStep 549449 = 412087) B412087
theorem B549611 : Blo 159796 549611 := bstep (se 1 (by rfl) ⟨412208, by rfl⟩ : syracuseStep 549611 = 824417) B824417
theorem B1041149 : Blo 159796 1041149 := bstep (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) B390431
theorem B40035221 : Blo 159796 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B4384205 : Blo 159796 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B288377 : Blo 159796 288377 := bstep (se 2 (by rfl) ⟨108141, by rfl⟩ : syracuseStep 288377 = 216283) B216283
theorem B1107715 : Blo 159796 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B4417361 : Blo 159796 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B551123 : Blo 159796 551123 := bstep (se 1 (by rfl) ⟨413342, by rfl⟩ : syracuseStep 551123 = 826685) B826685
theorem B551393 : Blo 159796 551393 := bstep (se 2 (by rfl) ⟨206772, by rfl⟩ : syracuseStep 551393 = 413545) B413545
theorem B289307 : Blo 159796 289307 := bstep (se 1 (by rfl) ⟨216980, by rfl⟩ : syracuseStep 289307 = 433961) B433961
theorem B1567259 : Blo 159796 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B584263 : Blo 159796 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B485993 : Blo 159796 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B1043147 : Blo 159796 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B224327 : Blo 159796 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B617615 : Blo 159796 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B912617 : Blo 159796 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B2354579 : Blo 159796 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B1109629 : Blo 159796 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B552743 : Blo 159796 552743 := bstep (se 1 (by rfl) ⟨414557, by rfl⟩ : syracuseStep 552743 = 829115) B829115
theorem B815021 : Blo 159796 815021 := bstep (se 3 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 815021 = 305633) B305633
theorem B618625 : Blo 159796 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B913619 : Blo 159796 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B159975 : Blo 159796 159975 := bstep (se 1 (by rfl) ⟨119981, by rfl⟩ : syracuseStep 159975 = 239963) B239963
theorem B160127 : Blo 159796 160127 := bstep (se 1 (by rfl) ⟨120095, by rfl⟩ : syracuseStep 160127 = 240191) B240191
theorem B913801 : Blo 159796 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B160207 : Blo 159796 160207 := bstep (se 1 (by rfl) ⟨120155, by rfl⟩ : syracuseStep 160207 = 240311) B240311
theorem B160359 : Blo 159796 160359 := bstep (se 1 (by rfl) ⟨120269, by rfl⟩ : syracuseStep 160359 = 240539) B240539
theorem B619271 : Blo 159796 619271 := bstep (se 1 (by rfl) ⟨464453, by rfl⟩ : syracuseStep 619271 = 928907) B928907
theorem B520985 : Blo 159796 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B160623 : Blo 159796 160623 := bstep (se 1 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 160623 = 240935) B240935
theorem B160679 : Blo 159796 160679 := bstep (se 1 (by rfl) ⟨120509, by rfl⟩ : syracuseStep 160679 = 241019) B241019
theorem B193447 : Blo 159796 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B160763 : Blo 159796 160763 := bstep (se 1 (by rfl) ⟨120572, by rfl⟩ : syracuseStep 160763 = 241145) B241145
theorem B160831 : Blo 159796 160831 := bstep (se 1 (by rfl) ⟨120623, by rfl⟩ : syracuseStep 160831 = 241247) B241247
theorem B160975 : Blo 159796 160975 := bstep (se 1 (by rfl) ⟨120731, by rfl⟩ : syracuseStep 160975 = 241463) B241463
theorem B161179 : Blo 159796 161179 := bstep (se 1 (by rfl) ⟨120884, by rfl⟩ : syracuseStep 161179 = 241769) B241769
theorem B816641 : Blo 159796 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B2094599 : Blo 159796 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B783881 : Blo 159796 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B456263 : Blo 159796 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B161391 : Blo 159796 161391 := bstep (se 1 (by rfl) ⟨121043, by rfl⟩ : syracuseStep 161391 = 242087) B242087
theorem B161447 : Blo 159796 161447 := bstep (se 1 (by rfl) ⟨121085, by rfl⟩ : syracuseStep 161447 = 242171) B242171
theorem B161531 : Blo 159796 161531 := bstep (se 1 (by rfl) ⟨121148, by rfl⟩ : syracuseStep 161531 = 242297) B242297
theorem B5306107 : Blo 159796 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B161567 : Blo 159796 161567 := bstep (se 1 (by rfl) ⟨121175, by rfl⟩ : syracuseStep 161567 = 242351) B242351
theorem B161599 : Blo 159796 161599 := bstep (se 1 (by rfl) ⟨121199, by rfl⟩ : syracuseStep 161599 = 242399) B242399
theorem B522215 : Blo 159796 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B161775 : Blo 159796 161775 := bstep (se 1 (by rfl) ⟨121331, by rfl⟩ : syracuseStep 161775 = 242663) B242663
theorem B456799 : Blo 159796 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B161947 : Blo 159796 161947 := bstep (se 1 (by rfl) ⟨121460, by rfl⟩ : syracuseStep 161947 = 242921) B242921
theorem B161983 : Blo 159796 161983 := bstep (se 1 (by rfl) ⟨121487, by rfl⟩ : syracuseStep 161983 = 242975) B242975
theorem B456947 : Blo 159796 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B817451 : Blo 159796 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B162095 : Blo 159796 162095 := bstep (se 1 (by rfl) ⟨121571, by rfl⟩ : syracuseStep 162095 = 243143) B243143
theorem B915785 : Blo 159796 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B162331 : Blo 159796 162331 := bstep (se 1 (by rfl) ⟨121748, by rfl⟩ : syracuseStep 162331 = 243497) B243497
theorem B162335 : Blo 159796 162335 := bstep (se 1 (by rfl) ⟨121751, by rfl⟩ : syracuseStep 162335 = 243503) B243503
theorem B260795 : Blo 159796 260795 := bstep (se 1 (by rfl) ⟨195596, by rfl⟩ : syracuseStep 260795 = 391193) B391193
theorem B1571663 : Blo 159796 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B162651 : Blo 159796 162651 := bstep (se 1 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 162651 = 243977) B243977
theorem B162719 : Blo 159796 162719 := bstep (se 1 (by rfl) ⟨122039, by rfl⟩ : syracuseStep 162719 = 244079) B244079
theorem B1047505 : Blo 159796 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B162863 : Blo 159796 162863 := bstep (se 1 (by rfl) ⟨122147, by rfl⟩ : syracuseStep 162863 = 244295) B244295
theorem B162887 : Blo 159796 162887 := bstep (se 1 (by rfl) ⟨122165, by rfl⟩ : syracuseStep 162887 = 244331) B244331
theorem B163039 : Blo 159796 163039 := bstep (se 1 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 163039 = 244559) B244559
theorem B359891 : Blo 159796 359891 := bstep (se 1 (by rfl) ⟨269918, by rfl⟩ : syracuseStep 359891 = 539837) B539837
theorem B163303 : Blo 159796 163303 := bstep (se 1 (by rfl) ⟨122477, by rfl⟩ : syracuseStep 163303 = 244955) B244955
theorem B523855 : Blo 159796 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B163419 : Blo 159796 163419 := bstep (se 1 (by rfl) ⟨122564, by rfl⟩ : syracuseStep 163419 = 245129) B245129
theorem B360161 : Blo 159796 360161 := bstep (se 2 (by rfl) ⟨135060, by rfl⟩ : syracuseStep 360161 = 270121) B270121
theorem B458473 : Blo 159796 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B524009 : Blo 159796 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B163655 : Blo 159796 163655 := bstep (se 1 (by rfl) ⟨122741, by rfl⟩ : syracuseStep 163655 = 245483) B245483
theorem B294779 : Blo 159796 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B229567 : Blo 159796 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B360683 : Blo 159796 360683 := bstep (se 1 (by rfl) ⟨270512, by rfl⟩ : syracuseStep 360683 = 541025) B541025
theorem B688495 : Blo 159796 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B2490743 : Blo 159796 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B459179 : Blo 159796 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B3146363 : Blo 159796 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B361583 : Blo 159796 361583 := bstep (se 1 (by rfl) ⟨271187, by rfl⟩ : syracuseStep 361583 = 542375) B542375
theorem B361979 : Blo 159796 361979 := bstep (se 1 (by rfl) ⟨271484, by rfl⟩ : syracuseStep 361979 = 542969) B542969
theorem B165403 : Blo 159796 165403 := bstep (se 1 (by rfl) ⟨124052, by rfl⟩ : syracuseStep 165403 = 248105) B248105
theorem B362015 : Blo 159796 362015 := bstep (se 1 (by rfl) ⟨271511, by rfl⟩ : syracuseStep 362015 = 543023) B543023
theorem B263711 : Blo 159796 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B362159 : Blo 159796 362159 := bstep (se 1 (by rfl) ⟨271619, by rfl⟩ : syracuseStep 362159 = 543239) B543239
theorem B362591 : Blo 159796 362591 := bstep (se 1 (by rfl) ⟨271943, by rfl⟩ : syracuseStep 362591 = 543887) B543887
theorem B1411181 : Blo 159796 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B1476953 : Blo 159796 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B362879 : Blo 159796 362879 := bstep (se 1 (by rfl) ⟨272159, by rfl⟩ : syracuseStep 362879 = 544319) B544319
theorem B920159 : Blo 159796 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B330335 : Blo 159796 330335 := bstep (se 1 (by rfl) ⟨247751, by rfl⟩ : syracuseStep 330335 = 495503) B495503
theorem B363347 : Blo 159796 363347 := bstep (se 1 (by rfl) ⟨272510, by rfl⟩ : syracuseStep 363347 = 545021) B545021
theorem B494717 : Blo 159796 494717 := bstep (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) B185519
theorem B363707 : Blo 159796 363707 := bstep (se 1 (by rfl) ⟨272780, by rfl⟩ : syracuseStep 363707 = 545561) B545561
theorem B363887 : Blo 159796 363887 := bstep (se 1 (by rfl) ⟨272915, by rfl⟩ : syracuseStep 363887 = 545831) B545831
theorem B659017 : Blo 159796 659017 := bstep (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) B494263
theorem B364607 : Blo 159796 364607 := bstep (se 1 (by rfl) ⟨273455, by rfl⟩ : syracuseStep 364607 = 546911) B546911
theorem B364841 : Blo 159796 364841 := bstep (se 2 (by rfl) ⟨136815, by rfl⟩ : syracuseStep 364841 = 273631) B273631
theorem B823607 : Blo 159796 823607 := bstep (se 1 (by rfl) ⟨617705, by rfl⟩ : syracuseStep 823607 = 1235411) B1235411
theorem B365111 : Blo 159796 365111 := bstep (se 1 (by rfl) ⟨273833, by rfl⟩ : syracuseStep 365111 = 547667) B547667
theorem B660215 : Blo 159796 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B1479505 : Blo 159796 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B365417 : Blo 159796 365417 := bstep (se 2 (by rfl) ⟨137031, by rfl⟩ : syracuseStep 365417 = 274063) B274063
theorem B365471 : Blo 159796 365471 := bstep (se 1 (by rfl) ⟨274103, by rfl⟩ : syracuseStep 365471 = 548207) B548207
theorem B365723 : Blo 159796 365723 := bstep (se 1 (by rfl) ⟨274292, by rfl⟩ : syracuseStep 365723 = 548585) B548585
theorem B922823 : Blo 159796 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B15832493 : Blo 159796 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B824833 : Blo 159796 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B366299 : Blo 159796 366299 := bstep (se 1 (by rfl) ⟨274724, by rfl⟩ : syracuseStep 366299 = 549449) B549449
theorem B366407 : Blo 159796 366407 := bstep (se 1 (by rfl) ⟨274805, by rfl⟩ : syracuseStep 366407 = 549611) B549611
theorem B694099 : Blo 159796 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B1218401 : Blo 159796 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B661385 : Blo 159796 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B1578953 : Blo 159796 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B2922803 : Blo 159796 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B203239 : Blo 159796 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B367415 : Blo 159796 367415 := bstep (se 1 (by rfl) ⟨275561, by rfl⟩ : syracuseStep 367415 = 551123) B551123
theorem B367595 : Blo 159796 367595 := bstep (se 1 (by rfl) ⟨275696, by rfl⟩ : syracuseStep 367595 = 551393) B551393
theorem B695431 : Blo 159796 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B1547849 : Blo 159796 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B368495 : Blo 159796 368495 := bstep (se 1 (by rfl) ⟨276371, by rfl⟩ : syracuseStep 368495 = 552743) B552743
theorem B991199 : Blo 159796 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B1024109 : Blo 159796 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B598205 : Blo 159796 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B304175 : Blo 159796 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B1844369 : Blo 159796 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B304631 : Blo 159796 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B173863 : Blo 159796 173863 := bstep (se 1 (by rfl) ⟨130397, by rfl⟩ : syracuseStep 173863 = 260795) B260795
theorem B698473 : Blo 159796 698473 := bstep (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) B523855
theorem B239927 : Blo 159796 239927 := bstep (se 1 (by rfl) ⟨179945, by rfl⟩ : syracuseStep 239927 = 359891) B359891
theorem B240107 : Blo 159796 240107 := bstep (se 1 (by rfl) ⟨180080, by rfl⟩ : syracuseStep 240107 = 360161) B360161
theorem B272875 : Blo 159796 272875 := bstep (se 1 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 272875 = 409313) B409313
theorem B5450321 : Blo 159796 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B273577 : Blo 159796 273577 := bstep (se 2 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 273577 = 205183) B205183
theorem B240809 : Blo 159796 240809 := bstep (se 2 (by rfl) ⟨90303, by rfl⟩ : syracuseStep 240809 = 180607) B180607
theorem B5024987 : Blo 159796 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B273719 : Blo 159796 273719 := bstep (se 1 (by rfl) ⟨205289, by rfl⟩ : syracuseStep 273719 = 410579) B410579
theorem B1945133 : Blo 159796 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B241223 : Blo 159796 241223 := bstep (se 1 (by rfl) ⟨180917, by rfl⟩ : syracuseStep 241223 = 361835) B361835
theorem B1060547 : Blo 159796 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B241403 : Blo 159796 241403 := bstep (se 1 (by rfl) ⟨181052, by rfl⟩ : syracuseStep 241403 = 362105) B362105
theorem B274171 : Blo 159796 274171 := bstep (se 1 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 274171 = 411257) B411257
theorem B929657 : Blo 159796 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B274313 : Blo 159796 274313 := bstep (se 2 (by rfl) ⟨102867, by rfl⟩ : syracuseStep 274313 = 205735) B205735
theorem B2338895 : Blo 159796 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B307327 : Blo 159796 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B242075 : Blo 159796 242075 := bstep (se 1 (by rfl) ⟨181556, by rfl⟩ : syracuseStep 242075 = 363113) B363113
theorem B406073 : Blo 159796 406073 := bstep (se 2 (by rfl) ⟨152277, by rfl⟩ : syracuseStep 406073 = 304555) B304555
theorem B6435607 : Blo 159796 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B242495 : Blo 159796 242495 := bstep (se 1 (by rfl) ⟨181871, by rfl⟩ : syracuseStep 242495 = 363743) B363743
theorem B242639 : Blo 159796 242639 := bstep (se 1 (by rfl) ⟨181979, by rfl⟩ : syracuseStep 242639 = 363959) B363959
theorem B1225691 : Blo 159796 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B242681 : Blo 159796 242681 := bstep (se 2 (by rfl) ⟨91005, by rfl⟩ : syracuseStep 242681 = 182011) B182011
theorem B242729 : Blo 159796 242729 := bstep (se 2 (by rfl) ⟨91023, by rfl⟩ : syracuseStep 242729 = 182047) B182047
theorem B242759 : Blo 159796 242759 := bstep (se 1 (by rfl) ⟨182069, by rfl⟩ : syracuseStep 242759 = 364139) B364139
theorem B242939 : Blo 159796 242939 := bstep (se 1 (by rfl) ⟨182204, by rfl⟩ : syracuseStep 242939 = 364409) B364409
theorem B275879 : Blo 159796 275879 := bstep (se 1 (by rfl) ⟨206909, by rfl⟩ : syracuseStep 275879 = 413819) B413819
theorem B1030283 : Blo 159796 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B244175 : Blo 159796 244175 := bstep (se 1 (by rfl) ⟨183131, by rfl⟩ : syracuseStep 244175 = 366263) B366263
theorem B244265 : Blo 159796 244265 := bstep (se 2 (by rfl) ⟨91599, by rfl⟩ : syracuseStep 244265 = 183199) B183199
theorem B244457 : Blo 159796 244457 := bstep (se 2 (by rfl) ⟨91671, by rfl⟩ : syracuseStep 244457 = 183343) B183343
theorem B244841 : Blo 159796 244841 := bstep (se 2 (by rfl) ⟨91815, by rfl⟩ : syracuseStep 244841 = 183631) B183631
theorem B244967 : Blo 159796 244967 := bstep (se 1 (by rfl) ⟨183725, by rfl⟩ : syracuseStep 244967 = 367451) B367451
theorem B539891 : Blo 159796 539891 := bstep (se 1 (by rfl) ⟨404918, by rfl⟩ : syracuseStep 539891 = 809837) B809837
theorem B4963751 : Blo 159796 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B1031717 : Blo 159796 1031717 := bstep (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) B193447
theorem B409151 : Blo 159796 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B245471 : Blo 159796 245471 := bstep (se 1 (by rfl) ⟨184103, by rfl⟩ : syracuseStep 245471 = 368207) B368207
theorem B245513 : Blo 159796 245513 := bstep (se 2 (by rfl) ⟨92067, by rfl⟩ : syracuseStep 245513 = 184135) B184135
theorem B540863 : Blo 159796 540863 := bstep (se 1 (by rfl) ⟨405647, by rfl⟩ : syracuseStep 540863 = 811295) B811295
theorem B1229093 : Blo 159796 1229093 := bstep (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) B230455
theorem B26690147 : Blo 159796 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B181471 : Blo 159796 181471 := bstep (se 1 (by rfl) ⟨136103, by rfl⟩ : syracuseStep 181471 = 272207) B272207
theorem B378475 : Blo 159796 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B182299 : Blo 159796 182299 := bstep (se 1 (by rfl) ⟨136724, by rfl⟩ : syracuseStep 182299 = 273449) B273449
theorem B411743 : Blo 159796 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B608411 : Blo 159796 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B543347 : Blo 159796 543347 := bstep (se 1 (by rfl) ⟨407510, by rfl⟩ : syracuseStep 543347 = 815021) B815021
theorem B609065 : Blo 159796 609065 := bstep (se 2 (by rfl) ⟨228399, by rfl⟩ : syracuseStep 609065 = 456799) B456799
theorem B609079 : Blo 159796 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B543617 : Blo 159796 543617 := bstep (se 2 (by rfl) ⟨203856, by rfl⟩ : syracuseStep 543617 = 407713) B407713
theorem B740333 : Blo 159796 740333 := bstep (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) B277625
theorem B412847 : Blo 159796 412847 := bstep (se 1 (by rfl) ⟨309635, by rfl⟩ : syracuseStep 412847 = 619271) B619271
theorem B347323 : Blo 159796 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B183775 : Blo 159796 183775 := bstep (se 1 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 183775 = 275663) B275663
theorem B544427 : Blo 159796 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B1396399 : Blo 159796 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B1396673 : Blo 159796 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B348143 : Blo 159796 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B577691 : Blo 159796 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B544967 : Blo 159796 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B610523 : Blo 159796 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B577979 : Blo 159796 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B2806343 : Blo 159796 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1004141 : Blo 159796 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B1397357 : Blo 159796 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B611297 : Blo 159796 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B546155 : Blo 159796 546155 := bstep (se 1 (by rfl) ⟨409616, by rfl⟩ : syracuseStep 546155 = 819233) B819233
theorem B6313459 : Blo 159796 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B546425 : Blo 159796 546425 := bstep (se 2 (by rfl) ⟨204909, by rfl⟩ : syracuseStep 546425 = 409819) B409819
theorem B546749 : Blo 159796 546749 := bstep (se 3 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 546749 = 205031) B205031
theorem B1366055 : Blo 159796 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B1366739 : Blo 159796 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B547937 : Blo 159796 547937 := bstep (se 2 (by rfl) ⟨205476, by rfl⟩ : syracuseStep 547937 = 410953) B410953
theorem B1858949 : Blo 159796 1858949 := bstep (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) B348553
theorem B548477 : Blo 159796 548477 := bstep (se 3 (by rfl) ⟨102839, by rfl⟩ : syracuseStep 548477 = 205679) B205679
theorem B548639 : Blo 159796 548639 := bstep (se 1 (by rfl) ⟨411479, by rfl⟩ : syracuseStep 548639 = 822959) B822959
theorem B548747 : Blo 159796 548747 := bstep (se 1 (by rfl) ⟨411560, by rfl⟩ : syracuseStep 548747 = 823121) B823121
theorem B909515 : Blo 159796 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B549287 : Blo 159796 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B3007003 : Blo 159796 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B779017 : Blo 159796 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B3892313 : Blo 159796 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B196338887 : Blo 159796 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B13297097 : Blo 159796 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B2975291 : Blo 159796 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B616187 : Blo 159796 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B1238813 : Blo 159796 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B714575 : Blo 159796 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B1370155 : Blo 159796 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B616841 : Blo 159796 616841 := bstep (se 2 (by rfl) ⟨231315, by rfl⟩ : syracuseStep 616841 = 462631) B462631
theorem B1174351 : Blo 159796 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B192251 : Blo 159796 192251 := bstep (se 1 (by rfl) ⟨144188, by rfl⟩ : syracuseStep 192251 = 288377) B288377
theorem B2944907 : Blo 159796 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B487417 : Blo 159796 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B159807 : Blo 159796 159807 := bstep (se 1 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 159807 = 239711) B239711
theorem B159847 : Blo 159796 159847 := bstep (se 1 (by rfl) ⟨119885, by rfl⟩ : syracuseStep 159847 = 239771) B239771
theorem B159871 : Blo 159796 159871 := bstep (se 1 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 159871 = 239807) B239807
theorem B159899 : Blo 159796 159899 := bstep (se 1 (by rfl) ⟨119924, by rfl⟩ : syracuseStep 159899 = 239849) B239849
theorem B160103 : Blo 159796 160103 := bstep (se 1 (by rfl) ⟨120077, by rfl⟩ : syracuseStep 160103 = 240155) B240155
theorem B192871 : Blo 159796 192871 := bstep (se 1 (by rfl) ⟨144653, by rfl⟩ : syracuseStep 192871 = 289307) B289307
theorem B1044839 : Blo 159796 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B323995 : Blo 159796 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B160155 : Blo 159796 160155 := bstep (se 1 (by rfl) ⟨120116, by rfl⟩ : syracuseStep 160155 = 240233) B240233
theorem B881111 : Blo 159796 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B619103 : Blo 159796 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B160507 : Blo 159796 160507 := bstep (se 1 (by rfl) ⟨120380, by rfl⟩ : syracuseStep 160507 = 240761) B240761
theorem B160575 : Blo 159796 160575 := bstep (se 1 (by rfl) ⟨120431, by rfl⟩ : syracuseStep 160575 = 240863) B240863
theorem B160603 : Blo 159796 160603 := bstep (se 1 (by rfl) ⟨120452, by rfl⟩ : syracuseStep 160603 = 240905) B240905
theorem B160671 : Blo 159796 160671 := bstep (se 1 (by rfl) ⟨120503, by rfl⟩ : syracuseStep 160671 = 241007) B241007
theorem B1569719 : Blo 159796 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B160751 : Blo 159796 160751 := bstep (se 1 (by rfl) ⟨120563, by rfl⟩ : syracuseStep 160751 = 241127) B241127
theorem B7074809 : Blo 159796 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B160839 : Blo 159796 160839 := bstep (se 1 (by rfl) ⟨120629, by rfl⟩ : syracuseStep 160839 = 241259) B241259
theorem B160923 : Blo 159796 160923 := bstep (se 1 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 160923 = 241385) B241385
theorem B161019 : Blo 159796 161019 := bstep (se 1 (by rfl) ⟨120764, by rfl⟩ : syracuseStep 161019 = 241529) B241529
theorem B161087 : Blo 159796 161087 := bstep (se 1 (by rfl) ⟨120815, by rfl⟩ : syracuseStep 161087 = 241631) B241631
theorem B685523 : Blo 159796 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B161255 : Blo 159796 161255 := bstep (se 1 (by rfl) ⟨120941, by rfl⟩ : syracuseStep 161255 = 241883) B241883
theorem B161263 : Blo 159796 161263 := bstep (se 1 (by rfl) ⟨120947, by rfl⟩ : syracuseStep 161263 = 241895) B241895
theorem B161371 : Blo 159796 161371 := bstep (se 1 (by rfl) ⟨121028, by rfl⟩ : syracuseStep 161371 = 242057) B242057
theorem B161435 : Blo 159796 161435 := bstep (se 1 (by rfl) ⟨121076, by rfl⟩ : syracuseStep 161435 = 242153) B242153
theorem B620257 : Blo 159796 620257 := bstep (se 2 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 620257 = 465193) B465193
theorem B161519 : Blo 159796 161519 := bstep (se 1 (by rfl) ⟨121139, by rfl⟩ : syracuseStep 161519 = 242279) B242279
theorem B161607 : Blo 159796 161607 := bstep (se 1 (by rfl) ⟨121205, by rfl⟩ : syracuseStep 161607 = 242411) B242411
theorem B161627 : Blo 159796 161627 := bstep (se 1 (by rfl) ⟨121220, by rfl⟩ : syracuseStep 161627 = 242441) B242441
theorem B161695 : Blo 159796 161695 := bstep (se 1 (by rfl) ⟨121271, by rfl⟩ : syracuseStep 161695 = 242543) B242543
theorem B161863 : Blo 159796 161863 := bstep (se 1 (by rfl) ⟨121397, by rfl⟩ : syracuseStep 161863 = 242795) B242795
theorem B162023 : Blo 159796 162023 := bstep (se 1 (by rfl) ⟨121517, by rfl⟩ : syracuseStep 162023 = 243035) B243035
theorem B1538351 : Blo 159796 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B522587 : Blo 159796 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B162207 : Blo 159796 162207 := bstep (se 1 (by rfl) ⟨121655, by rfl⟩ : syracuseStep 162207 = 243311) B243311
theorem B162255 : Blo 159796 162255 := bstep (se 1 (by rfl) ⟨121691, by rfl⟩ : syracuseStep 162255 = 243383) B243383
theorem B162279 : Blo 159796 162279 := bstep (se 1 (by rfl) ⟨121709, by rfl⟩ : syracuseStep 162279 = 243419) B243419
theorem B227881 : Blo 159796 227881 := bstep (se 2 (by rfl) ⟨85455, by rfl⟩ : syracuseStep 227881 = 170911) B170911
theorem B162395 : Blo 159796 162395 := bstep (se 1 (by rfl) ⟨121796, by rfl⟩ : syracuseStep 162395 = 243593) B243593
theorem B1276573 : Blo 159796 1276573 := bstep (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) B478715
theorem B162463 : Blo 159796 162463 := bstep (se 1 (by rfl) ⟨121847, by rfl⟩ : syracuseStep 162463 = 243695) B243695
theorem B228143 : Blo 159796 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B162631 : Blo 159796 162631 := bstep (se 1 (by rfl) ⟨121973, by rfl⟩ : syracuseStep 162631 = 243947) B243947
theorem B162671 : Blo 159796 162671 := bstep (se 1 (by rfl) ⟨122003, by rfl⟩ : syracuseStep 162671 = 244007) B244007
theorem B162727 : Blo 159796 162727 := bstep (se 1 (by rfl) ⟨122045, by rfl⟩ : syracuseStep 162727 = 244091) B244091
theorem B162907 : Blo 159796 162907 := bstep (se 1 (by rfl) ⟨122180, by rfl⟩ : syracuseStep 162907 = 244361) B244361
theorem B163023 : Blo 159796 163023 := bstep (se 1 (by rfl) ⟨122267, by rfl⟩ : syracuseStep 163023 = 244535) B244535
theorem B1047775 : Blo 159796 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B163047 : Blo 159796 163047 := bstep (se 1 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 163047 = 244571) B244571
theorem B982297 : Blo 159796 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B163143 : Blo 159796 163143 := bstep (se 1 (by rfl) ⟨122357, by rfl⟩ : syracuseStep 163143 = 244715) B244715
theorem B163279 : Blo 159796 163279 := bstep (se 1 (by rfl) ⟨122459, by rfl⟩ : syracuseStep 163279 = 244919) B244919
theorem B359999 : Blo 159796 359999 := bstep (se 1 (by rfl) ⟨269999, by rfl⟩ : syracuseStep 359999 = 539999) B539999
theorem B294511 : Blo 159796 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B163439 : Blo 159796 163439 := bstep (se 1 (by rfl) ⟨122579, by rfl⟩ : syracuseStep 163439 = 245159) B245159
theorem B163495 : Blo 159796 163495 := bstep (se 1 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 163495 = 245243) B245243
theorem B163559 : Blo 159796 163559 := bstep (se 1 (by rfl) ⟨122669, by rfl⟩ : syracuseStep 163559 = 245339) B245339
theorem B163615 : Blo 159796 163615 := bstep (se 1 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 163615 = 245423) B245423
theorem B163695 : Blo 159796 163695 := bstep (se 1 (by rfl) ⟨122771, by rfl⟩ : syracuseStep 163695 = 245543) B245543
theorem B360359 : Blo 159796 360359 := bstep (se 1 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 360359 = 540539) B540539
theorem B196519 : Blo 159796 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B163751 : Blo 159796 163751 := bstep (se 1 (by rfl) ⟨122813, by rfl⟩ : syracuseStep 163751 = 245627) B245627
theorem B360575 : Blo 159796 360575 := bstep (se 1 (by rfl) ⟨270431, by rfl⟩ : syracuseStep 360575 = 540863) B540863
theorem B819395 : Blo 159796 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B17793431 : Blo 159796 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B2097575 : Blo 159796 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B917993 : Blo 159796 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B2425373 : Blo 159796 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B2786237 : Blo 159796 2786237 := bstep (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) B1044839
theorem B5276981 : Blo 159796 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B984635 : Blo 159796 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B362231 : Blo 159796 362231 := bstep (se 1 (by rfl) ⟨271673, by rfl⟩ : syracuseStep 362231 = 543347) B543347
theorem B362411 : Blo 159796 362411 := bstep (se 1 (by rfl) ⟨271808, by rfl⟩ : syracuseStep 362411 = 543617) B543617
theorem B231817 : Blo 159796 231817 := bstep (se 2 (by rfl) ⟨86931, by rfl⟩ : syracuseStep 231817 = 173863) B173863
theorem B362951 : Blo 159796 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B363311 : Blo 159796 363311 := bstep (se 1 (by rfl) ⟨272483, by rfl⟩ : syracuseStep 363311 = 544967) B544967
theorem B1870895 : Blo 159796 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B363833 : Blo 159796 363833 := bstep (se 2 (by rfl) ⟨136437, by rfl⟩ : syracuseStep 363833 = 272875) B272875
theorem B364103 : Blo 159796 364103 := bstep (se 1 (by rfl) ⟨273077, by rfl⟩ : syracuseStep 364103 = 546155) B546155
theorem B10554995 : Blo 159796 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B364283 : Blo 159796 364283 := bstep (se 1 (by rfl) ⟨273212, by rfl⟩ : syracuseStep 364283 = 546425) B546425
theorem B364499 : Blo 159796 364499 := bstep (se 1 (by rfl) ⟨273374, by rfl⟩ : syracuseStep 364499 = 546749) B546749
theorem B1052635 : Blo 159796 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B364769 : Blo 159796 364769 := bstep (se 2 (by rfl) ⟨136788, by rfl⟩ : syracuseStep 364769 = 273577) B273577
theorem B463097 : Blo 159796 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B365291 : Blo 159796 365291 := bstep (se 1 (by rfl) ⟨273968, by rfl⟩ : syracuseStep 365291 = 547937) B547937
theorem B365561 : Blo 159796 365561 := bstep (se 2 (by rfl) ⟨137085, by rfl⟩ : syracuseStep 365561 = 274171) B274171
theorem B365651 : Blo 159796 365651 := bstep (se 1 (by rfl) ⟨274238, by rfl⟩ : syracuseStep 365651 = 548477) B548477
theorem B365759 : Blo 159796 365759 := bstep (se 1 (by rfl) ⟨274319, by rfl⟩ : syracuseStep 365759 = 548639) B548639
theorem B365831 : Blo 159796 365831 := bstep (se 1 (by rfl) ⟨274373, by rfl⟩ : syracuseStep 365831 = 548747) B548747
theorem B660799 : Blo 159796 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B366191 : Blo 159796 366191 := bstep (se 1 (by rfl) ⟨274643, by rfl⟩ : syracuseStep 366191 = 549287) B549287
theorem B431993 : Blo 159796 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B3708965 : Blo 159796 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B2594875 : Blo 159796 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B203087 : Blo 159796 203087 := bstep (se 1 (by rfl) ⟨152315, by rfl⟩ : syracuseStep 203087 = 304631) B304631
theorem B1972673 : Blo 159796 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B825875 : Blo 159796 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B3349991 : Blo 159796 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B827009 : Blo 159796 827009 := bstep (se 2 (by rfl) ⟨310128, by rfl⟩ : syracuseStep 827009 = 620257) B620257
theorem B925465 : Blo 159796 925465 := bstep (se 2 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 925465 = 694099) B694099
theorem B1974221 : Blo 159796 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B270715 : Blo 159796 270715 := bstep (se 1 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 270715 = 406073) B406073
theorem B3514757 : Blo 159796 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B270985 : Blo 159796 270985 := bstep (se 2 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 270985 = 203239) B203239
theorem B303841 : Blo 159796 303841 := bstep (se 2 (by rfl) ⟨113940, by rfl⟩ : syracuseStep 303841 = 227881) B227881
theorem B1025567 : Blo 159796 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B2828125 : Blo 159796 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B239999 : Blo 159796 239999 := bstep (se 1 (by rfl) ⟨179999, by rfl⟩ : syracuseStep 239999 = 359999) B359999
theorem B272767 : Blo 159796 272767 := bstep (se 1 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 272767 = 409151) B409151
theorem B240239 : Blo 159796 240239 := bstep (se 1 (by rfl) ⟨180179, by rfl⟩ : syracuseStep 240239 = 360359) B360359
theorem B928381 : Blo 159796 928381 := bstep (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) B348143
theorem B240455 : Blo 159796 240455 := bstep (se 1 (by rfl) ⟨180341, by rfl⟩ : syracuseStep 240455 = 360683) B360683
theorem B306089 : Blo 159796 306089 := bstep (se 2 (by rfl) ⟨114783, by rfl⟩ : syracuseStep 306089 = 229567) B229567
theorem B306119 : Blo 159796 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B4009337 : Blo 159796 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B241055 : Blo 159796 241055 := bstep (se 1 (by rfl) ⟨180791, by rfl⟩ : syracuseStep 241055 = 361583) B361583
theorem B241319 : Blo 159796 241319 := bstep (se 1 (by rfl) ⟨180989, by rfl⟩ : syracuseStep 241319 = 361979) B361979
theorem B241343 : Blo 159796 241343 := bstep (se 1 (by rfl) ⟨181007, by rfl⟩ : syracuseStep 241343 = 362015) B362015
theorem B175807 : Blo 159796 175807 := bstep (se 1 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 175807 = 263711) B263711
theorem B241439 : Blo 159796 241439 := bstep (se 1 (by rfl) ⟨181079, by rfl⟩ : syracuseStep 241439 = 362159) B362159
theorem B241727 : Blo 159796 241727 := bstep (se 1 (by rfl) ⟨181295, by rfl⟩ : syracuseStep 241727 = 362591) B362591
theorem B274495 : Blo 159796 274495 := bstep (se 1 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 274495 = 411743) B411743
theorem B405607 : Blo 159796 405607 := bstep (se 1 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 405607 = 608411) B608411
theorem B1650941 : Blo 159796 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B241919 : Blo 159796 241919 := bstep (se 1 (by rfl) ⟨181439, by rfl⟩ : syracuseStep 241919 = 362879) B362879
theorem B241961 : Blo 159796 241961 := bstep (se 2 (by rfl) ⟨90735, by rfl⟩ : syracuseStep 241961 = 181471) B181471
theorem B406043 : Blo 159796 406043 := bstep (se 1 (by rfl) ⟨304532, by rfl⟩ : syracuseStep 406043 = 609065) B609065
theorem B242231 : Blo 159796 242231 := bstep (se 1 (by rfl) ⟨181673, by rfl⟩ : syracuseStep 242231 = 363347) B363347
theorem B275231 : Blo 159796 275231 := bstep (se 1 (by rfl) ⟨206423, by rfl⟩ : syracuseStep 275231 = 412847) B412847
theorem B242471 : Blo 159796 242471 := bstep (se 1 (by rfl) ⟨181853, by rfl⟩ : syracuseStep 242471 = 363707) B363707
theorem B242591 : Blo 159796 242591 := bstep (se 1 (by rfl) ⟨181943, by rfl⟩ : syracuseStep 242591 = 363887) B363887
theorem B931115 : Blo 159796 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B243065 : Blo 159796 243065 := bstep (se 2 (by rfl) ⟨91149, by rfl⟩ : syracuseStep 243065 = 182299) B182299
theorem B243071 : Blo 159796 243071 := bstep (se 1 (by rfl) ⟨182303, by rfl⟩ : syracuseStep 243071 = 364607) B364607
theorem B931297 : Blo 159796 931297 := bstep (se 2 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 931297 = 698473) B698473
theorem B407015 : Blo 159796 407015 := bstep (se 1 (by rfl) ⟨305261, by rfl⟩ : syracuseStep 407015 = 610523) B610523
theorem B243227 : Blo 159796 243227 := bstep (se 1 (by rfl) ⟨182420, by rfl⟩ : syracuseStep 243227 = 364841) B364841
theorem B243407 : Blo 159796 243407 := bstep (se 1 (by rfl) ⟨182555, by rfl⟩ : syracuseStep 243407 = 365111) B365111
theorem B669427 : Blo 159796 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B931571 : Blo 159796 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B440143 : Blo 159796 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B243611 : Blo 159796 243611 := bstep (se 1 (by rfl) ⟨182708, by rfl⟩ : syracuseStep 243611 = 365417) B365417
theorem B243647 : Blo 159796 243647 := bstep (se 1 (by rfl) ⟨182735, by rfl⟩ : syracuseStep 243647 = 365471) B365471
theorem B407531 : Blo 159796 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B243815 : Blo 159796 243815 := bstep (se 1 (by rfl) ⟨182861, by rfl⟩ : syracuseStep 243815 = 365723) B365723
theorem B244199 : Blo 159796 244199 := bstep (se 1 (by rfl) ⟨183149, by rfl⟩ : syracuseStep 244199 = 366299) B366299
theorem B244271 : Blo 159796 244271 := bstep (se 1 (by rfl) ⟨183203, by rfl⟩ : syracuseStep 244271 = 366407) B366407
theorem B1948535 : Blo 159796 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B244943 : Blo 159796 244943 := bstep (se 1 (by rfl) ⟨183707, by rfl⟩ : syracuseStep 244943 = 367415) B367415
theorem B245033 : Blo 159796 245033 := bstep (se 2 (by rfl) ⟨91887, by rfl⟩ : syracuseStep 245033 = 183775) B183775
theorem B245063 : Blo 159796 245063 := bstep (se 1 (by rfl) ⟨183797, by rfl⟩ : syracuseStep 245063 = 367595) B367595
theorem B1031899 : Blo 159796 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B245663 : Blo 159796 245663 := bstep (se 1 (by rfl) ⟨184247, by rfl⟩ : syracuseStep 245663 = 368495) B368495
theorem B409769 : Blo 159796 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B1229579 : Blo 159796 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B130892591 : Blo 159796 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B8864731 : Blo 159796 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1983527 : Blo 159796 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B410791 : Blo 159796 410791 := bstep (se 1 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 410791 = 616187) B616187
theorem B476383 : Blo 159796 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B411227 : Blo 159796 411227 := bstep (se 1 (by rfl) ⟨308420, by rfl⟩ : syracuseStep 411227 = 616841) B616841
theorem B1099777 : Blo 159796 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B608381 : Blo 159796 608381 := bstep (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) B228143
theorem B182479 : Blo 159796 182479 := bstep (se 1 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 182479 = 273719) B273719
theorem B1296755 : Blo 159796 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B182875 : Blo 159796 182875 := bstep (se 1 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 182875 = 274313) B274313
theorem B1559263 : Blo 159796 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B412735 : Blo 159796 412735 := bstep (se 1 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 412735 = 619103) B619103
theorem B2018533 : Blo 159796 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B183919 : Blo 159796 183919 := bstep (se 1 (by rfl) ⟨137939, by rfl⟩ : syracuseStep 183919 = 275879) B275879
theorem B348391 : Blo 159796 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B1397033 : Blo 159796 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B512669 : Blo 159796 512669 := bstep (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) B192251
theorem B1660495 : Blo 159796 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1595213 : Blo 159796 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B1038689 : Blo 159796 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B940787 : Blo 159796 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B613439 : Blo 159796 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B220223 : Blo 159796 220223 := bstep (se 1 (by rfl) ⟨165167, by rfl⟩ : syracuseStep 220223 = 330335) B330335
theorem B220537 : Blo 159796 220537 := bstep (se 2 (by rfl) ⟨82701, by rfl⟩ : syracuseStep 220537 = 165403) B165403
theorem B4185917 : Blo 159796 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B1826873 : Blo 159796 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B385127 : Blo 159796 385127 := bstep (se 1 (by rfl) ⟨288845, by rfl⟩ : syracuseStep 385127 = 577691) B577691
theorem B811133 : Blo 159796 811133 := bstep (se 3 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 811133 = 304175) B304175
theorem B549071 : Blo 159796 549071 := bstep (se 1 (by rfl) ⟨411803, by rfl⟩ : syracuseStep 549071 = 823607) B823607
theorem B385319 : Blo 159796 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B615215 : Blo 159796 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B812105 : Blo 159796 812105 := bstep (se 2 (by rfl) ⟨304539, by rfl⟩ : syracuseStep 812105 = 609079) B609079
theorem B1565801 : Blo 159796 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B812267 : Blo 159796 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B910703 : Blo 159796 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B911159 : Blo 159796 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B1861865 : Blo 159796 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B1239299 : Blo 159796 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B1763693 : Blo 159796 1763693 := bstep (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) B661385
theorem B649889 : Blo 159796 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B682739 : Blo 159796 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B257161 : Blo 159796 257161 := bstep (se 2 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 257161 = 192871) B192871
theorem B8580809 : Blo 159796 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B159951 : Blo 159796 159951 := bstep (se 1 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 159951 = 239927) B239927
theorem B160071 : Blo 159796 160071 := bstep (se 1 (by rfl) ⟨120053, by rfl⟩ : syracuseStep 160071 = 240107) B240107
theorem B3633547 : Blo 159796 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B8417945 : Blo 159796 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B160539 : Blo 159796 160539 := bstep (se 1 (by rfl) ⟨120404, by rfl⟩ : syracuseStep 160539 = 240809) B240809
theorem B160815 : Blo 159796 160815 := bstep (se 1 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 160815 = 241223) B241223
theorem B160935 : Blo 159796 160935 := bstep (se 1 (by rfl) ⟨120701, by rfl⟩ : syracuseStep 160935 = 241403) B241403
theorem B619771 : Blo 159796 619771 := bstep (se 1 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 619771 = 929657) B929657
theorem B1963271 : Blo 159796 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B161383 : Blo 159796 161383 := bstep (se 1 (by rfl) ⟨121037, by rfl⟩ : syracuseStep 161383 = 242075) B242075
theorem B587407 : Blo 159796 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B161663 : Blo 159796 161663 := bstep (se 1 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 161663 = 242495) B242495
theorem B161759 : Blo 159796 161759 := bstep (se 1 (by rfl) ⟨121319, by rfl⟩ : syracuseStep 161759 = 242639) B242639
theorem B817127 : Blo 159796 817127 := bstep (se 1 (by rfl) ⟨612845, by rfl⟩ : syracuseStep 817127 = 1225691) B1225691
theorem B161787 : Blo 159796 161787 := bstep (se 1 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 161787 = 242681) B242681
theorem B4716539 : Blo 159796 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B161819 : Blo 159796 161819 := bstep (se 1 (by rfl) ⟨121364, by rfl⟩ : syracuseStep 161819 = 242729) B242729
theorem B161839 : Blo 159796 161839 := bstep (se 1 (by rfl) ⟨121379, by rfl⟩ : syracuseStep 161839 = 242759) B242759
theorem B161959 : Blo 159796 161959 := bstep (se 1 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 161959 = 242939) B242939
theorem B1702097 : Blo 159796 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B457015 : Blo 159796 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B686855 : Blo 159796 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B2751245 : Blo 159796 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B162783 : Blo 159796 162783 := bstep (se 1 (by rfl) ⟨122087, by rfl⟩ : syracuseStep 162783 = 244175) B244175
theorem B162843 : Blo 159796 162843 := bstep (se 1 (by rfl) ⟨122132, by rfl⟩ : syracuseStep 162843 = 244265) B244265
theorem B1309729 : Blo 159796 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B162971 : Blo 159796 162971 := bstep (se 1 (by rfl) ⟨122228, by rfl⟩ : syracuseStep 162971 = 244457) B244457
theorem B163227 : Blo 159796 163227 := bstep (se 1 (by rfl) ⟨122420, by rfl⟩ : syracuseStep 163227 = 244841) B244841
theorem B392681 : Blo 159796 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B163311 : Blo 159796 163311 := bstep (se 1 (by rfl) ⟨122483, by rfl⟩ : syracuseStep 163311 = 244967) B244967
theorem B359927 : Blo 159796 359927 := bstep (se 1 (by rfl) ⟨269945, by rfl⟩ : syracuseStep 359927 = 539891) B539891
theorem B3309167 : Blo 159796 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B163647 : Blo 159796 163647 := bstep (se 1 (by rfl) ⟨122735, by rfl⟩ : syracuseStep 163647 = 245471) B245471
theorem B163675 : Blo 159796 163675 := bstep (se 1 (by rfl) ⟨122756, by rfl⟩ : syracuseStep 163675 = 245513) B245513
theorem B262025 : Blo 159796 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B11862287 : Blo 159796 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B360953 : Blo 159796 360953 := bstep (se 2 (by rfl) ⟨135357, by rfl⟩ : syracuseStep 360953 = 270715) B270715
theorem B819719 : Blo 159796 819719 := bstep (se 1 (by rfl) ⟨614789, by rfl⟩ : syracuseStep 819719 = 1229579) B1229579
theorem B361313 : Blo 159796 361313 := bstep (se 2 (by rfl) ⟨135492, by rfl⟩ : syracuseStep 361313 = 270985) B270985
theorem B9372685 : Blo 159796 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B656423 : Blo 159796 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B349046909 : Blo 159796 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B3770833 : Blo 159796 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B363689 : Blo 159796 363689 := bstep (se 2 (by rfl) ⟨136383, by rfl⟩ : syracuseStep 363689 = 272767) B272767
theorem B692459 : Blo 159796 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B1315115 : Blo 159796 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B2691377 : Blo 159796 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B627191 : Blo 159796 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B234409 : Blo 159796 234409 := bstep (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) B175807
theorem B1151981 : Blo 159796 1151981 := bstep (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) B431993
theorem B2233327 : Blo 159796 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2790611 : Blo 159796 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B1316147 : Blo 159796 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1217915 : Blo 159796 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B365993 : Blo 159796 365993 := bstep (se 2 (by rfl) ⟨137247, by rfl⟩ : syracuseStep 365993 = 274495) B274495
theorem B366047 : Blo 159796 366047 := bstep (se 1 (by rfl) ⟨274535, by rfl⟩ : syracuseStep 366047 = 549071) B549071
theorem B826199 : Blo 159796 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B826361 : Blo 159796 826361 := bstep (se 2 (by rfl) ⟨309885, by rfl⟩ : syracuseStep 826361 = 619771) B619771
theorem B433259 : Blo 159796 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B204059 : Blo 159796 204059 := bstep (se 1 (by rfl) ⟨153044, by rfl⟩ : syracuseStep 204059 = 306089) B306089
theorem B4989053 : Blo 159796 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B270695 : Blo 159796 270695 := bstep (se 1 (by rfl) ⟨203021, by rfl⟩ : syracuseStep 270695 = 406043) B406043
theorem B5611963 : Blo 159796 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B271343 : Blo 159796 271343 := bstep (se 1 (by rfl) ⟨203507, by rfl⟩ : syracuseStep 271343 = 407015) B407015
theorem B271687 : Blo 159796 271687 := bstep (se 1 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 271687 = 407531) B407531
theorem B1746305 : Blo 159796 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B239951 : Blo 159796 239951 := bstep (se 1 (by rfl) ⟨179963, by rfl⟩ : syracuseStep 239951 = 359927) B359927
theorem B2206111 : Blo 159796 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B174683 : Blo 159796 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B240383 : Blo 159796 240383 := bstep (se 1 (by rfl) ⟨180287, by rfl⟩ : syracuseStep 240383 = 360575) B360575
theorem B273179 : Blo 159796 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B1616915 : Blo 159796 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1322351 : Blo 159796 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B3517987 : Blo 159796 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B405121 : Blo 159796 405121 := bstep (se 2 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 405121 = 303841) B303841
theorem B274151 : Blo 159796 274151 := bstep (se 1 (by rfl) ⟨205613, by rfl⟩ : syracuseStep 274151 = 411227) B411227
theorem B241487 : Blo 159796 241487 := bstep (se 1 (by rfl) ⟨181115, by rfl⟩ : syracuseStep 241487 = 362231) B362231
theorem B241607 : Blo 159796 241607 := bstep (se 1 (by rfl) ⟨181205, by rfl⟩ : syracuseStep 241607 = 362411) B362411
theorem B405587 : Blo 159796 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B864503 : Blo 159796 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B635177 : Blo 159796 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B241967 : Blo 159796 241967 := bstep (se 1 (by rfl) ⟨181475, by rfl⟩ : syracuseStep 241967 = 362951) B362951
theorem B242207 : Blo 159796 242207 := bstep (se 1 (by rfl) ⟨181655, by rfl⟩ : syracuseStep 242207 = 363311) B363311
theorem B242555 : Blo 159796 242555 := bstep (se 1 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 242555 = 363833) B363833
theorem B242735 : Blo 159796 242735 := bstep (se 1 (by rfl) ⟨182051, by rfl⟩ : syracuseStep 242735 = 364103) B364103
theorem B242855 : Blo 159796 242855 := bstep (se 1 (by rfl) ⟨182141, by rfl⟩ : syracuseStep 242855 = 364283) B364283
theorem B242999 : Blo 159796 242999 := bstep (se 1 (by rfl) ⟨182249, by rfl⟩ : syracuseStep 242999 = 364499) B364499
theorem B243179 : Blo 159796 243179 := bstep (se 1 (by rfl) ⟨182384, by rfl⟩ : syracuseStep 243179 = 364769) B364769
theorem B931355 : Blo 159796 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B243305 : Blo 159796 243305 := bstep (se 2 (by rfl) ⟨91239, by rfl⟩ : syracuseStep 243305 = 182479) B182479
theorem B243527 : Blo 159796 243527 := bstep (se 1 (by rfl) ⟨182645, by rfl⟩ : syracuseStep 243527 = 365291) B365291
theorem B309089 : Blo 159796 309089 := bstep (se 2 (by rfl) ⟨115908, by rfl⟩ : syracuseStep 309089 = 231817) B231817
theorem B243707 : Blo 159796 243707 := bstep (se 1 (by rfl) ⟨182780, by rfl⟩ : syracuseStep 243707 = 365561) B365561
theorem B243767 : Blo 159796 243767 := bstep (se 1 (by rfl) ⟨182825, by rfl⟩ : syracuseStep 243767 = 365651) B365651
theorem B243833 : Blo 159796 243833 := bstep (se 2 (by rfl) ⟨91437, by rfl⟩ : syracuseStep 243833 = 182875) B182875
theorem B243839 : Blo 159796 243839 := bstep (se 1 (by rfl) ⟨182879, by rfl⟩ : syracuseStep 243839 = 365759) B365759
theorem B243887 : Blo 159796 243887 := bstep (se 1 (by rfl) ⟨182915, by rfl⟩ : syracuseStep 243887 = 365831) B365831
theorem B2079017 : Blo 159796 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B244127 : Blo 159796 244127 := bstep (se 1 (by rfl) ⟨183095, by rfl⟩ : syracuseStep 244127 = 366191) B366191
theorem B1063475 : Blo 159796 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B2472643 : Blo 159796 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B342881 : Blo 159796 342881 := bstep (se 2 (by rfl) ⟨128580, by rfl⟩ : syracuseStep 342881 = 257161) B257161
theorem B408959 : Blo 159796 408959 := bstep (se 1 (by rfl) ⟨306719, by rfl⟩ : syracuseStep 408959 = 613439) B613439
theorem B245225 : Blo 159796 245225 := bstep (se 2 (by rfl) ⟨91959, by rfl⟩ : syracuseStep 245225 = 183919) B183919
theorem B540755 : Blo 159796 540755 := bstep (se 1 (by rfl) ⟨405566, by rfl⟩ : syracuseStep 540755 = 811133) B811133
theorem B540809 : Blo 159796 540809 := bstep (se 2 (by rfl) ⟨202803, by rfl⟩ : syracuseStep 540809 = 405607) B405607
theorem B410143 : Blo 159796 410143 := bstep (se 1 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 410143 = 615215) B615215
theorem B541403 : Blo 159796 541403 := bstep (se 1 (by rfl) ⟨406052, by rfl⟩ : syracuseStep 541403 = 812105) B812105
theorem B541511 : Blo 159796 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B541565 : Blo 159796 541565 := bstep (se 3 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 541565 = 203087) B203087
theorem B607135 : Blo 159796 607135 := bstep (se 1 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 607135 = 910703) B910703
theorem B607439 : Blo 159796 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B2213993 : Blo 159796 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B2672891 : Blo 159796 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B5720539 : Blo 159796 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B3459833 : Blo 159796 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B1100627 : Blo 159796 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B609353 : Blo 159796 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B183487 : Blo 159796 183487 := bstep (se 1 (by rfl) ⟨137615, by rfl⟩ : syracuseStep 183487 = 275231) B275231
theorem B544751 : Blo 159796 544751 := bstep (se 1 (by rfl) ⟨408563, by rfl⟩ : syracuseStep 544751 = 817127) B817127
theorem B1134731 : Blo 159796 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B2347429 : Blo 159796 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B1299023 : Blo 159796 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B1233953 : Blo 159796 1233953 := bstep (se 2 (by rfl) ⟨462732, by rfl⟩ : syracuseStep 1233953 = 925465) B925465
theorem B546263 : Blo 159796 546263 := bstep (se 1 (by rfl) ⟨409697, by rfl⟩ : syracuseStep 546263 = 819395) B819395
theorem B1398383 : Blo 159796 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B611995 : Blo 159796 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B1857491 : Blo 159796 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B1234925 : Blo 159796 1234925 := bstep (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) B463097
theorem B1858085 : Blo 159796 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B11819641 : Blo 159796 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B547721 : Blo 159796 547721 := bstep (se 2 (by rfl) ⟨205395, by rfl⟩ : syracuseStep 547721 = 410791) B410791
theorem B1367117 : Blo 159796 1367117 := bstep (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) B512669
theorem B1466369 : Blo 159796 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B1237841 : Blo 159796 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B550313 : Blo 159796 550313 := bstep (se 2 (by rfl) ⟨206367, by rfl⟩ : syracuseStep 550313 = 412735) B412735
theorem B550583 : Blo 159796 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B551339 : Blo 159796 551339 := bstep (se 1 (by rfl) ⟨413504, by rfl⟩ : syracuseStep 551339 = 827009) B827009
theorem B1403513 : Blo 159796 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B256751 : Blo 159796 256751 := bstep (se 1 (by rfl) ⟨192563, by rfl⟩ : syracuseStep 256751 = 385127) B385127
theorem B256879 : Blo 159796 256879 := bstep (se 1 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 256879 = 385319) B385319
theorem B4844729 : Blo 159796 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1043867 : Blo 159796 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B683711 : Blo 159796 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B1241243 : Blo 159796 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B1175795 : Blo 159796 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B159999 : Blo 159796 159999 := bstep (se 1 (by rfl) ⟨119999, by rfl⟩ : syracuseStep 159999 = 239999) B239999
theorem B160159 : Blo 159796 160159 := bstep (se 1 (by rfl) ⟨120119, by rfl⟩ : syracuseStep 160159 = 240239) B240239
theorem B881065 : Blo 159796 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B455159 : Blo 159796 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B160303 : Blo 159796 160303 := bstep (se 1 (by rfl) ⟨120227, by rfl⟩ : syracuseStep 160303 = 240455) B240455
theorem B1241729 : Blo 159796 1241729 := bstep (se 2 (by rfl) ⟨465648, by rfl⟩ : syracuseStep 1241729 = 931297) B931297
theorem B783209 : Blo 159796 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B160703 : Blo 159796 160703 := bstep (se 1 (by rfl) ⟨120527, by rfl⟩ : syracuseStep 160703 = 241055) B241055
theorem B160879 : Blo 159796 160879 := bstep (se 1 (by rfl) ⟨120659, by rfl⟩ : syracuseStep 160879 = 241319) B241319
theorem B160895 : Blo 159796 160895 := bstep (se 1 (by rfl) ⟨120671, by rfl⟩ : syracuseStep 160895 = 241343) B241343
theorem B816317 : Blo 159796 816317 := bstep (se 3 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 816317 = 306119) B306119
theorem B160959 : Blo 159796 160959 := bstep (se 1 (by rfl) ⟨120719, by rfl⟩ : syracuseStep 160959 = 241439) B241439
theorem B161151 : Blo 159796 161151 := bstep (se 1 (by rfl) ⟨120863, by rfl⟩ : syracuseStep 161151 = 241727) B241727
theorem B587261 : Blo 159796 587261 := bstep (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) B220223
theorem B161279 : Blo 159796 161279 := bstep (se 1 (by rfl) ⟨120959, by rfl⟩ : syracuseStep 161279 = 241919) B241919
theorem B161307 : Blo 159796 161307 := bstep (se 1 (by rfl) ⟨120980, by rfl⟩ : syracuseStep 161307 = 241961) B241961
theorem B161487 : Blo 159796 161487 := bstep (se 1 (by rfl) ⟨121115, by rfl⟩ : syracuseStep 161487 = 242231) B242231
theorem B161647 : Blo 159796 161647 := bstep (se 1 (by rfl) ⟨121235, by rfl⟩ : syracuseStep 161647 = 242471) B242471
theorem B161727 : Blo 159796 161727 := bstep (se 1 (by rfl) ⟨121295, by rfl⟩ : syracuseStep 161727 = 242591) B242591
theorem B1308847 : Blo 159796 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B620743 : Blo 159796 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B162043 : Blo 159796 162043 := bstep (se 1 (by rfl) ⟨121532, by rfl⟩ : syracuseStep 162043 = 243065) B243065
theorem B162047 : Blo 159796 162047 := bstep (se 1 (by rfl) ⟨121535, by rfl⟩ : syracuseStep 162047 = 243071) B243071
theorem B162151 : Blo 159796 162151 := bstep (se 1 (by rfl) ⟨121613, by rfl⟩ : syracuseStep 162151 = 243227) B243227
theorem B162271 : Blo 159796 162271 := bstep (se 1 (by rfl) ⟨121703, by rfl⟩ : syracuseStep 162271 = 243407) B243407
theorem B621047 : Blo 159796 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B3570277 : Blo 159796 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B162407 : Blo 159796 162407 := bstep (se 1 (by rfl) ⟨121805, by rfl⟩ : syracuseStep 162407 = 243611) B243611
theorem B162431 : Blo 159796 162431 := bstep (se 1 (by rfl) ⟨121823, by rfl⟩ : syracuseStep 162431 = 243647) B243647
theorem B3144359 : Blo 159796 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B162543 : Blo 159796 162543 := bstep (se 1 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 162543 = 243815) B243815
theorem B28146653 : Blo 159796 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B162799 : Blo 159796 162799 := bstep (se 1 (by rfl) ⟨122099, by rfl⟩ : syracuseStep 162799 = 244199) B244199
theorem B162847 : Blo 159796 162847 := bstep (se 1 (by rfl) ⟨122135, by rfl⟩ : syracuseStep 162847 = 244271) B244271
theorem B294049 : Blo 159796 294049 := bstep (se 2 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 294049 = 220537) B220537
theorem B457903 : Blo 159796 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B1834163 : Blo 159796 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B163295 : Blo 159796 163295 := bstep (se 1 (by rfl) ⟨122471, by rfl⟩ : syracuseStep 163295 = 244943) B244943
theorem B163355 : Blo 159796 163355 := bstep (se 1 (by rfl) ⟨122516, by rfl⟩ : syracuseStep 163355 = 245033) B245033
theorem B163375 : Blo 159796 163375 := bstep (se 1 (by rfl) ⟨122531, by rfl⟩ : syracuseStep 163375 = 245063) B245063
theorem B1375865 : Blo 159796 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B261787 : Blo 159796 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B163775 : Blo 159796 163775 := bstep (se 1 (by rfl) ⟨122831, by rfl⟩ : syracuseStep 163775 = 245663) B245663
theorem B360503 : Blo 159796 360503 := bstep (se 1 (by rfl) ⟨270377, by rfl⟩ : syracuseStep 360503 = 540755) B540755
theorem B360539 : Blo 159796 360539 := bstep (se 1 (by rfl) ⟨270404, by rfl⟩ : syracuseStep 360539 = 540809) B540809
theorem B360935 : Blo 159796 360935 := bstep (se 1 (by rfl) ⟨270701, by rfl⟩ : syracuseStep 360935 = 541403) B541403
theorem B361007 : Blo 159796 361007 := bstep (se 1 (by rfl) ⟨270755, by rfl⟩ : syracuseStep 361007 = 541511) B541511
theorem B361043 : Blo 159796 361043 := bstep (se 1 (by rfl) ⟨270782, by rfl⟩ : syracuseStep 361043 = 541565) B541565
theorem B1475995 : Blo 159796 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B362249 : Blo 159796 362249 := bstep (se 2 (by rfl) ⟨135843, by rfl⟩ : syracuseStep 362249 = 271687) B271687
theorem B363167 : Blo 159796 363167 := bstep (se 1 (by rfl) ⟨272375, by rfl⟩ : syracuseStep 363167 = 544751) B544751
theorem B756487 : Blo 159796 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B461639 : Blo 159796 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B822635 : Blo 159796 822635 := bstep (se 1 (by rfl) ⟨616976, by rfl⟩ : syracuseStep 822635 = 1233953) B1233953
theorem B3509725 : Blo 159796 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B364175 : Blo 159796 364175 := bstep (se 1 (by rfl) ⟨273131, by rfl⟩ : syracuseStep 364175 = 546263) B546263
theorem B823283 : Blo 159796 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B365147 : Blo 159796 365147 := bstep (se 1 (by rfl) ⟨273860, by rfl⟩ : syracuseStep 365147 = 547721) B547721
theorem B4690649 : Blo 159796 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B825227 : Blo 159796 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B366875 : Blo 159796 366875 := bstep (se 1 (by rfl) ⟨275156, by rfl⟩ : syracuseStep 366875 = 550313) B550313
theorem B367055 : Blo 159796 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B465821 : Blo 159796 465821 := bstep (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) B174683
theorem B367559 : Blo 159796 367559 := bstep (se 1 (by rfl) ⟨275669, by rfl⟩ : syracuseStep 367559 = 551339) B551339
theorem B171167 : Blo 159796 171167 := bstep (se 1 (by rfl) ⟨128375, by rfl⟩ : syracuseStep 171167 = 256751) B256751
theorem B695911 : Blo 159796 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B270391 : Blo 159796 270391 := bstep (se 1 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 270391 = 405587) B405587
theorem B827495 : Blo 159796 827495 := bstep (se 1 (by rfl) ⟨620621, by rfl⟩ : syracuseStep 827495 = 1241243) B1241243
theorem B1745129 : Blo 159796 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B827657 : Blo 159796 827657 := bstep (se 2 (by rfl) ⟨310371, by rfl⟩ : syracuseStep 827657 = 620743) B620743
theorem B303439 : Blo 159796 303439 := bstep (se 1 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 303439 = 455159) B455159
theorem B827819 : Blo 159796 827819 := bstep (se 1 (by rfl) ⟨620864, by rfl⟩ : syracuseStep 827819 = 1241729) B1241729
theorem B12919277 : Blo 159796 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B4760369 : Blo 159796 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B206059 : Blo 159796 206059 := bstep (se 1 (by rfl) ⟨154544, by rfl⟩ : syracuseStep 206059 = 309089) B309089
theorem B1386011 : Blo 159796 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B1222775 : Blo 159796 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B272639 : Blo 159796 272639 := bstep (se 1 (by rfl) ⟨204479, by rfl⟩ : syracuseStep 272639 = 408959) B408959
theorem B7908191 : Blo 159796 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B240635 : Blo 159796 240635 := bstep (se 1 (by rfl) ⟨180476, by rfl⟩ : syracuseStep 240635 = 360953) B360953
theorem B240875 : Blo 159796 240875 := bstep (se 1 (by rfl) ⟨180656, by rfl⟩ : syracuseStep 240875 = 361313) B361313
theorem B7482617 : Blo 159796 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B437615 : Blo 159796 437615 := bstep (se 1 (by rfl) ⟨328211, by rfl⟩ : syracuseStep 437615 = 656423) B656423
theorem B404959 : Blo 159796 404959 := bstep (se 1 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 404959 = 607439) B607439
theorem B12496913 : Blo 159796 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B232697939 : Blo 159796 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1781927 : Blo 159796 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B2306555 : Blo 159796 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B733751 : Blo 159796 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B406235 : Blo 159796 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B242459 : Blo 159796 242459 := bstep (se 1 (by rfl) ⟨181844, by rfl⟩ : syracuseStep 242459 = 363689) B363689
theorem B866015 : Blo 159796 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B5027777 : Blo 159796 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B767987 : Blo 159796 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B243995 : Blo 159796 243995 := bstep (se 1 (by rfl) ⟨182996, by rfl⟩ : syracuseStep 243995 = 365993) B365993
theorem B244031 : Blo 159796 244031 := bstep (se 1 (by rfl) ⟨183023, by rfl⟩ : syracuseStep 244031 = 366047) B366047
theorem B932255 : Blo 159796 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B342505 : Blo 159796 342505 := bstep (se 2 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 342505 = 256879) B256879
theorem B244649 : Blo 159796 244649 := bstep (se 2 (by rfl) ⟨91743, by rfl⟩ : syracuseStep 244649 = 183487) B183487
theorem B540161 : Blo 159796 540161 := bstep (se 2 (by rfl) ⟨202560, by rfl⟩ : syracuseStep 540161 = 405121) B405121
theorem B3326035 : Blo 159796 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B180463 : Blo 159796 180463 := bstep (se 1 (by rfl) ⟨135347, by rfl⟩ : syracuseStep 180463 = 270695) B270695
theorem B3129905 : Blo 159796 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B180895 : Blo 159796 180895 := bstep (se 1 (by rfl) ⟨135671, by rfl⟩ : syracuseStep 180895 = 271343) B271343
theorem B1164203 : Blo 159796 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B312545 : Blo 159796 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B935675 : Blo 159796 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B182119 : Blo 159796 182119 := bstep (se 1 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 182119 = 273179) B273179
theorem B182767 : Blo 159796 182767 := bstep (se 1 (by rfl) ⟨137075, by rfl⟩ : syracuseStep 182767 = 274151) B274151
theorem B576335 : Blo 159796 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B544157 : Blo 159796 544157 := bstep (se 3 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 544157 = 204059) B204059
theorem B544211 : Blo 159796 544211 := bstep (se 1 (by rfl) ⟨408158, by rfl⟩ : syracuseStep 544211 = 816317) B816317
theorem B3296857 : Blo 159796 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B610537 : Blo 159796 610537 := bstep (se 2 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 610537 = 457903) B457903
theorem B414031 : Blo 159796 414031 := bstep (se 1 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 414031 = 621047) B621047
theorem B708983 : Blo 159796 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B18764435 : Blo 159796 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B349049 : Blo 159796 349049 := bstep (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) B261787
theorem B546479 : Blo 159796 546479 := bstep (se 1 (by rfl) ⟨409859, by rfl⟩ : syracuseStep 546479 = 819719) B819719
theorem B546857 : Blo 159796 546857 := bstep (se 2 (by rfl) ⟨205071, by rfl⟩ : syracuseStep 546857 = 410143) B410143
theorem B809513 : Blo 159796 809513 := bstep (se 2 (by rfl) ⟨303567, by rfl⟩ : syracuseStep 809513 = 607135) B607135
theorem B876743 : Blo 159796 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B1794251 : Blo 159796 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B418127 : Blo 159796 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B2941481 : Blo 159796 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B7627385 : Blo 159796 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B1860407 : Blo 159796 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B811943 : Blo 159796 811943 := bstep (se 1 (by rfl) ⟨608957, by rfl⟩ : syracuseStep 811943 = 1217915) B1217915
theorem B1238327 : Blo 159796 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B1566029 : Blo 159796 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B1238723 : Blo 159796 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B550799 : Blo 159796 550799 := bstep (se 1 (by rfl) ⟨413099, by rfl⟩ : syracuseStep 550799 = 826199) B826199
theorem B550907 : Blo 159796 550907 := bstep (se 1 (by rfl) ⟨413180, by rfl⟩ : syracuseStep 550907 = 826361) B826361
theorem B911411 : Blo 159796 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B288839 : Blo 159796 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B977579 : Blo 159796 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B1174753 : Blo 159796 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B1568261 : Blo 159796 1568261 := bstep (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) B294049
theorem B2977769 : Blo 159796 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B159967 : Blo 159796 159967 := bstep (se 1 (by rfl) ⟨119975, by rfl⟩ : syracuseStep 159967 = 239951) B239951
theorem B160255 : Blo 159796 160255 := bstep (se 1 (by rfl) ⟨120191, by rfl⟩ : syracuseStep 160255 = 240383) B240383
theorem B1077943 : Blo 159796 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B815993 : Blo 159796 815993 := bstep (se 2 (by rfl) ⟨305997, by rfl⟩ : syracuseStep 815993 = 611995) B611995
theorem B881567 : Blo 159796 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B455807 : Blo 159796 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B160991 : Blo 159796 160991 := bstep (se 1 (by rfl) ⟨120743, by rfl⟩ : syracuseStep 160991 = 241487) B241487
theorem B161071 : Blo 159796 161071 := bstep (se 1 (by rfl) ⟨120803, by rfl⟩ : syracuseStep 161071 = 241607) B241607
theorem B783863 : Blo 159796 783863 := bstep (se 1 (by rfl) ⟨587897, by rfl⟩ : syracuseStep 783863 = 1175795) B1175795
theorem B423451 : Blo 159796 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B161311 : Blo 159796 161311 := bstep (se 1 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 161311 = 241967) B241967
theorem B161471 : Blo 159796 161471 := bstep (se 1 (by rfl) ⟨121103, by rfl⟩ : syracuseStep 161471 = 242207) B242207
theorem B522139 : Blo 159796 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B161703 : Blo 159796 161703 := bstep (se 1 (by rfl) ⟨121277, by rfl⟩ : syracuseStep 161703 = 242555) B242555
theorem B161823 : Blo 159796 161823 := bstep (se 1 (by rfl) ⟨121367, by rfl⟩ : syracuseStep 161823 = 242735) B242735
theorem B161903 : Blo 159796 161903 := bstep (se 1 (by rfl) ⟨121427, by rfl⟩ : syracuseStep 161903 = 242855) B242855
theorem B15759521 : Blo 159796 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B161999 : Blo 159796 161999 := bstep (se 1 (by rfl) ⟨121499, by rfl⟩ : syracuseStep 161999 = 242999) B242999
theorem B162119 : Blo 159796 162119 := bstep (se 1 (by rfl) ⟨121589, by rfl⟩ : syracuseStep 162119 = 243179) B243179
theorem B620903 : Blo 159796 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B162203 : Blo 159796 162203 := bstep (se 1 (by rfl) ⟨121652, by rfl⟩ : syracuseStep 162203 = 243305) B243305
theorem B162351 : Blo 159796 162351 := bstep (se 1 (by rfl) ⟨121763, by rfl⟩ : syracuseStep 162351 = 243527) B243527
theorem B162471 : Blo 159796 162471 := bstep (se 1 (by rfl) ⟨121853, by rfl⟩ : syracuseStep 162471 = 243707) B243707
theorem B162511 : Blo 159796 162511 := bstep (se 1 (by rfl) ⟨121883, by rfl⟩ : syracuseStep 162511 = 243767) B243767
theorem B162555 : Blo 159796 162555 := bstep (se 1 (by rfl) ⟨121916, by rfl⟩ : syracuseStep 162555 = 243833) B243833
theorem B162559 : Blo 159796 162559 := bstep (se 1 (by rfl) ⟨121919, by rfl⟩ : syracuseStep 162559 = 243839) B243839
theorem B162591 : Blo 159796 162591 := bstep (se 1 (by rfl) ⟨121943, by rfl⟩ : syracuseStep 162591 = 243887) B243887
theorem B162751 : Blo 159796 162751 := bstep (se 1 (by rfl) ⟨122063, by rfl⟩ : syracuseStep 162751 = 244127) B244127
theorem B2096239 : Blo 159796 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B228587 : Blo 159796 228587 := bstep (se 1 (by rfl) ⟨171440, by rfl⟩ : syracuseStep 228587 = 342881) B342881
theorem B163483 : Blo 159796 163483 := bstep (se 1 (by rfl) ⟨122612, by rfl⟩ : syracuseStep 163483 = 245225) B245225
theorem B917243 : Blo 159796 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B360521 : Blo 159796 360521 := bstep (se 2 (by rfl) ⟨135195, by rfl⟩ : syracuseStep 360521 = 270391) B270391
theorem B620527837 : Blo 159796 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B4653677 : Blo 159796 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B1115005 : Blo 159796 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B623783 : Blo 159796 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B1967993 : Blo 159796 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B362771 : Blo 159796 362771 := bstep (se 1 (by rfl) ⟨272078, by rfl⟩ : syracuseStep 362771 = 544157) B544157
theorem B362807 : Blo 159796 362807 := bstep (se 1 (by rfl) ⟨272105, by rfl⟩ : syracuseStep 362807 = 544211) B544211
theorem B1215485 : Blo 159796 1215485 := bstep (se 3 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 1215485 = 455807) B455807
theorem B364319 : Blo 159796 364319 := bstep (se 1 (by rfl) ⟨273239, by rfl⟩ : syracuseStep 364319 = 546479) B546479
theorem B364571 : Blo 159796 364571 := bstep (se 1 (by rfl) ⟨273428, by rfl⟩ : syracuseStep 364571 = 546857) B546857
theorem B4395809 : Blo 159796 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B432317 : Blo 159796 432317 := bstep (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) B162119
theorem B825551 : Blo 159796 825551 := bstep (se 1 (by rfl) ⟨619163, by rfl⟩ : syracuseStep 825551 = 1238327) B1238327
theorem B924007 : Blo 159796 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B825815 : Blo 159796 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B367199 : Blo 159796 367199 := bstep (se 1 (by rfl) ⟨275399, by rfl⟩ : syracuseStep 367199 = 550799) B550799
theorem B367271 : Blo 159796 367271 := bstep (se 1 (by rfl) ⟨275453, by rfl⟩ : syracuseStep 367271 = 550907) B550907
theorem B4988411 : Blo 159796 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B696185 : Blo 159796 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B8331275 : Blo 159796 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B1187951 : Blo 159796 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B270823 : Blo 159796 270823 := bstep (se 1 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 270823 = 406235) B406235
theorem B3351851 : Blo 159796 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B2794985 : Blo 159796 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B927881 : Blo 159796 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B7940717 : Blo 159796 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B240335 : Blo 159796 240335 := bstep (se 1 (by rfl) ⟨180251, by rfl⟩ : syracuseStep 240335 = 360503) B360503
theorem B240359 : Blo 159796 240359 := bstep (se 1 (by rfl) ⟨180269, by rfl⟩ : syracuseStep 240359 = 360539) B360539
theorem B4434713 : Blo 159796 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B240617 : Blo 159796 240617 := bstep (se 2 (by rfl) ⟨90231, by rfl⟩ : syracuseStep 240617 = 180463) B180463
theorem B240623 : Blo 159796 240623 := bstep (se 1 (by rfl) ⟨180467, by rfl⟩ : syracuseStep 240623 = 360935) B360935
theorem B240671 : Blo 159796 240671 := bstep (se 1 (by rfl) ⟨180503, by rfl⟩ : syracuseStep 240671 = 361007) B361007
theorem B240695 : Blo 159796 240695 := bstep (se 1 (by rfl) ⟨180521, by rfl⟩ : syracuseStep 240695 = 361043) B361043
theorem B404585 : Blo 159796 404585 := bstep (se 2 (by rfl) ⟨151719, by rfl⟩ : syracuseStep 404585 = 303439) B303439
theorem B208363 : Blo 159796 208363 := bstep (se 1 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 208363 = 312545) B312545
theorem B241193 : Blo 159796 241193 := bstep (se 2 (by rfl) ⟨90447, by rfl⟩ : syracuseStep 241193 = 180895) B180895
theorem B241499 : Blo 159796 241499 := bstep (se 1 (by rfl) ⟨181124, by rfl⟩ : syracuseStep 241499 = 362249) B362249
theorem B7843949 : Blo 159796 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B274745 : Blo 159796 274745 := bstep (se 2 (by rfl) ⟨103029, by rfl⟩ : syracuseStep 274745 = 206059) B206059
theorem B242111 : Blo 159796 242111 := bstep (se 1 (by rfl) ⟨181583, by rfl⟩ : syracuseStep 242111 = 363167) B363167
theorem B930797 : Blo 159796 930797 := bstep (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) B349049
theorem B242783 : Blo 159796 242783 := bstep (se 1 (by rfl) ⟨182087, by rfl⟩ : syracuseStep 242783 = 364175) B364175
theorem B242825 : Blo 159796 242825 := bstep (se 2 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 242825 = 182119) B182119
theorem B472655 : Blo 159796 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B243431 : Blo 159796 243431 := bstep (se 1 (by rfl) ⟨182573, by rfl⟩ : syracuseStep 243431 = 365147) B365147
theorem B3127099 : Blo 159796 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B243689 : Blo 159796 243689 := bstep (se 2 (by rfl) ⟨91383, by rfl⟩ : syracuseStep 243689 = 182767) B182767
theorem B244583 : Blo 159796 244583 := bstep (se 1 (by rfl) ⟨183437, by rfl⟩ : syracuseStep 244583 = 366875) B366875
theorem B244703 : Blo 159796 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B539675 : Blo 159796 539675 := bstep (se 1 (by rfl) ⟨404756, by rfl⟩ : syracuseStep 539675 = 809513) B809513
theorem B310547 : Blo 159796 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B539945 : Blo 159796 539945 := bstep (se 2 (by rfl) ⟨202479, by rfl⟩ : syracuseStep 539945 = 404959) B404959
theorem B245039 : Blo 159796 245039 := bstep (se 1 (by rfl) ⟨183779, by rfl⟩ : syracuseStep 245039 = 367559) B367559
theorem B1196167 : Blo 159796 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B541295 : Blo 159796 541295 := bstep (se 1 (by rfl) ⟨405971, by rfl⟩ : syracuseStep 541295 = 811943) B811943
theorem B1655741 : Blo 159796 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B607607 : Blo 159796 607607 := bstep (se 1 (by rfl) ⟨455705, by rfl⟩ : syracuseStep 607607 = 911411) B911411
theorem B181759 : Blo 159796 181759 := bstep (se 1 (by rfl) ⟨136319, by rfl⟩ : syracuseStep 181759 = 272639) B272639
theorem B1231037 : Blo 159796 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B543995 : Blo 159796 543995 := bstep (se 1 (by rfl) ⟨407996, by rfl⟩ : syracuseStep 543995 = 815993) B815993
theorem B609565 : Blo 159796 609565 := bstep (se 3 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 609565 = 228587) B228587
theorem B577343 : Blo 159796 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B511991 : Blo 159796 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B10506347 : Blo 159796 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B611495 : Blo 159796 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B2086603 : Blo 159796 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B776135 : Blo 159796 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B20339693 : Blo 159796 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B548423 : Blo 159796 548423 := bstep (se 1 (by rfl) ⟨411317, by rfl⟩ : syracuseStep 548423 = 822635) B822635
theorem B548855 : Blo 159796 548855 := bstep (se 1 (by rfl) ⟨411641, by rfl⟩ : syracuseStep 548855 = 823283) B823283
theorem B12509623 : Blo 159796 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B1008649 : Blo 159796 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B550151 : Blo 159796 550151 := bstep (se 1 (by rfl) ⟨412613, by rfl⟩ : syracuseStep 550151 = 825227) B825227
theorem B1566337 : Blo 159796 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B4679633 : Blo 159796 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B551663 : Blo 159796 551663 := bstep (se 1 (by rfl) ⟨413747, by rfl⟩ : syracuseStep 551663 = 827495) B827495
theorem B584495 : Blo 159796 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B551771 : Blo 159796 551771 := bstep (se 1 (by rfl) ⟨413828, by rfl⟩ : syracuseStep 551771 = 827657) B827657
theorem B551879 : Blo 159796 551879 := bstep (se 1 (by rfl) ⟨413909, by rfl⟩ : syracuseStep 551879 = 827819) B827819
theorem B814049 : Blo 159796 814049 := bstep (se 2 (by rfl) ⟨305268, by rfl⟩ : syracuseStep 814049 = 610537) B610537
theorem B8612851 : Blo 159796 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B552041 : Blo 159796 552041 := bstep (se 2 (by rfl) ⟨207015, by rfl⟩ : syracuseStep 552041 = 414031) B414031
theorem B3173579 : Blo 159796 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B1240271 : Blo 159796 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B1044019 : Blo 159796 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B1437257 : Blo 159796 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B192559 : Blo 159796 192559 := bstep (se 1 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 192559 = 288839) B288839
theorem B815183 : Blo 159796 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B651719 : Blo 159796 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B5272127 : Blo 159796 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B160423 : Blo 159796 160423 := bstep (se 1 (by rfl) ⟨120317, by rfl⟩ : syracuseStep 160423 = 240635) B240635
theorem B160583 : Blo 159796 160583 := bstep (se 1 (by rfl) ⟨120437, by rfl⟩ : syracuseStep 160583 = 240875) B240875
theorem B1536893 : Blo 159796 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B291743 : Blo 159796 291743 := bstep (se 1 (by rfl) ⟨218807, by rfl⟩ : syracuseStep 291743 = 437615) B437615
theorem B1045507 : Blo 159796 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B2258405 : Blo 159796 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B1537703 : Blo 159796 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B489167 : Blo 159796 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B456445 : Blo 159796 456445 := bstep (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) B171167
theorem B161639 : Blo 159796 161639 := bstep (se 1 (by rfl) ⟨121229, by rfl⟩ : syracuseStep 161639 = 242459) B242459
theorem B587711 : Blo 159796 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B456673 : Blo 159796 456673 := bstep (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) B342505
theorem B522575 : Blo 159796 522575 := bstep (se 1 (by rfl) ⟨391931, by rfl⟩ : syracuseStep 522575 = 783863) B783863
theorem B162663 : Blo 159796 162663 := bstep (se 1 (by rfl) ⟨121997, by rfl⟩ : syracuseStep 162663 = 243995) B243995
theorem B162687 : Blo 159796 162687 := bstep (se 1 (by rfl) ⟨122015, by rfl⟩ : syracuseStep 162687 = 244031) B244031
theorem B621503 : Blo 159796 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B163099 : Blo 159796 163099 := bstep (se 1 (by rfl) ⟨122324, by rfl⟩ : syracuseStep 163099 = 244649) B244649
theorem B360107 : Blo 159796 360107 := bstep (se 1 (by rfl) ⟨270080, by rfl⟩ : syracuseStep 360107 = 540161) B540161
theorem B360863 : Blo 159796 360863 := bstep (se 1 (by rfl) ⟨270647, by rfl⟩ : syracuseStep 360863 = 541295) B541295
theorem B361097 : Blo 159796 361097 := bstep (se 2 (by rfl) ⟨135411, by rfl⟩ : syracuseStep 361097 = 270823) B270823
theorem B1311995 : Blo 159796 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B1344865 : Blo 159796 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B820691 : Blo 159796 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B362663 : Blo 159796 362663 := bstep (se 1 (by rfl) ⟨271997, by rfl⟩ : syracuseStep 362663 = 543995) B543995
theorem B66717989 : Blo 159796 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B365615 : Blo 159796 365615 := bstep (se 1 (by rfl) ⟨274211, by rfl⟩ : syracuseStep 365615 = 548423) B548423
theorem B464123 : Blo 159796 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B365903 : Blo 159796 365903 := bstep (se 1 (by rfl) ⟨274427, by rfl⟩ : syracuseStep 365903 = 548855) B548855
theorem B366767 : Blo 159796 366767 := bstep (se 1 (by rfl) ⟨275075, by rfl⟩ : syracuseStep 366767 = 550151) B550151
theorem B2234567 : Blo 159796 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B2202173 : Blo 159796 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B3119755 : Blo 159796 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B367775 : Blo 159796 367775 := bstep (se 1 (by rfl) ⟨275831, by rfl⟩ : syracuseStep 367775 = 551663) B551663
theorem B2956475 : Blo 159796 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B367847 : Blo 159796 367847 := bstep (se 1 (by rfl) ⟨275885, by rfl⟩ : syracuseStep 367847 = 551771) B551771
theorem B367919 : Blo 159796 367919 := bstep (se 1 (by rfl) ⟨275939, by rfl⟩ : syracuseStep 367919 = 551879) B551879
theorem B269723 : Blo 159796 269723 := bstep (se 1 (by rfl) ⟨202292, by rfl⟩ : syracuseStep 269723 = 404585) B404585
theorem B368027 : Blo 159796 368027 := bstep (se 1 (by rfl) ⟨276020, by rfl⟩ : syracuseStep 368027 = 552041) B552041
theorem B826847 : Blo 159796 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B958171 : Blo 159796 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B4169465 : Blo 159796 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B434479 : Blo 159796 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B3514751 : Blo 159796 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B1024595 : Blo 159796 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B1025135 : Blo 159796 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B207031 : Blo 159796 207031 := bstep (se 1 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 207031 = 310547) B310547
theorem B240071 : Blo 159796 240071 := bstep (se 1 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 240071 = 360107) B360107
theorem B240347 : Blo 159796 240347 := bstep (se 1 (by rfl) ⟨180260, by rfl⟩ : syracuseStep 240347 = 360521) B360521
theorem B827370449 : Blo 159796 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B405071 : Blo 159796 405071 := bstep (se 1 (by rfl) ⟨303803, by rfl⟩ : syracuseStep 405071 = 607607) B607607
theorem B1486673 : Blo 159796 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B241847 : Blo 159796 241847 := bstep (se 1 (by rfl) ⟨181385, by rfl⟩ : syracuseStep 241847 = 362771) B362771
theorem B241871 : Blo 159796 241871 := bstep (se 1 (by rfl) ⟨181403, by rfl⟩ : syracuseStep 241871 = 362807) B362807
theorem B242345 : Blo 159796 242345 := bstep (se 2 (by rfl) ⟨90879, by rfl⟩ : syracuseStep 242345 = 181759) B181759
theorem B242879 : Blo 159796 242879 := bstep (se 1 (by rfl) ⟨182159, by rfl⟩ : syracuseStep 242879 = 364319) B364319
theorem B341327 : Blo 159796 341327 := bstep (se 1 (by rfl) ⟨255995, by rfl⟩ : syracuseStep 341327 = 511991) B511991
theorem B243047 : Blo 159796 243047 := bstep (se 1 (by rfl) ⟨182285, by rfl⟩ : syracuseStep 243047 = 364571) B364571
theorem B2930539 : Blo 159796 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B407663 : Blo 159796 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B11483801 : Blo 159796 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B244799 : Blo 159796 244799 := bstep (se 1 (by rfl) ⟨183599, by rfl⟩ : syracuseStep 244799 = 367199) B367199
theorem B244847 : Blo 159796 244847 := bstep (se 1 (by rfl) ⟨183635, by rfl⟩ : syracuseStep 244847 = 367271) B367271
theorem B1392025 : Blo 159796 1392025 := bstep (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) B1044019
theorem B3325607 : Blo 159796 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B5554183 : Blo 159796 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B1394009 : Blo 159796 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B5293811 : Blo 159796 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B542699 : Blo 159796 542699 := bstep (se 1 (by rfl) ⟨407024, by rfl⟩ : syracuseStep 542699 = 814049) B814049
theorem B2115719 : Blo 159796 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B608593 : Blo 159796 608593 := bstep (se 2 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 608593 = 456445) B456445
theorem B608897 : Blo 159796 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B543455 : Blo 159796 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B5229299 : Blo 159796 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B183163 : Blo 159796 183163 := bstep (se 1 (by rfl) ⟨137372, by rfl⟩ : syracuseStep 183163 = 274745) B274745
theorem B1232009 : Blo 159796 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B315103 : Blo 159796 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B11128549 : Blo 159796 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B348383 : Blo 159796 348383 := bstep (se 1 (by rfl) ⟨261287, by rfl⟩ : syracuseStep 348383 = 522575) B522575
theorem B414335 : Blo 159796 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B4445077 : Blo 159796 4445077 := bstep (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) B208363
theorem B1594889 : Blo 159796 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B1103827 : Blo 159796 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B415855 : Blo 159796 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B12671477 : Blo 159796 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B12409805 : Blo 159796 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B810323 : Blo 159796 810323 := bstep (se 1 (by rfl) ⟨607742, by rfl⟩ : syracuseStep 810323 = 1215485) B1215485
theorem B2088449 : Blo 159796 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B384895 : Blo 159796 384895 := bstep (se 1 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 384895 = 577343) B577343
theorem B7004231 : Blo 159796 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B517423 : Blo 159796 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B288211 : Blo 159796 288211 := bstep (se 1 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 288211 = 432317) B432317
theorem B550367 : Blo 159796 550367 := bstep (se 1 (by rfl) ⟨412775, by rfl⟩ : syracuseStep 550367 = 825551) B825551
theorem B812753 : Blo 159796 812753 := bstep (se 2 (by rfl) ⟨304782, by rfl⟩ : syracuseStep 812753 = 609565) B609565
theorem B13559795 : Blo 159796 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B256745 : Blo 159796 256745 := bstep (se 2 (by rfl) ⟨96279, by rfl⟩ : syracuseStep 256745 = 192559) B192559
theorem B1863323 : Blo 159796 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B618587 : Blo 159796 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B160223 : Blo 159796 160223 := bstep (se 1 (by rfl) ⟨120167, by rfl⟩ : syracuseStep 160223 = 240335) B240335
theorem B160239 : Blo 159796 160239 := bstep (se 1 (by rfl) ⟨120179, by rfl⟩ : syracuseStep 160239 = 240359) B240359
theorem B389663 : Blo 159796 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B160411 : Blo 159796 160411 := bstep (se 1 (by rfl) ⟨120308, by rfl⟩ : syracuseStep 160411 = 240617) B240617
theorem B160415 : Blo 159796 160415 := bstep (se 1 (by rfl) ⟨120311, by rfl⟩ : syracuseStep 160415 = 240623) B240623
theorem B160447 : Blo 159796 160447 := bstep (se 1 (by rfl) ⟨120335, by rfl⟩ : syracuseStep 160447 = 240671) B240671
theorem B160463 : Blo 159796 160463 := bstep (se 1 (by rfl) ⟨120347, by rfl⟩ : syracuseStep 160463 = 240695) B240695
theorem B160795 : Blo 159796 160795 := bstep (se 1 (by rfl) ⟨120596, by rfl⟩ : syracuseStep 160795 = 241193) B241193
theorem B160999 : Blo 159796 160999 := bstep (se 1 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 160999 = 241499) B241499
theorem B161407 : Blo 159796 161407 := bstep (se 1 (by rfl) ⟨121055, by rfl⟩ : syracuseStep 161407 = 242111) B242111
theorem B194495 : Blo 159796 194495 := bstep (se 1 (by rfl) ⟨145871, by rfl⟩ : syracuseStep 194495 = 291743) B291743
theorem B620531 : Blo 159796 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B161855 : Blo 159796 161855 := bstep (se 1 (by rfl) ⟨121391, by rfl⟩ : syracuseStep 161855 = 242783) B242783
theorem B161883 : Blo 159796 161883 := bstep (se 1 (by rfl) ⟨121412, by rfl⟩ : syracuseStep 161883 = 242825) B242825
theorem B1505603 : Blo 159796 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B326111 : Blo 159796 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B162287 : Blo 159796 162287 := bstep (se 1 (by rfl) ⟨121715, by rfl⟩ : syracuseStep 162287 = 243431) B243431
theorem B391807 : Blo 159796 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B162459 : Blo 159796 162459 := bstep (se 1 (by rfl) ⟨121844, by rfl⟩ : syracuseStep 162459 = 243689) B243689
theorem B163055 : Blo 159796 163055 := bstep (se 1 (by rfl) ⟨122291, by rfl⟩ : syracuseStep 163055 = 244583) B244583
theorem B163135 : Blo 159796 163135 := bstep (se 1 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 163135 = 244703) B244703
theorem B359783 : Blo 159796 359783 := bstep (se 1 (by rfl) ⟨269837, by rfl⟩ : syracuseStep 359783 = 539675) B539675
theorem B359963 : Blo 159796 359963 := bstep (se 1 (by rfl) ⟨269972, by rfl⟩ : syracuseStep 359963 = 539945) B539945
theorem B163359 : Blo 159796 163359 := bstep (se 1 (by rfl) ⟨122519, by rfl⟩ : syracuseStep 163359 = 245039) B245039
theorem B7405577 : Blo 159796 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B361799 : Blo 159796 361799 := bstep (se 1 (by rfl) ⟨271349, by rfl⟩ : syracuseStep 361799 = 542699) B542699
theorem B1410479 : Blo 159796 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B689897 : Blo 159796 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B362303 : Blo 159796 362303 := bstep (se 1 (by rfl) ⟨271727, by rfl⟩ : syracuseStep 362303 = 543455) B543455
theorem B821339 : Blo 159796 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B232255 : Blo 159796 232255 := bstep (se 1 (by rfl) ⟨174191, by rfl⟩ : syracuseStep 232255 = 348383) B348383
theorem B1970983 : Blo 159796 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B366911 : Blo 159796 366911 := bstep (se 1 (by rfl) ⟨275183, by rfl⟩ : syracuseStep 366911 = 550367) B550367
theorem B171163 : Blo 159796 171163 := bstep (se 1 (by rfl) ⟨128372, by rfl⟩ : syracuseStep 171163 = 256745) B256745
theorem B270047 : Blo 159796 270047 := bstep (se 1 (by rfl) ⟨202535, by rfl⟩ : syracuseStep 270047 = 405071) B405071
theorem B3907385 : Blo 159796 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B991115 : Blo 159796 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B271775 : Blo 159796 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B239855 : Blo 159796 239855 := bstep (se 1 (by rfl) ⟨179891, by rfl⟩ : syracuseStep 239855 = 359783) B359783
theorem B239975 : Blo 159796 239975 := bstep (se 1 (by rfl) ⟨179981, by rfl⟩ : syracuseStep 239975 = 359963) B359963
theorem B240575 : Blo 159796 240575 := bstep (se 1 (by rfl) ⟨180431, by rfl⟩ : syracuseStep 240575 = 360863) B360863
theorem B240731 : Blo 159796 240731 := bstep (se 1 (by rfl) ⟨180548, by rfl⟩ : syracuseStep 240731 = 361097) B361097
theorem B929339 : Blo 159796 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B241775 : Blo 159796 241775 := bstep (se 1 (by rfl) ⟨181331, by rfl⟩ : syracuseStep 241775 = 362663) B362663
theorem B44478659 : Blo 159796 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B405931 : Blo 159796 405931 := bstep (se 1 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 405931 = 608897) B608897
theorem B3486199 : Blo 159796 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B276041 : Blo 159796 276041 := bstep (se 2 (by rfl) ⟨103515, by rfl⟩ : syracuseStep 276041 = 207031) B207031
theorem B276223 : Blo 159796 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B243743 : Blo 159796 243743 := bstep (se 1 (by rfl) ⟨182807, by rfl⟩ : syracuseStep 243743 = 365615) B365615
theorem B309415 : Blo 159796 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B243935 : Blo 159796 243935 := bstep (se 1 (by rfl) ⟨182951, by rfl⟩ : syracuseStep 243935 = 365903) B365903
theorem B1063259 : Blo 159796 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B244217 : Blo 159796 244217 := bstep (se 2 (by rfl) ⟨91581, by rfl⟩ : syracuseStep 244217 = 183163) B183163
theorem B244511 : Blo 159796 244511 := bstep (se 1 (by rfl) ⟨183383, by rfl⟩ : syracuseStep 244511 = 366767) B366767
theorem B245183 : Blo 159796 245183 := bstep (se 1 (by rfl) ⟨183887, by rfl⟩ : syracuseStep 245183 = 367775) B367775
theorem B245231 : Blo 159796 245231 := bstep (se 1 (by rfl) ⟨183923, by rfl⟩ : syracuseStep 245231 = 367847) B367847
theorem B245279 : Blo 159796 245279 := bstep (se 1 (by rfl) ⟨183959, by rfl⟩ : syracuseStep 245279 = 367919) B367919
theorem B540215 : Blo 159796 540215 := bstep (se 1 (by rfl) ⟨405161, by rfl⟩ : syracuseStep 540215 = 810323) B810323
theorem B179815 : Blo 159796 179815 := bstep (se 1 (by rfl) ⟨134861, by rfl⟩ : syracuseStep 179815 = 269723) B269723
theorem B245351 : Blo 159796 245351 := bstep (se 1 (by rfl) ⟨184013, by rfl⟩ : syracuseStep 245351 = 368027) B368027
theorem B1392299 : Blo 159796 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B4669487 : Blo 159796 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B2343167 : Blo 159796 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B541835 : Blo 159796 541835 := bstep (se 1 (by rfl) ⟨406376, by rfl⟩ : syracuseStep 541835 = 812753) B812753
theorem B869629 : Blo 159796 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B412391 : Blo 159796 412391 := bstep (se 1 (by rfl) ⟨309293, by rfl⟩ : syracuseStep 412391 = 618587) B618587
theorem B413687 : Blo 159796 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B1003735 : Blo 159796 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B7655867 : Blo 159796 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B1856033 : Blo 159796 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B2052773 : Blo 159796 2052773 := bstep (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) B384895
theorem B2217071 : Blo 159796 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B579305 : Blo 159796 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B547127 : Blo 159796 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B3529207 : Blo 159796 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1793153 : Blo 159796 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B384281 : Blo 159796 384281 := bstep (se 2 (by rfl) ⟨144105, by rfl⟩ : syracuseStep 384281 = 288211) B288211
theorem B811457 : Blo 159796 811457 := bstep (se 2 (by rfl) ⟨304296, by rfl⟩ : syracuseStep 811457 = 608593) B608593
theorem B3498653 : Blo 159796 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B8447651 : Blo 159796 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B1468115 : Blo 159796 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B420137 : Blo 159796 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B14838065 : Blo 159796 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B551231 : Blo 159796 551231 := bstep (se 1 (by rfl) ⟨413423, by rfl⟩ : syracuseStep 551231 = 826847) B826847
theorem B2779643 : Blo 159796 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B518653 : Blo 159796 518653 := bstep (se 3 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 518653 = 194495) B194495
theorem B683063 : Blo 159796 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B5958845 : Blo 159796 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B683423 : Blo 159796 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B5926769 : Blo 159796 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B9039863 : Blo 159796 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B160047 : Blo 159796 160047 := bstep (se 1 (by rfl) ⟨120035, by rfl⟩ : syracuseStep 160047 = 240071) B240071
theorem B160231 : Blo 159796 160231 := bstep (se 1 (by rfl) ⟨120173, by rfl⟩ : syracuseStep 160231 = 240347) B240347
theorem B551580299 : Blo 159796 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B1242215 : Blo 159796 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B33092813 : Blo 159796 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B1471769 : Blo 159796 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B161231 : Blo 159796 161231 := bstep (se 1 (by rfl) ⟨120923, by rfl⟩ : syracuseStep 161231 = 241847) B241847
theorem B161247 : Blo 159796 161247 := bstep (se 1 (by rfl) ⟨120935, by rfl⟩ : syracuseStep 161247 = 241871) B241871
theorem B554473 : Blo 159796 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B259775 : Blo 159796 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B161563 : Blo 159796 161563 := bstep (se 1 (by rfl) ⟨121172, by rfl⟩ : syracuseStep 161563 = 242345) B242345
theorem B161919 : Blo 159796 161919 := bstep (se 1 (by rfl) ⟨121439, by rfl⟩ : syracuseStep 161919 = 242879) B242879
theorem B522409 : Blo 159796 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B4159673 : Blo 159796 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B227551 : Blo 159796 227551 := bstep (se 1 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 227551 = 341327) B341327
theorem B162031 : Blo 159796 162031 := bstep (se 1 (by rfl) ⟨121523, by rfl⟩ : syracuseStep 162031 = 243047) B243047
theorem B163199 : Blo 159796 163199 := bstep (se 1 (by rfl) ⟨122399, by rfl⟩ : syracuseStep 163199 = 244799) B244799
theorem B163231 : Blo 159796 163231 := bstep (se 1 (by rfl) ⟨122423, by rfl⟩ : syracuseStep 163231 = 244847) B244847
theorem B1277561 : Blo 159796 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B3112991 : Blo 159796 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B361223 : Blo 159796 361223 := bstep (se 1 (by rfl) ⟨270917, by rfl⟩ : syracuseStep 361223 = 541835) B541835
theorem B459931 : Blo 159796 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B88247501 : Blo 159796 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B691537 : Blo 159796 691537 := bstep (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) B518653
theorem B1478047 : Blo 159796 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B364751 : Blo 159796 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B660743 : Blo 159796 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B2627977 : Blo 159796 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B7412381 : Blo 159796 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B367487 : Blo 159796 367487 := bstep (se 1 (by rfl) ⟨275615, by rfl⟩ : syracuseStep 367487 = 551231) B551231
theorem B3972563 : Blo 159796 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B368297 : Blo 159796 368297 := bstep (se 2 (by rfl) ⟨138111, by rfl⟩ : syracuseStep 368297 = 276223) B276223
theorem B696545 : Blo 159796 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B303401 : Blo 159796 303401 := bstep (se 2 (by rfl) ⟨113775, by rfl⟩ : syracuseStep 303401 = 227551) B227551
theorem B828143 : Blo 159796 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B173183 : Blo 159796 173183 := bstep (se 1 (by rfl) ⟨129887, by rfl⟩ : syracuseStep 173183 = 259775) B259775
theorem B239753 : Blo 159796 239753 := bstep (se 2 (by rfl) ⟨89907, by rfl⟩ : syracuseStep 239753 = 179815) B179815
theorem B928199 : Blo 159796 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B241199 : Blo 159796 241199 := bstep (se 1 (by rfl) ⟨180899, by rfl⟩ : syracuseStep 241199 = 361799) B361799
theorem B5353253 : Blo 159796 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B241535 : Blo 159796 241535 := bstep (se 1 (by rfl) ⟨181151, by rfl⟩ : syracuseStep 241535 = 362303) B362303
theorem B1159505 : Blo 159796 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B274927 : Blo 159796 274927 := bstep (se 1 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 274927 = 412391) B412391
theorem B275791 : Blo 159796 275791 := bstep (se 1 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 275791 = 413687) B413687
theorem B309673 : Blo 159796 309673 := bstep (se 2 (by rfl) ⟨116127, by rfl⟩ : syracuseStep 309673 = 232255) B232255
theorem B244607 : Blo 159796 244607 := bstep (se 1 (by rfl) ⟨183455, by rfl⟩ : syracuseStep 244607 = 366911) B366911
theorem B1195435 : Blo 159796 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B180031 : Blo 159796 180031 := bstep (se 1 (by rfl) ⟨135023, by rfl⟩ : syracuseStep 180031 = 270047) B270047
theorem B2604923 : Blo 159796 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B540971 : Blo 159796 540971 := bstep (se 1 (by rfl) ⟨405728, by rfl⟩ : syracuseStep 540971 = 811457) B811457
theorem B541241 : Blo 159796 541241 := bstep (se 2 (by rfl) ⟨202965, by rfl⟩ : syracuseStep 541241 = 405931) B405931
theorem B181183 : Blo 159796 181183 := bstep (se 1 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 181183 = 271775) B271775
theorem B280091 : Blo 159796 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B739297 : Blo 159796 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B3951179 : Blo 159796 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B412553 : Blo 159796 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B4705609 : Blo 159796 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B184027 : Blo 159796 184027 := bstep (se 1 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 184027 = 276041) B276041
theorem B2773115 : Blo 159796 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B708839 : Blo 159796 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B4937051 : Blo 159796 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B1562111 : Blo 159796 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B940319 : Blo 159796 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B547559 : Blo 159796 547559 := bstep (se 1 (by rfl) ⟨410669, by rfl⟩ : syracuseStep 547559 = 821339) B821339
theorem B9329741 : Blo 159796 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B5103911 : Blo 159796 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B1237355 : Blo 159796 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B1368515 : Blo 159796 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B386203 : Blo 159796 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B256187 : Blo 159796 256187 := bstep (se 1 (by rfl) ⟨192140, by rfl⟩ : syracuseStep 256187 = 384281) B384281
theorem B4648265 : Blo 159796 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B912869 : Blo 159796 912869 := bstep (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) B171163
theorem B5631767 : Blo 159796 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B978743 : Blo 159796 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B159903 : Blo 159796 159903 := bstep (se 1 (by rfl) ⟨119927, by rfl⟩ : syracuseStep 159903 = 239855) B239855
theorem B9892043 : Blo 159796 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B159983 : Blo 159796 159983 := bstep (se 1 (by rfl) ⟨119987, by rfl⟩ : syracuseStep 159983 = 239975) B239975
theorem B160383 : Blo 159796 160383 := bstep (se 1 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 160383 = 240575) B240575
theorem B455375 : Blo 159796 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B160487 : Blo 159796 160487 := bstep (se 1 (by rfl) ⟨120365, by rfl⟩ : syracuseStep 160487 = 240731) B240731
theorem B455615 : Blo 159796 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B619559 : Blo 159796 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B6026575 : Blo 159796 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B161183 : Blo 159796 161183 := bstep (se 1 (by rfl) ⟨120887, by rfl⟩ : syracuseStep 161183 = 241775) B241775
theorem B29652439 : Blo 159796 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B367720199 : Blo 159796 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B981179 : Blo 159796 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B162495 : Blo 159796 162495 := bstep (se 1 (by rfl) ⟨121871, by rfl⟩ : syracuseStep 162495 = 243743) B243743
theorem B162623 : Blo 159796 162623 := bstep (se 1 (by rfl) ⟨121967, by rfl⟩ : syracuseStep 162623 = 243935) B243935
theorem B162811 : Blo 159796 162811 := bstep (se 1 (by rfl) ⟨122108, by rfl⟩ : syracuseStep 162811 = 244217) B244217
theorem B163007 : Blo 159796 163007 := bstep (se 1 (by rfl) ⟨122255, by rfl⟩ : syracuseStep 163007 = 244511) B244511
theorem B163455 : Blo 159796 163455 := bstep (se 1 (by rfl) ⟨122591, by rfl⟩ : syracuseStep 163455 = 245183) B245183
theorem B163487 : Blo 159796 163487 := bstep (se 1 (by rfl) ⟨122615, by rfl⟩ : syracuseStep 163487 = 245231) B245231
theorem B163519 : Blo 159796 163519 := bstep (se 1 (by rfl) ⟨122639, by rfl⟩ : syracuseStep 163519 = 245279) B245279
theorem B360143 : Blo 159796 360143 := bstep (se 1 (by rfl) ⟨270107, by rfl⟩ : syracuseStep 360143 = 540215) B540215
theorem B163567 : Blo 159796 163567 := bstep (se 1 (by rfl) ⟨122675, by rfl⟩ : syracuseStep 163567 = 245351) B245351
theorem B851707 : Blo 159796 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B360647 : Blo 159796 360647 := bstep (se 1 (by rfl) ⟨270485, by rfl⟩ : syracuseStep 360647 = 540971) B540971
theorem B360827 : Blo 159796 360827 := bstep (se 1 (by rfl) ⟨270620, by rfl⟩ : syracuseStep 360827 = 541241) B541241
theorem B985729 : Blo 159796 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B626879 : Blo 159796 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B922049 : Blo 159796 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B365039 : Blo 159796 365039 := bstep (se 1 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 365039 = 547559) B547559
theorem B1970729 : Blo 159796 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B464363 : Blo 159796 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B202267 : Blo 159796 202267 := bstep (se 1 (by rfl) ⟨151700, by rfl⟩ : syracuseStep 202267 = 303401) B303401
theorem B824903 : Blo 159796 824903 := bstep (se 1 (by rfl) ⟨618677, by rfl⟩ : syracuseStep 824903 = 1237355) B1237355
theorem B366569 : Blo 159796 366569 := bstep (se 2 (by rfl) ⟨137463, by rfl⟩ : syracuseStep 366569 = 274927) B274927
theorem B170791 : Blo 159796 170791 := bstep (se 1 (by rfl) ⟨128093, by rfl⟩ : syracuseStep 170791 = 256187) B256187
theorem B8035433 : Blo 159796 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B367721 : Blo 159796 367721 := bstep (se 2 (by rfl) ⟨137895, by rfl⟩ : syracuseStep 367721 = 275791) B275791
theorem B6594695 : Blo 159796 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B303583 : Blo 159796 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B303743 : Blo 159796 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B245146799 : Blo 159796 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B240041 : Blo 159796 240041 := bstep (se 2 (by rfl) ⟨90015, by rfl⟩ : syracuseStep 240041 = 180031) B180031
theorem B240095 : Blo 159796 240095 := bstep (se 1 (by rfl) ⟨180071, by rfl⟩ : syracuseStep 240095 = 360143) B360143
theorem B2075327 : Blo 159796 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B240815 : Blo 159796 240815 := bstep (se 1 (by rfl) ⟨180611, by rfl⟩ : syracuseStep 240815 = 361223) B361223
theorem B241577 : Blo 159796 241577 := bstep (se 2 (by rfl) ⟨90591, by rfl⟩ : syracuseStep 241577 = 181183) B181183
theorem B1847285 : Blo 159796 1847285 := bstep (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) B173183
theorem B2634119 : Blo 159796 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B275035 : Blo 159796 275035 := bstep (se 1 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 275035 = 412553) B412553
theorem B58831667 : Blo 159796 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B1848743 : Blo 159796 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B243167 : Blo 159796 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B472559 : Blo 159796 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B440495 : Blo 159796 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B3291367 : Blo 159796 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B6274145 : Blo 159796 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B244991 : Blo 159796 244991 := bstep (se 1 (by rfl) ⟨183743, by rfl⟩ : syracuseStep 244991 = 367487) B367487
theorem B245369 : Blo 159796 245369 := bstep (se 2 (by rfl) ⟨92013, by rfl⟩ : syracuseStep 245369 = 184027) B184027
theorem B245531 : Blo 159796 245531 := bstep (se 1 (by rfl) ⟨184148, by rfl⟩ : syracuseStep 245531 = 368297) B368297
theorem B39536585 : Blo 159796 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B3098843 : Blo 159796 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B608579 : Blo 159796 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B3754511 : Blo 159796 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B773003 : Blo 159796 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B412897 : Blo 159796 412897 := bstep (se 2 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 412897 = 309673) B309673
theorem B413039 : Blo 159796 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B4542437 : Blo 159796 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B1593913 : Blo 159796 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B2609981 : Blo 159796 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B186727 : Blo 159796 186727 := bstep (se 1 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 186727 = 280091) B280091
theorem B514937 : Blo 159796 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B613241 : Blo 159796 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B1041407 : Blo 159796 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B4941587 : Blo 159796 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B6219827 : Blo 159796 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B2648375 : Blo 159796 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B3402607 : Blo 159796 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B912343 : Blo 159796 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B552095 : Blo 159796 552095 := bstep (se 1 (by rfl) ⟨414071, by rfl⟩ : syracuseStep 552095 = 828143) B828143
theorem B159835 : Blo 159796 159835 := bstep (se 1 (by rfl) ⟨119876, by rfl⟩ : syracuseStep 159835 = 239753) B239753
theorem B618799 : Blo 159796 618799 := bstep (se 1 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 618799 = 928199) B928199
theorem B160799 : Blo 159796 160799 := bstep (se 1 (by rfl) ⟨120599, by rfl⟩ : syracuseStep 160799 = 241199) B241199
theorem B3568835 : Blo 159796 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B161023 : Blo 159796 161023 := bstep (se 1 (by rfl) ⟨120767, by rfl⟩ : syracuseStep 161023 = 241535) B241535
theorem B3503969 : Blo 159796 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B654119 : Blo 159796 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B163071 : Blo 159796 163071 := bstep (se 1 (by rfl) ⟨122303, by rfl⟩ : syracuseStep 163071 = 244607) B244607
theorem B1736615 : Blo 159796 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B2065895 : Blo 159796 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B1313819 : Blo 159796 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B1739987 : Blo 159796 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B1314305 : Blo 159796 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B1216457 : Blo 159796 1216457 := bstep (se 2 (by rfl) ⟨456171, by rfl⟩ : syracuseStep 1216457 = 912343) B912343
theorem B13177565 : Blo 159796 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B4396463 : Blo 159796 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B825065 : Blo 159796 825065 := bstep (se 2 (by rfl) ⟨309399, by rfl⟩ : syracuseStep 825065 = 618799) B618799
theorem B202495 : Blo 159796 202495 := bstep (se 1 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 202495 = 303743) B303743
theorem B694271 : Blo 159796 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B366713 : Blo 159796 366713 := bstep (se 2 (by rfl) ⟨137517, by rfl⟩ : syracuseStep 366713 = 275035) B275035
theorem B1383551 : Blo 159796 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B269689 : Blo 159796 269689 := bstep (se 2 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 269689 = 202267) B202267
theorem B368063 : Blo 159796 368063 := bstep (se 1 (by rfl) ⟨276047, by rfl⟩ : syracuseStep 368063 = 552095) B552095
theorem B2335979 : Blo 159796 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B436079 : Blo 159796 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B1157743 : Blo 159796 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B240431 : Blo 159796 240431 := bstep (se 1 (by rfl) ⟨180323, by rfl⟩ : syracuseStep 240431 = 360647) B360647
theorem B240551 : Blo 159796 240551 := bstep (se 1 (by rfl) ⟨180413, by rfl⟩ : syracuseStep 240551 = 360827) B360827
theorem B404777 : Blo 159796 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B26357723 : Blo 159796 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B405719 : Blo 159796 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B2503007 : Blo 159796 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B275359 : Blo 159796 275359 := bstep (se 1 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 275359 = 413039) B413039
theorem B3028291 : Blo 159796 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B243359 : Blo 159796 243359 := bstep (se 1 (by rfl) ⟨182519, by rfl⟩ : syracuseStep 243359 = 365039) B365039
theorem B309575 : Blo 159796 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B4536809 : Blo 159796 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B1260157 : Blo 159796 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B244379 : Blo 159796 244379 := bstep (se 1 (by rfl) ⟨183284, by rfl⟩ : syracuseStep 244379 = 366569) B366569
theorem B343291 : Blo 159796 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B408827 : Blo 159796 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B5356955 : Blo 159796 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B245147 : Blo 159796 245147 := bstep (se 1 (by rfl) ⟨183860, by rfl⟩ : syracuseStep 245147 = 367721) B367721
theorem B163431199 : Blo 159796 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B4146551 : Blo 159796 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B1231523 : Blo 159796 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B1756079 : Blo 159796 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B248969 : Blo 159796 248969 := bstep (se 2 (by rfl) ⟨93363, by rfl⟩ : syracuseStep 248969 = 186727) B186727
theorem B2379223 : Blo 159796 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1232495 : Blo 159796 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B4182763 : Blo 159796 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B515335 : Blo 159796 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B417919 : Blo 159796 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B614699 : Blo 159796 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B549935 : Blo 159796 549935 := bstep (se 1 (by rfl) ⟨412451, by rfl⟩ : syracuseStep 549935 = 824903) B824903
theorem B910885 : Blo 159796 910885 := bstep (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) B170791
theorem B550529 : Blo 159796 550529 := bstep (se 2 (by rfl) ⟨206448, by rfl⟩ : syracuseStep 550529 = 412897) B412897
theorem B2125217 : Blo 159796 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B1765583 : Blo 159796 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B160027 : Blo 159796 160027 := bstep (se 1 (by rfl) ⟨120020, by rfl⟩ : syracuseStep 160027 = 240041) B240041
theorem B160063 : Blo 159796 160063 := bstep (se 1 (by rfl) ⟨120047, by rfl⟩ : syracuseStep 160063 = 240095) B240095
theorem B160543 : Blo 159796 160543 := bstep (se 1 (by rfl) ⟨120407, by rfl⟩ : syracuseStep 160543 = 240815) B240815
theorem B161051 : Blo 159796 161051 := bstep (se 1 (by rfl) ⟨120788, by rfl⟩ : syracuseStep 161051 = 241577) B241577
theorem B4388489 : Blo 159796 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B39221111 : Blo 159796 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B162111 : Blo 159796 162111 := bstep (se 1 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 162111 = 243167) B243167
theorem B293663 : Blo 159796 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B163327 : Blo 159796 163327 := bstep (se 1 (by rfl) ⟨122495, by rfl⟩ : syracuseStep 163327 = 244991) B244991
theorem B163579 : Blo 159796 163579 := bstep (se 1 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 163579 = 245369) B245369
theorem B163687 : Blo 159796 163687 := bstep (se 1 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 163687 = 245531) B245531
theorem B557225 : Blo 159796 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B1377263 : Blo 159796 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B217908265 : Blo 159796 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B821015 : Blo 159796 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B1214513 : Blo 159796 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B165979 : Blo 159796 165979 := bstep (se 1 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 165979 = 248969) B248969
theorem B821663 : Blo 159796 821663 := bstep (se 1 (by rfl) ⟨616247, by rfl⟩ : syracuseStep 821663 = 1232495) B1232495
theorem B8785043 : Blo 159796 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B1543657 : Blo 159796 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B462847 : Blo 159796 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B922367 : Blo 159796 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B366623 : Blo 159796 366623 := bstep (se 1 (by rfl) ⟨274967, by rfl⟩ : syracuseStep 366623 = 549935) B549935
theorem B5577017 : Blo 159796 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B367019 : Blo 159796 367019 := bstep (se 1 (by rfl) ⟨275264, by rfl⟩ : syracuseStep 367019 = 550529) B550529
theorem B367145 : Blo 159796 367145 := bstep (se 2 (by rfl) ⟨137679, by rfl⟩ : syracuseStep 367145 = 275359) B275359
theorem B269851 : Blo 159796 269851 := bstep (se 1 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 269851 = 404777) B404777
theorem B1416811 : Blo 159796 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B269993 : Blo 159796 269993 := bstep (se 2 (by rfl) ⟨101247, by rfl⟩ : syracuseStep 269993 = 202495) B202495
theorem B17571815 : Blo 159796 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B270479 : Blo 159796 270479 := bstep (se 1 (by rfl) ⟨202859, by rfl⟩ : syracuseStep 270479 = 405719) B405719
theorem B1680209 : Blo 159796 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B2925659 : Blo 159796 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B206383 : Blo 159796 206383 := bstep (se 1 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 206383 = 309575) B309575
theorem B3024539 : Blo 159796 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B272551 : Blo 159796 272551 := bstep (se 1 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 272551 = 408827) B408827
theorem B2764367 : Blo 159796 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B1159991 : Blo 159796 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B2930975 : Blo 159796 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B244475 : Blo 159796 244475 := bstep (se 1 (by rfl) ⟨183356, by rfl⟩ : syracuseStep 244475 = 366713) B366713
theorem B245375 : Blo 159796 245375 := bstep (se 1 (by rfl) ⟨184031, by rfl⟩ : syracuseStep 245375 = 368063) B368063
theorem B409799 : Blo 159796 409799 := bstep (se 1 (by rfl) ⟨307349, by rfl⟩ : syracuseStep 409799 = 614699) B614699
theorem B1557319 : Blo 159796 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B64603541 : Blo 159796 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B217769 : Blo 159796 217769 := bstep (se 2 (by rfl) ⟨81663, by rfl⟩ : syracuseStep 217769 = 163327) B163327
theorem B1170719 : Blo 159796 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B875879 : Blo 159796 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B876203 : Blo 159796 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B810971 : Blo 159796 810971 := bstep (se 1 (by rfl) ⟨608228, by rfl⟩ : syracuseStep 810971 = 1216457) B1216457
theorem B550043 : Blo 159796 550043 := bstep (se 1 (by rfl) ⟨412532, by rfl⟩ : syracuseStep 550043 = 825065) B825065
theorem B3172297 : Blo 159796 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B290719 : Blo 159796 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B160287 : Blo 159796 160287 := bstep (se 1 (by rfl) ⟨120215, by rfl⟩ : syracuseStep 160287 = 240431) B240431
theorem B160367 : Blo 159796 160367 := bstep (se 1 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 160367 = 240551) B240551
theorem B783101 : Blo 159796 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B1177055 : Blo 159796 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B1668671 : Blo 159796 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B162239 : Blo 159796 162239 := bstep (se 1 (by rfl) ⟨121679, by rfl⟩ : syracuseStep 162239 = 243359) B243359
theorem B26147407 : Blo 159796 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B457721 : Blo 159796 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B687113 : Blo 159796 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B162919 : Blo 159796 162919 := bstep (se 1 (by rfl) ⟨122189, by rfl⟩ : syracuseStep 162919 = 244379) B244379
theorem B359585 : Blo 159796 359585 := bstep (se 2 (by rfl) ⟨134844, by rfl⟩ : syracuseStep 359585 = 269689) B269689
theorem B3571303 : Blo 159796 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B163431 : Blo 159796 163431 := bstep (se 1 (by rfl) ⟨122573, by rfl⟩ : syracuseStep 163431 = 245147) B245147
theorem B918175 : Blo 159796 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B4229729 : Blo 159796 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B363401 : Blo 159796 363401 := bstep (se 2 (by rfl) ⟨136275, by rfl⟩ : syracuseStep 363401 = 272551) B272551
theorem B1120139 : Blo 159796 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B366695 : Blo 159796 366695 := bstep (se 1 (by rfl) ⟨275021, by rfl⟩ : syracuseStep 366695 = 550043) B550043
theorem B1842911 : Blo 159796 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B305147 : Blo 159796 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B239723 : Blo 159796 239723 := bstep (se 1 (by rfl) ⟨179792, by rfl⟩ : syracuseStep 239723 = 359585) B359585
theorem B4761737 : Blo 159796 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1550501 : Blo 159796 1550501 := bstep (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) B290719
theorem B371483 : Blo 159796 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B273199 : Blo 159796 273199 := bstep (se 1 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 273199 = 409799) B409799
theorem B43069027 : Blo 159796 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B2076425 : Blo 159796 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B275177 : Blo 159796 275177 := bstep (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) B206383
theorem B244415 : Blo 159796 244415 := bstep (se 1 (by rfl) ⟨183311, by rfl⟩ : syracuseStep 244415 = 366623) B366623
theorem B244679 : Blo 159796 244679 := bstep (se 1 (by rfl) ⟨183509, by rfl⟩ : syracuseStep 244679 = 367019) B367019
theorem B244763 : Blo 159796 244763 := bstep (se 1 (by rfl) ⟨183572, by rfl⟩ : syracuseStep 244763 = 367145) B367145
theorem B179995 : Blo 159796 179995 := bstep (se 1 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 179995 = 269993) B269993
theorem B540647 : Blo 159796 540647 := bstep (se 1 (by rfl) ⟨405485, by rfl⟩ : syracuseStep 540647 = 810971) B810971
theorem B11714543 : Blo 159796 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B180319 : Blo 159796 180319 := bstep (se 1 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 180319 = 270479) B270479
theorem B1950439 : Blo 159796 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B2016359 : Blo 159796 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B773327 : Blo 159796 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B1953983 : Blo 159796 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B1889081 : Blo 159796 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B547343 : Blo 159796 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B809675 : Blo 159796 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B290544353 : Blo 159796 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B547775 : Blo 159796 547775 := bstep (se 1 (by rfl) ⟨410831, by rfl⟩ : syracuseStep 547775 = 821663) B821663
theorem B580717 : Blo 159796 580717 := bstep (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) B217769
theorem B5856695 : Blo 159796 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B221305 : Blo 159796 221305 := bstep (se 2 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 221305 = 165979) B165979
theorem B614911 : Blo 159796 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B2058209 : Blo 159796 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B780479 : Blo 159796 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B583919 : Blo 159796 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B584135 : Blo 159796 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B617129 : Blo 159796 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B14872045 : Blo 159796 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B522067 : Blo 159796 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B34863209 : Blo 159796 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B784703 : Blo 159796 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1112447 : Blo 159796 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B162983 : Blo 159796 162983 := bstep (se 1 (by rfl) ⟨122237, by rfl⟩ : syracuseStep 162983 = 244475) B244475
theorem B458075 : Blo 159796 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B359801 : Blo 159796 359801 := bstep (se 2 (by rfl) ⟨134925, by rfl⟩ : syracuseStep 359801 = 269851) B269851
theorem B163583 : Blo 159796 163583 := bstep (se 1 (by rfl) ⟨122687, by rfl⟩ : syracuseStep 163583 = 245375) B245375
theorem B295073 : Blo 159796 295073 := bstep (se 2 (by rfl) ⟨110652, by rfl⟩ : syracuseStep 295073 = 221305) B221305
theorem B819881 : Blo 159796 819881 := bstep (se 2 (by rfl) ⟨307455, by rfl⟩ : syracuseStep 819881 = 614911) B614911
theorem B1344239 : Blo 159796 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B2819819 : Blo 159796 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B364265 : Blo 159796 364265 := bstep (se 2 (by rfl) ⟨136599, by rfl⟩ : syracuseStep 364265 = 273199) B273199
theorem B364895 : Blo 159796 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B193696235 : Blo 159796 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B365183 : Blo 159796 365183 := bstep (se 1 (by rfl) ⟨273887, by rfl⟩ : syracuseStep 365183 = 547775) B547775
theorem B19829393 : Blo 159796 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B3904463 : Blo 159796 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B696089 : Blo 159796 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B1384283 : Blo 159796 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B23242139 : Blo 159796 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B305383 : Blo 159796 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B239867 : Blo 159796 239867 := bstep (se 1 (by rfl) ⟨179900, by rfl⟩ : syracuseStep 239867 = 359801) B359801
theorem B239993 : Blo 159796 239993 := bstep (se 2 (by rfl) ⟨89997, by rfl⟩ : syracuseStep 239993 = 179995) B179995
theorem B7809695 : Blo 159796 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B240425 : Blo 159796 240425 := bstep (se 2 (by rfl) ⟨90159, by rfl⟩ : syracuseStep 240425 = 180319) B180319
theorem B1224233 : Blo 159796 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B2600585 : Blo 159796 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B242267 : Blo 159796 242267 := bstep (se 1 (by rfl) ⟨181700, by rfl⟩ : syracuseStep 242267 = 363401) B363401
theorem B733805 : Blo 159796 733805 := bstep (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) B275177
theorem B1259387 : Blo 159796 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B244463 : Blo 159796 244463 := bstep (se 1 (by rfl) ⟨183347, by rfl⟩ : syracuseStep 244463 = 366695) B366695
theorem B539783 : Blo 159796 539783 := bstep (se 1 (by rfl) ⟨404837, by rfl⟩ : syracuseStep 539783 = 809675) B809675
theorem B57425369 : Blo 159796 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B1228607 : Blo 159796 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B1033667 : Blo 159796 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B411419 : Blo 159796 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B247655 : Blo 159796 247655 := bstep (se 1 (by rfl) ⟨185741, by rfl⟩ : syracuseStep 247655 = 371483) B371483
theorem B183451 : Blo 159796 183451 := bstep (se 1 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 183451 = 275177) B275177
theorem B774289 : Blo 159796 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B741631 : Blo 159796 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B1302655 : Blo 159796 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B746759 : Blo 159796 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B813725 : Blo 159796 813725 := bstep (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) B305147
theorem B1372139 : Blo 159796 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B159815 : Blo 159796 159815 := bstep (se 1 (by rfl) ⟨119861, by rfl⟩ : syracuseStep 159815 = 239723) B239723
theorem B3174491 : Blo 159796 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B520319 : Blo 159796 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B389279 : Blo 159796 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B389423 : Blo 159796 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B2062205 : Blo 159796 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B523135 : Blo 159796 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B162943 : Blo 159796 162943 := bstep (se 1 (by rfl) ⟨122207, by rfl⟩ : syracuseStep 162943 = 244415) B244415
theorem B163119 : Blo 159796 163119 := bstep (se 1 (by rfl) ⟨122339, by rfl⟩ : syracuseStep 163119 = 244679) B244679
theorem B163175 : Blo 159796 163175 := bstep (se 1 (by rfl) ⟨122381, by rfl⟩ : syracuseStep 163175 = 244763) B244763
theorem B360431 : Blo 159796 360431 := bstep (se 1 (by rfl) ⟨270323, by rfl⟩ : syracuseStep 360431 = 540647) B540647
theorem B196715 : Blo 159796 196715 := bstep (se 1 (by rfl) ⟨147536, by rfl⟩ : syracuseStep 196715 = 295073) B295073
theorem B1736873 : Blo 159796 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B689111 : Blo 159796 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B660413 : Blo 159796 660413 := bstep (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) B247655
theorem B464059 : Blo 159796 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B922855 : Blo 159796 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B988841 : Blo 159796 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B497839 : Blo 159796 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B697513 : Blo 159796 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B153134317 : Blo 159796 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B240287 : Blo 159796 240287 := bstep (se 1 (by rfl) ⟨180215, by rfl⟩ : syracuseStep 240287 = 360431) B360431
theorem B8465309 : Blo 159796 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B896159 : Blo 159796 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B274279 : Blo 159796 274279 := bstep (se 1 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 274279 = 411419) B411419
theorem B242843 : Blo 159796 242843 := bstep (se 1 (by rfl) ⟨182132, by rfl⟩ : syracuseStep 242843 = 364265) B364265
theorem B243263 : Blo 159796 243263 := bstep (se 1 (by rfl) ⟨182447, by rfl⟩ : syracuseStep 243263 = 364895) B364895
theorem B407177 : Blo 159796 407177 := bstep (se 2 (by rfl) ⟨152691, by rfl⟩ : syracuseStep 407177 = 305383) B305383
theorem B243455 : Blo 159796 243455 := bstep (se 1 (by rfl) ⟨182591, by rfl⟩ : syracuseStep 243455 = 365183) B365183
theorem B13219595 : Blo 159796 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B2602975 : Blo 159796 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B244601 : Blo 159796 244601 := bstep (se 2 (by rfl) ⟨91725, by rfl⟩ : syracuseStep 244601 = 183451) B183451
theorem B7519517 : Blo 159796 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B1032385 : Blo 159796 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B542483 : Blo 159796 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B346879 : Blo 159796 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B839591 : Blo 159796 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B546587 : Blo 159796 546587 := bstep (se 1 (by rfl) ⟨409940, by rfl⟩ : syracuseStep 546587 = 819881) B819881
theorem B129130823 : Blo 159796 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B15494759 : Blo 159796 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B159911 : Blo 159796 159911 := bstep (se 1 (by rfl) ⟨119933, by rfl⟩ : syracuseStep 159911 = 239867) B239867
theorem B159995 : Blo 159796 159995 := bstep (se 1 (by rfl) ⟨119996, by rfl⟩ : syracuseStep 159995 = 239993) B239993
theorem B5206463 : Blo 159796 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B160283 : Blo 159796 160283 := bstep (se 1 (by rfl) ⟨120212, by rfl⟩ : syracuseStep 160283 = 240425) B240425
theorem B816155 : Blo 159796 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B1733723 : Blo 159796 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B914759 : Blo 159796 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B259519 : Blo 159796 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B259615 : Blo 159796 259615 := bstep (se 1 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 259615 = 389423) B389423
theorem B161511 : Blo 159796 161511 := bstep (se 1 (by rfl) ⟨121133, by rfl⟩ : syracuseStep 161511 = 242267) B242267
theorem B489203 : Blo 159796 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B1374803 : Blo 159796 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B162975 : Blo 159796 162975 := bstep (se 1 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 162975 = 244463) B244463
theorem B359855 : Blo 159796 359855 := bstep (se 1 (by rfl) ⟨269891, by rfl⟩ : syracuseStep 359855 = 539783) B539783
theorem B819071 : Blo 159796 819071 := bstep (se 1 (by rfl) ⟨614303, by rfl⟩ : syracuseStep 819071 = 1228607) B1228607
theorem B1376513 : Blo 159796 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B524573 : Blo 159796 524573 := bstep (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) B196715
theorem B459407 : Blo 159796 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B361655 : Blo 159796 361655 := bstep (se 1 (by rfl) ⟨271241, by rfl⟩ : syracuseStep 361655 = 542483) B542483
theorem B559727 : Blo 159796 559727 := bstep (se 1 (by rfl) ⟨419795, by rfl⟩ : syracuseStep 559727 = 839591) B839591
theorem B462505 : Blo 159796 462505 := bstep (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) B346879
theorem B659227 : Blo 159796 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B364391 : Blo 159796 364391 := bstep (se 1 (by rfl) ⟨273293, by rfl⟩ : syracuseStep 364391 = 546587) B546587
theorem B365705 : Blo 159796 365705 := bstep (se 2 (by rfl) ⟨137139, by rfl⟩ : syracuseStep 365705 = 274279) B274279
theorem B86087215 : Blo 159796 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B816716357 : Blo 159796 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B5643539 : Blo 159796 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B597439 : Blo 159796 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B10329839 : Blo 159796 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B1384613 : Blo 159796 1384613 := bstep (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) B259615
theorem B663785 : Blo 159796 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B1155815 : Blo 159796 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B271451 : Blo 159796 271451 := bstep (se 1 (by rfl) ⟨203588, by rfl⟩ : syracuseStep 271451 = 407177) B407177
theorem B239903 : Blo 159796 239903 := bstep (se 1 (by rfl) ⟨179927, by rfl⟩ : syracuseStep 239903 = 359855) B359855
theorem B1157915 : Blo 159796 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B930017 : Blo 159796 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B440275 : Blo 159796 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B1230473 : Blo 159796 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B346025 : Blo 159796 346025 := bstep (se 2 (by rfl) ⟨129759, by rfl⟩ : syracuseStep 346025 = 259519) B259519
theorem B544103 : Blo 159796 544103 := bstep (se 1 (by rfl) ⟨408077, by rfl⟩ : syracuseStep 544103 = 816155) B816155
theorem B609839 : Blo 159796 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B546047 : Blo 159796 546047 := bstep (se 1 (by rfl) ⟨409535, by rfl⟩ : syracuseStep 546047 = 819071) B819071
theorem B618745 : Blo 159796 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B160191 : Blo 159796 160191 := bstep (se 1 (by rfl) ⟨120143, by rfl⟩ : syracuseStep 160191 = 240287) B240287
theorem B3470633 : Blo 159796 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B3470975 : Blo 159796 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B161895 : Blo 159796 161895 := bstep (se 1 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 161895 = 242843) B242843
theorem B162175 : Blo 159796 162175 := bstep (se 1 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 162175 = 243263) B243263
theorem B326135 : Blo 159796 326135 := bstep (se 1 (by rfl) ⟨244601, by rfl⟩ : syracuseStep 326135 = 489203) B489203
theorem B162303 : Blo 159796 162303 := bstep (se 1 (by rfl) ⟨121727, by rfl⟩ : syracuseStep 162303 = 243455) B243455
theorem B8813063 : Blo 159796 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B916535 : Blo 159796 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B163067 : Blo 159796 163067 := bstep (se 1 (by rfl) ⟨122300, by rfl⟩ : syracuseStep 163067 = 244601) B244601
theorem B5013011 : Blo 159796 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B917675 : Blo 159796 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B820315 : Blo 159796 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B230683 : Blo 159796 230683 := bstep (se 1 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 230683 = 346025) B346025
theorem B362735 : Blo 159796 362735 := bstep (se 1 (by rfl) ⟨272051, by rfl⟩ : syracuseStep 362735 = 544103) B544103
theorem B364031 : Blo 159796 364031 := bstep (se 1 (by rfl) ⟨273023, by rfl⟩ : syracuseStep 364031 = 546047) B546047
theorem B544477571 : Blo 159796 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B6886559 : Blo 159796 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B923075 : Blo 159796 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B824993 : Blo 159796 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B23501501 : Blo 159796 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B3186341 : Blo 159796 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B306271 : Blo 159796 306271 := bstep (se 1 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 306271 = 459407) B459407
theorem B241103 : Blo 159796 241103 := bstep (se 1 (by rfl) ⟨180827, by rfl⟩ : syracuseStep 241103 = 361655) B361655
theorem B373151 : Blo 159796 373151 := bstep (se 1 (by rfl) ⟨279863, by rfl⟩ : syracuseStep 373151 = 559727) B559727
theorem B406559 : Blo 159796 406559 := bstep (se 1 (by rfl) ⟨304919, by rfl⟩ : syracuseStep 406559 = 609839) B609839
theorem B242927 : Blo 159796 242927 := bstep (se 1 (by rfl) ⟨182195, by rfl⟩ : syracuseStep 242927 = 364391) B364391
theorem B243803 : Blo 159796 243803 := bstep (se 1 (by rfl) ⟨182852, by rfl⟩ : syracuseStep 243803 = 365705) B365705
theorem B442523 : Blo 159796 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B770543 : Blo 159796 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B180967 : Blo 159796 180967 := bstep (se 1 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 180967 = 271451) B271451
theorem B771943 : Blo 159796 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B2313755 : Blo 159796 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B2313983 : Blo 159796 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B217423 : Blo 159796 217423 := bstep (se 1 (by rfl) ⟨163067, by rfl⟩ : syracuseStep 217423 = 326135) B326135
theorem B611023 : Blo 159796 611023 := bstep (se 1 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 611023 = 916535) B916535
theorem B349715 : Blo 159796 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B3762359 : Blo 159796 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B616673 : Blo 159796 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B878969 : Blo 159796 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B159935 : Blo 159796 159935 := bstep (se 1 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 159935 = 239903) B239903
theorem B114782953 : Blo 159796 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B587033 : Blo 159796 587033 := bstep (se 2 (by rfl) ⟨220137, by rfl⟩ : syracuseStep 587033 = 440275) B440275
theorem B620011 : Blo 159796 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B3342007 : Blo 159796 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B295015 : Blo 159796 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B1542503 : Blo 159796 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B1542655 : Blo 159796 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B15667667 : Blo 159796 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B826681 : Blo 159796 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B271039 : Blo 159796 271039 := bstep (se 1 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 271039 = 406559) B406559
theorem B241289 : Blo 159796 241289 := bstep (se 2 (by rfl) ⟨90483, by rfl⟩ : syracuseStep 241289 = 180967) B180967
theorem B1093753 : Blo 159796 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B241823 : Blo 159796 241823 := bstep (se 1 (by rfl) ⟨181367, by rfl⟩ : syracuseStep 241823 = 362735) B362735
theorem B307577 : Blo 159796 307577 := bstep (se 2 (by rfl) ⟨115341, by rfl⟩ : syracuseStep 307577 = 230683) B230683
theorem B1159589 : Blo 159796 1159589 := bstep (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) B217423
theorem B242687 : Blo 159796 242687 := bstep (se 1 (by rfl) ⟨182015, by rfl⟩ : syracuseStep 242687 = 364031) B364031
theorem B1029257 : Blo 159796 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B362985047 : Blo 159796 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B18364157 : Blo 159796 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B932573 : Blo 159796 932573 := bstep (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) B349715
theorem B408361 : Blo 159796 408361 := bstep (se 2 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 408361 = 306271) B306271
theorem B153043937 : Blo 159796 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B2343917 : Blo 159796 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B2508239 : Blo 159796 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B411115 : Blo 159796 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B248767 : Blo 159796 248767 := bstep (se 1 (by rfl) ⟨186575, by rfl⟩ : syracuseStep 248767 = 373151) B373151
theorem B611783 : Blo 159796 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B513695 : Blo 159796 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B615383 : Blo 159796 615383 := bstep (se 1 (by rfl) ⟨461537, by rfl⟩ : syracuseStep 615383 = 923075) B923075
theorem B549995 : Blo 159796 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B2124227 : Blo 159796 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B814697 : Blo 159796 814697 := bstep (se 2 (by rfl) ⟨305511, by rfl⟩ : syracuseStep 814697 = 611023) B611023
theorem B160735 : Blo 159796 160735 := bstep (se 1 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 160735 = 241103) B241103
theorem B161951 : Blo 159796 161951 := bstep (se 1 (by rfl) ⟨121463, by rfl⟩ : syracuseStep 161951 = 242927) B242927
theorem B391355 : Blo 159796 391355 := bstep (se 1 (by rfl) ⟨293516, by rfl⟩ : syracuseStep 391355 = 587033) B587033
theorem B162535 : Blo 159796 162535 := bstep (se 1 (by rfl) ⟨121901, by rfl⟩ : syracuseStep 162535 = 243803) B243803
theorem B4456009 : Blo 159796 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B393353 : Blo 159796 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B361385 : Blo 159796 361385 := bstep (se 2 (by rfl) ⟨135519, by rfl⟩ : syracuseStep 361385 = 271039) B271039
theorem B1672159 : Blo 159796 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B820205 : Blo 159796 820205 := bstep (se 3 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 820205 = 307577) B307577
theorem B5866613 : Blo 159796 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B1416151 : Blo 159796 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B5941345 : Blo 159796 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B1028335 : Blo 159796 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B407855 : Blo 159796 407855 := bstep (se 1 (by rfl) ⟨305891, by rfl⟩ : syracuseStep 407855 = 611783) B611783
theorem B342463 : Blo 159796 342463 := bstep (se 1 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 342463 = 513695) B513695
theorem B1458337 : Blo 159796 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B410255 : Blo 159796 410255 := bstep (se 1 (by rfl) ⟨307691, by rfl⟩ : syracuseStep 410255 = 615383) B615383
theorem B543131 : Blo 159796 543131 := bstep (se 1 (by rfl) ⟨407348, by rfl⟩ : syracuseStep 543131 = 814697) B814697
theorem B773059 : Blo 159796 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B544481 : Blo 159796 544481 := bstep (se 2 (by rfl) ⟨204180, by rfl⟩ : syracuseStep 544481 = 408361) B408361
theorem B12242771 : Blo 159796 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B1102241 : Blo 159796 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B102029291 : Blo 159796 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B1562611 : Blo 159796 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B548153 : Blo 159796 548153 := bstep (se 2 (by rfl) ⟨205557, by rfl⟩ : syracuseStep 548153 = 411115) B411115
theorem B10445111 : Blo 159796 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B2056873 : Blo 159796 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B160859 : Blo 159796 160859 := bstep (se 1 (by rfl) ⟨120644, by rfl⟩ : syracuseStep 160859 = 241289) B241289
theorem B161215 : Blo 159796 161215 := bstep (se 1 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 161215 = 241823) B241823
theorem B161791 : Blo 159796 161791 := bstep (se 1 (by rfl) ⟨121343, by rfl⟩ : syracuseStep 161791 = 242687) B242687
theorem B686171 : Blo 159796 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B241990031 : Blo 159796 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B5307029 : Blo 159796 5307029 := bstep (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) B248767
theorem B260903 : Blo 159796 260903 := bstep (se 1 (by rfl) ⟨195677, by rfl⟩ : syracuseStep 260903 = 391355) B391355
theorem B621715 : Blo 159796 621715 := bstep (se 1 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 621715 = 932573) B932573
theorem B262235 : Blo 159796 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B2229545 : Blo 159796 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B362087 : Blo 159796 362087 := bstep (se 1 (by rfl) ⟨271565, by rfl⟩ : syracuseStep 362087 = 543131) B543131
theorem B362987 : Blo 159796 362987 := bstep (se 1 (by rfl) ⟨272240, by rfl⟩ : syracuseStep 362987 = 544481) B544481
theorem B8161847 : Blo 159796 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B365435 : Blo 159796 365435 := bstep (se 1 (by rfl) ⟨274076, by rfl⟩ : syracuseStep 365435 = 548153) B548153
theorem B828953 : Blo 159796 828953 := bstep (se 2 (by rfl) ⟨310857, by rfl⟩ : syracuseStep 828953 = 621715) B621715
theorem B271903 : Blo 159796 271903 := bstep (se 1 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 271903 = 407855) B407855
theorem B161326687 : Blo 159796 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B173935 : Blo 159796 173935 := bstep (se 1 (by rfl) ⟨130451, by rfl⟩ : syracuseStep 173935 = 260903) B260903
theorem B1944449 : Blo 159796 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B273503 : Blo 159796 273503 := bstep (se 1 (by rfl) ⟨205127, by rfl⟩ : syracuseStep 273503 = 410255) B410255
theorem B240923 : Blo 159796 240923 := bstep (se 1 (by rfl) ⟨180692, by rfl⟩ : syracuseStep 240923 = 361385) B361385
theorem B3911075 : Blo 159796 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B734827 : Blo 159796 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B1030745 : Blo 159796 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B6963407 : Blo 159796 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B2083481 : Blo 159796 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1888201 : Blo 159796 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B546803 : Blo 159796 546803 := bstep (se 1 (by rfl) ⟨410102, by rfl⟩ : syracuseStep 546803 = 820205) B820205
theorem B2742497 : Blo 159796 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B7921793 : Blo 159796 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B68019527 : Blo 159796 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B1829789 : Blo 159796 1829789 := bstep (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) B686171
theorem B1371113 : Blo 159796 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B456617 : Blo 159796 456617 := bstep (se 2 (by rfl) ⟨171231, by rfl⟩ : syracuseStep 456617 = 342463) B342463
theorem B3538019 : Blo 159796 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B5441231 : Blo 159796 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B362537 : Blo 159796 362537 := bstep (se 2 (by rfl) ⟨135951, by rfl⟩ : syracuseStep 362537 = 271903) B271903
theorem B231913 : Blo 159796 231913 := bstep (se 2 (by rfl) ⟨86967, by rfl⟩ : syracuseStep 231913 = 173935) B173935
theorem B364535 : Blo 159796 364535 := bstep (se 1 (by rfl) ⟨273401, by rfl⟩ : syracuseStep 364535 = 546803) B546803
theorem B5281195 : Blo 159796 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B1219859 : Blo 159796 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B304411 : Blo 159796 304411 := bstep (se 1 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 304411 = 456617) B456617
theorem B699293 : Blo 159796 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B1486363 : Blo 159796 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B241391 : Blo 159796 241391 := bstep (se 1 (by rfl) ⟨181043, by rfl⟩ : syracuseStep 241391 = 362087) B362087
theorem B241991 : Blo 159796 241991 := bstep (se 1 (by rfl) ⟨181493, by rfl⟩ : syracuseStep 241991 = 362987) B362987
theorem B1388987 : Blo 159796 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B215102249 : Blo 159796 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B243623 : Blo 159796 243623 := bstep (se 1 (by rfl) ⟨182717, by rfl⟩ : syracuseStep 243623 = 365435) B365435
theorem B1296299 : Blo 159796 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B182335 : Blo 159796 182335 := bstep (se 1 (by rfl) ⟨136751, by rfl⟩ : syracuseStep 182335 = 273503) B273503
theorem B2607383 : Blo 159796 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B4642271 : Blo 159796 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B1828331 : Blo 159796 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B2517601 : Blo 159796 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B45346351 : Blo 159796 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B552635 : Blo 159796 552635 := bstep (se 1 (by rfl) ⟨414476, by rfl⟩ : syracuseStep 552635 = 828953) B828953
theorem B914075 : Blo 159796 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B979769 : Blo 159796 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B160615 : Blo 159796 160615 := bstep (se 1 (by rfl) ⟨120461, by rfl⟩ : syracuseStep 160615 = 240923) B240923
theorem B687163 : Blo 159796 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B2358679 : Blo 159796 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B1738255 : Blo 159796 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B60461801 : Blo 159796 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1218887 : Blo 159796 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B368423 : Blo 159796 368423 := bstep (se 1 (by rfl) ⟨276317, by rfl⟩ : syracuseStep 368423 = 552635) B552635
theorem B925991 : Blo 159796 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B143401499 : Blo 159796 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B864199 : Blo 159796 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B241691 : Blo 159796 241691 := bstep (se 1 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 241691 = 362537) B362537
theorem B405881 : Blo 159796 405881 := bstep (se 2 (by rfl) ⟨152205, by rfl⟩ : syracuseStep 405881 = 304411) B304411
theorem B243023 : Blo 159796 243023 := bstep (se 1 (by rfl) ⟨182267, by rfl⟩ : syracuseStep 243023 = 364535) B364535
theorem B243113 : Blo 159796 243113 := bstep (se 2 (by rfl) ⟨91167, by rfl⟩ : syracuseStep 243113 = 182335) B182335
theorem B3356801 : Blo 159796 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B3094847 : Blo 159796 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1981817 : Blo 159796 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B609383 : Blo 159796 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B3627487 : Blo 159796 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B1236869 : Blo 159796 1236869 := bstep (se 4 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 1236869 = 231913) B231913
theorem B813239 : Blo 159796 813239 := bstep (se 1 (by rfl) ⟨609929, by rfl⟩ : syracuseStep 813239 = 1219859) B1219859
theorem B7041593 : Blo 159796 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B1864781 : Blo 159796 1864781 := bstep (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) B699293
theorem B160927 : Blo 159796 160927 := bstep (se 1 (by rfl) ⟨120695, by rfl⟩ : syracuseStep 160927 = 241391) B241391
theorem B161327 : Blo 159796 161327 := bstep (se 1 (by rfl) ⟨120995, by rfl⟩ : syracuseStep 161327 = 241991) B241991
theorem B653179 : Blo 159796 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B162415 : Blo 159796 162415 := bstep (se 1 (by rfl) ⟨121811, by rfl⟩ : syracuseStep 162415 = 243623) B243623
theorem B916217 : Blo 159796 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B3144905 : Blo 159796 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B40307867 : Blo 159796 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B824579 : Blo 159796 824579 := bstep (se 1 (by rfl) ⟨618434, by rfl⟩ : syracuseStep 824579 = 1236869) B1236869
theorem B1152265 : Blo 159796 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B270587 : Blo 159796 270587 := bstep (se 1 (by rfl) ⟨202940, by rfl⟩ : syracuseStep 270587 = 405881) B405881
theorem B4694395 : Blo 159796 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B2237867 : Blo 159796 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B1321211 : Blo 159796 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B406255 : Blo 159796 406255 := bstep (se 1 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 406255 = 609383) B609383
theorem B19346597 : Blo 159796 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B245615 : Blo 159796 245615 := bstep (se 1 (by rfl) ⟨184211, by rfl⟩ : syracuseStep 245615 = 368423) B368423
theorem B95600999 : Blo 159796 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B542159 : Blo 159796 542159 := bstep (se 1 (by rfl) ⟨406619, by rfl⟩ : syracuseStep 542159 = 813239) B813239
theorem B870905 : Blo 159796 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B610811 : Blo 159796 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B2317673 : Blo 159796 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B812591 : Blo 159796 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B617327 : Blo 159796 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B161127 : Blo 159796 161127 := bstep (se 1 (by rfl) ⟨120845, by rfl⟩ : syracuseStep 161127 = 241691) B241691
theorem B1243187 : Blo 159796 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B162015 : Blo 159796 162015 := bstep (se 1 (by rfl) ⟨121511, by rfl⟩ : syracuseStep 162015 = 243023) B243023
theorem B162075 : Blo 159796 162075 := bstep (se 1 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 162075 = 243113) B243113
theorem B2063231 : Blo 159796 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B2096603 : Blo 159796 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B63733999 : Blo 159796 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B6259193 : Blo 159796 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B361439 : Blo 159796 361439 := bstep (se 1 (by rfl) ⟨271079, by rfl⟩ : syracuseStep 361439 = 542159) B542159
theorem B26871911 : Blo 159796 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B828791 : Blo 159796 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B407207 : Blo 159796 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B180391 : Blo 159796 180391 := bstep (se 1 (by rfl) ⟨135293, by rfl⟩ : syracuseStep 180391 = 270587) B270587
theorem B1491911 : Blo 159796 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B541673 : Blo 159796 541673 := bstep (se 2 (by rfl) ⟨203127, by rfl⟩ : syracuseStep 541673 = 406255) B406255
theorem B541727 : Blo 159796 541727 := bstep (se 1 (by rfl) ⟨406295, by rfl⟩ : syracuseStep 541727 = 812591) B812591
theorem B411551 : Blo 159796 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B12897731 : Blo 159796 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B6180461 : Blo 159796 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B1397735 : Blo 159796 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B580603 : Blo 159796 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B549719 : Blo 159796 549719 := bstep (se 1 (by rfl) ⟨412289, by rfl⟩ : syracuseStep 549719 = 824579) B824579
theorem B880807 : Blo 159796 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B1536353 : Blo 159796 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B1375487 : Blo 159796 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B163743 : Blo 159796 163743 := bstep (se 1 (by rfl) ⟨122807, by rfl⟩ : syracuseStep 163743 = 245615) B245615
theorem B361115 : Blo 159796 361115 := bstep (se 1 (by rfl) ⟨270836, by rfl⟩ : syracuseStep 361115 = 541673) B541673
theorem B361151 : Blo 159796 361151 := bstep (se 1 (by rfl) ⟨270863, by rfl⟩ : syracuseStep 361151 = 541727) B541727
theorem B366479 : Blo 159796 366479 := bstep (se 1 (by rfl) ⟨274859, by rfl⟩ : syracuseStep 366479 = 549719) B549719
theorem B1024235 : Blo 159796 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B271471 : Blo 159796 271471 := bstep (se 1 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 271471 = 407207) B407207
theorem B240521 : Blo 159796 240521 := bstep (se 2 (by rfl) ⟨90195, by rfl⟩ : syracuseStep 240521 = 180391) B180391
theorem B84978665 : Blo 159796 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B4172795 : Blo 159796 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B994607 : Blo 159796 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B240959 : Blo 159796 240959 := bstep (se 1 (by rfl) ⟨180719, by rfl⟩ : syracuseStep 240959 = 361439) B361439
theorem B274367 : Blo 159796 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B8598487 : Blo 159796 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B931823 : Blo 159796 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B774137 : Blo 159796 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B17914607 : Blo 159796 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B4120307 : Blo 159796 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B1174409 : Blo 159796 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B552527 : Blo 159796 552527 := bstep (se 1 (by rfl) ⟨414395, by rfl⟩ : syracuseStep 552527 = 828791) B828791
theorem B916991 : Blo 159796 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B361961 : Blo 159796 361961 := bstep (se 2 (by rfl) ⟨135735, by rfl⟩ : syracuseStep 361961 = 271471) B271471
theorem B663071 : Blo 159796 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B368351 : Blo 159796 368351 := bstep (se 1 (by rfl) ⟨276263, by rfl⟩ : syracuseStep 368351 = 552527) B552527
theorem B240743 : Blo 159796 240743 := bstep (se 1 (by rfl) ⟨180557, by rfl⟩ : syracuseStep 240743 = 361115) B361115
theorem B240767 : Blo 159796 240767 := bstep (se 1 (by rfl) ⟨180575, by rfl⟩ : syracuseStep 240767 = 361151) B361151
theorem B244319 : Blo 159796 244319 := bstep (se 1 (by rfl) ⟨183239, by rfl⟩ : syracuseStep 244319 = 366479) B366479
theorem B11943071 : Blo 159796 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B182911 : Blo 159796 182911 := bstep (se 1 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 182911 = 274367) B274367
theorem B611327 : Blo 159796 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B516091 : Blo 159796 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B2746871 : Blo 159796 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B682823 : Blo 159796 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B11464649 : Blo 159796 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B160347 : Blo 159796 160347 := bstep (se 1 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 160347 = 240521) B240521
theorem B782939 : Blo 159796 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B56652443 : Blo 159796 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B2781863 : Blo 159796 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B160639 : Blo 159796 160639 := bstep (se 1 (by rfl) ⟨120479, by rfl⟩ : syracuseStep 160639 = 240959) B240959
theorem B621215 : Blo 159796 621215 := bstep (se 1 (by rfl) ⟨465911, by rfl⟩ : syracuseStep 621215 = 931823) B931823
theorem B7643099 : Blo 159796 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B241307 : Blo 159796 241307 := bstep (se 1 (by rfl) ⟨180980, by rfl⟩ : syracuseStep 241307 = 361961) B361961
theorem B407551 : Blo 159796 407551 := bstep (se 1 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 407551 = 611327) B611327
theorem B243881 : Blo 159796 243881 := bstep (se 2 (by rfl) ⟨91455, by rfl⟩ : syracuseStep 243881 = 182911) B182911
theorem B245567 : Blo 159796 245567 := bstep (se 1 (by rfl) ⟨184175, by rfl⟩ : syracuseStep 245567 = 368351) B368351
theorem B37768295 : Blo 159796 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B1854575 : Blo 159796 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B414143 : Blo 159796 414143 := bstep (se 1 (by rfl) ⟨310607, by rfl⟩ : syracuseStep 414143 = 621215) B621215
theorem B1831247 : Blo 159796 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B455215 : Blo 159796 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B160495 : Blo 159796 160495 := bstep (se 1 (by rfl) ⟨120371, by rfl⟩ : syracuseStep 160495 = 240743) B240743
theorem B160511 : Blo 159796 160511 := bstep (se 1 (by rfl) ⟨120383, by rfl⟩ : syracuseStep 160511 = 240767) B240767
theorem B521959 : Blo 159796 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B1768189 : Blo 159796 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B162879 : Blo 159796 162879 := bstep (se 1 (by rfl) ⟨122159, by rfl⟩ : syracuseStep 162879 = 244319) B244319
theorem B7962047 : Blo 159796 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B688121 : Blo 159796 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B695945 : Blo 159796 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B1220831 : Blo 159796 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B25178863 : Blo 159796 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B276095 : Blo 159796 276095 := bstep (se 1 (by rfl) ⟨207071, by rfl⟩ : syracuseStep 276095 = 414143) B414143
theorem B5095399 : Blo 159796 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B606953 : Blo 159796 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B543401 : Blo 159796 543401 := bstep (se 2 (by rfl) ⟨203775, by rfl⟩ : syracuseStep 543401 = 407551) B407551
theorem B1236383 : Blo 159796 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B160871 : Blo 159796 160871 := bstep (se 1 (by rfl) ⟨120653, by rfl⟩ : syracuseStep 160871 = 241307) B241307
theorem B2357585 : Blo 159796 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B162587 : Blo 159796 162587 := bstep (se 1 (by rfl) ⟨121940, by rfl⟩ : syracuseStep 162587 = 243881) B243881
theorem B5308031 : Blo 159796 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B163711 : Blo 159796 163711 := bstep (se 1 (by rfl) ⟨122783, by rfl⟩ : syracuseStep 163711 = 245567) B245567
theorem B458747 : Blo 159796 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B362267 : Blo 159796 362267 := bstep (se 1 (by rfl) ⟨271700, by rfl⟩ : syracuseStep 362267 = 543401) B543401
theorem B824255 : Blo 159796 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B463963 : Blo 159796 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B6793865 : Blo 159796 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B305831 : Blo 159796 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B404635 : Blo 159796 404635 := bstep (se 1 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 404635 = 606953) B606953
theorem B33571817 : Blo 159796 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B184063 : Blo 159796 184063 := bstep (se 1 (by rfl) ⟨138047, by rfl⟩ : syracuseStep 184063 = 276095) B276095
theorem B813887 : Blo 159796 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B1571723 : Blo 159796 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B3538687 : Blo 159796 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B22381211 : Blo 159796 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B4529243 : Blo 159796 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B203887 : Blo 159796 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B241511 : Blo 159796 241511 := bstep (se 1 (by rfl) ⟨181133, by rfl⟩ : syracuseStep 241511 = 362267) B362267
theorem B539513 : Blo 159796 539513 := bstep (se 2 (by rfl) ⟨202317, by rfl⟩ : syracuseStep 539513 = 404635) B404635
theorem B245417 : Blo 159796 245417 := bstep (se 2 (by rfl) ⟨92031, by rfl⟩ : syracuseStep 245417 = 184063) B184063
theorem B542591 : Blo 159796 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B549503 : Blo 159796 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B618617 : Blo 159796 618617 := bstep (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) B463963
theorem B1047815 : Blo 159796 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B4718249 : Blo 159796 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B361727 : Blo 159796 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B366335 : Blo 159796 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B271849 : Blo 159796 271849 := bstep (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) B203887
theorem B698543 : Blo 159796 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B14920807 : Blo 159796 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B412411 : Blo 159796 412411 := bstep (se 1 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 412411 = 618617) B618617
theorem B12077981 : Blo 159796 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B161007 : Blo 159796 161007 := bstep (se 1 (by rfl) ⟨120755, by rfl⟩ : syracuseStep 161007 = 241511) B241511
theorem B359675 : Blo 159796 359675 := bstep (se 1 (by rfl) ⟨269756, by rfl⟩ : syracuseStep 359675 = 539513) B539513
theorem B3145499 : Blo 159796 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B163611 : Blo 159796 163611 := bstep (se 1 (by rfl) ⟨122708, by rfl⟩ : syracuseStep 163611 = 245417) B245417
theorem B362465 : Blo 159796 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B19894409 : Blo 159796 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B465695 : Blo 159796 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B239783 : Blo 159796 239783 := bstep (se 1 (by rfl) ⟨179837, by rfl⟩ : syracuseStep 239783 = 359675) B359675
theorem B241151 : Blo 159796 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B244223 : Blo 159796 244223 := bstep (se 1 (by rfl) ⟨183167, by rfl⟩ : syracuseStep 244223 = 366335) B366335
theorem B8051987 : Blo 159796 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B549881 : Blo 159796 549881 := bstep (se 2 (by rfl) ⟨206205, by rfl⟩ : syracuseStep 549881 = 412411) B412411
theorem B2096999 : Blo 159796 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B366587 : Blo 159796 366587 := bstep (se 1 (by rfl) ⟨274940, by rfl⟩ : syracuseStep 366587 = 549881) B549881
theorem B241643 : Blo 159796 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B310463 : Blo 159796 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B1397999 : Blo 159796 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B13262939 : Blo 159796 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B5367991 : Blo 159796 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B159855 : Blo 159796 159855 := bstep (se 1 (by rfl) ⟨119891, by rfl⟩ : syracuseStep 159855 = 239783) B239783
theorem B160767 : Blo 159796 160767 := bstep (se 1 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 160767 = 241151) B241151
theorem B162815 : Blo 159796 162815 := bstep (se 1 (by rfl) ⟨122111, by rfl⟩ : syracuseStep 162815 = 244223) B244223
theorem B206975 : Blo 159796 206975 := bstep (se 1 (by rfl) ⟨155231, by rfl⟩ : syracuseStep 206975 = 310463) B310463
theorem B7157321 : Blo 159796 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B931999 : Blo 159796 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B244391 : Blo 159796 244391 := bstep (se 1 (by rfl) ⟨183293, by rfl⟩ : syracuseStep 244391 = 366587) B366587
theorem B8841959 : Blo 159796 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B161095 : Blo 159796 161095 := bstep (se 1 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 161095 = 241643) B241643
theorem B4771547 : Blo 159796 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B551933 : Blo 159796 551933 := bstep (se 3 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 551933 = 206975) B206975
theorem B5894639 : Blo 159796 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B1242665 : Blo 159796 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B162927 : Blo 159796 162927 := bstep (se 1 (by rfl) ⟨122195, by rfl⟩ : syracuseStep 162927 = 244391) B244391
theorem B3181031 : Blo 159796 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B367955 : Blo 159796 367955 := bstep (se 1 (by rfl) ⟨275966, by rfl⟩ : syracuseStep 367955 = 551933) B551933
theorem B828443 : Blo 159796 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B3929759 : Blo 159796 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B245303 : Blo 159796 245303 := bstep (se 1 (by rfl) ⟨183977, by rfl⟩ : syracuseStep 245303 = 367955) B367955
theorem B2120687 : Blo 159796 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B552295 : Blo 159796 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B2619839 : Blo 159796 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B1413791 : Blo 159796 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B1746559 : Blo 159796 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B736393 : Blo 159796 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B163535 : Blo 159796 163535 := bstep (se 1 (by rfl) ⟨122651, by rfl⟩ : syracuseStep 163535 = 245303) B245303
theorem B2328745 : Blo 159796 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B942527 : Blo 159796 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B981857 : Blo 159796 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B2513405 : Blo 159796 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B3104993 : Blo 159796 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B654571 : Blo 159796 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B1675603 : Blo 159796 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B2069995 : Blo 159796 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B3491045 : Blo 159796 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B2327363 : Blo 159796 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B2234137 : Blo 159796 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B2759993 : Blo 159796 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B1839995 : Blo 159796 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B1551575 : Blo 159796 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B2978849 : Blo 159796 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B1226663 : Blo 159796 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B1034383 : Blo 159796 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B1985899 : Blo 159796 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B1379177 : Blo 159796 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B2647865 : Blo 159796 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B817775 : Blo 159796 817775 := bstep (se 1 (by rfl) ⟨613331, by rfl⟩ : syracuseStep 817775 = 1226663) B1226663
theorem B919451 : Blo 159796 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B545183 : Blo 159796 545183 := bstep (se 1 (by rfl) ⟨408887, by rfl⟩ : syracuseStep 545183 = 817775) B817775
theorem B1765243 : Blo 159796 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B363455 : Blo 159796 363455 := bstep (se 1 (by rfl) ⟨272591, by rfl⟩ : syracuseStep 363455 = 545183) B545183
theorem B612967 : Blo 159796 612967 := bstep (se 1 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 612967 = 919451) B919451
theorem B2353657 : Blo 159796 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B242303 : Blo 159796 242303 := bstep (se 1 (by rfl) ⟨181727, by rfl⟩ : syracuseStep 242303 = 363455) B363455
theorem B3138209 : Blo 159796 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B817289 : Blo 159796 817289 := bstep (se 2 (by rfl) ⟨306483, by rfl⟩ : syracuseStep 817289 = 612967) B612967
theorem B544859 : Blo 159796 544859 := bstep (se 1 (by rfl) ⟨408644, by rfl⟩ : syracuseStep 544859 = 817289) B817289
theorem B2092139 : Blo 159796 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B161535 : Blo 159796 161535 := bstep (se 1 (by rfl) ⟨121151, by rfl⟩ : syracuseStep 161535 = 242303) B242303
theorem B363239 : Blo 159796 363239 := bstep (se 1 (by rfl) ⟨272429, by rfl⟩ : syracuseStep 363239 = 544859) B544859
theorem B1394759 : Blo 159796 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B929839 : Blo 159796 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B242159 : Blo 159796 242159 := bstep (se 1 (by rfl) ⟨181619, by rfl⟩ : syracuseStep 242159 = 363239) B363239
theorem B1239785 : Blo 159796 1239785 := bstep (se 2 (by rfl) ⟨464919, by rfl⟩ : syracuseStep 1239785 = 929839) B929839
theorem B161439 : Blo 159796 161439 := bstep (se 1 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 161439 = 242159) B242159
theorem B826523 : Blo 159796 826523 := bstep (se 1 (by rfl) ⟨619892, by rfl⟩ : syracuseStep 826523 = 1239785) B1239785
theorem B551015 : Blo 159796 551015 := bstep (se 1 (by rfl) ⟨413261, by rfl⟩ : syracuseStep 551015 = 826523) B826523
theorem B367343 : Blo 159796 367343 := bstep (se 1 (by rfl) ⟨275507, by rfl⟩ : syracuseStep 367343 = 551015) B551015
theorem B244895 : Blo 159796 244895 := bstep (se 1 (by rfl) ⟨183671, by rfl⟩ : syracuseStep 244895 = 367343) B367343
theorem B163263 : Blo 159796 163263 := bstep (se 1 (by rfl) ⟨122447, by rfl⟩ : syracuseStep 163263 = 244895) B244895

theorem C0 (j : ℕ) (h1 : 39949 ≤ j) (h2 : j ≤ 40648) : Blo 159796 (4 * j + 3) := by
  interval_cases j
  · exact B159799
  · exact B159803
  · exact B159807
  · exact B159811
  · exact B159815
  · exact B159819
  · exact B159823
  · exact B159827
  · exact B159831
  · exact B159835
  · exact B159839
  · exact B159843
  · exact B159847
  · exact B159851
  · exact B159855
  · exact B159859
  · exact B159863
  · exact B159867
  · exact B159871
  · exact B159875
  · exact B159879
  · exact B159883
  · exact B159887
  · exact B159891
  · exact B159895
  · exact B159899
  · exact B159903
  · exact B159907
  · exact B159911
  · exact B159915
  · exact B159919
  · exact B159923
  · exact B159927
  · exact B159931
  · exact B159935
  · exact B159939
  · exact B159943
  · exact B159947
  · exact B159951
  · exact B159955
  · exact B159959
  · exact B159963
  · exact B159967
  · exact B159971
  · exact B159975
  · exact B159979
  · exact B159983
  · exact B159987
  · exact B159991
  · exact B159995
  · exact B159999
  · exact B160003
  · exact B160007
  · exact B160011
  · exact B160015
  · exact B160019
  · exact B160023
  · exact B160027
  · exact B160031
  · exact B160035
  · exact B160039
  · exact B160043
  · exact B160047
  · exact B160051
  · exact B160055
  · exact B160059
  · exact B160063
  · exact B160067
  · exact B160071
  · exact B160075
  · exact B160079
  · exact B160083
  · exact B160087
  · exact B160091
  · exact B160095
  · exact B160099
  · exact B160103
  · exact B160107
  · exact B160111
  · exact B160115
  · exact B160119
  · exact B160123
  · exact B160127
  · exact B160131
  · exact B160135
  · exact B160139
  · exact B160143
  · exact B160147
  · exact B160151
  · exact B160155
  · exact B160159
  · exact B160163
  · exact B160167
  · exact B160171
  · exact B160175
  · exact B160179
  · exact B160183
  · exact B160187
  · exact B160191
  · exact B160195
  · exact B160199
  · exact B160203
  · exact B160207
  · exact B160211
  · exact B160215
  · exact B160219
  · exact B160223
  · exact B160227
  · exact B160231
  · exact B160235
  · exact B160239
  · exact B160243
  · exact B160247
  · exact B160251
  · exact B160255
  · exact B160259
  · exact B160263
  · exact B160267
  · exact B160271
  · exact B160275
  · exact B160279
  · exact B160283
  · exact B160287
  · exact B160291
  · exact B160295
  · exact B160299
  · exact B160303
  · exact B160307
  · exact B160311
  · exact B160315
  · exact B160319
  · exact B160323
  · exact B160327
  · exact B160331
  · exact B160335
  · exact B160339
  · exact B160343
  · exact B160347
  · exact B160351
  · exact B160355
  · exact B160359
  · exact B160363
  · exact B160367
  · exact B160371
  · exact B160375
  · exact B160379
  · exact B160383
  · exact B160387
  · exact B160391
  · exact B160395
  · exact B160399
  · exact B160403
  · exact B160407
  · exact B160411
  · exact B160415
  · exact B160419
  · exact B160423
  · exact B160427
  · exact B160431
  · exact B160435
  · exact B160439
  · exact B160443
  · exact B160447
  · exact B160451
  · exact B160455
  · exact B160459
  · exact B160463
  · exact B160467
  · exact B160471
  · exact B160475
  · exact B160479
  · exact B160483
  · exact B160487
  · exact B160491
  · exact B160495
  · exact B160499
  · exact B160503
  · exact B160507
  · exact B160511
  · exact B160515
  · exact B160519
  · exact B160523
  · exact B160527
  · exact B160531
  · exact B160535
  · exact B160539
  · exact B160543
  · exact B160547
  · exact B160551
  · exact B160555
  · exact B160559
  · exact B160563
  · exact B160567
  · exact B160571
  · exact B160575
  · exact B160579
  · exact B160583
  · exact B160587
  · exact B160591
  · exact B160595
  · exact B160599
  · exact B160603
  · exact B160607
  · exact B160611
  · exact B160615
  · exact B160619
  · exact B160623
  · exact B160627
  · exact B160631
  · exact B160635
  · exact B160639
  · exact B160643
  · exact B160647
  · exact B160651
  · exact B160655
  · exact B160659
  · exact B160663
  · exact B160667
  · exact B160671
  · exact B160675
  · exact B160679
  · exact B160683
  · exact B160687
  · exact B160691
  · exact B160695
  · exact B160699
  · exact B160703
  · exact B160707
  · exact B160711
  · exact B160715
  · exact B160719
  · exact B160723
  · exact B160727
  · exact B160731
  · exact B160735
  · exact B160739
  · exact B160743
  · exact B160747
  · exact B160751
  · exact B160755
  · exact B160759
  · exact B160763
  · exact B160767
  · exact B160771
  · exact B160775
  · exact B160779
  · exact B160783
  · exact B160787
  · exact B160791
  · exact B160795
  · exact B160799
  · exact B160803
  · exact B160807
  · exact B160811
  · exact B160815
  · exact B160819
  · exact B160823
  · exact B160827
  · exact B160831
  · exact B160835
  · exact B160839
  · exact B160843
  · exact B160847
  · exact B160851
  · exact B160855
  · exact B160859
  · exact B160863
  · exact B160867
  · exact B160871
  · exact B160875
  · exact B160879
  · exact B160883
  · exact B160887
  · exact B160891
  · exact B160895
  · exact B160899
  · exact B160903
  · exact B160907
  · exact B160911
  · exact B160915
  · exact B160919
  · exact B160923
  · exact B160927
  · exact B160931
  · exact B160935
  · exact B160939
  · exact B160943
  · exact B160947
  · exact B160951
  · exact B160955
  · exact B160959
  · exact B160963
  · exact B160967
  · exact B160971
  · exact B160975
  · exact B160979
  · exact B160983
  · exact B160987
  · exact B160991
  · exact B160995
  · exact B160999
  · exact B161003
  · exact B161007
  · exact B161011
  · exact B161015
  · exact B161019
  · exact B161023
  · exact B161027
  · exact B161031
  · exact B161035
  · exact B161039
  · exact B161043
  · exact B161047
  · exact B161051
  · exact B161055
  · exact B161059
  · exact B161063
  · exact B161067
  · exact B161071
  · exact B161075
  · exact B161079
  · exact B161083
  · exact B161087
  · exact B161091
  · exact B161095
  · exact B161099
  · exact B161103
  · exact B161107
  · exact B161111
  · exact B161115
  · exact B161119
  · exact B161123
  · exact B161127
  · exact B161131
  · exact B161135
  · exact B161139
  · exact B161143
  · exact B161147
  · exact B161151
  · exact B161155
  · exact B161159
  · exact B161163
  · exact B161167
  · exact B161171
  · exact B161175
  · exact B161179
  · exact B161183
  · exact B161187
  · exact B161191
  · exact B161195
  · exact B161199
  · exact B161203
  · exact B161207
  · exact B161211
  · exact B161215
  · exact B161219
  · exact B161223
  · exact B161227
  · exact B161231
  · exact B161235
  · exact B161239
  · exact B161243
  · exact B161247
  · exact B161251
  · exact B161255
  · exact B161259
  · exact B161263
  · exact B161267
  · exact B161271
  · exact B161275
  · exact B161279
  · exact B161283
  · exact B161287
  · exact B161291
  · exact B161295
  · exact B161299
  · exact B161303
  · exact B161307
  · exact B161311
  · exact B161315
  · exact B161319
  · exact B161323
  · exact B161327
  · exact B161331
  · exact B161335
  · exact B161339
  · exact B161343
  · exact B161347
  · exact B161351
  · exact B161355
  · exact B161359
  · exact B161363
  · exact B161367
  · exact B161371
  · exact B161375
  · exact B161379
  · exact B161383
  · exact B161387
  · exact B161391
  · exact B161395
  · exact B161399
  · exact B161403
  · exact B161407
  · exact B161411
  · exact B161415
  · exact B161419
  · exact B161423
  · exact B161427
  · exact B161431
  · exact B161435
  · exact B161439
  · exact B161443
  · exact B161447
  · exact B161451
  · exact B161455
  · exact B161459
  · exact B161463
  · exact B161467
  · exact B161471
  · exact B161475
  · exact B161479
  · exact B161483
  · exact B161487
  · exact B161491
  · exact B161495
  · exact B161499
  · exact B161503
  · exact B161507
  · exact B161511
  · exact B161515
  · exact B161519
  · exact B161523
  · exact B161527
  · exact B161531
  · exact B161535
  · exact B161539
  · exact B161543
  · exact B161547
  · exact B161551
  · exact B161555
  · exact B161559
  · exact B161563
  · exact B161567
  · exact B161571
  · exact B161575
  · exact B161579
  · exact B161583
  · exact B161587
  · exact B161591
  · exact B161595
  · exact B161599
  · exact B161603
  · exact B161607
  · exact B161611
  · exact B161615
  · exact B161619
  · exact B161623
  · exact B161627
  · exact B161631
  · exact B161635
  · exact B161639
  · exact B161643
  · exact B161647
  · exact B161651
  · exact B161655
  · exact B161659
  · exact B161663
  · exact B161667
  · exact B161671
  · exact B161675
  · exact B161679
  · exact B161683
  · exact B161687
  · exact B161691
  · exact B161695
  · exact B161699
  · exact B161703
  · exact B161707
  · exact B161711
  · exact B161715
  · exact B161719
  · exact B161723
  · exact B161727
  · exact B161731
  · exact B161735
  · exact B161739
  · exact B161743
  · exact B161747
  · exact B161751
  · exact B161755
  · exact B161759
  · exact B161763
  · exact B161767
  · exact B161771
  · exact B161775
  · exact B161779
  · exact B161783
  · exact B161787
  · exact B161791
  · exact B161795
  · exact B161799
  · exact B161803
  · exact B161807
  · exact B161811
  · exact B161815
  · exact B161819
  · exact B161823
  · exact B161827
  · exact B161831
  · exact B161835
  · exact B161839
  · exact B161843
  · exact B161847
  · exact B161851
  · exact B161855
  · exact B161859
  · exact B161863
  · exact B161867
  · exact B161871
  · exact B161875
  · exact B161879
  · exact B161883
  · exact B161887
  · exact B161891
  · exact B161895
  · exact B161899
  · exact B161903
  · exact B161907
  · exact B161911
  · exact B161915
  · exact B161919
  · exact B161923
  · exact B161927
  · exact B161931
  · exact B161935
  · exact B161939
  · exact B161943
  · exact B161947
  · exact B161951
  · exact B161955
  · exact B161959
  · exact B161963
  · exact B161967
  · exact B161971
  · exact B161975
  · exact B161979
  · exact B161983
  · exact B161987
  · exact B161991
  · exact B161995
  · exact B161999
  · exact B162003
  · exact B162007
  · exact B162011
  · exact B162015
  · exact B162019
  · exact B162023
  · exact B162027
  · exact B162031
  · exact B162035
  · exact B162039
  · exact B162043
  · exact B162047
  · exact B162051
  · exact B162055
  · exact B162059
  · exact B162063
  · exact B162067
  · exact B162071
  · exact B162075
  · exact B162079
  · exact B162083
  · exact B162087
  · exact B162091
  · exact B162095
  · exact B162099
  · exact B162103
  · exact B162107
  · exact B162111
  · exact B162115
  · exact B162119
  · exact B162123
  · exact B162127
  · exact B162131
  · exact B162135
  · exact B162139
  · exact B162143
  · exact B162147
  · exact B162151
  · exact B162155
  · exact B162159
  · exact B162163
  · exact B162167
  · exact B162171
  · exact B162175
  · exact B162179
  · exact B162183
  · exact B162187
  · exact B162191
  · exact B162195
  · exact B162199
  · exact B162203
  · exact B162207
  · exact B162211
  · exact B162215
  · exact B162219
  · exact B162223
  · exact B162227
  · exact B162231
  · exact B162235
  · exact B162239
  · exact B162243
  · exact B162247
  · exact B162251
  · exact B162255
  · exact B162259
  · exact B162263
  · exact B162267
  · exact B162271
  · exact B162275
  · exact B162279
  · exact B162283
  · exact B162287
  · exact B162291
  · exact B162295
  · exact B162299
  · exact B162303
  · exact B162307
  · exact B162311
  · exact B162315
  · exact B162319
  · exact B162323
  · exact B162327
  · exact B162331
  · exact B162335
  · exact B162339
  · exact B162343
  · exact B162347
  · exact B162351
  · exact B162355
  · exact B162359
  · exact B162363
  · exact B162367
  · exact B162371
  · exact B162375
  · exact B162379
  · exact B162383
  · exact B162387
  · exact B162391
  · exact B162395
  · exact B162399
  · exact B162403
  · exact B162407
  · exact B162411
  · exact B162415
  · exact B162419
  · exact B162423
  · exact B162427
  · exact B162431
  · exact B162435
  · exact B162439
  · exact B162443
  · exact B162447
  · exact B162451
  · exact B162455
  · exact B162459
  · exact B162463
  · exact B162467
  · exact B162471
  · exact B162475
  · exact B162479
  · exact B162483
  · exact B162487
  · exact B162491
  · exact B162495
  · exact B162499
  · exact B162503
  · exact B162507
  · exact B162511
  · exact B162515
  · exact B162519
  · exact B162523
  · exact B162527
  · exact B162531
  · exact B162535
  · exact B162539
  · exact B162543
  · exact B162547
  · exact B162551
  · exact B162555
  · exact B162559
  · exact B162563
  · exact B162567
  · exact B162571
  · exact B162575
  · exact B162579
  · exact B162583
  · exact B162587
  · exact B162591
  · exact B162595

theorem C1 (j : ℕ) (h1 : 40649 ≤ j) (h2 : j ≤ 40948) : Blo 159796 (4 * j + 3) := by
  interval_cases j
  · exact B162599
  · exact B162603
  · exact B162607
  · exact B162611
  · exact B162615
  · exact B162619
  · exact B162623
  · exact B162627
  · exact B162631
  · exact B162635
  · exact B162639
  · exact B162643
  · exact B162647
  · exact B162651
  · exact B162655
  · exact B162659
  · exact B162663
  · exact B162667
  · exact B162671
  · exact B162675
  · exact B162679
  · exact B162683
  · exact B162687
  · exact B162691
  · exact B162695
  · exact B162699
  · exact B162703
  · exact B162707
  · exact B162711
  · exact B162715
  · exact B162719
  · exact B162723
  · exact B162727
  · exact B162731
  · exact B162735
  · exact B162739
  · exact B162743
  · exact B162747
  · exact B162751
  · exact B162755
  · exact B162759
  · exact B162763
  · exact B162767
  · exact B162771
  · exact B162775
  · exact B162779
  · exact B162783
  · exact B162787
  · exact B162791
  · exact B162795
  · exact B162799
  · exact B162803
  · exact B162807
  · exact B162811
  · exact B162815
  · exact B162819
  · exact B162823
  · exact B162827
  · exact B162831
  · exact B162835
  · exact B162839
  · exact B162843
  · exact B162847
  · exact B162851
  · exact B162855
  · exact B162859
  · exact B162863
  · exact B162867
  · exact B162871
  · exact B162875
  · exact B162879
  · exact B162883
  · exact B162887
  · exact B162891
  · exact B162895
  · exact B162899
  · exact B162903
  · exact B162907
  · exact B162911
  · exact B162915
  · exact B162919
  · exact B162923
  · exact B162927
  · exact B162931
  · exact B162935
  · exact B162939
  · exact B162943
  · exact B162947
  · exact B162951
  · exact B162955
  · exact B162959
  · exact B162963
  · exact B162967
  · exact B162971
  · exact B162975
  · exact B162979
  · exact B162983
  · exact B162987
  · exact B162991
  · exact B162995
  · exact B162999
  · exact B163003
  · exact B163007
  · exact B163011
  · exact B163015
  · exact B163019
  · exact B163023
  · exact B163027
  · exact B163031
  · exact B163035
  · exact B163039
  · exact B163043
  · exact B163047
  · exact B163051
  · exact B163055
  · exact B163059
  · exact B163063
  · exact B163067
  · exact B163071
  · exact B163075
  · exact B163079
  · exact B163083
  · exact B163087
  · exact B163091
  · exact B163095
  · exact B163099
  · exact B163103
  · exact B163107
  · exact B163111
  · exact B163115
  · exact B163119
  · exact B163123
  · exact B163127
  · exact B163131
  · exact B163135
  · exact B163139
  · exact B163143
  · exact B163147
  · exact B163151
  · exact B163155
  · exact B163159
  · exact B163163
  · exact B163167
  · exact B163171
  · exact B163175
  · exact B163179
  · exact B163183
  · exact B163187
  · exact B163191
  · exact B163195
  · exact B163199
  · exact B163203
  · exact B163207
  · exact B163211
  · exact B163215
  · exact B163219
  · exact B163223
  · exact B163227
  · exact B163231
  · exact B163235
  · exact B163239
  · exact B163243
  · exact B163247
  · exact B163251
  · exact B163255
  · exact B163259
  · exact B163263
  · exact B163267
  · exact B163271
  · exact B163275
  · exact B163279
  · exact B163283
  · exact B163287
  · exact B163291
  · exact B163295
  · exact B163299
  · exact B163303
  · exact B163307
  · exact B163311
  · exact B163315
  · exact B163319
  · exact B163323
  · exact B163327
  · exact B163331
  · exact B163335
  · exact B163339
  · exact B163343
  · exact B163347
  · exact B163351
  · exact B163355
  · exact B163359
  · exact B163363
  · exact B163367
  · exact B163371
  · exact B163375
  · exact B163379
  · exact B163383
  · exact B163387
  · exact B163391
  · exact B163395
  · exact B163399
  · exact B163403
  · exact B163407
  · exact B163411
  · exact B163415
  · exact B163419
  · exact B163423
  · exact B163427
  · exact B163431
  · exact B163435
  · exact B163439
  · exact B163443
  · exact B163447
  · exact B163451
  · exact B163455
  · exact B163459
  · exact B163463
  · exact B163467
  · exact B163471
  · exact B163475
  · exact B163479
  · exact B163483
  · exact B163487
  · exact B163491
  · exact B163495
  · exact B163499
  · exact B163503
  · exact B163507
  · exact B163511
  · exact B163515
  · exact B163519
  · exact B163523
  · exact B163527
  · exact B163531
  · exact B163535
  · exact B163539
  · exact B163543
  · exact B163547
  · exact B163551
  · exact B163555
  · exact B163559
  · exact B163563
  · exact B163567
  · exact B163571
  · exact B163575
  · exact B163579
  · exact B163583
  · exact B163587
  · exact B163591
  · exact B163595
  · exact B163599
  · exact B163603
  · exact B163607
  · exact B163611
  · exact B163615
  · exact B163619
  · exact B163623
  · exact B163627
  · exact B163631
  · exact B163635
  · exact B163639
  · exact B163643
  · exact B163647
  · exact B163651
  · exact B163655
  · exact B163659
  · exact B163663
  · exact B163667
  · exact B163671
  · exact B163675
  · exact B163679
  · exact B163683
  · exact B163687
  · exact B163691
  · exact B163695
  · exact B163699
  · exact B163703
  · exact B163707
  · exact B163711
  · exact B163715
  · exact B163719
  · exact B163723
  · exact B163727
  · exact B163731
  · exact B163735
  · exact B163739
  · exact B163743
  · exact B163747
  · exact B163751
  · exact B163755
  · exact B163759
  · exact B163763
  · exact B163767
  · exact B163771
  · exact B163775
  · exact B163779
  · exact B163783
  · exact B163787
  · exact B163791
  · exact B163795

theorem solution (m : ℕ) (hlo : 159796 ≤ m) (hhi : m ≤ 163796) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 39949 ≤ j := by omega
    have hj2 : j ≤ 40948 := by omega
    have hb : Blo 159796 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 40649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
