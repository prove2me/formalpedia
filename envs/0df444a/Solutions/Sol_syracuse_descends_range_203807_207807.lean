-- Prove2me | solution 1 for syracuse_descends_range_203807_207807
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:53.510917+00:00
-- url     : https://prove2.me/submissions/d77404e4-761d-47d3-b9cf-1f3ffc7575c5

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


theorem B458765 : Blo 203807 458765 := bbase (se 3 (by rfl) ⟨86018, by rfl⟩ : syracuseStep 458765 = 172037) (by norm_num)
theorem B229405 : Blo 203807 229405 := bbase (se 3 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 229405 = 86027) (by norm_num)
theorem B786469 : Blo 203807 786469 := bbase (se 4 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 786469 = 147463) (by norm_num)
theorem B294949 : Blo 203807 294949 := bbase (se 4 (by rfl) ⟨27651, by rfl⟩ : syracuseStep 294949 = 55303) (by norm_num)
theorem B524333 : Blo 203807 524333 := bbase (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) (by norm_num)
theorem B1769525 : Blo 203807 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B229441 : Blo 203807 229441 := bbase (se 2 (by rfl) ⟨86040, by rfl⟩ : syracuseStep 229441 = 172081) (by norm_num)
theorem B262217 : Blo 203807 262217 := bbase (se 2 (by rfl) ⟨98331, by rfl⟩ : syracuseStep 262217 = 196663) (by norm_num)
theorem B458837 : Blo 203807 458837 := bbase (se 8 (by rfl) ⟨2688, by rfl⟩ : syracuseStep 458837 = 5377) (by norm_num)
theorem B688229 : Blo 203807 688229 := bbase (se 4 (by rfl) ⟨64521, by rfl⟩ : syracuseStep 688229 = 129043) (by norm_num)
theorem B229477 : Blo 203807 229477 := bbase (se 4 (by rfl) ⟨21513, by rfl⟩ : syracuseStep 229477 = 43027) (by norm_num)
theorem B262273 : Blo 203807 262273 := bbase (se 2 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 262273 = 196705) (by norm_num)
theorem B393349 : Blo 203807 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B229513 : Blo 203807 229513 := bbase (se 2 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 229513 = 172135) (by norm_num)
theorem B458909 : Blo 203807 458909 := bbase (se 3 (by rfl) ⟨86045, by rfl⟩ : syracuseStep 458909 = 172091) (by norm_num)
theorem B327845 : Blo 203807 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B229549 : Blo 203807 229549 := bbase (se 3 (by rfl) ⟨43040, by rfl⟩ : syracuseStep 229549 = 86081) (by norm_num)
theorem B229585 : Blo 203807 229585 := bbase (se 2 (by rfl) ⟨86094, by rfl⟩ : syracuseStep 229585 = 172189) (by norm_num)
theorem B262369 : Blo 203807 262369 := bbase (se 2 (by rfl) ⟨98388, by rfl⟩ : syracuseStep 262369 = 196777) (by norm_num)
theorem B458981 : Blo 203807 458981 := bbase (se 4 (by rfl) ⟨43029, by rfl⟩ : syracuseStep 458981 = 86059) (by norm_num)
theorem B229621 : Blo 203807 229621 := bbase (se 5 (by rfl) ⟨10763, by rfl⟩ : syracuseStep 229621 = 21527) (by norm_num)
theorem B393493 : Blo 203807 393493 := bbase (se 6 (by rfl) ⟨9222, by rfl⟩ : syracuseStep 393493 = 18445) (by norm_num)
theorem B229657 : Blo 203807 229657 := bbase (se 2 (by rfl) ⟨86121, by rfl⟩ : syracuseStep 229657 = 172243) (by norm_num)
theorem B459053 : Blo 203807 459053 := bbase (se 3 (by rfl) ⟨86072, by rfl⟩ : syracuseStep 459053 = 172145) (by norm_num)
theorem B262445 : Blo 203807 262445 := bbase (se 3 (by rfl) ⟨49208, by rfl⟩ : syracuseStep 262445 = 98417) (by norm_num)
theorem B229693 : Blo 203807 229693 := bbase (se 3 (by rfl) ⟨43067, by rfl⟩ : syracuseStep 229693 = 86135) (by norm_num)
theorem B491845 : Blo 203807 491845 := bbase (se 4 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 491845 = 92221) (by norm_num)
theorem B786773 : Blo 203807 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B229729 : Blo 203807 229729 := bbase (se 2 (by rfl) ⟨86148, by rfl⟩ : syracuseStep 229729 = 172297) (by norm_num)
theorem B328045 : Blo 203807 328045 := bbase (se 3 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 328045 = 123017) (by norm_num)
theorem B459125 : Blo 203807 459125 := bbase (se 5 (by rfl) ⟨21521, by rfl⟩ : syracuseStep 459125 = 43043) (by norm_num)
theorem B1048949 : Blo 203807 1048949 := bbase (se 5 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 1048949 = 98339) (by norm_num)
theorem B229765 : Blo 203807 229765 := bbase (se 4 (by rfl) ⟨21540, by rfl⟩ : syracuseStep 229765 = 43081) (by norm_num)
theorem B524677 : Blo 203807 524677 := bbase (se 4 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 524677 = 98377) (by norm_num)
theorem B262541 : Blo 203807 262541 := bbase (se 3 (by rfl) ⟨49226, by rfl⟩ : syracuseStep 262541 = 98453) (by norm_num)
theorem B229801 : Blo 203807 229801 := bbase (se 2 (by rfl) ⟨86175, by rfl⟩ : syracuseStep 229801 = 172351) (by norm_num)
theorem B393653 : Blo 203807 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B459197 : Blo 203807 459197 := bbase (se 3 (by rfl) ⟨86099, by rfl⟩ : syracuseStep 459197 = 172199) (by norm_num)
theorem B262597 : Blo 203807 262597 := bbase (se 4 (by rfl) ⟨24618, by rfl⟩ : syracuseStep 262597 = 49237) (by norm_num)
theorem B229837 : Blo 203807 229837 := bbase (se 3 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 229837 = 86189) (by norm_num)
theorem B229873 : Blo 203807 229873 := bbase (se 2 (by rfl) ⟨86202, by rfl⟩ : syracuseStep 229873 = 172405) (by norm_num)
theorem B524789 : Blo 203807 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B459269 : Blo 203807 459269 := bbase (se 4 (by rfl) ⟨43056, by rfl⟩ : syracuseStep 459269 = 86113) (by norm_num)
theorem B688661 : Blo 203807 688661 := bbase (se 6 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 688661 = 32281) (by norm_num)
theorem B229909 : Blo 203807 229909 := bbase (se 6 (by rfl) ⟨5388, by rfl⟩ : syracuseStep 229909 = 10777) (by norm_num)
theorem B262693 : Blo 203807 262693 := bbase (se 4 (by rfl) ⟨24627, by rfl⟩ : syracuseStep 262693 = 49255) (by norm_num)
theorem B229945 : Blo 203807 229945 := bbase (se 2 (by rfl) ⟨86229, by rfl⟩ : syracuseStep 229945 = 172459) (by norm_num)
theorem B393797 : Blo 203807 393797 := bbase (se 4 (by rfl) ⟨36918, by rfl⟩ : syracuseStep 393797 = 73837) (by norm_num)
theorem B459341 : Blo 203807 459341 := bbase (se 3 (by rfl) ⟨86126, by rfl⟩ : syracuseStep 459341 = 172253) (by norm_num)
theorem B229981 : Blo 203807 229981 := bbase (se 3 (by rfl) ⟨43121, by rfl⟩ : syracuseStep 229981 = 86243) (by norm_num)
theorem B328301 : Blo 203807 328301 := bbase (se 3 (by rfl) ⟨61556, by rfl⟩ : syracuseStep 328301 = 123113) (by norm_num)
theorem B230017 : Blo 203807 230017 := bbase (se 2 (by rfl) ⟨86256, by rfl⟩ : syracuseStep 230017 = 172513) (by norm_num)
theorem B459413 : Blo 203807 459413 := bbase (se 6 (by rfl) ⟨10767, by rfl⟩ : syracuseStep 459413 = 21535) (by norm_num)
theorem B230053 : Blo 203807 230053 := bbase (se 4 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 230053 = 43135) (by norm_num)
theorem B524981 : Blo 203807 524981 := bbase (se 5 (by rfl) ⟨24608, by rfl⟩ : syracuseStep 524981 = 49217) (by norm_num)
theorem B230089 : Blo 203807 230089 := bbase (se 2 (by rfl) ⟨86283, by rfl⟩ : syracuseStep 230089 = 172567) (by norm_num)
theorem B262865 : Blo 203807 262865 := bbase (se 2 (by rfl) ⟨98574, by rfl⟩ : syracuseStep 262865 = 197149) (by norm_num)
theorem B3572437 : Blo 203807 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B459485 : Blo 203807 459485 := bbase (se 3 (by rfl) ⟨86153, by rfl⟩ : syracuseStep 459485 = 172307) (by norm_num)
theorem B230125 : Blo 203807 230125 := bbase (se 3 (by rfl) ⟨43148, by rfl⟩ : syracuseStep 230125 = 86297) (by norm_num)
theorem B590581 : Blo 203807 590581 := bbase (se 5 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 590581 = 55367) (by norm_num)
theorem B262921 : Blo 203807 262921 := bbase (se 2 (by rfl) ⟨98595, by rfl⟩ : syracuseStep 262921 = 197191) (by norm_num)
theorem B230161 : Blo 203807 230161 := bbase (se 2 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 230161 = 172621) (by norm_num)
theorem B459557 : Blo 203807 459557 := bbase (se 4 (by rfl) ⟨43083, by rfl⟩ : syracuseStep 459557 = 86167) (by norm_num)
theorem B230197 : Blo 203807 230197 := bbase (se 5 (by rfl) ⟨10790, by rfl⟩ : syracuseStep 230197 = 21581) (by norm_num)
theorem B295741 : Blo 203807 295741 := bbase (se 3 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 295741 = 110903) (by norm_num)
theorem B230233 : Blo 203807 230233 := bbase (se 2 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 230233 = 172675) (by norm_num)
theorem B394085 : Blo 203807 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B459629 : Blo 203807 459629 := bbase (se 3 (by rfl) ⟨86180, by rfl⟩ : syracuseStep 459629 = 172361) (by norm_num)
theorem B230269 : Blo 203807 230269 := bbase (se 3 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 230269 = 86351) (by norm_num)
theorem B230305 : Blo 203807 230305 := bbase (se 2 (by rfl) ⟨86364, by rfl⟩ : syracuseStep 230305 = 172729) (by norm_num)
theorem B459701 : Blo 203807 459701 := bbase (se 5 (by rfl) ⟨21548, by rfl⟩ : syracuseStep 459701 = 43097) (by norm_num)
theorem B689093 : Blo 203807 689093 := bbase (se 4 (by rfl) ⟨64602, by rfl⟩ : syracuseStep 689093 = 129205) (by norm_num)
theorem B230341 : Blo 203807 230341 := bbase (se 4 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 230341 = 43189) (by norm_num)
theorem B230377 : Blo 203807 230377 := bbase (se 2 (by rfl) ⟨86391, by rfl⟩ : syracuseStep 230377 = 172783) (by norm_num)
theorem B426989 : Blo 203807 426989 := bbase (se 3 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 426989 = 160121) (by norm_num)
theorem B459773 : Blo 203807 459773 := bbase (se 3 (by rfl) ⟨86207, by rfl⟩ : syracuseStep 459773 = 172415) (by norm_num)
theorem B394237 : Blo 203807 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B230413 : Blo 203807 230413 := bbase (se 3 (by rfl) ⟨43202, by rfl⟩ : syracuseStep 230413 = 86405) (by norm_num)
theorem B525325 : Blo 203807 525325 := bbase (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) (by norm_num)
theorem B230449 : Blo 203807 230449 := bbase (se 2 (by rfl) ⟨86418, by rfl⟩ : syracuseStep 230449 = 172837) (by norm_num)
theorem B459845 : Blo 203807 459845 := bbase (se 4 (by rfl) ⟨43110, by rfl⟩ : syracuseStep 459845 = 86221) (by norm_num)
theorem B230485 : Blo 203807 230485 := bbase (se 8 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 230485 = 2701) (by norm_num)
theorem B230521 : Blo 203807 230521 := bbase (se 2 (by rfl) ⟨86445, by rfl⟩ : syracuseStep 230521 = 172891) (by norm_num)
theorem B525437 : Blo 203807 525437 := bbase (se 3 (by rfl) ⟨98519, by rfl⟩ : syracuseStep 525437 = 197039) (by norm_num)
theorem B459917 : Blo 203807 459917 := bbase (se 3 (by rfl) ⟨86234, by rfl⟩ : syracuseStep 459917 = 172469) (by norm_num)
theorem B230557 : Blo 203807 230557 := bbase (se 3 (by rfl) ⟨43229, by rfl⟩ : syracuseStep 230557 = 86459) (by norm_num)
theorem B1475765 : Blo 203807 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B885941 : Blo 203807 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B230593 : Blo 203807 230593 := bbase (se 2 (by rfl) ⟨86472, by rfl⟩ : syracuseStep 230593 = 172945) (by norm_num)
theorem B459989 : Blo 203807 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B230629 : Blo 203807 230629 := bbase (se 4 (by rfl) ⟨21621, by rfl⟩ : syracuseStep 230629 = 43243) (by norm_num)
theorem B230665 : Blo 203807 230665 := bbase (se 2 (by rfl) ⟨86499, by rfl⟩ : syracuseStep 230665 = 172999) (by norm_num)
theorem B460061 : Blo 203807 460061 := bbase (se 3 (by rfl) ⟨86261, by rfl⟩ : syracuseStep 460061 = 172523) (by norm_num)
theorem B230701 : Blo 203807 230701 := bbase (se 3 (by rfl) ⟨43256, by rfl⟩ : syracuseStep 230701 = 86513) (by norm_num)
theorem B591157 : Blo 203807 591157 := bbase (se 5 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 591157 = 55421) (by norm_num)
theorem B525629 : Blo 203807 525629 := bbase (se 3 (by rfl) ⟨98555, by rfl⟩ : syracuseStep 525629 = 197111) (by norm_num)
theorem B230737 : Blo 203807 230737 := bbase (se 2 (by rfl) ⟨86526, by rfl⟩ : syracuseStep 230737 = 173053) (by norm_num)
theorem B1901909 : Blo 203807 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B460133 : Blo 203807 460133 := bbase (se 4 (by rfl) ⟨43137, by rfl⟩ : syracuseStep 460133 = 86275) (by norm_num)
theorem B689525 : Blo 203807 689525 := bbase (se 5 (by rfl) ⟨32321, by rfl⟩ : syracuseStep 689525 = 64643) (by norm_num)
theorem B230773 : Blo 203807 230773 := bbase (se 5 (by rfl) ⟨10817, by rfl⟩ : syracuseStep 230773 = 21635) (by norm_num)
theorem B755077 : Blo 203807 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B492941 : Blo 203807 492941 := bbase (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) (by norm_num)
theorem B230809 : Blo 203807 230809 := bbase (se 2 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 230809 = 173107) (by norm_num)
theorem B460205 : Blo 203807 460205 := bbase (se 3 (by rfl) ⟨86288, by rfl⟩ : syracuseStep 460205 = 172577) (by norm_num)
theorem B230845 : Blo 203807 230845 := bbase (se 3 (by rfl) ⟨43283, by rfl⟩ : syracuseStep 230845 = 86567) (by norm_num)
theorem B1181141 : Blo 203807 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B230881 : Blo 203807 230881 := bbase (se 2 (by rfl) ⟨86580, by rfl⟩ : syracuseStep 230881 = 173161) (by norm_num)
theorem B460277 : Blo 203807 460277 := bbase (se 5 (by rfl) ⟨21575, by rfl⟩ : syracuseStep 460277 = 43151) (by norm_num)
theorem B230917 : Blo 203807 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B230953 : Blo 203807 230953 := bbase (se 2 (by rfl) ⟨86607, by rfl⟩ : syracuseStep 230953 = 173215) (by norm_num)
theorem B460349 : Blo 203807 460349 := bbase (se 3 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 460349 = 172631) (by norm_num)
theorem B230989 : Blo 203807 230989 := bbase (se 3 (by rfl) ⟨43310, by rfl⟩ : syracuseStep 230989 = 86621) (by norm_num)
theorem B231025 : Blo 203807 231025 := bbase (se 2 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 231025 = 173269) (by norm_num)
theorem B460421 : Blo 203807 460421 := bbase (se 4 (by rfl) ⟨43164, by rfl⟩ : syracuseStep 460421 = 86329) (by norm_num)
theorem B1050245 : Blo 203807 1050245 := bbase (se 4 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 1050245 = 196921) (by norm_num)
theorem B231061 : Blo 203807 231061 := bbase (se 6 (by rfl) ⟨5415, by rfl⟩ : syracuseStep 231061 = 10831) (by norm_num)
theorem B525973 : Blo 203807 525973 := bbase (se 6 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 525973 = 24655) (by norm_num)
theorem B624293 : Blo 203807 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B493229 : Blo 203807 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B231097 : Blo 203807 231097 := bbase (se 2 (by rfl) ⟨86661, by rfl⟩ : syracuseStep 231097 = 173323) (by norm_num)
theorem B460493 : Blo 203807 460493 := bbase (se 3 (by rfl) ⟨86342, by rfl⟩ : syracuseStep 460493 = 172685) (by norm_num)
theorem B329429 : Blo 203807 329429 := bbase (se 7 (by rfl) ⟨3860, by rfl⟩ : syracuseStep 329429 = 7721) (by norm_num)
theorem B231133 : Blo 203807 231133 := bbase (se 3 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 231133 = 86675) (by norm_num)
theorem B231169 : Blo 203807 231169 := bbase (se 2 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 231169 = 173377) (by norm_num)
theorem B460565 : Blo 203807 460565 := bbase (se 6 (by rfl) ⟨10794, by rfl⟩ : syracuseStep 460565 = 21589) (by norm_num)
theorem B689957 : Blo 203807 689957 := bbase (se 4 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 689957 = 129367) (by norm_num)
theorem B231205 : Blo 203807 231205 := bbase (se 4 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 231205 = 43351) (by norm_num)
theorem B231241 : Blo 203807 231241 := bbase (se 2 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 231241 = 173431) (by norm_num)
theorem B460637 : Blo 203807 460637 := bbase (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) (by norm_num)
theorem B231277 : Blo 203807 231277 := bbase (se 3 (by rfl) ⟨43364, by rfl⟩ : syracuseStep 231277 = 86729) (by norm_num)
theorem B231313 : Blo 203807 231313 := bbase (se 2 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 231313 = 173485) (by norm_num)
theorem B460709 : Blo 203807 460709 := bbase (se 4 (by rfl) ⟨43191, by rfl⟩ : syracuseStep 460709 = 86383) (by norm_num)
theorem B231349 : Blo 203807 231349 := bbase (se 5 (by rfl) ⟨10844, by rfl⟩ : syracuseStep 231349 = 21689) (by norm_num)
theorem B231385 : Blo 203807 231385 := bbase (se 2 (by rfl) ⟨86769, by rfl⟩ : syracuseStep 231385 = 173539) (by norm_num)
theorem B460781 : Blo 203807 460781 := bbase (se 3 (by rfl) ⟨86396, by rfl⟩ : syracuseStep 460781 = 172793) (by norm_num)
theorem B231421 : Blo 203807 231421 := bbase (se 3 (by rfl) ⟨43391, by rfl⟩ : syracuseStep 231421 = 86783) (by norm_num)
theorem B231457 : Blo 203807 231457 := bbase (se 2 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 231457 = 173593) (by norm_num)
theorem B460853 : Blo 203807 460853 := bbase (se 5 (by rfl) ⟨21602, by rfl⟩ : syracuseStep 460853 = 43205) (by norm_num)
theorem B231493 : Blo 203807 231493 := bbase (se 4 (by rfl) ⟨21702, by rfl⟩ : syracuseStep 231493 = 43405) (by norm_num)
theorem B231529 : Blo 203807 231529 := bbase (se 2 (by rfl) ⟨86823, by rfl⟩ : syracuseStep 231529 = 173647) (by norm_num)
theorem B460925 : Blo 203807 460925 := bbase (se 3 (by rfl) ⟨86423, by rfl⟩ : syracuseStep 460925 = 172847) (by norm_num)
theorem B231565 : Blo 203807 231565 := bbase (se 3 (by rfl) ⟨43418, by rfl⟩ : syracuseStep 231565 = 86837) (by norm_num)
theorem B231601 : Blo 203807 231601 := bbase (se 2 (by rfl) ⟨86850, by rfl⟩ : syracuseStep 231601 = 173701) (by norm_num)
theorem B460997 : Blo 203807 460997 := bbase (se 4 (by rfl) ⟨43218, by rfl⟩ : syracuseStep 460997 = 86437) (by norm_num)
theorem B690389 : Blo 203807 690389 := bbase (se 7 (by rfl) ⟨8090, by rfl⟩ : syracuseStep 690389 = 16181) (by norm_num)
theorem B592085 : Blo 203807 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B231637 : Blo 203807 231637 := bbase (se 7 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 231637 = 5429) (by norm_num)
theorem B329941 : Blo 203807 329941 := bbase (se 7 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 329941 = 7733) (by norm_num)
theorem B1575125 : Blo 203807 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B231673 : Blo 203807 231673 := bbase (se 2 (by rfl) ⟨86877, by rfl⟩ : syracuseStep 231673 = 173755) (by norm_num)
theorem B461069 : Blo 203807 461069 := bbase (se 3 (by rfl) ⟨86450, by rfl⟩ : syracuseStep 461069 = 172901) (by norm_num)
theorem B2492693 : Blo 203807 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B231709 : Blo 203807 231709 := bbase (se 3 (by rfl) ⟨43445, by rfl⟩ : syracuseStep 231709 = 86891) (by norm_num)
theorem B231745 : Blo 203807 231745 := bbase (se 2 (by rfl) ⟨86904, by rfl⟩ : syracuseStep 231745 = 173809) (by norm_num)
theorem B461141 : Blo 203807 461141 := bbase (se 10 (by rfl) ⟨675, by rfl⟩ : syracuseStep 461141 = 1351) (by norm_num)
theorem B231781 : Blo 203807 231781 := bbase (se 4 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 231781 = 43459) (by norm_num)
theorem B231817 : Blo 203807 231817 := bbase (se 2 (by rfl) ⟨86931, by rfl⟩ : syracuseStep 231817 = 173863) (by norm_num)
theorem B788885 : Blo 203807 788885 := bbase (se 6 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 788885 = 36979) (by norm_num)
theorem B461213 : Blo 203807 461213 := bbase (se 3 (by rfl) ⟨86477, by rfl⟩ : syracuseStep 461213 = 172955) (by norm_num)
theorem B231853 : Blo 203807 231853 := bbase (se 3 (by rfl) ⟨43472, by rfl⟩ : syracuseStep 231853 = 86945) (by norm_num)
theorem B231889 : Blo 203807 231889 := bbase (se 2 (by rfl) ⟨86958, by rfl⟩ : syracuseStep 231889 = 173917) (by norm_num)
theorem B1051093 : Blo 203807 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B461285 : Blo 203807 461285 := bbase (se 4 (by rfl) ⟨43245, by rfl⟩ : syracuseStep 461285 = 86491) (by norm_num)
theorem B231925 : Blo 203807 231925 := bbase (se 5 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 231925 = 21743) (by norm_num)
theorem B231961 : Blo 203807 231961 := bbase (se 2 (by rfl) ⟨86985, by rfl⟩ : syracuseStep 231961 = 173971) (by norm_num)
theorem B461357 : Blo 203807 461357 := bbase (se 3 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 461357 = 173009) (by norm_num)
theorem B625205 : Blo 203807 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B231997 : Blo 203807 231997 := bbase (se 3 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 231997 = 86999) (by norm_num)
theorem B559685 : Blo 203807 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B232033 : Blo 203807 232033 := bbase (se 2 (by rfl) ⟨87012, by rfl⟩ : syracuseStep 232033 = 174025) (by norm_num)
theorem B461429 : Blo 203807 461429 := bbase (se 5 (by rfl) ⟨21629, by rfl⟩ : syracuseStep 461429 = 43259) (by norm_num)
theorem B658037 : Blo 203807 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B690821 : Blo 203807 690821 := bbase (se 4 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 690821 = 129529) (by norm_num)
theorem B232069 : Blo 203807 232069 := bbase (se 4 (by rfl) ⟨21756, by rfl⟩ : syracuseStep 232069 = 43513) (by norm_num)
theorem B232105 : Blo 203807 232105 := bbase (se 2 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 232105 = 174079) (by norm_num)
theorem B461501 : Blo 203807 461501 := bbase (se 3 (by rfl) ⟨86531, by rfl⟩ : syracuseStep 461501 = 173063) (by norm_num)
theorem B559813 : Blo 203807 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B232141 : Blo 203807 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B232177 : Blo 203807 232177 := bbase (se 2 (by rfl) ⟨87066, by rfl⟩ : syracuseStep 232177 = 174133) (by norm_num)
theorem B330485 : Blo 203807 330485 := bbase (se 5 (by rfl) ⟨15491, by rfl⟩ : syracuseStep 330485 = 30983) (by norm_num)
theorem B461573 : Blo 203807 461573 := bbase (se 4 (by rfl) ⟨43272, by rfl⟩ : syracuseStep 461573 = 86545) (by norm_num)
theorem B232213 : Blo 203807 232213 := bbase (se 6 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 232213 = 10885) (by norm_num)
theorem B232249 : Blo 203807 232249 := bbase (se 2 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 232249 = 174187) (by norm_num)
theorem B461645 : Blo 203807 461645 := bbase (se 3 (by rfl) ⟨86558, by rfl⟩ : syracuseStep 461645 = 173117) (by norm_num)
theorem B232285 : Blo 203807 232285 := bbase (se 3 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 232285 = 87107) (by norm_num)
theorem B232321 : Blo 203807 232321 := bbase (se 2 (by rfl) ⟨87120, by rfl⟩ : syracuseStep 232321 = 174241) (by norm_num)
theorem B461717 : Blo 203807 461717 := bbase (se 6 (by rfl) ⟨10821, by rfl⟩ : syracuseStep 461717 = 21643) (by norm_num)
theorem B1051541 : Blo 203807 1051541 := bbase (se 6 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 1051541 = 49291) (by norm_num)
theorem B232357 : Blo 203807 232357 := bbase (se 4 (by rfl) ⟨21783, by rfl⟩ : syracuseStep 232357 = 43567) (by norm_num)
theorem B232393 : Blo 203807 232393 := bbase (se 2 (by rfl) ⟨87147, by rfl⟩ : syracuseStep 232393 = 174295) (by norm_num)
theorem B461789 : Blo 203807 461789 := bbase (se 3 (by rfl) ⟨86585, by rfl⟩ : syracuseStep 461789 = 173171) (by norm_num)
theorem B232429 : Blo 203807 232429 := bbase (se 3 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 232429 = 87161) (by norm_num)
theorem B232465 : Blo 203807 232465 := bbase (se 2 (by rfl) ⟨87174, by rfl⟩ : syracuseStep 232465 = 174349) (by norm_num)
theorem B461861 : Blo 203807 461861 := bbase (se 4 (by rfl) ⟨43299, by rfl⟩ : syracuseStep 461861 = 86599) (by norm_num)
theorem B691253 : Blo 203807 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B232501 : Blo 203807 232501 := bbase (se 5 (by rfl) ⟨10898, by rfl⟩ : syracuseStep 232501 = 21797) (by norm_num)
theorem B232537 : Blo 203807 232537 := bbase (se 2 (by rfl) ⟨87201, by rfl⟩ : syracuseStep 232537 = 174403) (by norm_num)
theorem B461933 : Blo 203807 461933 := bbase (se 3 (by rfl) ⟨86612, by rfl⟩ : syracuseStep 461933 = 173225) (by norm_num)
theorem B232573 : Blo 203807 232573 := bbase (se 3 (by rfl) ⟨43607, by rfl⟩ : syracuseStep 232573 = 87215) (by norm_num)
theorem B756869 : Blo 203807 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B232609 : Blo 203807 232609 := bbase (se 2 (by rfl) ⟨87228, by rfl⟩ : syracuseStep 232609 = 174457) (by norm_num)
theorem B462005 : Blo 203807 462005 := bbase (se 5 (by rfl) ⟨21656, by rfl⟩ : syracuseStep 462005 = 43313) (by norm_num)
theorem B232645 : Blo 203807 232645 := bbase (se 4 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 232645 = 43621) (by norm_num)
theorem B232681 : Blo 203807 232681 := bbase (se 2 (by rfl) ⟨87255, by rfl⟩ : syracuseStep 232681 = 174511) (by norm_num)
theorem B462077 : Blo 203807 462077 := bbase (se 3 (by rfl) ⟨86639, by rfl⟩ : syracuseStep 462077 = 173279) (by norm_num)
theorem B232717 : Blo 203807 232717 := bbase (se 3 (by rfl) ⟨43634, by rfl⟩ : syracuseStep 232717 = 87269) (by norm_num)
theorem B331037 : Blo 203807 331037 := bbase (se 3 (by rfl) ⟨62069, by rfl⟩ : syracuseStep 331037 = 124139) (by norm_num)
theorem B232753 : Blo 203807 232753 := bbase (se 2 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 232753 = 174565) (by norm_num)
theorem B331069 : Blo 203807 331069 := bbase (se 3 (by rfl) ⟨62075, by rfl⟩ : syracuseStep 331069 = 124151) (by norm_num)
theorem B462149 : Blo 203807 462149 := bbase (se 4 (by rfl) ⟨43326, by rfl⟩ : syracuseStep 462149 = 86653) (by norm_num)
theorem B232789 : Blo 203807 232789 := bbase (se 11 (by rfl) ⟨170, by rfl⟩ : syracuseStep 232789 = 341) (by norm_num)
theorem B232825 : Blo 203807 232825 := bbase (se 2 (by rfl) ⟨87309, by rfl⟩ : syracuseStep 232825 = 174619) (by norm_num)
theorem B462221 : Blo 203807 462221 := bbase (se 3 (by rfl) ⟨86666, by rfl⟩ : syracuseStep 462221 = 173333) (by norm_num)
theorem B232861 : Blo 203807 232861 := bbase (se 3 (by rfl) ⟨43661, by rfl⟩ : syracuseStep 232861 = 87323) (by norm_num)
theorem B232897 : Blo 203807 232897 := bbase (se 2 (by rfl) ⟨87336, by rfl⟩ : syracuseStep 232897 = 174673) (by norm_num)
theorem B462293 : Blo 203807 462293 := bbase (se 7 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 462293 = 10835) (by norm_num)
theorem B691685 : Blo 203807 691685 := bbase (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) (by norm_num)
theorem B232933 : Blo 203807 232933 := bbase (se 4 (by rfl) ⟨21837, by rfl⟩ : syracuseStep 232933 = 43675) (by norm_num)
theorem B232969 : Blo 203807 232969 := bbase (se 2 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 232969 = 174727) (by norm_num)
theorem B462365 : Blo 203807 462365 := bbase (se 3 (by rfl) ⟨86693, by rfl⟩ : syracuseStep 462365 = 173387) (by norm_num)
theorem B232993 : Blo 203807 232993 := bbase (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) (by norm_num)
theorem B233005 : Blo 203807 233005 := bbase (se 3 (by rfl) ⟨43688, by rfl⟩ : syracuseStep 233005 = 87377) (by norm_num)
theorem B233041 : Blo 203807 233041 := bbase (se 2 (by rfl) ⟨87390, by rfl⟩ : syracuseStep 233041 = 174781) (by norm_num)
theorem B462437 : Blo 203807 462437 := bbase (se 4 (by rfl) ⟨43353, by rfl⟩ : syracuseStep 462437 = 86707) (by norm_num)
theorem B233077 : Blo 203807 233077 := bbase (se 5 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 233077 = 21851) (by norm_num)
theorem B1183349 : Blo 203807 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B233113 : Blo 203807 233113 := bbase (se 2 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 233113 = 174835) (by norm_num)
theorem B462509 : Blo 203807 462509 := bbase (se 3 (by rfl) ⟨86720, by rfl⟩ : syracuseStep 462509 = 173441) (by norm_num)
theorem B298669 : Blo 203807 298669 := bbase (se 3 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 298669 = 112001) (by norm_num)
theorem B233149 : Blo 203807 233149 := bbase (se 3 (by rfl) ⟨43715, by rfl⟩ : syracuseStep 233149 = 87431) (by norm_num)
theorem B495325 : Blo 203807 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B233185 : Blo 203807 233185 := bbase (se 2 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 233185 = 174889) (by norm_num)
theorem B462581 : Blo 203807 462581 := bbase (se 5 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 462581 = 43367) (by norm_num)
theorem B233221 : Blo 203807 233221 := bbase (se 4 (by rfl) ⟨21864, by rfl⟩ : syracuseStep 233221 = 43729) (by norm_num)
theorem B233257 : Blo 203807 233257 := bbase (se 2 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 233257 = 174943) (by norm_num)
theorem B462653 : Blo 203807 462653 := bbase (se 3 (by rfl) ⟨86747, by rfl⟩ : syracuseStep 462653 = 173495) (by norm_num)
theorem B233293 : Blo 203807 233293 := bbase (se 3 (by rfl) ⟨43742, by rfl⟩ : syracuseStep 233293 = 87485) (by norm_num)
theorem B233329 : Blo 203807 233329 := bbase (se 2 (by rfl) ⟨87498, by rfl⟩ : syracuseStep 233329 = 174997) (by norm_num)
theorem B1118069 : Blo 203807 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B462725 : Blo 203807 462725 := bbase (se 4 (by rfl) ⟨43380, by rfl⟩ : syracuseStep 462725 = 86761) (by norm_num)
theorem B692117 : Blo 203807 692117 := bbase (se 6 (by rfl) ⟨16221, by rfl⟩ : syracuseStep 692117 = 32443) (by norm_num)
theorem B233365 : Blo 203807 233365 := bbase (se 6 (by rfl) ⟨5469, by rfl⟩ : syracuseStep 233365 = 10939) (by norm_num)
theorem B233401 : Blo 203807 233401 := bbase (se 2 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 233401 = 175051) (by norm_num)
theorem B462797 : Blo 203807 462797 := bbase (se 3 (by rfl) ⟨86774, by rfl⟩ : syracuseStep 462797 = 173549) (by norm_num)
theorem B233437 : Blo 203807 233437 := bbase (se 3 (by rfl) ⟨43769, by rfl⟩ : syracuseStep 233437 = 87539) (by norm_num)
theorem B233473 : Blo 203807 233473 := bbase (se 2 (by rfl) ⟨87552, by rfl⟩ : syracuseStep 233473 = 175105) (by norm_num)
theorem B462869 : Blo 203807 462869 := bbase (se 6 (by rfl) ⟨10848, by rfl⟩ : syracuseStep 462869 = 21697) (by norm_num)
theorem B233509 : Blo 203807 233509 := bbase (se 4 (by rfl) ⟨21891, by rfl⟩ : syracuseStep 233509 = 43783) (by norm_num)
theorem B233545 : Blo 203807 233545 := bbase (se 2 (by rfl) ⟨87579, by rfl⟩ : syracuseStep 233545 = 175159) (by norm_num)
theorem B462941 : Blo 203807 462941 := bbase (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) (by norm_num)
theorem B233581 : Blo 203807 233581 := bbase (se 3 (by rfl) ⟨43796, by rfl⟩ : syracuseStep 233581 = 87593) (by norm_num)
theorem B233617 : Blo 203807 233617 := bbase (se 2 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 233617 = 175213) (by norm_num)
theorem B463013 : Blo 203807 463013 := bbase (se 4 (by rfl) ⟨43407, by rfl⟩ : syracuseStep 463013 = 86815) (by norm_num)
theorem B233653 : Blo 203807 233653 := bbase (se 5 (by rfl) ⟨10952, by rfl⟩ : syracuseStep 233653 = 21905) (by norm_num)
theorem B233689 : Blo 203807 233689 := bbase (se 2 (by rfl) ⟨87633, by rfl⟩ : syracuseStep 233689 = 175267) (by norm_num)
theorem B331997 : Blo 203807 331997 := bbase (se 3 (by rfl) ⟨62249, by rfl⟩ : syracuseStep 331997 = 124499) (by norm_num)
theorem B463085 : Blo 203807 463085 := bbase (se 3 (by rfl) ⟨86828, by rfl⟩ : syracuseStep 463085 = 173657) (by norm_num)
theorem B233725 : Blo 203807 233725 := bbase (se 3 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 233725 = 87647) (by norm_num)
theorem B233761 : Blo 203807 233761 := bbase (se 2 (by rfl) ⟨87660, by rfl⟩ : syracuseStep 233761 = 175321) (by norm_num)
theorem B463157 : Blo 203807 463157 := bbase (se 5 (by rfl) ⟨21710, by rfl⟩ : syracuseStep 463157 = 43421) (by norm_num)
theorem B692549 : Blo 203807 692549 := bbase (se 4 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 692549 = 129853) (by norm_num)
theorem B495989 : Blo 203807 495989 := bbase (se 5 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 495989 = 46499) (by norm_num)
theorem B463229 : Blo 203807 463229 := bbase (se 3 (by rfl) ⟨86855, by rfl⟩ : syracuseStep 463229 = 173711) (by norm_num)
theorem B233869 : Blo 203807 233869 := bbase (se 3 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 233869 = 87701) (by norm_num)
theorem B463301 : Blo 203807 463301 := bbase (se 4 (by rfl) ⟨43434, by rfl⟩ : syracuseStep 463301 = 86869) (by norm_num)
theorem B463373 : Blo 203807 463373 := bbase (se 3 (by rfl) ⟨86882, by rfl⟩ : syracuseStep 463373 = 173765) (by norm_num)
theorem B463445 : Blo 203807 463445 := bbase (se 8 (by rfl) ⟨2715, by rfl⟩ : syracuseStep 463445 = 5431) (by norm_num)
theorem B266905 : Blo 203807 266905 := bbase (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) (by norm_num)
theorem B463517 : Blo 203807 463517 := bbase (se 3 (by rfl) ⟨86909, by rfl⟩ : syracuseStep 463517 = 173819) (by norm_num)
theorem B463589 : Blo 203807 463589 := bbase (se 4 (by rfl) ⟨43461, by rfl⟩ : syracuseStep 463589 = 86923) (by norm_num)
theorem B692981 : Blo 203807 692981 := bbase (se 5 (by rfl) ⟨32483, by rfl⟩ : syracuseStep 692981 = 64967) (by norm_num)
theorem B463661 : Blo 203807 463661 := bbase (se 3 (by rfl) ⟨86936, by rfl⟩ : syracuseStep 463661 = 173873) (by norm_num)
theorem B332605 : Blo 203807 332605 := bbase (se 3 (by rfl) ⟨62363, by rfl⟩ : syracuseStep 332605 = 124727) (by norm_num)
theorem B2954069 : Blo 203807 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B398189 : Blo 203807 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B463733 : Blo 203807 463733 := bbase (se 5 (by rfl) ⟨21737, by rfl⟩ : syracuseStep 463733 = 43475) (by norm_num)
theorem B332677 : Blo 203807 332677 := bbase (se 4 (by rfl) ⟨31188, by rfl⟩ : syracuseStep 332677 = 62377) (by norm_num)
theorem B463805 : Blo 203807 463805 := bbase (se 3 (by rfl) ⟨86963, by rfl⟩ : syracuseStep 463805 = 173927) (by norm_num)
theorem B332741 : Blo 203807 332741 := bbase (se 4 (by rfl) ⟨31194, by rfl⟩ : syracuseStep 332741 = 62389) (by norm_num)
theorem B529357 : Blo 203807 529357 := bbase (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) (by norm_num)
theorem B463877 : Blo 203807 463877 := bbase (se 4 (by rfl) ⟨43488, by rfl⟩ : syracuseStep 463877 = 86977) (by norm_num)
theorem B463949 : Blo 203807 463949 := bbase (se 3 (by rfl) ⟨86990, by rfl⟩ : syracuseStep 463949 = 173981) (by norm_num)
theorem B464021 : Blo 203807 464021 := bbase (se 6 (by rfl) ⟨10875, by rfl⟩ : syracuseStep 464021 = 21751) (by norm_num)
theorem B693413 : Blo 203807 693413 := bbase (se 4 (by rfl) ⟨65007, by rfl⟩ : syracuseStep 693413 = 130015) (by norm_num)
theorem B464093 : Blo 203807 464093 := bbase (se 3 (by rfl) ⟨87017, by rfl⟩ : syracuseStep 464093 = 174035) (by norm_num)
theorem B627941 : Blo 203807 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B464165 : Blo 203807 464165 := bbase (se 4 (by rfl) ⟨43515, by rfl⟩ : syracuseStep 464165 = 87031) (by norm_num)
theorem B464237 : Blo 203807 464237 := bbase (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) (by norm_num)
theorem B660869 : Blo 203807 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B464309 : Blo 203807 464309 := bbase (se 5 (by rfl) ⟨21764, by rfl⟩ : syracuseStep 464309 = 43529) (by norm_num)
theorem B464381 : Blo 203807 464381 := bbase (se 3 (by rfl) ⟨87071, by rfl⟩ : syracuseStep 464381 = 174143) (by norm_num)
theorem B464453 : Blo 203807 464453 := bbase (se 4 (by rfl) ⟨43542, by rfl⟩ : syracuseStep 464453 = 87085) (by norm_num)
theorem B693845 : Blo 203807 693845 := bbase (se 8 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 693845 = 8131) (by norm_num)
theorem B464525 : Blo 203807 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B464597 : Blo 203807 464597 := bbase (se 7 (by rfl) ⟨5444, by rfl⟩ : syracuseStep 464597 = 10889) (by norm_num)
theorem B464669 : Blo 203807 464669 := bbase (se 3 (by rfl) ⟨87125, by rfl⟩ : syracuseStep 464669 = 174251) (by norm_num)
theorem B628549 : Blo 203807 628549 := bbase (se 4 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 628549 = 117853) (by norm_num)
theorem B464741 : Blo 203807 464741 := bbase (se 4 (by rfl) ⟨43569, by rfl⟩ : syracuseStep 464741 = 87139) (by norm_num)
theorem B2627477 : Blo 203807 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B464813 : Blo 203807 464813 := bbase (se 3 (by rfl) ⟨87152, by rfl⟩ : syracuseStep 464813 = 174305) (by norm_num)
theorem B464885 : Blo 203807 464885 := bbase (se 5 (by rfl) ⟨21791, by rfl⟩ : syracuseStep 464885 = 43583) (by norm_num)
theorem B694277 : Blo 203807 694277 := bbase (se 4 (by rfl) ⟨65088, by rfl⟩ : syracuseStep 694277 = 130177) (by norm_num)
theorem B464957 : Blo 203807 464957 := bbase (se 3 (by rfl) ⟨87179, by rfl⟩ : syracuseStep 464957 = 174359) (by norm_num)
theorem B497765 : Blo 203807 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B465029 : Blo 203807 465029 := bbase (se 4 (by rfl) ⟨43596, by rfl⟩ : syracuseStep 465029 = 87193) (by norm_num)
theorem B465101 : Blo 203807 465101 := bbase (se 3 (by rfl) ⟨87206, by rfl⟩ : syracuseStep 465101 = 174413) (by norm_num)
theorem B661765 : Blo 203807 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B465173 : Blo 203807 465173 := bbase (se 6 (by rfl) ⟨10902, by rfl⟩ : syracuseStep 465173 = 21805) (by norm_num)
theorem B465245 : Blo 203807 465245 := bbase (se 3 (by rfl) ⟨87233, by rfl⟩ : syracuseStep 465245 = 174467) (by norm_num)
theorem B465317 : Blo 203807 465317 := bbase (se 4 (by rfl) ⟨43623, by rfl⟩ : syracuseStep 465317 = 87247) (by norm_num)
theorem B694709 : Blo 203807 694709 := bbase (se 5 (by rfl) ⟨32564, by rfl⟩ : syracuseStep 694709 = 65129) (by norm_num)
theorem B465389 : Blo 203807 465389 := bbase (se 3 (by rfl) ⟨87260, by rfl⟩ : syracuseStep 465389 = 174521) (by norm_num)
theorem B662069 : Blo 203807 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B465461 : Blo 203807 465461 := bbase (se 5 (by rfl) ⟨21818, by rfl⟩ : syracuseStep 465461 = 43637) (by norm_num)
theorem B236153 : Blo 203807 236153 := bbase (se 2 (by rfl) ⟨88557, by rfl⟩ : syracuseStep 236153 = 177115) (by norm_num)
theorem B465533 : Blo 203807 465533 := bbase (se 3 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 465533 = 174575) (by norm_num)
theorem B498325 : Blo 203807 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B465605 : Blo 203807 465605 := bbase (se 4 (by rfl) ⟨43650, by rfl⟩ : syracuseStep 465605 = 87301) (by norm_num)
theorem B3185365 : Blo 203807 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B465677 : Blo 203807 465677 := bbase (se 3 (by rfl) ⟨87314, by rfl⟩ : syracuseStep 465677 = 174629) (by norm_num)
theorem B465749 : Blo 203807 465749 := bbase (se 9 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 465749 = 2729) (by norm_num)
theorem B695141 : Blo 203807 695141 := bbase (se 4 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 695141 = 130339) (by norm_num)
theorem B465821 : Blo 203807 465821 := bbase (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) (by norm_num)
theorem B465893 : Blo 203807 465893 := bbase (se 4 (by rfl) ⟨43677, by rfl⟩ : syracuseStep 465893 = 87355) (by norm_num)
theorem B465965 : Blo 203807 465965 := bbase (se 3 (by rfl) ⟨87368, by rfl⟩ : syracuseStep 465965 = 174737) (by norm_num)
theorem B1317941 : Blo 203807 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B466037 : Blo 203807 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B236701 : Blo 203807 236701 := bbase (se 3 (by rfl) ⟨44381, by rfl⟩ : syracuseStep 236701 = 88763) (by norm_num)
theorem B335021 : Blo 203807 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B466109 : Blo 203807 466109 := bbase (se 3 (by rfl) ⟨87395, by rfl⟩ : syracuseStep 466109 = 174791) (by norm_num)
theorem B466181 : Blo 203807 466181 := bbase (se 4 (by rfl) ⟨43704, by rfl⟩ : syracuseStep 466181 = 87409) (by norm_num)
theorem B695573 : Blo 203807 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B466253 : Blo 203807 466253 := bbase (se 3 (by rfl) ⟨87422, by rfl⟩ : syracuseStep 466253 = 174845) (by norm_num)
theorem B466285 : Blo 203807 466285 := bbase (se 3 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 466285 = 174857) (by norm_num)
theorem B466325 : Blo 203807 466325 := bbase (se 6 (by rfl) ⟨10929, by rfl⟩ : syracuseStep 466325 = 21859) (by norm_num)
theorem B368077 : Blo 203807 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B466397 : Blo 203807 466397 := bbase (se 3 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 466397 = 174899) (by norm_num)
theorem B466469 : Blo 203807 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B368221 : Blo 203807 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B466541 : Blo 203807 466541 := bbase (se 3 (by rfl) ⟨87476, by rfl⟩ : syracuseStep 466541 = 174953) (by norm_num)
theorem B466613 : Blo 203807 466613 := bbase (se 5 (by rfl) ⟨21872, by rfl⟩ : syracuseStep 466613 = 43745) (by norm_num)
theorem B990917 : Blo 203807 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B696005 : Blo 203807 696005 := bbase (se 4 (by rfl) ⟨65250, by rfl⟩ : syracuseStep 696005 = 130501) (by norm_num)
theorem B466685 : Blo 203807 466685 := bbase (se 3 (by rfl) ⟨87503, by rfl⟩ : syracuseStep 466685 = 175007) (by norm_num)
theorem B466741 : Blo 203807 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B466757 : Blo 203807 466757 := bbase (se 4 (by rfl) ⟨43758, by rfl⟩ : syracuseStep 466757 = 87517) (by norm_num)
theorem B466829 : Blo 203807 466829 := bbase (se 3 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 466829 = 175061) (by norm_num)
theorem B1253333 : Blo 203807 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B466901 : Blo 203807 466901 := bbase (se 7 (by rfl) ⟨5471, by rfl⟩ : syracuseStep 466901 = 10943) (by norm_num)
theorem B466973 : Blo 203807 466973 := bbase (se 3 (by rfl) ⟨87557, by rfl⟩ : syracuseStep 466973 = 175115) (by norm_num)
theorem B467045 : Blo 203807 467045 := bbase (se 4 (by rfl) ⟨43785, by rfl⟩ : syracuseStep 467045 = 87571) (by norm_num)
theorem B696437 : Blo 203807 696437 := bbase (se 5 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 696437 = 65291) (by norm_num)
theorem B467117 : Blo 203807 467117 := bbase (se 3 (by rfl) ⟨87584, by rfl⟩ : syracuseStep 467117 = 175169) (by norm_num)
theorem B467189 : Blo 203807 467189 := bbase (se 5 (by rfl) ⟨21899, by rfl⟩ : syracuseStep 467189 = 43799) (by norm_num)
theorem B467261 : Blo 203807 467261 := bbase (se 3 (by rfl) ⟨87611, by rfl⟩ : syracuseStep 467261 = 175223) (by norm_num)
theorem B369029 : Blo 203807 369029 := bbase (se 4 (by rfl) ⟨34596, by rfl⟩ : syracuseStep 369029 = 69193) (by norm_num)
theorem B467333 : Blo 203807 467333 := bbase (se 4 (by rfl) ⟨43812, by rfl⟩ : syracuseStep 467333 = 87625) (by norm_num)
theorem B467405 : Blo 203807 467405 := bbase (se 3 (by rfl) ⟨87638, by rfl⟩ : syracuseStep 467405 = 175277) (by norm_num)
theorem B467453 : Blo 203807 467453 := bbase (se 3 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 467453 = 175295) (by norm_num)
theorem B369173 : Blo 203807 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B467477 : Blo 203807 467477 := bbase (se 6 (by rfl) ⟨10956, by rfl⟩ : syracuseStep 467477 = 21913) (by norm_num)
theorem B696869 : Blo 203807 696869 := bbase (se 4 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 696869 = 130663) (by norm_num)
theorem B369245 : Blo 203807 369245 := bbase (se 3 (by rfl) ⟨69233, by rfl⟩ : syracuseStep 369245 = 138467) (by norm_num)
theorem B467549 : Blo 203807 467549 := bbase (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) (by norm_num)
theorem B369461 : Blo 203807 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B303949 : Blo 203807 303949 := bbase (se 3 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 303949 = 113981) (by norm_num)
theorem B1254325 : Blo 203807 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B697301 : Blo 203807 697301 := bbase (se 7 (by rfl) ⟨8171, by rfl⟩ : syracuseStep 697301 = 16343) (by norm_num)
theorem B664661 : Blo 203807 664661 := bbase (se 8 (by rfl) ⟨3894, by rfl⟩ : syracuseStep 664661 = 7789) (by norm_num)
theorem B992533 : Blo 203807 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B599381 : Blo 203807 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B697733 : Blo 203807 697733 := bbase (se 4 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 697733 = 130825) (by norm_num)
theorem B435709 : Blo 203807 435709 := bbase (se 3 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 435709 = 163391) (by norm_num)
theorem B534101 : Blo 203807 534101 := bbase (se 8 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 534101 = 6259) (by norm_num)
theorem B370261 : Blo 203807 370261 := bbase (se 8 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 370261 = 4339) (by norm_num)
theorem B698165 : Blo 203807 698165 := bbase (se 5 (by rfl) ⟨32726, by rfl⟩ : syracuseStep 698165 = 65453) (by norm_num)
theorem B206813 : Blo 203807 206813 := bbase (se 3 (by rfl) ⟨38777, by rfl⟩ : syracuseStep 206813 = 77555) (by norm_num)
theorem B436205 : Blo 203807 436205 := bbase (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) (by norm_num)
theorem B698597 : Blo 203807 698597 := bbase (se 4 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 698597 = 130987) (by norm_num)
theorem B1059077 : Blo 203807 1059077 := bbase (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) (by norm_num)
theorem B207205 : Blo 203807 207205 := bbase (se 4 (by rfl) ⟨19425, by rfl⟩ : syracuseStep 207205 = 38851) (by norm_num)
theorem B371069 : Blo 203807 371069 := bbase (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) (by norm_num)
theorem B2337173 : Blo 203807 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B305717 : Blo 203807 305717 := bbase (se 5 (by rfl) ⟨14330, by rfl⟩ : syracuseStep 305717 = 28661) (by norm_num)
theorem B305741 : Blo 203807 305741 := bbase (se 3 (by rfl) ⟨57326, by rfl⟩ : syracuseStep 305741 = 114653) (by norm_num)
theorem B305765 : Blo 203807 305765 := bbase (se 4 (by rfl) ⟨28665, by rfl⟩ : syracuseStep 305765 = 57331) (by norm_num)
theorem B305789 : Blo 203807 305789 := bbase (se 3 (by rfl) ⟨57335, by rfl⟩ : syracuseStep 305789 = 114671) (by norm_num)
theorem B305813 : Blo 203807 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B699029 : Blo 203807 699029 := bbase (se 6 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 699029 = 32767) (by norm_num)
theorem B305837 : Blo 203807 305837 := bbase (se 3 (by rfl) ⟨57344, by rfl⟩ : syracuseStep 305837 = 114689) (by norm_num)
theorem B305861 : Blo 203807 305861 := bbase (se 4 (by rfl) ⟨28674, by rfl⟩ : syracuseStep 305861 = 57349) (by norm_num)
theorem B305885 : Blo 203807 305885 := bbase (se 3 (by rfl) ⟨57353, by rfl⟩ : syracuseStep 305885 = 114707) (by norm_num)
theorem B305909 : Blo 203807 305909 := bbase (se 5 (by rfl) ⟨14339, by rfl⟩ : syracuseStep 305909 = 28679) (by norm_num)
theorem B305933 : Blo 203807 305933 := bbase (se 3 (by rfl) ⟨57362, by rfl⟩ : syracuseStep 305933 = 114725) (by norm_num)
theorem B305957 : Blo 203807 305957 := bbase (se 4 (by rfl) ⟨28683, by rfl⟩ : syracuseStep 305957 = 57367) (by norm_num)
theorem B305981 : Blo 203807 305981 := bbase (se 3 (by rfl) ⟨57371, by rfl⟩ : syracuseStep 305981 = 114743) (by norm_num)
theorem B306005 : Blo 203807 306005 := bbase (se 9 (by rfl) ⟨896, by rfl⟩ : syracuseStep 306005 = 1793) (by norm_num)
theorem B437093 : Blo 203807 437093 := bbase (se 4 (by rfl) ⟨40977, by rfl⟩ : syracuseStep 437093 = 81955) (by norm_num)
theorem B306029 : Blo 203807 306029 := bbase (se 3 (by rfl) ⟨57380, by rfl⟩ : syracuseStep 306029 = 114761) (by norm_num)
theorem B306053 : Blo 203807 306053 := bbase (se 4 (by rfl) ⟨28692, by rfl⟩ : syracuseStep 306053 = 57385) (by norm_num)
theorem B306077 : Blo 203807 306077 := bbase (se 3 (by rfl) ⟨57389, by rfl⟩ : syracuseStep 306077 = 114779) (by norm_num)
theorem B306101 : Blo 203807 306101 := bbase (se 5 (by rfl) ⟨14348, by rfl⟩ : syracuseStep 306101 = 28697) (by norm_num)
theorem B306125 : Blo 203807 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B437213 : Blo 203807 437213 := bbase (se 3 (by rfl) ⟨81977, by rfl⟩ : syracuseStep 437213 = 163955) (by norm_num)
theorem B306149 : Blo 203807 306149 := bbase (se 4 (by rfl) ⟨28701, by rfl⟩ : syracuseStep 306149 = 57403) (by norm_num)
theorem B928741 : Blo 203807 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B306173 : Blo 203807 306173 := bbase (se 3 (by rfl) ⟨57407, by rfl⟩ : syracuseStep 306173 = 114815) (by norm_num)
theorem B306197 : Blo 203807 306197 := bbase (se 6 (by rfl) ⟨7176, by rfl⟩ : syracuseStep 306197 = 14353) (by norm_num)
theorem B306221 : Blo 203807 306221 := bbase (se 3 (by rfl) ⟨57416, by rfl⟩ : syracuseStep 306221 = 114833) (by norm_num)
theorem B306245 : Blo 203807 306245 := bbase (se 4 (by rfl) ⟨28710, by rfl⟩ : syracuseStep 306245 = 57421) (by norm_num)
theorem B699461 : Blo 203807 699461 := bbase (se 4 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 699461 = 131149) (by norm_num)
theorem B306269 : Blo 203807 306269 := bbase (se 3 (by rfl) ⟨57425, by rfl⟩ : syracuseStep 306269 = 114851) (by norm_num)
theorem B306293 : Blo 203807 306293 := bbase (se 5 (by rfl) ⟨14357, by rfl⟩ : syracuseStep 306293 = 28715) (by norm_num)
theorem B306317 : Blo 203807 306317 := bbase (se 3 (by rfl) ⟨57434, by rfl⟩ : syracuseStep 306317 = 114869) (by norm_num)
theorem B208013 : Blo 203807 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B306341 : Blo 203807 306341 := bbase (se 4 (by rfl) ⟨28719, by rfl⟩ : syracuseStep 306341 = 57439) (by norm_num)
theorem B306365 : Blo 203807 306365 := bbase (se 3 (by rfl) ⟨57443, by rfl⟩ : syracuseStep 306365 = 114887) (by norm_num)
theorem B306389 : Blo 203807 306389 := bbase (se 7 (by rfl) ⟨3590, by rfl⟩ : syracuseStep 306389 = 7181) (by norm_num)
theorem B306413 : Blo 203807 306413 := bbase (se 3 (by rfl) ⟨57452, by rfl⟩ : syracuseStep 306413 = 114905) (by norm_num)
theorem B306437 : Blo 203807 306437 := bbase (se 4 (by rfl) ⟨28728, by rfl⟩ : syracuseStep 306437 = 57457) (by norm_num)
theorem B306461 : Blo 203807 306461 := bbase (se 3 (by rfl) ⟨57461, by rfl⟩ : syracuseStep 306461 = 114923) (by norm_num)
theorem B306485 : Blo 203807 306485 := bbase (se 5 (by rfl) ⟨14366, by rfl⟩ : syracuseStep 306485 = 28733) (by norm_num)
theorem B306509 : Blo 203807 306509 := bbase (se 3 (by rfl) ⟨57470, by rfl⟩ : syracuseStep 306509 = 114941) (by norm_num)
theorem B306533 : Blo 203807 306533 := bbase (se 4 (by rfl) ⟨28737, by rfl⟩ : syracuseStep 306533 = 57475) (by norm_num)
theorem B306557 : Blo 203807 306557 := bbase (se 3 (by rfl) ⟨57479, by rfl⟩ : syracuseStep 306557 = 114959) (by norm_num)
theorem B306581 : Blo 203807 306581 := bbase (se 6 (by rfl) ⟨7185, by rfl⟩ : syracuseStep 306581 = 14371) (by norm_num)
theorem B306605 : Blo 203807 306605 := bbase (se 3 (by rfl) ⟨57488, by rfl⟩ : syracuseStep 306605 = 114977) (by norm_num)
theorem B1551797 : Blo 203807 1551797 := bbase (se 5 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 1551797 = 145481) (by norm_num)
theorem B306629 : Blo 203807 306629 := bbase (se 4 (by rfl) ⟨28746, by rfl⟩ : syracuseStep 306629 = 57493) (by norm_num)
theorem B306653 : Blo 203807 306653 := bbase (se 3 (by rfl) ⟨57497, by rfl⟩ : syracuseStep 306653 = 114995) (by norm_num)
theorem B306677 : Blo 203807 306677 := bbase (se 5 (by rfl) ⟨14375, by rfl⟩ : syracuseStep 306677 = 28751) (by norm_num)
theorem B699893 : Blo 203807 699893 := bbase (se 5 (by rfl) ⟨32807, by rfl⟩ : syracuseStep 699893 = 65615) (by norm_num)
theorem B306701 : Blo 203807 306701 := bbase (se 3 (by rfl) ⟨57506, by rfl⟩ : syracuseStep 306701 = 115013) (by norm_num)
theorem B306725 : Blo 203807 306725 := bbase (se 4 (by rfl) ⟨28755, by rfl⟩ : syracuseStep 306725 = 57511) (by norm_num)
theorem B306749 : Blo 203807 306749 := bbase (se 3 (by rfl) ⟨57515, by rfl⟩ : syracuseStep 306749 = 115031) (by norm_num)
theorem B306773 : Blo 203807 306773 := bbase (se 8 (by rfl) ⟨1797, by rfl⟩ : syracuseStep 306773 = 3595) (by norm_num)
theorem B437845 : Blo 203807 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B306797 : Blo 203807 306797 := bbase (se 3 (by rfl) ⟨57524, by rfl⟩ : syracuseStep 306797 = 115049) (by norm_num)
theorem B306821 : Blo 203807 306821 := bbase (se 4 (by rfl) ⟨28764, by rfl⟩ : syracuseStep 306821 = 57529) (by norm_num)
theorem B306845 : Blo 203807 306845 := bbase (se 3 (by rfl) ⟨57533, by rfl⟩ : syracuseStep 306845 = 115067) (by norm_num)
theorem B306869 : Blo 203807 306869 := bbase (se 5 (by rfl) ⟨14384, by rfl⟩ : syracuseStep 306869 = 28769) (by norm_num)
theorem B306893 : Blo 203807 306893 := bbase (se 3 (by rfl) ⟨57542, by rfl⟩ : syracuseStep 306893 = 115085) (by norm_num)
theorem B306917 : Blo 203807 306917 := bbase (se 4 (by rfl) ⟨28773, by rfl⟩ : syracuseStep 306917 = 57547) (by norm_num)
theorem B306941 : Blo 203807 306941 := bbase (se 3 (by rfl) ⟨57551, by rfl⟩ : syracuseStep 306941 = 115103) (by norm_num)
theorem B306965 : Blo 203807 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B306989 : Blo 203807 306989 := bbase (se 3 (by rfl) ⟨57560, by rfl⟩ : syracuseStep 306989 = 115121) (by norm_num)
theorem B307013 : Blo 203807 307013 := bbase (se 4 (by rfl) ⟨28782, by rfl⟩ : syracuseStep 307013 = 57565) (by norm_num)
theorem B307037 : Blo 203807 307037 := bbase (se 3 (by rfl) ⟨57569, by rfl⟩ : syracuseStep 307037 = 115139) (by norm_num)
theorem B307061 : Blo 203807 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B307085 : Blo 203807 307085 := bbase (se 3 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 307085 = 115157) (by norm_num)
theorem B307109 : Blo 203807 307109 := bbase (se 4 (by rfl) ⟨28791, by rfl⟩ : syracuseStep 307109 = 57583) (by norm_num)
theorem B700325 : Blo 203807 700325 := bbase (se 4 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 700325 = 131311) (by norm_num)
theorem B307133 : Blo 203807 307133 := bbase (se 3 (by rfl) ⟨57587, by rfl⟩ : syracuseStep 307133 = 115175) (by norm_num)
theorem B307157 : Blo 203807 307157 := bbase (se 7 (by rfl) ⟨3599, by rfl⟩ : syracuseStep 307157 = 7199) (by norm_num)
theorem B307181 : Blo 203807 307181 := bbase (se 3 (by rfl) ⟨57596, by rfl⟩ : syracuseStep 307181 = 115193) (by norm_num)
theorem B307205 : Blo 203807 307205 := bbase (se 4 (by rfl) ⟨28800, by rfl⟩ : syracuseStep 307205 = 57601) (by norm_num)
theorem B307229 : Blo 203807 307229 := bbase (se 3 (by rfl) ⟨57605, by rfl⟩ : syracuseStep 307229 = 115211) (by norm_num)
theorem B307253 : Blo 203807 307253 := bbase (se 5 (by rfl) ⟨14402, by rfl⟩ : syracuseStep 307253 = 28805) (by norm_num)
theorem B307277 : Blo 203807 307277 := bbase (se 3 (by rfl) ⟨57614, by rfl⟩ : syracuseStep 307277 = 115229) (by norm_num)
theorem B307301 : Blo 203807 307301 := bbase (se 4 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 307301 = 57619) (by norm_num)
theorem B307325 : Blo 203807 307325 := bbase (se 3 (by rfl) ⟨57623, by rfl⟩ : syracuseStep 307325 = 115247) (by norm_num)
theorem B307349 : Blo 203807 307349 := bbase (se 6 (by rfl) ⟨7203, by rfl⟩ : syracuseStep 307349 = 14407) (by norm_num)
theorem B307373 : Blo 203807 307373 := bbase (se 3 (by rfl) ⟨57632, by rfl⟩ : syracuseStep 307373 = 115265) (by norm_num)
theorem B307397 : Blo 203807 307397 := bbase (se 4 (by rfl) ⟨28818, by rfl⟩ : syracuseStep 307397 = 57637) (by norm_num)
theorem B307421 : Blo 203807 307421 := bbase (se 3 (by rfl) ⟨57641, by rfl⟩ : syracuseStep 307421 = 115283) (by norm_num)
theorem B307445 : Blo 203807 307445 := bbase (se 5 (by rfl) ⟨14411, by rfl⟩ : syracuseStep 307445 = 28823) (by norm_num)
theorem B307469 : Blo 203807 307469 := bbase (se 3 (by rfl) ⟨57650, by rfl⟩ : syracuseStep 307469 = 115301) (by norm_num)
theorem B307493 : Blo 203807 307493 := bbase (se 4 (by rfl) ⟨28827, by rfl⟩ : syracuseStep 307493 = 57655) (by norm_num)
theorem B307517 : Blo 203807 307517 := bbase (se 3 (by rfl) ⟨57659, by rfl⟩ : syracuseStep 307517 = 115319) (by norm_num)
theorem B307541 : Blo 203807 307541 := bbase (se 10 (by rfl) ⟨450, by rfl⟩ : syracuseStep 307541 = 901) (by norm_num)
theorem B700757 : Blo 203807 700757 := bbase (se 10 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 700757 = 2053) (by norm_num)
theorem B307565 : Blo 203807 307565 := bbase (se 3 (by rfl) ⟨57668, by rfl⟩ : syracuseStep 307565 = 115337) (by norm_num)
theorem B307589 : Blo 203807 307589 := bbase (se 4 (by rfl) ⟨28836, by rfl⟩ : syracuseStep 307589 = 57673) (by norm_num)
theorem B307613 : Blo 203807 307613 := bbase (se 3 (by rfl) ⟨57677, by rfl⟩ : syracuseStep 307613 = 115355) (by norm_num)
theorem B307637 : Blo 203807 307637 := bbase (se 5 (by rfl) ⟨14420, by rfl⟩ : syracuseStep 307637 = 28841) (by norm_num)
theorem B307661 : Blo 203807 307661 := bbase (se 3 (by rfl) ⟨57686, by rfl⟩ : syracuseStep 307661 = 115373) (by norm_num)
theorem B438733 : Blo 203807 438733 := bbase (se 3 (by rfl) ⟨82262, by rfl⟩ : syracuseStep 438733 = 164525) (by norm_num)
theorem B307685 : Blo 203807 307685 := bbase (se 4 (by rfl) ⟨28845, by rfl⟩ : syracuseStep 307685 = 57691) (by norm_num)
theorem B307709 : Blo 203807 307709 := bbase (se 3 (by rfl) ⟨57695, by rfl⟩ : syracuseStep 307709 = 115391) (by norm_num)
theorem B700949 : Blo 203807 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B307733 : Blo 203807 307733 := bbase (se 6 (by rfl) ⟨7212, by rfl⟩ : syracuseStep 307733 = 14425) (by norm_num)
theorem B307757 : Blo 203807 307757 := bbase (se 3 (by rfl) ⟨57704, by rfl⟩ : syracuseStep 307757 = 115409) (by norm_num)
theorem B307781 : Blo 203807 307781 := bbase (se 4 (by rfl) ⟨28854, by rfl⟩ : syracuseStep 307781 = 57709) (by norm_num)
theorem B438853 : Blo 203807 438853 := bbase (se 4 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 438853 = 82285) (by norm_num)
theorem B307805 : Blo 203807 307805 := bbase (se 3 (by rfl) ⟨57713, by rfl⟩ : syracuseStep 307805 = 115427) (by norm_num)
theorem B307829 : Blo 203807 307829 := bbase (se 5 (by rfl) ⟨14429, by rfl⟩ : syracuseStep 307829 = 28859) (by norm_num)
theorem B209525 : Blo 203807 209525 := bbase (se 5 (by rfl) ⟨9821, by rfl⟩ : syracuseStep 209525 = 19643) (by norm_num)
theorem B307853 : Blo 203807 307853 := bbase (se 3 (by rfl) ⟨57722, by rfl⟩ : syracuseStep 307853 = 115445) (by norm_num)
theorem B307877 : Blo 203807 307877 := bbase (se 4 (by rfl) ⟨28863, by rfl⟩ : syracuseStep 307877 = 57727) (by norm_num)
theorem B307901 : Blo 203807 307901 := bbase (se 3 (by rfl) ⟨57731, by rfl⟩ : syracuseStep 307901 = 115463) (by norm_num)
theorem B307925 : Blo 203807 307925 := bbase (se 7 (by rfl) ⟨3608, by rfl⟩ : syracuseStep 307925 = 7217) (by norm_num)
theorem B307949 : Blo 203807 307949 := bbase (se 3 (by rfl) ⟨57740, by rfl⟩ : syracuseStep 307949 = 115481) (by norm_num)
theorem B996101 : Blo 203807 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B307973 : Blo 203807 307973 := bbase (se 4 (by rfl) ⟨28872, by rfl⟩ : syracuseStep 307973 = 57745) (by norm_num)
theorem B701189 : Blo 203807 701189 := bbase (se 4 (by rfl) ⟨65736, by rfl⟩ : syracuseStep 701189 = 131473) (by norm_num)
theorem B307997 : Blo 203807 307997 := bbase (se 3 (by rfl) ⟨57749, by rfl⟩ : syracuseStep 307997 = 115499) (by norm_num)
theorem B308021 : Blo 203807 308021 := bbase (se 5 (by rfl) ⟨14438, by rfl⟩ : syracuseStep 308021 = 28877) (by norm_num)
theorem B439109 : Blo 203807 439109 := bbase (se 4 (by rfl) ⟨41166, by rfl⟩ : syracuseStep 439109 = 82333) (by norm_num)
theorem B308045 : Blo 203807 308045 := bbase (se 3 (by rfl) ⟨57758, by rfl⟩ : syracuseStep 308045 = 115517) (by norm_num)
theorem B308069 : Blo 203807 308069 := bbase (se 4 (by rfl) ⟨28881, by rfl⟩ : syracuseStep 308069 = 57763) (by norm_num)
theorem B308093 : Blo 203807 308093 := bbase (se 3 (by rfl) ⟨57767, by rfl⟩ : syracuseStep 308093 = 115535) (by norm_num)
theorem B308117 : Blo 203807 308117 := bbase (se 6 (by rfl) ⟨7221, by rfl⟩ : syracuseStep 308117 = 14443) (by norm_num)
theorem B1880981 : Blo 203807 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B308141 : Blo 203807 308141 := bbase (se 3 (by rfl) ⟨57776, by rfl⟩ : syracuseStep 308141 = 115553) (by norm_num)
theorem B471997 : Blo 203807 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B308165 : Blo 203807 308165 := bbase (se 4 (by rfl) ⟨28890, by rfl⟩ : syracuseStep 308165 = 57781) (by norm_num)
theorem B308189 : Blo 203807 308189 := bbase (se 3 (by rfl) ⟨57785, by rfl⟩ : syracuseStep 308189 = 115571) (by norm_num)
theorem B308213 : Blo 203807 308213 := bbase (se 5 (by rfl) ⟨14447, by rfl⟩ : syracuseStep 308213 = 28895) (by norm_num)
theorem B308237 : Blo 203807 308237 := bbase (se 3 (by rfl) ⟨57794, by rfl⟩ : syracuseStep 308237 = 115589) (by norm_num)
theorem B308261 : Blo 203807 308261 := bbase (se 4 (by rfl) ⟨28899, by rfl⟩ : syracuseStep 308261 = 57799) (by norm_num)
theorem B308285 : Blo 203807 308285 := bbase (se 3 (by rfl) ⟨57803, by rfl⟩ : syracuseStep 308285 = 115607) (by norm_num)
theorem B373837 : Blo 203807 373837 := bbase (se 3 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 373837 = 140189) (by norm_num)
theorem B308309 : Blo 203807 308309 := bbase (se 8 (by rfl) ⟨1806, by rfl⟩ : syracuseStep 308309 = 3613) (by norm_num)
theorem B308333 : Blo 203807 308333 := bbase (se 3 (by rfl) ⟨57812, by rfl⟩ : syracuseStep 308333 = 115625) (by norm_num)
theorem B308357 : Blo 203807 308357 := bbase (se 4 (by rfl) ⟨28908, by rfl⟩ : syracuseStep 308357 = 57817) (by norm_num)
theorem B308381 : Blo 203807 308381 := bbase (se 3 (by rfl) ⟨57821, by rfl⟩ : syracuseStep 308381 = 115643) (by norm_num)
theorem B308405 : Blo 203807 308405 := bbase (se 5 (by rfl) ⟨14456, by rfl⟩ : syracuseStep 308405 = 28913) (by norm_num)
theorem B308429 : Blo 203807 308429 := bbase (se 3 (by rfl) ⟨57830, by rfl⟩ : syracuseStep 308429 = 115661) (by norm_num)
theorem B308453 : Blo 203807 308453 := bbase (se 4 (by rfl) ⟨28917, by rfl⟩ : syracuseStep 308453 = 57835) (by norm_num)
theorem B210157 : Blo 203807 210157 := bbase (se 3 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 210157 = 78809) (by norm_num)
theorem B308477 : Blo 203807 308477 := bbase (se 3 (by rfl) ⟨57839, by rfl⟩ : syracuseStep 308477 = 115679) (by norm_num)
theorem B308501 : Blo 203807 308501 := bbase (se 6 (by rfl) ⟨7230, by rfl⟩ : syracuseStep 308501 = 14461) (by norm_num)
theorem B308525 : Blo 203807 308525 := bbase (se 3 (by rfl) ⟨57848, by rfl⟩ : syracuseStep 308525 = 115697) (by norm_num)
theorem B308549 : Blo 203807 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B308573 : Blo 203807 308573 := bbase (se 3 (by rfl) ⟨57857, by rfl⟩ : syracuseStep 308573 = 115715) (by norm_num)
theorem B308597 : Blo 203807 308597 := bbase (se 5 (by rfl) ⟨14465, by rfl⟩ : syracuseStep 308597 = 28931) (by norm_num)
theorem B308621 : Blo 203807 308621 := bbase (se 3 (by rfl) ⟨57866, by rfl⟩ : syracuseStep 308621 = 115733) (by norm_num)
theorem B308645 : Blo 203807 308645 := bbase (se 4 (by rfl) ⟨28935, by rfl⟩ : syracuseStep 308645 = 57871) (by norm_num)
theorem B308669 : Blo 203807 308669 := bbase (se 3 (by rfl) ⟨57875, by rfl⟩ : syracuseStep 308669 = 115751) (by norm_num)
theorem B308693 : Blo 203807 308693 := bbase (se 7 (by rfl) ⟨3617, by rfl⟩ : syracuseStep 308693 = 7235) (by norm_num)
theorem B308717 : Blo 203807 308717 := bbase (se 3 (by rfl) ⟨57884, by rfl⟩ : syracuseStep 308717 = 115769) (by norm_num)
theorem B210433 : Blo 203807 210433 := bbase (se 2 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 210433 = 157825) (by norm_num)
theorem B308741 : Blo 203807 308741 := bbase (se 4 (by rfl) ⟨28944, by rfl⟩ : syracuseStep 308741 = 57889) (by norm_num)
theorem B210449 : Blo 203807 210449 := bbase (se 2 (by rfl) ⟨78918, by rfl⟩ : syracuseStep 210449 = 157837) (by norm_num)
theorem B308765 : Blo 203807 308765 := bbase (se 3 (by rfl) ⟨57893, by rfl⟩ : syracuseStep 308765 = 115787) (by norm_num)
theorem B308789 : Blo 203807 308789 := bbase (se 5 (by rfl) ⟨14474, by rfl⟩ : syracuseStep 308789 = 28949) (by norm_num)
theorem B308813 : Blo 203807 308813 := bbase (se 3 (by rfl) ⟨57902, by rfl⟩ : syracuseStep 308813 = 115805) (by norm_num)
theorem B308837 : Blo 203807 308837 := bbase (se 4 (by rfl) ⟨28953, by rfl⟩ : syracuseStep 308837 = 57907) (by norm_num)
theorem B308861 : Blo 203807 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B308885 : Blo 203807 308885 := bbase (se 6 (by rfl) ⟨7239, by rfl⟩ : syracuseStep 308885 = 14479) (by norm_num)
theorem B308909 : Blo 203807 308909 := bbase (se 3 (by rfl) ⟨57920, by rfl⟩ : syracuseStep 308909 = 115841) (by norm_num)
theorem B439997 : Blo 203807 439997 := bbase (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) (by norm_num)
theorem B308933 : Blo 203807 308933 := bbase (se 4 (by rfl) ⟨28962, by rfl⟩ : syracuseStep 308933 = 57925) (by norm_num)
theorem B374477 : Blo 203807 374477 := bbase (se 3 (by rfl) ⟨70214, by rfl⟩ : syracuseStep 374477 = 140429) (by norm_num)
theorem B308957 : Blo 203807 308957 := bbase (se 3 (by rfl) ⟨57929, by rfl⟩ : syracuseStep 308957 = 115859) (by norm_num)
theorem B308981 : Blo 203807 308981 := bbase (se 5 (by rfl) ⟨14483, by rfl⟩ : syracuseStep 308981 = 28967) (by norm_num)
theorem B309005 : Blo 203807 309005 := bbase (se 3 (by rfl) ⟨57938, by rfl⟩ : syracuseStep 309005 = 115877) (by norm_num)
theorem B309029 : Blo 203807 309029 := bbase (se 4 (by rfl) ⟨28971, by rfl⟩ : syracuseStep 309029 = 57943) (by norm_num)
theorem B309053 : Blo 203807 309053 := bbase (se 3 (by rfl) ⟨57947, by rfl⟩ : syracuseStep 309053 = 115895) (by norm_num)
theorem B309077 : Blo 203807 309077 := bbase (se 9 (by rfl) ⟨905, by rfl⟩ : syracuseStep 309077 = 1811) (by norm_num)
theorem B309101 : Blo 203807 309101 := bbase (se 3 (by rfl) ⟨57956, by rfl⟩ : syracuseStep 309101 = 115913) (by norm_num)
theorem B309125 : Blo 203807 309125 := bbase (se 4 (by rfl) ⟨28980, by rfl⟩ : syracuseStep 309125 = 57961) (by norm_num)
theorem B2537365 : Blo 203807 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B309149 : Blo 203807 309149 := bbase (se 3 (by rfl) ⟨57965, by rfl⟩ : syracuseStep 309149 = 115931) (by norm_num)
theorem B440237 : Blo 203807 440237 := bbase (se 3 (by rfl) ⟨82544, by rfl⟩ : syracuseStep 440237 = 165089) (by norm_num)
theorem B309173 : Blo 203807 309173 := bbase (se 5 (by rfl) ⟨14492, by rfl⟩ : syracuseStep 309173 = 28985) (by norm_num)
theorem B309197 : Blo 203807 309197 := bbase (se 3 (by rfl) ⟨57974, by rfl⟩ : syracuseStep 309197 = 115949) (by norm_num)
theorem B309221 : Blo 203807 309221 := bbase (se 4 (by rfl) ⟨28989, by rfl⟩ : syracuseStep 309221 = 57979) (by norm_num)
theorem B309245 : Blo 203807 309245 := bbase (se 3 (by rfl) ⟨57983, by rfl⟩ : syracuseStep 309245 = 115967) (by norm_num)
theorem B309269 : Blo 203807 309269 := bbase (se 6 (by rfl) ⟨7248, by rfl⟩ : syracuseStep 309269 = 14497) (by norm_num)
theorem B309293 : Blo 203807 309293 := bbase (se 3 (by rfl) ⟨57992, by rfl⟩ : syracuseStep 309293 = 115985) (by norm_num)
theorem B309317 : Blo 203807 309317 := bbase (se 4 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 309317 = 57997) (by norm_num)
theorem B309341 : Blo 203807 309341 := bbase (se 3 (by rfl) ⟨58001, by rfl⟩ : syracuseStep 309341 = 116003) (by norm_num)
theorem B309365 : Blo 203807 309365 := bbase (se 5 (by rfl) ⟨14501, by rfl⟩ : syracuseStep 309365 = 29003) (by norm_num)
theorem B309389 : Blo 203807 309389 := bbase (se 3 (by rfl) ⟨58010, by rfl⟩ : syracuseStep 309389 = 116021) (by norm_num)
theorem B309413 : Blo 203807 309413 := bbase (se 4 (by rfl) ⟨29007, by rfl⟩ : syracuseStep 309413 = 58015) (by norm_num)
theorem B309437 : Blo 203807 309437 := bbase (se 3 (by rfl) ⟨58019, by rfl⟩ : syracuseStep 309437 = 116039) (by norm_num)
theorem B309461 : Blo 203807 309461 := bbase (se 7 (by rfl) ⟨3626, by rfl⟩ : syracuseStep 309461 = 7253) (by norm_num)
theorem B309485 : Blo 203807 309485 := bbase (se 3 (by rfl) ⟨58028, by rfl⟩ : syracuseStep 309485 = 116057) (by norm_num)
theorem B669941 : Blo 203807 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B309509 : Blo 203807 309509 := bbase (se 4 (by rfl) ⟨29016, by rfl⟩ : syracuseStep 309509 = 58033) (by norm_num)
theorem B309533 : Blo 203807 309533 := bbase (se 3 (by rfl) ⟨58037, by rfl⟩ : syracuseStep 309533 = 116075) (by norm_num)
theorem B309557 : Blo 203807 309557 := bbase (se 5 (by rfl) ⟨14510, by rfl⟩ : syracuseStep 309557 = 29021) (by norm_num)
theorem B899381 : Blo 203807 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B309581 : Blo 203807 309581 := bbase (se 3 (by rfl) ⟨58046, by rfl⟩ : syracuseStep 309581 = 116093) (by norm_num)
theorem B309605 : Blo 203807 309605 := bbase (se 4 (by rfl) ⟨29025, by rfl⟩ : syracuseStep 309605 = 58051) (by norm_num)
theorem B309629 : Blo 203807 309629 := bbase (se 3 (by rfl) ⟨58055, by rfl⟩ : syracuseStep 309629 = 116111) (by norm_num)
theorem B309653 : Blo 203807 309653 := bbase (se 6 (by rfl) ⟨7257, by rfl⟩ : syracuseStep 309653 = 14515) (by norm_num)
theorem B440741 : Blo 203807 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B440749 : Blo 203807 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B309677 : Blo 203807 309677 := bbase (se 3 (by rfl) ⟨58064, by rfl⟩ : syracuseStep 309677 = 116129) (by norm_num)
theorem B309701 : Blo 203807 309701 := bbase (se 4 (by rfl) ⟨29034, by rfl⟩ : syracuseStep 309701 = 58069) (by norm_num)
theorem B309725 : Blo 203807 309725 := bbase (se 3 (by rfl) ⟨58073, by rfl⟩ : syracuseStep 309725 = 116147) (by norm_num)
theorem B309749 : Blo 203807 309749 := bbase (se 5 (by rfl) ⟨14519, by rfl⟩ : syracuseStep 309749 = 29039) (by norm_num)
theorem B309773 : Blo 203807 309773 := bbase (se 3 (by rfl) ⟨58082, by rfl⟩ : syracuseStep 309773 = 116165) (by norm_num)
theorem B3750421 : Blo 203807 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B309797 : Blo 203807 309797 := bbase (se 4 (by rfl) ⟨29043, by rfl⟩ : syracuseStep 309797 = 58087) (by norm_num)
theorem B309821 : Blo 203807 309821 := bbase (se 3 (by rfl) ⟨58091, by rfl⟩ : syracuseStep 309821 = 116183) (by norm_num)
theorem B309845 : Blo 203807 309845 := bbase (se 8 (by rfl) ⟨1815, by rfl⟩ : syracuseStep 309845 = 3631) (by norm_num)
theorem B309869 : Blo 203807 309869 := bbase (se 3 (by rfl) ⟨58100, by rfl⟩ : syracuseStep 309869 = 116201) (by norm_num)
theorem B309893 : Blo 203807 309893 := bbase (se 4 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 309893 = 58105) (by norm_num)
theorem B309917 : Blo 203807 309917 := bbase (se 3 (by rfl) ⟨58109, by rfl⟩ : syracuseStep 309917 = 116219) (by norm_num)
theorem B309941 : Blo 203807 309941 := bbase (se 5 (by rfl) ⟨14528, by rfl⟩ : syracuseStep 309941 = 29057) (by norm_num)
theorem B309965 : Blo 203807 309965 := bbase (se 3 (by rfl) ⟨58118, by rfl⟩ : syracuseStep 309965 = 116237) (by norm_num)
theorem B309989 : Blo 203807 309989 := bbase (se 4 (by rfl) ⟨29061, by rfl⟩ : syracuseStep 309989 = 58123) (by norm_num)
theorem B310013 : Blo 203807 310013 := bbase (se 3 (by rfl) ⟨58127, by rfl⟩ : syracuseStep 310013 = 116255) (by norm_num)
theorem B310037 : Blo 203807 310037 := bbase (se 6 (by rfl) ⟨7266, by rfl⟩ : syracuseStep 310037 = 14533) (by norm_num)
theorem B310061 : Blo 203807 310061 := bbase (se 3 (by rfl) ⟨58136, by rfl⟩ : syracuseStep 310061 = 116273) (by norm_num)
theorem B310085 : Blo 203807 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B310109 : Blo 203807 310109 := bbase (se 3 (by rfl) ⟨58145, by rfl⟩ : syracuseStep 310109 = 116291) (by norm_num)
theorem B310133 : Blo 203807 310133 := bbase (se 5 (by rfl) ⟨14537, by rfl⟩ : syracuseStep 310133 = 29075) (by norm_num)
theorem B310157 : Blo 203807 310157 := bbase (se 3 (by rfl) ⟨58154, by rfl⟩ : syracuseStep 310157 = 116309) (by norm_num)
theorem B310181 : Blo 203807 310181 := bbase (se 4 (by rfl) ⟨29079, by rfl⟩ : syracuseStep 310181 = 58159) (by norm_num)
theorem B310205 : Blo 203807 310205 := bbase (se 3 (by rfl) ⟨58163, by rfl⟩ : syracuseStep 310205 = 116327) (by norm_num)
theorem B277453 : Blo 203807 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B310229 : Blo 203807 310229 := bbase (se 7 (by rfl) ⟨3635, by rfl⟩ : syracuseStep 310229 = 7271) (by norm_num)
theorem B310253 : Blo 203807 310253 := bbase (se 3 (by rfl) ⟨58172, by rfl⟩ : syracuseStep 310253 = 116345) (by norm_num)
theorem B1653749 : Blo 203807 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B310277 : Blo 203807 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B310301 : Blo 203807 310301 := bbase (se 3 (by rfl) ⟨58181, by rfl⟩ : syracuseStep 310301 = 116363) (by norm_num)
theorem B310325 : Blo 203807 310325 := bbase (se 5 (by rfl) ⟨14546, by rfl⟩ : syracuseStep 310325 = 29093) (by norm_num)
theorem B310349 : Blo 203807 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B310373 : Blo 203807 310373 := bbase (se 4 (by rfl) ⟨29097, by rfl⟩ : syracuseStep 310373 = 58195) (by norm_num)
theorem B310397 : Blo 203807 310397 := bbase (se 3 (by rfl) ⟨58199, by rfl⟩ : syracuseStep 310397 = 116399) (by norm_num)
theorem B244885 : Blo 203807 244885 := bbase (se 6 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 244885 = 11479) (by norm_num)
theorem B310421 : Blo 203807 310421 := bbase (se 6 (by rfl) ⟨7275, by rfl⟩ : syracuseStep 310421 = 14551) (by norm_num)
theorem B441517 : Blo 203807 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B310445 : Blo 203807 310445 := bbase (se 3 (by rfl) ⟨58208, by rfl⟩ : syracuseStep 310445 = 116417) (by norm_num)
theorem B310469 : Blo 203807 310469 := bbase (se 4 (by rfl) ⟨29106, by rfl⟩ : syracuseStep 310469 = 58213) (by norm_num)
theorem B310493 : Blo 203807 310493 := bbase (se 3 (by rfl) ⟨58217, by rfl⟩ : syracuseStep 310493 = 116435) (by norm_num)
theorem B310517 : Blo 203807 310517 := bbase (se 5 (by rfl) ⟨14555, by rfl⟩ : syracuseStep 310517 = 29111) (by norm_num)
theorem B310541 : Blo 203807 310541 := bbase (se 3 (by rfl) ⟨58226, by rfl⟩ : syracuseStep 310541 = 116453) (by norm_num)
theorem B310565 : Blo 203807 310565 := bbase (se 4 (by rfl) ⟨29115, by rfl⟩ : syracuseStep 310565 = 58231) (by norm_num)
theorem B310589 : Blo 203807 310589 := bbase (se 3 (by rfl) ⟨58235, by rfl⟩ : syracuseStep 310589 = 116471) (by norm_num)
theorem B310613 : Blo 203807 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B310637 : Blo 203807 310637 := bbase (se 3 (by rfl) ⟨58244, by rfl⟩ : syracuseStep 310637 = 116489) (by norm_num)
theorem B310661 : Blo 203807 310661 := bbase (se 4 (by rfl) ⟨29124, by rfl⟩ : syracuseStep 310661 = 58249) (by norm_num)
theorem B245149 : Blo 203807 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B310685 : Blo 203807 310685 := bbase (se 3 (by rfl) ⟨58253, by rfl⟩ : syracuseStep 310685 = 116507) (by norm_num)
theorem B212401 : Blo 203807 212401 := bbase (se 2 (by rfl) ⟨79650, by rfl⟩ : syracuseStep 212401 = 159301) (by norm_num)
theorem B310709 : Blo 203807 310709 := bbase (se 5 (by rfl) ⟨14564, by rfl⟩ : syracuseStep 310709 = 29129) (by norm_num)
theorem B310733 : Blo 203807 310733 := bbase (se 3 (by rfl) ⟨58262, by rfl⟩ : syracuseStep 310733 = 116525) (by norm_num)
theorem B310757 : Blo 203807 310757 := bbase (se 4 (by rfl) ⟨29133, by rfl⟩ : syracuseStep 310757 = 58267) (by norm_num)
theorem B310781 : Blo 203807 310781 := bbase (se 3 (by rfl) ⟨58271, by rfl⟩ : syracuseStep 310781 = 116543) (by norm_num)
theorem B245269 : Blo 203807 245269 := bbase (se 6 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 245269 = 11497) (by norm_num)
theorem B441877 : Blo 203807 441877 := bbase (se 6 (by rfl) ⟨10356, by rfl⟩ : syracuseStep 441877 = 20713) (by norm_num)
theorem B310805 : Blo 203807 310805 := bbase (se 6 (by rfl) ⟨7284, by rfl⟩ : syracuseStep 310805 = 14569) (by norm_num)
theorem B310829 : Blo 203807 310829 := bbase (se 3 (by rfl) ⟨58280, by rfl⟩ : syracuseStep 310829 = 116561) (by norm_num)
theorem B310853 : Blo 203807 310853 := bbase (se 4 (by rfl) ⟨29142, by rfl⟩ : syracuseStep 310853 = 58285) (by norm_num)
theorem B310877 : Blo 203807 310877 := bbase (se 3 (by rfl) ⟨58289, by rfl⟩ : syracuseStep 310877 = 116579) (by norm_num)
theorem B310901 : Blo 203807 310901 := bbase (se 5 (by rfl) ⟨14573, by rfl⟩ : syracuseStep 310901 = 29147) (by norm_num)
theorem B310925 : Blo 203807 310925 := bbase (se 3 (by rfl) ⟨58298, by rfl⟩ : syracuseStep 310925 = 116597) (by norm_num)
theorem B310949 : Blo 203807 310949 := bbase (se 4 (by rfl) ⟨29151, by rfl⟩ : syracuseStep 310949 = 58303) (by norm_num)
theorem B310973 : Blo 203807 310973 := bbase (se 3 (by rfl) ⟨58307, by rfl⟩ : syracuseStep 310973 = 116615) (by norm_num)
theorem B310997 : Blo 203807 310997 := bbase (se 7 (by rfl) ⟨3644, by rfl⟩ : syracuseStep 310997 = 7289) (by norm_num)
theorem B311021 : Blo 203807 311021 := bbase (se 3 (by rfl) ⟨58316, by rfl⟩ : syracuseStep 311021 = 116633) (by norm_num)
theorem B311045 : Blo 203807 311045 := bbase (se 4 (by rfl) ⟨29160, by rfl⟩ : syracuseStep 311045 = 58321) (by norm_num)
theorem B311069 : Blo 203807 311069 := bbase (se 3 (by rfl) ⟨58325, by rfl⟩ : syracuseStep 311069 = 116651) (by norm_num)
theorem B311093 : Blo 203807 311093 := bbase (se 5 (by rfl) ⟨14582, by rfl⟩ : syracuseStep 311093 = 29165) (by norm_num)
theorem B311117 : Blo 203807 311117 := bbase (se 3 (by rfl) ⟨58334, by rfl⟩ : syracuseStep 311117 = 116669) (by norm_num)
theorem B311141 : Blo 203807 311141 := bbase (se 4 (by rfl) ⟨29169, by rfl⟩ : syracuseStep 311141 = 58339) (by norm_num)
theorem B311165 : Blo 203807 311165 := bbase (se 3 (by rfl) ⟨58343, by rfl⟩ : syracuseStep 311165 = 116687) (by norm_num)
theorem B442253 : Blo 203807 442253 := bbase (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) (by norm_num)
theorem B2703253 : Blo 203807 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B311189 : Blo 203807 311189 := bbase (se 6 (by rfl) ⟨7293, by rfl⟩ : syracuseStep 311189 = 14587) (by norm_num)
theorem B343973 : Blo 203807 343973 := bbase (se 4 (by rfl) ⟨32247, by rfl⟩ : syracuseStep 343973 = 64495) (by norm_num)
theorem B1032101 : Blo 203807 1032101 := bbase (se 4 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 1032101 = 193519) (by norm_num)
theorem B311213 : Blo 203807 311213 := bbase (se 3 (by rfl) ⟨58352, by rfl⟩ : syracuseStep 311213 = 116705) (by norm_num)
theorem B311237 : Blo 203807 311237 := bbase (se 4 (by rfl) ⟨29178, by rfl⟩ : syracuseStep 311237 = 58357) (by norm_num)
theorem B311261 : Blo 203807 311261 := bbase (se 3 (by rfl) ⟨58361, by rfl⟩ : syracuseStep 311261 = 116723) (by norm_num)
theorem B212977 : Blo 203807 212977 := bbase (se 2 (by rfl) ⟨79866, by rfl⟩ : syracuseStep 212977 = 159733) (by norm_num)
theorem B311285 : Blo 203807 311285 := bbase (se 5 (by rfl) ⟨14591, by rfl⟩ : syracuseStep 311285 = 29183) (by norm_num)
theorem B311309 : Blo 203807 311309 := bbase (se 3 (by rfl) ⟨58370, by rfl⟩ : syracuseStep 311309 = 116741) (by norm_num)
theorem B344101 : Blo 203807 344101 := bbase (se 4 (by rfl) ⟨32259, by rfl⟩ : syracuseStep 344101 = 64519) (by norm_num)
theorem B311333 : Blo 203807 311333 := bbase (se 4 (by rfl) ⟨29187, by rfl⟩ : syracuseStep 311333 = 58375) (by norm_num)
theorem B311357 : Blo 203807 311357 := bbase (se 3 (by rfl) ⟨58379, by rfl⟩ : syracuseStep 311357 = 116759) (by norm_num)
theorem B311381 : Blo 203807 311381 := bbase (se 8 (by rfl) ⟨1824, by rfl⟩ : syracuseStep 311381 = 3649) (by norm_num)
theorem B311405 : Blo 203807 311405 := bbase (se 3 (by rfl) ⟨58388, by rfl⟩ : syracuseStep 311405 = 116777) (by norm_num)
theorem B344189 : Blo 203807 344189 := bbase (se 3 (by rfl) ⟨64535, by rfl⟩ : syracuseStep 344189 = 129071) (by norm_num)
theorem B311429 : Blo 203807 311429 := bbase (se 4 (by rfl) ⟨29196, by rfl⟩ : syracuseStep 311429 = 58393) (by norm_num)
theorem B311453 : Blo 203807 311453 := bbase (se 3 (by rfl) ⟨58397, by rfl⟩ : syracuseStep 311453 = 116795) (by norm_num)
theorem B311477 : Blo 203807 311477 := bbase (se 5 (by rfl) ⟨14600, by rfl⟩ : syracuseStep 311477 = 29201) (by norm_num)
theorem B311501 : Blo 203807 311501 := bbase (se 3 (by rfl) ⟨58406, by rfl⟩ : syracuseStep 311501 = 116813) (by norm_num)
theorem B442597 : Blo 203807 442597 := bbase (se 4 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 442597 = 82987) (by norm_num)
theorem B311525 : Blo 203807 311525 := bbase (se 4 (by rfl) ⟨29205, by rfl⟩ : syracuseStep 311525 = 58411) (by norm_num)
theorem B737525 : Blo 203807 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B835829 : Blo 203807 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B344317 : Blo 203807 344317 := bbase (se 3 (by rfl) ⟨64559, by rfl⟩ : syracuseStep 344317 = 129119) (by norm_num)
theorem B311549 : Blo 203807 311549 := bbase (se 3 (by rfl) ⟨58415, by rfl⟩ : syracuseStep 311549 = 116831) (by norm_num)
theorem B311573 : Blo 203807 311573 := bbase (se 6 (by rfl) ⟨7302, by rfl⟩ : syracuseStep 311573 = 14605) (by norm_num)
theorem B311597 : Blo 203807 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B311621 : Blo 203807 311621 := bbase (se 4 (by rfl) ⟨29214, by rfl⟩ : syracuseStep 311621 = 58429) (by norm_num)
theorem B344405 : Blo 203807 344405 := bbase (se 10 (by rfl) ⟨504, by rfl⟩ : syracuseStep 344405 = 1009) (by norm_num)
theorem B311645 : Blo 203807 311645 := bbase (se 3 (by rfl) ⟨58433, by rfl⟩ : syracuseStep 311645 = 116867) (by norm_num)
theorem B246125 : Blo 203807 246125 := bbase (se 3 (by rfl) ⟨46148, by rfl⟩ : syracuseStep 246125 = 92297) (by norm_num)
theorem B311669 : Blo 203807 311669 := bbase (se 5 (by rfl) ⟨14609, by rfl⟩ : syracuseStep 311669 = 29219) (by norm_num)
theorem B311693 : Blo 203807 311693 := bbase (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) (by norm_num)
theorem B704933 : Blo 203807 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B344533 : Blo 203807 344533 := bbase (se 7 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 344533 = 8075) (by norm_num)
theorem B344621 : Blo 203807 344621 := bbase (se 3 (by rfl) ⟨64616, by rfl⟩ : syracuseStep 344621 = 129233) (by norm_num)
theorem B344749 : Blo 203807 344749 := bbase (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) (by norm_num)
theorem B344837 : Blo 203807 344837 := bbase (se 4 (by rfl) ⟨32328, by rfl⟩ : syracuseStep 344837 = 64657) (by norm_num)
theorem B1491797 : Blo 203807 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B344965 : Blo 203807 344965 := bbase (se 4 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 344965 = 64681) (by norm_num)
theorem B738229 : Blo 203807 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B1262549 : Blo 203807 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B345053 : Blo 203807 345053 := bbase (se 3 (by rfl) ⟨64697, by rfl⟩ : syracuseStep 345053 = 129395) (by norm_num)
theorem B312365 : Blo 203807 312365 := bbase (se 3 (by rfl) ⟨58568, by rfl⟩ : syracuseStep 312365 = 117137) (by norm_num)
theorem B246845 : Blo 203807 246845 := bbase (se 3 (by rfl) ⟨46283, by rfl⟩ : syracuseStep 246845 = 92567) (by norm_num)
theorem B345181 : Blo 203807 345181 := bbase (se 3 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 345181 = 129443) (by norm_num)
theorem B1033397 : Blo 203807 1033397 := bbase (se 5 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 1033397 = 96881) (by norm_num)
theorem B279733 : Blo 203807 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B345269 : Blo 203807 345269 := bbase (se 5 (by rfl) ⟨16184, by rfl⟩ : syracuseStep 345269 = 32369) (by norm_num)
theorem B345397 : Blo 203807 345397 := bbase (se 5 (by rfl) ⟨16190, by rfl⟩ : syracuseStep 345397 = 32381) (by norm_num)
theorem B247153 : Blo 203807 247153 := bbase (se 2 (by rfl) ⟨92682, by rfl⟩ : syracuseStep 247153 = 185365) (by norm_num)
theorem B1328501 : Blo 203807 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B345485 : Blo 203807 345485 := bbase (se 3 (by rfl) ⟨64778, by rfl⟩ : syracuseStep 345485 = 129557) (by norm_num)
theorem B837029 : Blo 203807 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B247249 : Blo 203807 247249 := bbase (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) (by norm_num)
theorem B345613 : Blo 203807 345613 := bbase (se 3 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 345613 = 129605) (by norm_num)
theorem B247393 : Blo 203807 247393 := bbase (se 2 (by rfl) ⟨92772, by rfl⟩ : syracuseStep 247393 = 185545) (by norm_num)
theorem B345701 : Blo 203807 345701 := bbase (se 4 (by rfl) ⟨32409, by rfl⟩ : syracuseStep 345701 = 64819) (by norm_num)
theorem B280189 : Blo 203807 280189 := bbase (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) (by norm_num)
theorem B2639573 : Blo 203807 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B345829 : Blo 203807 345829 := bbase (se 4 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 345829 = 64843) (by norm_num)
theorem B345917 : Blo 203807 345917 := bbase (se 3 (by rfl) ⟨64859, by rfl⟩ : syracuseStep 345917 = 129719) (by norm_num)
theorem B280469 : Blo 203807 280469 := bbase (se 6 (by rfl) ⟨6573, by rfl⟩ : syracuseStep 280469 = 13147) (by norm_num)
theorem B346045 : Blo 203807 346045 := bbase (se 3 (by rfl) ⟨64883, by rfl⟩ : syracuseStep 346045 = 129767) (by norm_num)
theorem B1886165 : Blo 203807 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B346133 : Blo 203807 346133 := bbase (se 6 (by rfl) ⟨8112, by rfl⟩ : syracuseStep 346133 = 16225) (by norm_num)
theorem B313381 : Blo 203807 313381 := bbase (se 4 (by rfl) ⟨29379, by rfl⟩ : syracuseStep 313381 = 58759) (by norm_num)
theorem B346261 : Blo 203807 346261 := bbase (se 6 (by rfl) ⟨8115, by rfl⟩ : syracuseStep 346261 = 16231) (by norm_num)
theorem B1230997 : Blo 203807 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B346349 : Blo 203807 346349 := bbase (se 3 (by rfl) ⟨64940, by rfl⟩ : syracuseStep 346349 = 129881) (by norm_num)
theorem B346477 : Blo 203807 346477 := bbase (se 3 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 346477 = 129929) (by norm_num)
theorem B870821 : Blo 203807 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B1034693 : Blo 203807 1034693 := bbase (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) (by norm_num)
theorem B346565 : Blo 203807 346565 := bbase (se 4 (by rfl) ⟨32490, by rfl⟩ : syracuseStep 346565 = 64981) (by norm_num)
theorem B346693 : Blo 203807 346693 := bbase (se 4 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 346693 = 65005) (by norm_num)
theorem B248393 : Blo 203807 248393 := bbase (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) (by norm_num)
theorem B346781 : Blo 203807 346781 := bbase (se 3 (by rfl) ⟨65021, by rfl⟩ : syracuseStep 346781 = 130043) (by norm_num)
theorem B314093 : Blo 203807 314093 := bbase (se 3 (by rfl) ⟨58892, by rfl⟩ : syracuseStep 314093 = 117785) (by norm_num)
theorem B346909 : Blo 203807 346909 := bbase (se 3 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 346909 = 130091) (by norm_num)
theorem B346997 : Blo 203807 346997 := bbase (se 5 (by rfl) ⟨16265, by rfl⟩ : syracuseStep 346997 = 32531) (by norm_num)
theorem B576437 : Blo 203807 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B347125 : Blo 203807 347125 := bbase (se 5 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 347125 = 32543) (by norm_num)
theorem B1559573 : Blo 203807 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B347213 : Blo 203807 347213 := bbase (se 3 (by rfl) ⟨65102, by rfl⟩ : syracuseStep 347213 = 130205) (by norm_num)
theorem B314501 : Blo 203807 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B347341 : Blo 203807 347341 := bbase (se 3 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 347341 = 130253) (by norm_num)
theorem B1002725 : Blo 203807 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B249085 : Blo 203807 249085 := bbase (se 3 (by rfl) ⟨46703, by rfl⟩ : syracuseStep 249085 = 93407) (by norm_num)
theorem B281885 : Blo 203807 281885 := bbase (se 3 (by rfl) ⟨52853, by rfl⟩ : syracuseStep 281885 = 105707) (by norm_num)
theorem B347429 : Blo 203807 347429 := bbase (se 4 (by rfl) ⟨32571, by rfl⟩ : syracuseStep 347429 = 65143) (by norm_num)
theorem B314749 : Blo 203807 314749 := bbase (se 3 (by rfl) ⟨59015, by rfl⟩ : syracuseStep 314749 = 118031) (by norm_num)
theorem B871829 : Blo 203807 871829 := bbase (se 6 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 871829 = 40867) (by norm_num)
theorem B347557 : Blo 203807 347557 := bbase (se 4 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 347557 = 65167) (by norm_num)
theorem B249301 : Blo 203807 249301 := bbase (se 7 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 249301 = 5843) (by norm_num)
theorem B347645 : Blo 203807 347645 := bbase (se 3 (by rfl) ⟨65183, by rfl⟩ : syracuseStep 347645 = 130367) (by norm_num)
theorem B347773 : Blo 203807 347773 := bbase (se 3 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 347773 = 130415) (by norm_num)
theorem B1035989 : Blo 203807 1035989 := bbase (se 7 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 1035989 = 24281) (by norm_num)
theorem B347861 : Blo 203807 347861 := bbase (se 7 (by rfl) ⟨4076, by rfl⟩ : syracuseStep 347861 = 8153) (by norm_num)
theorem B315133 : Blo 203807 315133 := bbase (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) (by norm_num)
theorem B347989 : Blo 203807 347989 := bbase (se 9 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 347989 = 2039) (by norm_num)
theorem B5820245 : Blo 203807 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B348077 : Blo 203807 348077 := bbase (se 3 (by rfl) ⟨65264, by rfl⟩ : syracuseStep 348077 = 130529) (by norm_num)
theorem B937973 : Blo 203807 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B348205 : Blo 203807 348205 := bbase (se 3 (by rfl) ⟨65288, by rfl⟩ : syracuseStep 348205 = 130577) (by norm_num)
theorem B348293 : Blo 203807 348293 := bbase (se 4 (by rfl) ⟨32652, by rfl⟩ : syracuseStep 348293 = 65305) (by norm_num)
theorem B413957 : Blo 203807 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B348421 : Blo 203807 348421 := bbase (se 4 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 348421 = 65329) (by norm_num)
theorem B348509 : Blo 203807 348509 := bbase (se 3 (by rfl) ⟨65345, by rfl⟩ : syracuseStep 348509 = 130691) (by norm_num)
theorem B348637 : Blo 203807 348637 := bbase (se 3 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 348637 = 130739) (by norm_num)
theorem B283133 : Blo 203807 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B348725 : Blo 203807 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B774805 : Blo 203807 774805 := bbase (se 6 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 774805 = 36319) (by norm_num)
theorem B348853 : Blo 203807 348853 := bbase (se 5 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 348853 = 32705) (by norm_num)
theorem B217829 : Blo 203807 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B348941 : Blo 203807 348941 := bbase (se 3 (by rfl) ⟨65426, by rfl⟩ : syracuseStep 348941 = 130853) (by norm_num)
theorem B349069 : Blo 203807 349069 := bbase (se 3 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 349069 = 130901) (by norm_num)
theorem B775109 : Blo 203807 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B1037285 : Blo 203807 1037285 := bbase (se 4 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 1037285 = 194491) (by norm_num)
theorem B349157 : Blo 203807 349157 := bbase (se 4 (by rfl) ⟨32733, by rfl⟩ : syracuseStep 349157 = 65467) (by norm_num)
theorem B349181 : Blo 203807 349181 := bbase (se 3 (by rfl) ⟨65471, by rfl⟩ : syracuseStep 349181 = 130943) (by norm_num)
theorem B349285 : Blo 203807 349285 := bbase (se 4 (by rfl) ⟨32745, by rfl⟩ : syracuseStep 349285 = 65491) (by norm_num)
theorem B873605 : Blo 203807 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B218273 : Blo 203807 218273 := bbase (se 2 (by rfl) ⟨81852, by rfl⟩ : syracuseStep 218273 = 163705) (by norm_num)
theorem B349373 : Blo 203807 349373 := bbase (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) (by norm_num)
theorem B709829 : Blo 203807 709829 := bbase (se 4 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 709829 = 133093) (by norm_num)
theorem B218333 : Blo 203807 218333 := bbase (se 3 (by rfl) ⟨40937, by rfl⟩ : syracuseStep 218333 = 81875) (by norm_num)
theorem B349501 : Blo 203807 349501 := bbase (se 3 (by rfl) ⟨65531, by rfl⟩ : syracuseStep 349501 = 131063) (by norm_num)
theorem B218461 : Blo 203807 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B349589 : Blo 203807 349589 := bbase (se 6 (by rfl) ⟨8193, by rfl⟩ : syracuseStep 349589 = 16387) (by norm_num)
theorem B284077 : Blo 203807 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B1496501 : Blo 203807 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B349717 : Blo 203807 349717 := bbase (se 6 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 349717 = 16393) (by norm_num)
theorem B349805 : Blo 203807 349805 := bbase (se 3 (by rfl) ⟨65588, by rfl⟩ : syracuseStep 349805 = 131177) (by norm_num)
theorem B349933 : Blo 203807 349933 := bbase (se 3 (by rfl) ⟨65612, by rfl⟩ : syracuseStep 349933 = 131225) (by norm_num)
theorem B218905 : Blo 203807 218905 := bbase (se 2 (by rfl) ⟨82089, by rfl⟩ : syracuseStep 218905 = 164179) (by norm_num)
theorem B350021 : Blo 203807 350021 := bbase (se 4 (by rfl) ⟨32814, by rfl⟩ : syracuseStep 350021 = 65629) (by norm_num)
theorem B219025 : Blo 203807 219025 := bbase (se 2 (by rfl) ⟨82134, by rfl⟩ : syracuseStep 219025 = 164269) (by norm_num)
theorem B939941 : Blo 203807 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B350149 : Blo 203807 350149 := bbase (se 4 (by rfl) ⟨32826, by rfl⟩ : syracuseStep 350149 = 65653) (by norm_num)
theorem B350237 : Blo 203807 350237 := bbase (se 3 (by rfl) ⟨65669, by rfl⟩ : syracuseStep 350237 = 131339) (by norm_num)
theorem B219277 : Blo 203807 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B219281 : Blo 203807 219281 := bbase (se 2 (by rfl) ⟨82230, by rfl⟩ : syracuseStep 219281 = 164461) (by norm_num)
theorem B350365 : Blo 203807 350365 := bbase (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) (by norm_num)
theorem B1038581 : Blo 203807 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B350453 : Blo 203807 350453 := bbase (se 5 (by rfl) ⟨16427, by rfl⟩ : syracuseStep 350453 = 32855) (by norm_num)
theorem B350581 : Blo 203807 350581 := bbase (se 5 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 350581 = 32867) (by norm_num)
theorem B350669 : Blo 203807 350669 := bbase (se 3 (by rfl) ⟨65750, by rfl⟩ : syracuseStep 350669 = 131501) (by norm_num)
theorem B1169909 : Blo 203807 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B219845 : Blo 203807 219845 := bbase (se 4 (by rfl) ⟨20610, by rfl⟩ : syracuseStep 219845 = 41221) (by norm_num)
theorem B351029 : Blo 203807 351029 := bbase (se 5 (by rfl) ⟨16454, by rfl⟩ : syracuseStep 351029 = 32909) (by norm_num)
theorem B580421 : Blo 203807 580421 := bbase (se 4 (by rfl) ⟨54414, by rfl⟩ : syracuseStep 580421 = 108829) (by norm_num)
theorem B220033 : Blo 203807 220033 := bbase (se 2 (by rfl) ⟨82512, by rfl⟩ : syracuseStep 220033 = 165025) (by norm_num)
theorem B777221 : Blo 203807 777221 := bbase (se 4 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 777221 = 145729) (by norm_num)
theorem B777509 : Blo 203807 777509 := bbase (se 4 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 777509 = 145783) (by norm_num)
theorem B843061 : Blo 203807 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B351589 : Blo 203807 351589 := bbase (se 4 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 351589 = 65923) (by norm_num)
theorem B1039877 : Blo 203807 1039877 := bbase (se 4 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 1039877 = 194977) (by norm_num)
theorem B417413 : Blo 203807 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B2088629 : Blo 203807 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B220853 : Blo 203807 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B515909 : Blo 203807 515909 := bbase (se 4 (by rfl) ⟨48366, by rfl⟩ : syracuseStep 515909 = 96733) (by norm_num)
theorem B909413 : Blo 203807 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B221297 : Blo 203807 221297 := bbase (se 2 (by rfl) ⟨82986, by rfl⟩ : syracuseStep 221297 = 165973) (by norm_num)
theorem B516253 : Blo 203807 516253 := bbase (se 3 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 516253 = 193595) (by norm_num)
theorem B516365 : Blo 203807 516365 := bbase (se 3 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 516365 = 193637) (by norm_num)
theorem B221545 : Blo 203807 221545 := bbase (se 2 (by rfl) ⟨83079, by rfl⟩ : syracuseStep 221545 = 166159) (by norm_num)
theorem B582005 : Blo 203807 582005 := bbase (se 5 (by rfl) ⟨27281, by rfl⟩ : syracuseStep 582005 = 54563) (by norm_num)
theorem B778693 : Blo 203807 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B516557 : Blo 203807 516557 := bbase (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) (by norm_num)
theorem B746101 : Blo 203807 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B778997 : Blo 203807 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B1041173 : Blo 203807 1041173 := bbase (se 6 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 1041173 = 48805) (by norm_num)
theorem B516901 : Blo 203807 516901 := bbase (se 4 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 516901 = 96919) (by norm_num)
theorem B418621 : Blo 203807 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B517013 : Blo 203807 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B746405 : Blo 203807 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B582677 : Blo 203807 582677 := bbase (se 6 (by rfl) ⟨13656, by rfl⟩ : syracuseStep 582677 = 27313) (by norm_num)
theorem B517205 : Blo 203807 517205 := bbase (se 8 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 517205 = 6061) (by norm_num)
theorem B353381 : Blo 203807 353381 := bbase (se 4 (by rfl) ⟨33129, by rfl⟩ : syracuseStep 353381 = 66259) (by norm_num)
theorem B877877 : Blo 203807 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B517549 : Blo 203807 517549 := bbase (se 3 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 517549 = 194081) (by norm_num)
theorem B583109 : Blo 203807 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B517661 : Blo 203807 517661 := bbase (se 3 (by rfl) ⟨97061, by rfl⟩ : syracuseStep 517661 = 194123) (by norm_num)
theorem B222793 : Blo 203807 222793 := bbase (se 2 (by rfl) ⟨83547, by rfl⟩ : syracuseStep 222793 = 167095) (by norm_num)
theorem B517853 : Blo 203807 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B419813 : Blo 203807 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B1042469 : Blo 203807 1042469 := bbase (se 4 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 1042469 = 195463) (by norm_num)
theorem B518197 : Blo 203807 518197 := bbase (se 5 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 518197 = 48581) (by norm_num)
theorem B911477 : Blo 203807 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B944261 : Blo 203807 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B518309 : Blo 203807 518309 := bbase (se 4 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 518309 = 97183) (by norm_num)
theorem B583861 : Blo 203807 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B1009925 : Blo 203807 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B518501 : Blo 203807 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B387517 : Blo 203807 387517 := bbase (se 3 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 387517 = 145319) (by norm_num)
theorem B387661 : Blo 203807 387661 := bbase (se 3 (by rfl) ⟨72686, by rfl⟩ : syracuseStep 387661 = 145373) (by norm_num)
theorem B1567349 : Blo 203807 1567349 := bbase (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) (by norm_num)
theorem B518845 : Blo 203807 518845 := bbase (se 3 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 518845 = 194567) (by norm_num)
theorem B387821 : Blo 203807 387821 := bbase (se 3 (by rfl) ⟨72716, by rfl⟩ : syracuseStep 387821 = 145433) (by norm_num)
theorem B453413 : Blo 203807 453413 := bbase (se 4 (by rfl) ⟨42507, by rfl⟩ : syracuseStep 453413 = 85015) (by norm_num)
theorem B518957 : Blo 203807 518957 := bbase (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) (by norm_num)
theorem B781109 : Blo 203807 781109 := bbase (se 5 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 781109 = 73229) (by norm_num)
theorem B387965 : Blo 203807 387965 := bbase (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) (by norm_num)
theorem B519149 : Blo 203807 519149 := bbase (se 3 (by rfl) ⟨97340, by rfl⟩ : syracuseStep 519149 = 194681) (by norm_num)
theorem B879653 : Blo 203807 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B781397 : Blo 203807 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B388253 : Blo 203807 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B1305845 : Blo 203807 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B879893 : Blo 203807 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B421157 : Blo 203807 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B388405 : Blo 203807 388405 := bbase (se 5 (by rfl) ⟨18206, by rfl⟩ : syracuseStep 388405 = 36413) (by norm_num)
theorem B1043765 : Blo 203807 1043765 := bbase (se 5 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 1043765 = 97853) (by norm_num)
theorem B519493 : Blo 203807 519493 := bbase (se 4 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 519493 = 97405) (by norm_num)
theorem B519605 : Blo 203807 519605 := bbase (se 5 (by rfl) ⟨24356, by rfl⟩ : syracuseStep 519605 = 48713) (by norm_num)
theorem B290245 : Blo 203807 290245 := bbase (se 4 (by rfl) ⟨27210, by rfl⟩ : syracuseStep 290245 = 54421) (by norm_num)
theorem B421373 : Blo 203807 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B388709 : Blo 203807 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B519797 : Blo 203807 519797 := bbase (se 5 (by rfl) ⟨24365, by rfl⟩ : syracuseStep 519797 = 48731) (by norm_num)
theorem B290461 : Blo 203807 290461 := bbase (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) (by norm_num)
theorem B520141 : Blo 203807 520141 := bbase (se 3 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 520141 = 195053) (by norm_num)
theorem B258005 : Blo 203807 258005 := bbase (se 7 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 258005 = 6047) (by norm_num)
theorem B258061 : Blo 203807 258061 := bbase (se 3 (by rfl) ⟨48386, by rfl⟩ : syracuseStep 258061 = 96773) (by norm_num)
theorem B290837 : Blo 203807 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B520253 : Blo 203807 520253 := bbase (se 3 (by rfl) ⟨97547, by rfl⟩ : syracuseStep 520253 = 195095) (by norm_num)
theorem B258157 : Blo 203807 258157 := bbase (se 3 (by rfl) ⟨48404, by rfl⟩ : syracuseStep 258157 = 96809) (by norm_num)
theorem B782581 : Blo 203807 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B520445 : Blo 203807 520445 := bbase (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) (by norm_num)
theorem B258329 : Blo 203807 258329 := bbase (se 2 (by rfl) ⟨96873, by rfl⟩ : syracuseStep 258329 = 193747) (by norm_num)
theorem B258385 : Blo 203807 258385 := bbase (se 2 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 258385 = 193789) (by norm_num)
theorem B389461 : Blo 203807 389461 := bbase (se 10 (by rfl) ⟨570, by rfl⟩ : syracuseStep 389461 = 1141) (by norm_num)
theorem B258481 : Blo 203807 258481 := bbase (se 2 (by rfl) ⟨96930, by rfl⟩ : syracuseStep 258481 = 193861) (by norm_num)
theorem B389605 : Blo 203807 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B1667573 : Blo 203807 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B782885 : Blo 203807 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B1045061 : Blo 203807 1045061 := bbase (se 4 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 1045061 = 195949) (by norm_num)
theorem B520789 : Blo 203807 520789 := bbase (se 8 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 520789 = 6103) (by norm_num)
theorem B258653 : Blo 203807 258653 := bbase (se 3 (by rfl) ⟨48497, by rfl⟩ : syracuseStep 258653 = 96995) (by norm_num)
theorem B389765 : Blo 203807 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B258709 : Blo 203807 258709 := bbase (se 6 (by rfl) ⟨6063, by rfl⟩ : syracuseStep 258709 = 12127) (by norm_num)
theorem B848549 : Blo 203807 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B520901 : Blo 203807 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B488141 : Blo 203807 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B258805 : Blo 203807 258805 := bbase (se 5 (by rfl) ⟨12131, by rfl⟩ : syracuseStep 258805 = 24263) (by norm_num)
theorem B389909 : Blo 203807 389909 := bbase (se 6 (by rfl) ⟨9138, by rfl⟩ : syracuseStep 389909 = 18277) (by norm_num)
theorem B1995637 : Blo 203807 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B521093 : Blo 203807 521093 := bbase (se 4 (by rfl) ⟨48852, by rfl⟩ : syracuseStep 521093 = 97705) (by norm_num)
theorem B258977 : Blo 203807 258977 := bbase (se 2 (by rfl) ⟨97116, by rfl⟩ : syracuseStep 258977 = 194233) (by norm_num)
theorem B586709 : Blo 203807 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B259033 : Blo 203807 259033 := bbase (se 2 (by rfl) ⟨97137, by rfl⟩ : syracuseStep 259033 = 194275) (by norm_num)
theorem B390197 : Blo 203807 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B259129 : Blo 203807 259129 := bbase (se 2 (by rfl) ⟨97173, by rfl⟩ : syracuseStep 259129 = 194347) (by norm_num)
theorem B1766549 : Blo 203807 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B390349 : Blo 203807 390349 := bbase (se 3 (by rfl) ⟨73190, by rfl⟩ : syracuseStep 390349 = 146381) (by norm_num)
theorem B521437 : Blo 203807 521437 := bbase (se 3 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 521437 = 195539) (by norm_num)
theorem B259301 : Blo 203807 259301 := bbase (se 4 (by rfl) ⟨24309, by rfl⟩ : syracuseStep 259301 = 48619) (by norm_num)
theorem B259357 : Blo 203807 259357 := bbase (se 3 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 259357 = 97259) (by norm_num)
theorem B521549 : Blo 203807 521549 := bbase (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) (by norm_num)
theorem B259453 : Blo 203807 259453 := bbase (se 3 (by rfl) ⟨48647, by rfl⟩ : syracuseStep 259453 = 97295) (by norm_num)
theorem B292261 : Blo 203807 292261 := bbase (se 4 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 292261 = 54799) (by norm_num)
theorem B3503573 : Blo 203807 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B390653 : Blo 203807 390653 := bbase (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) (by norm_num)
theorem B882181 : Blo 203807 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B521741 : Blo 203807 521741 := bbase (se 3 (by rfl) ⟨97826, by rfl⟩ : syracuseStep 521741 = 195653) (by norm_num)
theorem B259625 : Blo 203807 259625 := bbase (se 2 (by rfl) ⟨97359, by rfl⟩ : syracuseStep 259625 = 194719) (by norm_num)
theorem B259681 : Blo 203807 259681 := bbase (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) (by norm_num)
theorem B259777 : Blo 203807 259777 := bbase (se 2 (by rfl) ⟨97416, by rfl⟩ : syracuseStep 259777 = 194833) (by norm_num)
theorem B980693 : Blo 203807 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B1046357 : Blo 203807 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B522085 : Blo 203807 522085 := bbase (se 4 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 522085 = 97891) (by norm_num)
theorem B259949 : Blo 203807 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B260005 : Blo 203807 260005 := bbase (se 4 (by rfl) ⟨24375, by rfl⟩ : syracuseStep 260005 = 48751) (by norm_num)
theorem B522197 : Blo 203807 522197 := bbase (se 7 (by rfl) ⟨6119, by rfl⟩ : syracuseStep 522197 = 12239) (by norm_num)
theorem B292853 : Blo 203807 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B260101 : Blo 203807 260101 := bbase (se 4 (by rfl) ⟨24384, by rfl⟩ : syracuseStep 260101 = 48769) (by norm_num)
theorem B292933 : Blo 203807 292933 := bbase (se 4 (by rfl) ⟨27462, by rfl⟩ : syracuseStep 292933 = 54925) (by norm_num)
theorem B587893 : Blo 203807 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B522389 : Blo 203807 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B260273 : Blo 203807 260273 := bbase (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) (by norm_num)
theorem B293053 : Blo 203807 293053 := bbase (se 3 (by rfl) ⟨54947, by rfl⟩ : syracuseStep 293053 = 109895) (by norm_num)
theorem B260329 : Blo 203807 260329 := bbase (se 2 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 260329 = 195247) (by norm_num)
theorem B391405 : Blo 203807 391405 := bbase (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) (by norm_num)
theorem B588053 : Blo 203807 588053 := bbase (se 6 (by rfl) ⟨13782, by rfl⟩ : syracuseStep 588053 = 27565) (by norm_num)
theorem B293149 : Blo 203807 293149 := bbase (se 3 (by rfl) ⟨54965, by rfl⟩ : syracuseStep 293149 = 109931) (by norm_num)
theorem B260425 : Blo 203807 260425 := bbase (se 2 (by rfl) ⟨97659, by rfl⟩ : syracuseStep 260425 = 195319) (by norm_num)
theorem B1603925 : Blo 203807 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1177973 : Blo 203807 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B391549 : Blo 203807 391549 := bbase (se 3 (by rfl) ⟨73415, by rfl⟩ : syracuseStep 391549 = 146831) (by norm_num)
theorem B2521493 : Blo 203807 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B522733 : Blo 203807 522733 := bbase (se 3 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 522733 = 196025) (by norm_num)
theorem B260597 : Blo 203807 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B588293 : Blo 203807 588293 := bbase (se 4 (by rfl) ⟨55152, by rfl⟩ : syracuseStep 588293 = 110305) (by norm_num)
theorem B653845 : Blo 203807 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B391709 : Blo 203807 391709 := bbase (se 3 (by rfl) ⟨73445, by rfl⟩ : syracuseStep 391709 = 146891) (by norm_num)
theorem B260653 : Blo 203807 260653 := bbase (se 3 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 260653 = 97745) (by norm_num)
theorem B522845 : Blo 203807 522845 := bbase (se 3 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 522845 = 196067) (by norm_num)
theorem B784997 : Blo 203807 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B555653 : Blo 203807 555653 := bbase (se 4 (by rfl) ⟨52092, by rfl⟩ : syracuseStep 555653 = 104185) (by norm_num)
theorem B260749 : Blo 203807 260749 := bbase (se 3 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 260749 = 97781) (by norm_num)
theorem B391853 : Blo 203807 391853 := bbase (se 3 (by rfl) ⟨73472, by rfl⟩ : syracuseStep 391853 = 146945) (by norm_num)
theorem B588485 : Blo 203807 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B293645 : Blo 203807 293645 := bbase (se 3 (by rfl) ⟨55058, by rfl⟩ : syracuseStep 293645 = 110117) (by norm_num)
theorem B523037 : Blo 203807 523037 := bbase (se 3 (by rfl) ⟨98069, by rfl⟩ : syracuseStep 523037 = 196139) (by norm_num)
theorem B260921 : Blo 203807 260921 := bbase (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) (by norm_num)
theorem B981845 : Blo 203807 981845 := bbase (se 9 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 981845 = 5753) (by norm_num)
theorem B260977 : Blo 203807 260977 := bbase (se 2 (by rfl) ⟨97866, by rfl⟩ : syracuseStep 260977 = 195733) (by norm_num)
theorem B785285 : Blo 203807 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B392141 : Blo 203807 392141 := bbase (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) (by norm_num)
theorem B261073 : Blo 203807 261073 := bbase (se 2 (by rfl) ⟨97902, by rfl⟩ : syracuseStep 261073 = 195805) (by norm_num)
theorem B883669 : Blo 203807 883669 := bbase (se 7 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 883669 = 20711) (by norm_num)
theorem B883685 : Blo 203807 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B392293 : Blo 203807 392293 := bbase (se 4 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 392293 = 73555) (by norm_num)
theorem B1047653 : Blo 203807 1047653 := bbase (se 4 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 1047653 = 196435) (by norm_num)
theorem B523381 : Blo 203807 523381 := bbase (se 5 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 523381 = 49067) (by norm_num)
theorem B261245 : Blo 203807 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B261301 : Blo 203807 261301 := bbase (se 5 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 261301 = 24497) (by norm_num)
theorem B523493 : Blo 203807 523493 := bbase (se 4 (by rfl) ⟨49077, by rfl⟩ : syracuseStep 523493 = 98155) (by norm_num)
theorem B261397 : Blo 203807 261397 := bbase (se 6 (by rfl) ⟨6126, by rfl⟩ : syracuseStep 261397 = 12253) (by norm_num)
theorem B294197 : Blo 203807 294197 := bbase (se 5 (by rfl) ⟨13790, by rfl⟩ : syracuseStep 294197 = 27581) (by norm_num)
theorem B392597 : Blo 203807 392597 := bbase (se 6 (by rfl) ⟨9201, by rfl⟩ : syracuseStep 392597 = 18403) (by norm_num)
theorem B523685 : Blo 203807 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B261569 : Blo 203807 261569 := bbase (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) (by norm_num)
theorem B261625 : Blo 203807 261625 := bbase (se 2 (by rfl) ⟨98109, by rfl⟩ : syracuseStep 261625 = 196219) (by norm_num)
theorem B1179157 : Blo 203807 1179157 := bbase (se 6 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 1179157 = 55273) (by norm_num)
theorem B982613 : Blo 203807 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B261721 : Blo 203807 261721 := bbase (se 2 (by rfl) ⟨98145, by rfl⟩ : syracuseStep 261721 = 196291) (by norm_num)
theorem B589477 : Blo 203807 589477 := bbase (se 4 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 589477 = 110527) (by norm_num)
theorem B491221 : Blo 203807 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B327397 : Blo 203807 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B524029 : Blo 203807 524029 := bbase (se 3 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 524029 = 196511) (by norm_num)
theorem B786181 : Blo 203807 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B261893 : Blo 203807 261893 := bbase (se 4 (by rfl) ⟨24552, by rfl⟩ : syracuseStep 261893 = 49105) (by norm_num)
theorem B261949 : Blo 203807 261949 := bbase (se 3 (by rfl) ⟨49115, by rfl⟩ : syracuseStep 261949 = 98231) (by norm_num)
theorem B524141 : Blo 203807 524141 := bbase (se 3 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 524141 = 196553) (by norm_num)
theorem B458621 : Blo 203807 458621 := bbase (se 3 (by rfl) ⟨85991, by rfl⟩ : syracuseStep 458621 = 171983) (by norm_num)
theorem B262045 : Blo 203807 262045 := bbase (se 3 (by rfl) ⟨49133, by rfl⟩ : syracuseStep 262045 = 98267) (by norm_num)
theorem B229297 : Blo 203807 229297 := bbase (se 2 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 229297 = 171973) (by norm_num)
theorem B491453 : Blo 203807 491453 := bbase (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) (by norm_num)
theorem B458693 : Blo 203807 458693 := bbase (se 4 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 458693 = 86005) (by norm_num)
theorem B229333 : Blo 203807 229333 := bbase (se 7 (by rfl) ⟨2687, by rfl⟩ : syracuseStep 229333 = 5375) (by norm_num)
theorem B557045 : Blo 203807 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B229369 : Blo 203807 229369 := bbase (se 2 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 229369 = 172027) (by norm_num)
theorem B1179683 : Blo 203807 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B458801 : Blo 203807 458801 := bstep (se 2 (by rfl) ⟨172050, by rfl⟩ : syracuseStep 458801 = 344101) B344101
theorem B1048625 : Blo 203807 1048625 := bstep (se 2 (by rfl) ⟨393234, by rfl⟩ : syracuseStep 1048625 = 786469) B786469
theorem B393265 : Blo 203807 393265 := bstep (se 2 (by rfl) ⟨147474, by rfl⟩ : syracuseStep 393265 = 294949) B294949
theorem B458819 : Blo 203807 458819 := bstep (se 1 (by rfl) ⟨344114, by rfl⟩ : syracuseStep 458819 = 688229) B688229
theorem B229459 : Blo 203807 229459 := bstep (se 1 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 229459 = 344189) B344189
theorem B491683 : Blo 203807 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B557219 : Blo 203807 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B524465 : Blo 203807 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B688337 : Blo 203807 688337 := bstep (se 2 (by rfl) ⟨258126, by rfl⟩ : syracuseStep 688337 = 516253) B516253
theorem B229603 : Blo 203807 229603 := bstep (se 1 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 229603 = 344405) B344405
theorem B524515 : Blo 203807 524515 := bstep (se 1 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 524515 = 786773) B786773
theorem B262435 : Blo 203807 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B590129 : Blo 203807 590129 := bstep (se 2 (by rfl) ⟨221298, by rfl⟩ : syracuseStep 590129 = 442597) B442597
theorem B459089 : Blo 203807 459089 := bstep (se 2 (by rfl) ⟨172158, by rfl⟩ : syracuseStep 459089 = 344317) B344317
theorem B459107 : Blo 203807 459107 := bstep (se 1 (by rfl) ⟨344330, by rfl⟩ : syracuseStep 459107 = 688661) B688661
theorem B524657 : Blo 203807 524657 := bstep (se 2 (by rfl) ⟨196746, by rfl⟩ : syracuseStep 524657 = 393493) B393493
theorem B229747 : Blo 203807 229747 := bstep (se 1 (by rfl) ⟨172310, by rfl⟩ : syracuseStep 229747 = 344621) B344621
theorem B262531 : Blo 203807 262531 := bstep (se 1 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 262531 = 393797) B393797
theorem B655793 : Blo 203807 655793 := bstep (se 2 (by rfl) ⟨245922, by rfl⟩ : syracuseStep 655793 = 491845) B491845
theorem B229891 : Blo 203807 229891 := bstep (se 1 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 229891 = 344837) B344837
theorem B885325 : Blo 203807 885325 := bstep (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) B331997
theorem B459377 : Blo 203807 459377 := bstep (se 2 (by rfl) ⟨172266, by rfl⟩ : syracuseStep 459377 = 344533) B344533
theorem B459395 : Blo 203807 459395 := bstep (se 1 (by rfl) ⟨344546, by rfl⟩ : syracuseStep 459395 = 689093) B689093
theorem B230035 : Blo 203807 230035 := bstep (se 1 (by rfl) ⟨172526, by rfl⟩ : syracuseStep 230035 = 345053) B345053
theorem B688877 : Blo 203807 688877 := bstep (se 3 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 688877 = 258329) B258329
theorem B688931 : Blo 203807 688931 := bstep (se 1 (by rfl) ⟨516698, by rfl⟩ : syracuseStep 688931 = 1033397) B1033397
theorem B230179 : Blo 203807 230179 := bstep (se 1 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 230179 = 345269) B345269
theorem B983843 : Blo 203807 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B590627 : Blo 203807 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B459665 : Blo 203807 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B459683 : Blo 203807 459683 := bstep (se 1 (by rfl) ⟨344762, by rfl⟩ : syracuseStep 459683 = 689525) B689525
theorem B885667 : Blo 203807 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B230323 : Blo 203807 230323 := bstep (se 1 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 230323 = 345485) B345485
theorem B328627 : Blo 203807 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B558019 : Blo 203807 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B656333 : Blo 203807 656333 := bstep (se 3 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 656333 = 246125) B246125
theorem B787427 : Blo 203807 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B787441 : Blo 203807 787441 := bstep (se 2 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 787441 = 590581) B590581
theorem B689201 : Blo 203807 689201 := bstep (se 2 (by rfl) ⟨258450, by rfl⟩ : syracuseStep 689201 = 516901) B516901
theorem B230467 : Blo 203807 230467 := bstep (se 1 (by rfl) ⟨172850, by rfl⟩ : syracuseStep 230467 = 345701) B345701
theorem B558161 : Blo 203807 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B394321 : Blo 203807 394321 := bstep (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) B295741
theorem B459953 : Blo 203807 459953 := bstep (se 2 (by rfl) ⟨172482, by rfl⟩ : syracuseStep 459953 = 344965) B344965
theorem B2360501 : Blo 203807 2360501 := bstep (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) B221297
theorem B459971 : Blo 203807 459971 := bstep (se 1 (by rfl) ⟨344978, by rfl⟩ : syracuseStep 459971 = 689957) B689957
theorem B230611 : Blo 203807 230611 := bstep (se 1 (by rfl) ⟨172958, by rfl⟩ : syracuseStep 230611 = 345917) B345917
theorem B984305 : Blo 203807 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B1672433 : Blo 203807 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B755021 : Blo 203807 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B525649 : Blo 203807 525649 := bstep (se 2 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 525649 = 394237) B394237
theorem B230755 : Blo 203807 230755 := bstep (se 1 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 230755 = 346133) B346133
theorem B460241 : Blo 203807 460241 := bstep (se 2 (by rfl) ⟨172590, by rfl⟩ : syracuseStep 460241 = 345181) B345181
theorem B460259 : Blo 203807 460259 := bstep (se 1 (by rfl) ⟨345194, by rfl⟩ : syracuseStep 460259 = 690389) B690389
theorem B394723 : Blo 203807 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B1050083 : Blo 203807 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B230899 : Blo 203807 230899 := bstep (se 1 (by rfl) ⟨173174, by rfl⟩ : syracuseStep 230899 = 346349) B346349
theorem B689741 : Blo 203807 689741 := bstep (se 3 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 689741 = 258653) B258653
theorem B525923 : Blo 203807 525923 := bstep (se 1 (by rfl) ⟨394442, by rfl⟩ : syracuseStep 525923 = 788885) B788885
theorem B689795 : Blo 203807 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B231043 : Blo 203807 231043 := bstep (se 1 (by rfl) ⟨173282, by rfl⟩ : syracuseStep 231043 = 346565) B346565
theorem B558733 : Blo 203807 558733 := bstep (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) B209525
theorem B460529 : Blo 203807 460529 := bstep (se 2 (by rfl) ⟨172698, by rfl⟩ : syracuseStep 460529 = 345397) B345397
theorem B460547 : Blo 203807 460547 := bstep (se 1 (by rfl) ⟨345410, by rfl⟩ : syracuseStep 460547 = 690821) B690821
theorem B231187 : Blo 203807 231187 := bstep (se 1 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 231187 = 346781) B346781
theorem B3573557 : Blo 203807 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B329537 : Blo 203807 329537 := bstep (se 2 (by rfl) ⟨123576, by rfl⟩ : syracuseStep 329537 = 247153) B247153
theorem B1181573 : Blo 203807 1181573 := bstep (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) B221545
theorem B690065 : Blo 203807 690065 := bstep (se 2 (by rfl) ⟨258774, by rfl⟩ : syracuseStep 690065 = 517549) B517549
theorem B231331 : Blo 203807 231331 := bstep (se 1 (by rfl) ⟨173498, by rfl⟩ : syracuseStep 231331 = 346997) B346997
theorem B329665 : Blo 203807 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B460817 : Blo 203807 460817 := bstep (se 2 (by rfl) ⟨172806, by rfl⟩ : syracuseStep 460817 = 345613) B345613
theorem B460835 : Blo 203807 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B231475 : Blo 203807 231475 := bstep (se 1 (by rfl) ⟨173606, by rfl⟩ : syracuseStep 231475 = 347213) B347213
theorem B985229 : Blo 203807 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B231619 : Blo 203807 231619 := bstep (se 1 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 231619 = 347429) B347429
theorem B1050893 : Blo 203807 1050893 := bstep (se 3 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 1050893 = 394085) B394085
theorem B461105 : Blo 203807 461105 := bstep (se 2 (by rfl) ⟨172914, by rfl⟩ : syracuseStep 461105 = 345829) B345829
theorem B461123 : Blo 203807 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B231763 : Blo 203807 231763 := bstep (se 1 (by rfl) ⟨173822, by rfl⟩ : syracuseStep 231763 = 347645) B347645
theorem B788899 : Blo 203807 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B690605 : Blo 203807 690605 := bstep (se 3 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 690605 = 258977) B258977
theorem B690659 : Blo 203807 690659 := bstep (se 1 (by rfl) ⟨517994, by rfl⟩ : syracuseStep 690659 = 1035989) B1035989
theorem B231907 : Blo 203807 231907 := bstep (se 1 (by rfl) ⟨173930, by rfl⟩ : syracuseStep 231907 = 347861) B347861
theorem B461393 : Blo 203807 461393 := bstep (se 2 (by rfl) ⟨173022, by rfl⟩ : syracuseStep 461393 = 346045) B346045
theorem B461411 : Blo 203807 461411 := bstep (se 1 (by rfl) ⟨346058, by rfl⟩ : syracuseStep 461411 = 692117) B692117
theorem B232051 : Blo 203807 232051 := bstep (se 1 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 232051 = 348077) B348077
theorem B625315 : Blo 203807 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B690929 : Blo 203807 690929 := bstep (se 2 (by rfl) ⟨259098, by rfl⟩ : syracuseStep 690929 = 518197) B518197
theorem B232195 : Blo 203807 232195 := bstep (se 1 (by rfl) ⟨174146, by rfl⟩ : syracuseStep 232195 = 348293) B348293
theorem B658253 : Blo 203807 658253 := bstep (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) B246845
theorem B461681 : Blo 203807 461681 := bstep (se 2 (by rfl) ⟨173130, by rfl⟩ : syracuseStep 461681 = 346261) B346261
theorem B1641329 : Blo 203807 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B461699 : Blo 203807 461699 := bstep (se 1 (by rfl) ⟨346274, by rfl⟩ : syracuseStep 461699 = 692549) B692549
theorem B232339 : Blo 203807 232339 := bstep (se 1 (by rfl) ⟨174254, by rfl⟩ : syracuseStep 232339 = 348509) B348509
theorem B330659 : Blo 203807 330659 := bstep (se 1 (by rfl) ⟨247994, by rfl⟩ : syracuseStep 330659 = 495989) B495989
theorem B232483 : Blo 203807 232483 := bstep (se 1 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 232483 = 348725) B348725
theorem B461969 : Blo 203807 461969 := bstep (se 2 (by rfl) ⟨173238, by rfl⟩ : syracuseStep 461969 = 346477) B346477
theorem B461987 : Blo 203807 461987 := bstep (se 1 (by rfl) ⟨346490, by rfl⟩ : syracuseStep 461987 = 692981) B692981
theorem B232627 : Blo 203807 232627 := bstep (se 1 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 232627 = 348941) B348941
theorem B1969379 : Blo 203807 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B265459 : Blo 203807 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B691469 : Blo 203807 691469 := bstep (se 3 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 691469 = 259301) B259301
theorem B691523 : Blo 203807 691523 := bstep (se 1 (by rfl) ⟨518642, by rfl⟩ : syracuseStep 691523 = 1037285) B1037285
theorem B232771 : Blo 203807 232771 := bstep (se 1 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 232771 = 349157) B349157
theorem B232787 : Blo 203807 232787 := bstep (se 1 (by rfl) ⟨174590, by rfl⟩ : syracuseStep 232787 = 349181) B349181
theorem B462257 : Blo 203807 462257 := bstep (se 2 (by rfl) ⟨173346, by rfl⟩ : syracuseStep 462257 = 346693) B346693
theorem B462275 : Blo 203807 462275 := bstep (se 1 (by rfl) ⟨346706, by rfl⟩ : syracuseStep 462275 = 693413) B693413
theorem B232915 : Blo 203807 232915 := bstep (se 1 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 232915 = 349373) B349373
theorem B691793 : Blo 203807 691793 := bstep (se 2 (by rfl) ⟨259422, by rfl⟩ : syracuseStep 691793 = 518845) B518845
theorem B233059 : Blo 203807 233059 := bstep (se 1 (by rfl) ⟨174794, by rfl⟩ : syracuseStep 233059 = 349589) B349589
theorem B462545 : Blo 203807 462545 := bstep (se 2 (by rfl) ⟨173454, by rfl⟩ : syracuseStep 462545 = 346909) B346909
theorem B462563 : Blo 203807 462563 := bstep (se 1 (by rfl) ⟨346922, by rfl⟩ : syracuseStep 462563 = 693845) B693845
theorem B233203 : Blo 203807 233203 := bstep (se 1 (by rfl) ⟨174902, by rfl⟩ : syracuseStep 233203 = 349805) B349805
theorem B233347 : Blo 203807 233347 := bstep (se 1 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 233347 = 350021) B350021
theorem B626627 : Blo 203807 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B462833 : Blo 203807 462833 := bstep (se 2 (by rfl) ⟨173562, by rfl⟩ : syracuseStep 462833 = 347125) B347125
theorem B462851 : Blo 203807 462851 := bstep (se 1 (by rfl) ⟨347138, by rfl⟩ : syracuseStep 462851 = 694277) B694277
theorem B233491 : Blo 203807 233491 := bstep (se 1 (by rfl) ⟨175118, by rfl⟩ : syracuseStep 233491 = 350237) B350237
theorem B561197 : Blo 203807 561197 := bstep (se 3 (by rfl) ⟨105224, by rfl⟩ : syracuseStep 561197 = 210449) B210449
theorem B692333 : Blo 203807 692333 := bstep (se 3 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 692333 = 259625) B259625
theorem B692387 : Blo 203807 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B233635 : Blo 203807 233635 := bstep (se 1 (by rfl) ⟨175226, by rfl⟩ : syracuseStep 233635 = 350453) B350453
theorem B463121 : Blo 203807 463121 := bstep (se 2 (by rfl) ⟨173670, by rfl⟩ : syracuseStep 463121 = 347341) B347341
theorem B463139 : Blo 203807 463139 := bstep (se 1 (by rfl) ⟨347354, by rfl⟩ : syracuseStep 463139 = 694709) B694709
theorem B233779 : Blo 203807 233779 := bstep (se 1 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 233779 = 350669) B350669
theorem B1773893 : Blo 203807 1773893 := bstep (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) B332605
theorem B332113 : Blo 203807 332113 := bstep (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) B249085
theorem B692657 : Blo 203807 692657 := bstep (se 2 (by rfl) ⟨259746, by rfl⟩ : syracuseStep 692657 = 519493) B519493
theorem B1315277 : Blo 203807 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B234019 : Blo 203807 234019 := bstep (se 1 (by rfl) ⟨175514, by rfl⟩ : syracuseStep 234019 = 351029) B351029
theorem B463409 : Blo 203807 463409 := bstep (se 2 (by rfl) ⟨173778, by rfl⟩ : syracuseStep 463409 = 347557) B347557
theorem B463427 : Blo 203807 463427 := bstep (se 1 (by rfl) ⟨347570, by rfl⟩ : syracuseStep 463427 = 695141) B695141
theorem B463697 : Blo 203807 463697 := bstep (se 2 (by rfl) ⟨173886, by rfl⟩ : syracuseStep 463697 = 347773) B347773
theorem B463715 : Blo 203807 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B398225 : Blo 203807 398225 := bstep (se 2 (by rfl) ⟨149334, by rfl⟩ : syracuseStep 398225 = 298669) B298669
theorem B693197 : Blo 203807 693197 := bstep (se 3 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 693197 = 259949) B259949
theorem B660433 : Blo 203807 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B693251 : Blo 203807 693251 := bstep (se 1 (by rfl) ⟨519938, by rfl⟩ : syracuseStep 693251 = 1039877) B1039877
theorem B463985 : Blo 203807 463985 := bstep (se 2 (by rfl) ⟨173994, by rfl⟩ : syracuseStep 463985 = 347989) B347989
theorem B660611 : Blo 203807 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B464003 : Blo 203807 464003 := bstep (se 1 (by rfl) ⟨348002, by rfl⟩ : syracuseStep 464003 = 696005) B696005
theorem B693521 : Blo 203807 693521 := bstep (se 2 (by rfl) ⟨260070, by rfl⟩ : syracuseStep 693521 = 520141) B520141
theorem B464273 : Blo 203807 464273 := bstep (se 2 (by rfl) ⟨174102, by rfl⟩ : syracuseStep 464273 = 348205) B348205
theorem B464291 : Blo 203807 464291 := bstep (se 1 (by rfl) ⟨348218, by rfl⟩ : syracuseStep 464291 = 696437) B696437
theorem B464561 : Blo 203807 464561 := bstep (se 2 (by rfl) ⟨174210, by rfl⟩ : syracuseStep 464561 = 348421) B348421
theorem B464579 : Blo 203807 464579 := bstep (se 1 (by rfl) ⟨348434, by rfl⟩ : syracuseStep 464579 = 696869) B696869
theorem B694061 : Blo 203807 694061 := bstep (se 3 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 694061 = 260273) B260273
theorem B694115 : Blo 203807 694115 := bstep (se 1 (by rfl) ⟨520586, by rfl⟩ : syracuseStep 694115 = 1041173) B1041173
theorem B497603 : Blo 203807 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B464849 : Blo 203807 464849 := bstep (se 2 (by rfl) ⟨174318, by rfl⟩ : syracuseStep 464849 = 348637) B348637
theorem B464867 : Blo 203807 464867 := bstep (se 1 (by rfl) ⟨348650, by rfl⟩ : syracuseStep 464867 = 697301) B697301
theorem B694385 : Blo 203807 694385 := bstep (se 2 (by rfl) ⟨260394, by rfl⟩ : syracuseStep 694385 = 520789) B520789
theorem B2398349 : Blo 203807 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B399587 : Blo 203807 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B465137 : Blo 203807 465137 := bstep (se 2 (by rfl) ⟨174426, by rfl⟩ : syracuseStep 465137 = 348853) B348853
theorem B465155 : Blo 203807 465155 := bstep (se 1 (by rfl) ⟨348866, by rfl⟩ : syracuseStep 465155 = 697733) B697733
theorem B2660849 : Blo 203807 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B465425 : Blo 203807 465425 := bstep (se 2 (by rfl) ⟨174534, by rfl⟩ : syracuseStep 465425 = 349069) B349069
theorem B465443 : Blo 203807 465443 := bstep (se 1 (by rfl) ⟨349082, by rfl⟩ : syracuseStep 465443 = 698165) B698165
theorem B629329 : Blo 203807 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B694925 : Blo 203807 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B694979 : Blo 203807 694979 := bstep (se 1 (by rfl) ⟨521234, by rfl⟩ : syracuseStep 694979 = 1042469) B1042469
theorem B629507 : Blo 203807 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B498449 : Blo 203807 498449 := bstep (se 2 (by rfl) ⟨186918, by rfl⟩ : syracuseStep 498449 = 373837) B373837
theorem B465713 : Blo 203807 465713 := bstep (se 2 (by rfl) ⟨174642, by rfl⟩ : syracuseStep 465713 = 349285) B349285
theorem B465731 : Blo 203807 465731 := bstep (se 1 (by rfl) ⟨349298, by rfl⟩ : syracuseStep 465731 = 698597) B698597
theorem B662381 : Blo 203807 662381 := bstep (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) B248393
theorem B3152837 : Blo 203807 3152837 := bstep (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) B591157
theorem B695249 : Blo 203807 695249 := bstep (se 2 (by rfl) ⟨260718, by rfl⟩ : syracuseStep 695249 = 521437) B521437
theorem B629741 : Blo 203807 629741 := bstep (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) B236153
theorem B203811 : Blo 203807 203811 := bstep (se 1 (by rfl) ⟨152858, by rfl⟩ : syracuseStep 203811 = 305717) B305717
theorem B203827 : Blo 203807 203827 := bstep (se 1 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 203827 = 305741) B305741
theorem B203843 : Blo 203807 203843 := bstep (se 1 (by rfl) ⟨152882, by rfl⟩ : syracuseStep 203843 = 305765) B305765
theorem B466001 : Blo 203807 466001 := bstep (se 2 (by rfl) ⟨174750, by rfl⟩ : syracuseStep 466001 = 349501) B349501
theorem B203859 : Blo 203807 203859 := bstep (se 1 (by rfl) ⟨152894, by rfl⟩ : syracuseStep 203859 = 305789) B305789
theorem B203875 : Blo 203807 203875 := bstep (se 1 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 203875 = 305813) B305813
theorem B466019 : Blo 203807 466019 := bstep (se 1 (by rfl) ⟨349514, by rfl⟩ : syracuseStep 466019 = 699029) B699029
theorem B203891 : Blo 203807 203891 := bstep (se 1 (by rfl) ⟨152918, by rfl⟩ : syracuseStep 203891 = 305837) B305837
theorem B203907 : Blo 203807 203907 := bstep (se 1 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 203907 = 305861) B305861
theorem B203923 : Blo 203807 203923 := bstep (se 1 (by rfl) ⟨152942, by rfl⟩ : syracuseStep 203923 = 305885) B305885
theorem B203939 : Blo 203807 203939 := bstep (se 1 (by rfl) ⟨152954, by rfl⟩ : syracuseStep 203939 = 305909) B305909
theorem B203955 : Blo 203807 203955 := bstep (se 1 (by rfl) ⟨152966, by rfl⟩ : syracuseStep 203955 = 305933) B305933
theorem B203971 : Blo 203807 203971 := bstep (se 1 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 203971 = 305957) B305957
theorem B302275 : Blo 203807 302275 := bstep (se 1 (by rfl) ⟨226706, by rfl⟩ : syracuseStep 302275 = 453413) B453413
theorem B203987 : Blo 203807 203987 := bstep (se 1 (by rfl) ⟨152990, by rfl⟩ : syracuseStep 203987 = 305981) B305981
theorem B204003 : Blo 203807 204003 := bstep (se 1 (by rfl) ⟨153002, by rfl⟩ : syracuseStep 204003 = 306005) B306005
theorem B204019 : Blo 203807 204019 := bstep (se 1 (by rfl) ⟨153014, by rfl⟩ : syracuseStep 204019 = 306029) B306029
theorem B204035 : Blo 203807 204035 := bstep (se 1 (by rfl) ⟨153026, by rfl⟩ : syracuseStep 204035 = 306053) B306053
theorem B204051 : Blo 203807 204051 := bstep (se 1 (by rfl) ⟨153038, by rfl⟩ : syracuseStep 204051 = 306077) B306077
theorem B204067 : Blo 203807 204067 := bstep (se 1 (by rfl) ⟨153050, by rfl⟩ : syracuseStep 204067 = 306101) B306101
theorem B204083 : Blo 203807 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B204099 : Blo 203807 204099 := bstep (se 1 (by rfl) ⟨153074, by rfl⟩ : syracuseStep 204099 = 306149) B306149
theorem B204115 : Blo 203807 204115 := bstep (se 1 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 204115 = 306173) B306173
theorem B204131 : Blo 203807 204131 := bstep (se 1 (by rfl) ⟨153098, by rfl⟩ : syracuseStep 204131 = 306197) B306197
theorem B466289 : Blo 203807 466289 := bstep (se 2 (by rfl) ⟨174858, by rfl⟩ : syracuseStep 466289 = 349717) B349717
theorem B204147 : Blo 203807 204147 := bstep (se 1 (by rfl) ⟨153110, by rfl⟩ : syracuseStep 204147 = 306221) B306221
theorem B204163 : Blo 203807 204163 := bstep (se 1 (by rfl) ⟨153122, by rfl⟩ : syracuseStep 204163 = 306245) B306245
theorem B466307 : Blo 203807 466307 := bstep (se 1 (by rfl) ⟨349730, by rfl⟩ : syracuseStep 466307 = 699461) B699461
theorem B204179 : Blo 203807 204179 := bstep (se 1 (by rfl) ⟨153134, by rfl⟩ : syracuseStep 204179 = 306269) B306269
theorem B204195 : Blo 203807 204195 := bstep (se 1 (by rfl) ⟨153146, by rfl⟩ : syracuseStep 204195 = 306293) B306293
theorem B204211 : Blo 203807 204211 := bstep (se 1 (by rfl) ⟨153158, by rfl⟩ : syracuseStep 204211 = 306317) B306317
theorem B204227 : Blo 203807 204227 := bstep (se 1 (by rfl) ⟨153170, by rfl⟩ : syracuseStep 204227 = 306341) B306341
theorem B204243 : Blo 203807 204243 := bstep (se 1 (by rfl) ⟨153182, by rfl⟩ : syracuseStep 204243 = 306365) B306365
theorem B204259 : Blo 203807 204259 := bstep (se 1 (by rfl) ⟨153194, by rfl⟩ : syracuseStep 204259 = 306389) B306389
theorem B695789 : Blo 203807 695789 := bstep (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) B260921
theorem B204275 : Blo 203807 204275 := bstep (se 1 (by rfl) ⟨153206, by rfl⟩ : syracuseStep 204275 = 306413) B306413
theorem B204291 : Blo 203807 204291 := bstep (se 1 (by rfl) ⟨153218, by rfl⟩ : syracuseStep 204291 = 306437) B306437
theorem B204307 : Blo 203807 204307 := bstep (se 1 (by rfl) ⟨153230, by rfl⟩ : syracuseStep 204307 = 306461) B306461
theorem B204323 : Blo 203807 204323 := bstep (se 1 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 204323 = 306485) B306485
theorem B695843 : Blo 203807 695843 := bstep (se 1 (by rfl) ⟨521882, by rfl⟩ : syracuseStep 695843 = 1043765) B1043765
theorem B204339 : Blo 203807 204339 := bstep (se 1 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 204339 = 306509) B306509
theorem B204355 : Blo 203807 204355 := bstep (se 1 (by rfl) ⟨153266, by rfl⟩ : syracuseStep 204355 = 306533) B306533
theorem B204371 : Blo 203807 204371 := bstep (se 1 (by rfl) ⟨153278, by rfl⟩ : syracuseStep 204371 = 306557) B306557
theorem B204387 : Blo 203807 204387 := bstep (se 1 (by rfl) ⟨153290, by rfl⟩ : syracuseStep 204387 = 306581) B306581
theorem B204403 : Blo 203807 204403 := bstep (se 1 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 204403 = 306605) B306605
theorem B204419 : Blo 203807 204419 := bstep (se 1 (by rfl) ⟨153314, by rfl⟩ : syracuseStep 204419 = 306629) B306629
theorem B466577 : Blo 203807 466577 := bstep (se 2 (by rfl) ⟨174966, by rfl⟩ : syracuseStep 466577 = 349933) B349933
theorem B204435 : Blo 203807 204435 := bstep (se 1 (by rfl) ⟨153326, by rfl⟩ : syracuseStep 204435 = 306653) B306653
theorem B204451 : Blo 203807 204451 := bstep (se 1 (by rfl) ⟨153338, by rfl⟩ : syracuseStep 204451 = 306677) B306677
theorem B466595 : Blo 203807 466595 := bstep (se 1 (by rfl) ⟨349946, by rfl⟩ : syracuseStep 466595 = 699893) B699893
theorem B204467 : Blo 203807 204467 := bstep (se 1 (by rfl) ⟨153350, by rfl⟩ : syracuseStep 204467 = 306701) B306701
theorem B204483 : Blo 203807 204483 := bstep (se 1 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 204483 = 306725) B306725
theorem B204499 : Blo 203807 204499 := bstep (se 1 (by rfl) ⟨153374, by rfl⟩ : syracuseStep 204499 = 306749) B306749
theorem B204515 : Blo 203807 204515 := bstep (se 1 (by rfl) ⟨153386, by rfl⟩ : syracuseStep 204515 = 306773) B306773
theorem B204531 : Blo 203807 204531 := bstep (se 1 (by rfl) ⟨153398, by rfl⟩ : syracuseStep 204531 = 306797) B306797
theorem B204547 : Blo 203807 204547 := bstep (se 1 (by rfl) ⟨153410, by rfl⟩ : syracuseStep 204547 = 306821) B306821
theorem B204563 : Blo 203807 204563 := bstep (se 1 (by rfl) ⟨153422, by rfl⟩ : syracuseStep 204563 = 306845) B306845
theorem B204579 : Blo 203807 204579 := bstep (se 1 (by rfl) ⟨153434, by rfl⟩ : syracuseStep 204579 = 306869) B306869
theorem B696113 : Blo 203807 696113 := bstep (se 2 (by rfl) ⟨261042, by rfl⟩ : syracuseStep 696113 = 522085) B522085
theorem B204595 : Blo 203807 204595 := bstep (se 1 (by rfl) ⟨153446, by rfl⟩ : syracuseStep 204595 = 306893) B306893
theorem B204611 : Blo 203807 204611 := bstep (se 1 (by rfl) ⟨153458, by rfl⟩ : syracuseStep 204611 = 306917) B306917
theorem B204627 : Blo 203807 204627 := bstep (se 1 (by rfl) ⟨153470, by rfl⟩ : syracuseStep 204627 = 306941) B306941
theorem B204643 : Blo 203807 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B3383153 : Blo 203807 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B204659 : Blo 203807 204659 := bstep (se 1 (by rfl) ⟨153494, by rfl⟩ : syracuseStep 204659 = 306989) B306989
theorem B204675 : Blo 203807 204675 := bstep (se 1 (by rfl) ⟨153506, by rfl⟩ : syracuseStep 204675 = 307013) B307013
theorem B204691 : Blo 203807 204691 := bstep (se 1 (by rfl) ⟨153518, by rfl⟩ : syracuseStep 204691 = 307037) B307037
theorem B204707 : Blo 203807 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B466865 : Blo 203807 466865 := bstep (se 2 (by rfl) ⟨175074, by rfl⟩ : syracuseStep 466865 = 350149) B350149
theorem B204723 : Blo 203807 204723 := bstep (se 1 (by rfl) ⟨153542, by rfl⟩ : syracuseStep 204723 = 307085) B307085
theorem B204739 : Blo 203807 204739 := bstep (se 1 (by rfl) ⟨153554, by rfl⟩ : syracuseStep 204739 = 307109) B307109
theorem B466883 : Blo 203807 466883 := bstep (se 1 (by rfl) ⟨350162, by rfl⟩ : syracuseStep 466883 = 700325) B700325
theorem B204755 : Blo 203807 204755 := bstep (se 1 (by rfl) ⟨153566, by rfl⟩ : syracuseStep 204755 = 307133) B307133
theorem B204771 : Blo 203807 204771 := bstep (se 1 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 204771 = 307157) B307157
theorem B204787 : Blo 203807 204787 := bstep (se 1 (by rfl) ⟨153590, by rfl⟩ : syracuseStep 204787 = 307181) B307181
theorem B204803 : Blo 203807 204803 := bstep (se 1 (by rfl) ⟨153602, by rfl⟩ : syracuseStep 204803 = 307205) B307205
theorem B204819 : Blo 203807 204819 := bstep (se 1 (by rfl) ⟨153614, by rfl⟩ : syracuseStep 204819 = 307229) B307229
theorem B204835 : Blo 203807 204835 := bstep (se 1 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 204835 = 307253) B307253
theorem B204851 : Blo 203807 204851 := bstep (se 1 (by rfl) ⟨153638, by rfl⟩ : syracuseStep 204851 = 307277) B307277
theorem B204867 : Blo 203807 204867 := bstep (se 1 (by rfl) ⟨153650, by rfl⟩ : syracuseStep 204867 = 307301) B307301
theorem B204883 : Blo 203807 204883 := bstep (se 1 (by rfl) ⟨153662, by rfl⟩ : syracuseStep 204883 = 307325) B307325
theorem B204899 : Blo 203807 204899 := bstep (se 1 (by rfl) ⟨153674, by rfl⟩ : syracuseStep 204899 = 307349) B307349
theorem B204915 : Blo 203807 204915 := bstep (se 1 (by rfl) ⟨153686, by rfl⟩ : syracuseStep 204915 = 307373) B307373
theorem B204931 : Blo 203807 204931 := bstep (se 1 (by rfl) ⟨153698, by rfl⟩ : syracuseStep 204931 = 307397) B307397
theorem B204947 : Blo 203807 204947 := bstep (se 1 (by rfl) ⟨153710, by rfl⟩ : syracuseStep 204947 = 307421) B307421
theorem B204963 : Blo 203807 204963 := bstep (se 1 (by rfl) ⟨153722, by rfl⟩ : syracuseStep 204963 = 307445) B307445
theorem B204979 : Blo 203807 204979 := bstep (se 1 (by rfl) ⟨153734, by rfl⟩ : syracuseStep 204979 = 307469) B307469
theorem B204995 : Blo 203807 204995 := bstep (se 1 (by rfl) ⟨153746, by rfl⟩ : syracuseStep 204995 = 307493) B307493
theorem B467153 : Blo 203807 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B205011 : Blo 203807 205011 := bstep (se 1 (by rfl) ⟨153758, by rfl⟩ : syracuseStep 205011 = 307517) B307517
theorem B205027 : Blo 203807 205027 := bstep (se 1 (by rfl) ⟨153770, by rfl⟩ : syracuseStep 205027 = 307541) B307541
theorem B467171 : Blo 203807 467171 := bstep (se 1 (by rfl) ⟨350378, by rfl⟩ : syracuseStep 467171 = 700757) B700757
theorem B205043 : Blo 203807 205043 := bstep (se 1 (by rfl) ⟨153782, by rfl⟩ : syracuseStep 205043 = 307565) B307565
theorem B205059 : Blo 203807 205059 := bstep (se 1 (by rfl) ⟨153794, by rfl⟩ : syracuseStep 205059 = 307589) B307589
theorem B205075 : Blo 203807 205075 := bstep (se 1 (by rfl) ⟨153806, by rfl⟩ : syracuseStep 205075 = 307613) B307613
theorem B205091 : Blo 203807 205091 := bstep (se 1 (by rfl) ⟨153818, by rfl⟩ : syracuseStep 205091 = 307637) B307637
theorem B205107 : Blo 203807 205107 := bstep (se 1 (by rfl) ⟨153830, by rfl⟩ : syracuseStep 205107 = 307661) B307661
theorem B205123 : Blo 203807 205123 := bstep (se 1 (by rfl) ⟨153842, by rfl⟩ : syracuseStep 205123 = 307685) B307685
theorem B696653 : Blo 203807 696653 := bstep (se 3 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 696653 = 261245) B261245
theorem B205139 : Blo 203807 205139 := bstep (se 1 (by rfl) ⟨153854, by rfl⟩ : syracuseStep 205139 = 307709) B307709
theorem B467299 : Blo 203807 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B205155 : Blo 203807 205155 := bstep (se 1 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 205155 = 307733) B307733
theorem B205171 : Blo 203807 205171 := bstep (se 1 (by rfl) ⟨153878, by rfl⟩ : syracuseStep 205171 = 307757) B307757
theorem B205187 : Blo 203807 205187 := bstep (se 1 (by rfl) ⟨153890, by rfl⟩ : syracuseStep 205187 = 307781) B307781
theorem B696707 : Blo 203807 696707 := bstep (se 1 (by rfl) ⟨522530, by rfl⟩ : syracuseStep 696707 = 1045061) B1045061
theorem B1188229 : Blo 203807 1188229 := bstep (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) B222793
theorem B205203 : Blo 203807 205203 := bstep (se 1 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 205203 = 307805) B307805
theorem B205219 : Blo 203807 205219 := bstep (se 1 (by rfl) ⟨153914, by rfl⟩ : syracuseStep 205219 = 307829) B307829
theorem B205235 : Blo 203807 205235 := bstep (se 1 (by rfl) ⟨153926, by rfl⟩ : syracuseStep 205235 = 307853) B307853
theorem B205251 : Blo 203807 205251 := bstep (se 1 (by rfl) ⟨153938, by rfl⟩ : syracuseStep 205251 = 307877) B307877
theorem B565699 : Blo 203807 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B1974725 : Blo 203807 1974725 := bstep (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) B370261
theorem B205267 : Blo 203807 205267 := bstep (se 1 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 205267 = 307901) B307901
theorem B205283 : Blo 203807 205283 := bstep (se 1 (by rfl) ⟨153962, by rfl⟩ : syracuseStep 205283 = 307925) B307925
theorem B467441 : Blo 203807 467441 := bstep (se 2 (by rfl) ⟨175290, by rfl⟩ : syracuseStep 467441 = 350581) B350581
theorem B205299 : Blo 203807 205299 := bstep (se 1 (by rfl) ⟨153974, by rfl⟩ : syracuseStep 205299 = 307949) B307949
theorem B664067 : Blo 203807 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B205315 : Blo 203807 205315 := bstep (se 1 (by rfl) ⟨153986, by rfl⟩ : syracuseStep 205315 = 307973) B307973
theorem B1319429 : Blo 203807 1319429 := bstep (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) B247393
theorem B467459 : Blo 203807 467459 := bstep (se 1 (by rfl) ⟨350594, by rfl⟩ : syracuseStep 467459 = 701189) B701189
theorem B205331 : Blo 203807 205331 := bstep (se 1 (by rfl) ⟨153998, by rfl⟩ : syracuseStep 205331 = 307997) B307997
theorem B205347 : Blo 203807 205347 := bstep (se 1 (by rfl) ⟨154010, by rfl⟩ : syracuseStep 205347 = 308021) B308021
theorem B205363 : Blo 203807 205363 := bstep (se 1 (by rfl) ⟨154022, by rfl⟩ : syracuseStep 205363 = 308045) B308045
theorem B205379 : Blo 203807 205379 := bstep (se 1 (by rfl) ⟨154034, by rfl⟩ : syracuseStep 205379 = 308069) B308069
theorem B205395 : Blo 203807 205395 := bstep (se 1 (by rfl) ⟨154046, by rfl⟩ : syracuseStep 205395 = 308093) B308093
theorem B205411 : Blo 203807 205411 := bstep (se 1 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 205411 = 308117) B308117
theorem B1253987 : Blo 203807 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B205427 : Blo 203807 205427 := bstep (se 1 (by rfl) ⟨154070, by rfl⟩ : syracuseStep 205427 = 308141) B308141
theorem B205443 : Blo 203807 205443 := bstep (se 1 (by rfl) ⟨154082, by rfl⟩ : syracuseStep 205443 = 308165) B308165
theorem B696977 : Blo 203807 696977 := bstep (se 2 (by rfl) ⟨261366, by rfl⟩ : syracuseStep 696977 = 522733) B522733
theorem B205459 : Blo 203807 205459 := bstep (se 1 (by rfl) ⟨154094, by rfl⟩ : syracuseStep 205459 = 308189) B308189
theorem B205475 : Blo 203807 205475 := bstep (se 1 (by rfl) ⟨154106, by rfl⟩ : syracuseStep 205475 = 308213) B308213
theorem B205491 : Blo 203807 205491 := bstep (se 1 (by rfl) ⟨154118, by rfl⟩ : syracuseStep 205491 = 308237) B308237
theorem B205507 : Blo 203807 205507 := bstep (se 1 (by rfl) ⟨154130, by rfl⟩ : syracuseStep 205507 = 308261) B308261
theorem B205523 : Blo 203807 205523 := bstep (se 1 (by rfl) ⟨154142, by rfl⟩ : syracuseStep 205523 = 308285) B308285
theorem B205539 : Blo 203807 205539 := bstep (se 1 (by rfl) ⟨154154, by rfl⟩ : syracuseStep 205539 = 308309) B308309
theorem B205555 : Blo 203807 205555 := bstep (se 1 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 205555 = 308333) B308333
theorem B205571 : Blo 203807 205571 := bstep (se 1 (by rfl) ⟨154178, by rfl⟩ : syracuseStep 205571 = 308357) B308357
theorem B1123085 : Blo 203807 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B205587 : Blo 203807 205587 := bstep (se 1 (by rfl) ⟨154190, by rfl⟩ : syracuseStep 205587 = 308381) B308381
theorem B205603 : Blo 203807 205603 := bstep (se 1 (by rfl) ⟨154202, by rfl⟩ : syracuseStep 205603 = 308405) B308405
theorem B205619 : Blo 203807 205619 := bstep (se 1 (by rfl) ⟨154214, by rfl⟩ : syracuseStep 205619 = 308429) B308429
theorem B205635 : Blo 203807 205635 := bstep (se 1 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 205635 = 308453) B308453
theorem B205651 : Blo 203807 205651 := bstep (se 1 (by rfl) ⟨154238, by rfl⟩ : syracuseStep 205651 = 308477) B308477
theorem B205667 : Blo 203807 205667 := bstep (se 1 (by rfl) ⟨154250, by rfl⟩ : syracuseStep 205667 = 308501) B308501
theorem B664433 : Blo 203807 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B205683 : Blo 203807 205683 := bstep (se 1 (by rfl) ⟨154262, by rfl⟩ : syracuseStep 205683 = 308525) B308525
theorem B205699 : Blo 203807 205699 := bstep (se 1 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 205699 = 308549) B308549
theorem B828301 : Blo 203807 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B205715 : Blo 203807 205715 := bstep (se 1 (by rfl) ⟨154286, by rfl⟩ : syracuseStep 205715 = 308573) B308573
theorem B205731 : Blo 203807 205731 := bstep (se 1 (by rfl) ⟨154298, by rfl⟩ : syracuseStep 205731 = 308597) B308597
theorem B205747 : Blo 203807 205747 := bstep (se 1 (by rfl) ⟨154310, by rfl⟩ : syracuseStep 205747 = 308621) B308621
theorem B205763 : Blo 203807 205763 := bstep (se 1 (by rfl) ⟨154322, by rfl⟩ : syracuseStep 205763 = 308645) B308645
theorem B205779 : Blo 203807 205779 := bstep (se 1 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 205779 = 308669) B308669
theorem B2335715 : Blo 203807 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B205795 : Blo 203807 205795 := bstep (se 1 (by rfl) ⟨154346, by rfl⟩ : syracuseStep 205795 = 308693) B308693
theorem B205811 : Blo 203807 205811 := bstep (se 1 (by rfl) ⟨154358, by rfl⟩ : syracuseStep 205811 = 308717) B308717
theorem B205827 : Blo 203807 205827 := bstep (se 1 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 205827 = 308741) B308741
theorem B205843 : Blo 203807 205843 := bstep (se 1 (by rfl) ⟨154382, by rfl⟩ : syracuseStep 205843 = 308765) B308765
theorem B205859 : Blo 203807 205859 := bstep (se 1 (by rfl) ⟨154394, by rfl⟩ : syracuseStep 205859 = 308789) B308789
theorem B205875 : Blo 203807 205875 := bstep (se 1 (by rfl) ⟨154406, by rfl⟩ : syracuseStep 205875 = 308813) B308813
theorem B205891 : Blo 203807 205891 := bstep (se 1 (by rfl) ⟨154418, by rfl⟩ : syracuseStep 205891 = 308837) B308837
theorem B205907 : Blo 203807 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B205923 : Blo 203807 205923 := bstep (se 1 (by rfl) ⟨154442, by rfl⟩ : syracuseStep 205923 = 308885) B308885
theorem B205939 : Blo 203807 205939 := bstep (se 1 (by rfl) ⟨154454, by rfl⟩ : syracuseStep 205939 = 308909) B308909
theorem B205955 : Blo 203807 205955 := bstep (se 1 (by rfl) ⟨154466, by rfl⟩ : syracuseStep 205955 = 308933) B308933
theorem B205971 : Blo 203807 205971 := bstep (se 1 (by rfl) ⟨154478, by rfl⟩ : syracuseStep 205971 = 308957) B308957
theorem B205987 : Blo 203807 205987 := bstep (se 1 (by rfl) ⟨154490, by rfl⟩ : syracuseStep 205987 = 308981) B308981
theorem B697517 : Blo 203807 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B206003 : Blo 203807 206003 := bstep (se 1 (by rfl) ⟨154502, by rfl⟩ : syracuseStep 206003 = 309005) B309005
theorem B206019 : Blo 203807 206019 := bstep (se 1 (by rfl) ⟨154514, by rfl⟩ : syracuseStep 206019 = 309029) B309029
theorem B206035 : Blo 203807 206035 := bstep (se 1 (by rfl) ⟨154526, by rfl⟩ : syracuseStep 206035 = 309053) B309053
theorem B206051 : Blo 203807 206051 := bstep (se 1 (by rfl) ⟨154538, by rfl⟩ : syracuseStep 206051 = 309077) B309077
theorem B697571 : Blo 203807 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B206067 : Blo 203807 206067 := bstep (se 1 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 206067 = 309101) B309101
theorem B206083 : Blo 203807 206083 := bstep (se 1 (by rfl) ⟨154562, by rfl⟩ : syracuseStep 206083 = 309125) B309125
theorem B369937 : Blo 203807 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B206099 : Blo 203807 206099 := bstep (se 1 (by rfl) ⟨154574, by rfl⟩ : syracuseStep 206099 = 309149) B309149
theorem B206115 : Blo 203807 206115 := bstep (se 1 (by rfl) ⟨154586, by rfl⟩ : syracuseStep 206115 = 309173) B309173
theorem B206131 : Blo 203807 206131 := bstep (se 1 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 206131 = 309197) B309197
theorem B206147 : Blo 203807 206147 := bstep (se 1 (by rfl) ⟨154610, by rfl⟩ : syracuseStep 206147 = 309221) B309221
theorem B1680709 : Blo 203807 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B1123661 : Blo 203807 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B206163 : Blo 203807 206163 := bstep (se 1 (by rfl) ⟨154622, by rfl⟩ : syracuseStep 206163 = 309245) B309245
theorem B206179 : Blo 203807 206179 := bstep (se 1 (by rfl) ⟨154634, by rfl⟩ : syracuseStep 206179 = 309269) B309269
theorem B206195 : Blo 203807 206195 := bstep (se 1 (by rfl) ⟨154646, by rfl⟩ : syracuseStep 206195 = 309293) B309293
theorem B206211 : Blo 203807 206211 := bstep (se 1 (by rfl) ⟨154658, by rfl⟩ : syracuseStep 206211 = 309317) B309317
theorem B206227 : Blo 203807 206227 := bstep (se 1 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 206227 = 309341) B309341
theorem B206243 : Blo 203807 206243 := bstep (se 1 (by rfl) ⟨154682, by rfl⟩ : syracuseStep 206243 = 309365) B309365
theorem B206259 : Blo 203807 206259 := bstep (se 1 (by rfl) ⟨154694, by rfl⟩ : syracuseStep 206259 = 309389) B309389
theorem B206275 : Blo 203807 206275 := bstep (se 1 (by rfl) ⟨154706, by rfl⟩ : syracuseStep 206275 = 309413) B309413
theorem B206291 : Blo 203807 206291 := bstep (se 1 (by rfl) ⟨154718, by rfl⟩ : syracuseStep 206291 = 309437) B309437
theorem B206307 : Blo 203807 206307 := bstep (se 1 (by rfl) ⟨154730, by rfl⟩ : syracuseStep 206307 = 309461) B309461
theorem B697841 : Blo 203807 697841 := bstep (se 2 (by rfl) ⟨261690, by rfl⟩ : syracuseStep 697841 = 523381) B523381
theorem B206323 : Blo 203807 206323 := bstep (se 1 (by rfl) ⟨154742, by rfl⟩ : syracuseStep 206323 = 309485) B309485
theorem B206339 : Blo 203807 206339 := bstep (se 1 (by rfl) ⟨154754, by rfl⟩ : syracuseStep 206339 = 309509) B309509
theorem B206355 : Blo 203807 206355 := bstep (se 1 (by rfl) ⟨154766, by rfl⟩ : syracuseStep 206355 = 309533) B309533
theorem B206371 : Blo 203807 206371 := bstep (se 1 (by rfl) ⟨154778, by rfl⟩ : syracuseStep 206371 = 309557) B309557
theorem B206387 : Blo 203807 206387 := bstep (se 1 (by rfl) ⟨154790, by rfl⟩ : syracuseStep 206387 = 309581) B309581
theorem B206403 : Blo 203807 206403 := bstep (se 1 (by rfl) ⟨154802, by rfl⟩ : syracuseStep 206403 = 309605) B309605
theorem B206419 : Blo 203807 206419 := bstep (se 1 (by rfl) ⟨154814, by rfl⟩ : syracuseStep 206419 = 309629) B309629
theorem B206435 : Blo 203807 206435 := bstep (se 1 (by rfl) ⟨154826, by rfl⟩ : syracuseStep 206435 = 309653) B309653
theorem B1680995 : Blo 203807 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B206451 : Blo 203807 206451 := bstep (se 1 (by rfl) ⟨154838, by rfl⟩ : syracuseStep 206451 = 309677) B309677
theorem B206467 : Blo 203807 206467 := bstep (se 1 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 206467 = 309701) B309701
theorem B206483 : Blo 203807 206483 := bstep (se 1 (by rfl) ⟨154862, by rfl⟩ : syracuseStep 206483 = 309725) B309725
theorem B206499 : Blo 203807 206499 := bstep (se 1 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 206499 = 309749) B309749
theorem B206515 : Blo 203807 206515 := bstep (se 1 (by rfl) ⟨154886, by rfl⟩ : syracuseStep 206515 = 309773) B309773
theorem B206531 : Blo 203807 206531 := bstep (se 1 (by rfl) ⟨154898, by rfl⟩ : syracuseStep 206531 = 309797) B309797
theorem B3352261 : Blo 203807 3352261 := bstep (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) B628549
theorem B206547 : Blo 203807 206547 := bstep (se 1 (by rfl) ⟨154910, by rfl⟩ : syracuseStep 206547 = 309821) B309821
theorem B206563 : Blo 203807 206563 := bstep (se 1 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 206563 = 309845) B309845
theorem B1124081 : Blo 203807 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B206579 : Blo 203807 206579 := bstep (se 1 (by rfl) ⟨154934, by rfl⟩ : syracuseStep 206579 = 309869) B309869
theorem B370435 : Blo 203807 370435 := bstep (se 1 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 370435 = 555653) B555653
theorem B206595 : Blo 203807 206595 := bstep (se 1 (by rfl) ⟨154946, by rfl⟩ : syracuseStep 206595 = 309893) B309893
theorem B206611 : Blo 203807 206611 := bstep (se 1 (by rfl) ⟨154958, by rfl⟩ : syracuseStep 206611 = 309917) B309917
theorem B206627 : Blo 203807 206627 := bstep (se 1 (by rfl) ⟨154970, by rfl⟩ : syracuseStep 206627 = 309941) B309941
theorem B468785 : Blo 203807 468785 := bstep (se 2 (by rfl) ⟨175794, by rfl⟩ : syracuseStep 468785 = 351589) B351589
theorem B206643 : Blo 203807 206643 := bstep (se 1 (by rfl) ⟨154982, by rfl⟩ : syracuseStep 206643 = 309965) B309965
theorem B206659 : Blo 203807 206659 := bstep (se 1 (by rfl) ⟨154994, by rfl⟩ : syracuseStep 206659 = 309989) B309989
theorem B206675 : Blo 203807 206675 := bstep (se 1 (by rfl) ⟨155006, by rfl⟩ : syracuseStep 206675 = 310013) B310013
theorem B206691 : Blo 203807 206691 := bstep (se 1 (by rfl) ⟨155018, by rfl⟩ : syracuseStep 206691 = 310037) B310037
theorem B206707 : Blo 203807 206707 := bstep (se 1 (by rfl) ⟨155030, by rfl⟩ : syracuseStep 206707 = 310061) B310061
theorem B206723 : Blo 203807 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B206739 : Blo 203807 206739 := bstep (se 1 (by rfl) ⟨155054, by rfl⟩ : syracuseStep 206739 = 310109) B310109
theorem B206755 : Blo 203807 206755 := bstep (se 1 (by rfl) ⟨155066, by rfl⟩ : syracuseStep 206755 = 310133) B310133
theorem B206771 : Blo 203807 206771 := bstep (se 1 (by rfl) ⟨155078, by rfl⟩ : syracuseStep 206771 = 310157) B310157
theorem B206787 : Blo 203807 206787 := bstep (se 1 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 206787 = 310181) B310181
theorem B206803 : Blo 203807 206803 := bstep (se 1 (by rfl) ⟨155102, by rfl⟩ : syracuseStep 206803 = 310205) B310205
theorem B206819 : Blo 203807 206819 := bstep (se 1 (by rfl) ⟨155114, by rfl⟩ : syracuseStep 206819 = 310229) B310229
theorem B206835 : Blo 203807 206835 := bstep (se 1 (by rfl) ⟨155126, by rfl⟩ : syracuseStep 206835 = 310253) B310253
theorem B206851 : Blo 203807 206851 := bstep (se 1 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 206851 = 310277) B310277
theorem B698381 : Blo 203807 698381 := bstep (se 3 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 698381 = 261893) B261893
theorem B206867 : Blo 203807 206867 := bstep (se 1 (by rfl) ⟨155150, by rfl⟩ : syracuseStep 206867 = 310301) B310301
theorem B206883 : Blo 203807 206883 := bstep (se 1 (by rfl) ⟨155162, by rfl⟩ : syracuseStep 206883 = 310325) B310325
theorem B206899 : Blo 203807 206899 := bstep (se 1 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 206899 = 310349) B310349
theorem B206915 : Blo 203807 206915 := bstep (se 1 (by rfl) ⟨155186, by rfl⟩ : syracuseStep 206915 = 310373) B310373
theorem B698435 : Blo 203807 698435 := bstep (se 1 (by rfl) ⟨523826, by rfl⟩ : syracuseStep 698435 = 1047653) B1047653
theorem B206931 : Blo 203807 206931 := bstep (se 1 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 206931 = 310397) B310397
theorem B206947 : Blo 203807 206947 := bstep (se 1 (by rfl) ⟨155210, by rfl⟩ : syracuseStep 206947 = 310421) B310421
theorem B206963 : Blo 203807 206963 := bstep (se 1 (by rfl) ⟨155222, by rfl⟩ : syracuseStep 206963 = 310445) B310445
theorem B206979 : Blo 203807 206979 := bstep (se 1 (by rfl) ⟨155234, by rfl⟩ : syracuseStep 206979 = 310469) B310469
theorem B206995 : Blo 203807 206995 := bstep (se 1 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 206995 = 310493) B310493
theorem B207011 : Blo 203807 207011 := bstep (se 1 (by rfl) ⟨155258, by rfl⟩ : syracuseStep 207011 = 310517) B310517
theorem B207027 : Blo 203807 207027 := bstep (se 1 (by rfl) ⟨155270, by rfl⟩ : syracuseStep 207027 = 310541) B310541
theorem B207043 : Blo 203807 207043 := bstep (se 1 (by rfl) ⟨155282, by rfl⟩ : syracuseStep 207043 = 310565) B310565
theorem B207059 : Blo 203807 207059 := bstep (se 1 (by rfl) ⟨155294, by rfl⟩ : syracuseStep 207059 = 310589) B310589
theorem B207075 : Blo 203807 207075 := bstep (se 1 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 207075 = 310613) B310613
theorem B207091 : Blo 203807 207091 := bstep (se 1 (by rfl) ⟨155318, by rfl⟩ : syracuseStep 207091 = 310637) B310637
theorem B207107 : Blo 203807 207107 := bstep (se 1 (by rfl) ⟨155330, by rfl⟩ : syracuseStep 207107 = 310661) B310661
theorem B207123 : Blo 203807 207123 := bstep (se 1 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 207123 = 310685) B310685
theorem B207139 : Blo 203807 207139 := bstep (se 1 (by rfl) ⟨155354, by rfl⟩ : syracuseStep 207139 = 310709) B310709
theorem B436529 : Blo 203807 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B207155 : Blo 203807 207155 := bstep (se 1 (by rfl) ⟨155366, by rfl⟩ : syracuseStep 207155 = 310733) B310733
theorem B207171 : Blo 203807 207171 := bstep (se 1 (by rfl) ⟨155378, by rfl⟩ : syracuseStep 207171 = 310757) B310757
theorem B698705 : Blo 203807 698705 := bstep (se 2 (by rfl) ⟨262014, by rfl⟩ : syracuseStep 698705 = 524029) B524029
theorem B207187 : Blo 203807 207187 := bstep (se 1 (by rfl) ⟨155390, by rfl⟩ : syracuseStep 207187 = 310781) B310781
theorem B207203 : Blo 203807 207203 := bstep (se 1 (by rfl) ⟨155402, by rfl⟩ : syracuseStep 207203 = 310805) B310805
theorem B207219 : Blo 203807 207219 := bstep (se 1 (by rfl) ⟨155414, by rfl⟩ : syracuseStep 207219 = 310829) B310829
theorem B207235 : Blo 203807 207235 := bstep (se 1 (by rfl) ⟨155426, by rfl⟩ : syracuseStep 207235 = 310853) B310853
theorem B207251 : Blo 203807 207251 := bstep (se 1 (by rfl) ⟨155438, by rfl⟩ : syracuseStep 207251 = 310877) B310877
theorem B207267 : Blo 203807 207267 := bstep (se 1 (by rfl) ⟨155450, by rfl⟩ : syracuseStep 207267 = 310901) B310901
theorem B207283 : Blo 203807 207283 := bstep (se 1 (by rfl) ⟨155462, by rfl⟩ : syracuseStep 207283 = 310925) B310925
theorem B207299 : Blo 203807 207299 := bstep (se 1 (by rfl) ⟨155474, by rfl⟩ : syracuseStep 207299 = 310949) B310949
theorem B207315 : Blo 203807 207315 := bstep (se 1 (by rfl) ⟨155486, by rfl⟩ : syracuseStep 207315 = 310973) B310973
theorem B207331 : Blo 203807 207331 := bstep (se 1 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 207331 = 310997) B310997
theorem B207347 : Blo 203807 207347 := bstep (se 1 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 207347 = 311021) B311021
theorem B207363 : Blo 203807 207363 := bstep (se 1 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 207363 = 311045) B311045
theorem B207379 : Blo 203807 207379 := bstep (se 1 (by rfl) ⟨155534, by rfl⟩ : syracuseStep 207379 = 311069) B311069
theorem B207395 : Blo 203807 207395 := bstep (se 1 (by rfl) ⟨155546, by rfl⟩ : syracuseStep 207395 = 311093) B311093
theorem B207411 : Blo 203807 207411 := bstep (se 1 (by rfl) ⟨155558, by rfl⟩ : syracuseStep 207411 = 311117) B311117
theorem B305729 : Blo 203807 305729 := bstep (se 2 (by rfl) ⟨114648, by rfl⟩ : syracuseStep 305729 = 229297) B229297
theorem B207427 : Blo 203807 207427 := bstep (se 1 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 207427 = 311141) B311141
theorem B305747 : Blo 203807 305747 := bstep (se 1 (by rfl) ⟨229310, by rfl⟩ : syracuseStep 305747 = 458621) B458621
theorem B207443 : Blo 203807 207443 := bstep (se 1 (by rfl) ⟨155582, by rfl⟩ : syracuseStep 207443 = 311165) B311165
theorem B207459 : Blo 203807 207459 := bstep (se 1 (by rfl) ⟨155594, by rfl⟩ : syracuseStep 207459 = 311189) B311189
theorem B305777 : Blo 203807 305777 := bstep (se 2 (by rfl) ⟨114666, by rfl⟩ : syracuseStep 305777 = 229333) B229333
theorem B207475 : Blo 203807 207475 := bstep (se 1 (by rfl) ⟨155606, by rfl⟩ : syracuseStep 207475 = 311213) B311213
theorem B305795 : Blo 203807 305795 := bstep (se 1 (by rfl) ⟨229346, by rfl⟩ : syracuseStep 305795 = 458693) B458693
theorem B207491 : Blo 203807 207491 := bstep (se 1 (by rfl) ⟨155618, by rfl⟩ : syracuseStep 207491 = 311237) B311237
theorem B207507 : Blo 203807 207507 := bstep (se 1 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 207507 = 311261) B311261
theorem B305825 : Blo 203807 305825 := bstep (se 2 (by rfl) ⟨114684, by rfl⟩ : syracuseStep 305825 = 229369) B229369
theorem B371363 : Blo 203807 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B207523 : Blo 203807 207523 := bstep (se 1 (by rfl) ⟨155642, by rfl⟩ : syracuseStep 207523 = 311285) B311285
theorem B305843 : Blo 203807 305843 := bstep (se 1 (by rfl) ⟨229382, by rfl⟩ : syracuseStep 305843 = 458765) B458765
theorem B207539 : Blo 203807 207539 := bstep (se 1 (by rfl) ⟨155654, by rfl⟩ : syracuseStep 207539 = 311309) B311309
theorem B207555 : Blo 203807 207555 := bstep (se 1 (by rfl) ⟨155666, by rfl⟩ : syracuseStep 207555 = 311333) B311333
theorem B305873 : Blo 203807 305873 := bstep (se 2 (by rfl) ⟨114702, by rfl⟩ : syracuseStep 305873 = 229405) B229405
theorem B207571 : Blo 203807 207571 := bstep (se 1 (by rfl) ⟨155678, by rfl⟩ : syracuseStep 207571 = 311357) B311357
theorem B305891 : Blo 203807 305891 := bstep (se 1 (by rfl) ⟨229418, by rfl⟩ : syracuseStep 305891 = 458837) B458837
theorem B207587 : Blo 203807 207587 := bstep (se 1 (by rfl) ⟨155690, by rfl⟩ : syracuseStep 207587 = 311381) B311381
theorem B207603 : Blo 203807 207603 := bstep (se 1 (by rfl) ⟨155702, by rfl⟩ : syracuseStep 207603 = 311405) B311405
theorem B305921 : Blo 203807 305921 := bstep (se 2 (by rfl) ⟨114720, by rfl⟩ : syracuseStep 305921 = 229441) B229441
theorem B207619 : Blo 203807 207619 := bstep (se 1 (by rfl) ⟨155714, by rfl⟩ : syracuseStep 207619 = 311429) B311429
theorem B305939 : Blo 203807 305939 := bstep (se 1 (by rfl) ⟨229454, by rfl⟩ : syracuseStep 305939 = 458909) B458909
theorem B207635 : Blo 203807 207635 := bstep (se 1 (by rfl) ⟨155726, by rfl⟩ : syracuseStep 207635 = 311453) B311453
theorem B207651 : Blo 203807 207651 := bstep (se 1 (by rfl) ⟨155738, by rfl⟩ : syracuseStep 207651 = 311477) B311477
theorem B305969 : Blo 203807 305969 := bstep (se 2 (by rfl) ⟨114738, by rfl⟩ : syracuseStep 305969 = 229477) B229477
theorem B207667 : Blo 203807 207667 := bstep (se 1 (by rfl) ⟨155750, by rfl⟩ : syracuseStep 207667 = 311501) B311501
theorem B305987 : Blo 203807 305987 := bstep (se 1 (by rfl) ⟨229490, by rfl⟩ : syracuseStep 305987 = 458981) B458981
theorem B207683 : Blo 203807 207683 := bstep (se 1 (by rfl) ⟨155762, by rfl⟩ : syracuseStep 207683 = 311525) B311525
theorem B207699 : Blo 203807 207699 := bstep (se 1 (by rfl) ⟨155774, by rfl⟩ : syracuseStep 207699 = 311549) B311549
theorem B306017 : Blo 203807 306017 := bstep (se 2 (by rfl) ⟨114756, by rfl⟩ : syracuseStep 306017 = 229513) B229513
theorem B207715 : Blo 203807 207715 := bstep (se 1 (by rfl) ⟨155786, by rfl⟩ : syracuseStep 207715 = 311573) B311573
theorem B699245 : Blo 203807 699245 := bstep (se 3 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 699245 = 262217) B262217
theorem B306035 : Blo 203807 306035 := bstep (se 1 (by rfl) ⟨229526, by rfl⟩ : syracuseStep 306035 = 459053) B459053
theorem B207731 : Blo 203807 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B207747 : Blo 203807 207747 := bstep (se 1 (by rfl) ⟨155810, by rfl⟩ : syracuseStep 207747 = 311621) B311621
theorem B306065 : Blo 203807 306065 := bstep (se 2 (by rfl) ⟨114774, by rfl⟩ : syracuseStep 306065 = 229549) B229549
theorem B207763 : Blo 203807 207763 := bstep (se 1 (by rfl) ⟨155822, by rfl⟩ : syracuseStep 207763 = 311645) B311645
theorem B306083 : Blo 203807 306083 := bstep (se 1 (by rfl) ⟨229562, by rfl⟩ : syracuseStep 306083 = 459125) B459125
theorem B699299 : Blo 203807 699299 := bstep (se 1 (by rfl) ⟨524474, by rfl⟩ : syracuseStep 699299 = 1048949) B1048949
theorem B207779 : Blo 203807 207779 := bstep (se 1 (by rfl) ⟨155834, by rfl⟩ : syracuseStep 207779 = 311669) B311669
theorem B207795 : Blo 203807 207795 := bstep (se 1 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 207795 = 311693) B311693
theorem B306113 : Blo 203807 306113 := bstep (se 2 (by rfl) ⟨114792, by rfl⟩ : syracuseStep 306113 = 229585) B229585
theorem B469955 : Blo 203807 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B306131 : Blo 203807 306131 := bstep (se 1 (by rfl) ⟨229598, by rfl⟩ : syracuseStep 306131 = 459197) B459197
theorem B306161 : Blo 203807 306161 := bstep (se 2 (by rfl) ⟨114810, by rfl⟩ : syracuseStep 306161 = 229621) B229621
theorem B306179 : Blo 203807 306179 := bstep (se 1 (by rfl) ⟨229634, by rfl⟩ : syracuseStep 306179 = 459269) B459269
theorem B306209 : Blo 203807 306209 := bstep (se 2 (by rfl) ⟨114828, by rfl⟩ : syracuseStep 306209 = 229657) B229657
theorem B306227 : Blo 203807 306227 := bstep (se 1 (by rfl) ⟨229670, by rfl⟩ : syracuseStep 306227 = 459341) B459341
theorem B306257 : Blo 203807 306257 := bstep (se 2 (by rfl) ⟨114846, by rfl⟩ : syracuseStep 306257 = 229693) B229693
theorem B306275 : Blo 203807 306275 := bstep (se 1 (by rfl) ⟨229706, by rfl⟩ : syracuseStep 306275 = 459413) B459413
theorem B306305 : Blo 203807 306305 := bstep (se 2 (by rfl) ⟨114864, by rfl⟩ : syracuseStep 306305 = 229729) B229729
theorem B437393 : Blo 203807 437393 := bstep (se 2 (by rfl) ⟨164022, by rfl⟩ : syracuseStep 437393 = 328045) B328045
theorem B306323 : Blo 203807 306323 := bstep (se 1 (by rfl) ⟨229742, by rfl⟩ : syracuseStep 306323 = 459485) B459485
theorem B306353 : Blo 203807 306353 := bstep (se 2 (by rfl) ⟨114882, by rfl⟩ : syracuseStep 306353 = 229765) B229765
theorem B699569 : Blo 203807 699569 := bstep (se 2 (by rfl) ⟨262338, by rfl⟩ : syracuseStep 699569 = 524677) B524677
theorem B306371 : Blo 203807 306371 := bstep (se 1 (by rfl) ⟨229778, by rfl⟩ : syracuseStep 306371 = 459557) B459557
theorem B306401 : Blo 203807 306401 := bstep (se 2 (by rfl) ⟨114900, by rfl⟩ : syracuseStep 306401 = 229801) B229801
theorem B994531 : Blo 203807 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B306419 : Blo 203807 306419 := bstep (se 1 (by rfl) ⟨229814, by rfl⟩ : syracuseStep 306419 = 459629) B459629
theorem B306449 : Blo 203807 306449 := bstep (se 2 (by rfl) ⟨114918, by rfl⟩ : syracuseStep 306449 = 229837) B229837
theorem B306467 : Blo 203807 306467 := bstep (se 1 (by rfl) ⟨229850, by rfl⟩ : syracuseStep 306467 = 459701) B459701
theorem B306497 : Blo 203807 306497 := bstep (se 2 (by rfl) ⟨114936, by rfl⟩ : syracuseStep 306497 = 229873) B229873
theorem B306515 : Blo 203807 306515 := bstep (se 1 (by rfl) ⟨229886, by rfl⟩ : syracuseStep 306515 = 459773) B459773
theorem B306545 : Blo 203807 306545 := bstep (se 2 (by rfl) ⟨114954, by rfl⟩ : syracuseStep 306545 = 229909) B229909
theorem B208243 : Blo 203807 208243 := bstep (se 1 (by rfl) ⟨156182, by rfl⟩ : syracuseStep 208243 = 312365) B312365
theorem B306563 : Blo 203807 306563 := bstep (se 1 (by rfl) ⟨229922, by rfl⟩ : syracuseStep 306563 = 459845) B459845
theorem B306593 : Blo 203807 306593 := bstep (se 2 (by rfl) ⟨114972, by rfl⟩ : syracuseStep 306593 = 229945) B229945
theorem B306611 : Blo 203807 306611 := bstep (se 1 (by rfl) ⟨229958, by rfl⟩ : syracuseStep 306611 = 459917) B459917
theorem B699853 : Blo 203807 699853 := bstep (se 3 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 699853 = 262445) B262445
theorem B306641 : Blo 203807 306641 := bstep (se 2 (by rfl) ⟨114990, by rfl⟩ : syracuseStep 306641 = 229981) B229981
theorem B306659 : Blo 203807 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B994801 : Blo 203807 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B306689 : Blo 203807 306689 := bstep (se 2 (by rfl) ⟨115008, by rfl⟩ : syracuseStep 306689 = 230017) B230017
theorem B306707 : Blo 203807 306707 := bstep (se 1 (by rfl) ⟨230030, by rfl⟩ : syracuseStep 306707 = 460061) B460061
theorem B306737 : Blo 203807 306737 := bstep (se 2 (by rfl) ⟨115026, by rfl⟩ : syracuseStep 306737 = 230053) B230053
theorem B306755 : Blo 203807 306755 := bstep (se 1 (by rfl) ⟨230066, by rfl⟩ : syracuseStep 306755 = 460133) B460133
theorem B306785 : Blo 203807 306785 := bstep (se 2 (by rfl) ⟨115044, by rfl⟩ : syracuseStep 306785 = 230089) B230089
theorem B4763249 : Blo 203807 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B306803 : Blo 203807 306803 := bstep (se 1 (by rfl) ⟨230102, by rfl⟩ : syracuseStep 306803 = 460205) B460205
theorem B306833 : Blo 203807 306833 := bstep (se 2 (by rfl) ⟨115062, by rfl⟩ : syracuseStep 306833 = 230125) B230125
theorem B306851 : Blo 203807 306851 := bstep (se 1 (by rfl) ⟨230138, by rfl⟩ : syracuseStep 306851 = 460277) B460277
theorem B306881 : Blo 203807 306881 := bstep (se 2 (by rfl) ⟨115080, by rfl⟩ : syracuseStep 306881 = 230161) B230161
theorem B700109 : Blo 203807 700109 := bstep (se 3 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 700109 = 262541) B262541
theorem B306899 : Blo 203807 306899 := bstep (se 1 (by rfl) ⟨230174, by rfl⟩ : syracuseStep 306899 = 460349) B460349
theorem B306929 : Blo 203807 306929 := bstep (se 2 (by rfl) ⟨115098, by rfl⟩ : syracuseStep 306929 = 230197) B230197
theorem B306947 : Blo 203807 306947 := bstep (se 1 (by rfl) ⟨230210, by rfl⟩ : syracuseStep 306947 = 460421) B460421
theorem B700163 : Blo 203807 700163 := bstep (se 1 (by rfl) ⟨525122, by rfl⟩ : syracuseStep 700163 = 1050245) B1050245
theorem B306977 : Blo 203807 306977 := bstep (se 2 (by rfl) ⟨115116, by rfl⟩ : syracuseStep 306977 = 230233) B230233
theorem B306995 : Blo 203807 306995 := bstep (se 1 (by rfl) ⟨230246, by rfl⟩ : syracuseStep 306995 = 460493) B460493
theorem B307025 : Blo 203807 307025 := bstep (se 2 (by rfl) ⟨115134, by rfl⟩ : syracuseStep 307025 = 230269) B230269
theorem B307043 : Blo 203807 307043 := bstep (se 1 (by rfl) ⟨230282, by rfl⟩ : syracuseStep 307043 = 460565) B460565
theorem B307073 : Blo 203807 307073 := bstep (se 2 (by rfl) ⟨115152, by rfl⟩ : syracuseStep 307073 = 230305) B230305
theorem B307091 : Blo 203807 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B307121 : Blo 203807 307121 := bstep (se 2 (by rfl) ⟨115170, by rfl⟩ : syracuseStep 307121 = 230341) B230341
theorem B307139 : Blo 203807 307139 := bstep (se 1 (by rfl) ⟨230354, by rfl⟩ : syracuseStep 307139 = 460709) B460709
theorem B307169 : Blo 203807 307169 := bstep (se 2 (by rfl) ⟨115188, by rfl⟩ : syracuseStep 307169 = 230377) B230377
theorem B1257443 : Blo 203807 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B307187 : Blo 203807 307187 := bstep (se 1 (by rfl) ⟨230390, by rfl⟩ : syracuseStep 307187 = 460781) B460781
theorem B307217 : Blo 203807 307217 := bstep (se 2 (by rfl) ⟨115206, by rfl⟩ : syracuseStep 307217 = 230413) B230413
theorem B700433 : Blo 203807 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B307235 : Blo 203807 307235 := bstep (se 1 (by rfl) ⟨230426, by rfl⟩ : syracuseStep 307235 = 460853) B460853
theorem B307265 : Blo 203807 307265 := bstep (se 2 (by rfl) ⟨115224, by rfl⟩ : syracuseStep 307265 = 230449) B230449
theorem B307283 : Blo 203807 307283 := bstep (se 1 (by rfl) ⟨230462, by rfl⟩ : syracuseStep 307283 = 460925) B460925
theorem B307313 : Blo 203807 307313 := bstep (se 2 (by rfl) ⟨115242, by rfl⟩ : syracuseStep 307313 = 230485) B230485
theorem B307331 : Blo 203807 307331 := bstep (se 1 (by rfl) ⟨230498, by rfl⟩ : syracuseStep 307331 = 460997) B460997
theorem B307361 : Blo 203807 307361 := bstep (se 2 (by rfl) ⟨115260, by rfl⟩ : syracuseStep 307361 = 230521) B230521
theorem B307379 : Blo 203807 307379 := bstep (se 1 (by rfl) ⟨230534, by rfl⟩ : syracuseStep 307379 = 461069) B461069
theorem B307409 : Blo 203807 307409 := bstep (se 2 (by rfl) ⟨115278, by rfl⟩ : syracuseStep 307409 = 230557) B230557
theorem B307427 : Blo 203807 307427 := bstep (se 1 (by rfl) ⟨230570, by rfl⟩ : syracuseStep 307427 = 461141) B461141
theorem B372977 : Blo 203807 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B307457 : Blo 203807 307457 := bstep (se 2 (by rfl) ⟨115296, by rfl⟩ : syracuseStep 307457 = 230593) B230593
theorem B307475 : Blo 203807 307475 := bstep (se 1 (by rfl) ⟨230606, by rfl⟩ : syracuseStep 307475 = 461213) B461213
theorem B307505 : Blo 203807 307505 := bstep (se 2 (by rfl) ⟨115314, by rfl⟩ : syracuseStep 307505 = 230629) B230629
theorem B307523 : Blo 203807 307523 := bstep (se 1 (by rfl) ⟨230642, by rfl⟩ : syracuseStep 307523 = 461285) B461285
theorem B307553 : Blo 203807 307553 := bstep (se 2 (by rfl) ⟨115332, by rfl⟩ : syracuseStep 307553 = 230665) B230665
theorem B1323377 : Blo 203807 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B307571 : Blo 203807 307571 := bstep (se 1 (by rfl) ⟨230678, by rfl⟩ : syracuseStep 307571 = 461357) B461357
theorem B373123 : Blo 203807 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B307601 : Blo 203807 307601 := bstep (se 2 (by rfl) ⟨115350, by rfl⟩ : syracuseStep 307601 = 230701) B230701
theorem B307619 : Blo 203807 307619 := bstep (se 1 (by rfl) ⟨230714, by rfl⟩ : syracuseStep 307619 = 461429) B461429
theorem B438691 : Blo 203807 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B307649 : Blo 203807 307649 := bstep (se 2 (by rfl) ⟨115368, by rfl⟩ : syracuseStep 307649 = 230737) B230737
theorem B307667 : Blo 203807 307667 := bstep (se 1 (by rfl) ⟨230750, by rfl⟩ : syracuseStep 307667 = 461501) B461501
theorem B307697 : Blo 203807 307697 := bstep (se 2 (by rfl) ⟨115386, by rfl⟩ : syracuseStep 307697 = 230773) B230773
theorem B209395 : Blo 203807 209395 := bstep (se 1 (by rfl) ⟨157046, by rfl⟩ : syracuseStep 209395 = 314093) B314093
theorem B307715 : Blo 203807 307715 := bstep (se 1 (by rfl) ⟨230786, by rfl⟩ : syracuseStep 307715 = 461573) B461573
theorem B307745 : Blo 203807 307745 := bstep (se 2 (by rfl) ⟨115404, by rfl⟩ : syracuseStep 307745 = 230809) B230809
theorem B700973 : Blo 203807 700973 := bstep (se 3 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 700973 = 262865) B262865
theorem B307763 : Blo 203807 307763 := bstep (se 1 (by rfl) ⟨230822, by rfl⟩ : syracuseStep 307763 = 461645) B461645
theorem B307793 : Blo 203807 307793 := bstep (se 2 (by rfl) ⟨115422, by rfl⟩ : syracuseStep 307793 = 230845) B230845
theorem B307811 : Blo 203807 307811 := bstep (se 1 (by rfl) ⟨230858, by rfl⟩ : syracuseStep 307811 = 461717) B461717
theorem B701027 : Blo 203807 701027 := bstep (se 1 (by rfl) ⟨525770, by rfl⟩ : syracuseStep 701027 = 1051541) B1051541
theorem B307841 : Blo 203807 307841 := bstep (se 2 (by rfl) ⟨115440, by rfl⟩ : syracuseStep 307841 = 230881) B230881
theorem B307859 : Blo 203807 307859 := bstep (se 1 (by rfl) ⟨230894, by rfl⟩ : syracuseStep 307859 = 461789) B461789
theorem B307889 : Blo 203807 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B307907 : Blo 203807 307907 := bstep (se 1 (by rfl) ⟨230930, by rfl⟩ : syracuseStep 307907 = 461861) B461861
theorem B307937 : Blo 203807 307937 := bstep (se 2 (by rfl) ⟨115476, by rfl⟩ : syracuseStep 307937 = 230953) B230953
theorem B307955 : Blo 203807 307955 := bstep (se 1 (by rfl) ⟨230966, by rfl⟩ : syracuseStep 307955 = 461933) B461933
theorem B307985 : Blo 203807 307985 := bstep (se 2 (by rfl) ⟨115494, by rfl⟩ : syracuseStep 307985 = 230989) B230989
theorem B308003 : Blo 203807 308003 := bstep (se 1 (by rfl) ⟨231002, by rfl⟩ : syracuseStep 308003 = 462005) B462005
theorem B308033 : Blo 203807 308033 := bstep (se 2 (by rfl) ⟨115512, by rfl⟩ : syracuseStep 308033 = 231025) B231025
theorem B668483 : Blo 203807 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B373585 : Blo 203807 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B308051 : Blo 203807 308051 := bstep (se 1 (by rfl) ⟨231038, by rfl⟩ : syracuseStep 308051 = 462077) B462077
theorem B308081 : Blo 203807 308081 := bstep (se 2 (by rfl) ⟨115530, by rfl⟩ : syracuseStep 308081 = 231061) B231061
theorem B701297 : Blo 203807 701297 := bstep (se 2 (by rfl) ⟨262986, by rfl⟩ : syracuseStep 701297 = 525973) B525973
theorem B308099 : Blo 203807 308099 := bstep (se 1 (by rfl) ⟨231074, by rfl⟩ : syracuseStep 308099 = 462149) B462149
theorem B308129 : Blo 203807 308129 := bstep (se 2 (by rfl) ⟨115548, by rfl⟩ : syracuseStep 308129 = 231097) B231097
theorem B308147 : Blo 203807 308147 := bstep (se 1 (by rfl) ⟨231110, by rfl⟩ : syracuseStep 308147 = 462221) B462221
theorem B308177 : Blo 203807 308177 := bstep (se 2 (by rfl) ⟨115566, by rfl⟩ : syracuseStep 308177 = 231133) B231133
theorem B308195 : Blo 203807 308195 := bstep (se 1 (by rfl) ⟨231146, by rfl⟩ : syracuseStep 308195 = 462293) B462293
theorem B308225 : Blo 203807 308225 := bstep (se 2 (by rfl) ⟨115584, by rfl⟩ : syracuseStep 308225 = 231169) B231169
theorem B308243 : Blo 203807 308243 := bstep (se 1 (by rfl) ⟨231182, by rfl⟩ : syracuseStep 308243 = 462365) B462365
theorem B308273 : Blo 203807 308273 := bstep (se 2 (by rfl) ⟨115602, by rfl⟩ : syracuseStep 308273 = 231205) B231205
theorem B308291 : Blo 203807 308291 := bstep (se 1 (by rfl) ⟨231218, by rfl⟩ : syracuseStep 308291 = 462437) B462437
theorem B308321 : Blo 203807 308321 := bstep (se 2 (by rfl) ⟨115620, by rfl⟩ : syracuseStep 308321 = 231241) B231241
theorem B308339 : Blo 203807 308339 := bstep (se 1 (by rfl) ⟨231254, by rfl⟩ : syracuseStep 308339 = 462509) B462509
theorem B308369 : Blo 203807 308369 := bstep (se 2 (by rfl) ⟨115638, by rfl⟩ : syracuseStep 308369 = 231277) B231277
theorem B308387 : Blo 203807 308387 := bstep (se 1 (by rfl) ⟨231290, by rfl⟩ : syracuseStep 308387 = 462581) B462581
theorem B308417 : Blo 203807 308417 := bstep (se 2 (by rfl) ⟨115656, by rfl⟩ : syracuseStep 308417 = 231313) B231313
theorem B308435 : Blo 203807 308435 := bstep (se 1 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 308435 = 462653) B462653
theorem B3880163 : Blo 203807 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B308465 : Blo 203807 308465 := bstep (se 2 (by rfl) ⟨115674, by rfl⟩ : syracuseStep 308465 = 231349) B231349
theorem B308483 : Blo 203807 308483 := bstep (se 1 (by rfl) ⟨231362, by rfl⟩ : syracuseStep 308483 = 462725) B462725
theorem B308513 : Blo 203807 308513 := bstep (se 2 (by rfl) ⟨115692, by rfl⟩ : syracuseStep 308513 = 231385) B231385
theorem B308531 : Blo 203807 308531 := bstep (se 1 (by rfl) ⟨231398, by rfl⟩ : syracuseStep 308531 = 462797) B462797
theorem B308561 : Blo 203807 308561 := bstep (se 2 (by rfl) ⟨115710, by rfl⟩ : syracuseStep 308561 = 231421) B231421
theorem B308579 : Blo 203807 308579 := bstep (se 1 (by rfl) ⟨231434, by rfl⟩ : syracuseStep 308579 = 462869) B462869
theorem B308609 : Blo 203807 308609 := bstep (se 2 (by rfl) ⟨115728, by rfl⟩ : syracuseStep 308609 = 231457) B231457
theorem B308627 : Blo 203807 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B308657 : Blo 203807 308657 := bstep (se 2 (by rfl) ⟨115746, by rfl⟩ : syracuseStep 308657 = 231493) B231493
theorem B308675 : Blo 203807 308675 := bstep (se 1 (by rfl) ⟨231506, by rfl⟩ : syracuseStep 308675 = 463013) B463013
theorem B308705 : Blo 203807 308705 := bstep (se 2 (by rfl) ⟨115764, by rfl⟩ : syracuseStep 308705 = 231529) B231529
theorem B308723 : Blo 203807 308723 := bstep (se 1 (by rfl) ⟨231542, by rfl⟩ : syracuseStep 308723 = 463085) B463085
theorem B275971 : Blo 203807 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B308753 : Blo 203807 308753 := bstep (se 2 (by rfl) ⟨115782, by rfl⟩ : syracuseStep 308753 = 231565) B231565
theorem B308771 : Blo 203807 308771 := bstep (se 1 (by rfl) ⟨231578, by rfl⟩ : syracuseStep 308771 = 463157) B463157
theorem B308801 : Blo 203807 308801 := bstep (se 2 (by rfl) ⟨115800, by rfl⟩ : syracuseStep 308801 = 231601) B231601
theorem B308819 : Blo 203807 308819 := bstep (se 1 (by rfl) ⟨231614, by rfl⟩ : syracuseStep 308819 = 463229) B463229
theorem B308849 : Blo 203807 308849 := bstep (se 2 (by rfl) ⟨115818, by rfl⟩ : syracuseStep 308849 = 231637) B231637
theorem B439921 : Blo 203807 439921 := bstep (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) B329941
theorem B308867 : Blo 203807 308867 := bstep (se 1 (by rfl) ⟨231650, by rfl⟩ : syracuseStep 308867 = 463301) B463301
theorem B308897 : Blo 203807 308897 := bstep (se 2 (by rfl) ⟨115836, by rfl⟩ : syracuseStep 308897 = 231673) B231673
theorem B308915 : Blo 203807 308915 := bstep (se 1 (by rfl) ⟨231686, by rfl⟩ : syracuseStep 308915 = 463373) B463373
theorem B308945 : Blo 203807 308945 := bstep (se 2 (by rfl) ⟨115854, by rfl⟩ : syracuseStep 308945 = 231709) B231709
theorem B308963 : Blo 203807 308963 := bstep (se 1 (by rfl) ⟨231722, by rfl⟩ : syracuseStep 308963 = 463445) B463445
theorem B308993 : Blo 203807 308993 := bstep (se 2 (by rfl) ⟨115872, by rfl⟩ : syracuseStep 308993 = 231745) B231745
theorem B309011 : Blo 203807 309011 := bstep (se 1 (by rfl) ⟨231758, by rfl⟩ : syracuseStep 309011 = 463517) B463517
theorem B309041 : Blo 203807 309041 := bstep (se 2 (by rfl) ⟨115890, by rfl⟩ : syracuseStep 309041 = 231781) B231781
theorem B309059 : Blo 203807 309059 := bstep (se 1 (by rfl) ⟨231794, by rfl⟩ : syracuseStep 309059 = 463589) B463589
theorem B309089 : Blo 203807 309089 := bstep (se 2 (by rfl) ⟨115908, by rfl⟩ : syracuseStep 309089 = 231817) B231817
theorem B309107 : Blo 203807 309107 := bstep (se 1 (by rfl) ⟨231830, by rfl⟩ : syracuseStep 309107 = 463661) B463661
theorem B309137 : Blo 203807 309137 := bstep (se 2 (by rfl) ⟨115926, by rfl⟩ : syracuseStep 309137 = 231853) B231853
theorem B309155 : Blo 203807 309155 := bstep (se 1 (by rfl) ⟨231866, by rfl⟩ : syracuseStep 309155 = 463733) B463733
theorem B309185 : Blo 203807 309185 := bstep (se 2 (by rfl) ⟨115944, by rfl⟩ : syracuseStep 309185 = 231889) B231889
theorem B309203 : Blo 203807 309203 := bstep (se 1 (by rfl) ⟨231902, by rfl⟩ : syracuseStep 309203 = 463805) B463805
theorem B309233 : Blo 203807 309233 := bstep (se 2 (by rfl) ⟨115962, by rfl⟩ : syracuseStep 309233 = 231925) B231925
theorem B309251 : Blo 203807 309251 := bstep (se 1 (by rfl) ⟨231938, by rfl⟩ : syracuseStep 309251 = 463877) B463877
theorem B309281 : Blo 203807 309281 := bstep (se 2 (by rfl) ⟨115980, by rfl⟩ : syracuseStep 309281 = 231961) B231961
theorem B309299 : Blo 203807 309299 := bstep (se 1 (by rfl) ⟨231974, by rfl⟩ : syracuseStep 309299 = 463949) B463949
theorem B309329 : Blo 203807 309329 := bstep (se 2 (by rfl) ⟨115998, by rfl⟩ : syracuseStep 309329 = 231997) B231997
theorem B309347 : Blo 203807 309347 := bstep (se 1 (by rfl) ⟨232010, by rfl⟩ : syracuseStep 309347 = 464021) B464021
theorem B309377 : Blo 203807 309377 := bstep (se 2 (by rfl) ⟨116016, by rfl⟩ : syracuseStep 309377 = 232033) B232033
theorem B473219 : Blo 203807 473219 := bstep (se 1 (by rfl) ⟨354914, by rfl⟩ : syracuseStep 473219 = 709829) B709829
theorem B1423493 : Blo 203807 1423493 := bstep (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) B266905
theorem B309395 : Blo 203807 309395 := bstep (se 1 (by rfl) ⟨232046, by rfl⟩ : syracuseStep 309395 = 464093) B464093
theorem B309425 : Blo 203807 309425 := bstep (se 2 (by rfl) ⟨116034, by rfl⟩ : syracuseStep 309425 = 232069) B232069
theorem B309443 : Blo 203807 309443 := bstep (se 1 (by rfl) ⟨232082, by rfl⟩ : syracuseStep 309443 = 464165) B464165
theorem B309473 : Blo 203807 309473 := bstep (se 2 (by rfl) ⟨116052, by rfl⟩ : syracuseStep 309473 = 232105) B232105
theorem B309491 : Blo 203807 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B440579 : Blo 203807 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B309521 : Blo 203807 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B309539 : Blo 203807 309539 := bstep (se 1 (by rfl) ⟨232154, by rfl⟩ : syracuseStep 309539 = 464309) B464309
theorem B997667 : Blo 203807 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B309569 : Blo 203807 309569 := bstep (se 2 (by rfl) ⟨116088, by rfl⟩ : syracuseStep 309569 = 232177) B232177
theorem B309587 : Blo 203807 309587 := bstep (se 1 (by rfl) ⟨232190, by rfl⟩ : syracuseStep 309587 = 464381) B464381
theorem B309617 : Blo 203807 309617 := bstep (se 2 (by rfl) ⟨116106, by rfl⟩ : syracuseStep 309617 = 232213) B232213
theorem B309635 : Blo 203807 309635 := bstep (se 1 (by rfl) ⟨232226, by rfl⟩ : syracuseStep 309635 = 464453) B464453
theorem B309665 : Blo 203807 309665 := bstep (se 2 (by rfl) ⟨116124, by rfl⟩ : syracuseStep 309665 = 232249) B232249
theorem B309683 : Blo 203807 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B309713 : Blo 203807 309713 := bstep (se 2 (by rfl) ⟨116142, by rfl⟩ : syracuseStep 309713 = 232285) B232285
theorem B309731 : Blo 203807 309731 := bstep (se 1 (by rfl) ⟨232298, by rfl⟩ : syracuseStep 309731 = 464597) B464597
theorem B309761 : Blo 203807 309761 := bstep (se 2 (by rfl) ⟨116160, by rfl⟩ : syracuseStep 309761 = 232321) B232321
theorem B309779 : Blo 203807 309779 := bstep (se 1 (by rfl) ⟨232334, by rfl⟩ : syracuseStep 309779 = 464669) B464669
theorem B309809 : Blo 203807 309809 := bstep (se 2 (by rfl) ⟨116178, by rfl⟩ : syracuseStep 309809 = 232357) B232357
theorem B309827 : Blo 203807 309827 := bstep (se 1 (by rfl) ⟨232370, by rfl⟩ : syracuseStep 309827 = 464741) B464741
theorem B309857 : Blo 203807 309857 := bstep (se 2 (by rfl) ⟨116196, by rfl⟩ : syracuseStep 309857 = 232393) B232393
theorem B1751651 : Blo 203807 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B309875 : Blo 203807 309875 := bstep (se 1 (by rfl) ⟨232406, by rfl⟩ : syracuseStep 309875 = 464813) B464813
theorem B309905 : Blo 203807 309905 := bstep (se 2 (by rfl) ⟨116214, by rfl⟩ : syracuseStep 309905 = 232429) B232429
theorem B309923 : Blo 203807 309923 := bstep (se 1 (by rfl) ⟨232442, by rfl⟩ : syracuseStep 309923 = 464885) B464885
theorem B309953 : Blo 203807 309953 := bstep (se 2 (by rfl) ⟨116232, by rfl⟩ : syracuseStep 309953 = 232465) B232465
theorem B309971 : Blo 203807 309971 := bstep (se 1 (by rfl) ⟨232478, by rfl⟩ : syracuseStep 309971 = 464957) B464957
theorem B310001 : Blo 203807 310001 := bstep (se 2 (by rfl) ⟨116250, by rfl⟩ : syracuseStep 310001 = 232501) B232501
theorem B310019 : Blo 203807 310019 := bstep (se 1 (by rfl) ⟨232514, by rfl⟩ : syracuseStep 310019 = 465029) B465029
theorem B310049 : Blo 203807 310049 := bstep (se 2 (by rfl) ⟨116268, by rfl⟩ : syracuseStep 310049 = 232537) B232537
theorem B310067 : Blo 203807 310067 := bstep (se 1 (by rfl) ⟨232550, by rfl⟩ : syracuseStep 310067 = 465101) B465101
theorem B310097 : Blo 203807 310097 := bstep (se 2 (by rfl) ⟨116286, by rfl⟩ : syracuseStep 310097 = 232573) B232573
theorem B310115 : Blo 203807 310115 := bstep (se 1 (by rfl) ⟨232586, by rfl⟩ : syracuseStep 310115 = 465173) B465173
theorem B310145 : Blo 203807 310145 := bstep (se 2 (by rfl) ⟨116304, by rfl⟩ : syracuseStep 310145 = 232609) B232609
theorem B1424269 : Blo 203807 1424269 := bstep (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) B534101
theorem B310163 : Blo 203807 310163 := bstep (se 1 (by rfl) ⟨232622, by rfl⟩ : syracuseStep 310163 = 465245) B465245
theorem B310193 : Blo 203807 310193 := bstep (se 2 (by rfl) ⟨116322, by rfl⟩ : syracuseStep 310193 = 232645) B232645
theorem B310211 : Blo 203807 310211 := bstep (se 1 (by rfl) ⟨232658, by rfl⟩ : syracuseStep 310211 = 465317) B465317
theorem B310241 : Blo 203807 310241 := bstep (se 2 (by rfl) ⟨116340, by rfl⟩ : syracuseStep 310241 = 232681) B232681
theorem B310259 : Blo 203807 310259 := bstep (se 1 (by rfl) ⟨232694, by rfl⟩ : syracuseStep 310259 = 465389) B465389
theorem B310289 : Blo 203807 310289 := bstep (se 2 (by rfl) ⟨116358, by rfl⟩ : syracuseStep 310289 = 232717) B232717
theorem B441379 : Blo 203807 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B310307 : Blo 203807 310307 := bstep (se 1 (by rfl) ⟨232730, by rfl⟩ : syracuseStep 310307 = 465461) B465461
theorem B310337 : Blo 203807 310337 := bstep (se 2 (by rfl) ⟨116376, by rfl⟩ : syracuseStep 310337 = 232753) B232753
theorem B1621061 : Blo 203807 1621061 := bstep (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) B303949
theorem B441425 : Blo 203807 441425 := bstep (se 2 (by rfl) ⟨165534, by rfl⟩ : syracuseStep 441425 = 331069) B331069
theorem B310355 : Blo 203807 310355 := bstep (se 1 (by rfl) ⟨232766, by rfl⟩ : syracuseStep 310355 = 465533) B465533
theorem B310385 : Blo 203807 310385 := bstep (se 2 (by rfl) ⟨116394, by rfl⟩ : syracuseStep 310385 = 232789) B232789
theorem B310403 : Blo 203807 310403 := bstep (se 1 (by rfl) ⟨232802, by rfl⟩ : syracuseStep 310403 = 465605) B465605
theorem B310433 : Blo 203807 310433 := bstep (se 2 (by rfl) ⟨116412, by rfl⟩ : syracuseStep 310433 = 232825) B232825
theorem B310451 : Blo 203807 310451 := bstep (se 1 (by rfl) ⟨232838, by rfl⟩ : syracuseStep 310451 = 465677) B465677
theorem B998605 : Blo 203807 998605 := bstep (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) B374477
theorem B310481 : Blo 203807 310481 := bstep (se 2 (by rfl) ⟨116430, by rfl⟩ : syracuseStep 310481 = 232861) B232861
theorem B310499 : Blo 203807 310499 := bstep (se 1 (by rfl) ⟨232874, by rfl⟩ : syracuseStep 310499 = 465749) B465749
theorem B310529 : Blo 203807 310529 := bstep (se 2 (by rfl) ⟨116448, by rfl⟩ : syracuseStep 310529 = 232897) B232897
theorem B310547 : Blo 203807 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B310577 : Blo 203807 310577 := bstep (se 2 (by rfl) ⟨116466, by rfl⟩ : syracuseStep 310577 = 232933) B232933
theorem B310595 : Blo 203807 310595 := bstep (se 1 (by rfl) ⟨232946, by rfl⟩ : syracuseStep 310595 = 465893) B465893
theorem B310625 : Blo 203807 310625 := bstep (se 2 (by rfl) ⟨116484, by rfl⟩ : syracuseStep 310625 = 232969) B232969
theorem B310643 : Blo 203807 310643 := bstep (se 1 (by rfl) ⟨232982, by rfl⟩ : syracuseStep 310643 = 465965) B465965
theorem B310657 : Blo 203807 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B310673 : Blo 203807 310673 := bstep (se 2 (by rfl) ⟨116502, by rfl⟩ : syracuseStep 310673 = 233005) B233005
theorem B310691 : Blo 203807 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B310721 : Blo 203807 310721 := bstep (se 2 (by rfl) ⟨116520, by rfl⟩ : syracuseStep 310721 = 233041) B233041
theorem B310739 : Blo 203807 310739 := bstep (se 1 (by rfl) ⟨233054, by rfl⟩ : syracuseStep 310739 = 466109) B466109
theorem B310769 : Blo 203807 310769 := bstep (se 2 (by rfl) ⟨116538, by rfl⟩ : syracuseStep 310769 = 233077) B233077
theorem B310787 : Blo 203807 310787 := bstep (se 1 (by rfl) ⟨233090, by rfl⟩ : syracuseStep 310787 = 466181) B466181
theorem B310817 : Blo 203807 310817 := bstep (se 2 (by rfl) ⟨116556, by rfl⟩ : syracuseStep 310817 = 233113) B233113
theorem B310835 : Blo 203807 310835 := bstep (se 1 (by rfl) ⟨233126, by rfl⟩ : syracuseStep 310835 = 466253) B466253
theorem B310865 : Blo 203807 310865 := bstep (se 2 (by rfl) ⟨116574, by rfl⟩ : syracuseStep 310865 = 233149) B233149
theorem B310883 : Blo 203807 310883 := bstep (se 1 (by rfl) ⟨233162, by rfl⟩ : syracuseStep 310883 = 466325) B466325
theorem B310913 : Blo 203807 310913 := bstep (se 2 (by rfl) ⟨116592, by rfl⟩ : syracuseStep 310913 = 233185) B233185
theorem B310931 : Blo 203807 310931 := bstep (se 1 (by rfl) ⟨233198, by rfl⟩ : syracuseStep 310931 = 466397) B466397
theorem B310961 : Blo 203807 310961 := bstep (se 2 (by rfl) ⟨116610, by rfl⟩ : syracuseStep 310961 = 233221) B233221
theorem B310979 : Blo 203807 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B311009 : Blo 203807 311009 := bstep (se 2 (by rfl) ⟨116628, by rfl⟩ : syracuseStep 311009 = 233257) B233257
theorem B311027 : Blo 203807 311027 := bstep (se 1 (by rfl) ⟨233270, by rfl⟩ : syracuseStep 311027 = 466541) B466541
theorem B311057 : Blo 203807 311057 := bstep (se 2 (by rfl) ⟨116646, by rfl⟩ : syracuseStep 311057 = 233293) B233293
theorem B1392419 : Blo 203807 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B311075 : Blo 203807 311075 := bstep (se 1 (by rfl) ⟨233306, by rfl⟩ : syracuseStep 311075 = 466613) B466613
theorem B311105 : Blo 203807 311105 := bstep (se 2 (by rfl) ⟨116664, by rfl⟩ : syracuseStep 311105 = 233329) B233329
theorem B311123 : Blo 203807 311123 := bstep (se 1 (by rfl) ⟨233342, by rfl⟩ : syracuseStep 311123 = 466685) B466685
theorem B311153 : Blo 203807 311153 := bstep (se 2 (by rfl) ⟨116682, by rfl⟩ : syracuseStep 311153 = 233365) B233365
theorem B343939 : Blo 203807 343939 := bstep (se 1 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 343939 = 515909) B515909
theorem B311171 : Blo 203807 311171 := bstep (se 1 (by rfl) ⟨233378, by rfl⟩ : syracuseStep 311171 = 466757) B466757
theorem B311201 : Blo 203807 311201 := bstep (se 2 (by rfl) ⟨116700, by rfl⟩ : syracuseStep 311201 = 233401) B233401
theorem B311219 : Blo 203807 311219 := bstep (se 1 (by rfl) ⟨233414, by rfl⟩ : syracuseStep 311219 = 466829) B466829
theorem B311249 : Blo 203807 311249 := bstep (se 2 (by rfl) ⟨116718, by rfl⟩ : syracuseStep 311249 = 233437) B233437
theorem B835555 : Blo 203807 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B311267 : Blo 203807 311267 := bstep (se 1 (by rfl) ⟨233450, by rfl⟩ : syracuseStep 311267 = 466901) B466901
theorem B311297 : Blo 203807 311297 := bstep (se 2 (by rfl) ⟨116736, by rfl⟩ : syracuseStep 311297 = 233473) B233473
theorem B344081 : Blo 203807 344081 := bstep (se 2 (by rfl) ⟨129030, by rfl⟩ : syracuseStep 344081 = 258061) B258061
theorem B311315 : Blo 203807 311315 := bstep (se 1 (by rfl) ⟨233486, by rfl⟩ : syracuseStep 311315 = 466973) B466973
theorem B311345 : Blo 203807 311345 := bstep (se 2 (by rfl) ⟨116754, by rfl⟩ : syracuseStep 311345 = 233509) B233509
theorem B606275 : Blo 203807 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B311363 : Blo 203807 311363 := bstep (se 1 (by rfl) ⟨233522, by rfl⟩ : syracuseStep 311363 = 467045) B467045
theorem B311393 : Blo 203807 311393 := bstep (se 2 (by rfl) ⟨116772, by rfl⟩ : syracuseStep 311393 = 233545) B233545
theorem B311411 : Blo 203807 311411 := bstep (se 1 (by rfl) ⟨233558, by rfl⟩ : syracuseStep 311411 = 467117) B467117
theorem B344209 : Blo 203807 344209 := bstep (se 2 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 344209 = 258157) B258157
theorem B311441 : Blo 203807 311441 := bstep (se 2 (by rfl) ⟨116790, by rfl⟩ : syracuseStep 311441 = 233581) B233581
theorem B311459 : Blo 203807 311459 := bstep (se 1 (by rfl) ⟨233594, by rfl⟩ : syracuseStep 311459 = 467189) B467189
theorem B344243 : Blo 203807 344243 := bstep (se 1 (by rfl) ⟨258182, by rfl⟩ : syracuseStep 344243 = 516365) B516365
theorem B311489 : Blo 203807 311489 := bstep (se 2 (by rfl) ⟨116808, by rfl⟩ : syracuseStep 311489 = 233617) B233617
theorem B311507 : Blo 203807 311507 := bstep (se 1 (by rfl) ⟨233630, by rfl⟩ : syracuseStep 311507 = 467261) B467261
theorem B311537 : Blo 203807 311537 := bstep (se 2 (by rfl) ⟨116826, by rfl⟩ : syracuseStep 311537 = 233653) B233653
theorem B246019 : Blo 203807 246019 := bstep (se 1 (by rfl) ⟨184514, by rfl⟩ : syracuseStep 246019 = 369029) B369029
theorem B311555 : Blo 203807 311555 := bstep (se 1 (by rfl) ⟨233666, by rfl⟩ : syracuseStep 311555 = 467333) B467333
theorem B1327373 : Blo 203807 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B311585 : Blo 203807 311585 := bstep (se 2 (by rfl) ⟨116844, by rfl⟩ : syracuseStep 311585 = 233689) B233689
theorem B344371 : Blo 203807 344371 := bstep (se 1 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 344371 = 516557) B516557
theorem B311603 : Blo 203807 311603 := bstep (se 1 (by rfl) ⟨233702, by rfl⟩ : syracuseStep 311603 = 467405) B467405
theorem B311633 : Blo 203807 311633 := bstep (se 2 (by rfl) ⟨116862, by rfl⟩ : syracuseStep 311633 = 233725) B233725
theorem B311635 : Blo 203807 311635 := bstep (se 1 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 311635 = 467453) B467453
theorem B246115 : Blo 203807 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B311651 : Blo 203807 311651 := bstep (se 1 (by rfl) ⟨233738, by rfl⟩ : syracuseStep 311651 = 467477) B467477
theorem B311681 : Blo 203807 311681 := bstep (se 2 (by rfl) ⟨116880, by rfl⟩ : syracuseStep 311681 = 233761) B233761
theorem B246163 : Blo 203807 246163 := bstep (se 1 (by rfl) ⟨184622, by rfl⟩ : syracuseStep 246163 = 369245) B369245
theorem B311699 : Blo 203807 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B344513 : Blo 203807 344513 := bstep (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) B258385
theorem B311825 : Blo 203807 311825 := bstep (se 2 (by rfl) ⟨116934, by rfl⟩ : syracuseStep 311825 = 233869) B233869
theorem B344641 : Blo 203807 344641 := bstep (se 2 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 344641 = 258481) B258481
theorem B344675 : Blo 203807 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B344803 : Blo 203807 344803 := bstep (se 1 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 344803 = 517205) B517205
theorem B443107 : Blo 203807 443107 := bstep (se 1 (by rfl) ⟨332330, by rfl⟩ : syracuseStep 443107 = 664661) B664661
theorem B1262405 : Blo 203807 1262405 := bstep (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) B236701
theorem B1033073 : Blo 203807 1033073 := bstep (se 2 (by rfl) ⟨387402, by rfl⟩ : syracuseStep 1033073 = 774805) B774805
theorem B344945 : Blo 203807 344945 := bstep (se 2 (by rfl) ⟨129354, by rfl⟩ : syracuseStep 344945 = 258709) B258709
theorem B345073 : Blo 203807 345073 := bstep (se 2 (by rfl) ⟨129402, by rfl⟩ : syracuseStep 345073 = 258805) B258805
theorem B345107 : Blo 203807 345107 := bstep (se 1 (by rfl) ⟨258830, by rfl⟩ : syracuseStep 345107 = 517661) B517661
theorem B345235 : Blo 203807 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B443569 : Blo 203807 443569 := bstep (se 2 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 443569 = 332677) B332677
theorem B705809 : Blo 203807 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B345377 : Blo 203807 345377 := bstep (se 2 (by rfl) ⟨129516, by rfl⟩ : syracuseStep 345377 = 259033) B259033
theorem B279875 : Blo 203807 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B345505 : Blo 203807 345505 := bstep (se 2 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 345505 = 259129) B259129
theorem B607651 : Blo 203807 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B345539 : Blo 203807 345539 := bstep (se 1 (by rfl) ⟨259154, by rfl⟩ : syracuseStep 345539 = 518309) B518309
theorem B673283 : Blo 203807 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B706051 : Blo 203807 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B345667 : Blo 203807 345667 := bstep (se 1 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 345667 = 518501) B518501
theorem B247379 : Blo 203807 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B1558115 : Blo 203807 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B345809 : Blo 203807 345809 := bstep (se 2 (by rfl) ⟨129678, by rfl⟩ : syracuseStep 345809 = 259357) B259357
theorem B345937 : Blo 203807 345937 := bstep (se 2 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 345937 = 259453) B259453
theorem B345971 : Blo 203807 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B378769 : Blo 203807 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B346099 : Blo 203807 346099 := bstep (se 1 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 346099 = 519149) B519149
theorem B280577 : Blo 203807 280577 := bstep (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) B210433
theorem B346241 : Blo 203807 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B870563 : Blo 203807 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B346369 : Blo 203807 346369 := bstep (se 2 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 346369 = 259777) B259777
theorem B1132805 : Blo 203807 1132805 := bstep (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) B212401
theorem B1034531 : Blo 203807 1034531 := bstep (se 1 (by rfl) ⟨775898, by rfl⟩ : syracuseStep 1034531 = 1551797) B1551797
theorem B346403 : Blo 203807 346403 := bstep (se 1 (by rfl) ⟨259802, by rfl⟩ : syracuseStep 346403 = 519605) B519605
theorem B346531 : Blo 203807 346531 := bstep (se 1 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 346531 = 519797) B519797
theorem B1329605 : Blo 203807 1329605 := bstep (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) B249301
theorem B346673 : Blo 203807 346673 := bstep (se 2 (by rfl) ⟨130002, by rfl⟩ : syracuseStep 346673 = 260005) B260005
theorem B346801 : Blo 203807 346801 := bstep (se 2 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 346801 = 260101) B260101
theorem B346835 : Blo 203807 346835 := bstep (se 1 (by rfl) ⟨260126, by rfl⟩ : syracuseStep 346835 = 520253) B520253
theorem B346963 : Blo 203807 346963 := bstep (se 1 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 346963 = 520445) B520445
theorem B347105 : Blo 203807 347105 := bstep (se 2 (by rfl) ⟨130164, by rfl⟩ : syracuseStep 347105 = 260329) B260329
theorem B838669 : Blo 203807 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B2018317 : Blo 203807 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B1035341 : Blo 203807 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B347233 : Blo 203807 347233 := bstep (se 2 (by rfl) ⟨130212, by rfl⟩ : syracuseStep 347233 = 260425) B260425
theorem B347267 : Blo 203807 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B347395 : Blo 203807 347395 := bstep (se 1 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 347395 = 521093) B521093
theorem B871793 : Blo 203807 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B5000561 : Blo 203807 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B347537 : Blo 203807 347537 := bstep (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) B260653
theorem B347665 : Blo 203807 347665 := bstep (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) B260749
theorem B347699 : Blo 203807 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B4247153 : Blo 203807 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B347827 : Blo 203807 347827 := bstep (se 1 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 347827 = 521741) B521741
theorem B347969 : Blo 203807 347969 := bstep (se 2 (by rfl) ⟨130488, by rfl⟩ : syracuseStep 347969 = 260977) B260977
theorem B348097 : Blo 203807 348097 := bstep (se 2 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 348097 = 261073) B261073
theorem B348131 : Blo 203807 348131 := bstep (se 1 (by rfl) ⟨261098, by rfl⟩ : syracuseStep 348131 = 522197) B522197
theorem B348259 : Blo 203807 348259 := bstep (se 1 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 348259 = 522389) B522389
theorem B1167493 : Blo 203807 1167493 := bstep (se 4 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 1167493 = 218905) B218905
theorem B446627 : Blo 203807 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B1069283 : Blo 203807 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B348401 : Blo 203807 348401 := bstep (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) B261301
theorem B348529 : Blo 203807 348529 := bstep (se 2 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 348529 = 261397) B261397
theorem B348563 : Blo 203807 348563 := bstep (se 1 (by rfl) ⟨261422, by rfl⟩ : syracuseStep 348563 = 522845) B522845
theorem B348691 : Blo 203807 348691 := bstep (se 1 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 348691 = 523037) B523037
theorem B348833 : Blo 203807 348833 := bstep (se 2 (by rfl) ⟨130812, by rfl⟩ : syracuseStep 348833 = 261625) B261625
theorem B1102499 : Blo 203807 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B348961 : Blo 203807 348961 := bstep (se 2 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 348961 = 261721) B261721
theorem B348995 : Blo 203807 348995 := bstep (se 1 (by rfl) ⟨261746, by rfl⟩ : syracuseStep 348995 = 523493) B523493
theorem B349123 : Blo 203807 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B349265 : Blo 203807 349265 := bstep (se 2 (by rfl) ⟨130974, by rfl⟩ : syracuseStep 349265 = 261949) B261949
theorem B349393 : Blo 203807 349393 := bstep (se 2 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 349393 = 262045) B262045
theorem B349427 : Blo 203807 349427 := bstep (se 1 (by rfl) ⟨262070, by rfl⟩ : syracuseStep 349427 = 524141) B524141
theorem B283969 : Blo 203807 283969 := bstep (se 2 (by rfl) ⟨106488, by rfl⟩ : syracuseStep 283969 = 212977) B212977
theorem B349555 : Blo 203807 349555 := bstep (se 1 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 349555 = 524333) B524333
theorem B775565 : Blo 203807 775565 := bstep (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) B290837
theorem B349697 : Blo 203807 349697 := bstep (se 2 (by rfl) ⟨131136, by rfl⟩ : syracuseStep 349697 = 262273) B262273
theorem B349825 : Blo 203807 349825 := bstep (se 2 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 349825 = 262369) B262369
theorem B349859 : Blo 203807 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B218867 : Blo 203807 218867 := bstep (se 1 (by rfl) ⟨164150, by rfl⟩ : syracuseStep 218867 = 328301) B328301
theorem B874253 : Blo 203807 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B349987 : Blo 203807 349987 := bstep (se 1 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 349987 = 524981) B524981
theorem B1038257 : Blo 203807 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B350129 : Blo 203807 350129 := bstep (se 2 (by rfl) ⟨131298, by rfl⟩ : syracuseStep 350129 = 262597) B262597
theorem B841699 : Blo 203807 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B350257 : Blo 203807 350257 := bstep (se 2 (by rfl) ⟨131346, by rfl⟩ : syracuseStep 350257 = 262693) B262693
theorem B1169477 : Blo 203807 1169477 := bstep (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) B219277
theorem B350291 : Blo 203807 350291 := bstep (se 1 (by rfl) ⟨262718, by rfl⟩ : syracuseStep 350291 = 525437) B525437
theorem B350419 : Blo 203807 350419 := bstep (se 1 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 350419 = 525629) B525629
theorem B1267939 : Blo 203807 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B350561 : Blo 203807 350561 := bstep (se 2 (by rfl) ⟨131460, by rfl⟩ : syracuseStep 350561 = 262921) B262921
theorem B416195 : Blo 203807 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B219619 : Blo 203807 219619 := bstep (se 1 (by rfl) ⟨164714, by rfl⟩ : syracuseStep 219619 = 329429) B329429
theorem B1759715 : Blo 203807 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1563461 : Blo 203807 1563461 := bstep (se 4 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 1563461 = 293149) B293149
theorem B1661795 : Blo 203807 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B580547 : Blo 203807 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B1006769 : Blo 203807 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1105093 : Blo 203807 1105093 := bstep (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) B207205
theorem B580877 : Blo 203807 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B580945 : Blo 203807 580945 := bstep (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) B435709
theorem B1039715 : Blo 203807 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B220691 : Blo 203807 220691 := bstep (se 1 (by rfl) ⟨165518, by rfl⟩ : syracuseStep 220691 = 331037) B331037
theorem B581219 : Blo 203807 581219 := bstep (se 1 (by rfl) ⟨435914, by rfl⟩ : syracuseStep 581219 = 871829) B871829
theorem B745379 : Blo 203807 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B1138637 : Blo 203807 1138637 := bstep (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) B426989
theorem B417841 : Blo 203807 417841 := bstep (se 2 (by rfl) ⟨156690, by rfl⟩ : syracuseStep 417841 = 313381) B313381
theorem B1040525 : Blo 203807 1040525 := bstep (se 3 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 1040525 = 390197) B390197
theorem B778481 : Blo 203807 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B942349 : Blo 203807 942349 := bstep (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) B353381
theorem B582061 : Blo 203807 582061 := bstep (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) B218273
theorem B582221 : Blo 203807 582221 := bstep (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) B218333
theorem B516689 : Blo 203807 516689 := bstep (se 2 (by rfl) ⟨193758, by rfl⟩ : syracuseStep 516689 = 387517) B387517
theorem B1401457 : Blo 203807 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B516739 : Blo 203807 516739 := bstep (se 1 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 516739 = 775109) B775109
theorem B221827 : Blo 203807 221827 := bstep (se 1 (by rfl) ⟨166370, by rfl⟩ : syracuseStep 221827 = 332741) B332741
theorem B582403 : Blo 203807 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B516881 : Blo 203807 516881 := bstep (se 2 (by rfl) ⟨193830, by rfl⟩ : syracuseStep 516881 = 387661) B387661
theorem B418627 : Blo 203807 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B746417 : Blo 203807 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B1238321 : Blo 203807 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B779939 : Blo 203807 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B517873 : Blo 203807 517873 := bstep (se 2 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 517873 = 388405) B388405
theorem B1173325 : Blo 203807 1173325 := bstep (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) B439997
theorem B419665 : Blo 203807 419665 := bstep (se 2 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 419665 = 314749) B314749
theorem B386947 : Blo 203807 386947 := bstep (se 1 (by rfl) ⟨290210, by rfl⟩ : syracuseStep 386947 = 580421) B580421
theorem B386993 : Blo 203807 386993 := bstep (se 2 (by rfl) ⟨145122, by rfl⟩ : syracuseStep 386993 = 290245) B290245
theorem B518147 : Blo 203807 518147 := bstep (se 1 (by rfl) ⟨388610, by rfl⟩ : syracuseStep 518147 = 777221) B777221
theorem B878627 : Blo 203807 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B583793 : Blo 203807 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B518339 : Blo 203807 518339 := bstep (se 1 (by rfl) ⟨388754, by rfl⟩ : syracuseStep 518339 = 777509) B777509
theorem B387281 : Blo 203807 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B4483349 : Blo 203807 4483349 := bstep (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) B210157
theorem B747917 : Blo 203807 747917 := bstep (se 3 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 747917 = 280469) B280469
theorem B551501 : Blo 203807 551501 := bstep (se 3 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 551501 = 206813) B206813
theorem B780941 : Blo 203807 780941 := bstep (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) B292853
theorem B388003 : Blo 203807 388003 := bstep (se 1 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 388003 = 582005) B582005
theorem B1043441 : Blo 203807 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B584749 : Blo 203807 584749 := bstep (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) B219281
theorem B519281 : Blo 203807 519281 := bstep (se 2 (by rfl) ⟨194730, by rfl⟩ : syracuseStep 519281 = 389461) B389461
theorem B519331 : Blo 203807 519331 := bstep (se 1 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 519331 = 778997) B778997
theorem B584977 : Blo 203807 584977 := bstep (se 2 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 584977 = 438733) B438733
theorem B519473 : Blo 203807 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B388451 : Blo 203807 388451 := bstep (se 1 (by rfl) ⟨291338, by rfl⟩ : syracuseStep 388451 = 582677) B582677
theorem B585137 : Blo 203807 585137 := bstep (se 2 (by rfl) ⟨219426, by rfl⟩ : syracuseStep 585137 = 438853) B438853
theorem B585251 : Blo 203807 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B388739 : Blo 203807 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B1175309 : Blo 203807 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B290803 : Blo 203807 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B1667213 : Blo 203807 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B520465 : Blo 203807 520465 := bstep (se 2 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 520465 = 390349) B390349
theorem B1044899 : Blo 203807 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B291281 : Blo 203807 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B258547 : Blo 203807 258547 := bstep (se 1 (by rfl) ⟨193910, by rfl⟩ : syracuseStep 258547 = 387821) B387821
theorem B586253 : Blo 203807 586253 := bstep (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) B219845
theorem B1569293 : Blo 203807 1569293 := bstep (se 3 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 1569293 = 588485) B588485
theorem B520739 : Blo 203807 520739 := bstep (se 1 (by rfl) ⟨390554, by rfl⟩ : syracuseStep 520739 = 781109) B781109
theorem B389681 : Blo 203807 389681 := bstep (se 2 (by rfl) ⟨146130, by rfl⟩ : syracuseStep 389681 = 292261) B292261
theorem B291395 : Blo 203807 291395 := bstep (se 1 (by rfl) ⟨218546, by rfl⟩ : syracuseStep 291395 = 437093) B437093
theorem B258643 : Blo 203807 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B881293 : Blo 203807 881293 := bstep (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) B330485
theorem B291475 : Blo 203807 291475 := bstep (se 1 (by rfl) ⟨218606, by rfl⟩ : syracuseStep 291475 = 437213) B437213
theorem B1176241 : Blo 203807 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B586435 : Blo 203807 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B783053 : Blo 203807 783053 := bstep (se 3 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 783053 = 293645) B293645
theorem B520931 : Blo 203807 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B5206837 : Blo 203807 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B1307461 : Blo 203807 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B586595 : Blo 203807 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B259139 : Blo 203807 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B1537165 : Blo 203807 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B292033 : Blo 203807 292033 := bstep (se 2 (by rfl) ⟨109512, by rfl⟩ : syracuseStep 292033 = 219025) B219025
theorem B1045709 : Blo 203807 1045709 := bstep (se 3 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 1045709 = 392141) B392141
theorem B390577 : Blo 203807 390577 := bstep (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) B292933
theorem B783857 : Blo 203807 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B390737 : Blo 203807 390737 := bstep (se 2 (by rfl) ⟨146526, by rfl⟩ : syracuseStep 390737 = 293053) B293053
theorem B521873 : Blo 203807 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B1111715 : Blo 203807 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B882353 : Blo 203807 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B521923 : Blo 203807 521923 := bstep (se 1 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 521923 = 782885) B782885
theorem B554701 : Blo 203807 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B259843 : Blo 203807 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B522065 : Blo 203807 522065 := bstep (se 2 (by rfl) ⟨195774, by rfl⟩ : syracuseStep 522065 = 391549) B391549
theorem B259939 : Blo 203807 259939 := bstep (se 1 (by rfl) ⟨194954, by rfl⟩ : syracuseStep 259939 = 389909) B389909
theorem B292739 : Blo 203807 292739 := bstep (se 1 (by rfl) ⟨219554, by rfl⟩ : syracuseStep 292739 = 439109) B439109
theorem B587665 : Blo 203807 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B391139 : Blo 203807 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B751693 : Blo 203807 751693 := bstep (se 3 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 751693 = 281885) B281885
theorem B1177699 : Blo 203807 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B784525 : Blo 203807 784525 := bstep (se 3 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 784525 = 294197) B294197
theorem B260435 : Blo 203807 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B653795 : Blo 203807 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B293377 : Blo 203807 293377 := bstep (se 2 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 293377 = 220033) B220033
theorem B1178225 : Blo 203807 1178225 := bstep (se 2 (by rfl) ⟨441834, by rfl⟩ : syracuseStep 1178225 = 883669) B883669
theorem B293491 : Blo 203807 293491 := bstep (se 1 (by rfl) ⟨220118, by rfl⟩ : syracuseStep 293491 = 440237) B440237
theorem B523057 : Blo 203807 523057 := bstep (se 2 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 523057 = 392293) B392293
theorem B392035 : Blo 203807 392035 := bstep (se 1 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 392035 = 588053) B588053
theorem B326513 : Blo 203807 326513 := bstep (se 2 (by rfl) ⟨122442, by rfl⟩ : syracuseStep 326513 = 244885) B244885
theorem B588689 : Blo 203807 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B785315 : Blo 203807 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B2489285 : Blo 203807 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B392195 : Blo 203807 392195 := bstep (se 1 (by rfl) ⟨294146, by rfl⟩ : syracuseStep 392195 = 588293) B588293
theorem B1113101 : Blo 203807 1113101 := bstep (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) B417413
theorem B261139 : Blo 203807 261139 := bstep (se 1 (by rfl) ⟨195854, by rfl⟩ : syracuseStep 261139 = 391709) B391709
theorem B523331 : Blo 203807 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B261235 : Blo 203807 261235 := bstep (se 1 (by rfl) ⟨195926, by rfl⟩ : syracuseStep 261235 = 391853) B391853
theorem B588941 : Blo 203807 588941 := bstep (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) B220853
theorem B621713 : Blo 203807 621713 := bstep (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) B466285
theorem B654563 : Blo 203807 654563 := bstep (se 1 (by rfl) ⟨490922, by rfl⟩ : syracuseStep 654563 = 981845) B981845
theorem B523523 : Blo 203807 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B490769 : Blo 203807 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B589123 : Blo 203807 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B327025 : Blo 203807 327025 := bstep (se 2 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 327025 = 245269) B245269
theorem B589169 : Blo 203807 589169 := bstep (se 2 (by rfl) ⟨220938, by rfl⟩ : syracuseStep 589169 = 441877) B441877
theorem B1572209 : Blo 203807 1572209 := bstep (se 2 (by rfl) ⟨589578, by rfl⟩ : syracuseStep 1572209 = 1179157) B1179157
theorem B490961 : Blo 203807 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B785969 : Blo 203807 785969 := bstep (se 2 (by rfl) ⟨294738, by rfl⟩ : syracuseStep 785969 = 589477) B589477
theorem B261731 : Blo 203807 261731 := bstep (se 1 (by rfl) ⟨196298, by rfl⟩ : syracuseStep 261731 = 392597) B392597
theorem B654961 : Blo 203807 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B1048241 : Blo 203807 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B655075 : Blo 203807 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B3604337 : Blo 203807 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B688013 : Blo 203807 688013 := bstep (se 3 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 688013 = 258005) B258005
theorem B294835 : Blo 203807 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B229315 : Blo 203807 229315 := bstep (se 1 (by rfl) ⟨171986, by rfl⟩ : syracuseStep 229315 = 343973) B343973
theorem B688067 : Blo 203807 688067 := bstep (se 1 (by rfl) ⟨516050, by rfl⟩ : syracuseStep 688067 = 1032101) B1032101
theorem B327635 : Blo 203807 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B229387 : Blo 203807 229387 := bstep (se 1 (by rfl) ⟨172040, by rfl⟩ : syracuseStep 229387 = 344081) B344081
theorem B786455 : Blo 203807 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B524353 : Blo 203807 524353 := bstep (se 2 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 524353 = 393265) B393265
theorem B229495 : Blo 203807 229495 := bstep (se 1 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 229495 = 344243) B344243
theorem B458891 : Blo 203807 458891 := bstep (se 1 (by rfl) ⟨344168, by rfl⟩ : syracuseStep 458891 = 688337) B688337
theorem B884915 : Blo 203807 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B458945 : Blo 203807 458945 := bstep (se 2 (by rfl) ⟨172104, by rfl⟩ : syracuseStep 458945 = 344209) B344209
theorem B393419 : Blo 203807 393419 := bstep (se 1 (by rfl) ⟨295064, by rfl⟩ : syracuseStep 393419 = 590129) B590129
theorem B655577 : Blo 203807 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B2228485 : Blo 203807 2228485 := bstep (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) B417841
theorem B229675 : Blo 203807 229675 := bstep (se 1 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 229675 = 344513) B344513
theorem B328025 : Blo 203807 328025 := bstep (se 2 (by rfl) ⟨123009, by rfl⟩ : syracuseStep 328025 = 246019) B246019
theorem B229783 : Blo 203807 229783 := bstep (se 1 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 229783 = 344675) B344675
theorem B459161 : Blo 203807 459161 := bstep (se 2 (by rfl) ⟨172185, by rfl⟩ : syracuseStep 459161 = 344371) B344371
theorem B328153 : Blo 203807 328153 := bstep (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) B246115
theorem B623065 : Blo 203807 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B459251 : Blo 203807 459251 := bstep (se 1 (by rfl) ⟨344438, by rfl⟩ : syracuseStep 459251 = 688877) B688877
theorem B459287 : Blo 203807 459287 := bstep (se 1 (by rfl) ⟨344465, by rfl⟩ : syracuseStep 459287 = 688931) B688931
theorem B655895 : Blo 203807 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B328217 : Blo 203807 328217 := bstep (se 2 (by rfl) ⟨123081, by rfl⟩ : syracuseStep 328217 = 246163) B246163
theorem B393751 : Blo 203807 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B688715 : Blo 203807 688715 := bstep (se 1 (by rfl) ⟨516536, by rfl⟩ : syracuseStep 688715 = 1033073) B1033073
theorem B229963 : Blo 203807 229963 := bstep (se 1 (by rfl) ⟨172472, by rfl⟩ : syracuseStep 229963 = 344945) B344945
theorem B754265 : Blo 203807 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B2851421 : Blo 203807 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B524951 : Blo 203807 524951 := bstep (se 1 (by rfl) ⟨393713, by rfl⟩ : syracuseStep 524951 = 787427) B787427
theorem B230071 : Blo 203807 230071 := bstep (se 1 (by rfl) ⟨172553, by rfl⟩ : syracuseStep 230071 = 345107) B345107
theorem B459467 : Blo 203807 459467 := bstep (se 1 (by rfl) ⟨344600, by rfl⟩ : syracuseStep 459467 = 689201) B689201
theorem B459521 : Blo 203807 459521 := bstep (se 2 (by rfl) ⟨172320, by rfl⟩ : syracuseStep 459521 = 344641) B344641
theorem B1180433 : Blo 203807 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1573667 : Blo 203807 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B1868609 : Blo 203807 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B656203 : Blo 203807 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B1114955 : Blo 203807 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B688985 : Blo 203807 688985 := bstep (se 2 (by rfl) ⟨258369, by rfl⟩ : syracuseStep 688985 = 516739) B516739
theorem B295769 : Blo 203807 295769 := bstep (se 2 (by rfl) ⟨110913, by rfl⟩ : syracuseStep 295769 = 221827) B221827
theorem B230251 : Blo 203807 230251 := bstep (se 1 (by rfl) ⟨172688, by rfl⟩ : syracuseStep 230251 = 345377) B345377
theorem B230359 : Blo 203807 230359 := bstep (se 1 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 230359 = 345539) B345539
theorem B459737 : Blo 203807 459737 := bstep (se 2 (by rfl) ⟨172401, by rfl⟩ : syracuseStep 459737 = 344803) B344803
theorem B590809 : Blo 203807 590809 := bstep (se 2 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 590809 = 443107) B443107
theorem B459827 : Blo 203807 459827 := bstep (se 1 (by rfl) ⟨344870, by rfl⟩ : syracuseStep 459827 = 689741) B689741
theorem B459863 : Blo 203807 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B230539 : Blo 203807 230539 := bstep (se 1 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 230539 = 345809) B345809
theorem B1180889 : Blo 203807 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B230647 : Blo 203807 230647 := bstep (se 1 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 230647 = 345971) B345971
theorem B787715 : Blo 203807 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B460043 : Blo 203807 460043 := bstep (se 1 (by rfl) ⟨345032, by rfl⟩ : syracuseStep 460043 = 690065) B690065
theorem B460097 : Blo 203807 460097 := bstep (se 2 (by rfl) ⟨172536, by rfl⟩ : syracuseStep 460097 = 345073) B345073
theorem B1049921 : Blo 203807 1049921 := bstep (se 2 (by rfl) ⟨393720, by rfl⟩ : syracuseStep 1049921 = 787441) B787441
theorem B230827 : Blo 203807 230827 := bstep (se 1 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 230827 = 346241) B346241
theorem B656819 : Blo 203807 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B525761 : Blo 203807 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B755203 : Blo 203807 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B689687 : Blo 203807 689687 := bstep (se 1 (by rfl) ⟨517265, by rfl⟩ : syracuseStep 689687 = 1034531) B1034531
theorem B230935 : Blo 203807 230935 := bstep (se 1 (by rfl) ⟨173201, by rfl⟩ : syracuseStep 230935 = 346403) B346403
theorem B460313 : Blo 203807 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B591425 : Blo 203807 591425 := bstep (se 2 (by rfl) ⟨221784, by rfl⟩ : syracuseStep 591425 = 443569) B443569
theorem B460403 : Blo 203807 460403 := bstep (se 1 (by rfl) ⟨345302, by rfl⟩ : syracuseStep 460403 = 690605) B690605
theorem B886403 : Blo 203807 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B460439 : Blo 203807 460439 := bstep (se 1 (by rfl) ⟨345329, by rfl⟩ : syracuseStep 460439 = 690659) B690659
theorem B493249 : Blo 203807 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B231115 : Blo 203807 231115 := bstep (se 1 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 231115 = 346673) B346673
theorem B231223 : Blo 203807 231223 := bstep (se 1 (by rfl) ⟨173417, by rfl⟩ : syracuseStep 231223 = 346835) B346835
theorem B460619 : Blo 203807 460619 := bstep (se 1 (by rfl) ⟨345464, by rfl⟩ : syracuseStep 460619 = 690929) B690929
theorem B460673 : Blo 203807 460673 := bstep (se 2 (by rfl) ⟨172752, by rfl⟩ : syracuseStep 460673 = 345505) B345505
theorem B526297 : Blo 203807 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B231403 : Blo 203807 231403 := bstep (se 1 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 231403 = 347105) B347105
theorem B690227 : Blo 203807 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B231511 : Blo 203807 231511 := bstep (se 1 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 231511 = 347267) B347267
theorem B460889 : Blo 203807 460889 := bstep (se 2 (by rfl) ⟨172833, by rfl⟩ : syracuseStep 460889 = 345667) B345667
theorem B1312919 : Blo 203807 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B460979 : Blo 203807 460979 := bstep (se 1 (by rfl) ⟨345734, by rfl⟩ : syracuseStep 460979 = 691469) B691469
theorem B461015 : Blo 203807 461015 := bstep (se 1 (by rfl) ⟨345761, by rfl⟩ : syracuseStep 461015 = 691523) B691523
theorem B231691 : Blo 203807 231691 := bstep (se 1 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 231691 = 347537) B347537
theorem B690497 : Blo 203807 690497 := bstep (se 2 (by rfl) ⟨258936, by rfl⟩ : syracuseStep 690497 = 517873) B517873
theorem B493913 : Blo 203807 493913 := bstep (se 2 (by rfl) ⟨185217, by rfl⟩ : syracuseStep 493913 = 370435) B370435
theorem B231799 : Blo 203807 231799 := bstep (se 1 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 231799 = 347699) B347699
theorem B461195 : Blo 203807 461195 := bstep (se 1 (by rfl) ⟨345896, by rfl⟩ : syracuseStep 461195 = 691793) B691793
theorem B461249 : Blo 203807 461249 := bstep (se 2 (by rfl) ⟨172968, by rfl⟩ : syracuseStep 461249 = 345937) B345937
theorem B559553 : Blo 203807 559553 := bstep (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) B419665
theorem B231979 : Blo 203807 231979 := bstep (se 1 (by rfl) ⟨173984, by rfl⟩ : syracuseStep 231979 = 347969) B347969
theorem B1116773 : Blo 203807 1116773 := bstep (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) B209395
theorem B232087 : Blo 203807 232087 := bstep (se 1 (by rfl) ⟨174065, by rfl⟩ : syracuseStep 232087 = 348131) B348131
theorem B461465 : Blo 203807 461465 := bstep (se 2 (by rfl) ⟨173049, by rfl⟩ : syracuseStep 461465 = 346099) B346099
theorem B461555 : Blo 203807 461555 := bstep (se 1 (by rfl) ⟨346166, by rfl⟩ : syracuseStep 461555 = 692333) B692333
theorem B461591 : Blo 203807 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B297751 : Blo 203807 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B232267 : Blo 203807 232267 := bstep (se 1 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 232267 = 348401) B348401
theorem B691037 : Blo 203807 691037 := bstep (se 3 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 691037 = 259139) B259139
theorem B1182595 : Blo 203807 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B232375 : Blo 203807 232375 := bstep (se 1 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 232375 = 348563) B348563
theorem B461771 : Blo 203807 461771 := bstep (se 1 (by rfl) ⟨346328, by rfl⟩ : syracuseStep 461771 = 692657) B692657
theorem B461825 : Blo 203807 461825 := bstep (se 2 (by rfl) ⟨173184, by rfl⟩ : syracuseStep 461825 = 346369) B346369
theorem B232555 : Blo 203807 232555 := bstep (se 1 (by rfl) ⟨174416, by rfl⟩ : syracuseStep 232555 = 348833) B348833
theorem B232663 : Blo 203807 232663 := bstep (se 1 (by rfl) ⟨174497, by rfl⟩ : syracuseStep 232663 = 348995) B348995
theorem B462041 : Blo 203807 462041 := bstep (se 2 (by rfl) ⟨173265, by rfl⟩ : syracuseStep 462041 = 346531) B346531
theorem B1051865 : Blo 203807 1051865 := bstep (se 2 (by rfl) ⟨394449, by rfl⟩ : syracuseStep 1051865 = 788899) B788899
theorem B265483 : Blo 203807 265483 := bstep (se 1 (by rfl) ⟨199112, by rfl⟩ : syracuseStep 265483 = 398225) B398225
theorem B462131 : Blo 203807 462131 := bstep (se 1 (by rfl) ⟨346598, by rfl⟩ : syracuseStep 462131 = 693197) B693197
theorem B462167 : Blo 203807 462167 := bstep (se 1 (by rfl) ⟨346625, by rfl⟩ : syracuseStep 462167 = 693251) B693251
theorem B232843 : Blo 203807 232843 := bstep (se 1 (by rfl) ⟨174632, by rfl⟩ : syracuseStep 232843 = 349265) B349265
theorem B232951 : Blo 203807 232951 := bstep (se 1 (by rfl) ⟨174713, by rfl⟩ : syracuseStep 232951 = 349427) B349427
theorem B462347 : Blo 203807 462347 := bstep (se 1 (by rfl) ⟨346760, by rfl⟩ : syracuseStep 462347 = 693521) B693521
theorem B462401 : Blo 203807 462401 := bstep (se 2 (by rfl) ⟨173400, by rfl⟩ : syracuseStep 462401 = 346801) B346801
theorem B233131 : Blo 203807 233131 := bstep (se 1 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 233131 = 349697) B349697
theorem B233239 : Blo 203807 233239 := bstep (se 1 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 233239 = 349859) B349859
theorem B462617 : Blo 203807 462617 := bstep (se 2 (by rfl) ⟨173481, by rfl⟩ : syracuseStep 462617 = 346963) B346963
theorem B462707 : Blo 203807 462707 := bstep (se 1 (by rfl) ⟨347030, by rfl⟩ : syracuseStep 462707 = 694061) B694061
theorem B462743 : Blo 203807 462743 := bstep (se 1 (by rfl) ⟨347057, by rfl⟩ : syracuseStep 462743 = 694115) B694115
theorem B692171 : Blo 203807 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B233419 : Blo 203807 233419 := bstep (se 1 (by rfl) ⟨175064, by rfl⟩ : syracuseStep 233419 = 350129) B350129
theorem B1118225 : Blo 203807 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B2691089 : Blo 203807 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B233527 : Blo 203807 233527 := bstep (se 1 (by rfl) ⟨175145, by rfl⟩ : syracuseStep 233527 = 350291) B350291
theorem B462923 : Blo 203807 462923 := bstep (se 1 (by rfl) ⟨347192, by rfl⟩ : syracuseStep 462923 = 694385) B694385
theorem B462977 : Blo 203807 462977 := bstep (se 2 (by rfl) ⟨173616, by rfl⟩ : syracuseStep 462977 = 347233) B347233
theorem B692441 : Blo 203807 692441 := bstep (se 2 (by rfl) ⟨259665, by rfl⟩ : syracuseStep 692441 = 519331) B519331
theorem B659677 : Blo 203807 659677 := bstep (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) B247379
theorem B233707 : Blo 203807 233707 := bstep (se 1 (by rfl) ⟨175280, by rfl⟩ : syracuseStep 233707 = 350561) B350561
theorem B1773899 : Blo 203807 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B463193 : Blo 203807 463193 := bstep (se 2 (by rfl) ⟨173697, by rfl⟩ : syracuseStep 463193 = 347395) B347395
theorem B2232677 : Blo 203807 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B463283 : Blo 203807 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B463319 : Blo 203807 463319 := bstep (se 1 (by rfl) ⟨347489, by rfl⟩ : syracuseStep 463319 = 694979) B694979
theorem B332299 : Blo 203807 332299 := bstep (se 1 (by rfl) ⟨249224, by rfl⟩ : syracuseStep 332299 = 498449) B498449
theorem B2101891 : Blo 203807 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B463499 : Blo 203807 463499 := bstep (se 1 (by rfl) ⟨347624, by rfl⟩ : syracuseStep 463499 = 695249) B695249
theorem B463553 : Blo 203807 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B2331341 : Blo 203807 2331341 := bstep (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) B874253
theorem B1250093 : Blo 203807 1250093 := bstep (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) B468785
theorem B693143 : Blo 203807 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B463769 : Blo 203807 463769 := bstep (se 2 (by rfl) ⟨173913, by rfl⟩ : syracuseStep 463769 = 347827) B347827
theorem B463859 : Blo 203807 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B463895 : Blo 203807 463895 := bstep (se 1 (by rfl) ⟨347921, by rfl⟩ : syracuseStep 463895 = 695843) B695843
theorem B464075 : Blo 203807 464075 := bstep (se 1 (by rfl) ⟨348056, by rfl⟩ : syracuseStep 464075 = 696113) B696113
theorem B464129 : Blo 203807 464129 := bstep (se 2 (by rfl) ⟨174048, by rfl⟩ : syracuseStep 464129 = 348097) B348097
theorem B496919 : Blo 203807 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B759091 : Blo 203807 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B693683 : Blo 203807 693683 := bstep (se 1 (by rfl) ⟨520262, by rfl⟩ : syracuseStep 693683 = 1040525) B1040525
theorem B464345 : Blo 203807 464345 := bstep (se 2 (by rfl) ⟨174129, by rfl⟩ : syracuseStep 464345 = 348259) B348259
theorem B464435 : Blo 203807 464435 := bstep (se 1 (by rfl) ⟨348326, by rfl⟩ : syracuseStep 464435 = 696653) B696653
theorem B464471 : Blo 203807 464471 := bstep (se 1 (by rfl) ⟨348353, by rfl⟩ : syracuseStep 464471 = 696707) B696707
theorem B1316483 : Blo 203807 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B693953 : Blo 203807 693953 := bstep (se 2 (by rfl) ⟨260232, by rfl⟩ : syracuseStep 693953 = 520465) B520465
theorem B464651 : Blo 203807 464651 := bstep (se 1 (by rfl) ⟨348488, by rfl⟩ : syracuseStep 464651 = 696977) B696977
theorem B464705 : Blo 203807 464705 := bstep (se 2 (by rfl) ⟨174264, by rfl⟩ : syracuseStep 464705 = 348529) B348529
theorem B497497 : Blo 203807 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B497611 : Blo 203807 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B464921 : Blo 203807 464921 := bstep (se 2 (by rfl) ⟨174345, by rfl⟩ : syracuseStep 464921 = 348691) B348691
theorem B8198213 : Blo 203807 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B465011 : Blo 203807 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B465047 : Blo 203807 465047 := bstep (se 1 (by rfl) ⟨348785, by rfl⟩ : syracuseStep 465047 = 697571) B697571
theorem B825547 : Blo 203807 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B694493 : Blo 203807 694493 := bstep (se 3 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 694493 = 260435) B260435
theorem B465227 : Blo 203807 465227 := bstep (se 1 (by rfl) ⟨348920, by rfl⟩ : syracuseStep 465227 = 697841) B697841
theorem B465281 : Blo 203807 465281 := bstep (se 2 (by rfl) ⟨174480, by rfl⟩ : syracuseStep 465281 = 348961) B348961
theorem B1120663 : Blo 203807 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B1743281 : Blo 203807 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B498113 : Blo 203807 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B465497 : Blo 203807 465497 := bstep (se 2 (by rfl) ⟨174561, by rfl⟩ : syracuseStep 465497 = 349123) B349123
theorem B465587 : Blo 203807 465587 := bstep (se 1 (by rfl) ⟨349190, by rfl⟩ : syracuseStep 465587 = 698381) B698381
theorem B465623 : Blo 203807 465623 := bstep (se 1 (by rfl) ⟨349217, by rfl⟩ : syracuseStep 465623 = 698435) B698435
theorem B2988899 : Blo 203807 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B465803 : Blo 203807 465803 := bstep (se 1 (by rfl) ⟨349352, by rfl⟩ : syracuseStep 465803 = 698705) B698705
theorem B498611 : Blo 203807 498611 := bstep (se 1 (by rfl) ⟨373958, by rfl⟩ : syracuseStep 498611 = 747917) B747917
theorem B465857 : Blo 203807 465857 := bstep (se 2 (by rfl) ⟨174696, by rfl⟩ : syracuseStep 465857 = 349393) B349393
theorem B1514501 : Blo 203807 1514501 := bstep (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) B283969
theorem B203819 : Blo 203807 203819 := bstep (se 1 (by rfl) ⟨152864, by rfl⟩ : syracuseStep 203819 = 305729) B305729
theorem B367667 : Blo 203807 367667 := bstep (se 1 (by rfl) ⟨275750, by rfl⟩ : syracuseStep 367667 = 551501) B551501
theorem B203831 : Blo 203807 203831 := bstep (se 1 (by rfl) ⟨152873, by rfl⟩ : syracuseStep 203831 = 305747) B305747
theorem B203851 : Blo 203807 203851 := bstep (se 1 (by rfl) ⟨152888, by rfl⟩ : syracuseStep 203851 = 305777) B305777
theorem B203863 : Blo 203807 203863 := bstep (se 1 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 203863 = 305795) B305795
theorem B990301 : Blo 203807 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B203883 : Blo 203807 203883 := bstep (se 1 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 203883 = 305825) B305825
theorem B203895 : Blo 203807 203895 := bstep (se 1 (by rfl) ⟨152921, by rfl⟩ : syracuseStep 203895 = 305843) B305843
theorem B203915 : Blo 203807 203915 := bstep (se 1 (by rfl) ⟨152936, by rfl⟩ : syracuseStep 203915 = 305873) B305873
theorem B203927 : Blo 203807 203927 := bstep (se 1 (by rfl) ⟨152945, by rfl⟩ : syracuseStep 203927 = 305891) B305891
theorem B466073 : Blo 203807 466073 := bstep (se 2 (by rfl) ⟨174777, by rfl⟩ : syracuseStep 466073 = 349555) B349555
theorem B203947 : Blo 203807 203947 := bstep (se 1 (by rfl) ⟨152960, by rfl⟩ : syracuseStep 203947 = 305921) B305921
theorem B203959 : Blo 203807 203959 := bstep (se 1 (by rfl) ⟨152969, by rfl⟩ : syracuseStep 203959 = 305939) B305939
theorem B203979 : Blo 203807 203979 := bstep (se 1 (by rfl) ⟨152984, by rfl⟩ : syracuseStep 203979 = 305969) B305969
theorem B203991 : Blo 203807 203991 := bstep (se 1 (by rfl) ⟨152993, by rfl⟩ : syracuseStep 203991 = 305987) B305987
theorem B204011 : Blo 203807 204011 := bstep (se 1 (by rfl) ⟨153008, by rfl⟩ : syracuseStep 204011 = 306017) B306017
theorem B466163 : Blo 203807 466163 := bstep (se 1 (by rfl) ⟨349622, by rfl⟩ : syracuseStep 466163 = 699245) B699245
theorem B204023 : Blo 203807 204023 := bstep (se 1 (by rfl) ⟨153017, by rfl⟩ : syracuseStep 204023 = 306035) B306035
theorem B204043 : Blo 203807 204043 := bstep (se 1 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 204043 = 306065) B306065
theorem B204055 : Blo 203807 204055 := bstep (se 1 (by rfl) ⟨153041, by rfl⟩ : syracuseStep 204055 = 306083) B306083
theorem B466199 : Blo 203807 466199 := bstep (se 1 (by rfl) ⟨349649, by rfl⟩ : syracuseStep 466199 = 699299) B699299
theorem B204075 : Blo 203807 204075 := bstep (se 1 (by rfl) ⟨153056, by rfl⟩ : syracuseStep 204075 = 306113) B306113
theorem B204087 : Blo 203807 204087 := bstep (se 1 (by rfl) ⟨153065, by rfl⟩ : syracuseStep 204087 = 306131) B306131
theorem B204107 : Blo 203807 204107 := bstep (se 1 (by rfl) ⟨153080, by rfl⟩ : syracuseStep 204107 = 306161) B306161
theorem B695627 : Blo 203807 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B204119 : Blo 203807 204119 := bstep (se 1 (by rfl) ⟨153089, by rfl⟩ : syracuseStep 204119 = 306179) B306179
theorem B367961 : Blo 203807 367961 := bstep (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) B275971
theorem B204139 : Blo 203807 204139 := bstep (se 1 (by rfl) ⟨153104, by rfl⟩ : syracuseStep 204139 = 306209) B306209
theorem B204151 : Blo 203807 204151 := bstep (se 1 (by rfl) ⟨153113, by rfl⟩ : syracuseStep 204151 = 306227) B306227
theorem B204171 : Blo 203807 204171 := bstep (se 1 (by rfl) ⟨153128, by rfl⟩ : syracuseStep 204171 = 306257) B306257
theorem B204183 : Blo 203807 204183 := bstep (se 1 (by rfl) ⟨153137, by rfl⟩ : syracuseStep 204183 = 306275) B306275
theorem B204203 : Blo 203807 204203 := bstep (se 1 (by rfl) ⟨153152, by rfl⟩ : syracuseStep 204203 = 306305) B306305
theorem B204215 : Blo 203807 204215 := bstep (se 1 (by rfl) ⟨153161, by rfl⟩ : syracuseStep 204215 = 306323) B306323
theorem B204235 : Blo 203807 204235 := bstep (se 1 (by rfl) ⟨153176, by rfl⟩ : syracuseStep 204235 = 306353) B306353
theorem B466379 : Blo 203807 466379 := bstep (se 1 (by rfl) ⟨349784, by rfl⟩ : syracuseStep 466379 = 699569) B699569
theorem B204247 : Blo 203807 204247 := bstep (se 1 (by rfl) ⟨153185, by rfl⟩ : syracuseStep 204247 = 306371) B306371
theorem B204267 : Blo 203807 204267 := bstep (se 1 (by rfl) ⟨153200, by rfl⟩ : syracuseStep 204267 = 306401) B306401
theorem B204279 : Blo 203807 204279 := bstep (se 1 (by rfl) ⟨153209, by rfl⟩ : syracuseStep 204279 = 306419) B306419
theorem B466433 : Blo 203807 466433 := bstep (se 2 (by rfl) ⟨174912, by rfl⟩ : syracuseStep 466433 = 349825) B349825
theorem B204299 : Blo 203807 204299 := bstep (se 1 (by rfl) ⟨153224, by rfl⟩ : syracuseStep 204299 = 306449) B306449
theorem B204311 : Blo 203807 204311 := bstep (se 1 (by rfl) ⟨153233, by rfl⟩ : syracuseStep 204311 = 306467) B306467
theorem B204331 : Blo 203807 204331 := bstep (se 1 (by rfl) ⟨153248, by rfl⟩ : syracuseStep 204331 = 306497) B306497
theorem B204343 : Blo 203807 204343 := bstep (se 1 (by rfl) ⟨153257, by rfl⟩ : syracuseStep 204343 = 306515) B306515
theorem B204363 : Blo 203807 204363 := bstep (se 1 (by rfl) ⟨153272, by rfl⟩ : syracuseStep 204363 = 306545) B306545
theorem B204375 : Blo 203807 204375 := bstep (se 1 (by rfl) ⟨153281, by rfl⟩ : syracuseStep 204375 = 306563) B306563
theorem B695897 : Blo 203807 695897 := bstep (se 2 (by rfl) ⟨260961, by rfl⟩ : syracuseStep 695897 = 521923) B521923
theorem B204395 : Blo 203807 204395 := bstep (se 1 (by rfl) ⟨153296, by rfl⟩ : syracuseStep 204395 = 306593) B306593
theorem B204407 : Blo 203807 204407 := bstep (se 1 (by rfl) ⟨153305, by rfl⟩ : syracuseStep 204407 = 306611) B306611
theorem B204427 : Blo 203807 204427 := bstep (se 1 (by rfl) ⟨153320, by rfl⟩ : syracuseStep 204427 = 306641) B306641
theorem B204439 : Blo 203807 204439 := bstep (se 1 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 204439 = 306659) B306659
theorem B204459 : Blo 203807 204459 := bstep (se 1 (by rfl) ⟨153344, by rfl⟩ : syracuseStep 204459 = 306689) B306689
theorem B204471 : Blo 203807 204471 := bstep (se 1 (by rfl) ⟨153353, by rfl⟩ : syracuseStep 204471 = 306707) B306707
theorem B204491 : Blo 203807 204491 := bstep (se 1 (by rfl) ⟨153368, by rfl⟩ : syracuseStep 204491 = 306737) B306737
theorem B204503 : Blo 203807 204503 := bstep (se 1 (by rfl) ⟨153377, by rfl⟩ : syracuseStep 204503 = 306755) B306755
theorem B466649 : Blo 203807 466649 := bstep (se 2 (by rfl) ⟨174993, by rfl⟩ : syracuseStep 466649 = 349987) B349987
theorem B204523 : Blo 203807 204523 := bstep (se 1 (by rfl) ⟨153392, by rfl⟩ : syracuseStep 204523 = 306785) B306785
theorem B204535 : Blo 203807 204535 := bstep (se 1 (by rfl) ⟨153401, by rfl⟩ : syracuseStep 204535 = 306803) B306803
theorem B204555 : Blo 203807 204555 := bstep (se 1 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 204555 = 306833) B306833
theorem B204567 : Blo 203807 204567 := bstep (se 1 (by rfl) ⟨153425, by rfl⟩ : syracuseStep 204567 = 306851) B306851
theorem B204587 : Blo 203807 204587 := bstep (se 1 (by rfl) ⟨153440, by rfl⟩ : syracuseStep 204587 = 306881) B306881
theorem B466739 : Blo 203807 466739 := bstep (se 1 (by rfl) ⟨350054, by rfl⟩ : syracuseStep 466739 = 700109) B700109
theorem B204599 : Blo 203807 204599 := bstep (se 1 (by rfl) ⟨153449, by rfl⟩ : syracuseStep 204599 = 306899) B306899
theorem B204619 : Blo 203807 204619 := bstep (se 1 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 204619 = 306929) B306929
theorem B204631 : Blo 203807 204631 := bstep (se 1 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 204631 = 306947) B306947
theorem B466775 : Blo 203807 466775 := bstep (se 1 (by rfl) ⟨350081, by rfl⟩ : syracuseStep 466775 = 700163) B700163
theorem B204651 : Blo 203807 204651 := bstep (se 1 (by rfl) ⟨153488, by rfl⟩ : syracuseStep 204651 = 306977) B306977
theorem B204663 : Blo 203807 204663 := bstep (se 1 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 204663 = 306995) B306995
theorem B204683 : Blo 203807 204683 := bstep (se 1 (by rfl) ⟨153512, by rfl⟩ : syracuseStep 204683 = 307025) B307025
theorem B204695 : Blo 203807 204695 := bstep (se 1 (by rfl) ⟨153521, by rfl⟩ : syracuseStep 204695 = 307043) B307043
theorem B204715 : Blo 203807 204715 := bstep (se 1 (by rfl) ⟨153536, by rfl⟩ : syracuseStep 204715 = 307073) B307073
theorem B204727 : Blo 203807 204727 := bstep (se 1 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 204727 = 307091) B307091
theorem B204747 : Blo 203807 204747 := bstep (se 1 (by rfl) ⟨153560, by rfl⟩ : syracuseStep 204747 = 307121) B307121
theorem B1679309 : Blo 203807 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B204759 : Blo 203807 204759 := bstep (se 1 (by rfl) ⟨153569, by rfl⟩ : syracuseStep 204759 = 307139) B307139
theorem B1122265 : Blo 203807 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B204779 : Blo 203807 204779 := bstep (se 1 (by rfl) ⟨153584, by rfl⟩ : syracuseStep 204779 = 307169) B307169
theorem B204791 : Blo 203807 204791 := bstep (se 1 (by rfl) ⟨153593, by rfl⟩ : syracuseStep 204791 = 307187) B307187
theorem B204811 : Blo 203807 204811 := bstep (se 1 (by rfl) ⟨153608, by rfl⟩ : syracuseStep 204811 = 307217) B307217
theorem B466955 : Blo 203807 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B204823 : Blo 203807 204823 := bstep (se 1 (by rfl) ⟨153617, by rfl⟩ : syracuseStep 204823 = 307235) B307235
theorem B204843 : Blo 203807 204843 := bstep (se 1 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 204843 = 307265) B307265
theorem B204855 : Blo 203807 204855 := bstep (se 1 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 204855 = 307283) B307283
theorem B467009 : Blo 203807 467009 := bstep (se 2 (by rfl) ⟨175128, by rfl⟩ : syracuseStep 467009 = 350257) B350257
theorem B204875 : Blo 203807 204875 := bstep (se 1 (by rfl) ⟨153656, by rfl⟩ : syracuseStep 204875 = 307313) B307313
theorem B204887 : Blo 203807 204887 := bstep (se 1 (by rfl) ⟨153665, by rfl⟩ : syracuseStep 204887 = 307331) B307331
theorem B204907 : Blo 203807 204907 := bstep (se 1 (by rfl) ⟨153680, by rfl⟩ : syracuseStep 204907 = 307361) B307361
theorem B204919 : Blo 203807 204919 := bstep (se 1 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 204919 = 307379) B307379
theorem B204939 : Blo 203807 204939 := bstep (se 1 (by rfl) ⟨153704, by rfl⟩ : syracuseStep 204939 = 307409) B307409
theorem B204951 : Blo 203807 204951 := bstep (se 1 (by rfl) ⟨153713, by rfl⟩ : syracuseStep 204951 = 307427) B307427
theorem B204971 : Blo 203807 204971 := bstep (se 1 (by rfl) ⟨153728, by rfl⟩ : syracuseStep 204971 = 307457) B307457
theorem B204983 : Blo 203807 204983 := bstep (se 1 (by rfl) ⟨153737, by rfl⟩ : syracuseStep 204983 = 307475) B307475
theorem B205003 : Blo 203807 205003 := bstep (se 1 (by rfl) ⟨153752, by rfl⟩ : syracuseStep 205003 = 307505) B307505
theorem B205015 : Blo 203807 205015 := bstep (se 1 (by rfl) ⟨153761, by rfl⟩ : syracuseStep 205015 = 307523) B307523
theorem B205035 : Blo 203807 205035 := bstep (se 1 (by rfl) ⟨153776, by rfl⟩ : syracuseStep 205035 = 307553) B307553
theorem B205047 : Blo 203807 205047 := bstep (se 1 (by rfl) ⟨153785, by rfl⟩ : syracuseStep 205047 = 307571) B307571
theorem B205067 : Blo 203807 205067 := bstep (se 1 (by rfl) ⟨153800, by rfl⟩ : syracuseStep 205067 = 307601) B307601
theorem B205079 : Blo 203807 205079 := bstep (se 1 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 205079 = 307619) B307619
theorem B696599 : Blo 203807 696599 := bstep (se 1 (by rfl) ⟨522449, by rfl⟩ : syracuseStep 696599 = 1044899) B1044899
theorem B467225 : Blo 203807 467225 := bstep (se 2 (by rfl) ⟨175209, by rfl⟩ : syracuseStep 467225 = 350419) B350419
theorem B205099 : Blo 203807 205099 := bstep (se 1 (by rfl) ⟨153824, by rfl⟩ : syracuseStep 205099 = 307649) B307649
theorem B205111 : Blo 203807 205111 := bstep (se 1 (by rfl) ⟨153833, by rfl⟩ : syracuseStep 205111 = 307667) B307667
theorem B205131 : Blo 203807 205131 := bstep (se 1 (by rfl) ⟨153848, by rfl⟩ : syracuseStep 205131 = 307697) B307697
theorem B205143 : Blo 203807 205143 := bstep (se 1 (by rfl) ⟨153857, by rfl⟩ : syracuseStep 205143 = 307715) B307715
theorem B205163 : Blo 203807 205163 := bstep (se 1 (by rfl) ⟨153872, by rfl⟩ : syracuseStep 205163 = 307745) B307745
theorem B467315 : Blo 203807 467315 := bstep (se 1 (by rfl) ⟨350486, by rfl⟩ : syracuseStep 467315 = 700973) B700973
theorem B205175 : Blo 203807 205175 := bstep (se 1 (by rfl) ⟨153881, by rfl⟩ : syracuseStep 205175 = 307763) B307763
theorem B205195 : Blo 203807 205195 := bstep (se 1 (by rfl) ⟨153896, by rfl⟩ : syracuseStep 205195 = 307793) B307793
theorem B205207 : Blo 203807 205207 := bstep (se 1 (by rfl) ⟨153905, by rfl⟩ : syracuseStep 205207 = 307811) B307811
theorem B467351 : Blo 203807 467351 := bstep (se 1 (by rfl) ⟨350513, by rfl⟩ : syracuseStep 467351 = 701027) B701027
theorem B205227 : Blo 203807 205227 := bstep (se 1 (by rfl) ⟨153920, by rfl⟩ : syracuseStep 205227 = 307841) B307841
theorem B205239 : Blo 203807 205239 := bstep (se 1 (by rfl) ⟨153929, by rfl⟩ : syracuseStep 205239 = 307859) B307859
theorem B205259 : Blo 203807 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B205271 : Blo 203807 205271 := bstep (se 1 (by rfl) ⟨153953, by rfl⟩ : syracuseStep 205271 = 307907) B307907
theorem B205291 : Blo 203807 205291 := bstep (se 1 (by rfl) ⟨153968, by rfl⟩ : syracuseStep 205291 = 307937) B307937
theorem B205303 : Blo 203807 205303 := bstep (se 1 (by rfl) ⟨153977, by rfl⟩ : syracuseStep 205303 = 307955) B307955
theorem B205323 : Blo 203807 205323 := bstep (se 1 (by rfl) ⟨153992, by rfl⟩ : syracuseStep 205323 = 307985) B307985
theorem B205335 : Blo 203807 205335 := bstep (se 1 (by rfl) ⟨154001, by rfl⟩ : syracuseStep 205335 = 308003) B308003
theorem B205355 : Blo 203807 205355 := bstep (se 1 (by rfl) ⟨154016, by rfl⟩ : syracuseStep 205355 = 308033) B308033
theorem B205367 : Blo 203807 205367 := bstep (se 1 (by rfl) ⟨154025, by rfl⟩ : syracuseStep 205367 = 308051) B308051
theorem B205387 : Blo 203807 205387 := bstep (se 1 (by rfl) ⟨154040, by rfl⟩ : syracuseStep 205387 = 308081) B308081
theorem B467531 : Blo 203807 467531 := bstep (se 1 (by rfl) ⟨350648, by rfl⟩ : syracuseStep 467531 = 701297) B701297
theorem B205399 : Blo 203807 205399 := bstep (se 1 (by rfl) ⟨154049, by rfl⟩ : syracuseStep 205399 = 308099) B308099
theorem B205419 : Blo 203807 205419 := bstep (se 1 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 205419 = 308129) B308129
theorem B205431 : Blo 203807 205431 := bstep (se 1 (by rfl) ⟨154073, by rfl⟩ : syracuseStep 205431 = 308147) B308147
theorem B205451 : Blo 203807 205451 := bstep (se 1 (by rfl) ⟨154088, by rfl⟩ : syracuseStep 205451 = 308177) B308177
theorem B205463 : Blo 203807 205463 := bstep (se 1 (by rfl) ⟨154097, by rfl⟩ : syracuseStep 205463 = 308195) B308195
theorem B205483 : Blo 203807 205483 := bstep (se 1 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 205483 = 308225) B308225
theorem B205495 : Blo 203807 205495 := bstep (se 1 (by rfl) ⟨154121, by rfl⟩ : syracuseStep 205495 = 308243) B308243
theorem B205515 : Blo 203807 205515 := bstep (se 1 (by rfl) ⟨154136, by rfl⟩ : syracuseStep 205515 = 308273) B308273
theorem B205527 : Blo 203807 205527 := bstep (se 1 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 205527 = 308291) B308291
theorem B205547 : Blo 203807 205547 := bstep (se 1 (by rfl) ⟨154160, by rfl⟩ : syracuseStep 205547 = 308321) B308321
theorem B205559 : Blo 203807 205559 := bstep (se 1 (by rfl) ⟨154169, by rfl⟩ : syracuseStep 205559 = 308339) B308339
theorem B205579 : Blo 203807 205579 := bstep (se 1 (by rfl) ⟨154184, by rfl⟩ : syracuseStep 205579 = 308369) B308369
theorem B205591 : Blo 203807 205591 := bstep (se 1 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 205591 = 308387) B308387
theorem B205611 : Blo 203807 205611 := bstep (se 1 (by rfl) ⟨154208, by rfl⟩ : syracuseStep 205611 = 308417) B308417
theorem B697139 : Blo 203807 697139 := bstep (se 1 (by rfl) ⟨522854, by rfl⟩ : syracuseStep 697139 = 1045709) B1045709
theorem B205623 : Blo 203807 205623 := bstep (se 1 (by rfl) ⟨154217, by rfl⟩ : syracuseStep 205623 = 308435) B308435
theorem B205643 : Blo 203807 205643 := bstep (se 1 (by rfl) ⟨154232, by rfl⟩ : syracuseStep 205643 = 308465) B308465
theorem B205655 : Blo 203807 205655 := bstep (se 1 (by rfl) ⟨154241, by rfl⟩ : syracuseStep 205655 = 308483) B308483
theorem B205675 : Blo 203807 205675 := bstep (se 1 (by rfl) ⟨154256, by rfl⟩ : syracuseStep 205675 = 308513) B308513
theorem B205687 : Blo 203807 205687 := bstep (se 1 (by rfl) ⟨154265, by rfl⟩ : syracuseStep 205687 = 308531) B308531
theorem B205707 : Blo 203807 205707 := bstep (se 1 (by rfl) ⟨154280, by rfl⟩ : syracuseStep 205707 = 308561) B308561
theorem B205719 : Blo 203807 205719 := bstep (se 1 (by rfl) ⟨154289, by rfl⟩ : syracuseStep 205719 = 308579) B308579
theorem B205739 : Blo 203807 205739 := bstep (se 1 (by rfl) ⟨154304, by rfl⟩ : syracuseStep 205739 = 308609) B308609
theorem B205751 : Blo 203807 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B205771 : Blo 203807 205771 := bstep (se 1 (by rfl) ⟨154328, by rfl⟩ : syracuseStep 205771 = 308657) B308657
theorem B205783 : Blo 203807 205783 := bstep (se 1 (by rfl) ⟨154337, by rfl⟩ : syracuseStep 205783 = 308675) B308675
theorem B205803 : Blo 203807 205803 := bstep (se 1 (by rfl) ⟨154352, by rfl⟩ : syracuseStep 205803 = 308705) B308705
theorem B205815 : Blo 203807 205815 := bstep (se 1 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 205815 = 308723) B308723
theorem B205835 : Blo 203807 205835 := bstep (se 1 (by rfl) ⟨154376, by rfl⟩ : syracuseStep 205835 = 308753) B308753
theorem B205847 : Blo 203807 205847 := bstep (se 1 (by rfl) ⟨154385, by rfl⟩ : syracuseStep 205847 = 308771) B308771
theorem B205867 : Blo 203807 205867 := bstep (se 1 (by rfl) ⟨154400, by rfl⟩ : syracuseStep 205867 = 308801) B308801
theorem B205879 : Blo 203807 205879 := bstep (se 1 (by rfl) ⟨154409, by rfl⟩ : syracuseStep 205879 = 308819) B308819
theorem B697409 : Blo 203807 697409 := bstep (se 2 (by rfl) ⟨261528, by rfl⟩ : syracuseStep 697409 = 523057) B523057
theorem B205899 : Blo 203807 205899 := bstep (se 1 (by rfl) ⟨154424, by rfl⟩ : syracuseStep 205899 = 308849) B308849
theorem B205911 : Blo 203807 205911 := bstep (se 1 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 205911 = 308867) B308867
theorem B205931 : Blo 203807 205931 := bstep (se 1 (by rfl) ⟨154448, by rfl⟩ : syracuseStep 205931 = 308897) B308897
theorem B205943 : Blo 203807 205943 := bstep (se 1 (by rfl) ⟨154457, by rfl⟩ : syracuseStep 205943 = 308915) B308915
theorem B205963 : Blo 203807 205963 := bstep (se 1 (by rfl) ⟨154472, by rfl⟩ : syracuseStep 205963 = 308945) B308945
theorem B205975 : Blo 203807 205975 := bstep (se 1 (by rfl) ⟨154481, by rfl⟩ : syracuseStep 205975 = 308963) B308963
theorem B205995 : Blo 203807 205995 := bstep (se 1 (by rfl) ⟨154496, by rfl⟩ : syracuseStep 205995 = 308993) B308993
theorem B206007 : Blo 203807 206007 := bstep (se 1 (by rfl) ⟨154505, by rfl⟩ : syracuseStep 206007 = 309011) B309011
theorem B206027 : Blo 203807 206027 := bstep (se 1 (by rfl) ⟨154520, by rfl⟩ : syracuseStep 206027 = 309041) B309041
theorem B206039 : Blo 203807 206039 := bstep (se 1 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 206039 = 309059) B309059
theorem B206059 : Blo 203807 206059 := bstep (se 1 (by rfl) ⟨154544, by rfl⟩ : syracuseStep 206059 = 309089) B309089
theorem B206071 : Blo 203807 206071 := bstep (se 1 (by rfl) ⟨154553, by rfl⟩ : syracuseStep 206071 = 309107) B309107
theorem B206091 : Blo 203807 206091 := bstep (se 1 (by rfl) ⟨154568, by rfl⟩ : syracuseStep 206091 = 309137) B309137
theorem B206103 : Blo 203807 206103 := bstep (se 1 (by rfl) ⟨154577, by rfl⟩ : syracuseStep 206103 = 309155) B309155
theorem B206123 : Blo 203807 206123 := bstep (se 1 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 206123 = 309185) B309185
theorem B206135 : Blo 203807 206135 := bstep (se 1 (by rfl) ⟨154601, by rfl⟩ : syracuseStep 206135 = 309203) B309203
theorem B206155 : Blo 203807 206155 := bstep (se 1 (by rfl) ⟨154616, by rfl⟩ : syracuseStep 206155 = 309233) B309233
theorem B206167 : Blo 203807 206167 := bstep (se 1 (by rfl) ⟨154625, by rfl⟩ : syracuseStep 206167 = 309251) B309251
theorem B206187 : Blo 203807 206187 := bstep (se 1 (by rfl) ⟨154640, by rfl⟩ : syracuseStep 206187 = 309281) B309281
theorem B206199 : Blo 203807 206199 := bstep (se 1 (by rfl) ⟨154649, by rfl⟩ : syracuseStep 206199 = 309299) B309299
theorem B206219 : Blo 203807 206219 := bstep (se 1 (by rfl) ⟨154664, by rfl⟩ : syracuseStep 206219 = 309329) B309329
theorem B206231 : Blo 203807 206231 := bstep (se 1 (by rfl) ⟨154673, by rfl⟩ : syracuseStep 206231 = 309347) B309347
theorem B206251 : Blo 203807 206251 := bstep (se 1 (by rfl) ⟨154688, by rfl⟩ : syracuseStep 206251 = 309377) B309377
theorem B206263 : Blo 203807 206263 := bstep (se 1 (by rfl) ⟨154697, by rfl⟩ : syracuseStep 206263 = 309395) B309395
theorem B206283 : Blo 203807 206283 := bstep (se 1 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 206283 = 309425) B309425
theorem B206295 : Blo 203807 206295 := bstep (se 1 (by rfl) ⟨154721, by rfl⟩ : syracuseStep 206295 = 309443) B309443
theorem B206315 : Blo 203807 206315 := bstep (se 1 (by rfl) ⟨154736, by rfl⟩ : syracuseStep 206315 = 309473) B309473
theorem B206327 : Blo 203807 206327 := bstep (se 1 (by rfl) ⟨154745, by rfl⟩ : syracuseStep 206327 = 309491) B309491
theorem B206347 : Blo 203807 206347 := bstep (se 1 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 206347 = 309521) B309521
theorem B206359 : Blo 203807 206359 := bstep (se 1 (by rfl) ⟨154769, by rfl⟩ : syracuseStep 206359 = 309539) B309539
theorem B665111 : Blo 203807 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B206379 : Blo 203807 206379 := bstep (se 1 (by rfl) ⟨154784, by rfl⟩ : syracuseStep 206379 = 309569) B309569
theorem B206391 : Blo 203807 206391 := bstep (se 1 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 206391 = 309587) B309587
theorem B206411 : Blo 203807 206411 := bstep (se 1 (by rfl) ⟨154808, by rfl⟩ : syracuseStep 206411 = 309617) B309617
theorem B206423 : Blo 203807 206423 := bstep (se 1 (by rfl) ⟨154817, by rfl⟩ : syracuseStep 206423 = 309635) B309635
theorem B403033 : Blo 203807 403033 := bstep (se 2 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 403033 = 302275) B302275
theorem B697949 : Blo 203807 697949 := bstep (se 3 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 697949 = 261731) B261731
theorem B206443 : Blo 203807 206443 := bstep (se 1 (by rfl) ⟨154832, by rfl⟩ : syracuseStep 206443 = 309665) B309665
theorem B206455 : Blo 203807 206455 := bstep (se 1 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 206455 = 309683) B309683
theorem B206475 : Blo 203807 206475 := bstep (se 1 (by rfl) ⟨154856, by rfl⟩ : syracuseStep 206475 = 309713) B309713
theorem B435863 : Blo 203807 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B206487 : Blo 203807 206487 := bstep (se 1 (by rfl) ⟨154865, by rfl⟩ : syracuseStep 206487 = 309731) B309731
theorem B206507 : Blo 203807 206507 := bstep (se 1 (by rfl) ⟨154880, by rfl⟩ : syracuseStep 206507 = 309761) B309761
theorem B206519 : Blo 203807 206519 := bstep (se 1 (by rfl) ⟨154889, by rfl⟩ : syracuseStep 206519 = 309779) B309779
theorem B206539 : Blo 203807 206539 := bstep (se 1 (by rfl) ⟨154904, by rfl⟩ : syracuseStep 206539 = 309809) B309809
theorem B206551 : Blo 203807 206551 := bstep (se 1 (by rfl) ⟨154913, by rfl⟩ : syracuseStep 206551 = 309827) B309827
theorem B206571 : Blo 203807 206571 := bstep (se 1 (by rfl) ⟨154928, by rfl⟩ : syracuseStep 206571 = 309857) B309857
theorem B206583 : Blo 203807 206583 := bstep (se 1 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 206583 = 309875) B309875
theorem B206603 : Blo 203807 206603 := bstep (se 1 (by rfl) ⟨154952, by rfl⟩ : syracuseStep 206603 = 309905) B309905
theorem B206615 : Blo 203807 206615 := bstep (se 1 (by rfl) ⟨154961, by rfl⟩ : syracuseStep 206615 = 309923) B309923
theorem B206635 : Blo 203807 206635 := bstep (se 1 (by rfl) ⟨154976, by rfl⟩ : syracuseStep 206635 = 309953) B309953
theorem B206647 : Blo 203807 206647 := bstep (se 1 (by rfl) ⟨154985, by rfl⟩ : syracuseStep 206647 = 309971) B309971
theorem B436033 : Blo 203807 436033 := bstep (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) B327025
theorem B206667 : Blo 203807 206667 := bstep (se 1 (by rfl) ⟨155000, by rfl⟩ : syracuseStep 206667 = 310001) B310001
theorem B206679 : Blo 203807 206679 := bstep (se 1 (by rfl) ⟨155009, by rfl⟩ : syracuseStep 206679 = 310019) B310019
theorem B829277 : Blo 203807 829277 := bstep (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) B310979
theorem B206699 : Blo 203807 206699 := bstep (se 1 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 206699 = 310049) B310049
theorem B206711 : Blo 203807 206711 := bstep (se 1 (by rfl) ⟨155033, by rfl⟩ : syracuseStep 206711 = 310067) B310067
theorem B206731 : Blo 203807 206731 := bstep (se 1 (by rfl) ⟨155048, by rfl⟩ : syracuseStep 206731 = 310097) B310097
theorem B206743 : Blo 203807 206743 := bstep (se 1 (by rfl) ⟨155057, by rfl⟩ : syracuseStep 206743 = 310115) B310115
theorem B206763 : Blo 203807 206763 := bstep (se 1 (by rfl) ⟨155072, by rfl⟩ : syracuseStep 206763 = 310145) B310145
theorem B206775 : Blo 203807 206775 := bstep (se 1 (by rfl) ⟨155081, by rfl⟩ : syracuseStep 206775 = 310163) B310163
theorem B206795 : Blo 203807 206795 := bstep (se 1 (by rfl) ⟨155096, by rfl⟩ : syracuseStep 206795 = 310193) B310193
theorem B206807 : Blo 203807 206807 := bstep (se 1 (by rfl) ⟨155105, by rfl⟩ : syracuseStep 206807 = 310211) B310211
theorem B206827 : Blo 203807 206827 := bstep (se 1 (by rfl) ⟨155120, by rfl⟩ : syracuseStep 206827 = 310241) B310241
theorem B206839 : Blo 203807 206839 := bstep (se 1 (by rfl) ⟨155129, by rfl⟩ : syracuseStep 206839 = 310259) B310259
theorem B206859 : Blo 203807 206859 := bstep (se 1 (by rfl) ⟨155144, by rfl⟩ : syracuseStep 206859 = 310289) B310289
theorem B206871 : Blo 203807 206871 := bstep (se 1 (by rfl) ⟨155153, by rfl⟩ : syracuseStep 206871 = 310307) B310307
theorem B206891 : Blo 203807 206891 := bstep (se 1 (by rfl) ⟨155168, by rfl⟩ : syracuseStep 206891 = 310337) B310337
theorem B206903 : Blo 203807 206903 := bstep (se 1 (by rfl) ⟨155177, by rfl⟩ : syracuseStep 206903 = 310355) B310355
theorem B206923 : Blo 203807 206923 := bstep (se 1 (by rfl) ⟨155192, by rfl⟩ : syracuseStep 206923 = 310385) B310385
theorem B206935 : Blo 203807 206935 := bstep (se 1 (by rfl) ⟨155201, by rfl⟩ : syracuseStep 206935 = 310403) B310403
theorem B206955 : Blo 203807 206955 := bstep (se 1 (by rfl) ⟨155216, by rfl⟩ : syracuseStep 206955 = 310433) B310433
theorem B206967 : Blo 203807 206967 := bstep (se 1 (by rfl) ⟨155225, by rfl⟩ : syracuseStep 206967 = 310451) B310451
theorem B206987 : Blo 203807 206987 := bstep (se 1 (by rfl) ⟨155240, by rfl⟩ : syracuseStep 206987 = 310481) B310481
theorem B436375 : Blo 203807 436375 := bstep (se 1 (by rfl) ⟨327281, by rfl⟩ : syracuseStep 436375 = 654563) B654563
theorem B206999 : Blo 203807 206999 := bstep (se 1 (by rfl) ⟨155249, by rfl⟩ : syracuseStep 206999 = 310499) B310499
theorem B207019 : Blo 203807 207019 := bstep (se 1 (by rfl) ⟨155264, by rfl⟩ : syracuseStep 207019 = 310529) B310529
theorem B207031 : Blo 203807 207031 := bstep (se 1 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 207031 = 310547) B310547
theorem B207051 : Blo 203807 207051 := bstep (se 1 (by rfl) ⟨155288, by rfl⟩ : syracuseStep 207051 = 310577) B310577
theorem B207063 : Blo 203807 207063 := bstep (se 1 (by rfl) ⟨155297, by rfl⟩ : syracuseStep 207063 = 310595) B310595
theorem B207083 : Blo 203807 207083 := bstep (se 1 (by rfl) ⟨155312, by rfl⟩ : syracuseStep 207083 = 310625) B310625
theorem B207095 : Blo 203807 207095 := bstep (se 1 (by rfl) ⟨155321, by rfl⟩ : syracuseStep 207095 = 310643) B310643
theorem B207115 : Blo 203807 207115 := bstep (se 1 (by rfl) ⟨155336, by rfl⟩ : syracuseStep 207115 = 310673) B310673
theorem B207127 : Blo 203807 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B207147 : Blo 203807 207147 := bstep (se 1 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 207147 = 310721) B310721
theorem B207159 : Blo 203807 207159 := bstep (se 1 (by rfl) ⟨155369, by rfl⟩ : syracuseStep 207159 = 310739) B310739
theorem B207179 : Blo 203807 207179 := bstep (se 1 (by rfl) ⟨155384, by rfl⟩ : syracuseStep 207179 = 310769) B310769
theorem B207191 : Blo 203807 207191 := bstep (se 1 (by rfl) ⟨155393, by rfl⟩ : syracuseStep 207191 = 310787) B310787
theorem B207211 : Blo 203807 207211 := bstep (se 1 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 207211 = 310817) B310817
theorem B207223 : Blo 203807 207223 := bstep (se 1 (by rfl) ⟨155417, by rfl⟩ : syracuseStep 207223 = 310835) B310835
theorem B207243 : Blo 203807 207243 := bstep (se 1 (by rfl) ⟨155432, by rfl⟩ : syracuseStep 207243 = 310865) B310865
theorem B207255 : Blo 203807 207255 := bstep (se 1 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 207255 = 310883) B310883
theorem B207275 : Blo 203807 207275 := bstep (se 1 (by rfl) ⟨155456, by rfl⟩ : syracuseStep 207275 = 310913) B310913
theorem B207287 : Blo 203807 207287 := bstep (se 1 (by rfl) ⟨155465, by rfl⟩ : syracuseStep 207287 = 310931) B310931
theorem B698827 : Blo 203807 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B207307 : Blo 203807 207307 := bstep (se 1 (by rfl) ⟨155480, by rfl⟩ : syracuseStep 207307 = 310961) B310961
theorem B207319 : Blo 203807 207319 := bstep (se 1 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 207319 = 310979) B310979
theorem B207339 : Blo 203807 207339 := bstep (se 1 (by rfl) ⟨155504, by rfl⟩ : syracuseStep 207339 = 311009) B311009
theorem B207351 : Blo 203807 207351 := bstep (se 1 (by rfl) ⟨155513, by rfl⟩ : syracuseStep 207351 = 311027) B311027
theorem B207371 : Blo 203807 207371 := bstep (se 1 (by rfl) ⟨155528, by rfl⟩ : syracuseStep 207371 = 311057) B311057
theorem B928279 : Blo 203807 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B207383 : Blo 203807 207383 := bstep (se 1 (by rfl) ⟨155537, by rfl⟩ : syracuseStep 207383 = 311075) B311075
theorem B207403 : Blo 203807 207403 := bstep (se 1 (by rfl) ⟨155552, by rfl⟩ : syracuseStep 207403 = 311105) B311105
theorem B207415 : Blo 203807 207415 := bstep (se 1 (by rfl) ⟨155561, by rfl⟩ : syracuseStep 207415 = 311123) B311123
theorem B2402891 : Blo 203807 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B207435 : Blo 203807 207435 := bstep (se 1 (by rfl) ⟨155576, by rfl⟩ : syracuseStep 207435 = 311153) B311153
theorem B207447 : Blo 203807 207447 := bstep (se 1 (by rfl) ⟨155585, by rfl⟩ : syracuseStep 207447 = 311171) B311171
theorem B305753 : Blo 203807 305753 := bstep (se 2 (by rfl) ⟨114657, by rfl⟩ : syracuseStep 305753 = 229315) B229315
theorem B207467 : Blo 203807 207467 := bstep (se 1 (by rfl) ⟨155600, by rfl⟩ : syracuseStep 207467 = 311201) B311201
theorem B207479 : Blo 203807 207479 := bstep (se 1 (by rfl) ⟨155609, by rfl⟩ : syracuseStep 207479 = 311219) B311219
theorem B207499 : Blo 203807 207499 := bstep (se 1 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 207499 = 311249) B311249
theorem B207511 : Blo 203807 207511 := bstep (se 1 (by rfl) ⟨155633, by rfl⟩ : syracuseStep 207511 = 311267) B311267
theorem B207531 : Blo 203807 207531 := bstep (se 1 (by rfl) ⟨155648, by rfl⟩ : syracuseStep 207531 = 311297) B311297
theorem B207543 : Blo 203807 207543 := bstep (se 1 (by rfl) ⟨155657, by rfl⟩ : syracuseStep 207543 = 311315) B311315
theorem B305867 : Blo 203807 305867 := bstep (se 1 (by rfl) ⟨229400, by rfl⟩ : syracuseStep 305867 = 458801) B458801
theorem B699083 : Blo 203807 699083 := bstep (se 1 (by rfl) ⟨524312, by rfl⟩ : syracuseStep 699083 = 1048625) B1048625
theorem B207563 : Blo 203807 207563 := bstep (se 1 (by rfl) ⟨155672, by rfl⟩ : syracuseStep 207563 = 311345) B311345
theorem B305879 : Blo 203807 305879 := bstep (se 1 (by rfl) ⟨229409, by rfl⟩ : syracuseStep 305879 = 458819) B458819
theorem B404183 : Blo 203807 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B207575 : Blo 203807 207575 := bstep (se 1 (by rfl) ⟨155681, by rfl⟩ : syracuseStep 207575 = 311363) B311363
theorem B207595 : Blo 203807 207595 := bstep (se 1 (by rfl) ⟨155696, by rfl⟩ : syracuseStep 207595 = 311393) B311393
theorem B207607 : Blo 203807 207607 := bstep (se 1 (by rfl) ⟨155705, by rfl⟩ : syracuseStep 207607 = 311411) B311411
theorem B207627 : Blo 203807 207627 := bstep (se 1 (by rfl) ⟨155720, by rfl⟩ : syracuseStep 207627 = 311441) B311441
theorem B371479 : Blo 203807 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B207639 : Blo 203807 207639 := bstep (se 1 (by rfl) ⟨155729, by rfl⟩ : syracuseStep 207639 = 311459) B311459
theorem B305945 : Blo 203807 305945 := bstep (se 2 (by rfl) ⟨114729, by rfl⟩ : syracuseStep 305945 = 229459) B229459
theorem B207659 : Blo 203807 207659 := bstep (se 1 (by rfl) ⟨155744, by rfl⟩ : syracuseStep 207659 = 311489) B311489
theorem B207671 : Blo 203807 207671 := bstep (se 1 (by rfl) ⟨155753, by rfl⟩ : syracuseStep 207671 = 311507) B311507
theorem B207691 : Blo 203807 207691 := bstep (se 1 (by rfl) ⟨155768, by rfl⟩ : syracuseStep 207691 = 311537) B311537
theorem B207703 : Blo 203807 207703 := bstep (se 1 (by rfl) ⟨155777, by rfl⟩ : syracuseStep 207703 = 311555) B311555
theorem B207723 : Blo 203807 207723 := bstep (se 1 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 207723 = 311585) B311585
theorem B207735 : Blo 203807 207735 := bstep (se 1 (by rfl) ⟨155801, by rfl⟩ : syracuseStep 207735 = 311603) B311603
theorem B306059 : Blo 203807 306059 := bstep (se 1 (by rfl) ⟨229544, by rfl⟩ : syracuseStep 306059 = 459089) B459089
theorem B207755 : Blo 203807 207755 := bstep (se 1 (by rfl) ⟨155816, by rfl⟩ : syracuseStep 207755 = 311633) B311633
theorem B306071 : Blo 203807 306071 := bstep (se 1 (by rfl) ⟨229553, by rfl⟩ : syracuseStep 306071 = 459107) B459107
theorem B207767 : Blo 203807 207767 := bstep (se 1 (by rfl) ⟨155825, by rfl⟩ : syracuseStep 207767 = 311651) B311651
theorem B207787 : Blo 203807 207787 := bstep (se 1 (by rfl) ⟨155840, by rfl⟩ : syracuseStep 207787 = 311681) B311681
theorem B207799 : Blo 203807 207799 := bstep (se 1 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 207799 = 311699) B311699
theorem B437195 : Blo 203807 437195 := bstep (se 1 (by rfl) ⟨327896, by rfl⟩ : syracuseStep 437195 = 655793) B655793
theorem B306137 : Blo 203807 306137 := bstep (se 2 (by rfl) ⟨114801, by rfl⟩ : syracuseStep 306137 = 229603) B229603
theorem B699353 : Blo 203807 699353 := bstep (se 2 (by rfl) ⟨262257, by rfl⟩ : syracuseStep 699353 = 524515) B524515
theorem B207883 : Blo 203807 207883 := bstep (se 1 (by rfl) ⟨155912, by rfl⟩ : syracuseStep 207883 = 311825) B311825
theorem B1256465 : Blo 203807 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B306251 : Blo 203807 306251 := bstep (se 1 (by rfl) ⟨229688, by rfl⟩ : syracuseStep 306251 = 459377) B459377
theorem B306263 : Blo 203807 306263 := bstep (se 1 (by rfl) ⟨229697, by rfl⟩ : syracuseStep 306263 = 459395) B459395
theorem B306329 : Blo 203807 306329 := bstep (se 2 (by rfl) ⟨114873, by rfl⟩ : syracuseStep 306329 = 229747) B229747
theorem B1584305 : Blo 203807 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B306443 : Blo 203807 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B306455 : Blo 203807 306455 := bstep (se 1 (by rfl) ⟨229841, by rfl⟩ : syracuseStep 306455 = 459683) B459683
theorem B437555 : Blo 203807 437555 := bstep (se 1 (by rfl) ⟨328166, by rfl⟩ : syracuseStep 437555 = 656333) B656333
theorem B306521 : Blo 203807 306521 := bstep (se 2 (by rfl) ⟨114945, by rfl⟩ : syracuseStep 306521 = 229891) B229891
theorem B372107 : Blo 203807 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B306635 : Blo 203807 306635 := bstep (se 1 (by rfl) ⟨229976, by rfl⟩ : syracuseStep 306635 = 459953) B459953
theorem B306647 : Blo 203807 306647 := bstep (se 1 (by rfl) ⟨229985, by rfl⟩ : syracuseStep 306647 = 459971) B459971
theorem B470539 : Blo 203807 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B306713 : Blo 203807 306713 := bstep (se 2 (by rfl) ⟨115017, by rfl⟩ : syracuseStep 306713 = 230035) B230035
theorem B503347 : Blo 203807 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B306827 : Blo 203807 306827 := bstep (se 1 (by rfl) ⟨230120, by rfl⟩ : syracuseStep 306827 = 460241) B460241
theorem B306839 : Blo 203807 306839 := bstep (se 1 (by rfl) ⟨230129, by rfl⟩ : syracuseStep 306839 = 460259) B460259
theorem B700055 : Blo 203807 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B306905 : Blo 203807 306905 := bstep (se 2 (by rfl) ⟨115089, by rfl⟩ : syracuseStep 306905 = 230179) B230179
theorem B307019 : Blo 203807 307019 := bstep (se 1 (by rfl) ⟨230264, by rfl⟩ : syracuseStep 307019 = 460529) B460529
theorem B307031 : Blo 203807 307031 := bstep (se 1 (by rfl) ⟨230273, by rfl⟩ : syracuseStep 307031 = 460547) B460547
theorem B6762341 : Blo 203807 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B307097 : Blo 203807 307097 := bstep (se 2 (by rfl) ⟨115161, by rfl⟩ : syracuseStep 307097 = 230323) B230323
theorem B307211 : Blo 203807 307211 := bstep (se 1 (by rfl) ⟨230408, by rfl⟩ : syracuseStep 307211 = 460817) B460817
theorem B307223 : Blo 203807 307223 := bstep (se 1 (by rfl) ⟨230417, by rfl⟩ : syracuseStep 307223 = 460835) B460835
theorem B307289 : Blo 203807 307289 := bstep (se 2 (by rfl) ⟨115233, by rfl⟩ : syracuseStep 307289 = 230467) B230467
theorem B700595 : Blo 203807 700595 := bstep (se 1 (by rfl) ⟨525446, by rfl⟩ : syracuseStep 700595 = 1050893) B1050893
theorem B307403 : Blo 203807 307403 := bstep (se 1 (by rfl) ⟨230552, by rfl⟩ : syracuseStep 307403 = 461105) B461105
theorem B307415 : Blo 203807 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B307481 : Blo 203807 307481 := bstep (se 2 (by rfl) ⟨115305, by rfl⟩ : syracuseStep 307481 = 230611) B230611
theorem B307595 : Blo 203807 307595 := bstep (se 1 (by rfl) ⟨230696, by rfl⟩ : syracuseStep 307595 = 461393) B461393
theorem B307607 : Blo 203807 307607 := bstep (se 1 (by rfl) ⟨230705, by rfl⟩ : syracuseStep 307607 = 461411) B461411
theorem B2240945 : Blo 203807 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B700865 : Blo 203807 700865 := bstep (se 2 (by rfl) ⟨262824, by rfl⟩ : syracuseStep 700865 = 525649) B525649
theorem B307673 : Blo 203807 307673 := bstep (se 2 (by rfl) ⟨115377, by rfl⟩ : syracuseStep 307673 = 230755) B230755
theorem B307787 : Blo 203807 307787 := bstep (se 1 (by rfl) ⟨230840, by rfl⟩ : syracuseStep 307787 = 461681) B461681
theorem B1094219 : Blo 203807 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B307799 : Blo 203807 307799 := bstep (se 1 (by rfl) ⟨230849, by rfl⟩ : syracuseStep 307799 = 461699) B461699
theorem B307865 : Blo 203807 307865 := bstep (se 2 (by rfl) ⟨115449, by rfl⟩ : syracuseStep 307865 = 230899) B230899
theorem B2994893 : Blo 203807 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B307979 : Blo 203807 307979 := bstep (se 1 (by rfl) ⟨230984, by rfl⟩ : syracuseStep 307979 = 461969) B461969
theorem B307991 : Blo 203807 307991 := bstep (se 1 (by rfl) ⟨230993, by rfl⟩ : syracuseStep 307991 = 461987) B461987
theorem B308057 : Blo 203807 308057 := bstep (se 2 (by rfl) ⟨115521, by rfl⟩ : syracuseStep 308057 = 231043) B231043
theorem B4469681 : Blo 203807 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B308171 : Blo 203807 308171 := bstep (se 1 (by rfl) ⟨231128, by rfl⟩ : syracuseStep 308171 = 462257) B462257
theorem B308183 : Blo 203807 308183 := bstep (se 1 (by rfl) ⟨231137, by rfl⟩ : syracuseStep 308183 = 462275) B462275
theorem B308249 : Blo 203807 308249 := bstep (se 2 (by rfl) ⟨115593, by rfl⟩ : syracuseStep 308249 = 231187) B231187
theorem B2831435 : Blo 203807 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B308363 : Blo 203807 308363 := bstep (se 1 (by rfl) ⟨231272, by rfl⟩ : syracuseStep 308363 = 462545) B462545
theorem B308375 : Blo 203807 308375 := bstep (se 1 (by rfl) ⟨231281, by rfl⟩ : syracuseStep 308375 = 462563) B462563
theorem B505025 : Blo 203807 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B308441 : Blo 203807 308441 := bstep (se 2 (by rfl) ⟨115665, by rfl⟩ : syracuseStep 308441 = 231331) B231331
theorem B439553 : Blo 203807 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B308555 : Blo 203807 308555 := bstep (se 1 (by rfl) ⟨231416, by rfl⟩ : syracuseStep 308555 = 462833) B462833
theorem B308567 : Blo 203807 308567 := bstep (se 1 (by rfl) ⟨231425, by rfl⟩ : syracuseStep 308567 = 462851) B462851
theorem B374131 : Blo 203807 374131 := bstep (se 1 (by rfl) ⟨280598, by rfl⟩ : syracuseStep 374131 = 561197) B561197
theorem B308633 : Blo 203807 308633 := bstep (se 2 (by rfl) ⟨115737, by rfl⟩ : syracuseStep 308633 = 231475) B231475
theorem B308747 : Blo 203807 308747 := bstep (se 1 (by rfl) ⟨231560, by rfl⟩ : syracuseStep 308747 = 463121) B463121
theorem B308759 : Blo 203807 308759 := bstep (se 1 (by rfl) ⟨231569, by rfl⟩ : syracuseStep 308759 = 463139) B463139
theorem B308825 : Blo 203807 308825 := bstep (se 2 (by rfl) ⟨115809, by rfl⟩ : syracuseStep 308825 = 231619) B231619
theorem B308939 : Blo 203807 308939 := bstep (se 1 (by rfl) ⟨231704, by rfl⟩ : syracuseStep 308939 = 463409) B463409
theorem B308951 : Blo 203807 308951 := bstep (se 1 (by rfl) ⟨231713, by rfl⟩ : syracuseStep 308951 = 463427) B463427
theorem B734999 : Blo 203807 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B309017 : Blo 203807 309017 := bstep (se 2 (by rfl) ⟨115881, by rfl⟩ : syracuseStep 309017 = 231763) B231763
theorem B309131 : Blo 203807 309131 := bstep (se 1 (by rfl) ⟨231848, by rfl⟩ : syracuseStep 309131 = 463697) B463697
theorem B309143 : Blo 203807 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B309209 : Blo 203807 309209 := bstep (se 2 (by rfl) ⟨115953, by rfl⟩ : syracuseStep 309209 = 231907) B231907
theorem B309323 : Blo 203807 309323 := bstep (se 1 (by rfl) ⟨231992, by rfl⟩ : syracuseStep 309323 = 463985) B463985
theorem B440407 : Blo 203807 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B309335 : Blo 203807 309335 := bstep (se 1 (by rfl) ⟨232001, by rfl⟩ : syracuseStep 309335 = 464003) B464003
theorem B309401 : Blo 203807 309401 := bstep (se 2 (by rfl) ⟨116025, by rfl⟩ : syracuseStep 309401 = 232051) B232051
theorem B833753 : Blo 203807 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B309515 : Blo 203807 309515 := bstep (se 1 (by rfl) ⟨232136, by rfl⟩ : syracuseStep 309515 = 464273) B464273
theorem B309527 : Blo 203807 309527 := bstep (se 1 (by rfl) ⟨232145, by rfl⟩ : syracuseStep 309527 = 464291) B464291
theorem B309593 : Blo 203807 309593 := bstep (se 2 (by rfl) ⟨116097, by rfl⟩ : syracuseStep 309593 = 232195) B232195
theorem B309707 : Blo 203807 309707 := bstep (se 1 (by rfl) ⟨232280, by rfl⟩ : syracuseStep 309707 = 464561) B464561
theorem B309719 : Blo 203807 309719 := bstep (se 1 (by rfl) ⟨232289, by rfl⟩ : syracuseStep 309719 = 464579) B464579
theorem B309785 : Blo 203807 309785 := bstep (se 2 (by rfl) ⟨116169, by rfl⟩ : syracuseStep 309785 = 232339) B232339
theorem B309899 : Blo 203807 309899 := bstep (se 1 (by rfl) ⟨232424, by rfl⟩ : syracuseStep 309899 = 464849) B464849
theorem B309911 : Blo 203807 309911 := bstep (se 1 (by rfl) ⟨232433, by rfl⟩ : syracuseStep 309911 = 464867) B464867
theorem B309977 : Blo 203807 309977 := bstep (se 2 (by rfl) ⟨116241, by rfl⟩ : syracuseStep 309977 = 232483) B232483
theorem B310091 : Blo 203807 310091 := bstep (se 1 (by rfl) ⟨232568, by rfl⟩ : syracuseStep 310091 = 465137) B465137
theorem B310103 : Blo 203807 310103 := bstep (se 1 (by rfl) ⟨232577, by rfl⟩ : syracuseStep 310103 = 465155) B465155
theorem B310169 : Blo 203807 310169 := bstep (se 2 (by rfl) ⟨116313, by rfl⟩ : syracuseStep 310169 = 232627) B232627
theorem B277463 : Blo 203807 277463 := bstep (se 1 (by rfl) ⟨208097, by rfl⟩ : syracuseStep 277463 = 416195) B416195
theorem B1326041 : Blo 203807 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B310283 : Blo 203807 310283 := bstep (se 1 (by rfl) ⟨232712, by rfl⟩ : syracuseStep 310283 = 465425) B465425
theorem B310295 : Blo 203807 310295 := bstep (se 1 (by rfl) ⟨232721, by rfl⟩ : syracuseStep 310295 = 465443) B465443
theorem B310361 : Blo 203807 310361 := bstep (se 2 (by rfl) ⟨116385, by rfl⟩ : syracuseStep 310361 = 232771) B232771
theorem B310475 : Blo 203807 310475 := bstep (se 1 (by rfl) ⟨232856, by rfl⟩ : syracuseStep 310475 = 465713) B465713
theorem B310487 : Blo 203807 310487 := bstep (se 1 (by rfl) ⟨232865, by rfl⟩ : syracuseStep 310487 = 465731) B465731
theorem B441587 : Blo 203807 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B933137 : Blo 203807 933137 := bstep (se 2 (by rfl) ⟨349926, by rfl⟩ : syracuseStep 933137 = 699853) B699853
theorem B310553 : Blo 203807 310553 := bstep (se 2 (by rfl) ⟨116457, by rfl⟩ : syracuseStep 310553 = 232915) B232915
theorem B1326401 : Blo 203807 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B310667 : Blo 203807 310667 := bstep (se 1 (by rfl) ⟨233000, by rfl⟩ : syracuseStep 310667 = 466001) B466001
theorem B310679 : Blo 203807 310679 := bstep (se 1 (by rfl) ⟨233009, by rfl⟩ : syracuseStep 310679 = 466019) B466019
theorem B671179 : Blo 203807 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B310745 : Blo 203807 310745 := bstep (se 2 (by rfl) ⟨116529, by rfl⟩ : syracuseStep 310745 = 233059) B233059
theorem B310859 : Blo 203807 310859 := bstep (se 1 (by rfl) ⟨233144, by rfl⟩ : syracuseStep 310859 = 466289) B466289
theorem B310871 : Blo 203807 310871 := bstep (se 1 (by rfl) ⟨233153, by rfl⟩ : syracuseStep 310871 = 466307) B466307
theorem B1752677 : Blo 203807 1752677 := bstep (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) B328627
theorem B310937 : Blo 203807 310937 := bstep (se 2 (by rfl) ⟨116601, by rfl⟩ : syracuseStep 310937 = 233203) B233203
theorem B311051 : Blo 203807 311051 := bstep (se 1 (by rfl) ⟨233288, by rfl⟩ : syracuseStep 311051 = 466577) B466577
theorem B311063 : Blo 203807 311063 := bstep (se 1 (by rfl) ⟨233297, by rfl⟩ : syracuseStep 311063 = 466595) B466595
theorem B311129 : Blo 203807 311129 := bstep (se 2 (by rfl) ⟨116673, by rfl⟩ : syracuseStep 311129 = 233347) B233347
theorem B1326941 : Blo 203807 1326941 := bstep (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) B497603
theorem B311243 : Blo 203807 311243 := bstep (se 1 (by rfl) ⟨233432, by rfl⟩ : syracuseStep 311243 = 466865) B466865
theorem B311255 : Blo 203807 311255 := bstep (se 1 (by rfl) ⟨233441, by rfl⟩ : syracuseStep 311255 = 466883) B466883
theorem B311321 : Blo 203807 311321 := bstep (se 2 (by rfl) ⟨116745, by rfl⟩ : syracuseStep 311321 = 233491) B233491
theorem B2343005 : Blo 203807 2343005 := bstep (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) B878627
theorem B311435 : Blo 203807 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B311447 : Blo 203807 311447 := bstep (se 1 (by rfl) ⟨233585, by rfl⟩ : syracuseStep 311447 = 467171) B467171
theorem B1556657 : Blo 203807 1556657 := bstep (se 2 (by rfl) ⟨583746, by rfl⟩ : syracuseStep 1556657 = 1167493) B1167493
theorem B311513 : Blo 203807 311513 := bstep (se 2 (by rfl) ⟨116817, by rfl⟩ : syracuseStep 311513 = 233635) B233635
theorem B311627 : Blo 203807 311627 := bstep (se 1 (by rfl) ⟨233720, by rfl⟩ : syracuseStep 311627 = 467441) B467441
theorem B442711 : Blo 203807 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B311639 : Blo 203807 311639 := bstep (se 1 (by rfl) ⟨233729, by rfl⟩ : syracuseStep 311639 = 467459) B467459
theorem B344459 : Blo 203807 344459 := bstep (se 1 (by rfl) ⟨258344, by rfl⟩ : syracuseStep 344459 = 516689) B516689
theorem B835991 : Blo 203807 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B311705 : Blo 203807 311705 := bstep (se 2 (by rfl) ⟨116889, by rfl⟩ : syracuseStep 311705 = 233779) B233779
theorem B442817 : Blo 203807 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B344587 : Blo 203807 344587 := bstep (se 1 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 344587 = 516881) B516881
theorem B1032749 : Blo 203807 1032749 := bstep (se 3 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 1032749 = 387281) B387281
theorem B442955 : Blo 203807 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B1065565 : Blo 203807 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B1557143 : Blo 203807 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B344729 : Blo 203807 344729 := bstep (se 2 (by rfl) ⟨129273, by rfl⟩ : syracuseStep 344729 = 258547) B258547
theorem B312025 : Blo 203807 312025 := bstep (se 2 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 312025 = 234019) B234019
theorem B344857 : Blo 203807 344857 := bstep (se 2 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 344857 = 258643) B258643
theorem B1164077 : Blo 203807 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B345431 : Blo 203807 345431 := bstep (se 1 (by rfl) ⟨259073, by rfl⟩ : syracuseStep 345431 = 518147) B518147
theorem B345559 : Blo 203807 345559 := bstep (se 1 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 345559 = 518339) B518339
theorem B313303 : Blo 203807 313303 := bstep (se 1 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 313303 = 469955) B469955
theorem B346187 : Blo 203807 346187 := bstep (se 1 (by rfl) ⟨259640, by rfl⟩ : syracuseStep 346187 = 519281) B519281
theorem B346315 : Blo 203807 346315 := bstep (se 1 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 346315 = 519473) B519473
theorem B1755341 : Blo 203807 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B739601 : Blo 203807 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B346457 : Blo 203807 346457 := bstep (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) B259843
theorem B346585 : Blo 203807 346585 := bstep (se 2 (by rfl) ⟨129969, by rfl⟩ : syracuseStep 346585 = 259939) B259939
theorem B838295 : Blo 203807 838295 := bstep (se 1 (by rfl) ⟨628721, by rfl⟩ : syracuseStep 838295 = 1257443) B1257443
theorem B1002257 : Blo 203807 1002257 := bstep (se 2 (by rfl) ⟨375846, by rfl⟩ : syracuseStep 1002257 = 751693) B751693
theorem B248651 : Blo 203807 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B347159 : Blo 203807 347159 := bstep (se 1 (by rfl) ⟨260369, by rfl⟩ : syracuseStep 347159 = 520739) B520739
theorem B1657901 : Blo 203807 1657901 := bstep (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) B621713
theorem B347287 : Blo 203807 347287 := bstep (se 1 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 347287 = 520931) B520931
theorem B445655 : Blo 203807 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B839105 : Blo 203807 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B347915 : Blo 203807 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B741143 : Blo 203807 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B348043 : Blo 203807 348043 := bstep (se 1 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 348043 = 522065) B522065
theorem B348185 : Blo 203807 348185 := bstep (se 2 (by rfl) ⟨130569, by rfl⟩ : syracuseStep 348185 = 261139) B261139
theorem B315479 : Blo 203807 315479 := bstep (se 1 (by rfl) ⟨236609, by rfl⟩ : syracuseStep 315479 = 473219) B473219
theorem B348313 : Blo 203807 348313 := bstep (se 2 (by rfl) ⟨130617, by rfl⟩ : syracuseStep 348313 = 261235) B261235
theorem B1331473 : Blo 203807 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B1036637 : Blo 203807 1036637 := bstep (se 3 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 1036637 = 388739) B388739
theorem B1167767 : Blo 203807 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B774593 : Blo 203807 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B414209 : Blo 203807 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B217675 : Blo 203807 217675 := bstep (se 1 (by rfl) ⟨163256, by rfl⟩ : syracuseStep 217675 = 326513) B326513
theorem B1659523 : Blo 203807 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B742067 : Blo 203807 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B348887 : Blo 203807 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B873281 : Blo 203807 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B349015 : Blo 203807 349015 := bstep (se 1 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 349015 = 523523) B523523
theorem B873433 : Blo 203807 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B218423 : Blo 203807 218423 := bstep (se 1 (by rfl) ⟨163817, by rfl⟩ : syracuseStep 218423 = 327635) B327635
theorem B349643 : Blo 203807 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B349771 : Blo 203807 349771 := bstep (se 1 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 349771 = 524657) B524657
theorem B349913 : Blo 203807 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B415513 : Blo 203807 415513 := bstep (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) B311635
theorem B350041 : Blo 203807 350041 := bstep (se 2 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 350041 = 262531) B262531
theorem B841603 : Blo 203807 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B776081 : Blo 203807 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B776537 : Blo 203807 776537 := bstep (se 2 (by rfl) ⟨291201, by rfl⟩ : syracuseStep 776537 = 582403) B582403
theorem B1038743 : Blo 203807 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B350615 : Blo 203807 350615 := bstep (se 1 (by rfl) ⟨262961, by rfl⟩ : syracuseStep 350615 = 525923) B525923
theorem B1104401 : Blo 203807 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B2382371 : Blo 203807 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B219691 : Blo 203807 219691 := bstep (se 1 (by rfl) ⟨164768, by rfl⟩ : syracuseStep 219691 = 329537) B329537
theorem B776749 : Blo 203807 776749 := bstep (se 3 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 776749 = 291281) B291281
theorem B744025 : Blo 203807 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B580375 : Blo 203807 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B777053 : Blo 203807 777053 := bstep (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) B291395
theorem B220439 : Blo 203807 220439 := bstep (se 1 (by rfl) ⟨165329, by rfl⟩ : syracuseStep 220439 = 330659) B330659
theorem B941401 : Blo 203807 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B744977 : Blo 203807 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B581195 : Blo 203807 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B3333707 : Blo 203807 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1564433 : Blo 203807 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B515929 : Blo 203807 515929 := bstep (se 2 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 515929 = 386947) B386947
theorem B876851 : Blo 203807 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B746333 : Blo 203807 746333 := bstep (se 3 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 746333 = 279875) B279875
theorem B517043 : Blo 203807 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B517337 : Blo 203807 517337 := bstep (se 2 (by rfl) ⟨194001, by rfl⟩ : syracuseStep 517337 = 388003) B388003
theorem B1795421 : Blo 203807 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B779651 : Blo 203807 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B779665 : Blo 203807 779665 := bstep (se 2 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 779665 = 584749) B584749
theorem B1598899 : Blo 203807 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1173143 : Blo 203807 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B353945 : Blo 203807 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B779969 : Blo 203807 779969 := bstep (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) B584977
theorem B419671 : Blo 203807 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B1042307 : Blo 203807 1042307 := bstep (se 1 (by rfl) ⟨781730, by rfl⟩ : syracuseStep 1042307 = 1563461) B1563461
theorem B1107863 : Blo 203807 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B387031 : Blo 203807 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B583645 : Blo 203807 583645 := bstep (se 3 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 583645 = 218867) B218867
theorem B7596101 : Blo 203807 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B387251 : Blo 203807 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B780637 : Blo 203807 780637 := bstep (se 3 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 780637 = 292739) B292739
theorem B387479 : Blo 203807 387479 := bstep (se 1 (by rfl) ⟨290609, by rfl⟩ : syracuseStep 387479 = 581219) B581219
theorem B2255435 : Blo 203807 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B387737 : Blo 203807 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B748205 : Blo 203807 748205 := bstep (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) B280577
theorem B518987 : Blo 203807 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B879619 : Blo 203807 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B388147 : Blo 203807 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B584921 : Blo 203807 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B1175057 : Blo 203807 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B388633 : Blo 203807 388633 := bstep (se 2 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 388633 = 291475) B291475
theorem B749107 : Blo 203807 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B1568321 : Blo 203807 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B781913 : Blo 203807 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B5893829 : Blo 203807 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B6942449 : Blo 203807 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B519959 : Blo 203807 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B749387 : Blo 203807 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B880577 : Blo 203807 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B257995 : Blo 203807 257995 := bstep (se 1 (by rfl) ⟨193496, by rfl⟩ : syracuseStep 257995 = 386993) B386993
theorem B389195 : Blo 203807 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B389377 : Blo 203807 389377 := bstep (se 2 (by rfl) ⟨146016, by rfl⟩ : syracuseStep 389377 = 292033) B292033
theorem B520627 : Blo 203807 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B520769 : Blo 203807 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B1110629 : Blo 203807 1110629 := bstep (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) B208243
theorem B291595 : Blo 203807 291595 := bstep (se 1 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 291595 = 437393) B437393
theorem B586561 : Blo 203807 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B3240805 : Blo 203807 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B258967 : Blo 203807 258967 := bstep (se 1 (by rfl) ⟨194225, by rfl⟩ : syracuseStep 258967 = 388451) B388451
theorem B390091 : Blo 203807 390091 := bstep (se 1 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 390091 = 585137) B585137
theorem B390167 : Blo 203807 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B3175499 : Blo 203807 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B783539 : Blo 203807 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B783553 : Blo 203807 783553 := bstep (se 2 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 783553 = 587665) B587665
theorem B1111475 : Blo 203807 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B1570265 : Blo 203807 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B1046033 : Blo 203807 1046033 := bstep (se 2 (by rfl) ⟨392262, by rfl⟩ : syracuseStep 1046033 = 784525) B784525
theorem B882251 : Blo 203807 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B390835 : Blo 203807 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B1046195 : Blo 203807 1046195 := bstep (se 1 (by rfl) ⟨784646, by rfl⟩ : syracuseStep 1046195 = 1569293) B1569293
theorem B259787 : Blo 203807 259787 := bstep (se 1 (by rfl) ⟨194840, by rfl⟩ : syracuseStep 259787 = 389681) B389681
theorem B522035 : Blo 203807 522035 := bstep (se 1 (by rfl) ⟨391526, by rfl⟩ : syracuseStep 522035 = 783053) B783053
theorem B391063 : Blo 203807 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B292825 : Blo 203807 292825 := bstep (se 2 (by rfl) ⟨109809, by rfl⟩ : syracuseStep 292825 = 219619) B219619
theorem B391169 : Blo 203807 391169 := bstep (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) B293377
theorem B2586775 : Blo 203807 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B391321 : Blo 203807 391321 := bstep (se 2 (by rfl) ⟨146745, by rfl⟩ : syracuseStep 391321 = 293491) B293491
theorem B620765 : Blo 203807 620765 := bstep (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) B232787
theorem B522571 : Blo 203807 522571 := bstep (se 1 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 522571 = 783857) B783857
theorem B260491 : Blo 203807 260491 := bstep (se 1 (by rfl) ⟨195368, by rfl⟩ : syracuseStep 260491 = 390737) B390737
theorem B588235 : Blo 203807 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B522713 : Blo 203807 522713 := bstep (se 2 (by rfl) ⟨196017, by rfl⟩ : syracuseStep 522713 = 392035) B392035
theorem B1309229 : Blo 203807 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B260759 : Blo 203807 260759 := bstep (se 1 (by rfl) ⟨195569, by rfl⟩ : syracuseStep 260759 = 391139) B391139
theorem B588505 : Blo 203807 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B588509 : Blo 203807 588509 := bstep (se 3 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 588509 = 220691) B220691
theorem B948995 : Blo 203807 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B293719 : Blo 203807 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B785483 : Blo 203807 785483 := bstep (se 1 (by rfl) ⟨589112, by rfl⟩ : syracuseStep 785483 = 1178225) B1178225
theorem B785497 : Blo 203807 785497 := bstep (se 2 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 785497 = 589123) B589123
theorem B392459 : Blo 203807 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B523543 : Blo 203807 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B261463 : Blo 203807 261463 := bstep (se 1 (by rfl) ⟨196097, by rfl⟩ : syracuseStep 261463 = 392195) B392195
theorem B1080707 : Blo 203807 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B294283 : Blo 203807 294283 := bstep (se 1 (by rfl) ⟨220712, by rfl⟩ : syracuseStep 294283 = 441425) B441425
theorem B392627 : Blo 203807 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B327179 : Blo 203807 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B392779 : Blo 203807 392779 := bstep (se 1 (by rfl) ⟨294584, by rfl⟩ : syracuseStep 392779 = 589169) B589169
theorem B1048139 : Blo 203807 1048139 := bstep (se 1 (by rfl) ⟨786104, by rfl⟩ : syracuseStep 1048139 = 1572209) B1572209
theorem B523979 : Blo 203807 523979 := bstep (se 1 (by rfl) ⟨392984, by rfl⟩ : syracuseStep 523979 = 785969) B785969
theorem B458585 : Blo 203807 458585 := bstep (se 2 (by rfl) ⟨171969, by rfl⟩ : syracuseStep 458585 = 343939) B343939
theorem B1671005 : Blo 203807 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B393113 : Blo 203807 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B458675 : Blo 203807 458675 := bstep (se 1 (by rfl) ⟨344006, by rfl⟩ : syracuseStep 458675 = 688013) B688013
theorem B458711 : Blo 203807 458711 := bstep (se 1 (by rfl) ⟨344033, by rfl⟩ : syracuseStep 458711 = 688067) B688067
theorem B1114073 : Blo 203807 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B524303 : Blo 203807 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B589943 : Blo 203807 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B262279 : Blo 203807 262279 := bstep (se 1 (by rfl) ⟨196709, by rfl⟩ : syracuseStep 262279 = 393419) B393419
theorem B229639 : Blo 203807 229639 := bstep (se 1 (by rfl) ⟨172229, by rfl⟩ : syracuseStep 229639 = 344459) B344459
theorem B557327 : Blo 203807 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B295211 : Blo 203807 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B688499 : Blo 203807 688499 := bstep (se 1 (by rfl) ⟨516374, by rfl⟩ : syracuseStep 688499 = 1032749) B1032749
theorem B459143 : Blo 203807 459143 := bstep (se 1 (by rfl) ⟨344357, by rfl⟩ : syracuseStep 459143 = 688715) B688715
theorem B229819 : Blo 203807 229819 := bstep (se 1 (by rfl) ⟨172364, by rfl⟩ : syracuseStep 229819 = 344729) B344729
theorem B786955 : Blo 203807 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B1049111 : Blo 203807 1049111 := bstep (se 1 (by rfl) ⟨786833, by rfl⟩ : syracuseStep 1049111 = 1573667) B1573667
theorem B459323 : Blo 203807 459323 := bstep (se 1 (by rfl) ⟨344492, by rfl⟩ : syracuseStep 459323 = 688985) B688985
theorem B459449 : Blo 203807 459449 := bstep (se 2 (by rfl) ⟨172293, by rfl⟩ : syracuseStep 459449 = 344587) B344587
theorem B525001 : Blo 203807 525001 := bstep (se 2 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 525001 = 393751) B393751
theorem B787259 : Blo 203807 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B525143 : Blo 203807 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B230287 : Blo 203807 230287 := bstep (se 1 (by rfl) ⟨172715, by rfl⟩ : syracuseStep 230287 = 345431) B345431
theorem B459791 : Blo 203807 459791 := bstep (se 1 (by rfl) ⟨344843, by rfl⟩ : syracuseStep 459791 = 689687) B689687
theorem B459809 : Blo 203807 459809 := bstep (se 2 (by rfl) ⟨172428, by rfl⟩ : syracuseStep 459809 = 344857) B344857
theorem B394283 : Blo 203807 394283 := bstep (se 1 (by rfl) ⟨295712, by rfl⟩ : syracuseStep 394283 = 591425) B591425
theorem B590935 : Blo 203807 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B787745 : Blo 203807 787745 := bstep (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) B590809
theorem B460151 : Blo 203807 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B230791 : Blo 203807 230791 := bstep (se 1 (by rfl) ⟨173093, by rfl⟩ : syracuseStep 230791 = 346187) B346187
theorem B493067 : Blo 203807 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B1181213 : Blo 203807 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B460331 : Blo 203807 460331 := bstep (se 1 (by rfl) ⟨345248, by rfl⟩ : syracuseStep 460331 = 690497) B690497
theorem B230971 : Blo 203807 230971 := bstep (se 1 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 230971 = 346457) B346457
theorem B329275 : Blo 203807 329275 := bstep (se 1 (by rfl) ⟨246956, by rfl⟩ : syracuseStep 329275 = 493913) B493913
theorem B7603789 : Blo 203807 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B558863 : Blo 203807 558863 := bstep (se 1 (by rfl) ⟨419147, by rfl⟩ : syracuseStep 558863 = 838295) B838295
theorem B2361125 : Blo 203807 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B460691 : Blo 203807 460691 := bstep (se 1 (by rfl) ⟨345518, by rfl⟩ : syracuseStep 460691 = 691037) B691037
theorem B2131865 : Blo 203807 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B460745 : Blo 203807 460745 := bstep (se 2 (by rfl) ⟨172779, by rfl⟩ : syracuseStep 460745 = 345559) B345559
theorem B231439 : Blo 203807 231439 := bstep (se 1 (by rfl) ⟨173579, by rfl⟩ : syracuseStep 231439 = 347159) B347159
theorem B4982957 : Blo 203807 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B788717 : Blo 203807 788717 := bstep (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) B295769
theorem B657665 : Blo 203807 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B559403 : Blo 203807 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B559561 : Blo 203807 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B231943 : Blo 203807 231943 := bstep (se 1 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 231943 = 347915) B347915
theorem B494095 : Blo 203807 494095 := bstep (se 1 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 494095 = 741143) B741143
theorem B461447 : Blo 203807 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B232123 : Blo 203807 232123 := bstep (se 1 (by rfl) ⟨174092, by rfl⟩ : syracuseStep 232123 = 348185) B348185
theorem B4950821 : Blo 203807 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B461627 : Blo 203807 461627 := bstep (se 1 (by rfl) ⟨346220, by rfl⟩ : syracuseStep 461627 = 692441) B692441
theorem B1182599 : Blo 203807 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B691091 : Blo 203807 691091 := bstep (se 1 (by rfl) ⟨518318, by rfl⟩ : syracuseStep 691091 = 1036637) B1036637
theorem B461753 : Blo 203807 461753 := bstep (se 2 (by rfl) ⟨173157, by rfl⟩ : syracuseStep 461753 = 346315) B346315
theorem B494711 : Blo 203807 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B232591 : Blo 203807 232591 := bstep (se 1 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 232591 = 348887) B348887
theorem B462095 : Blo 203807 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B462113 : Blo 203807 462113 := bstep (se 2 (by rfl) ⟨173292, by rfl⟩ : syracuseStep 462113 = 346585) B346585
theorem B462455 : Blo 203807 462455 := bstep (se 1 (by rfl) ⟨346841, by rfl⟩ : syracuseStep 462455 = 693683) B693683
theorem B233095 : Blo 203807 233095 := bstep (se 1 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 233095 = 349643) B349643
theorem B495305 : Blo 203807 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B397001 : Blo 203807 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B462635 : Blo 203807 462635 := bstep (se 1 (by rfl) ⟨346976, by rfl⟩ : syracuseStep 462635 = 693953) B693953
theorem B233275 : Blo 203807 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B1576793 : Blo 203807 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B462995 : Blo 203807 462995 := bstep (se 1 (by rfl) ⟨347246, by rfl⟩ : syracuseStep 462995 = 694493) B694493
theorem B463049 : Blo 203807 463049 := bstep (se 2 (by rfl) ⟨173643, by rfl⟩ : syracuseStep 463049 = 347287) B347287
theorem B692495 : Blo 203807 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B233743 : Blo 203807 233743 := bstep (se 1 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 233743 = 350615) B350615
theorem B332075 : Blo 203807 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B692765 : Blo 203807 692765 := bstep (se 3 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 692765 = 259787) B259787
theorem B332407 : Blo 203807 332407 := bstep (se 1 (by rfl) ⟨249305, by rfl⟩ : syracuseStep 332407 = 498611) B498611
theorem B5968565 : Blo 203807 5968565 := bstep (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) B559553
theorem B627385 : Blo 203807 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B463751 : Blo 203807 463751 := bstep (se 1 (by rfl) ⟨347813, by rfl⟩ : syracuseStep 463751 = 695627) B695627
theorem B496651 : Blo 203807 496651 := bstep (se 1 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 496651 = 744977) B744977
theorem B463931 : Blo 203807 463931 := bstep (se 1 (by rfl) ⟨347948, by rfl⟩ : syracuseStep 463931 = 695897) B695897
theorem B464057 : Blo 203807 464057 := bstep (se 2 (by rfl) ⟨174021, by rfl⟩ : syracuseStep 464057 = 348043) B348043
theorem B1119539 : Blo 203807 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B464399 : Blo 203807 464399 := bstep (se 1 (by rfl) ⟨348299, by rfl⟩ : syracuseStep 464399 = 696599) B696599
theorem B464417 : Blo 203807 464417 := bstep (se 2 (by rfl) ⟨174156, by rfl⟩ : syracuseStep 464417 = 348313) B348313
theorem B1775297 : Blo 203807 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B464759 : Blo 203807 464759 := bstep (se 1 (by rfl) ⟨348569, by rfl⟩ : syracuseStep 464759 = 697139) B697139
theorem B497555 : Blo 203807 497555 := bstep (se 1 (by rfl) ⟨373166, by rfl⟩ : syracuseStep 497555 = 746333) B746333
theorem B694169 : Blo 203807 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B464939 : Blo 203807 464939 := bstep (se 1 (by rfl) ⟨348704, by rfl⟩ : syracuseStep 464939 = 697409) B697409
theorem B465299 : Blo 203807 465299 := bstep (se 1 (by rfl) ⟨348974, by rfl⟩ : syracuseStep 465299 = 697949) B697949
theorem B235963 : Blo 203807 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B465353 : Blo 203807 465353 := bstep (se 2 (by rfl) ⟨174507, by rfl⟩ : syracuseStep 465353 = 349015) B349015
theorem B694871 : Blo 203807 694871 := bstep (se 1 (by rfl) ⟨521153, by rfl⟩ : syracuseStep 694871 = 1042307) B1042307
theorem B203835 : Blo 203807 203835 := bstep (se 1 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 203835 = 305753) B305753
theorem B695357 : Blo 203807 695357 := bstep (se 3 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 695357 = 260759) B260759
theorem B498803 : Blo 203807 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B5020805 : Blo 203807 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B203911 : Blo 203807 203911 := bstep (se 1 (by rfl) ⟨152933, by rfl⟩ : syracuseStep 203911 = 305867) B305867
theorem B466055 : Blo 203807 466055 := bstep (se 1 (by rfl) ⟨349541, by rfl⟩ : syracuseStep 466055 = 699083) B699083
theorem B203919 : Blo 203807 203919 := bstep (se 1 (by rfl) ⟨152939, by rfl⟩ : syracuseStep 203919 = 305879) B305879
theorem B269455 : Blo 203807 269455 := bstep (se 1 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 269455 = 404183) B404183
theorem B498841 : Blo 203807 498841 := bstep (se 2 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 498841 = 374131) B374131
theorem B203963 : Blo 203807 203963 := bstep (se 1 (by rfl) ⟨152972, by rfl⟩ : syracuseStep 203963 = 305945) B305945
theorem B204039 : Blo 203807 204039 := bstep (se 1 (by rfl) ⟨153029, by rfl⟩ : syracuseStep 204039 = 306059) B306059
theorem B204047 : Blo 203807 204047 := bstep (se 1 (by rfl) ⟨153035, by rfl⟩ : syracuseStep 204047 = 306071) B306071
theorem B204091 : Blo 203807 204091 := bstep (se 1 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 204091 = 306137) B306137
theorem B466235 : Blo 203807 466235 := bstep (se 1 (by rfl) ⟨349676, by rfl⟩ : syracuseStep 466235 = 699353) B699353
theorem B204167 : Blo 203807 204167 := bstep (se 1 (by rfl) ⟨153125, by rfl⟩ : syracuseStep 204167 = 306251) B306251
theorem B204175 : Blo 203807 204175 := bstep (se 1 (by rfl) ⟨153131, by rfl⟩ : syracuseStep 204175 = 306263) B306263
theorem B466361 : Blo 203807 466361 := bstep (se 2 (by rfl) ⟨174885, by rfl⟩ : syracuseStep 466361 = 349771) B349771
theorem B204219 : Blo 203807 204219 := bstep (se 1 (by rfl) ⟨153164, by rfl⟩ : syracuseStep 204219 = 306329) B306329
theorem B1056203 : Blo 203807 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B204295 : Blo 203807 204295 := bstep (se 1 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 204295 = 306443) B306443
theorem B204303 : Blo 203807 204303 := bstep (se 1 (by rfl) ⟨153227, by rfl⟩ : syracuseStep 204303 = 306455) B306455
theorem B204347 : Blo 203807 204347 := bstep (se 1 (by rfl) ⟨153260, by rfl⟩ : syracuseStep 204347 = 306521) B306521
theorem B204423 : Blo 203807 204423 := bstep (se 1 (by rfl) ⟨153317, by rfl⟩ : syracuseStep 204423 = 306635) B306635
theorem B204431 : Blo 203807 204431 := bstep (se 1 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 204431 = 306647) B306647
theorem B204475 : Blo 203807 204475 := bstep (se 1 (by rfl) ⟨153356, by rfl⟩ : syracuseStep 204475 = 306713) B306713
theorem B204551 : Blo 203807 204551 := bstep (se 1 (by rfl) ⟨153413, by rfl⟩ : syracuseStep 204551 = 306827) B306827
theorem B204559 : Blo 203807 204559 := bstep (se 1 (by rfl) ⟨153419, by rfl⟩ : syracuseStep 204559 = 306839) B306839
theorem B466703 : Blo 203807 466703 := bstep (se 1 (by rfl) ⟨350027, by rfl⟩ : syracuseStep 466703 = 700055) B700055
theorem B663329 : Blo 203807 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B466721 : Blo 203807 466721 := bstep (se 2 (by rfl) ⟨175020, by rfl⟩ : syracuseStep 466721 = 350041) B350041
theorem B204603 : Blo 203807 204603 := bstep (se 1 (by rfl) ⟨153452, by rfl⟩ : syracuseStep 204603 = 306905) B306905
theorem B1122137 : Blo 203807 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B204679 : Blo 203807 204679 := bstep (se 1 (by rfl) ⟨153509, by rfl⟩ : syracuseStep 204679 = 307019) B307019
theorem B499591 : Blo 203807 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B204687 : Blo 203807 204687 := bstep (se 1 (by rfl) ⟨153515, by rfl⟩ : syracuseStep 204687 = 307031) B307031
theorem B204731 : Blo 203807 204731 := bstep (se 1 (by rfl) ⟨153548, by rfl⟩ : syracuseStep 204731 = 307097) B307097
theorem B663481 : Blo 203807 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B204807 : Blo 203807 204807 := bstep (se 1 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 204807 = 307211) B307211
theorem B204815 : Blo 203807 204815 := bstep (se 1 (by rfl) ⟨153611, by rfl⟩ : syracuseStep 204815 = 307223) B307223
theorem B204859 : Blo 203807 204859 := bstep (se 1 (by rfl) ⟨153644, by rfl⟩ : syracuseStep 204859 = 307289) B307289
theorem B467063 : Blo 203807 467063 := bstep (se 1 (by rfl) ⟨350297, by rfl⟩ : syracuseStep 467063 = 700595) B700595
theorem B204935 : Blo 203807 204935 := bstep (se 1 (by rfl) ⟨153701, by rfl⟩ : syracuseStep 204935 = 307403) B307403
theorem B204943 : Blo 203807 204943 := bstep (se 1 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 204943 = 307415) B307415
theorem B204987 : Blo 203807 204987 := bstep (se 1 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 204987 = 307481) B307481
theorem B3449033 : Blo 203807 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B205063 : Blo 203807 205063 := bstep (se 1 (by rfl) ⟨153797, by rfl⟩ : syracuseStep 205063 = 307595) B307595
theorem B205071 : Blo 203807 205071 := bstep (se 1 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 205071 = 307607) B307607
theorem B467243 : Blo 203807 467243 := bstep (se 1 (by rfl) ⟨350432, by rfl⟩ : syracuseStep 467243 = 700865) B700865
theorem B205115 : Blo 203807 205115 := bstep (se 1 (by rfl) ⟨153836, by rfl⟩ : syracuseStep 205115 = 307673) B307673
theorem B205191 : Blo 203807 205191 := bstep (se 1 (by rfl) ⟨153893, by rfl⟩ : syracuseStep 205191 = 307787) B307787
theorem B729479 : Blo 203807 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B205199 : Blo 203807 205199 := bstep (se 1 (by rfl) ⟨153899, by rfl⟩ : syracuseStep 205199 = 307799) B307799
theorem B696761 : Blo 203807 696761 := bstep (se 2 (by rfl) ⟨261285, by rfl⟩ : syracuseStep 696761 = 522571) B522571
theorem B205243 : Blo 203807 205243 := bstep (se 1 (by rfl) ⟨153932, by rfl⟩ : syracuseStep 205243 = 307865) B307865
theorem B205319 : Blo 203807 205319 := bstep (se 1 (by rfl) ⟨153989, by rfl⟩ : syracuseStep 205319 = 307979) B307979
theorem B205327 : Blo 203807 205327 := bstep (se 1 (by rfl) ⟨153995, by rfl⟩ : syracuseStep 205327 = 307991) B307991
theorem B205371 : Blo 203807 205371 := bstep (se 1 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 205371 = 308057) B308057
theorem B1188413 : Blo 203807 1188413 := bstep (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) B445655
theorem B205447 : Blo 203807 205447 := bstep (se 1 (by rfl) ⟨154085, by rfl⟩ : syracuseStep 205447 = 308171) B308171
theorem B205455 : Blo 203807 205455 := bstep (se 1 (by rfl) ⟨154091, by rfl⟩ : syracuseStep 205455 = 308183) B308183
theorem B205499 : Blo 203807 205499 := bstep (se 1 (by rfl) ⟨154124, by rfl⟩ : syracuseStep 205499 = 308249) B308249
theorem B205575 : Blo 203807 205575 := bstep (se 1 (by rfl) ⟨154181, by rfl⟩ : syracuseStep 205575 = 308363) B308363
theorem B205583 : Blo 203807 205583 := bstep (se 1 (by rfl) ⟨154187, by rfl⟩ : syracuseStep 205583 = 308375) B308375
theorem B992033 : Blo 203807 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B336683 : Blo 203807 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B205627 : Blo 203807 205627 := bstep (se 1 (by rfl) ⟨154220, by rfl⟩ : syracuseStep 205627 = 308441) B308441
theorem B205703 : Blo 203807 205703 := bstep (se 1 (by rfl) ⟨154277, by rfl⟩ : syracuseStep 205703 = 308555) B308555
theorem B205711 : Blo 203807 205711 := bstep (se 1 (by rfl) ⟨154283, by rfl⟩ : syracuseStep 205711 = 308567) B308567
theorem B205755 : Blo 203807 205755 := bstep (se 1 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 205755 = 308633) B308633
theorem B205831 : Blo 203807 205831 := bstep (se 1 (by rfl) ⟨154373, by rfl⟩ : syracuseStep 205831 = 308747) B308747
theorem B697355 : Blo 203807 697355 := bstep (se 1 (by rfl) ⟨523016, by rfl⟩ : syracuseStep 697355 = 1046033) B1046033
theorem B205839 : Blo 203807 205839 := bstep (se 1 (by rfl) ⟨154379, by rfl⟩ : syracuseStep 205839 = 308759) B308759
theorem B205883 : Blo 203807 205883 := bstep (se 1 (by rfl) ⟨154412, by rfl⟩ : syracuseStep 205883 = 308825) B308825
theorem B697463 : Blo 203807 697463 := bstep (se 1 (by rfl) ⟨523097, by rfl⟩ : syracuseStep 697463 = 1046195) B1046195
theorem B205959 : Blo 203807 205959 := bstep (se 1 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 205959 = 308939) B308939
theorem B205967 : Blo 203807 205967 := bstep (se 1 (by rfl) ⟨154475, by rfl⟩ : syracuseStep 205967 = 308951) B308951
theorem B206011 : Blo 203807 206011 := bstep (se 1 (by rfl) ⟨154508, by rfl⟩ : syracuseStep 206011 = 309017) B309017
theorem B206087 : Blo 203807 206087 := bstep (se 1 (by rfl) ⟨154565, by rfl⟩ : syracuseStep 206087 = 309131) B309131
theorem B206095 : Blo 203807 206095 := bstep (se 1 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 206095 = 309143) B309143
theorem B206139 : Blo 203807 206139 := bstep (se 1 (by rfl) ⟨154604, by rfl⟩ : syracuseStep 206139 = 309209) B309209
theorem B206215 : Blo 203807 206215 := bstep (se 1 (by rfl) ⟨154661, by rfl⟩ : syracuseStep 206215 = 309323) B309323
theorem B206223 : Blo 203807 206223 := bstep (se 1 (by rfl) ⟨154667, by rfl⟩ : syracuseStep 206223 = 309335) B309335
theorem B206267 : Blo 203807 206267 := bstep (se 1 (by rfl) ⟨154700, by rfl⟩ : syracuseStep 206267 = 309401) B309401
theorem B1320401 : Blo 203807 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B206343 : Blo 203807 206343 := bstep (se 1 (by rfl) ⟨154757, by rfl⟩ : syracuseStep 206343 = 309515) B309515
theorem B206351 : Blo 203807 206351 := bstep (se 1 (by rfl) ⟨154763, by rfl⟩ : syracuseStep 206351 = 309527) B309527
theorem B1549853 : Blo 203807 1549853 := bstep (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) B581195
theorem B206395 : Blo 203807 206395 := bstep (se 1 (by rfl) ⟨154796, by rfl⟩ : syracuseStep 206395 = 309593) B309593
theorem B206471 : Blo 203807 206471 := bstep (se 1 (by rfl) ⟨154853, by rfl⟩ : syracuseStep 206471 = 309707) B309707
theorem B206479 : Blo 203807 206479 := bstep (se 1 (by rfl) ⟨154859, by rfl⟩ : syracuseStep 206479 = 309719) B309719
theorem B206523 : Blo 203807 206523 := bstep (se 1 (by rfl) ⟨154892, by rfl⟩ : syracuseStep 206523 = 309785) B309785
theorem B698057 : Blo 203807 698057 := bstep (se 2 (by rfl) ⟨261771, by rfl⟩ : syracuseStep 698057 = 523543) B523543
theorem B206599 : Blo 203807 206599 := bstep (se 1 (by rfl) ⟨154949, by rfl⟩ : syracuseStep 206599 = 309899) B309899
theorem B206607 : Blo 203807 206607 := bstep (se 1 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 206607 = 309911) B309911
theorem B206651 : Blo 203807 206651 := bstep (se 1 (by rfl) ⟨154988, by rfl⟩ : syracuseStep 206651 = 309977) B309977
theorem B632663 : Blo 203807 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B206727 : Blo 203807 206727 := bstep (se 1 (by rfl) ⟨155045, by rfl⟩ : syracuseStep 206727 = 310091) B310091
theorem B206735 : Blo 203807 206735 := bstep (se 1 (by rfl) ⟨155051, by rfl⟩ : syracuseStep 206735 = 310103) B310103
theorem B894905 : Blo 203807 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B206779 : Blo 203807 206779 := bstep (se 1 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 206779 = 310169) B310169
theorem B206855 : Blo 203807 206855 := bstep (se 1 (by rfl) ⟨155141, by rfl⟩ : syracuseStep 206855 = 310283) B310283
theorem B206863 : Blo 203807 206863 := bstep (se 1 (by rfl) ⟨155147, by rfl⟩ : syracuseStep 206863 = 310295) B310295
theorem B206907 : Blo 203807 206907 := bstep (se 1 (by rfl) ⟨155180, by rfl⟩ : syracuseStep 206907 = 310361) B310361
theorem B206983 : Blo 203807 206983 := bstep (se 1 (by rfl) ⟨155237, by rfl⟩ : syracuseStep 206983 = 310475) B310475
theorem B206991 : Blo 203807 206991 := bstep (se 1 (by rfl) ⟨155243, by rfl⟩ : syracuseStep 206991 = 310487) B310487
theorem B207035 : Blo 203807 207035 := bstep (se 1 (by rfl) ⟨155276, by rfl⟩ : syracuseStep 207035 = 310553) B310553
theorem B207111 : Blo 203807 207111 := bstep (se 1 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 207111 = 310667) B310667
theorem B207119 : Blo 203807 207119 := bstep (se 1 (by rfl) ⟨155339, by rfl⟩ : syracuseStep 207119 = 310679) B310679
theorem B207163 : Blo 203807 207163 := bstep (se 1 (by rfl) ⟨155372, by rfl⟩ : syracuseStep 207163 = 310745) B310745
theorem B698759 : Blo 203807 698759 := bstep (se 1 (by rfl) ⟨524069, by rfl⟩ : syracuseStep 698759 = 1048139) B1048139
theorem B207239 : Blo 203807 207239 := bstep (se 1 (by rfl) ⟨155429, by rfl⟩ : syracuseStep 207239 = 310859) B310859
theorem B207247 : Blo 203807 207247 := bstep (se 1 (by rfl) ⟨155435, by rfl⟩ : syracuseStep 207247 = 310871) B310871
theorem B207291 : Blo 203807 207291 := bstep (se 1 (by rfl) ⟨155468, by rfl⟩ : syracuseStep 207291 = 310937) B310937
theorem B207367 : Blo 203807 207367 := bstep (se 1 (by rfl) ⟨155525, by rfl⟩ : syracuseStep 207367 = 311051) B311051
theorem B207375 : Blo 203807 207375 := bstep (se 1 (by rfl) ⟨155531, by rfl⟩ : syracuseStep 207375 = 311063) B311063
theorem B305723 : Blo 203807 305723 := bstep (se 1 (by rfl) ⟨229292, by rfl⟩ : syracuseStep 305723 = 458585) B458585
theorem B207419 : Blo 203807 207419 := bstep (se 1 (by rfl) ⟨155564, by rfl⟩ : syracuseStep 207419 = 311129) B311129
theorem B305783 : Blo 203807 305783 := bstep (se 1 (by rfl) ⟨229337, by rfl⟩ : syracuseStep 305783 = 458675) B458675
theorem B207495 : Blo 203807 207495 := bstep (se 1 (by rfl) ⟨155621, by rfl⟩ : syracuseStep 207495 = 311243) B311243
theorem B305807 : Blo 203807 305807 := bstep (se 1 (by rfl) ⟨229355, by rfl⟩ : syracuseStep 305807 = 458711) B458711
theorem B207503 : Blo 203807 207503 := bstep (se 1 (by rfl) ⟨155627, by rfl⟩ : syracuseStep 207503 = 311255) B311255
theorem B305849 : Blo 203807 305849 := bstep (se 2 (by rfl) ⟨114693, by rfl⟩ : syracuseStep 305849 = 229387) B229387
theorem B207547 : Blo 203807 207547 := bstep (se 1 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 207547 = 311321) B311321
theorem B699137 : Blo 203807 699137 := bstep (se 2 (by rfl) ⟨262176, by rfl⟩ : syracuseStep 699137 = 524353) B524353
theorem B305927 : Blo 203807 305927 := bstep (se 1 (by rfl) ⟨229445, by rfl⟩ : syracuseStep 305927 = 458891) B458891
theorem B207623 : Blo 203807 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B207631 : Blo 203807 207631 := bstep (se 1 (by rfl) ⟨155723, by rfl⟩ : syracuseStep 207631 = 311447) B311447
theorem B305963 : Blo 203807 305963 := bstep (se 1 (by rfl) ⟨229472, by rfl⟩ : syracuseStep 305963 = 458945) B458945
theorem B437051 : Blo 203807 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B207675 : Blo 203807 207675 := bstep (se 1 (by rfl) ⟨155756, by rfl⟩ : syracuseStep 207675 = 311513) B311513
theorem B305993 : Blo 203807 305993 := bstep (se 2 (by rfl) ⟨114747, by rfl⟩ : syracuseStep 305993 = 229495) B229495
theorem B207751 : Blo 203807 207751 := bstep (se 1 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 207751 = 311627) B311627
theorem B207759 : Blo 203807 207759 := bstep (se 1 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 207759 = 311639) B311639
theorem B306107 : Blo 203807 306107 := bstep (se 1 (by rfl) ⟨229580, by rfl⟩ : syracuseStep 306107 = 459161) B459161
theorem B207803 : Blo 203807 207803 := bstep (se 1 (by rfl) ⟨155852, by rfl⟩ : syracuseStep 207803 = 311705) B311705
theorem B306167 : Blo 203807 306167 := bstep (se 1 (by rfl) ⟨229625, by rfl⟩ : syracuseStep 306167 = 459251) B459251
theorem B306191 : Blo 203807 306191 := bstep (se 1 (by rfl) ⟨229643, by rfl⟩ : syracuseStep 306191 = 459287) B459287
theorem B306233 : Blo 203807 306233 := bstep (se 2 (by rfl) ⟨114837, by rfl⟩ : syracuseStep 306233 = 229675) B229675
theorem B502843 : Blo 203807 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B306311 : Blo 203807 306311 := bstep (se 1 (by rfl) ⟨229733, by rfl⟩ : syracuseStep 306311 = 459467) B459467
theorem B306347 : Blo 203807 306347 := bstep (se 1 (by rfl) ⟨229760, by rfl⟩ : syracuseStep 306347 = 459521) B459521
theorem B306377 : Blo 203807 306377 := bstep (se 2 (by rfl) ⟨114891, by rfl⟩ : syracuseStep 306377 = 229783) B229783
theorem B437537 : Blo 203807 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B830753 : Blo 203807 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B306491 : Blo 203807 306491 := bstep (se 1 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 306491 = 459737) B459737
theorem B306551 : Blo 203807 306551 := bstep (se 1 (by rfl) ⟨229913, by rfl⟩ : syracuseStep 306551 = 459827) B459827
theorem B306575 : Blo 203807 306575 := bstep (se 1 (by rfl) ⟨229931, by rfl⟩ : syracuseStep 306575 = 459863) B459863
theorem B306617 : Blo 203807 306617 := bstep (se 2 (by rfl) ⟨114981, by rfl⟩ : syracuseStep 306617 = 229963) B229963
theorem B1420753 : Blo 203807 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B306695 : Blo 203807 306695 := bstep (se 1 (by rfl) ⟨230021, by rfl⟩ : syracuseStep 306695 = 460043) B460043
theorem B306731 : Blo 203807 306731 := bstep (se 1 (by rfl) ⟨230048, by rfl⟩ : syracuseStep 306731 = 460097) B460097
theorem B699947 : Blo 203807 699947 := bstep (se 1 (by rfl) ⟨524960, by rfl⟩ : syracuseStep 699947 = 1049921) B1049921
theorem B306761 : Blo 203807 306761 := bstep (se 2 (by rfl) ⟨115035, by rfl⟩ : syracuseStep 306761 = 230071) B230071
theorem B437879 : Blo 203807 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B306875 : Blo 203807 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B306935 : Blo 203807 306935 := bstep (se 1 (by rfl) ⟨230201, by rfl⟩ : syracuseStep 306935 = 460403) B460403
theorem B306959 : Blo 203807 306959 := bstep (se 1 (by rfl) ⟨230219, by rfl⟩ : syracuseStep 306959 = 460439) B460439
theorem B307001 : Blo 203807 307001 := bstep (se 2 (by rfl) ⟨115125, by rfl⟩ : syracuseStep 307001 = 230251) B230251
theorem B307079 : Blo 203807 307079 := bstep (se 1 (by rfl) ⟨230309, by rfl⟩ : syracuseStep 307079 = 460619) B460619
theorem B307115 : Blo 203807 307115 := bstep (se 1 (by rfl) ⟨230336, by rfl⟩ : syracuseStep 307115 = 460673) B460673
theorem B307145 : Blo 203807 307145 := bstep (se 2 (by rfl) ⟨115179, by rfl⟩ : syracuseStep 307145 = 230359) B230359
theorem B307259 : Blo 203807 307259 := bstep (se 1 (by rfl) ⟨230444, by rfl⟩ : syracuseStep 307259 = 460889) B460889
theorem B1749053 : Blo 203807 1749053 := bstep (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) B655895
theorem B307319 : Blo 203807 307319 := bstep (se 1 (by rfl) ⟨230489, by rfl⟩ : syracuseStep 307319 = 460979) B460979
theorem B307343 : Blo 203807 307343 := bstep (se 1 (by rfl) ⟨230507, by rfl⟩ : syracuseStep 307343 = 461015) B461015
theorem B307385 : Blo 203807 307385 := bstep (se 2 (by rfl) ⟨115269, by rfl⟩ : syracuseStep 307385 = 230539) B230539
theorem B307463 : Blo 203807 307463 := bstep (se 1 (by rfl) ⟨230597, by rfl⟩ : syracuseStep 307463 = 461195) B461195
theorem B2961677 : Blo 203807 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B307499 : Blo 203807 307499 := bstep (se 1 (by rfl) ⟨230624, by rfl⟩ : syracuseStep 307499 = 461249) B461249
theorem B307529 : Blo 203807 307529 := bstep (se 2 (by rfl) ⟨115323, by rfl⟩ : syracuseStep 307529 = 230647) B230647
theorem B307643 : Blo 203807 307643 := bstep (se 1 (by rfl) ⟨230732, by rfl⟩ : syracuseStep 307643 = 461465) B461465
theorem B307703 : Blo 203807 307703 := bstep (se 1 (by rfl) ⟨230777, by rfl⟩ : syracuseStep 307703 = 461555) B461555
theorem B668171 : Blo 203807 668171 := bstep (se 1 (by rfl) ⟨501128, by rfl⟩ : syracuseStep 668171 = 1002257) B1002257
theorem B307727 : Blo 203807 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B307769 : Blo 203807 307769 := bstep (se 2 (by rfl) ⟨115413, by rfl⟩ : syracuseStep 307769 = 230827) B230827
theorem B307847 : Blo 203807 307847 := bstep (se 1 (by rfl) ⟨230885, by rfl⟩ : syracuseStep 307847 = 461771) B461771
theorem B307883 : Blo 203807 307883 := bstep (se 1 (by rfl) ⟨230912, by rfl⟩ : syracuseStep 307883 = 461825) B461825
theorem B307913 : Blo 203807 307913 := bstep (se 2 (by rfl) ⟨115467, by rfl⟩ : syracuseStep 307913 = 230935) B230935
theorem B537377 : Blo 203807 537377 := bstep (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) B403033
theorem B308027 : Blo 203807 308027 := bstep (se 1 (by rfl) ⟨231020, by rfl⟩ : syracuseStep 308027 = 462041) B462041
theorem B701243 : Blo 203807 701243 := bstep (se 1 (by rfl) ⟨525932, by rfl⟩ : syracuseStep 701243 = 1051865) B1051865
theorem B308087 : Blo 203807 308087 := bstep (se 1 (by rfl) ⟨231065, by rfl⟩ : syracuseStep 308087 = 462131) B462131
theorem B308111 : Blo 203807 308111 := bstep (se 1 (by rfl) ⟨231083, by rfl⟩ : syracuseStep 308111 = 462167) B462167
theorem B308153 : Blo 203807 308153 := bstep (se 2 (by rfl) ⟨115557, by rfl⟩ : syracuseStep 308153 = 231115) B231115
theorem B308231 : Blo 203807 308231 := bstep (se 1 (by rfl) ⟨231173, by rfl⟩ : syracuseStep 308231 = 462347) B462347
theorem B308267 : Blo 203807 308267 := bstep (se 1 (by rfl) ⟨231200, by rfl⟩ : syracuseStep 308267 = 462401) B462401
theorem B308297 : Blo 203807 308297 := bstep (se 2 (by rfl) ⟨115611, by rfl⟩ : syracuseStep 308297 = 231223) B231223
theorem B308411 : Blo 203807 308411 := bstep (se 1 (by rfl) ⟨231308, by rfl⟩ : syracuseStep 308411 = 462617) B462617
theorem B308471 : Blo 203807 308471 := bstep (se 1 (by rfl) ⟨231353, by rfl⟩ : syracuseStep 308471 = 462707) B462707
theorem B308495 : Blo 203807 308495 := bstep (se 1 (by rfl) ⟨231371, by rfl⟩ : syracuseStep 308495 = 462743) B462743
theorem B701729 : Blo 203807 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B308537 : Blo 203807 308537 := bstep (se 2 (by rfl) ⟨115701, by rfl⟩ : syracuseStep 308537 = 231403) B231403
theorem B308615 : Blo 203807 308615 := bstep (se 1 (by rfl) ⟨231461, by rfl⟩ : syracuseStep 308615 = 462923) B462923
theorem B210319 : Blo 203807 210319 := bstep (se 1 (by rfl) ⟨157739, by rfl⟩ : syracuseStep 210319 = 315479) B315479
theorem B308651 : Blo 203807 308651 := bstep (se 1 (by rfl) ⟨231488, by rfl⟩ : syracuseStep 308651 = 462977) B462977
theorem B308681 : Blo 203807 308681 := bstep (se 2 (by rfl) ⟨115755, by rfl⟩ : syracuseStep 308681 = 231511) B231511
theorem B308795 : Blo 203807 308795 := bstep (se 1 (by rfl) ⟨231596, by rfl⟩ : syracuseStep 308795 = 463193) B463193
theorem B1488451 : Blo 203807 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B308855 : Blo 203807 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B308879 : Blo 203807 308879 := bstep (se 1 (by rfl) ⟨231659, by rfl⟩ : syracuseStep 308879 = 463319) B463319
theorem B276139 : Blo 203807 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B308921 : Blo 203807 308921 := bstep (se 2 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 308921 = 231691) B231691
theorem B308999 : Blo 203807 308999 := bstep (se 1 (by rfl) ⟨231749, by rfl⟩ : syracuseStep 308999 = 463499) B463499
theorem B309035 : Blo 203807 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B1554227 : Blo 203807 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B309065 : Blo 203807 309065 := bstep (se 2 (by rfl) ⟨115899, by rfl⟩ : syracuseStep 309065 = 231799) B231799
theorem B931769 : Blo 203807 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B309179 : Blo 203807 309179 := bstep (se 1 (by rfl) ⟨231884, by rfl⟩ : syracuseStep 309179 = 463769) B463769
theorem B309239 : Blo 203807 309239 := bstep (se 1 (by rfl) ⟨231929, by rfl⟩ : syracuseStep 309239 = 463859) B463859
theorem B309263 : Blo 203807 309263 := bstep (se 1 (by rfl) ⟨231947, by rfl⟩ : syracuseStep 309263 = 463895) B463895
theorem B309305 : Blo 203807 309305 := bstep (se 2 (by rfl) ⟨115989, by rfl⟩ : syracuseStep 309305 = 231979) B231979
theorem B1325117 : Blo 203807 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B309383 : Blo 203807 309383 := bstep (se 1 (by rfl) ⟨232037, by rfl⟩ : syracuseStep 309383 = 464075) B464075
theorem B309419 : Blo 203807 309419 := bstep (se 1 (by rfl) ⟨232064, by rfl⟩ : syracuseStep 309419 = 464129) B464129
theorem B309449 : Blo 203807 309449 := bstep (se 2 (by rfl) ⟨116043, by rfl⟩ : syracuseStep 309449 = 232087) B232087
theorem B309563 : Blo 203807 309563 := bstep (se 1 (by rfl) ⟨232172, by rfl⟩ : syracuseStep 309563 = 464345) B464345
theorem B309623 : Blo 203807 309623 := bstep (se 1 (by rfl) ⟨232217, by rfl⟩ : syracuseStep 309623 = 464435) B464435
theorem B309647 : Blo 203807 309647 := bstep (se 1 (by rfl) ⟨232235, by rfl⟩ : syracuseStep 309647 = 464471) B464471
theorem B309689 : Blo 203807 309689 := bstep (se 2 (by rfl) ⟨116133, by rfl⟩ : syracuseStep 309689 = 232267) B232267
theorem B309767 : Blo 203807 309767 := bstep (se 1 (by rfl) ⟨232325, by rfl⟩ : syracuseStep 309767 = 464651) B464651
theorem B309803 : Blo 203807 309803 := bstep (se 1 (by rfl) ⟨232352, by rfl⟩ : syracuseStep 309803 = 464705) B464705
theorem B309833 : Blo 203807 309833 := bstep (se 2 (by rfl) ⟨116187, by rfl⟩ : syracuseStep 309833 = 232375) B232375
theorem B277177 : Blo 203807 277177 := bstep (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) B207883
theorem B309947 : Blo 203807 309947 := bstep (se 1 (by rfl) ⟨232460, by rfl⟩ : syracuseStep 309947 = 464921) B464921
theorem B310007 : Blo 203807 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B310031 : Blo 203807 310031 := bstep (se 1 (by rfl) ⟨232523, by rfl⟩ : syracuseStep 310031 = 465047) B465047
theorem B310073 : Blo 203807 310073 := bstep (se 2 (by rfl) ⟨116277, by rfl⟩ : syracuseStep 310073 = 232555) B232555
theorem B310151 : Blo 203807 310151 := bstep (se 1 (by rfl) ⟨232613, by rfl⟩ : syracuseStep 310151 = 465227) B465227
theorem B310187 : Blo 203807 310187 := bstep (se 1 (by rfl) ⟨232640, by rfl⟩ : syracuseStep 310187 = 465281) B465281
theorem B310217 : Blo 203807 310217 := bstep (se 2 (by rfl) ⟨116331, by rfl⟩ : syracuseStep 310217 = 232663) B232663
theorem B1162187 : Blo 203807 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B1588247 : Blo 203807 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B310331 : Blo 203807 310331 := bstep (se 1 (by rfl) ⟨232748, by rfl⟩ : syracuseStep 310331 = 465497) B465497
theorem B310391 : Blo 203807 310391 := bstep (se 1 (by rfl) ⟨232793, by rfl⟩ : syracuseStep 310391 = 465587) B465587
theorem B310415 : Blo 203807 310415 := bstep (se 1 (by rfl) ⟨232811, by rfl⟩ : syracuseStep 310415 = 465623) B465623
theorem B310457 : Blo 203807 310457 := bstep (se 2 (by rfl) ⟨116421, by rfl⟩ : syracuseStep 310457 = 232843) B232843
theorem B310535 : Blo 203807 310535 := bstep (se 1 (by rfl) ⟨232901, by rfl⟩ : syracuseStep 310535 = 465803) B465803
theorem B310571 : Blo 203807 310571 := bstep (se 1 (by rfl) ⟨232928, by rfl⟩ : syracuseStep 310571 = 465857) B465857
theorem B310601 : Blo 203807 310601 := bstep (se 2 (by rfl) ⟨116475, by rfl⟩ : syracuseStep 310601 = 232951) B232951
theorem B245111 : Blo 203807 245111 := bstep (se 1 (by rfl) ⟨183833, by rfl⟩ : syracuseStep 245111 = 367667) B367667
theorem B671129 : Blo 203807 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B310715 : Blo 203807 310715 := bstep (se 1 (by rfl) ⟨233036, by rfl⟩ : syracuseStep 310715 = 466073) B466073
theorem B310775 : Blo 203807 310775 := bstep (se 1 (by rfl) ⟨233081, by rfl⟩ : syracuseStep 310775 = 466163) B466163
theorem B310799 : Blo 203807 310799 := bstep (se 1 (by rfl) ⟨233099, by rfl⟩ : syracuseStep 310799 = 466199) B466199
theorem B310841 : Blo 203807 310841 := bstep (se 2 (by rfl) ⟨116565, by rfl⟩ : syracuseStep 310841 = 233131) B233131
theorem B310919 : Blo 203807 310919 := bstep (se 1 (by rfl) ⟨233189, by rfl⟩ : syracuseStep 310919 = 466379) B466379
theorem B310955 : Blo 203807 310955 := bstep (se 1 (by rfl) ⟨233216, by rfl⟩ : syracuseStep 310955 = 466433) B466433
theorem B310985 : Blo 203807 310985 := bstep (se 2 (by rfl) ⟨116619, by rfl⟩ : syracuseStep 310985 = 233239) B233239
theorem B311099 : Blo 203807 311099 := bstep (se 1 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 311099 = 466649) B466649
theorem B311159 : Blo 203807 311159 := bstep (se 1 (by rfl) ⟨233369, by rfl⟩ : syracuseStep 311159 = 466739) B466739
theorem B311183 : Blo 203807 311183 := bstep (se 1 (by rfl) ⟨233387, by rfl⟩ : syracuseStep 311183 = 466775) B466775
theorem B343993 : Blo 203807 343993 := bstep (se 2 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 343993 = 257995) B257995
theorem B311225 : Blo 203807 311225 := bstep (se 2 (by rfl) ⟨116709, by rfl⟩ : syracuseStep 311225 = 233419) B233419
theorem B311303 : Blo 203807 311303 := bstep (se 1 (by rfl) ⟨233477, by rfl⟩ : syracuseStep 311303 = 466955) B466955
theorem B311339 : Blo 203807 311339 := bstep (se 1 (by rfl) ⟨233504, by rfl⟩ : syracuseStep 311339 = 467009) B467009
theorem B311369 : Blo 203807 311369 := bstep (se 2 (by rfl) ⟨116763, by rfl⟩ : syracuseStep 311369 = 233527) B233527
theorem B311483 : Blo 203807 311483 := bstep (se 1 (by rfl) ⟨233612, by rfl⟩ : syracuseStep 311483 = 467225) B467225
theorem B311543 : Blo 203807 311543 := bstep (se 1 (by rfl) ⟨233657, by rfl⟩ : syracuseStep 311543 = 467315) B467315
theorem B311567 : Blo 203807 311567 := bstep (se 1 (by rfl) ⟨233675, by rfl⟩ : syracuseStep 311567 = 467351) B467351
theorem B311609 : Blo 203807 311609 := bstep (se 2 (by rfl) ⟨116853, by rfl⟩ : syracuseStep 311609 = 233707) B233707
theorem B311687 : Blo 203807 311687 := bstep (se 1 (by rfl) ⟨233765, by rfl⟩ : syracuseStep 311687 = 467531) B467531
theorem B344695 : Blo 203807 344695 := bstep (se 1 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 344695 = 517043) B517043
theorem B443065 : Blo 203807 443065 := bstep (se 2 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 443065 = 332299) B332299
theorem B344891 : Blo 203807 344891 := bstep (se 1 (by rfl) ⟨258668, by rfl⟩ : syracuseStep 344891 = 517337) B517337
theorem B2212697 : Blo 203807 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B2802521 : Blo 203807 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1196947 : Blo 203807 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B443407 : Blo 203807 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B345289 : Blo 203807 345289 := bstep (se 2 (by rfl) ⟨129483, by rfl⟩ : syracuseStep 345289 = 258967) B258967
theorem B738575 : Blo 203807 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B1164577 : Blo 203807 1164577 := bstep (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) B873433
theorem B5064067 : Blo 203807 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B345991 : Blo 203807 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B837643 : Blo 203807 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B248071 : Blo 203807 248071 := bstep (se 1 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 248071 = 372107) B372107
theorem B346639 : Blo 203807 346639 := bstep (se 1 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 346639 = 519959) B519959
theorem B1165853 : Blo 203807 1165853 := bstep (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) B437195
theorem B739901 : Blo 203807 739901 := bstep (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) B277463
theorem B4508227 : Blo 203807 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B1100729 : Blo 203807 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B1493963 : Blo 203807 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B347179 : Blo 203807 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B347321 : Blo 203807 347321 := bstep (se 2 (by rfl) ⟨130245, by rfl⟩ : syracuseStep 347321 = 260491) B260491
theorem B1494217 : Blo 203807 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B2116999 : Blo 203807 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1887623 : Blo 203807 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B1035665 : Blo 203807 1035665 := bstep (se 2 (by rfl) ⟨388374, by rfl⟩ : syracuseStep 1035665 = 776749) B776749
theorem B740983 : Blo 203807 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B773833 : Blo 203807 773833 := bstep (se 2 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 773833 = 580375) B580375
theorem B348023 : Blo 203807 348023 := bstep (se 1 (by rfl) ⟨261017, by rfl⟩ : syracuseStep 348023 = 522035) B522035
theorem B872477 : Blo 203807 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B2216069 : Blo 203807 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B413843 : Blo 203807 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B348475 : Blo 203807 348475 := bstep (se 1 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 348475 = 522713) B522713
theorem B872819 : Blo 203807 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B348617 : Blo 203807 348617 := bstep (se 2 (by rfl) ⟨130731, by rfl⟩ : syracuseStep 348617 = 261463) B261463
theorem B1168451 : Blo 203807 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B349319 : Blo 203807 349319 := bstep (se 1 (by rfl) ⟨261989, by rfl⟩ : syracuseStep 349319 = 523979) B523979
theorem B1496353 : Blo 203807 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B742715 : Blo 203807 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B1562003 : Blo 203807 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B1037771 : Blo 203807 1037771 := bstep (se 1 (by rfl) ⟨778328, by rfl⟩ : syracuseStep 1037771 = 1556657) B1556657
theorem B218683 : Blo 203807 218683 := bstep (se 1 (by rfl) ⟨164012, by rfl⟩ : syracuseStep 218683 = 328025) B328025
theorem B2971313 : Blo 203807 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1038095 : Blo 203807 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B349967 : Blo 203807 349967 := bstep (se 1 (by rfl) ⟨262475, by rfl⟩ : syracuseStep 349967 = 524951) B524951
theorem B2348837 : Blo 203807 2348837 := bstep (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) B440407
theorem B776051 : Blo 203807 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B743303 : Blo 203807 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B87447605 : Blo 203807 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B416033 : Blo 203807 416033 := bstep (se 2 (by rfl) ⟨156012, by rfl⟩ : syracuseStep 416033 = 312025) B312025
theorem B350507 : Blo 203807 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B874937 : Blo 203807 874937 := bstep (se 2 (by rfl) ⟨328101, by rfl⟩ : syracuseStep 874937 = 656203) B656203
theorem B875245 : Blo 203807 875245 := bstep (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) B328217
theorem B875279 : Blo 203807 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B1170227 : Blo 203807 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B744515 : Blo 203807 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B1039553 : Blo 203807 1039553 := bstep (se 2 (by rfl) ⟨389832, by rfl⟩ : syracuseStep 1039553 = 779665) B779665
theorem B1006937 : Blo 203807 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B1105267 : Blo 203807 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B3333581 : Blo 203807 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B516041 : Blo 203807 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B417737 : Blo 203807 417737 := bstep (se 2 (by rfl) ⟨156651, by rfl⟩ : syracuseStep 417737 = 313303) B313303
theorem B778193 : Blo 203807 778193 := bstep (se 2 (by rfl) ⟨291822, by rfl⟩ : syracuseStep 778193 = 583645) B583645
theorem B745483 : Blo 203807 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B1794059 : Blo 203807 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B581833 : Blo 203807 581833 := bstep (se 2 (by rfl) ⟨218187, by rfl⟩ : syracuseStep 581833 = 436375) B436375
theorem B1171685 : Blo 203807 1171685 := bstep (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) B219691
theorem B778511 : Blo 203807 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B516395 : Blo 203807 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B1040849 : Blo 203807 1040849 := bstep (se 2 (by rfl) ⟨390318, by rfl⟩ : syracuseStep 1040849 = 780637) B780637
theorem B582187 : Blo 203807 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B1172141 : Blo 203807 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B582461 : Blo 203807 582461 := bstep (se 3 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 582461 = 218423) B218423
theorem B877655 : Blo 203807 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B517387 : Blo 203807 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B1172825 : Blo 203807 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B517529 : Blo 203807 517529 := bstep (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) B388147
theorem B517691 : Blo 203807 517691 := bstep (se 1 (by rfl) ⟨388268, by rfl⟩ : syracuseStep 517691 = 776537) B776537
theorem B353977 : Blo 203807 353977 := bstep (se 2 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 353977 = 265483) B265483
theorem B518035 : Blo 203807 518035 := bstep (se 1 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 518035 = 777053) B777053
theorem B1992599 : Blo 203807 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B1009667 : Blo 203807 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B518177 : Blo 203807 518177 := bstep (se 2 (by rfl) ⟨194316, by rfl⟩ : syracuseStep 518177 = 388633) B388633
theorem B1959997 : Blo 203807 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B2222471 : Blo 203807 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B1042955 : Blo 203807 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B1043117 : Blo 203807 1043117 := bstep (se 3 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 1043117 = 391169) B391169
theorem B584567 : Blo 203807 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B879569 : Blo 203807 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B519169 : Blo 203807 519169 := bstep (se 2 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 519169 = 389377) B389377
theorem B290233 : Blo 203807 290233 := bstep (se 2 (by rfl) ⟨108837, by rfl⟩ : syracuseStep 290233 = 217675) B217675
theorem B519767 : Blo 203807 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B388793 : Blo 203807 388793 := bstep (se 2 (by rfl) ⟨145797, by rfl⟩ : syracuseStep 388793 = 291595) B291595
theorem B782081 : Blo 203807 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B290575 : Blo 203807 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B782095 : Blo 203807 782095 := bstep (se 1 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 782095 = 1173143) B1173143
theorem B519979 : Blo 203807 519979 := bstep (se 1 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 519979 = 779969) B779969
theorem B4321073 : Blo 203807 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B552851 : Blo 203807 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B520121 : Blo 203807 520121 := bstep (se 2 (by rfl) ⟨195045, by rfl⟩ : syracuseStep 520121 = 390091) B390091
theorem B2945069 : Blo 203807 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B258167 : Blo 203807 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B1044737 : Blo 203807 1044737 := bstep (se 2 (by rfl) ⟨391776, by rfl⟩ : syracuseStep 1044737 = 783553) B783553
theorem B258319 : Blo 203807 258319 := bstep (se 1 (by rfl) ⟨193739, by rfl⟩ : syracuseStep 258319 = 387479) B387479
theorem B1601927 : Blo 203807 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B1503623 : Blo 203807 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1012121 : Blo 203807 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B258491 : Blo 203807 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B389947 : Blo 203807 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B291703 : Blo 203807 291703 := bstep (se 1 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 291703 = 437555) B437555
theorem B521113 : Blo 203807 521113 := bstep (se 2 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 521113 = 390835) B390835
theorem B783371 : Blo 203807 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B1045547 : Blo 203807 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B521275 : Blo 203807 521275 := bstep (se 1 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 521275 = 781913) B781913
theorem B3929219 : Blo 203807 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B521417 : Blo 203807 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B390433 : Blo 203807 390433 := bstep (se 2 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 390433 = 292825) B292825
theorem B587051 : Blo 203807 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B259463 : Blo 203807 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B521761 : Blo 203807 521761 := bstep (se 2 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 521761 = 391321) B391321
theorem B3995237 : Blo 203807 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B1996595 : Blo 203807 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B784313 : Blo 203807 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B2979787 : Blo 203807 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B260111 : Blo 203807 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B1046557 : Blo 203807 1046557 := bstep (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) B392459
theorem B587837 : Blo 203807 587837 := bstep (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) B220439
theorem B2652277 : Blo 203807 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B522359 : Blo 203807 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B981229 : Blo 203807 981229 := bstep (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) B367961
theorem B784673 : Blo 203807 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B1046843 : Blo 203807 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B2881885 : Blo 203807 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B588167 : Blo 203807 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B391625 : Blo 203807 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B1047005 : Blo 203807 1047005 := bstep (se 3 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 1047005 = 392627) B392627
theorem B1047329 : Blo 203807 1047329 := bstep (se 2 (by rfl) ⟨392748, by rfl⟩ : syracuseStep 1047329 = 785497) B785497
theorem B555835 : Blo 203807 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B2325509 : Blo 203807 2325509 := bstep (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) B436033
theorem B392339 : Blo 203807 392339 := bstep (se 1 (by rfl) ⟨294254, by rfl⟩ : syracuseStep 392339 = 588509) B588509
theorem B392377 : Blo 203807 392377 := bstep (se 2 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 392377 = 294283) B294283
theorem B18513197 : Blo 203807 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B884027 : Blo 203807 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B523655 : Blo 203807 523655 := bstep (se 1 (by rfl) ⟨392741, by rfl⟩ : syracuseStep 523655 = 785483) B785483
theorem B523705 : Blo 203807 523705 := bstep (se 2 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 523705 = 392779) B392779
theorem B294391 : Blo 203807 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B622091 : Blo 203807 622091 := bstep (se 1 (by rfl) ⟨466568, by rfl⟩ : syracuseStep 622091 = 933137) B933137
theorem B884267 : Blo 203807 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B1048301 : Blo 203807 1048301 := bstep (se 3 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 1048301 = 393113) B393113
theorem B687905 : Blo 203807 687905 := bstep (se 2 (by rfl) ⟨257964, by rfl⟩ : syracuseStep 687905 = 515929) B515929
theorem B1114003 : Blo 203807 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B884627 : Blo 203807 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B458999 : Blo 203807 458999 := bstep (se 1 (by rfl) ⟨344249, by rfl⟩ : syracuseStep 458999 = 688499) B688499
theorem B688445 : Blo 203807 688445 := bstep (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) B258167
theorem B1573181 : Blo 203807 1573181 := bstep (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) B589943
theorem B229927 : Blo 203807 229927 := bstep (se 1 (by rfl) ⟨172445, by rfl⟩ : syracuseStep 229927 = 344891) B344891
theorem B524839 : Blo 203807 524839 := bstep (se 1 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 524839 = 787259) B787259
theorem B932774453 : Blo 203807 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B1049273 : Blo 203807 1049273 := bstep (se 2 (by rfl) ⟨393477, by rfl⟩ : syracuseStep 1049273 = 786955) B786955
theorem B262855 : Blo 203807 262855 := bstep (se 1 (by rfl) ⟨197141, by rfl⟩ : syracuseStep 262855 = 394283) B394283
theorem B787229 : Blo 203807 787229 := bstep (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) B295211
theorem B459593 : Blo 203807 459593 := bstep (se 2 (by rfl) ⟨172347, by rfl⟩ : syracuseStep 459593 = 344695) B344695
theorem B492383 : Blo 203807 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B525163 : Blo 203807 525163 := bstep (se 1 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 525163 = 787745) B787745
theorem B590753 : Blo 203807 590753 := bstep (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) B443065
theorem B328711 : Blo 203807 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B787475 : Blo 203807 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B689309 : Blo 203807 689309 := bstep (se 3 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 689309 = 258491) B258491
theorem B1574083 : Blo 203807 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B591209 : Blo 203807 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B787913 : Blo 203807 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B525811 : Blo 203807 525811 := bstep (se 1 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 525811 = 788717) B788717
theorem B460385 : Blo 203807 460385 := bstep (se 2 (by rfl) ⟨172644, by rfl⟩ : syracuseStep 460385 = 345289) B345289
theorem B689849 : Blo 203807 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B6752089 : Blo 203807 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B788399 : Blo 203807 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B460727 : Blo 203807 460727 := bstep (se 1 (by rfl) ⟨345545, by rfl⟩ : syracuseStep 460727 = 691091) B691091
theorem B329807 : Blo 203807 329807 := bstep (se 1 (by rfl) ⟨247355, by rfl⟩ : syracuseStep 329807 = 494711) B494711
theorem B231547 : Blo 203807 231547 := bstep (se 1 (by rfl) ⟨173660, by rfl⟩ : syracuseStep 231547 = 347321) B347321
theorem B5900525 : Blo 203807 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B7473389 : Blo 203807 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B690443 : Blo 203807 690443 := bstep (se 1 (by rfl) ⟨517832, by rfl⟩ : syracuseStep 690443 = 1035665) B1035665
theorem B330203 : Blo 203807 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B461321 : Blo 203807 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B690713 : Blo 203807 690713 := bstep (se 2 (by rfl) ⟨259017, by rfl⟩ : syracuseStep 690713 = 518035) B518035
theorem B232015 : Blo 203807 232015 := bstep (se 1 (by rfl) ⟨174011, by rfl⟩ : syracuseStep 232015 = 348023) B348023
theorem B1116857 : Blo 203807 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B1477379 : Blo 203807 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B461663 : Blo 203807 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B232411 : Blo 203807 232411 := bstep (se 1 (by rfl) ⟨174308, by rfl⟩ : syracuseStep 232411 = 348617) B348617
theorem B330761 : Blo 203807 330761 := bstep (se 2 (by rfl) ⟨124035, by rfl⟩ : syracuseStep 330761 = 248071) B248071
theorem B461843 : Blo 203807 461843 := bstep (se 1 (by rfl) ⟨346382, by rfl⟩ : syracuseStep 461843 = 692765) B692765
theorem B1772837 : Blo 203807 1772837 := bstep (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) B332407
theorem B462185 : Blo 203807 462185 := bstep (se 2 (by rfl) ⟨173319, by rfl⟩ : syracuseStep 462185 = 346639) B346639
theorem B658793 : Blo 203807 658793 := bstep (se 2 (by rfl) ⟨247047, by rfl⟩ : syracuseStep 658793 = 494095) B494095
theorem B232879 : Blo 203807 232879 := bstep (se 1 (by rfl) ⟨174659, by rfl⟩ : syracuseStep 232879 = 349319) B349319
theorem B2985437 : Blo 203807 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B495143 : Blo 203807 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B691847 : Blo 203807 691847 := bstep (se 1 (by rfl) ⟨518885, by rfl⟩ : syracuseStep 691847 = 1037771) B1037771
theorem B691901 : Blo 203807 691901 := bstep (se 3 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 691901 = 259463) B259463
theorem B1183531 : Blo 203807 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B692063 : Blo 203807 692063 := bstep (se 1 (by rfl) ⟨519047, by rfl⟩ : syracuseStep 692063 = 1038095) B1038095
theorem B233311 : Blo 203807 233311 := bstep (se 1 (by rfl) ⟨174983, by rfl⟩ : syracuseStep 233311 = 349967) B349967
theorem B331703 : Blo 203807 331703 := bstep (se 1 (by rfl) ⟨248777, by rfl⟩ : syracuseStep 331703 = 497555) B497555
theorem B462779 : Blo 203807 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B692225 : Blo 203807 692225 := bstep (se 2 (by rfl) ⟨259584, by rfl⟩ : syracuseStep 692225 = 519169) B519169
theorem B462905 : Blo 203807 462905 := bstep (se 2 (by rfl) ⟨173589, by rfl⟩ : syracuseStep 462905 = 347179) B347179
theorem B233671 : Blo 203807 233671 := bstep (se 1 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 233671 = 350507) B350507
theorem B463247 : Blo 203807 463247 := bstep (se 1 (by rfl) ⟨347435, by rfl⟩ : syracuseStep 463247 = 694871) B694871
theorem B463571 : Blo 203807 463571 := bstep (se 1 (by rfl) ⟨347678, by rfl⟩ : syracuseStep 463571 = 695357) B695357
theorem B496343 : Blo 203807 496343 := bstep (se 1 (by rfl) ⟨372257, by rfl⟩ : syracuseStep 496343 = 744515) B744515
theorem B3347203 : Blo 203807 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B693035 : Blo 203807 693035 := bstep (se 1 (by rfl) ⟨519776, by rfl⟩ : syracuseStep 693035 = 1039553) B1039553
theorem B987977 : Blo 203807 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B693305 : Blo 203807 693305 := bstep (se 2 (by rfl) ⟨259989, by rfl⟩ : syracuseStep 693305 = 519979) B519979
theorem B2692445 : Blo 203807 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B693629 : Blo 203807 693629 := bstep (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) B260111
theorem B2299355 : Blo 203807 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B464507 : Blo 203807 464507 := bstep (se 1 (by rfl) ⟨348380, by rfl⟩ : syracuseStep 464507 = 696761) B696761
theorem B693899 : Blo 203807 693899 := bstep (se 1 (by rfl) ⟨520424, by rfl⟩ : syracuseStep 693899 = 1040849) B1040849
theorem B792275 : Blo 203807 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B464633 : Blo 203807 464633 := bstep (se 2 (by rfl) ⟨174237, by rfl⟩ : syracuseStep 464633 = 348475) B348475
theorem B661355 : Blo 203807 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B464903 : Blo 203807 464903 := bstep (se 1 (by rfl) ⟨348677, by rfl⟩ : syracuseStep 464903 = 697355) B697355
theorem B464975 : Blo 203807 464975 := bstep (se 1 (by rfl) ⟨348731, by rfl⟩ : syracuseStep 464975 = 697463) B697463
theorem B2660485 : Blo 203807 2660485 := bstep (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) B498841
theorem B465371 : Blo 203807 465371 := bstep (se 1 (by rfl) ⟨349028, by rfl⟩ : syracuseStep 465371 = 698057) B698057
theorem B694817 : Blo 203807 694817 := bstep (se 2 (by rfl) ⟨260556, by rfl⟩ : syracuseStep 694817 = 521113) B521113
theorem B596603 : Blo 203807 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B662201 : Blo 203807 662201 := bstep (se 2 (by rfl) ⟨248325, by rfl⟩ : syracuseStep 662201 = 496651) B496651
theorem B695033 : Blo 203807 695033 := bstep (se 2 (by rfl) ⟨260637, by rfl⟩ : syracuseStep 695033 = 521275) B521275
theorem B1973069 : Blo 203807 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B1481647 : Blo 203807 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B465839 : Blo 203807 465839 := bstep (se 1 (by rfl) ⟨349379, by rfl⟩ : syracuseStep 465839 = 698759) B698759
theorem B695303 : Blo 203807 695303 := bstep (se 1 (by rfl) ⟨521477, by rfl⟩ : syracuseStep 695303 = 1042955) B1042955
theorem B203815 : Blo 203807 203815 := bstep (se 1 (by rfl) ⟨152861, by rfl⟩ : syracuseStep 203815 = 305723) B305723
theorem B203855 : Blo 203807 203855 := bstep (se 1 (by rfl) ⟨152891, by rfl⟩ : syracuseStep 203855 = 305783) B305783
theorem B203871 : Blo 203807 203871 := bstep (se 1 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 203871 = 305807) B305807
theorem B695411 : Blo 203807 695411 := bstep (se 1 (by rfl) ⟨521558, by rfl⟩ : syracuseStep 695411 = 1043117) B1043117
theorem B203899 : Blo 203807 203899 := bstep (se 1 (by rfl) ⟨152924, by rfl⟩ : syracuseStep 203899 = 305849) B305849
theorem B466091 : Blo 203807 466091 := bstep (se 1 (by rfl) ⟨349568, by rfl⟩ : syracuseStep 466091 = 699137) B699137
theorem B203951 : Blo 203807 203951 := bstep (se 1 (by rfl) ⟨152963, by rfl⟩ : syracuseStep 203951 = 305927) B305927
theorem B203975 : Blo 203807 203975 := bstep (se 1 (by rfl) ⟨152981, by rfl⟩ : syracuseStep 203975 = 305963) B305963
theorem B203995 : Blo 203807 203995 := bstep (se 1 (by rfl) ⟨152996, by rfl⟩ : syracuseStep 203995 = 305993) B305993
theorem B204071 : Blo 203807 204071 := bstep (se 1 (by rfl) ⟨153053, by rfl⟩ : syracuseStep 204071 = 306107) B306107
theorem B204111 : Blo 203807 204111 := bstep (se 1 (by rfl) ⟨153083, by rfl⟩ : syracuseStep 204111 = 306167) B306167
theorem B204127 : Blo 203807 204127 := bstep (se 1 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 204127 = 306191) B306191
theorem B204155 : Blo 203807 204155 := bstep (se 1 (by rfl) ⟨153116, by rfl⟩ : syracuseStep 204155 = 306233) B306233
theorem B695681 : Blo 203807 695681 := bstep (se 2 (by rfl) ⟨260880, by rfl⟩ : syracuseStep 695681 = 521761) B521761
theorem B1121701 : Blo 203807 1121701 := bstep (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) B210319
theorem B204207 : Blo 203807 204207 := bstep (se 1 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 204207 = 306311) B306311
theorem B204231 : Blo 203807 204231 := bstep (se 1 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 204231 = 306347) B306347
theorem B204251 : Blo 203807 204251 := bstep (se 1 (by rfl) ⟨153188, by rfl⟩ : syracuseStep 204251 = 306377) B306377
theorem B826861 : Blo 203807 826861 := bstep (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) B310073
theorem B204327 : Blo 203807 204327 := bstep (se 1 (by rfl) ⟨153245, by rfl⟩ : syracuseStep 204327 = 306491) B306491
theorem B204367 : Blo 203807 204367 := bstep (se 1 (by rfl) ⟨153275, by rfl⟩ : syracuseStep 204367 = 306551) B306551
theorem B204383 : Blo 203807 204383 := bstep (se 1 (by rfl) ⟨153287, by rfl⟩ : syracuseStep 204383 = 306575) B306575
theorem B204411 : Blo 203807 204411 := bstep (se 1 (by rfl) ⟨153308, by rfl⟩ : syracuseStep 204411 = 306617) B306617
theorem B1547909 : Blo 203807 1547909 := bstep (se 4 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 1547909 = 290233) B290233
theorem B204463 : Blo 203807 204463 := bstep (se 1 (by rfl) ⟨153347, by rfl⟩ : syracuseStep 204463 = 306695) B306695
theorem B204487 : Blo 203807 204487 := bstep (se 1 (by rfl) ⟨153365, by rfl⟩ : syracuseStep 204487 = 306731) B306731
theorem B466631 : Blo 203807 466631 := bstep (se 1 (by rfl) ⟨349973, by rfl⟩ : syracuseStep 466631 = 699947) B699947
theorem B204507 : Blo 203807 204507 := bstep (se 1 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 204507 = 306761) B306761
theorem B204583 : Blo 203807 204583 := bstep (se 1 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 204583 = 306875) B306875
theorem B204623 : Blo 203807 204623 := bstep (se 1 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 204623 = 306935) B306935
theorem B204639 : Blo 203807 204639 := bstep (se 1 (by rfl) ⟨153479, by rfl⟩ : syracuseStep 204639 = 306959) B306959
theorem B204667 : Blo 203807 204667 := bstep (se 1 (by rfl) ⟨153500, by rfl⟩ : syracuseStep 204667 = 307001) B307001
theorem B204719 : Blo 203807 204719 := bstep (se 1 (by rfl) ⟨153539, by rfl⟩ : syracuseStep 204719 = 307079) B307079
theorem B368567 : Blo 203807 368567 := bstep (se 1 (by rfl) ⟨276425, by rfl⟩ : syracuseStep 368567 = 552851) B552851
theorem B3973049 : Blo 203807 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B204743 : Blo 203807 204743 := bstep (se 1 (by rfl) ⟨153557, by rfl⟩ : syracuseStep 204743 = 307115) B307115
theorem B204763 : Blo 203807 204763 := bstep (se 1 (by rfl) ⟨153572, by rfl⟩ : syracuseStep 204763 = 307145) B307145
theorem B204839 : Blo 203807 204839 := bstep (se 1 (by rfl) ⟨153629, by rfl⟩ : syracuseStep 204839 = 307259) B307259
theorem B204879 : Blo 203807 204879 := bstep (se 1 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 204879 = 307319) B307319
theorem B204895 : Blo 203807 204895 := bstep (se 1 (by rfl) ⟨153671, by rfl⟩ : syracuseStep 204895 = 307343) B307343
theorem B204923 : Blo 203807 204923 := bstep (se 1 (by rfl) ⟨153692, by rfl⟩ : syracuseStep 204923 = 307385) B307385
theorem B696491 : Blo 203807 696491 := bstep (se 1 (by rfl) ⟨522368, by rfl⟩ : syracuseStep 696491 = 1044737) B1044737
theorem B204975 : Blo 203807 204975 := bstep (se 1 (by rfl) ⟨153731, by rfl⟩ : syracuseStep 204975 = 307463) B307463
theorem B1974451 : Blo 203807 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B204999 : Blo 203807 204999 := bstep (se 1 (by rfl) ⟨153749, by rfl⟩ : syracuseStep 204999 = 307499) B307499
theorem B205019 : Blo 203807 205019 := bstep (se 1 (by rfl) ⟨153764, by rfl⟩ : syracuseStep 205019 = 307529) B307529
theorem B205095 : Blo 203807 205095 := bstep (se 1 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 205095 = 307643) B307643
theorem B205135 : Blo 203807 205135 := bstep (se 1 (by rfl) ⟨153851, by rfl⟩ : syracuseStep 205135 = 307703) B307703
theorem B205151 : Blo 203807 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B205179 : Blo 203807 205179 := bstep (se 1 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 205179 = 307769) B307769
theorem B205231 : Blo 203807 205231 := bstep (se 1 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 205231 = 307847) B307847
theorem B205255 : Blo 203807 205255 := bstep (se 1 (by rfl) ⟨153941, by rfl⟩ : syracuseStep 205255 = 307883) B307883
theorem B3842513 : Blo 203807 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B205275 : Blo 203807 205275 := bstep (se 1 (by rfl) ⟨153956, by rfl⟩ : syracuseStep 205275 = 307913) B307913
theorem B205351 : Blo 203807 205351 := bstep (se 1 (by rfl) ⟨154013, by rfl⟩ : syracuseStep 205351 = 308027) B308027
theorem B467495 : Blo 203807 467495 := bstep (se 1 (by rfl) ⟨350621, by rfl⟩ : syracuseStep 467495 = 701243) B701243
theorem B205391 : Blo 203807 205391 := bstep (se 1 (by rfl) ⟨154043, by rfl⟩ : syracuseStep 205391 = 308087) B308087
theorem B205407 : Blo 203807 205407 := bstep (se 1 (by rfl) ⟨154055, by rfl⟩ : syracuseStep 205407 = 308111) B308111
theorem B205435 : Blo 203807 205435 := bstep (se 1 (by rfl) ⟨154076, by rfl⟩ : syracuseStep 205435 = 308153) B308153
theorem B205487 : Blo 203807 205487 := bstep (se 1 (by rfl) ⟨154115, by rfl⟩ : syracuseStep 205487 = 308231) B308231
theorem B205511 : Blo 203807 205511 := bstep (se 1 (by rfl) ⟨154133, by rfl⟩ : syracuseStep 205511 = 308267) B308267
theorem B697031 : Blo 203807 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B205531 : Blo 203807 205531 := bstep (se 1 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 205531 = 308297) B308297
theorem B205607 : Blo 203807 205607 := bstep (se 1 (by rfl) ⟨154205, by rfl⟩ : syracuseStep 205607 = 308411) B308411
theorem B205647 : Blo 203807 205647 := bstep (se 1 (by rfl) ⟨154235, by rfl⟩ : syracuseStep 205647 = 308471) B308471
theorem B205663 : Blo 203807 205663 := bstep (se 1 (by rfl) ⟨154247, by rfl⟩ : syracuseStep 205663 = 308495) B308495
theorem B467819 : Blo 203807 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B205691 : Blo 203807 205691 := bstep (se 1 (by rfl) ⟨154268, by rfl⟩ : syracuseStep 205691 = 308537) B308537
theorem B369569 : Blo 203807 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B205743 : Blo 203807 205743 := bstep (se 1 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 205743 = 308615) B308615
theorem B205767 : Blo 203807 205767 := bstep (se 1 (by rfl) ⟨154325, by rfl⟩ : syracuseStep 205767 = 308651) B308651
theorem B205787 : Blo 203807 205787 := bstep (se 1 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 205787 = 308681) B308681
theorem B205863 : Blo 203807 205863 := bstep (se 1 (by rfl) ⟨154397, by rfl⟩ : syracuseStep 205863 = 308795) B308795
theorem B2663491 : Blo 203807 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B205903 : Blo 203807 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B205919 : Blo 203807 205919 := bstep (se 1 (by rfl) ⟨154439, by rfl⟩ : syracuseStep 205919 = 308879) B308879
theorem B205947 : Blo 203807 205947 := bstep (se 1 (by rfl) ⟨154460, by rfl⟩ : syracuseStep 205947 = 308921) B308921
theorem B205999 : Blo 203807 205999 := bstep (se 1 (by rfl) ⟨154499, by rfl⟩ : syracuseStep 205999 = 308999) B308999
theorem B206023 : Blo 203807 206023 := bstep (se 1 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 206023 = 309035) B309035
theorem B206043 : Blo 203807 206043 := bstep (se 1 (by rfl) ⟨154532, by rfl⟩ : syracuseStep 206043 = 309065) B309065
theorem B206119 : Blo 203807 206119 := bstep (se 1 (by rfl) ⟨154589, by rfl⟩ : syracuseStep 206119 = 309179) B309179
theorem B206159 : Blo 203807 206159 := bstep (se 1 (by rfl) ⟨154619, by rfl⟩ : syracuseStep 206159 = 309239) B309239
theorem B206175 : Blo 203807 206175 := bstep (se 1 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 206175 = 309263) B309263
theorem B206203 : Blo 203807 206203 := bstep (se 1 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 206203 = 309305) B309305
theorem B206255 : Blo 203807 206255 := bstep (se 1 (by rfl) ⟨154691, by rfl⟩ : syracuseStep 206255 = 309383) B309383
theorem B206279 : Blo 203807 206279 := bstep (se 1 (by rfl) ⟨154709, by rfl⟩ : syracuseStep 206279 = 309419) B309419
theorem B206299 : Blo 203807 206299 := bstep (se 1 (by rfl) ⟨154724, by rfl⟩ : syracuseStep 206299 = 309449) B309449
theorem B206375 : Blo 203807 206375 := bstep (se 1 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 206375 = 309563) B309563
theorem B697895 : Blo 203807 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B206415 : Blo 203807 206415 := bstep (se 1 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 206415 = 309623) B309623
theorem B206431 : Blo 203807 206431 := bstep (se 1 (by rfl) ⟨154823, by rfl⟩ : syracuseStep 206431 = 309647) B309647
theorem B206459 : Blo 203807 206459 := bstep (se 1 (by rfl) ⟨154844, by rfl⟩ : syracuseStep 206459 = 309689) B309689
theorem B698003 : Blo 203807 698003 := bstep (se 1 (by rfl) ⟨523502, by rfl⟩ : syracuseStep 698003 = 1047005) B1047005
theorem B206511 : Blo 203807 206511 := bstep (se 1 (by rfl) ⟨154883, by rfl⟩ : syracuseStep 206511 = 309767) B309767
theorem B206535 : Blo 203807 206535 := bstep (se 1 (by rfl) ⟨154901, by rfl⟩ : syracuseStep 206535 = 309803) B309803
theorem B206555 : Blo 203807 206555 := bstep (se 1 (by rfl) ⟨154916, by rfl⟩ : syracuseStep 206555 = 309833) B309833
theorem B206631 : Blo 203807 206631 := bstep (se 1 (by rfl) ⟨154973, by rfl⟩ : syracuseStep 206631 = 309947) B309947
theorem B206671 : Blo 203807 206671 := bstep (se 1 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 206671 = 310007) B310007
theorem B206687 : Blo 203807 206687 := bstep (se 1 (by rfl) ⟨155015, by rfl⟩ : syracuseStep 206687 = 310031) B310031
theorem B698219 : Blo 203807 698219 := bstep (se 1 (by rfl) ⟨523664, by rfl⟩ : syracuseStep 698219 = 1047329) B1047329
theorem B1058669 : Blo 203807 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B206715 : Blo 203807 206715 := bstep (se 1 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 206715 = 310073) B310073
theorem B698273 : Blo 203807 698273 := bstep (se 2 (by rfl) ⟨261852, by rfl⟩ : syracuseStep 698273 = 523705) B523705
theorem B206767 : Blo 203807 206767 := bstep (se 1 (by rfl) ⟨155075, by rfl⟩ : syracuseStep 206767 = 310151) B310151
theorem B206791 : Blo 203807 206791 := bstep (se 1 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 206791 = 310187) B310187
theorem B206811 : Blo 203807 206811 := bstep (se 1 (by rfl) ⟨155108, by rfl⟩ : syracuseStep 206811 = 310217) B310217
theorem B1550339 : Blo 203807 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B1058831 : Blo 203807 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B2664485 : Blo 203807 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B206887 : Blo 203807 206887 := bstep (se 1 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 206887 = 310331) B310331
theorem B206927 : Blo 203807 206927 := bstep (se 1 (by rfl) ⟨155195, by rfl⟩ : syracuseStep 206927 = 310391) B310391
theorem B206943 : Blo 203807 206943 := bstep (se 1 (by rfl) ⟨155207, by rfl⟩ : syracuseStep 206943 = 310415) B310415
theorem B5941349 : Blo 203807 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B206971 : Blo 203807 206971 := bstep (se 1 (by rfl) ⟨155228, by rfl⟩ : syracuseStep 206971 = 310457) B310457
theorem B207023 : Blo 203807 207023 := bstep (se 1 (by rfl) ⟨155267, by rfl⟩ : syracuseStep 207023 = 310535) B310535
theorem B207047 : Blo 203807 207047 := bstep (se 1 (by rfl) ⟨155285, by rfl⟩ : syracuseStep 207047 = 310571) B310571
theorem B207067 : Blo 203807 207067 := bstep (se 1 (by rfl) ⟨155300, by rfl⟩ : syracuseStep 207067 = 310601) B310601
theorem B4204781 : Blo 203807 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B207143 : Blo 203807 207143 := bstep (se 1 (by rfl) ⟨155357, by rfl⟩ : syracuseStep 207143 = 310715) B310715
theorem B207183 : Blo 203807 207183 := bstep (se 1 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 207183 = 310775) B310775
theorem B207199 : Blo 203807 207199 := bstep (se 1 (by rfl) ⟨155399, by rfl⟩ : syracuseStep 207199 = 310799) B310799
theorem B207227 : Blo 203807 207227 := bstep (se 1 (by rfl) ⟨155420, by rfl⟩ : syracuseStep 207227 = 310841) B310841
theorem B207279 : Blo 203807 207279 := bstep (se 1 (by rfl) ⟨155459, by rfl⟩ : syracuseStep 207279 = 310919) B310919
theorem B207303 : Blo 203807 207303 := bstep (se 1 (by rfl) ⟨155477, by rfl⟩ : syracuseStep 207303 = 310955) B310955
theorem B207323 : Blo 203807 207323 := bstep (se 1 (by rfl) ⟨155492, by rfl⟩ : syracuseStep 207323 = 310985) B310985
theorem B698867 : Blo 203807 698867 := bstep (se 1 (by rfl) ⟨524150, by rfl⟩ : syracuseStep 698867 = 1048301) B1048301
theorem B207399 : Blo 203807 207399 := bstep (se 1 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 207399 = 311099) B311099
theorem B207439 : Blo 203807 207439 := bstep (se 1 (by rfl) ⟨155579, by rfl⟩ : syracuseStep 207439 = 311159) B311159
theorem B207455 : Blo 203807 207455 := bstep (se 1 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 207455 = 311183) B311183
theorem B207483 : Blo 203807 207483 := bstep (se 1 (by rfl) ⟨155612, by rfl⟩ : syracuseStep 207483 = 311225) B311225
theorem B207535 : Blo 203807 207535 := bstep (se 1 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 207535 = 311303) B311303
theorem B993977 : Blo 203807 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B207559 : Blo 203807 207559 := bstep (se 1 (by rfl) ⟨155669, by rfl⟩ : syracuseStep 207559 = 311339) B311339
theorem B207579 : Blo 203807 207579 := bstep (se 1 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 207579 = 311369) B311369
theorem B207655 : Blo 203807 207655 := bstep (se 1 (by rfl) ⟨155741, by rfl⟩ : syracuseStep 207655 = 311483) B311483
theorem B207695 : Blo 203807 207695 := bstep (se 1 (by rfl) ⟨155771, by rfl⟩ : syracuseStep 207695 = 311543) B311543
theorem B371551 : Blo 203807 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B207711 : Blo 203807 207711 := bstep (se 1 (by rfl) ⟨155783, by rfl⟩ : syracuseStep 207711 = 311567) B311567
theorem B207739 : Blo 203807 207739 := bstep (se 1 (by rfl) ⟨155804, by rfl⟩ : syracuseStep 207739 = 311609) B311609
theorem B306095 : Blo 203807 306095 := bstep (se 1 (by rfl) ⟨229571, by rfl⟩ : syracuseStep 306095 = 459143) B459143
theorem B207791 : Blo 203807 207791 := bstep (se 1 (by rfl) ⟨155843, by rfl⟩ : syracuseStep 207791 = 311687) B311687
theorem B306185 : Blo 203807 306185 := bstep (se 2 (by rfl) ⟨114819, by rfl⟩ : syracuseStep 306185 = 229639) B229639
theorem B699407 : Blo 203807 699407 := bstep (se 1 (by rfl) ⟨524555, by rfl⟩ : syracuseStep 699407 = 1049111) B1049111
theorem B306215 : Blo 203807 306215 := bstep (se 1 (by rfl) ⟨229661, by rfl⟩ : syracuseStep 306215 = 459323) B459323
theorem B306299 : Blo 203807 306299 := bstep (se 1 (by rfl) ⟨229724, by rfl⟩ : syracuseStep 306299 = 459449) B459449
theorem B306425 : Blo 203807 306425 := bstep (se 2 (by rfl) ⟨114909, by rfl⟩ : syracuseStep 306425 = 229819) B229819
theorem B306527 : Blo 203807 306527 := bstep (se 1 (by rfl) ⟨229895, by rfl⟩ : syracuseStep 306527 = 459791) B459791
theorem B306539 : Blo 203807 306539 := bstep (se 1 (by rfl) ⟨229904, by rfl⟩ : syracuseStep 306539 = 459809) B459809
theorem B306767 : Blo 203807 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B700001 : Blo 203807 700001 := bstep (se 2 (by rfl) ⟨262500, by rfl⟩ : syracuseStep 700001 = 525001) B525001
theorem B4009661 : Blo 203807 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B306887 : Blo 203807 306887 := bstep (se 1 (by rfl) ⟨230165, by rfl⟩ : syracuseStep 306887 = 460331) B460331
theorem B372575 : Blo 203807 372575 := bstep (se 1 (by rfl) ⟨279431, by rfl⟩ : syracuseStep 372575 = 558863) B558863
theorem B307049 : Blo 203807 307049 := bstep (se 2 (by rfl) ⟨115143, by rfl⟩ : syracuseStep 307049 = 230287) B230287
theorem B307127 : Blo 203807 307127 := bstep (se 1 (by rfl) ⟨230345, by rfl⟩ : syracuseStep 307127 = 460691) B460691
theorem B1421243 : Blo 203807 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B307163 : Blo 203807 307163 := bstep (se 1 (by rfl) ⟨230372, by rfl⟩ : syracuseStep 307163 = 460745) B460745
theorem B3321971 : Blo 203807 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B438443 : Blo 203807 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B372935 : Blo 203807 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B1552769 : Blo 203807 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B307631 : Blo 203807 307631 := bstep (se 1 (by rfl) ⟨230723, by rfl⟩ : syracuseStep 307631 = 461447) B461447
theorem B307721 : Blo 203807 307721 := bstep (se 2 (by rfl) ⟨115395, by rfl⟩ : syracuseStep 307721 = 230791) B230791
theorem B307751 : Blo 203807 307751 := bstep (se 1 (by rfl) ⟨230813, by rfl⟩ : syracuseStep 307751 = 461627) B461627
theorem B307835 : Blo 203807 307835 := bstep (se 1 (by rfl) ⟨230876, by rfl⟩ : syracuseStep 307835 = 461753) B461753
theorem B733819 : Blo 203807 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B995975 : Blo 203807 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B307961 : Blo 203807 307961 := bstep (se 2 (by rfl) ⟨115485, by rfl⟩ : syracuseStep 307961 = 230971) B230971
theorem B439033 : Blo 203807 439033 := bstep (se 2 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 439033 = 329275) B329275
theorem B10138385 : Blo 203807 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B897821 : Blo 203807 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B308063 : Blo 203807 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B308075 : Blo 203807 308075 := bstep (se 1 (by rfl) ⟨231056, by rfl⟩ : syracuseStep 308075 = 462113) B462113
theorem B1258415 : Blo 203807 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B308303 : Blo 203807 308303 := bstep (se 1 (by rfl) ⟨231227, by rfl⟩ : syracuseStep 308303 = 462455) B462455
theorem B308423 : Blo 203807 308423 := bstep (se 1 (by rfl) ⟨231317, by rfl⟩ : syracuseStep 308423 = 462635) B462635
theorem B308585 : Blo 203807 308585 := bstep (se 2 (by rfl) ⟨115719, by rfl⟩ : syracuseStep 308585 = 231439) B231439
theorem B308663 : Blo 203807 308663 := bstep (se 1 (by rfl) ⟨231497, by rfl⟩ : syracuseStep 308663 = 462995) B462995
theorem B308699 : Blo 203807 308699 := bstep (se 1 (by rfl) ⟨231524, by rfl⟩ : syracuseStep 308699 = 463049) B463049
theorem B3979043 : Blo 203807 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B309167 : Blo 203807 309167 := bstep (se 1 (by rfl) ⟨231875, by rfl⟩ : syracuseStep 309167 = 463751) B463751
theorem B309257 : Blo 203807 309257 := bstep (se 2 (by rfl) ⟨115971, by rfl⟩ : syracuseStep 309257 = 231943) B231943
theorem B309287 : Blo 203807 309287 := bstep (se 1 (by rfl) ⟨231965, by rfl⟩ : syracuseStep 309287 = 463931) B463931
theorem B6010969 : Blo 203807 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B309371 : Blo 203807 309371 := bstep (se 1 (by rfl) ⟨232028, by rfl⟩ : syracuseStep 309371 = 464057) B464057
theorem B309497 : Blo 203807 309497 := bstep (se 2 (by rfl) ⟨116061, by rfl⟩ : syracuseStep 309497 = 232123) B232123
theorem B309599 : Blo 203807 309599 := bstep (se 1 (by rfl) ⟨232199, by rfl⟩ : syracuseStep 309599 = 464399) B464399
theorem B309611 : Blo 203807 309611 := bstep (se 1 (by rfl) ⟨232208, by rfl⟩ : syracuseStep 309611 = 464417) B464417
theorem B1980875 : Blo 203807 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B3521069 : Blo 203807 3521069 := bstep (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) B1320401
theorem B309839 : Blo 203807 309839 := bstep (se 1 (by rfl) ⟨232379, by rfl⟩ : syracuseStep 309839 = 464759) B464759
theorem B309959 : Blo 203807 309959 := bstep (se 1 (by rfl) ⟨232469, by rfl⟩ : syracuseStep 309959 = 464939) B464939
theorem B670457 : Blo 203807 670457 := bstep (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) B502843
theorem B310121 : Blo 203807 310121 := bstep (se 2 (by rfl) ⟨116295, by rfl⟩ : syracuseStep 310121 = 232591) B232591
theorem B277355 : Blo 203807 277355 := bstep (se 1 (by rfl) ⟨208016, by rfl⟩ : syracuseStep 277355 = 416033) B416033
theorem B310199 : Blo 203807 310199 := bstep (se 1 (by rfl) ⟨232649, by rfl⟩ : syracuseStep 310199 = 465299) B465299
theorem B310235 : Blo 203807 310235 := bstep (se 1 (by rfl) ⟨232676, by rfl⟩ : syracuseStep 310235 = 465353) B465353
theorem B310703 : Blo 203807 310703 := bstep (se 1 (by rfl) ⟨233027, by rfl⟩ : syracuseStep 310703 = 466055) B466055
theorem B310793 : Blo 203807 310793 := bstep (se 2 (by rfl) ⟨116547, by rfl⟩ : syracuseStep 310793 = 233095) B233095
theorem B310823 : Blo 203807 310823 := bstep (se 1 (by rfl) ⟨233117, by rfl⟩ : syracuseStep 310823 = 466235) B466235
theorem B671291 : Blo 203807 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B1031777 : Blo 203807 1031777 := bstep (se 2 (by rfl) ⟨386916, by rfl⟩ : syracuseStep 1031777 = 773833) B773833
theorem B310907 : Blo 203807 310907 := bstep (se 1 (by rfl) ⟨233180, by rfl⟩ : syracuseStep 310907 = 466361) B466361
theorem B704135 : Blo 203807 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B1982141 : Blo 203807 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B311033 : Blo 203807 311033 := bstep (se 2 (by rfl) ⟨116637, by rfl⟩ : syracuseStep 311033 = 233275) B233275
theorem B311135 : Blo 203807 311135 := bstep (se 1 (by rfl) ⟨233351, by rfl⟩ : syracuseStep 311135 = 466703) B466703
theorem B442219 : Blo 203807 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B311147 : Blo 203807 311147 := bstep (se 1 (by rfl) ⟨233360, by rfl⟩ : syracuseStep 311147 = 466721) B466721
theorem B344027 : Blo 203807 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B278491 : Blo 203807 278491 := bstep (se 1 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 278491 = 417737) B417737
theorem B1196039 : Blo 203807 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B311375 : Blo 203807 311375 := bstep (se 1 (by rfl) ⟨233531, by rfl⟩ : syracuseStep 311375 = 467063) B467063
theorem B344263 : Blo 203807 344263 := bstep (se 1 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 344263 = 516395) B516395
theorem B311495 : Blo 203807 311495 := bstep (se 1 (by rfl) ⟨233621, by rfl⟩ : syracuseStep 311495 = 467243) B467243
theorem B344425 : Blo 203807 344425 := bstep (se 2 (by rfl) ⟨129159, by rfl⟩ : syracuseStep 344425 = 258319) B258319
theorem B311657 : Blo 203807 311657 := bstep (se 2 (by rfl) ⟨116871, by rfl⟩ : syracuseStep 311657 = 233743) B233743
theorem B836513 : Blo 203807 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B345019 : Blo 203807 345019 := bstep (se 1 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 345019 = 517529) B517529
theorem B1033235 : Blo 203807 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B345127 : Blo 203807 345127 := bstep (se 1 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 345127 = 517691) B517691
theorem B1328399 : Blo 203807 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B345451 : Blo 203807 345451 := bstep (se 1 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 345451 = 518177) B518177
theorem B11290661 : Blo 203807 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B1984601 : Blo 203807 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B346511 : Blo 203807 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B346747 : Blo 203807 346747 := bstep (se 1 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 346747 = 520121) B520121
theorem B1395409 : Blo 203807 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B1166035 : Blo 203807 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B1067951 : Blo 203807 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B674747 : Blo 203807 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B1330141 : Blo 203807 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B1166309 : Blo 203807 1166309 := bstep (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) B218683
theorem B445447 : Blo 203807 445447 := bstep (se 1 (by rfl) ⟨334085, by rfl⟩ : syracuseStep 445447 = 668171) B668171
theorem B314617 : Blo 203807 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B347611 : Blo 203807 347611 := bstep (se 1 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 347611 = 521417) B521417
theorem B1887877 : Blo 203807 1887877 := bstep (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) B353977
theorem B1166993 : Blo 203807 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B741113 : Blo 203807 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B1036151 : Blo 203807 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B1331063 : Blo 203807 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B348239 : Blo 203807 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B774791 : Blo 203807 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B12342131 : Blo 203807 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B349103 : Blo 203807 349103 := bstep (se 1 (by rfl) ⟨261827, by rfl⟩ : syracuseStep 349103 = 523655) B523655
theorem B447419 : Blo 203807 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B414727 : Blo 203807 414727 := bstep (se 1 (by rfl) ⟨311045, by rfl⟩ : syracuseStep 414727 = 622091) B622091
theorem B349535 : Blo 203807 349535 := bstep (se 1 (by rfl) ⟨262151, by rfl⟩ : syracuseStep 349535 = 524303) B524303
theorem B349705 : Blo 203807 349705 := bstep (se 2 (by rfl) ⟨131139, by rfl⟩ : syracuseStep 349705 = 262279) B262279
theorem B775777 : Blo 203807 775777 := bstep (se 2 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 775777 = 581833) B581833
theorem B1103581 : Blo 203807 1103581 := bstep (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) B413843
theorem B350095 : Blo 203807 350095 := bstep (se 1 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 350095 = 525143) B525143
theorem B776249 : Blo 203807 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B777235 : Blo 203807 777235 := bstep (se 1 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 777235 = 1165853) B1165853
theorem B581651 : Blo 203807 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B2613329 : Blo 203807 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B221383 : Blo 203807 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B581879 : Blo 203807 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B746081 : Blo 203807 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B778967 : Blo 203807 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B1041335 : Blo 203807 1041335 := bstep (se 1 (by rfl) ⟨781001, by rfl⟩ : syracuseStep 1041335 = 1562003) B1562003
theorem B1565891 : Blo 203807 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B517367 : Blo 203807 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B1992289 : Blo 203807 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B583291 : Blo 203807 583291 := bstep (se 1 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 583291 = 874937) B874937
theorem B583519 : Blo 203807 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B780151 : Blo 203807 780151 := bstep (se 1 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 780151 = 1170227) B1170227
theorem B1894337 : Blo 203807 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B6383717 : Blo 203807 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B2222387 : Blo 203807 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B387433 : Blo 203807 387433 := bstep (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) B290575
theorem B1042793 : Blo 203807 1042793 := bstep (se 2 (by rfl) ⟨391047, by rfl⟩ : syracuseStep 1042793 = 782095) B782095
theorem B748091 : Blo 203807 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B518795 : Blo 203807 518795 := bstep (se 1 (by rfl) ⟨389096, by rfl⟩ : syracuseStep 518795 = 778193) B778193
theorem B781123 : Blo 203807 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B3533645 : Blo 203807 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B519007 : Blo 203807 519007 := bstep (se 1 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 519007 = 778511) B778511
theorem B486319 : Blo 203807 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B781427 : Blo 203807 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B388307 : Blo 203807 388307 := bstep (se 1 (by rfl) ⟨291230, by rfl⟩ : syracuseStep 388307 = 582461) B582461
theorem B585103 : Blo 203807 585103 := bstep (se 1 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 585103 = 877655) B877655
theorem B781883 : Blo 203807 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B519929 : Blo 203807 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B388937 : Blo 203807 388937 := bstep (se 2 (by rfl) ⟨145851, by rfl⟩ : syracuseStep 388937 = 291703) B291703
theorem B421775 : Blo 203807 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B520577 : Blo 203807 520577 := bstep (se 2 (by rfl) ⟨195216, by rfl⟩ : syracuseStep 520577 = 390433) B390433
theorem B1995137 : Blo 203807 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B291367 : Blo 203807 291367 := bstep (se 1 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 291367 = 437051) B437051
theorem B389711 : Blo 203807 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B586379 : Blo 203807 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B13202189 : Blo 203807 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B291691 : Blo 203807 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B553835 : Blo 203807 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B291919 : Blo 203807 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B259195 : Blo 203807 259195 := bstep (se 1 (by rfl) ⟨194396, by rfl⟩ : syracuseStep 259195 = 388793) B388793
theorem B521387 : Blo 203807 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B2880715 : Blo 203807 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B1963379 : Blo 203807 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B3536369 : Blo 203807 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B1308305 : Blo 203807 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B5732021 : Blo 203807 5732021 := bstep (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) B537377
theorem B522247 : Blo 203807 522247 := bstep (se 1 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 522247 = 783371) B783371
theorem B2619479 : Blo 203807 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B391367 : Blo 203807 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B1472741 : Blo 203807 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B653629 : Blo 203807 653629 := bstep (se 3 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 653629 = 245111) B245111
theorem B621179 : Blo 203807 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B522875 : Blo 203807 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B391891 : Blo 203807 391891 := bstep (se 1 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 391891 = 587837) B587837
theorem B359273 : Blo 203807 359273 := bstep (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) B269455
theorem B523115 : Blo 203807 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B523169 : Blo 203807 523169 := bstep (se 2 (by rfl) ⟨196188, by rfl⟩ : syracuseStep 523169 = 392377) B392377
theorem B392111 : Blo 203807 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B261083 : Blo 203807 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B1473689 : Blo 203807 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B392521 : Blo 203807 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B261559 : Blo 203807 261559 := bstep (se 1 (by rfl) ⟨196169, by rfl⟩ : syracuseStep 261559 = 392339) B392339
theorem B589351 : Blo 203807 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B3538565 : Blo 203807 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B589511 : Blo 203807 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B458603 : Blo 203807 458603 := bstep (se 1 (by rfl) ⟨343952, by rfl⟩ : syracuseStep 458603 = 687905) B687905
theorem B458657 : Blo 203807 458657 := bstep (se 2 (by rfl) ⟨171996, by rfl⟩ : syracuseStep 458657 = 343993) B343993
theorem B589751 : Blo 203807 589751 := bstep (se 1 (by rfl) ⟨442313, by rfl⟩ : syracuseStep 589751 = 884627) B884627
theorem B458963 : Blo 203807 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B1048787 : Blo 203807 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B459017 : Blo 203807 459017 := bstep (se 2 (by rfl) ⟨172131, by rfl⟩ : syracuseStep 459017 = 344263) B344263
theorem B295177 : Blo 203807 295177 := bstep (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) B221383
theorem B459233 : Blo 203807 459233 := bstep (se 2 (by rfl) ⟨172212, by rfl⟩ : syracuseStep 459233 = 344425) B344425
theorem B524819 : Blo 203807 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B328255 : Blo 203807 328255 := bstep (se 1 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 328255 = 492383) B492383
theorem B557675 : Blo 203807 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B393835 : Blo 203807 393835 := bstep (se 1 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 393835 = 590753) B590753
theorem B688823 : Blo 203807 688823 := bstep (se 1 (by rfl) ⟨516617, by rfl⟩ : syracuseStep 688823 = 1033235) B1033235
theorem B524983 : Blo 203807 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B459539 : Blo 203807 459539 := bstep (se 1 (by rfl) ⟨344654, by rfl⟩ : syracuseStep 459539 = 689309) B689309
theorem B885599 : Blo 203807 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B394139 : Blo 203807 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B525275 : Blo 203807 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B459899 : Blo 203807 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B460025 : Blo 203807 460025 := bstep (se 2 (by rfl) ⟨172509, by rfl⟩ : syracuseStep 460025 = 345019) B345019
theorem B525599 : Blo 203807 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B460169 : Blo 203807 460169 := bstep (se 2 (by rfl) ⟨172563, by rfl⟩ : syracuseStep 460169 = 345127) B345127
theorem B3933683 : Blo 203807 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B460295 : Blo 203807 460295 := bstep (se 1 (by rfl) ⟨345221, by rfl⟩ : syracuseStep 460295 = 690443) B690443
theorem B231007 : Blo 203807 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B460475 : Blo 203807 460475 := bstep (se 1 (by rfl) ⟨345356, by rfl⟩ : syracuseStep 460475 = 690713) B690713
theorem B460601 : Blo 203807 460601 := bstep (se 2 (by rfl) ⟨172725, by rfl⟩ : syracuseStep 460601 = 345451) B345451
theorem B2656385 : Blo 203807 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B1181891 : Blo 203807 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B1476893 : Blo 203807 1476893 := bstep (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) B553835
theorem B330095 : Blo 203807 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B985517 : Blo 203807 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B461231 : Blo 203807 461231 := bstep (se 1 (by rfl) ⟨345923, by rfl⟩ : syracuseStep 461231 = 691847) B691847
theorem B461267 : Blo 203807 461267 := bstep (se 1 (by rfl) ⟨345950, by rfl⟩ : syracuseStep 461267 = 691901) B691901
theorem B494075 : Blo 203807 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B461375 : Blo 203807 461375 := bstep (se 1 (by rfl) ⟨346031, by rfl⟩ : syracuseStep 461375 = 692063) B692063
theorem B690767 : Blo 203807 690767 := bstep (se 1 (by rfl) ⟨518075, by rfl⟩ : syracuseStep 690767 = 1036151) B1036151
theorem B887375 : Blo 203807 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B461483 : Blo 203807 461483 := bstep (se 1 (by rfl) ⟨346112, by rfl⟩ : syracuseStep 461483 = 692225) B692225
theorem B232159 : Blo 203807 232159 := bstep (se 1 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 232159 = 348239) B348239
theorem B330895 : Blo 203807 330895 := bstep (se 1 (by rfl) ⟨248171, by rfl⟩ : syracuseStep 330895 = 496343) B496343
theorem B462023 : Blo 203807 462023 := bstep (se 1 (by rfl) ⟨346517, by rfl⟩ : syracuseStep 462023 = 693035) B693035
theorem B8228087 : Blo 203807 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B232735 : Blo 203807 232735 := bstep (se 1 (by rfl) ⟨174551, by rfl⟩ : syracuseStep 232735 = 349103) B349103
theorem B298279 : Blo 203807 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B462203 : Blo 203807 462203 := bstep (se 1 (by rfl) ⟨346652, by rfl⟩ : syracuseStep 462203 = 693305) B693305
theorem B462329 : Blo 203807 462329 := bstep (se 2 (by rfl) ⟨173373, by rfl⟩ : syracuseStep 462329 = 346747) B346747
theorem B233023 : Blo 203807 233023 := bstep (se 1 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 233023 = 349535) B349535
theorem B7179853 : Blo 203807 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B462419 : Blo 203807 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B462599 : Blo 203807 462599 := bstep (se 1 (by rfl) ⟨346949, by rfl⟩ : syracuseStep 462599 = 693899) B693899
theorem B692009 : Blo 203807 692009 := bstep (se 2 (by rfl) ⟨259503, by rfl⟩ : syracuseStep 692009 = 519007) B519007
theorem B495401 : Blo 203807 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B1773521 : Blo 203807 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B593929 : Blo 203807 593929 := bstep (se 2 (by rfl) ⟨222723, by rfl⟩ : syracuseStep 593929 = 445447) B445447
theorem B463211 : Blo 203807 463211 := bstep (se 1 (by rfl) ⟨347408, by rfl⟩ : syracuseStep 463211 = 694817) B694817
theorem B397735 : Blo 203807 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B463355 : Blo 203807 463355 := bstep (se 1 (by rfl) ⟨347516, by rfl⟩ : syracuseStep 463355 = 695033) B695033
theorem B1315379 : Blo 203807 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B463481 : Blo 203807 463481 := bstep (se 2 (by rfl) ⟨173805, by rfl⟩ : syracuseStep 463481 = 347611) B347611
theorem B463535 : Blo 203807 463535 := bstep (se 1 (by rfl) ⟨347651, by rfl⟩ : syracuseStep 463535 = 695303) B695303
theorem B463607 : Blo 203807 463607 := bstep (se 1 (by rfl) ⟨347705, by rfl⟩ : syracuseStep 463607 = 695411) B695411
theorem B463787 : Blo 203807 463787 := bstep (se 1 (by rfl) ⟨347840, by rfl⟩ : syracuseStep 463787 = 695681) B695681
theorem B1578041 : Blo 203807 1578041 := bstep (se 2 (by rfl) ⟨591765, by rfl⟩ : syracuseStep 1578041 = 1183531) B1183531
theorem B1742219 : Blo 203807 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B464327 : Blo 203807 464327 := bstep (se 1 (by rfl) ⟨348245, by rfl⟩ : syracuseStep 464327 = 696491) B696491
theorem B2561675 : Blo 203807 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B497387 : Blo 203807 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B464687 : Blo 203807 464687 := bstep (se 1 (by rfl) ⟨348515, by rfl⟩ : syracuseStep 464687 = 697031) B697031
theorem B19929037 : Blo 203807 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B694223 : Blo 203807 694223 := bstep (se 1 (by rfl) ⟨520667, by rfl⟩ : syracuseStep 694223 = 1041335) B1041335
theorem B4462937 : Blo 203807 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B8395109 : Blo 203807 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B465263 : Blo 203807 465263 := bstep (se 1 (by rfl) ⟨348947, by rfl⟩ : syracuseStep 465263 = 697895) B697895
theorem B465335 : Blo 203807 465335 := bstep (se 1 (by rfl) ⟨349001, by rfl⟩ : syracuseStep 465335 = 698003) B698003
theorem B465479 : Blo 203807 465479 := bstep (se 1 (by rfl) ⟨349109, by rfl⟩ : syracuseStep 465479 = 698219) B698219
theorem B465515 : Blo 203807 465515 := bstep (se 1 (by rfl) ⟨349136, by rfl⟩ : syracuseStep 465515 = 698273) B698273
theorem B1776323 : Blo 203807 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1481591 : Blo 203807 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B695195 : Blo 203807 695195 := bstep (se 1 (by rfl) ⟨521396, by rfl⟩ : syracuseStep 695195 = 1042793) B1042793
theorem B3840953 : Blo 203807 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B465911 : Blo 203807 465911 := bstep (se 1 (by rfl) ⟨349433, by rfl⟩ : syracuseStep 465911 = 698867) B698867
theorem B498727 : Blo 203807 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B662651 : Blo 203807 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B204063 : Blo 203807 204063 := bstep (se 1 (by rfl) ⟨153047, by rfl⟩ : syracuseStep 204063 = 306095) B306095
theorem B204123 : Blo 203807 204123 := bstep (se 1 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 204123 = 306185) B306185
theorem B3939677 : Blo 203807 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B466271 : Blo 203807 466271 := bstep (se 1 (by rfl) ⟨349703, by rfl⟩ : syracuseStep 466271 = 699407) B699407
theorem B466273 : Blo 203807 466273 := bstep (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) B349705
theorem B204143 : Blo 203807 204143 := bstep (se 1 (by rfl) ⟨153107, by rfl⟩ : syracuseStep 204143 = 306215) B306215
theorem B204199 : Blo 203807 204199 := bstep (se 1 (by rfl) ⟨153149, by rfl⟩ : syracuseStep 204199 = 306299) B306299
theorem B204283 : Blo 203807 204283 := bstep (se 1 (by rfl) ⟨153212, by rfl⟩ : syracuseStep 204283 = 306425) B306425
theorem B204351 : Blo 203807 204351 := bstep (se 1 (by rfl) ⟨153263, by rfl⟩ : syracuseStep 204351 = 306527) B306527
theorem B204359 : Blo 203807 204359 := bstep (se 1 (by rfl) ⟨153269, by rfl⟩ : syracuseStep 204359 = 306539) B306539
theorem B958061 : Blo 203807 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B204511 : Blo 203807 204511 := bstep (se 1 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 204511 = 306767) B306767
theorem B466667 : Blo 203807 466667 := bstep (se 1 (by rfl) ⟨350000, by rfl⟩ : syracuseStep 466667 = 700001) B700001
theorem B204591 : Blo 203807 204591 := bstep (se 1 (by rfl) ⟨153443, by rfl⟩ : syracuseStep 204591 = 306887) B306887
theorem B466793 : Blo 203807 466793 := bstep (se 2 (by rfl) ⟨175047, by rfl⟩ : syracuseStep 466793 = 350095) B350095
theorem B204699 : Blo 203807 204699 := bstep (se 1 (by rfl) ⟨153524, by rfl⟩ : syracuseStep 204699 = 307049) B307049
theorem B696221 : Blo 203807 696221 := bstep (se 3 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 696221 = 261083) B261083
theorem B204751 : Blo 203807 204751 := bstep (se 1 (by rfl) ⟨153563, by rfl⟩ : syracuseStep 204751 = 307127) B307127
theorem B204775 : Blo 203807 204775 := bstep (se 1 (by rfl) ⟨153581, by rfl⟩ : syracuseStep 204775 = 307163) B307163
theorem B696329 : Blo 203807 696329 := bstep (se 2 (by rfl) ⟨261123, by rfl⟩ : syracuseStep 696329 = 522247) B522247
theorem B3547313 : Blo 203807 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B205087 : Blo 203807 205087 := bstep (se 1 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 205087 = 307631) B307631
theorem B205147 : Blo 203807 205147 := bstep (se 1 (by rfl) ⟨153860, by rfl⟩ : syracuseStep 205147 = 307721) B307721
theorem B205167 : Blo 203807 205167 := bstep (se 1 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 205167 = 307751) B307751
theorem B205223 : Blo 203807 205223 := bstep (se 1 (by rfl) ⟨153917, by rfl⟩ : syracuseStep 205223 = 307835) B307835
theorem B663983 : Blo 203807 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B205307 : Blo 203807 205307 := bstep (se 1 (by rfl) ⟨153980, by rfl⟩ : syracuseStep 205307 = 307961) B307961
theorem B6758923 : Blo 203807 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B598547 : Blo 203807 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B205375 : Blo 203807 205375 := bstep (se 1 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 205375 = 308063) B308063
theorem B205383 : Blo 203807 205383 := bstep (se 1 (by rfl) ⟨154037, by rfl⟩ : syracuseStep 205383 = 308075) B308075
theorem B205535 : Blo 203807 205535 := bstep (se 1 (by rfl) ⟨154151, by rfl⟩ : syracuseStep 205535 = 308303) B308303
theorem B205615 : Blo 203807 205615 := bstep (se 1 (by rfl) ⟨154211, by rfl⟩ : syracuseStep 205615 = 308423) B308423
theorem B205723 : Blo 203807 205723 := bstep (se 1 (by rfl) ⟨154292, by rfl⟩ : syracuseStep 205723 = 308585) B308585
theorem B205775 : Blo 203807 205775 := bstep (se 1 (by rfl) ⟨154331, by rfl⟩ : syracuseStep 205775 = 308663) B308663
theorem B205799 : Blo 203807 205799 := bstep (se 1 (by rfl) ⟨154349, by rfl⟩ : syracuseStep 205799 = 308699) B308699
theorem B1975529 : Blo 203807 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B206111 : Blo 203807 206111 := bstep (se 1 (by rfl) ⟨154583, by rfl⟩ : syracuseStep 206111 = 309167) B309167
theorem B206171 : Blo 203807 206171 := bstep (se 1 (by rfl) ⟨154628, by rfl⟩ : syracuseStep 206171 = 309257) B309257
theorem B206191 : Blo 203807 206191 := bstep (se 1 (by rfl) ⟨154643, by rfl⟩ : syracuseStep 206191 = 309287) B309287
theorem B1746319 : Blo 203807 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B206247 : Blo 203807 206247 := bstep (se 1 (by rfl) ⟨154685, by rfl⟩ : syracuseStep 206247 = 309371) B309371
theorem B206331 : Blo 203807 206331 := bstep (se 1 (by rfl) ⟨154748, by rfl⟩ : syracuseStep 206331 = 309497) B309497
theorem B206399 : Blo 203807 206399 := bstep (se 1 (by rfl) ⟨154799, by rfl⟩ : syracuseStep 206399 = 309599) B309599
theorem B206407 : Blo 203807 206407 := bstep (se 1 (by rfl) ⟨154805, by rfl⟩ : syracuseStep 206407 = 309611) B309611
theorem B1320583 : Blo 203807 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B206559 : Blo 203807 206559 := bstep (se 1 (by rfl) ⟨154919, by rfl⟩ : syracuseStep 206559 = 309839) B309839
theorem B206639 : Blo 203807 206639 := bstep (se 1 (by rfl) ⟨154979, by rfl⟩ : syracuseStep 206639 = 309959) B309959
theorem B206747 : Blo 203807 206747 := bstep (se 1 (by rfl) ⟨155060, by rfl⟩ : syracuseStep 206747 = 310121) B310121
theorem B206799 : Blo 203807 206799 := bstep (se 1 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 206799 = 310199) B310199
theorem B206823 : Blo 203807 206823 := bstep (se 1 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 206823 = 310235) B310235
theorem B207135 : Blo 203807 207135 := bstep (se 1 (by rfl) ⟨155351, by rfl⟩ : syracuseStep 207135 = 310703) B310703
theorem B207195 : Blo 203807 207195 := bstep (se 1 (by rfl) ⟨155396, by rfl⟩ : syracuseStep 207195 = 310793) B310793
theorem B207215 : Blo 203807 207215 := bstep (se 1 (by rfl) ⟨155411, by rfl⟩ : syracuseStep 207215 = 310823) B310823
theorem B207271 : Blo 203807 207271 := bstep (se 1 (by rfl) ⟨155453, by rfl⟩ : syracuseStep 207271 = 310907) B310907
theorem B469423 : Blo 203807 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B1321427 : Blo 203807 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B207355 : Blo 203807 207355 := bstep (se 1 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 207355 = 311033) B311033
theorem B207423 : Blo 203807 207423 := bstep (se 1 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 207423 = 311135) B311135
theorem B305735 : Blo 203807 305735 := bstep (se 1 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 305735 = 458603) B458603
theorem B207431 : Blo 203807 207431 := bstep (se 1 (by rfl) ⟨155573, by rfl⟩ : syracuseStep 207431 = 311147) B311147
theorem B305771 : Blo 203807 305771 := bstep (se 1 (by rfl) ⟨229328, by rfl⟩ : syracuseStep 305771 = 458657) B458657
theorem B371321 : Blo 203807 371321 := bstep (se 2 (by rfl) ⟨139245, by rfl⟩ : syracuseStep 371321 = 278491) B278491
theorem B797359 : Blo 203807 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B207583 : Blo 203807 207583 := bstep (se 1 (by rfl) ⟨155687, by rfl⟩ : syracuseStep 207583 = 311375) B311375
theorem B207663 : Blo 203807 207663 := bstep (se 1 (by rfl) ⟨155747, by rfl⟩ : syracuseStep 207663 = 311495) B311495
theorem B305999 : Blo 203807 305999 := bstep (se 1 (by rfl) ⟨229499, by rfl⟩ : syracuseStep 305999 = 458999) B458999
theorem B2632601 : Blo 203807 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B207771 : Blo 203807 207771 := bstep (se 1 (by rfl) ⟨155828, by rfl⟩ : syracuseStep 207771 = 311657) B311657
theorem B621849635 : Blo 203807 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B699515 : Blo 203807 699515 := bstep (se 1 (by rfl) ⟨524636, by rfl⟩ : syracuseStep 699515 = 1049273) B1049273
theorem B994493 : Blo 203807 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B306395 : Blo 203807 306395 := bstep (se 1 (by rfl) ⟨229796, by rfl⟩ : syracuseStep 306395 = 459593) B459593
theorem B306569 : Blo 203807 306569 := bstep (se 2 (by rfl) ⟨114963, by rfl⟩ : syracuseStep 306569 = 229927) B229927
theorem B699785 : Blo 203807 699785 := bstep (se 2 (by rfl) ⟨262419, by rfl⟩ : syracuseStep 699785 = 524839) B524839
theorem B306923 : Blo 203807 306923 := bstep (se 1 (by rfl) ⟨230192, by rfl⟩ : syracuseStep 306923 = 460385) B460385
theorem B700217 : Blo 203807 700217 := bstep (se 2 (by rfl) ⟨262581, by rfl⟩ : syracuseStep 700217 = 525163) B525163
theorem B307151 : Blo 203807 307151 := bstep (se 1 (by rfl) ⟨230363, by rfl⟩ : syracuseStep 307151 = 460727) B460727
theorem B438281 : Blo 203807 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B1323067 : Blo 203807 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B3551321 : Blo 203807 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B307547 : Blo 203807 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B307775 : Blo 203807 307775 := bstep (se 1 (by rfl) ⟨230831, by rfl⟩ : syracuseStep 307775 = 461663) B461663
theorem B701081 : Blo 203807 701081 := bstep (se 2 (by rfl) ⟨262905, by rfl⟩ : syracuseStep 701081 = 525811) B525811
theorem B307895 : Blo 203807 307895 := bstep (se 1 (by rfl) ⟨230921, by rfl⟩ : syracuseStep 307895 = 461843) B461843
theorem B2634605 : Blo 203807 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B308123 : Blo 203807 308123 := bstep (se 1 (by rfl) ⟨231092, by rfl⟩ : syracuseStep 308123 = 462185) B462185
theorem B439195 : Blo 203807 439195 := bstep (se 1 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 439195 = 658793) B658793
theorem B308519 : Blo 203807 308519 := bstep (se 1 (by rfl) ⟨231389, by rfl⟩ : syracuseStep 308519 = 462779) B462779
theorem B308603 : Blo 203807 308603 := bstep (se 1 (by rfl) ⟨231452, by rfl⟩ : syracuseStep 308603 = 462905) B462905
theorem B308729 : Blo 203807 308729 := bstep (se 2 (by rfl) ⟨115773, by rfl⟩ : syracuseStep 308729 = 231547) B231547
theorem B308831 : Blo 203807 308831 := bstep (se 1 (by rfl) ⟨231623, by rfl⟩ : syracuseStep 308831 = 463247) B463247
theorem B309047 : Blo 203807 309047 := bstep (se 1 (by rfl) ⟨231785, by rfl⟩ : syracuseStep 309047 = 463571) B463571
theorem B309353 : Blo 203807 309353 := bstep (se 2 (by rfl) ⟨116007, by rfl⟩ : syracuseStep 309353 = 232015) B232015
theorem B1554713 : Blo 203807 1554713 := bstep (se 2 (by rfl) ⟨583017, by rfl⟩ : syracuseStep 1554713 = 1166035) B1166035
theorem B309671 : Blo 203807 309671 := bstep (se 1 (by rfl) ⟨232253, by rfl⟩ : syracuseStep 309671 = 464507) B464507
theorem B309755 : Blo 203807 309755 := bstep (se 1 (by rfl) ⟨232316, by rfl⟩ : syracuseStep 309755 = 464633) B464633
theorem B440903 : Blo 203807 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B309881 : Blo 203807 309881 := bstep (se 2 (by rfl) ⟨116205, by rfl⟩ : syracuseStep 309881 = 232411) B232411
theorem B309935 : Blo 203807 309935 := bstep (se 1 (by rfl) ⟨232451, by rfl⟩ : syracuseStep 309935 = 464903) B464903
theorem B309983 : Blo 203807 309983 := bstep (se 1 (by rfl) ⟨232487, by rfl⟩ : syracuseStep 309983 = 464975) B464975
theorem B310247 : Blo 203807 310247 := bstep (se 1 (by rfl) ⟨232685, by rfl⟩ : syracuseStep 310247 = 465371) B465371
theorem B441467 : Blo 203807 441467 := bstep (se 1 (by rfl) ⟨331100, by rfl⟩ : syracuseStep 441467 = 662201) B662201
theorem B2112733 : Blo 203807 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B1555685 : Blo 203807 1555685 := bstep (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) B291691
theorem B310505 : Blo 203807 310505 := bstep (se 2 (by rfl) ⟨116439, by rfl⟩ : syracuseStep 310505 = 232879) B232879
theorem B310559 : Blo 203807 310559 := bstep (se 1 (by rfl) ⟨232919, by rfl⟩ : syracuseStep 310559 = 465839) B465839
theorem B310727 : Blo 203807 310727 := bstep (se 1 (by rfl) ⟨233045, by rfl⟩ : syracuseStep 310727 = 466091) B466091
theorem B1031939 : Blo 203807 1031939 := bstep (se 1 (by rfl) ⟨773954, by rfl⟩ : syracuseStep 1031939 = 1547909) B1547909
theorem B311081 : Blo 203807 311081 := bstep (se 2 (by rfl) ⟨116655, by rfl⟩ : syracuseStep 311081 = 233311) B233311
theorem B311087 : Blo 203807 311087 := bstep (se 1 (by rfl) ⟨233315, by rfl⟩ : syracuseStep 311087 = 466631) B466631
theorem B245711 : Blo 203807 245711 := bstep (se 1 (by rfl) ⟨184283, by rfl⟩ : syracuseStep 245711 = 368567) B368567
theorem B2211877 : Blo 203807 2211877 := bstep (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) B414727
theorem B311561 : Blo 203807 311561 := bstep (se 2 (by rfl) ⟨116835, by rfl⟩ : syracuseStep 311561 = 233671) B233671
theorem B311663 : Blo 203807 311663 := bstep (se 1 (by rfl) ⟨233747, by rfl⟩ : syracuseStep 311663 = 467495) B467495
theorem B311879 : Blo 203807 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B344911 : Blo 203807 344911 := bstep (se 1 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 344911 = 517367) B517367
theorem B705779 : Blo 203807 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B1262891 : Blo 203807 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B1033559 : Blo 203807 1033559 := bstep (se 1 (by rfl) ⟨775169, by rfl⟩ : syracuseStep 1033559 = 1550339) B1550339
theorem B705887 : Blo 203807 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B2803187 : Blo 203807 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B345593 : Blo 203807 345593 := bstep (se 2 (by rfl) ⟨129597, by rfl⟩ : syracuseStep 345593 = 259195) B259195
theorem B345863 : Blo 203807 345863 := bstep (se 1 (by rfl) ⟨259397, by rfl⟩ : syracuseStep 345863 = 518795) B518795
theorem B1034369 : Blo 203807 1034369 := bstep (se 2 (by rfl) ⟨387888, by rfl⟩ : syracuseStep 1034369 = 775777) B775777
theorem B9423053 : Blo 203807 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B739613 : Blo 203807 739613 := bstep (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) B277355
theorem B2673107 : Blo 203807 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B346619 : Blo 203807 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B248383 : Blo 203807 248383 := bstep (se 1 (by rfl) ⟨186287, by rfl⟩ : syracuseStep 248383 = 372575) B372575
theorem B281183 : Blo 203807 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B2214647 : Blo 203807 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B8014625 : Blo 203807 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B1035179 : Blo 203807 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B347051 : Blo 203807 347051 := bstep (se 1 (by rfl) ⟨260288, by rfl⟩ : syracuseStep 347051 = 520577) B520577
theorem B1330091 : Blo 203807 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B871505 : Blo 203807 871505 := bstep (se 2 (by rfl) ⟨326814, by rfl⟩ : syracuseStep 871505 = 653629) B653629
theorem B8801459 : Blo 203807 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B838943 : Blo 203807 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B347591 : Blo 203807 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B872203 : Blo 203807 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B3821347 : Blo 203807 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B1036313 : Blo 203807 1036313 := bstep (se 2 (by rfl) ⟨388617, by rfl⟩ : syracuseStep 1036313 = 777235) B777235
theorem B2347379 : Blo 203807 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B414119 : Blo 203807 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B348583 : Blo 203807 348583 := bstep (se 1 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 348583 = 522875) B522875
theorem B446971 : Blo 203807 446971 := bstep (se 1 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 446971 = 670457) B670457
theorem B1495601 : Blo 203807 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B348743 : Blo 203807 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B348745 : Blo 203807 348745 := bstep (se 2 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 348745 = 261559) B261559
theorem B348779 : Blo 203807 348779 := bstep (se 1 (by rfl) ⟨261584, by rfl⟩ : syracuseStep 348779 = 523169) B523169
theorem B1102481 : Blo 203807 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B447527 : Blo 203807 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B350473 : Blo 203807 350473 := bstep (se 2 (by rfl) ⟨131427, by rfl⟩ : syracuseStep 350473 = 262855) B262855
theorem B7527107 : Blo 203807 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B219871 : Blo 203807 219871 := bstep (se 1 (by rfl) ⟨164903, by rfl⟩ : syracuseStep 219871 = 329807) B329807
theorem B1039229 : Blo 203807 1039229 := bstep (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) B389711
theorem B744571 : Blo 203807 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B449831 : Blo 203807 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B777539 : Blo 203807 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B777721 : Blo 203807 777721 := bstep (se 2 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 777721 = 583291) B583291
theorem B1990291 : Blo 203807 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B777995 : Blo 203807 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B9002785 : Blo 203807 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B778025 : Blo 203807 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B1040201 : Blo 203807 1040201 := bstep (se 2 (by rfl) ⟨390075, by rfl⟩ : syracuseStep 1040201 = 780151) B780151
theorem B221135 : Blo 203807 221135 := bstep (se 1 (by rfl) ⟨165851, by rfl⟩ : syracuseStep 221135 = 331703) B331703
theorem B516527 : Blo 203807 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B516577 : Blo 203807 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B1860545 : Blo 203807 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B5235677 : Blo 203807 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B1532903 : Blo 203807 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1041497 : Blo 203807 1041497 := bstep (se 2 (by rfl) ⟨390561, by rfl⟩ : syracuseStep 1041497 = 781123) B781123
theorem B648425 : Blo 203807 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B517499 : Blo 203807 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B419489 : Blo 203807 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B780137 : Blo 203807 780137 := bstep (se 2 (by rfl) ⟨292551, by rfl⟩ : syracuseStep 780137 = 585103) B585103
theorem B2517169 : Blo 203807 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B2648699 : Blo 203807 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B387767 : Blo 203807 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B387919 : Blo 203807 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B519311 : Blo 203807 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B388489 : Blo 203807 388489 := bstep (se 2 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 388489 = 291367) B291367
theorem B1043927 : Blo 203807 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B978425 : Blo 203807 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B585377 : Blo 203807 585377 := bstep (se 2 (by rfl) ⟨219516, by rfl⟩ : syracuseStep 585377 = 439033) B439033
theorem B880541 : Blo 203807 880541 := bstep (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) B330203
theorem B4255811 : Blo 203807 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B3960899 : Blo 203807 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B389225 : Blo 203807 389225 := bstep (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) B291919
theorem B520951 : Blo 203807 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B258871 : Blo 203807 258871 := bstep (se 1 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 258871 = 388307) B388307
theorem B1471441 : Blo 203807 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B521255 : Blo 203807 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B2847869 : Blo 203807 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B259291 : Blo 203807 259291 := bstep (se 1 (by rfl) ⟨194468, by rfl⟩ : syracuseStep 259291 = 388937) B388937
theorem B947495 : Blo 203807 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B882029 : Blo 203807 882029 := bstep (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) B330761
theorem B292295 : Blo 203807 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B390919 : Blo 203807 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B522521 : Blo 203807 522521 := bstep (se 2 (by rfl) ⟨195945, by rfl⟩ : syracuseStep 522521 = 391891) B391891
theorem B2357579 : Blo 203807 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B2652695 : Blo 203807 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B260911 : Blo 203807 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B981827 : Blo 203807 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B523361 : Blo 203807 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B261407 : Blo 203807 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B785801 : Blo 203807 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B982459 : Blo 203807 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B687851 : Blo 203807 687851 := bstep (se 1 (by rfl) ⟨515888, by rfl⟩ : syracuseStep 687851 = 1031777) B1031777
theorem B2359043 : Blo 203807 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B393007 : Blo 203807 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B589625 : Blo 203807 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B393167 : Blo 203807 393167 := bstep (se 1 (by rfl) ⟨294875, by rfl⟩ : syracuseStep 393167 = 589751) B589751
theorem B229351 : Blo 203807 229351 := bstep (se 1 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 229351 = 344027) B344027
theorem B2949169 : Blo 203807 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B9470189 : Blo 203807 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B393569 : Blo 203807 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B459215 : Blo 203807 459215 := bstep (se 1 (by rfl) ⟨344411, by rfl⟩ : syracuseStep 459215 = 688823) B688823
theorem B590399 : Blo 203807 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B262759 : Blo 203807 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B688769 : Blo 203807 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B9011897 : Blo 203807 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B525113 : Blo 203807 525113 := bstep (se 2 (by rfl) ⟨196917, by rfl⟩ : syracuseStep 525113 = 393835) B393835
theorem B689039 : Blo 203807 689039 := bstep (se 1 (by rfl) ⟨516779, by rfl⟩ : syracuseStep 689039 = 1033559) B1033559
theorem B2622455 : Blo 203807 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B230395 : Blo 203807 230395 := bstep (se 1 (by rfl) ⟨172796, by rfl⟩ : syracuseStep 230395 = 345593) B345593
theorem B459881 : Blo 203807 459881 := bstep (se 2 (by rfl) ⟨172455, by rfl⟩ : syracuseStep 459881 = 344911) B344911
theorem B230575 : Blo 203807 230575 := bstep (se 1 (by rfl) ⟨172931, by rfl⟩ : syracuseStep 230575 = 345863) B345863
theorem B689579 : Blo 203807 689579 := bstep (se 1 (by rfl) ⟨517184, by rfl⟩ : syracuseStep 689579 = 1034369) B1034369
theorem B1770923 : Blo 203807 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B787927 : Blo 203807 787927 := bstep (se 1 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 787927 = 1181891) B1181891
theorem B984595 : Blo 203807 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B493075 : Blo 203807 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B657011 : Blo 203807 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B231079 : Blo 203807 231079 := bstep (se 1 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 231079 = 346619) B346619
theorem B329383 : Blo 203807 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B460511 : Blo 203807 460511 := bstep (se 1 (by rfl) ⟨345383, by rfl⟩ : syracuseStep 460511 = 690767) B690767
theorem B1476431 : Blo 203807 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B2328425 : Blo 203807 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B5343083 : Blo 203807 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B690119 : Blo 203807 690119 := bstep (se 1 (by rfl) ⟨517589, by rfl⟩ : syracuseStep 690119 = 1035179) B1035179
theorem B231367 : Blo 203807 231367 := bstep (se 1 (by rfl) ⟨173525, by rfl⟩ : syracuseStep 231367 = 347051) B347051
theorem B886727 : Blo 203807 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B5867639 : Blo 203807 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B559295 : Blo 203807 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B231727 : Blo 203807 231727 := bstep (se 1 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 231727 = 347591) B347591
theorem B461339 : Blo 203807 461339 := bstep (se 1 (by rfl) ⟨346004, by rfl⟩ : syracuseStep 461339 = 692009) B692009
theorem B1182347 : Blo 203807 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B690875 : Blo 203807 690875 := bstep (se 1 (by rfl) ⟨518156, by rfl⟩ : syracuseStep 690875 = 1036313) B1036313
theorem B232519 : Blo 203807 232519 := bstep (se 1 (by rfl) ⟨174389, by rfl⟩ : syracuseStep 232519 = 348779) B348779
theorem B625897 : Blo 203807 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B298351 : Blo 203807 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B1052027 : Blo 203807 1052027 := bstep (se 1 (by rfl) ⟨789020, by rfl⟩ : syracuseStep 1052027 = 1578041) B1578041
theorem B331177 : Blo 203807 331177 := bstep (se 2 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 331177 = 248383) B248383
theorem B2526653 : Blo 203807 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B7475165 : Blo 203807 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B462815 : Blo 203807 462815 := bstep (se 1 (by rfl) ⟨347111, by rfl⟩ : syracuseStep 462815 = 694223) B694223
theorem B1184215 : Blo 203807 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B987727 : Blo 203807 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B692819 : Blo 203807 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B463463 : Blo 203807 463463 := bstep (se 1 (by rfl) ⟨347597, by rfl⟩ : syracuseStep 463463 = 695195) B695195
theorem B9573137 : Blo 203807 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2626451 : Blo 203807 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B693467 : Blo 203807 693467 := bstep (se 1 (by rfl) ⟨520100, by rfl⟩ : syracuseStep 693467 = 1040201) B1040201
theorem B464147 : Blo 203807 464147 := bstep (se 1 (by rfl) ⟨348110, by rfl⟩ : syracuseStep 464147 = 696221) B696221
theorem B464219 : Blo 203807 464219 := bstep (se 1 (by rfl) ⟨348164, by rfl⟩ : syracuseStep 464219 = 696329) B696329
theorem B791905 : Blo 203807 791905 := bstep (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) B593929
theorem B2364875 : Blo 203807 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B464777 : Blo 203807 464777 := bstep (se 2 (by rfl) ⟨174291, by rfl⟩ : syracuseStep 464777 = 348583) B348583
theorem B3971045 : Blo 203807 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B595961 : Blo 203807 595961 := bstep (se 2 (by rfl) ⟨223485, by rfl⟩ : syracuseStep 595961 = 446971) B446971
theorem B694331 : Blo 203807 694331 := bstep (se 1 (by rfl) ⟨520748, by rfl⟩ : syracuseStep 694331 = 1041497) B1041497
theorem B464993 : Blo 203807 464993 := bstep (se 2 (by rfl) ⟨174372, by rfl⟩ : syracuseStep 464993 = 348745) B348745
theorem B1317019 : Blo 203807 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B694601 : Blo 203807 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B2366333 : Blo 203807 2366333 := bstep (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) B887375
theorem B203823 : Blo 203807 203823 := bstep (se 1 (by rfl) ⟨152867, by rfl⟩ : syracuseStep 203823 = 305735) B305735
theorem B203847 : Blo 203807 203847 := bstep (se 1 (by rfl) ⟨152885, by rfl⟩ : syracuseStep 203847 = 305771) B305771
theorem B203999 : Blo 203807 203999 := bstep (se 1 (by rfl) ⟨152999, by rfl⟩ : syracuseStep 203999 = 305999) B305999
theorem B466343 : Blo 203807 466343 := bstep (se 1 (by rfl) ⟨349757, by rfl⟩ : syracuseStep 466343 = 699515) B699515
theorem B662995 : Blo 203807 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B204263 : Blo 203807 204263 := bstep (se 1 (by rfl) ⟨153197, by rfl⟩ : syracuseStep 204263 = 306395) B306395
theorem B204379 : Blo 203807 204379 := bstep (se 1 (by rfl) ⟨153284, by rfl⟩ : syracuseStep 204379 = 306569) B306569
theorem B466523 : Blo 203807 466523 := bstep (se 1 (by rfl) ⟨349892, by rfl⟩ : syracuseStep 466523 = 699785) B699785
theorem B695951 : Blo 203807 695951 := bstep (se 1 (by rfl) ⟨521963, by rfl⟩ : syracuseStep 695951 = 1043927) B1043927
theorem B204615 : Blo 203807 204615 := bstep (se 1 (by rfl) ⟨153461, by rfl⟩ : syracuseStep 204615 = 306923) B306923
theorem B466811 : Blo 203807 466811 := bstep (se 1 (by rfl) ⟨350108, by rfl⟩ : syracuseStep 466811 = 700217) B700217
theorem B204767 : Blo 203807 204767 := bstep (se 1 (by rfl) ⟨153575, by rfl⟩ : syracuseStep 204767 = 307151) B307151
theorem B205031 : Blo 203807 205031 := bstep (se 1 (by rfl) ⟨153773, by rfl⟩ : syracuseStep 205031 = 307547) B307547
theorem B467297 : Blo 203807 467297 := bstep (se 2 (by rfl) ⟨175236, by rfl⟩ : syracuseStep 467297 = 350473) B350473
theorem B205183 : Blo 203807 205183 := bstep (se 1 (by rfl) ⟨153887, by rfl⟩ : syracuseStep 205183 = 307775) B307775
theorem B467387 : Blo 203807 467387 := bstep (se 1 (by rfl) ⟨350540, by rfl⟩ : syracuseStep 467387 = 701081) B701081
theorem B205263 : Blo 203807 205263 := bstep (se 1 (by rfl) ⟨153947, by rfl⟩ : syracuseStep 205263 = 307895) B307895
theorem B205415 : Blo 203807 205415 := bstep (se 1 (by rfl) ⟨154061, by rfl⟩ : syracuseStep 205415 = 308123) B308123
theorem B697085 : Blo 203807 697085 := bstep (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) B261407
theorem B205679 : Blo 203807 205679 := bstep (se 1 (by rfl) ⟨154259, by rfl⟩ : syracuseStep 205679 = 308519) B308519
theorem B205735 : Blo 203807 205735 := bstep (se 1 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 205735 = 308603) B308603
theorem B205819 : Blo 203807 205819 := bstep (se 1 (by rfl) ⟨154364, by rfl⟩ : syracuseStep 205819 = 308729) B308729
theorem B205887 : Blo 203807 205887 := bstep (se 1 (by rfl) ⟨154415, by rfl⟩ : syracuseStep 205887 = 308831) B308831
theorem B206031 : Blo 203807 206031 := bstep (se 1 (by rfl) ⟨154523, by rfl⟩ : syracuseStep 206031 = 309047) B309047
theorem B664969 : Blo 203807 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B206235 : Blo 203807 206235 := bstep (se 1 (by rfl) ⟨154676, by rfl⟩ : syracuseStep 206235 = 309353) B309353
theorem B206447 : Blo 203807 206447 := bstep (se 1 (by rfl) ⟨154835, by rfl⟩ : syracuseStep 206447 = 309671) B309671
theorem B206503 : Blo 203807 206503 := bstep (se 1 (by rfl) ⟨154877, by rfl⟩ : syracuseStep 206503 = 309755) B309755
theorem B206587 : Blo 203807 206587 := bstep (se 1 (by rfl) ⟨154940, by rfl⟩ : syracuseStep 206587 = 309881) B309881
theorem B206623 : Blo 203807 206623 := bstep (se 1 (by rfl) ⟨154967, by rfl⟩ : syracuseStep 206623 = 309935) B309935
theorem B206655 : Blo 203807 206655 := bstep (se 1 (by rfl) ⟨154991, by rfl⟩ : syracuseStep 206655 = 309983) B309983
theorem B206831 : Blo 203807 206831 := bstep (se 1 (by rfl) ⟨155123, by rfl⟩ : syracuseStep 206831 = 310247) B310247
theorem B1321069 : Blo 203807 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B207003 : Blo 203807 207003 := bstep (se 1 (by rfl) ⟨155252, by rfl⟩ : syracuseStep 207003 = 310505) B310505
theorem B207039 : Blo 203807 207039 := bstep (se 1 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 207039 = 310559) B310559
theorem B207151 : Blo 203807 207151 := bstep (se 1 (by rfl) ⟨155363, by rfl⟩ : syracuseStep 207151 = 310727) B310727
theorem B12003713 : Blo 203807 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B207387 : Blo 203807 207387 := bstep (se 1 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 207387 = 311081) B311081
theorem B207391 : Blo 203807 207391 := bstep (se 1 (by rfl) ⟨155543, by rfl⟩ : syracuseStep 207391 = 311087) B311087
theorem B305801 : Blo 203807 305801 := bstep (se 2 (by rfl) ⟨114675, by rfl⟩ : syracuseStep 305801 = 229351) B229351
theorem B305975 : Blo 203807 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B699191 : Blo 203807 699191 := bstep (se 1 (by rfl) ⟨524393, by rfl⟩ : syracuseStep 699191 = 1048787) B1048787
theorem B306011 : Blo 203807 306011 := bstep (se 1 (by rfl) ⟨229508, by rfl⟩ : syracuseStep 306011 = 459017) B459017
theorem B207707 : Blo 203807 207707 := bstep (se 1 (by rfl) ⟨155780, by rfl⟩ : syracuseStep 207707 = 311561) B311561
theorem B207775 : Blo 203807 207775 := bstep (se 1 (by rfl) ⟨155831, by rfl⟩ : syracuseStep 207775 = 311663) B311663
theorem B306155 : Blo 203807 306155 := bstep (se 1 (by rfl) ⟨229616, by rfl⟩ : syracuseStep 306155 = 459233) B459233
theorem B207919 : Blo 203807 207919 := bstep (se 1 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 207919 = 311879) B311879
theorem B371783 : Blo 203807 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B306359 : Blo 203807 306359 := bstep (se 1 (by rfl) ⟨229769, by rfl⟩ : syracuseStep 306359 = 459539) B459539
theorem B306599 : Blo 203807 306599 := bstep (se 1 (by rfl) ⟨229949, by rfl⟩ : syracuseStep 306599 = 459899) B459899
theorem B470519 : Blo 203807 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B306683 : Blo 203807 306683 := bstep (se 1 (by rfl) ⟨230012, by rfl⟩ : syracuseStep 306683 = 460025) B460025
theorem B470591 : Blo 203807 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B699977 : Blo 203807 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B306779 : Blo 203807 306779 := bstep (se 1 (by rfl) ⟨230084, by rfl⟩ : syracuseStep 306779 = 460169) B460169
theorem B306863 : Blo 203807 306863 := bstep (se 1 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 306863 = 460295) B460295
theorem B306983 : Blo 203807 306983 := bstep (se 1 (by rfl) ⟨230237, by rfl⟩ : syracuseStep 306983 = 460475) B460475
theorem B307067 : Blo 203807 307067 := bstep (se 1 (by rfl) ⟨230300, by rfl⟩ : syracuseStep 307067 = 460601) B460601
theorem B929981 : Blo 203807 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B307487 : Blo 203807 307487 := bstep (se 1 (by rfl) ⟨230615, by rfl⟩ : syracuseStep 307487 = 461231) B461231
theorem B307511 : Blo 203807 307511 := bstep (se 1 (by rfl) ⟨230633, by rfl⟩ : syracuseStep 307511 = 461267) B461267
theorem B1782071 : Blo 203807 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B307583 : Blo 203807 307583 := bstep (se 1 (by rfl) ⟨230687, by rfl⟩ : syracuseStep 307583 = 461375) B461375
theorem B307655 : Blo 203807 307655 := bstep (se 1 (by rfl) ⟨230741, by rfl⟩ : syracuseStep 307655 = 461483) B461483
theorem B308009 : Blo 203807 308009 := bstep (se 2 (by rfl) ⟨115503, by rfl⟩ : syracuseStep 308009 = 231007) B231007
theorem B308015 : Blo 203807 308015 := bstep (se 1 (by rfl) ⟨231011, by rfl⟩ : syracuseStep 308015 = 462023) B462023
theorem B5485391 : Blo 203807 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B308135 : Blo 203807 308135 := bstep (se 1 (by rfl) ⟨231101, by rfl⟩ : syracuseStep 308135 = 462203) B462203
theorem B308219 : Blo 203807 308219 := bstep (se 1 (by rfl) ⟨231164, by rfl⟩ : syracuseStep 308219 = 462329) B462329
theorem B308279 : Blo 203807 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B308399 : Blo 203807 308399 := bstep (se 1 (by rfl) ⟨231299, by rfl⟩ : syracuseStep 308399 = 462599) B462599
theorem B3356225 : Blo 203807 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B308807 : Blo 203807 308807 := bstep (se 1 (by rfl) ⟨231605, by rfl⟩ : syracuseStep 308807 = 463211) B463211
theorem B1750693 : Blo 203807 1750693 := bstep (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) B328255
theorem B308903 : Blo 203807 308903 := bstep (se 1 (by rfl) ⟨231677, by rfl⟩ : syracuseStep 308903 = 463355) B463355
theorem B997067 : Blo 203807 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B308987 : Blo 203807 308987 := bstep (se 1 (by rfl) ⟨231740, by rfl⟩ : syracuseStep 308987 = 463481) B463481
theorem B734987 : Blo 203807 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B309023 : Blo 203807 309023 := bstep (se 1 (by rfl) ⟨231767, by rfl⟩ : syracuseStep 309023 = 463535) B463535
theorem B309071 : Blo 203807 309071 := bstep (se 1 (by rfl) ⟨231803, by rfl⟩ : syracuseStep 309071 = 463607) B463607
theorem B309191 : Blo 203807 309191 := bstep (se 1 (by rfl) ⟨231893, by rfl⟩ : syracuseStep 309191 = 463787) B463787
theorem B1063145 : Blo 203807 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B1161479 : Blo 203807 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B309545 : Blo 203807 309545 := bstep (se 2 (by rfl) ⟨116079, by rfl⟩ : syracuseStep 309545 = 232159) B232159
theorem B309551 : Blo 203807 309551 := bstep (se 1 (by rfl) ⟨232163, by rfl⟩ : syracuseStep 309551 = 464327) B464327
theorem B309791 : Blo 203807 309791 := bstep (se 1 (by rfl) ⟨232343, by rfl⟩ : syracuseStep 309791 = 464687) B464687
theorem B310175 : Blo 203807 310175 := bstep (se 1 (by rfl) ⟨232631, by rfl⟩ : syracuseStep 310175 = 465263) B465263
theorem B310223 : Blo 203807 310223 := bstep (se 1 (by rfl) ⟨232667, by rfl⟩ : syracuseStep 310223 = 465335) B465335
theorem B310313 : Blo 203807 310313 := bstep (se 2 (by rfl) ⟨116367, by rfl⟩ : syracuseStep 310313 = 232735) B232735
theorem B310319 : Blo 203807 310319 := bstep (se 1 (by rfl) ⟨232739, by rfl⟩ : syracuseStep 310319 = 465479) B465479
theorem B310343 : Blo 203807 310343 := bstep (se 1 (by rfl) ⟨232757, by rfl⟩ : syracuseStep 310343 = 465515) B465515
theorem B1326365 : Blo 203807 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B310607 : Blo 203807 310607 := bstep (se 1 (by rfl) ⟨232955, by rfl⟩ : syracuseStep 310607 = 465911) B465911
theorem B441767 : Blo 203807 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B310697 : Blo 203807 310697 := bstep (se 2 (by rfl) ⟨116511, by rfl⟩ : syracuseStep 310697 = 233023) B233023
theorem B310847 : Blo 203807 310847 := bstep (se 1 (by rfl) ⟨233135, by rfl⟩ : syracuseStep 310847 = 466271) B466271
theorem B1162937 : Blo 203807 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B638707 : Blo 203807 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B311111 : Blo 203807 311111 := bstep (se 1 (by rfl) ⟨233333, by rfl⟩ : syracuseStep 311111 = 466667) B466667
theorem B311195 : Blo 203807 311195 := bstep (se 1 (by rfl) ⟨233396, by rfl⟩ : syracuseStep 311195 = 466793) B466793
theorem B344351 : Blo 203807 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B442655 : Blo 203807 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B3490451 : Blo 203807 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B344999 : Blo 203807 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B345161 : Blo 203807 345161 := bstep (se 2 (by rfl) ⟨129435, by rfl⟩ : syracuseStep 345161 = 258871) B258871
theorem B279659 : Blo 203807 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B1590821 : Blo 203807 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B345721 : Blo 203807 345721 := bstep (se 2 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 345721 = 259291) B259291
theorem B247547 : Blo 203807 247547 := bstep (se 1 (by rfl) ⟨185660, by rfl⟩ : syracuseStep 247547 = 371321) B371321
theorem B1034045 : Blo 203807 1034045 := bstep (se 3 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 1034045 = 387767) B387767
theorem B20072285 : Blo 203807 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B1755067 : Blo 203807 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B414566423 : Blo 203807 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B346207 : Blo 203807 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B10242541 : Blo 203807 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B2837207 : Blo 203807 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2640599 : Blo 203807 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B1756403 : Blo 203807 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B347503 : Blo 203807 347503 := bstep (se 1 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 347503 = 521255) B521255
theorem B1199549 : Blo 203807 1199549 := bstep (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) B449831
theorem B347881 : Blo 203807 347881 := bstep (se 2 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 347881 = 260911) B260911
theorem B1036475 : Blo 203807 1036475 := bstep (se 1 (by rfl) ⟨777356, by rfl⟩ : syracuseStep 1036475 = 1554713) B1554713
theorem B348347 : Blo 203807 348347 := bstep (se 1 (by rfl) ⟨261260, by rfl⟩ : syracuseStep 348347 = 522521) B522521
theorem B1036961 : Blo 203807 1036961 := bstep (se 2 (by rfl) ⟨388860, by rfl⟩ : syracuseStep 1036961 = 777721) B777721
theorem B348907 : Blo 203807 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B1037123 : Blo 203807 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B1037933 : Blo 203807 1037933 := bstep (se 3 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 1037933 = 389225) B389225
theorem B349879 : Blo 203807 349879 := bstep (se 1 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 349879 = 524819) B524819
theorem B350183 : Blo 203807 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B350399 : Blo 203807 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B841927 : Blo 203807 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1104317 : Blo 203807 1104317 := bstep (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) B414119
theorem B1596125 : Blo 203807 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B6282035 : Blo 203807 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B581003 : Blo 203807 581003 := bstep (se 1 (by rfl) ⟨435752, by rfl⟩ : syracuseStep 581003 = 871505) B871505
theorem B1760777 : Blo 203807 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B4087741 : Blo 203807 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B1564919 : Blo 203807 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B876919 : Blo 203807 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B1729133 : Blo 203807 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B517225 : Blo 203807 517225 := bstep (se 2 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 517225 = 387919) B387919
theorem B779453 : Blo 203807 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B2975291 : Blo 203807 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B5596739 : Blo 203807 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B517985 : Blo 203807 517985 := bstep (se 2 (by rfl) ⟨194244, by rfl⟩ : syracuseStep 517985 = 388489) B388489
theorem B518359 : Blo 203807 518359 := bstep (se 1 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 518359 = 777539) B777539
theorem B518663 : Blo 203807 518663 := bstep (se 1 (by rfl) ⟨388997, by rfl⟩ : syracuseStep 518663 = 777995) B777995
theorem B518683 : Blo 203807 518683 := bstep (se 1 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 518683 = 778025) B778025
theorem B1764089 : Blo 203807 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B1240363 : Blo 203807 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B1764773 : Blo 203807 1764773 := bstep (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) B330895
theorem B880253 : Blo 203807 880253 := bstep (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) B330095
theorem B585593 : Blo 203807 585593 := bstep (se 2 (by rfl) ⟨219597, by rfl⟩ : syracuseStep 585593 = 439195) B439195
theorem B520091 : Blo 203807 520091 := bstep (se 1 (by rfl) ⟨390068, by rfl⟩ : syracuseStep 520091 = 780137) B780137
theorem B1961921 : Blo 203807 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B27324533 : Blo 203807 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1175741 : Blo 203807 1175741 := bstep (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) B440903
theorem B749821 : Blo 203807 749821 := bstep (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) B281183
theorem B880951 : Blo 203807 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B1765799 : Blo 203807 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B652283 : Blo 203807 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B521225 : Blo 203807 521225 := bstep (se 2 (by rfl) ⟨195459, by rfl⟩ : syracuseStep 521225 = 390919) B390919
theorem B390251 : Blo 203807 390251 := bstep (se 1 (by rfl) ⟨292688, by rfl⟩ : syracuseStep 390251 = 585377) B585377
theorem B26572049 : Blo 203807 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B587027 : Blo 203807 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B292187 : Blo 203807 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B1898579 : Blo 203807 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B8485013 : Blo 203807 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B588019 : Blo 203807 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B293161 : Blo 203807 293161 := bstep (se 2 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 293161 = 219871) B219871
theorem B20380517 : Blo 203807 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B1571719 : Blo 203807 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B2816977 : Blo 203807 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1768463 : Blo 203807 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B621697 : Blo 203807 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B654551 : Blo 203807 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B1309945 : Blo 203807 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B294311 : Blo 203807 294311 := bstep (se 1 (by rfl) ⟨220733, by rfl⟩ : syracuseStep 294311 = 441467) B441467
theorem B2653721 : Blo 203807 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B523867 : Blo 203807 523867 := bstep (se 1 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 523867 = 785801) B785801
theorem B524009 : Blo 203807 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B458567 : Blo 203807 458567 := bstep (se 1 (by rfl) ⟨343925, by rfl⟩ : syracuseStep 458567 = 687851) B687851
theorem B687959 : Blo 203807 687959 := bstep (se 1 (by rfl) ⟨515969, by rfl⟩ : syracuseStep 687959 = 1031939) B1031939
theorem B1572695 : Blo 203807 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B393083 : Blo 203807 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B655229 : Blo 203807 655229 := bstep (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) B245711
theorem B589693 : Blo 203807 589693 := bstep (se 3 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 589693 = 221135) B221135
theorem B262111 : Blo 203807 262111 := bstep (se 1 (by rfl) ⟨196583, by rfl⟩ : syracuseStep 262111 = 393167) B393167
theorem B3932225 : Blo 203807 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B229567 : Blo 203807 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B295103 : Blo 203807 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B262379 : Blo 203807 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B393599 : Blo 203807 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B459179 : Blo 203807 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B2326967 : Blo 203807 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B459359 : Blo 203807 459359 := bstep (se 1 (by rfl) ⟨344519, by rfl⟩ : syracuseStep 459359 = 689039) B689039
theorem B229999 : Blo 203807 229999 := bstep (se 1 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 229999 = 344999) B344999
theorem B230107 : Blo 203807 230107 := bstep (se 1 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 230107 = 345161) B345161
theorem B459719 : Blo 203807 459719 := bstep (se 1 (by rfl) ⟨344789, by rfl⟩ : syracuseStep 459719 = 689579) B689579
theorem B1180615 : Blo 203807 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B689363 : Blo 203807 689363 := bstep (se 1 (by rfl) ⟨517022, by rfl⟩ : syracuseStep 689363 = 1034045) B1034045
theorem B984287 : Blo 203807 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B460079 : Blo 203807 460079 := bstep (se 1 (by rfl) ⟨345059, by rfl⟩ : syracuseStep 460079 = 690119) B690119
theorem B591151 : Blo 203807 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B689633 : Blo 203807 689633 := bstep (se 2 (by rfl) ⟨258612, by rfl⟩ : syracuseStep 689633 = 517225) B517225
theorem B788231 : Blo 203807 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B460583 : Blo 203807 460583 := bstep (se 1 (by rfl) ⟨345437, by rfl⟩ : syracuseStep 460583 = 690875) B690875
theorem B886625 : Blo 203807 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B1050569 : Blo 203807 1050569 := bstep (se 2 (by rfl) ⟨393963, by rfl⟩ : syracuseStep 1050569 = 787927) B787927
theorem B1312793 : Blo 203807 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B657433 : Blo 203807 657433 := bstep (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) B493075
theorem B460961 : Blo 203807 460961 := bstep (se 2 (by rfl) ⟨172860, by rfl⟩ : syracuseStep 460961 = 345721) B345721
theorem B4983443 : Blo 203807 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B690983 : Blo 203807 690983 := bstep (se 1 (by rfl) ⟨518237, by rfl⟩ : syracuseStep 690983 = 1036475) B1036475
theorem B232231 : Blo 203807 232231 := bstep (se 1 (by rfl) ⟨174173, by rfl⟩ : syracuseStep 232231 = 348347) B348347
theorem B461609 : Blo 203807 461609 := bstep (se 2 (by rfl) ⟨173103, by rfl⟩ : syracuseStep 461609 = 346207) B346207
theorem B691145 : Blo 203807 691145 := bstep (se 2 (by rfl) ⟨259179, by rfl⟩ : syracuseStep 691145 = 518359) B518359
theorem B461879 : Blo 203807 461879 := bstep (se 1 (by rfl) ⟨346409, by rfl⟩ : syracuseStep 461879 = 692819) B692819
theorem B691307 : Blo 203807 691307 := bstep (se 1 (by rfl) ⟨518480, by rfl⟩ : syracuseStep 691307 = 1036961) B1036961
theorem B691415 : Blo 203807 691415 := bstep (se 1 (by rfl) ⟨518561, by rfl⟩ : syracuseStep 691415 = 1037123) B1037123
theorem B691577 : Blo 203807 691577 := bstep (se 2 (by rfl) ⟨259341, by rfl⟩ : syracuseStep 691577 = 518683) B518683
theorem B462311 : Blo 203807 462311 := bstep (se 1 (by rfl) ⟨346733, by rfl⟩ : syracuseStep 462311 = 693467) B693467
theorem B1576583 : Blo 203807 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B691955 : Blo 203807 691955 := bstep (se 1 (by rfl) ⟨518966, by rfl⟩ : syracuseStep 691955 = 1037933) B1037933
theorem B233455 : Blo 203807 233455 := bstep (se 1 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 233455 = 350183) B350183
theorem B397307 : Blo 203807 397307 := bstep (se 1 (by rfl) ⟨297980, by rfl⟩ : syracuseStep 397307 = 595961) B595961
theorem B462887 : Blo 203807 462887 := bstep (se 1 (by rfl) ⟨347165, by rfl⟩ : syracuseStep 462887 = 694331) B694331
theorem B233599 : Blo 203807 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B463067 : Blo 203807 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B463337 : Blo 203807 463337 := bstep (se 2 (by rfl) ⟨173751, by rfl⟩ : syracuseStep 463337 = 347503) B347503
theorem B397801 : Blo 203807 397801 := bstep (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) B298351
theorem B2658845 : Blo 203807 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B1577555 : Blo 203807 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B660125 : Blo 203807 660125 := bstep (se 3 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 660125 = 247547) B247547
theorem B463841 : Blo 203807 463841 := bstep (se 2 (by rfl) ⟨173940, by rfl⟩ : syracuseStep 463841 = 347881) B347881
theorem B463967 : Blo 203807 463967 := bstep (se 1 (by rfl) ⟨347975, by rfl⟩ : syracuseStep 463967 = 695951) B695951
theorem B1152755 : Blo 203807 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B464723 : Blo 203807 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B1578953 : Blo 203807 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B1316969 : Blo 203807 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B465209 : Blo 203807 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B8002475 : Blo 203807 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B203867 : Blo 203807 203867 := bstep (se 1 (by rfl) ⟨152900, by rfl⟩ : syracuseStep 203867 = 305801) B305801
theorem B1055873 : Blo 203807 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B203983 : Blo 203807 203983 := bstep (se 1 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 203983 = 305975) B305975
theorem B466127 : Blo 203807 466127 := bstep (se 1 (by rfl) ⟨349595, by rfl⟩ : syracuseStep 466127 = 699191) B699191
theorem B204007 : Blo 203807 204007 := bstep (se 1 (by rfl) ⟨153005, by rfl⟩ : syracuseStep 204007 = 306011) B306011
theorem B204103 : Blo 203807 204103 := bstep (se 1 (by rfl) ⟨153077, by rfl⟩ : syracuseStep 204103 = 306155) B306155
theorem B204239 : Blo 203807 204239 := bstep (se 1 (by rfl) ⟨153179, by rfl⟩ : syracuseStep 204239 = 306359) B306359
theorem B2334257 : Blo 203807 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B466505 : Blo 203807 466505 := bstep (se 2 (by rfl) ⟨174939, by rfl⟩ : syracuseStep 466505 = 349879) B349879
theorem B204399 : Blo 203807 204399 := bstep (se 1 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 204399 = 306599) B306599
theorem B204455 : Blo 203807 204455 := bstep (se 1 (by rfl) ⟨153341, by rfl⟩ : syracuseStep 204455 = 306683) B306683
theorem B466651 : Blo 203807 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B204519 : Blo 203807 204519 := bstep (se 1 (by rfl) ⟨153389, by rfl⟩ : syracuseStep 204519 = 306779) B306779
theorem B204575 : Blo 203807 204575 := bstep (se 1 (by rfl) ⟨153431, by rfl⟩ : syracuseStep 204575 = 306863) B306863
theorem B204655 : Blo 203807 204655 := bstep (se 1 (by rfl) ⟨153491, by rfl⟩ : syracuseStep 204655 = 306983) B306983
theorem B204711 : Blo 203807 204711 := bstep (se 1 (by rfl) ⟨153533, by rfl⟩ : syracuseStep 204711 = 307067) B307067
theorem B204991 : Blo 203807 204991 := bstep (se 1 (by rfl) ⟨153743, by rfl⟩ : syracuseStep 204991 = 307487) B307487
theorem B205007 : Blo 203807 205007 := bstep (se 1 (by rfl) ⟨153755, by rfl⟩ : syracuseStep 205007 = 307511) B307511
theorem B1188047 : Blo 203807 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B205055 : Blo 203807 205055 := bstep (se 1 (by rfl) ⟨153791, by rfl⟩ : syracuseStep 205055 = 307583) B307583
theorem B1122569 : Blo 203807 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B205103 : Blo 203807 205103 := bstep (se 1 (by rfl) ⟨153827, by rfl⟩ : syracuseStep 205103 = 307655) B307655
theorem B205339 : Blo 203807 205339 := bstep (se 1 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 205339 = 308009) B308009
theorem B205343 : Blo 203807 205343 := bstep (se 1 (by rfl) ⟨154007, by rfl⟩ : syracuseStep 205343 = 308015) B308015
theorem B205423 : Blo 203807 205423 := bstep (se 1 (by rfl) ⟨154067, by rfl⟩ : syracuseStep 205423 = 308135) B308135
theorem B205479 : Blo 203807 205479 := bstep (se 1 (by rfl) ⟨154109, by rfl⟩ : syracuseStep 205479 = 308219) B308219
theorem B434855 : Blo 203807 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B205519 : Blo 203807 205519 := bstep (se 1 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 205519 = 308279) B308279
theorem B205599 : Blo 203807 205599 := bstep (se 1 (by rfl) ⟨154199, by rfl⟩ : syracuseStep 205599 = 308399) B308399
theorem B2237483 : Blo 203807 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B205871 : Blo 203807 205871 := bstep (se 1 (by rfl) ⟨154403, by rfl⟩ : syracuseStep 205871 = 308807) B308807
theorem B205935 : Blo 203807 205935 := bstep (se 1 (by rfl) ⟨154451, by rfl⟩ : syracuseStep 205935 = 308903) B308903
theorem B205991 : Blo 203807 205991 := bstep (se 1 (by rfl) ⟨154493, by rfl⟩ : syracuseStep 205991 = 308987) B308987
theorem B206015 : Blo 203807 206015 := bstep (se 1 (by rfl) ⟨154511, by rfl⟩ : syracuseStep 206015 = 309023) B309023
theorem B206047 : Blo 203807 206047 := bstep (se 1 (by rfl) ⟨154535, by rfl⟩ : syracuseStep 206047 = 309071) B309071
theorem B206127 : Blo 203807 206127 := bstep (se 1 (by rfl) ⟨154595, by rfl⟩ : syracuseStep 206127 = 309191) B309191
theorem B828929 : Blo 203807 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B206363 : Blo 203807 206363 := bstep (se 1 (by rfl) ⟨154772, by rfl⟩ : syracuseStep 206363 = 309545) B309545
theorem B206367 : Blo 203807 206367 := bstep (se 1 (by rfl) ⟨154775, by rfl⟩ : syracuseStep 206367 = 309551) B309551
theorem B1746593 : Blo 203807 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B206527 : Blo 203807 206527 := bstep (se 1 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 206527 = 309791) B309791
theorem B206783 : Blo 203807 206783 := bstep (se 1 (by rfl) ⟨155087, by rfl⟩ : syracuseStep 206783 = 310175) B310175
theorem B206815 : Blo 203807 206815 := bstep (se 1 (by rfl) ⟨155111, by rfl⟩ : syracuseStep 206815 = 310223) B310223
theorem B206875 : Blo 203807 206875 := bstep (se 1 (by rfl) ⟨155156, by rfl⟩ : syracuseStep 206875 = 310313) B310313
theorem B206879 : Blo 203807 206879 := bstep (se 1 (by rfl) ⟨155159, by rfl⟩ : syracuseStep 206879 = 310319) B310319
theorem B206895 : Blo 203807 206895 := bstep (se 1 (by rfl) ⟨155171, by rfl⟩ : syracuseStep 206895 = 310343) B310343
theorem B698489 : Blo 203807 698489 := bstep (se 2 (by rfl) ⟨261933, by rfl⟩ : syracuseStep 698489 = 523867) B523867
theorem B436367 : Blo 203807 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B207071 : Blo 203807 207071 := bstep (se 1 (by rfl) ⟨155303, by rfl⟩ : syracuseStep 207071 = 310607) B310607
theorem B207131 : Blo 203807 207131 := bstep (se 1 (by rfl) ⟨155348, by rfl⟩ : syracuseStep 207131 = 310697) B310697
theorem B1747277 : Blo 203807 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B207231 : Blo 203807 207231 := bstep (se 1 (by rfl) ⟨155423, by rfl⟩ : syracuseStep 207231 = 310847) B310847
theorem B305711 : Blo 203807 305711 := bstep (se 1 (by rfl) ⟨229283, by rfl⟩ : syracuseStep 305711 = 458567) B458567
theorem B207407 : Blo 203807 207407 := bstep (se 1 (by rfl) ⟨155555, by rfl⟩ : syracuseStep 207407 = 311111) B311111
theorem B5450321 : Blo 203807 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B207463 : Blo 203807 207463 := bstep (se 1 (by rfl) ⟨155597, by rfl⟩ : syracuseStep 207463 = 311195) B311195
theorem B306143 : Blo 203807 306143 := bstep (se 1 (by rfl) ⟨229607, by rfl⟩ : syracuseStep 306143 = 459215) B459215
theorem B6007931 : Blo 203807 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1748303 : Blo 203807 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B306587 : Blo 203807 306587 := bstep (se 1 (by rfl) ⟨229940, by rfl⟩ : syracuseStep 306587 = 459881) B459881
theorem B1060547 : Blo 203807 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B307007 : Blo 203807 307007 := bstep (se 1 (by rfl) ⟨230255, by rfl⟩ : syracuseStep 307007 = 460511) B460511
theorem B13381523 : Blo 203807 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1552283 : Blo 203807 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B307193 : Blo 203807 307193 := bstep (se 2 (by rfl) ⟨115197, by rfl⟩ : syracuseStep 307193 = 230395) B230395
theorem B276377615 : Blo 203807 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B3911759 : Blo 203807 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B372863 : Blo 203807 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B307433 : Blo 203807 307433 := bstep (se 2 (by rfl) ⟨115287, by rfl⟩ : syracuseStep 307433 = 230575) B230575
theorem B307559 : Blo 203807 307559 := bstep (se 1 (by rfl) ⟨230669, by rfl⟩ : syracuseStep 307559 = 461339) B461339
theorem B308105 : Blo 203807 308105 := bstep (se 2 (by rfl) ⟨115539, by rfl⟩ : syracuseStep 308105 = 231079) B231079
theorem B439177 : Blo 203807 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B701351 : Blo 203807 701351 := bstep (se 1 (by rfl) ⟨526013, by rfl⟩ : syracuseStep 701351 = 1052027) B1052027
theorem B1684435 : Blo 203807 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2340089 : Blo 203807 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B308489 : Blo 203807 308489 := bstep (se 2 (by rfl) ⟨115683, by rfl⟩ : syracuseStep 308489 = 231367) B231367
theorem B308543 : Blo 203807 308543 := bstep (se 1 (by rfl) ⟨231407, by rfl⟩ : syracuseStep 308543 = 462815) B462815
theorem B308969 : Blo 203807 308969 := bstep (se 2 (by rfl) ⟨115863, by rfl⟩ : syracuseStep 308969 = 231727) B231727
theorem B308975 : Blo 203807 308975 := bstep (se 1 (by rfl) ⟨231731, by rfl⟩ : syracuseStep 308975 = 463463) B463463
theorem B1750967 : Blo 203807 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B309431 : Blo 203807 309431 := bstep (se 1 (by rfl) ⟨232073, by rfl⟩ : syracuseStep 309431 = 464147) B464147
theorem B309479 : Blo 203807 309479 := bstep (se 1 (by rfl) ⟨232109, by rfl⟩ : syracuseStep 309479 = 464219) B464219
theorem B309851 : Blo 203807 309851 := bstep (se 1 (by rfl) ⟨232388, by rfl⟩ : syracuseStep 309851 = 464777) B464777
theorem B277225 : Blo 203807 277225 := bstep (se 2 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 277225 = 207919) B207919
theorem B309995 : Blo 203807 309995 := bstep (se 1 (by rfl) ⟨232496, by rfl⟩ : syracuseStep 309995 = 464993) B464993
theorem B310025 : Blo 203807 310025 := bstep (se 2 (by rfl) ⟨116259, by rfl⟩ : syracuseStep 310025 = 232519) B232519
theorem B736211 : Blo 203807 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B1752029 : Blo 203807 1752029 := bstep (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) B657011
theorem B834529 : Blo 203807 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B1653817 : Blo 203807 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B1064083 : Blo 203807 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B441569 : Blo 203807 441569 := bstep (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) B331177
theorem B310895 : Blo 203807 310895 := bstep (se 1 (by rfl) ⟨233171, by rfl⟩ : syracuseStep 310895 = 466343) B466343
theorem B311015 : Blo 203807 311015 := bstep (se 1 (by rfl) ⟨233261, by rfl⟩ : syracuseStep 311015 = 466523) B466523
theorem B311207 : Blo 203807 311207 := bstep (se 1 (by rfl) ⟨233405, by rfl⟩ : syracuseStep 311207 = 466811) B466811
theorem B311531 : Blo 203807 311531 := bstep (se 1 (by rfl) ⟨233648, by rfl⟩ : syracuseStep 311531 = 467297) B467297
theorem B311591 : Blo 203807 311591 := bstep (se 1 (by rfl) ⟨233693, by rfl⟩ : syracuseStep 311591 = 467387) B467387
theorem B999761 : Blo 203807 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B1983527 : Blo 203807 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B345323 : Blo 203807 345323 := bstep (se 1 (by rfl) ⟨258992, by rfl⟩ : syracuseStep 345323 = 517985) B517985
theorem B345775 : Blo 203807 345775 := bstep (se 1 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 345775 = 518663) B518663
theorem B247855 : Blo 203807 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B313679 : Blo 203807 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B313727 : Blo 203807 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B346727 : Blo 203807 346727 := bstep (se 1 (by rfl) ⟨260045, by rfl⟩ : syracuseStep 346727 = 520091) B520091
theorem B1756025 : Blo 203807 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B3656927 : Blo 203807 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B347483 : Blo 203807 347483 := bstep (se 1 (by rfl) ⟨260612, by rfl⟩ : syracuseStep 347483 = 521225) B521225
theorem B17714699 : Blo 203807 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B3198797 : Blo 203807 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B3755969 : Blo 203807 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B1265719 : Blo 203807 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B5656675 : Blo 203807 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B708763 : Blo 203807 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B774319 : Blo 203807 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B13587011 : Blo 203807 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B775291 : Blo 203807 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B349339 : Blo 203807 349339 := bstep (se 1 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 349339 = 524009) B524009
theorem B349481 : Blo 203807 349481 := bstep (se 2 (by rfl) ⟨131055, by rfl⟩ : syracuseStep 349481 = 262111) B262111
theorem B6313459 : Blo 203807 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B1169225 : Blo 203807 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B350075 : Blo 203807 350075 := bstep (se 1 (by rfl) ⟨262556, by rfl⟩ : syracuseStep 350075 = 525113) B525113
theorem B350345 : Blo 203807 350345 := bstep (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) B262759
theorem B3562055 : Blo 203807 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B1760399 : Blo 203807 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1170935 : Blo 203807 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B1761425 : Blo 203807 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B745757 : Blo 203807 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B6382091 : Blo 203807 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B13656721 : Blo 203807 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1565405 : Blo 203807 1565405 := bstep (se 3 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 1565405 = 587027) B587027
theorem B779165 : Blo 203807 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B2647363 : Blo 203807 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B4188023 : Blo 203807 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B387335 : Blo 203807 387335 := bstep (se 1 (by rfl) ⟨290501, by rfl⟩ : syracuseStep 387335 = 581003) B581003
theorem B1173851 : Blo 203807 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B1043279 : Blo 203807 1043279 := bstep (se 1 (by rfl) ⟨782459, by rfl⟩ : syracuseStep 1043279 = 1564919) B1564919
theorem B1174601 : Blo 203807 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B519635 : Blo 203807 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B3731159 : Blo 203807 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B1176059 : Blo 203807 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B7565885 : Blo 203807 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1176515 : Blo 203807 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B586835 : Blo 203807 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B390395 : Blo 203807 390395 := bstep (se 1 (by rfl) ⟨292796, by rfl⟩ : syracuseStep 390395 = 585593) B585593
theorem B1307947 : Blo 203807 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B18216355 : Blo 203807 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B619987 : Blo 203807 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B783827 : Blo 203807 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B1177199 : Blo 203807 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B784025 : Blo 203807 784025 := bstep (se 2 (by rfl) ⟨294009, by rfl⟩ : syracuseStep 784025 = 588019) B588019
theorem B390881 : Blo 203807 390881 := bstep (se 2 (by rfl) ⟨146580, by rfl⟩ : syracuseStep 390881 = 293161) B293161
theorem B260167 : Blo 203807 260167 := bstep (se 1 (by rfl) ⟨195125, by rfl⟩ : syracuseStep 260167 = 390251) B390251
theorem B784829 : Blo 203807 784829 := bstep (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) B294311
theorem B489991 : Blo 203807 489991 := bstep (se 1 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 489991 = 734987) B734987
theorem B2095625 : Blo 203807 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B883993 : Blo 203807 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B1178975 : Blo 203807 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B884243 : Blo 203807 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B294511 : Blo 203807 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B851609 : Blo 203807 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B1769147 : Blo 203807 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B786257 : Blo 203807 786257 := bstep (se 2 (by rfl) ⟨294846, by rfl⟩ : syracuseStep 786257 = 589693) B589693
theorem B458639 : Blo 203807 458639 := bstep (se 1 (by rfl) ⟨343979, by rfl⟩ : syracuseStep 458639 = 687959) B687959
theorem B1048463 : Blo 203807 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B262055 : Blo 203807 262055 := bstep (se 1 (by rfl) ⟨196541, by rfl⟩ : syracuseStep 262055 = 393083) B393083
theorem B2621483 : Blo 203807 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B786941 : Blo 203807 786941 := bstep (se 3 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 786941 = 295103) B295103
theorem B459575 : Blo 203807 459575 := bstep (se 1 (by rfl) ⟨344681, by rfl⟩ : syracuseStep 459575 = 689363) B689363
theorem B656191 : Blo 203807 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B230215 : Blo 203807 230215 := bstep (se 1 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 230215 = 345323) B345323
theorem B459755 : Blo 203807 459755 := bstep (se 1 (by rfl) ⟨344816, by rfl⟩ : syracuseStep 459755 = 689633) B689633
theorem B1049597 : Blo 203807 1049597 := bstep (se 3 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 1049597 = 393599) B393599
theorem B525487 : Blo 203807 525487 := bstep (se 1 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 525487 = 788231) B788231
theorem B591083 : Blo 203807 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B1574153 : Blo 203807 1574153 := bstep (se 2 (by rfl) ⟨590307, by rfl⟩ : syracuseStep 1574153 = 1180615) B1180615
theorem B788201 : Blo 203807 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B231151 : Blo 203807 231151 := bstep (se 1 (by rfl) ⟨173363, by rfl⟩ : syracuseStep 231151 = 346727) B346727
theorem B460655 : Blo 203807 460655 := bstep (se 1 (by rfl) ⟨345491, by rfl⟩ : syracuseStep 460655 = 690983) B690983
theorem B460763 : Blo 203807 460763 := bstep (se 1 (by rfl) ⟨345572, by rfl⟩ : syracuseStep 460763 = 691145) B691145
theorem B460871 : Blo 203807 460871 := bstep (se 1 (by rfl) ⟨345653, by rfl⟩ : syracuseStep 460871 = 691307) B691307
theorem B460943 : Blo 203807 460943 := bstep (se 1 (by rfl) ⟨345707, by rfl⟩ : syracuseStep 460943 = 691415) B691415
theorem B231655 : Blo 203807 231655 := bstep (se 1 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 231655 = 347483) B347483
theorem B461033 : Blo 203807 461033 := bstep (se 2 (by rfl) ⟨172887, by rfl⟩ : syracuseStep 461033 = 345775) B345775
theorem B461051 : Blo 203807 461051 := bstep (se 1 (by rfl) ⟨345788, by rfl⟩ : syracuseStep 461051 = 691577) B691577
theorem B1051055 : Blo 203807 1051055 := bstep (se 1 (by rfl) ⟨788291, by rfl⟩ : syracuseStep 1051055 = 1576583) B1576583
theorem B461303 : Blo 203807 461303 := bstep (se 1 (by rfl) ⟨345977, by rfl⟩ : syracuseStep 461303 = 691955) B691955
theorem B2132531 : Blo 203807 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B330473 : Blo 203807 330473 := bstep (se 2 (by rfl) ⟨123927, by rfl⟩ : syracuseStep 330473 = 247855) B247855
theorem B1772563 : Blo 203807 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1051703 : Blo 203807 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B232987 : Blo 203807 232987 := bstep (se 1 (by rfl) ⟨174740, by rfl⟩ : syracuseStep 232987 = 349481) B349481
theorem B1478533 : Blo 203807 1478533 := bstep (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) B277225
theorem B233383 : Blo 203807 233383 := bstep (se 1 (by rfl) ⟨175037, by rfl⟩ : syracuseStep 233383 = 350075) B350075
theorem B1052635 : Blo 203807 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B233563 : Blo 203807 233563 := bstep (se 1 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 233563 = 350345) B350345
theorem B7542233 : Blo 203807 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B792031 : Blo 203807 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B497171 : Blo 203807 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B530401 : Blo 203807 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B2792015 : Blo 203807 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B465659 : Blo 203807 465659 := bstep (se 1 (by rfl) ⟨349244, by rfl⟩ : syracuseStep 465659 = 698489) B698489
theorem B465785 : Blo 203807 465785 := bstep (se 2 (by rfl) ⟨174669, by rfl⟩ : syracuseStep 465785 = 349339) B349339
theorem B203807 : Blo 203807 203807 := bstep (se 1 (by rfl) ⟨152855, by rfl⟩ : syracuseStep 203807 = 305711) B305711
theorem B1743929 : Blo 203807 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B24288473 : Blo 203807 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B695519 : Blo 203807 695519 := bstep (se 1 (by rfl) ⟨521639, by rfl⟩ : syracuseStep 695519 = 1043279) B1043279
theorem B826649 : Blo 203807 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B204095 : Blo 203807 204095 := bstep (se 1 (by rfl) ⟨153071, by rfl⟩ : syracuseStep 204095 = 306143) B306143
theorem B4005287 : Blo 203807 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B204391 : Blo 203807 204391 := bstep (se 1 (by rfl) ⟨153293, by rfl⟩ : syracuseStep 204391 = 306587) B306587
theorem B204671 : Blo 203807 204671 := bstep (se 1 (by rfl) ⟨153503, by rfl⟩ : syracuseStep 204671 = 307007) B307007
theorem B8921015 : Blo 203807 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B204795 : Blo 203807 204795 := bstep (se 1 (by rfl) ⟨153596, by rfl⟩ : syracuseStep 204795 = 307193) B307193
theorem B204955 : Blo 203807 204955 := bstep (se 1 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 204955 = 307433) B307433
theorem B205039 : Blo 203807 205039 := bstep (se 1 (by rfl) ⟨153779, by rfl⟩ : syracuseStep 205039 = 307559) B307559
theorem B205403 : Blo 203807 205403 := bstep (se 1 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 205403 = 308105) B308105
theorem B467567 : Blo 203807 467567 := bstep (se 1 (by rfl) ⟨350675, by rfl⟩ : syracuseStep 467567 = 701351) B701351
theorem B205659 : Blo 203807 205659 := bstep (se 1 (by rfl) ⟨154244, by rfl⟩ : syracuseStep 205659 = 308489) B308489
theorem B205695 : Blo 203807 205695 := bstep (se 1 (by rfl) ⟨154271, by rfl⟩ : syracuseStep 205695 = 308543) B308543
theorem B205979 : Blo 203807 205979 := bstep (se 1 (by rfl) ⟨154484, by rfl⟩ : syracuseStep 205979 = 308969) B308969
theorem B205983 : Blo 203807 205983 := bstep (se 1 (by rfl) ⟨154487, by rfl⟩ : syracuseStep 205983 = 308975) B308975
theorem B2205089 : Blo 203807 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B206287 : Blo 203807 206287 := bstep (se 1 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 206287 = 309431) B309431
theorem B206319 : Blo 203807 206319 := bstep (se 1 (by rfl) ⟨154739, by rfl⟩ : syracuseStep 206319 = 309479) B309479
theorem B1418777 : Blo 203807 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B206567 : Blo 203807 206567 := bstep (se 1 (by rfl) ⟨154925, by rfl⟩ : syracuseStep 206567 = 309851) B309851
theorem B206663 : Blo 203807 206663 := bstep (se 1 (by rfl) ⟨154997, by rfl⟩ : syracuseStep 206663 = 309995) B309995
theorem B206683 : Blo 203807 206683 := bstep (se 1 (by rfl) ⟨155012, by rfl⟩ : syracuseStep 206683 = 310025) B310025
theorem B2828125 : Blo 203807 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B207263 : Blo 203807 207263 := bstep (se 1 (by rfl) ⟨155447, by rfl⟩ : syracuseStep 207263 = 310895) B310895
theorem B567739 : Blo 203807 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B698813 : Blo 203807 698813 := bstep (se 3 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 698813 = 262055) B262055
theorem B207343 : Blo 203807 207343 := bstep (se 1 (by rfl) ⟨155507, by rfl⟩ : syracuseStep 207343 = 311015) B311015
theorem B305759 : Blo 203807 305759 := bstep (se 1 (by rfl) ⟨229319, by rfl⟩ : syracuseStep 305759 = 458639) B458639
theorem B698975 : Blo 203807 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B207471 : Blo 203807 207471 := bstep (se 1 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 207471 = 311207) B311207
theorem B1059485 : Blo 203807 1059485 := bstep (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) B397307
theorem B207687 : Blo 203807 207687 := bstep (se 1 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 207687 = 311531) B311531
theorem B207727 : Blo 203807 207727 := bstep (se 1 (by rfl) ⟨155795, by rfl⟩ : syracuseStep 207727 = 311591) B311591
theorem B306089 : Blo 203807 306089 := bstep (se 2 (by rfl) ⟨114783, by rfl⟩ : syracuseStep 306089 = 229567) B229567
theorem B306119 : Blo 203807 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B1551311 : Blo 203807 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B994301 : Blo 203807 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B306239 : Blo 203807 306239 := bstep (se 1 (by rfl) ⟨229679, by rfl⟩ : syracuseStep 306239 = 459359) B459359
theorem B699677 : Blo 203807 699677 := bstep (se 3 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 699677 = 262379) B262379
theorem B306479 : Blo 203807 306479 := bstep (se 1 (by rfl) ⟨229859, by rfl⟩ : syracuseStep 306479 = 459719) B459719
theorem B1322351 : Blo 203807 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B306665 : Blo 203807 306665 := bstep (se 2 (by rfl) ⟨114999, by rfl⟩ : syracuseStep 306665 = 229999) B229999
theorem B306719 : Blo 203807 306719 := bstep (se 1 (by rfl) ⟨230039, by rfl⟩ : syracuseStep 306719 = 460079) B460079
theorem B2666029 : Blo 203807 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B306809 : Blo 203807 306809 := bstep (se 2 (by rfl) ⟨115053, by rfl⟩ : syracuseStep 306809 = 230107) B230107
theorem B307055 : Blo 203807 307055 := bstep (se 1 (by rfl) ⟨230291, by rfl⟩ : syracuseStep 307055 = 460583) B460583
theorem B700379 : Blo 203807 700379 := bstep (se 1 (by rfl) ⟨525284, by rfl⟩ : syracuseStep 700379 = 1050569) B1050569
theorem B17018909 : Blo 203807 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B307307 : Blo 203807 307307 := bstep (se 1 (by rfl) ⟨230480, by rfl⟩ : syracuseStep 307307 = 460961) B460961
theorem B3322295 : Blo 203807 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B307739 : Blo 203807 307739 := bstep (se 1 (by rfl) ⟨230804, by rfl⟩ : syracuseStep 307739 = 461609) B461609
theorem B307919 : Blo 203807 307919 := bstep (se 1 (by rfl) ⟨230939, by rfl⟩ : syracuseStep 307919 = 461879) B461879
theorem B2437951 : Blo 203807 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B308207 : Blo 203807 308207 := bstep (se 1 (by rfl) ⟨231155, by rfl⟩ : syracuseStep 308207 = 462311) B462311
theorem B11809799 : Blo 203807 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B2503979 : Blo 203807 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B308591 : Blo 203807 308591 := bstep (se 1 (by rfl) ⟨231443, by rfl⟩ : syracuseStep 308591 = 462887) B462887
theorem B308711 : Blo 203807 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B308891 : Blo 203807 308891 := bstep (se 1 (by rfl) ⟨231668, by rfl⟩ : syracuseStep 308891 = 463337) B463337
theorem B9058007 : Blo 203807 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B440083 : Blo 203807 440083 := bstep (se 1 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 440083 = 660125) B660125
theorem B309227 : Blo 203807 309227 := bstep (se 1 (by rfl) ⟨231920, by rfl⟩ : syracuseStep 309227 = 463841) B463841
theorem B309311 : Blo 203807 309311 := bstep (se 1 (by rfl) ⟨231983, by rfl⟩ : syracuseStep 309311 = 463967) B463967
theorem B309641 : Blo 203807 309641 := bstep (se 2 (by rfl) ⟨116115, by rfl⟩ : syracuseStep 309641 = 232231) B232231
theorem B768503 : Blo 203807 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B309815 : Blo 203807 309815 := bstep (se 1 (by rfl) ⟨232361, by rfl⟩ : syracuseStep 309815 = 464723) B464723
theorem B310139 : Blo 203807 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B2374703 : Blo 203807 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B310751 : Blo 203807 310751 := bstep (se 1 (by rfl) ⟨233063, by rfl⟩ : syracuseStep 310751 = 466127) B466127
theorem B1556171 : Blo 203807 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B311003 : Blo 203807 311003 := bstep (se 1 (by rfl) ⟨233252, by rfl⟩ : syracuseStep 311003 = 466505) B466505
theorem B311273 : Blo 203807 311273 := bstep (se 2 (by rfl) ⟨116727, by rfl⟩ : syracuseStep 311273 = 233455) B233455
theorem B1687625 : Blo 203807 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B311465 : Blo 203807 311465 := bstep (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) B233599
theorem B1032425 : Blo 203807 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B1163645 : Blo 203807 1163645 := bstep (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) B436367
theorem B1491655 : Blo 203807 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B836477 : Blo 203807 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B836605 : Blo 203807 836605 := bstep (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) B313727
theorem B1164395 : Blo 203807 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B2245913 : Blo 203807 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1033721 : Blo 203807 1033721 := bstep (se 2 (by rfl) ⟨387645, by rfl⟩ : syracuseStep 1033721 = 775291) B775291
theorem B1164851 : Blo 203807 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1165535 : Blo 203807 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B346423 : Blo 203807 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B1034855 : Blo 203807 1034855 := bstep (se 1 (by rfl) ⟨776141, by rfl⟩ : syracuseStep 1034855 = 1552283) B1552283
theorem B2607839 : Blo 203807 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B346889 : Blo 203807 346889 := bstep (se 2 (by rfl) ⟨130083, by rfl⟩ : syracuseStep 346889 = 260167) B260167
theorem B1560059 : Blo 203807 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B1167311 : Blo 203807 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B1397083 : Blo 203807 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1168019 : Blo 203807 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B18208961 : Blo 203807 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B875195 : Blo 203807 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B3529817 : Blo 203807 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B1170683 : Blo 203807 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B876577 : Blo 203807 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B779483 : Blo 203807 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B877979 : Blo 203807 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B5334983 : Blo 203807 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1173599 : Blo 203807 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B780623 : Blo 203807 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B1174283 : Blo 203807 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B748379 : Blo 203807 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B945017 : Blo 203807 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B289903 : Blo 203807 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B1043603 : Blo 203807 1043603 := bstep (se 1 (by rfl) ⟨782702, by rfl⟩ : syracuseStep 1043603 = 1565405) B1565405
theorem B519443 : Blo 203807 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B552619 : Blo 203807 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B585569 : Blo 203807 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B258223 : Blo 203807 258223 := bstep (se 1 (by rfl) ⟨193667, by rfl⟩ : syracuseStep 258223 = 387335) B387335
theorem B782567 : Blo 203807 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B3633547 : Blo 203807 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B8417945 : Blo 203807 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B783067 : Blo 203807 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B2487439 : Blo 203807 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B184251743 : Blo 203807 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B784039 : Blo 203807 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B2815661 : Blo 203807 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B5043923 : Blo 203807 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B1177517 : Blo 203807 1177517 := bstep (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) B441569
theorem B784343 : Blo 203807 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B653321 : Blo 203807 653321 := bstep (se 2 (by rfl) ⟨244995, by rfl⟩ : syracuseStep 653321 = 489991) B489991
theorem B391223 : Blo 203807 391223 := bstep (se 1 (by rfl) ⟨293417, by rfl⟩ : syracuseStep 391223 = 586835) B586835
theorem B260263 : Blo 203807 260263 := bstep (se 1 (by rfl) ⟨195197, by rfl⟩ : syracuseStep 260263 = 390395) B390395
theorem B522551 : Blo 203807 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B784799 : Blo 203807 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B522683 : Blo 203807 522683 := bstep (se 1 (by rfl) ⟨392012, by rfl⟩ : syracuseStep 522683 = 784025) B784025
theorem B2488805 : Blo 203807 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B260587 : Blo 203807 260587 := bstep (se 1 (by rfl) ⟨195440, by rfl⟩ : syracuseStep 260587 = 390881) B390881
theorem B1112705 : Blo 203807 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B2357981 : Blo 203807 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B523219 : Blo 203807 523219 := bstep (se 1 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 523219 = 784829) B784829
theorem B1178657 : Blo 203807 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B490807 : Blo 203807 490807 := bstep (se 1 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 490807 = 736211) B736211
theorem B392681 : Blo 203807 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B785983 : Blo 203807 785983 := bstep (se 1 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 785983 = 1178975) B1178975
theorem B1179431 : Blo 203807 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B524171 : Blo 203807 524171 := bstep (se 1 (by rfl) ⟨393128, by rfl⟩ : syracuseStep 524171 = 786257) B786257
theorem B688283 : Blo 203807 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B524627 : Blo 203807 524627 := bstep (se 1 (by rfl) ⟨393470, by rfl⟩ : syracuseStep 524627 = 786941) B786941
theorem B557651 : Blo 203807 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B394055 : Blo 203807 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B1049435 : Blo 203807 1049435 := bstep (se 1 (by rfl) ⟨787076, by rfl⟩ : syracuseStep 1049435 = 1574153) B1574153
theorem B689147 : Blo 203807 689147 := bstep (se 1 (by rfl) ⟨516860, by rfl⟩ : syracuseStep 689147 = 1033721) B1033721
theorem B525467 : Blo 203807 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B1115473 : Blo 203807 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B689903 : Blo 203807 689903 := bstep (se 1 (by rfl) ⟨517427, by rfl⟩ : syracuseStep 689903 = 1034855) B1034855
theorem B1738559 : Blo 203807 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B231259 : Blo 203807 231259 := bstep (se 1 (by rfl) ⟨173444, by rfl⟩ : syracuseStep 231259 = 346889) B346889
theorem B3770833 : Blo 203807 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B461897 : Blo 203807 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B756985 : Blo 203807 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B331447 : Blo 203807 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B2363417 : Blo 203807 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B24154685 : Blo 203807 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B16192315 : Blo 203807 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B463679 : Blo 203807 463679 := bstep (se 1 (by rfl) ⟨347759, by rfl⟩ : syracuseStep 463679 = 695519) B695519
theorem B1971377 : Blo 203807 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B3250601 : Blo 203807 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B3316585 : Blo 203807 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B465875 : Blo 203807 465875 := bstep (se 1 (by rfl) ⟨349406, by rfl⟩ : syracuseStep 465875 = 698813) B698813
theorem B203839 : Blo 203807 203839 := bstep (se 1 (by rfl) ⟨152879, by rfl⟩ : syracuseStep 203839 = 305759) B305759
theorem B465983 : Blo 203807 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B2825293 : Blo 203807 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B498919 : Blo 203807 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B630011 : Blo 203807 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B204059 : Blo 203807 204059 := bstep (se 1 (by rfl) ⟨153044, by rfl⟩ : syracuseStep 204059 = 306089) B306089
theorem B1056041 : Blo 203807 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B204079 : Blo 203807 204079 := bstep (se 1 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 204079 = 306119) B306119
theorem B662867 : Blo 203807 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B204159 : Blo 203807 204159 := bstep (se 1 (by rfl) ⟨153119, by rfl⟩ : syracuseStep 204159 = 306239) B306239
theorem B695735 : Blo 203807 695735 := bstep (se 1 (by rfl) ⟨521801, by rfl⟩ : syracuseStep 695735 = 1043603) B1043603
theorem B466451 : Blo 203807 466451 := bstep (se 1 (by rfl) ⟨349838, by rfl⟩ : syracuseStep 466451 = 699677) B699677
theorem B204319 : Blo 203807 204319 := bstep (se 1 (by rfl) ⟨153239, by rfl⟩ : syracuseStep 204319 = 306479) B306479
theorem B204443 : Blo 203807 204443 := bstep (se 1 (by rfl) ⟨153332, by rfl⟩ : syracuseStep 204443 = 306665) B306665
theorem B204479 : Blo 203807 204479 := bstep (se 1 (by rfl) ⟨153359, by rfl⟩ : syracuseStep 204479 = 306719) B306719
theorem B204539 : Blo 203807 204539 := bstep (se 1 (by rfl) ⟨153404, by rfl⟩ : syracuseStep 204539 = 306809) B306809
theorem B204703 : Blo 203807 204703 := bstep (se 1 (by rfl) ⟨153527, by rfl⟩ : syracuseStep 204703 = 307055) B307055
theorem B466919 : Blo 203807 466919 := bstep (se 1 (by rfl) ⟨350189, by rfl⟩ : syracuseStep 466919 = 700379) B700379
theorem B11345939 : Blo 203807 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B204871 : Blo 203807 204871 := bstep (se 1 (by rfl) ⟨153653, by rfl⟩ : syracuseStep 204871 = 307307) B307307
theorem B205159 : Blo 203807 205159 := bstep (se 1 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 205159 = 307739) B307739
theorem B5611963 : Blo 203807 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B205279 : Blo 203807 205279 := bstep (se 1 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 205279 = 307919) B307919
theorem B205471 : Blo 203807 205471 := bstep (se 1 (by rfl) ⟨154103, by rfl⟩ : syracuseStep 205471 = 308207) B308207
theorem B7873199 : Blo 203807 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B205727 : Blo 203807 205727 := bstep (se 1 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 205727 = 308591) B308591
theorem B205807 : Blo 203807 205807 := bstep (se 1 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 205807 = 308711) B308711
theorem B205927 : Blo 203807 205927 := bstep (se 1 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 205927 = 308891) B308891
theorem B1877107 : Blo 203807 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B697625 : Blo 203807 697625 := bstep (se 2 (by rfl) ⟨261609, by rfl⟩ : syracuseStep 697625 = 523219) B523219
theorem B206151 : Blo 203807 206151 := bstep (se 1 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 206151 = 309227) B309227
theorem B435547 : Blo 203807 435547 := bstep (se 1 (by rfl) ⟨326660, by rfl⟩ : syracuseStep 435547 = 653321) B653321
theorem B206207 : Blo 203807 206207 := bstep (se 1 (by rfl) ⟨154655, by rfl⟩ : syracuseStep 206207 = 309311) B309311
theorem B206427 : Blo 203807 206427 := bstep (se 1 (by rfl) ⟨154820, by rfl⟩ : syracuseStep 206427 = 309641) B309641
theorem B206543 : Blo 203807 206543 := bstep (se 1 (by rfl) ⟨154907, by rfl⟩ : syracuseStep 206543 = 309815) B309815
theorem B206759 : Blo 203807 206759 := bstep (se 1 (by rfl) ⟨155069, by rfl⟩ : syracuseStep 206759 = 310139) B310139
theorem B1583135 : Blo 203807 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B207167 : Blo 203807 207167 := bstep (se 1 (by rfl) ⟨155375, by rfl⟩ : syracuseStep 207167 = 310751) B310751
theorem B207335 : Blo 203807 207335 := bstep (se 1 (by rfl) ⟨155501, by rfl⟩ : syracuseStep 207335 = 311003) B311003
theorem B207515 : Blo 203807 207515 := bstep (se 1 (by rfl) ⟨155636, by rfl⟩ : syracuseStep 207515 = 311273) B311273
theorem B1747655 : Blo 203807 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B1125083 : Blo 203807 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B207643 : Blo 203807 207643 := bstep (se 1 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 207643 = 311465) B311465
theorem B306383 : Blo 203807 306383 := bstep (se 1 (by rfl) ⟨229787, by rfl⟩ : syracuseStep 306383 = 459575) B459575
theorem B306503 : Blo 203807 306503 := bstep (se 1 (by rfl) ⟨229877, by rfl⟩ : syracuseStep 306503 = 459755) B459755
theorem B699731 : Blo 203807 699731 := bstep (se 1 (by rfl) ⟨524798, by rfl⟩ : syracuseStep 699731 = 1049597) B1049597
theorem B306953 : Blo 203807 306953 := bstep (se 2 (by rfl) ⟨115107, by rfl⟩ : syracuseStep 306953 = 230215) B230215
theorem B307103 : Blo 203807 307103 := bstep (se 1 (by rfl) ⟨230327, by rfl⟩ : syracuseStep 307103 = 460655) B460655
theorem B307175 : Blo 203807 307175 := bstep (se 1 (by rfl) ⟨230381, by rfl⟩ : syracuseStep 307175 = 460763) B460763
theorem B307247 : Blo 203807 307247 := bstep (se 1 (by rfl) ⟨230435, by rfl⟩ : syracuseStep 307247 = 460871) B460871
theorem B307295 : Blo 203807 307295 := bstep (se 1 (by rfl) ⟨230471, by rfl⟩ : syracuseStep 307295 = 460943) B460943
theorem B307355 : Blo 203807 307355 := bstep (se 1 (by rfl) ⟨230516, by rfl⟩ : syracuseStep 307355 = 461033) B461033
theorem B307367 : Blo 203807 307367 := bstep (se 1 (by rfl) ⟨230525, by rfl⟩ : syracuseStep 307367 = 461051) B461051
theorem B700649 : Blo 203807 700649 := bstep (se 2 (by rfl) ⟨262743, by rfl⟩ : syracuseStep 700649 = 525487) B525487
theorem B700703 : Blo 203807 700703 := bstep (se 1 (by rfl) ⟨525527, by rfl⟩ : syracuseStep 700703 = 1051055) B1051055
theorem B307535 : Blo 203807 307535 := bstep (se 1 (by rfl) ⟨230651, by rfl⟩ : syracuseStep 307535 = 461303) B461303
theorem B1421687 : Blo 203807 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B701135 : Blo 203807 701135 := bstep (se 1 (by rfl) ⟨525851, by rfl⟩ : syracuseStep 701135 = 1051703) B1051703
theorem B308201 : Blo 203807 308201 := bstep (se 2 (by rfl) ⟨115575, by rfl⟩ : syracuseStep 308201 = 231151) B231151
theorem B308873 : Blo 203807 308873 := bstep (se 2 (by rfl) ⟨115827, by rfl⟩ : syracuseStep 308873 = 231655) B231655
theorem B5028155 : Blo 203807 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B188627285 : Blo 203807 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B12139307 : Blo 203807 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B310439 : Blo 203807 310439 := bstep (se 1 (by rfl) ⟨232829, by rfl⟩ : syracuseStep 310439 = 465659) B465659
theorem B310523 : Blo 203807 310523 := bstep (se 1 (by rfl) ⟨232892, by rfl⟩ : syracuseStep 310523 = 465785) B465785
theorem B310649 : Blo 203807 310649 := bstep (se 2 (by rfl) ⟨116493, by rfl⟩ : syracuseStep 310649 = 232987) B232987
theorem B1162619 : Blo 203807 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B3554705 : Blo 203807 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2670191 : Blo 203807 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B311177 : Blo 203807 311177 := bstep (se 2 (by rfl) ⟨116691, by rfl⟩ : syracuseStep 311177 = 233383) B233383
theorem B5947343 : Blo 203807 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B311417 : Blo 203807 311417 := bstep (se 2 (by rfl) ⟨116781, by rfl⟩ : syracuseStep 311417 = 233563) B233563
theorem B344297 : Blo 203807 344297 := bstep (se 2 (by rfl) ⟨129111, by rfl⟩ : syracuseStep 344297 = 258223) B258223
theorem B311711 : Blo 203807 311711 := bstep (se 1 (by rfl) ⟨233783, by rfl⟩ : syracuseStep 311711 = 467567) B467567
theorem B3556655 : Blo 203807 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B1034207 : Blo 203807 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B346295 : Blo 203807 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B707201 : Blo 203807 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B347017 : Blo 203807 347017 := bstep (se 2 (by rfl) ⟨130131, by rfl⟩ : syracuseStep 347017 = 260263) B260263
theorem B2214863 : Blo 203807 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B347449 : Blo 203807 347449 := bstep (se 2 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 347449 = 260587) B260587
theorem B122834495 : Blo 203807 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B3362615 : Blo 203807 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B348367 : Blo 203807 348367 := bstep (se 1 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 348367 = 522551) B522551
theorem B348455 : Blo 203807 348455 := bstep (se 1 (by rfl) ⟨261341, by rfl⟩ : syracuseStep 348455 = 522683) B522683
theorem B1659203 : Blo 203807 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B512335 : Blo 203807 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B741803 : Blo 203807 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B1561517 : Blo 203807 1561517 := bstep (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) B585569
theorem B1037447 : Blo 203807 1037447 := bstep (se 1 (by rfl) ⟨778085, by rfl⟩ : syracuseStep 1037447 = 1556171) B1556171
theorem B349447 : Blo 203807 349447 := bstep (se 1 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 349447 = 524171) B524171
theorem B1168769 : Blo 203807 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B775763 : Blo 203807 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B776263 : Blo 203807 776263 := bstep (se 1 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 776263 = 1164395) B1164395
theorem B1497275 : Blo 203807 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B1988873 : Blo 203807 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B776567 : Blo 203807 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B874921 : Blo 203807 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B777023 : Blo 203807 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B220315 : Blo 203807 220315 := bstep (se 1 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 220315 = 330473) B330473
theorem B1040039 : Blo 203807 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B778207 : Blo 203807 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B778679 : Blo 203807 778679 := bstep (se 1 (by rfl) ⟨584009, by rfl⟩ : syracuseStep 778679 = 1168019) B1168019
theorem B386537 : Blo 203807 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B1861343 : Blo 203807 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B583463 : Blo 203807 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B2353211 : Blo 203807 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B780455 : Blo 203807 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B551099 : Blo 203807 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B1403513 : Blo 203807 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B1862777 : Blo 203807 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B4844729 : Blo 203807 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B519655 : Blo 203807 519655 := bstep (se 1 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 519655 = 779483) B779483
theorem B585319 : Blo 203807 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B1470059 : Blo 203807 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1044089 : Blo 203807 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B945851 : Blo 203807 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B782399 : Blo 203807 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B520415 : Blo 203807 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B782855 : Blo 203807 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B1045385 : Blo 203807 1045385 := bstep (se 2 (by rfl) ⟨392019, by rfl⟩ : syracuseStep 1045385 = 784039) B784039
theorem B881567 : Blo 203807 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B586777 : Blo 203807 586777 := bstep (se 2 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 586777 = 440083) B440083
theorem B521711 : Blo 203807 521711 := bstep (se 1 (by rfl) ⟨391283, by rfl⟩ : syracuseStep 521711 = 782567) B782567
theorem B1669319 : Blo 203807 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B785011 : Blo 203807 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B522895 : Blo 203807 522895 := bstep (se 1 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 522895 = 784343) B784343
theorem B260815 : Blo 203807 260815 := bstep (se 1 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 260815 = 391223) B391223
theorem B523199 : Blo 203807 523199 := bstep (se 1 (by rfl) ⟨392399, by rfl⟩ : syracuseStep 523199 = 784799) B784799
theorem B654409 : Blo 203807 654409 := bstep (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) B490807
theorem B1571987 : Blo 203807 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B785771 : Blo 203807 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B1047977 : Blo 203807 1047977 := bstep (se 2 (by rfl) ⟨392991, by rfl⟩ : syracuseStep 1047977 = 785983) B785983
theorem B261787 : Blo 203807 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B786287 : Blo 203807 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B458855 : Blo 203807 458855 := bstep (se 1 (by rfl) ⟨344141, by rfl⟩ : syracuseStep 458855 = 688283) B688283
theorem B229531 : Blo 203807 229531 := bstep (se 1 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 229531 = 344297) B344297
theorem B262703 : Blo 203807 262703 := bstep (se 1 (by rfl) ⟨197027, by rfl⟩ : syracuseStep 262703 = 394055) B394055
theorem B459431 : Blo 203807 459431 := bstep (se 1 (by rfl) ⟨344573, by rfl⟩ : syracuseStep 459431 = 689147) B689147
theorem B459935 : Blo 203807 459935 := bstep (se 1 (by rfl) ⟨344951, by rfl⟩ : syracuseStep 459935 = 689903) B689903
theorem B689471 : Blo 203807 689471 := bstep (se 1 (by rfl) ⟨517103, by rfl⟩ : syracuseStep 689471 = 1034207) B1034207
theorem B230863 : Blo 203807 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B1476575 : Blo 203807 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B81889663 : Blo 203807 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B1575611 : Blo 203807 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B232303 : Blo 203807 232303 := bstep (se 1 (by rfl) ⟨174227, by rfl⟩ : syracuseStep 232303 = 348455) B348455
theorem B691631 : Blo 203807 691631 := bstep (se 1 (by rfl) ⟨518723, by rfl⟩ : syracuseStep 691631 = 1037447) B1037447
theorem B1314251 : Blo 203807 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B462689 : Blo 203807 462689 := bstep (se 2 (by rfl) ⟨173508, by rfl⟩ : syracuseStep 462689 = 347017) B347017
theorem B2167067 : Blo 203807 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B463265 : Blo 203807 463265 := bstep (se 2 (by rfl) ⟨173724, by rfl⟩ : syracuseStep 463265 = 347449) B347449
theorem B692873 : Blo 203807 692873 := bstep (se 2 (by rfl) ⟨259827, by rfl⟩ : syracuseStep 692873 = 519655) B519655
theorem B463823 : Blo 203807 463823 := bstep (se 1 (by rfl) ⟨347867, by rfl⟩ : syracuseStep 463823 = 695735) B695735
theorem B693359 : Blo 203807 693359 := bstep (se 1 (by rfl) ⟨520019, by rfl⟩ : syracuseStep 693359 = 1040039) B1040039
theorem B464489 : Blo 203807 464489 := bstep (se 2 (by rfl) ⟨174183, by rfl⟩ : syracuseStep 464489 = 348367) B348367
theorem B5248799 : Blo 203807 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B465083 : Blo 203807 465083 := bstep (se 1 (by rfl) ⟨348812, by rfl⟩ : syracuseStep 465083 = 697625) B697625
theorem B1055423 : Blo 203807 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B367399 : Blo 203807 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B465929 : Blo 203807 465929 := bstep (se 2 (by rfl) ⟨174723, by rfl⟩ : syracuseStep 465929 = 349447) B349447
theorem B204255 : Blo 203807 204255 := bstep (se 1 (by rfl) ⟨153191, by rfl⟩ : syracuseStep 204255 = 306383) B306383
theorem B204335 : Blo 203807 204335 := bstep (se 1 (by rfl) ⟨153251, by rfl⟩ : syracuseStep 204335 = 306503) B306503
theorem B466487 : Blo 203807 466487 := bstep (se 1 (by rfl) ⟨349865, by rfl⟩ : syracuseStep 466487 = 699731) B699731
theorem B696059 : Blo 203807 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B204635 : Blo 203807 204635 := bstep (se 1 (by rfl) ⟨153476, by rfl⟩ : syracuseStep 204635 = 306953) B306953
theorem B204735 : Blo 203807 204735 := bstep (se 1 (by rfl) ⟨153551, by rfl⟩ : syracuseStep 204735 = 307103) B307103
theorem B204783 : Blo 203807 204783 := bstep (se 1 (by rfl) ⟨153587, by rfl⟩ : syracuseStep 204783 = 307175) B307175
theorem B204831 : Blo 203807 204831 := bstep (se 1 (by rfl) ⟨153623, by rfl⟩ : syracuseStep 204831 = 307247) B307247
theorem B204863 : Blo 203807 204863 := bstep (se 1 (by rfl) ⟨153647, by rfl⟩ : syracuseStep 204863 = 307295) B307295
theorem B204903 : Blo 203807 204903 := bstep (se 1 (by rfl) ⟨153677, by rfl⟩ : syracuseStep 204903 = 307355) B307355
theorem B204911 : Blo 203807 204911 := bstep (se 1 (by rfl) ⟨153683, by rfl⟩ : syracuseStep 204911 = 307367) B307367
theorem B467099 : Blo 203807 467099 := bstep (se 1 (by rfl) ⟨350324, by rfl⟩ : syracuseStep 467099 = 700649) B700649
theorem B467135 : Blo 203807 467135 := bstep (se 1 (by rfl) ⟨350351, by rfl⟩ : syracuseStep 467135 = 700703) B700703
theorem B205023 : Blo 203807 205023 := bstep (se 1 (by rfl) ⟨153767, by rfl⟩ : syracuseStep 205023 = 307535) B307535
theorem B467423 : Blo 203807 467423 := bstep (se 1 (by rfl) ⟨350567, by rfl⟩ : syracuseStep 467423 = 701135) B701135
theorem B12919277 : Blo 203807 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B696923 : Blo 203807 696923 := bstep (se 1 (by rfl) ⟨522692, by rfl⟩ : syracuseStep 696923 = 1045385) B1045385
theorem B205467 : Blo 203807 205467 := bstep (se 1 (by rfl) ⟨154100, by rfl⟩ : syracuseStep 205467 = 308201) B308201
theorem B697193 : Blo 203807 697193 := bstep (se 2 (by rfl) ⟨261447, by rfl⟩ : syracuseStep 697193 = 522895) B522895
theorem B205915 : Blo 203807 205915 := bstep (se 1 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 205915 = 308873) B308873
theorem B3352103 : Blo 203807 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B665225 : Blo 203807 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B206959 : Blo 203807 206959 := bstep (se 1 (by rfl) ⟨155219, by rfl⟩ : syracuseStep 206959 = 310439) B310439
theorem B207015 : Blo 203807 207015 := bstep (se 1 (by rfl) ⟨155261, by rfl⟩ : syracuseStep 207015 = 310523) B310523
theorem B207099 : Blo 203807 207099 := bstep (se 1 (by rfl) ⟨155324, by rfl⟩ : syracuseStep 207099 = 310649) B310649
theorem B2369803 : Blo 203807 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B698651 : Blo 203807 698651 := bstep (se 1 (by rfl) ⟨523988, by rfl⟩ : syracuseStep 698651 = 1047977) B1047977
theorem B1780127 : Blo 203807 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B207451 : Blo 203807 207451 := bstep (se 1 (by rfl) ⟨155588, by rfl⟩ : syracuseStep 207451 = 311177) B311177
theorem B207611 : Blo 203807 207611 := bstep (se 1 (by rfl) ⟨155708, by rfl⟩ : syracuseStep 207611 = 311417) B311417
theorem B207807 : Blo 203807 207807 := bstep (se 1 (by rfl) ⟨155855, by rfl⟩ : syracuseStep 207807 = 311711) B311711
theorem B699623 : Blo 203807 699623 := bstep (se 1 (by rfl) ⟨524717, by rfl⟩ : syracuseStep 699623 = 1049435) B1049435
theorem B7482617 : Blo 203807 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B2371103 : Blo 203807 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1159039 : Blo 203807 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B2502809 : Blo 203807 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B1487069 : Blo 203807 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B2732453 : Blo 203807 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B471467 : Blo 203807 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B1487297 : Blo 203807 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B307931 : Blo 203807 307931 := bstep (se 1 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 307931 = 461897) B461897
theorem B143471573 : Blo 203807 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B308345 : Blo 203807 308345 := bstep (se 2 (by rfl) ⟨115629, by rfl⟩ : syracuseStep 308345 = 231259) B231259
theorem B16103123 : Blo 203807 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B309119 : Blo 203807 309119 := bstep (se 1 (by rfl) ⟨231839, by rfl⟩ : syracuseStep 309119 = 463679) B463679
theorem B5027777 : Blo 203807 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1030765 : Blo 203807 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B998183 : Blo 203807 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B1325915 : Blo 203807 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B7912565 : Blo 203807 7912565 := bstep (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) B741803
theorem B310583 : Blo 203807 310583 := bstep (se 1 (by rfl) ⟨232937, by rfl⟩ : syracuseStep 310583 = 465875) B465875
theorem B310655 : Blo 203807 310655 := bstep (se 1 (by rfl) ⟨232991, by rfl⟩ : syracuseStep 310655 = 465983) B465983
theorem B704027 : Blo 203807 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B441911 : Blo 203807 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B441929 : Blo 203807 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B310967 : Blo 203807 310967 := bstep (se 1 (by rfl) ⟨233225, by rfl⟩ : syracuseStep 310967 = 466451) B466451
theorem B311279 : Blo 203807 311279 := bstep (se 1 (by rfl) ⟨233459, by rfl⟩ : syracuseStep 311279 = 466919) B466919
theorem B935675 : Blo 203807 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B1165103 : Blo 203807 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B1035017 : Blo 203807 1035017 := bstep (se 2 (by rfl) ⟨388131, by rfl⟩ : syracuseStep 1035017 = 776263) B776263
theorem B346943 : Blo 203807 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B1166561 : Blo 203807 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B347753 : Blo 203807 347753 := bstep (se 2 (by rfl) ⟨130407, by rfl⟩ : syracuseStep 347753 = 260815) B260815
theorem B347807 : Blo 203807 347807 := bstep (se 1 (by rfl) ⟨260855, by rfl⟩ : syracuseStep 347807 = 521711) B521711
theorem B872545 : Blo 203807 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B125751523 : Blo 203807 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B348799 : Blo 203807 348799 := bstep (se 1 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 348799 = 523199) B523199
theorem B349049 : Blo 203807 349049 := bstep (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) B261787
theorem B775079 : Blo 203807 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B1037609 : Blo 203807 1037609 := bstep (se 2 (by rfl) ⟨389103, by rfl⟩ : syracuseStep 1037609 = 778207) B778207
theorem B349751 : Blo 203807 349751 := bstep (se 1 (by rfl) ⟨262313, by rfl⟩ : syracuseStep 349751 = 524627) B524627
theorem B350311 : Blo 203807 350311 := bstep (se 1 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 350311 = 525467) B525467
theorem B580729 : Blo 203807 580729 := bstep (se 2 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 580729 = 435547) B435547
theorem B1106135 : Blo 203807 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1041011 : Blo 203807 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B779179 : Blo 203807 779179 := bstep (se 1 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 779179 = 1168769) B1168769
theorem B517175 : Blo 203807 517175 := bstep (se 1 (by rfl) ⟨387881, by rfl⟩ : syracuseStep 517175 = 775763) B775763
theorem B517711 : Blo 203807 517711 := bstep (se 1 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 517711 = 776567) B776567
theorem B1009313 : Blo 203807 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B518015 : Blo 203807 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B780425 : Blo 203807 780425 := bstep (se 2 (by rfl) ⟨292659, by rfl⟩ : syracuseStep 780425 = 585319) B585319
theorem B420007 : Blo 203807 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B7563959 : Blo 203807 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B519119 : Blo 203807 519119 := bstep (se 1 (by rfl) ⟨389339, by rfl⟩ : syracuseStep 519119 = 778679) B778679
theorem B21589753 : Blo 203807 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1240895 : Blo 203807 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B388975 : Blo 203807 388975 := bstep (se 1 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 388975 = 583463) B583463
theorem B782369 : Blo 203807 782369 := bstep (se 2 (by rfl) ⟨293388, by rfl⟩ : syracuseStep 782369 = 586777) B586777
theorem B1568807 : Blo 203807 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B520303 : Blo 203807 520303 := bstep (se 1 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 520303 = 780455) B780455
theorem B750055 : Blo 203807 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B1241851 : Blo 203807 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B980039 : Blo 203807 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B521599 : Blo 203807 521599 := bstep (se 1 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 521599 = 782399) B782399
theorem B947791 : Blo 203807 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B521903 : Blo 203807 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B587711 : Blo 203807 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B1046681 : Blo 203807 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B4422113 : Blo 203807 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B3767057 : Blo 203807 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1112879 : Blo 203807 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B293753 : Blo 203807 293753 := bstep (se 2 (by rfl) ⟨110157, by rfl⟩ : syracuseStep 293753 = 220315) B220315
theorem B2522269 : Blo 203807 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B8092871 : Blo 203807 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B1047991 : Blo 203807 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B523847 : Blo 203807 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B524191 : Blo 203807 524191 := bstep (se 1 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 524191 = 786287) B786287
theorem B3964895 : Blo 203807 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B459647 : Blo 203807 459647 := bstep (se 1 (by rfl) ⟨344735, by rfl⟩ : syracuseStep 459647 = 689471) B689471
theorem B623783 : Blo 203807 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B984383 : Blo 203807 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B1050407 : Blo 203807 1050407 := bstep (se 1 (by rfl) ⟨787805, by rfl⟩ : syracuseStep 1050407 = 1575611) B1575611
theorem B690011 : Blo 203807 690011 := bstep (se 1 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 690011 = 1035017) B1035017
theorem B231295 : Blo 203807 231295 := bstep (se 1 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 231295 = 346943) B346943
theorem B690281 : Blo 203807 690281 := bstep (se 2 (by rfl) ⟨258855, by rfl⟩ : syracuseStep 690281 = 517711) B517711
theorem B461087 : Blo 203807 461087 := bstep (se 1 (by rfl) ⟨345815, by rfl⟩ : syracuseStep 461087 = 691631) B691631
theorem B231835 : Blo 203807 231835 := bstep (se 1 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 231835 = 347753) B347753
theorem B231871 : Blo 203807 231871 := bstep (se 1 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 231871 = 347807) B347807
theorem B1444711 : Blo 203807 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B560009 : Blo 203807 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B461915 : Blo 203807 461915 := bstep (se 1 (by rfl) ⟨346436, by rfl⟩ : syracuseStep 461915 = 692873) B692873
theorem B109186217 : Blo 203807 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B232699 : Blo 203807 232699 := bstep (se 1 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 232699 = 349049) B349049
theorem B462239 : Blo 203807 462239 := bstep (se 1 (by rfl) ⟨346679, by rfl⟩ : syracuseStep 462239 = 693359) B693359
theorem B691739 : Blo 203807 691739 := bstep (se 1 (by rfl) ⟨518804, by rfl⟩ : syracuseStep 691739 = 1037609) B1037609
theorem B233167 : Blo 203807 233167 := bstep (se 1 (by rfl) ⟨174875, by rfl⟩ : syracuseStep 233167 = 349751) B349751
theorem B464039 : Blo 203807 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B693737 : Blo 203807 693737 := bstep (se 2 (by rfl) ⟨260151, by rfl⟩ : syracuseStep 693737 = 520303) B520303
theorem B464615 : Blo 203807 464615 := bstep (se 1 (by rfl) ⟨348461, by rfl⟩ : syracuseStep 464615 = 696923) B696923
theorem B694007 : Blo 203807 694007 := bstep (se 1 (by rfl) ⟨520505, by rfl⟩ : syracuseStep 694007 = 1041011) B1041011
theorem B464795 : Blo 203807 464795 := bstep (se 1 (by rfl) ⟨348596, by rfl⟩ : syracuseStep 464795 = 697193) B697193
theorem B465065 : Blo 203807 465065 := bstep (se 2 (by rfl) ⟨174399, by rfl⟩ : syracuseStep 465065 = 348799) B348799
theorem B2234735 : Blo 203807 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B465767 : Blo 203807 465767 := bstep (se 1 (by rfl) ⟨349325, by rfl⟩ : syracuseStep 465767 = 698651) B698651
theorem B1186751 : Blo 203807 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B695465 : Blo 203807 695465 := bstep (se 2 (by rfl) ⟨260799, by rfl⟩ : syracuseStep 695465 = 521599) B521599
theorem B2661821 : Blo 203807 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B466415 : Blo 203807 466415 := bstep (se 1 (by rfl) ⟨349811, by rfl⟩ : syracuseStep 466415 = 699623) B699623
theorem B4988411 : Blo 203807 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B1580735 : Blo 203807 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B827263 : Blo 203807 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B467081 : Blo 203807 467081 := bstep (se 2 (by rfl) ⟨175155, by rfl⟩ : syracuseStep 467081 = 350311) B350311
theorem B991379 : Blo 203807 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B991531 : Blo 203807 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B205287 : Blo 203807 205287 := bstep (se 1 (by rfl) ⟨153965, by rfl⟩ : syracuseStep 205287 = 307931) B307931
theorem B205563 : Blo 203807 205563 := bstep (se 1 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 205563 = 308345) B308345
theorem B206079 : Blo 203807 206079 := bstep (se 1 (by rfl) ⟨154559, by rfl⟩ : syracuseStep 206079 = 309119) B309119
theorem B3351851 : Blo 203807 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B697787 : Blo 203807 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B207055 : Blo 203807 207055 := bstep (se 1 (by rfl) ⟨155291, by rfl⟩ : syracuseStep 207055 = 310583) B310583
theorem B207103 : Blo 203807 207103 := bstep (se 1 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 207103 = 310655) B310655
theorem B469351 : Blo 203807 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B207311 : Blo 203807 207311 := bstep (se 1 (by rfl) ⟨155483, by rfl⟩ : syracuseStep 207311 = 310967) B310967
theorem B698921 : Blo 203807 698921 := bstep (se 2 (by rfl) ⟨262095, by rfl⟩ : syracuseStep 698921 = 524191) B524191
theorem B207519 : Blo 203807 207519 := bstep (se 1 (by rfl) ⟨155639, by rfl⟩ : syracuseStep 207519 = 311279) B311279
theorem B305903 : Blo 203807 305903 := bstep (se 1 (by rfl) ⟨229427, by rfl⟩ : syracuseStep 305903 = 458855) B458855
theorem B306041 : Blo 203807 306041 := bstep (se 2 (by rfl) ⟨114765, by rfl⟩ : syracuseStep 306041 = 229531) B229531
theorem B306287 : Blo 203807 306287 := bstep (se 1 (by rfl) ⟨229715, by rfl⟩ : syracuseStep 306287 = 459431) B459431
theorem B306623 : Blo 203807 306623 := bstep (se 1 (by rfl) ⟨229967, by rfl⟩ : syracuseStep 306623 = 459935) B459935
theorem B1257245 : Blo 203807 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B700541 : Blo 203807 700541 := bstep (se 3 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 700541 = 262703) B262703
theorem B307817 : Blo 203807 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B308459 : Blo 203807 308459 := bstep (se 1 (by rfl) ⟨231344, by rfl⟩ : syracuseStep 308459 = 462689) B462689
theorem B308843 : Blo 203807 308843 := bstep (se 1 (by rfl) ⟨231632, by rfl⟩ : syracuseStep 308843 = 463265) B463265
theorem B3159737 : Blo 203807 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B309215 : Blo 203807 309215 := bstep (se 1 (by rfl) ⟨231911, by rfl⟩ : syracuseStep 309215 = 463823) B463823
theorem B309659 : Blo 203807 309659 := bstep (se 1 (by rfl) ⟨232244, by rfl⟩ : syracuseStep 309659 = 464489) B464489
theorem B309737 : Blo 203807 309737 := bstep (se 2 (by rfl) ⟨116151, by rfl⟩ : syracuseStep 309737 = 232303) B232303
theorem B310055 : Blo 203807 310055 := bstep (se 1 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 310055 = 465083) B465083
theorem B703615 : Blo 203807 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B310619 : Blo 203807 310619 := bstep (se 1 (by rfl) ⟨232964, by rfl⟩ : syracuseStep 310619 = 465929) B465929
theorem B28786337 : Blo 203807 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B310991 : Blo 203807 310991 := bstep (se 1 (by rfl) ⟨233243, by rfl⟩ : syracuseStep 310991 = 466487) B466487
theorem B311399 : Blo 203807 311399 := bstep (se 1 (by rfl) ⟨233549, by rfl⟩ : syracuseStep 311399 = 467099) B467099
theorem B311423 : Blo 203807 311423 := bstep (se 1 (by rfl) ⟨233567, by rfl⟩ : syracuseStep 311423 = 467135) B467135
theorem B1163393 : Blo 203807 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B737423 : Blo 203807 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B311615 : Blo 203807 311615 := bstep (se 1 (by rfl) ⟨233711, by rfl⟩ : syracuseStep 311615 = 467423) B467423
theorem B1000073 : Blo 203807 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B344783 : Blo 203807 344783 := bstep (se 1 (by rfl) ⟨258587, by rfl⟩ : syracuseStep 344783 = 517175) B517175
theorem B13452101 : Blo 203807 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B1655801 : Blo 203807 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B443483 : Blo 203807 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B672875 : Blo 203807 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B345343 : Blo 203807 345343 := bstep (se 1 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 345343 = 518015) B518015
theorem B346079 : Blo 203807 346079 := bstep (se 1 (by rfl) ⟨259559, by rfl⟩ : syracuseStep 346079 = 519119) B519119
theorem B1263721 : Blo 203807 1263721 := bstep (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) B947791
theorem B2967677 : Blo 203807 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B1821635 : Blo 203807 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B347935 : Blo 203807 347935 := bstep (se 1 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 347935 = 521903) B521903
theorem B10735415 : Blo 203807 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B774305 : Blo 203807 774305 := bstep (se 2 (by rfl) ⟨290364, by rfl⟩ : syracuseStep 774305 = 580729) B580729
theorem B2511371 : Blo 203807 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1397321 : Blo 203807 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B6181541 : Blo 203807 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B5395247 : Blo 203807 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B349231 : Blo 203807 349231 := bstep (se 1 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 349231 = 523847) B523847
theorem B2643263 : Blo 203807 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B776735 : Blo 203807 776735 := bstep (se 1 (by rfl) ⟨582551, by rfl⟩ : syracuseStep 776735 = 1165103) B1165103
theorem B1038905 : Blo 203807 1038905 := bstep (se 2 (by rfl) ⟨389589, by rfl⟩ : syracuseStep 1038905 = 779179) B779179
theorem B777707 : Blo 203807 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B876167 : Blo 203807 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B516719 : Blo 203807 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B3499199 : Blo 203807 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B1959461 : Blo 203807 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B518633 : Blo 203807 518633 := bstep (se 2 (by rfl) ⟨194487, by rfl⟩ : syracuseStep 518633 = 388975) B388975
theorem B167668697 : Blo 203807 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B8612851 : Blo 203807 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B520283 : Blo 203807 520283 := bstep (se 1 (by rfl) ⟨390212, by rfl⟩ : syracuseStep 520283 = 780425) B780425
theorem B5042639 : Blo 203807 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B783341 : Blo 203807 783341 := bstep (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) B293753
theorem B521579 : Blo 203807 521579 := bstep (se 1 (by rfl) ⟨391184, by rfl⟩ : syracuseStep 521579 = 782369) B782369
theorem B1045871 : Blo 203807 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B1668539 : Blo 203807 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B95647715 : Blo 203807 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B653359 : Blo 203807 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B1374353 : Blo 203807 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B391807 : Blo 203807 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B2948075 : Blo 203807 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B883943 : Blo 203807 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B5275043 : Blo 203807 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B294607 : Blo 203807 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B294619 : Blo 203807 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B491615 : Blo 203807 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B229855 : Blo 203807 229855 := bstep (se 1 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 229855 = 344783) B344783
theorem B295655 : Blo 203807 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B656255 : Blo 203807 656255 := bstep (se 1 (by rfl) ⟨492191, by rfl⟩ : syracuseStep 656255 = 984383) B984383
theorem B460007 : Blo 203807 460007 := bstep (se 1 (by rfl) ⟨345005, by rfl⟩ : syracuseStep 460007 = 690011) B690011
theorem B230719 : Blo 203807 230719 := bstep (se 1 (by rfl) ⟨173039, by rfl⟩ : syracuseStep 230719 = 346079) B346079
theorem B460187 : Blo 203807 460187 := bstep (se 1 (by rfl) ⟨345140, by rfl⟩ : syracuseStep 460187 = 690281) B690281
theorem B460457 : Blo 203807 460457 := bstep (se 2 (by rfl) ⟨172671, by rfl⟩ : syracuseStep 460457 = 345343) B345343
theorem B1214423 : Blo 203807 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B461159 : Blo 203807 461159 := bstep (se 1 (by rfl) ⟨345869, by rfl⟩ : syracuseStep 461159 = 691739) B691739
theorem B625801 : Blo 203807 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B462491 : Blo 203807 462491 := bstep (se 1 (by rfl) ⟨346868, by rfl⟩ : syracuseStep 462491 = 693737) B693737
theorem B462671 : Blo 203807 462671 := bstep (se 1 (by rfl) ⟨347003, by rfl⟩ : syracuseStep 462671 = 694007) B694007
theorem B692603 : Blo 203807 692603 := bstep (se 1 (by rfl) ⟨519452, by rfl⟩ : syracuseStep 692603 = 1038905) B1038905
theorem B791167 : Blo 203807 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B463643 : Blo 203807 463643 := bstep (se 1 (by rfl) ⟨347732, by rfl⟩ : syracuseStep 463643 = 695465) B695465
theorem B1774547 : Blo 203807 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B463913 : Blo 203807 463913 := bstep (se 2 (by rfl) ⟨173967, by rfl⟩ : syracuseStep 463913 = 347935) B347935
theorem B1053823 : Blo 203807 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B660919 : Blo 203807 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B2332799 : Blo 203807 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B2234567 : Blo 203807 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B465191 : Blo 203807 465191 := bstep (se 1 (by rfl) ⟨348893, by rfl⟩ : syracuseStep 465191 = 697787) B697787
theorem B465641 : Blo 203807 465641 := bstep (se 2 (by rfl) ⟨174615, by rfl⟩ : syracuseStep 465641 = 349231) B349231
theorem B465947 : Blo 203807 465947 := bstep (se 1 (by rfl) ⟨349460, by rfl⟩ : syracuseStep 465947 = 698921) B698921
theorem B203935 : Blo 203807 203935 := bstep (se 1 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 203935 = 305903) B305903
theorem B204027 : Blo 203807 204027 := bstep (se 1 (by rfl) ⟨153020, by rfl⟩ : syracuseStep 204027 = 306041) B306041
theorem B111779131 : Blo 203807 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B204191 : Blo 203807 204191 := bstep (se 1 (by rfl) ⟨153143, by rfl⟩ : syracuseStep 204191 = 306287) B306287
theorem B204415 : Blo 203807 204415 := bstep (se 1 (by rfl) ⟨153311, by rfl⟩ : syracuseStep 204415 = 306623) B306623
theorem B467027 : Blo 203807 467027 := bstep (se 1 (by rfl) ⟨350270, by rfl⟩ : syracuseStep 467027 = 700541) B700541
theorem B205211 : Blo 203807 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B205639 : Blo 203807 205639 := bstep (se 1 (by rfl) ⟨154229, by rfl⟩ : syracuseStep 205639 = 308459) B308459
theorem B697247 : Blo 203807 697247 := bstep (se 1 (by rfl) ⟨522935, by rfl⟩ : syracuseStep 697247 = 1045871) B1045871
theorem B205895 : Blo 203807 205895 := bstep (se 1 (by rfl) ⟨154421, by rfl⟩ : syracuseStep 205895 = 308843) B308843
theorem B2106491 : Blo 203807 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B206143 : Blo 203807 206143 := bstep (se 1 (by rfl) ⟨154607, by rfl⟩ : syracuseStep 206143 = 309215) B309215
theorem B206439 : Blo 203807 206439 := bstep (se 1 (by rfl) ⟨154829, by rfl⟩ : syracuseStep 206439 = 309659) B309659
theorem B206491 : Blo 203807 206491 := bstep (se 1 (by rfl) ⟨154868, by rfl⟩ : syracuseStep 206491 = 309737) B309737
theorem B206703 : Blo 203807 206703 := bstep (se 1 (by rfl) ⟨155027, by rfl⟩ : syracuseStep 206703 = 310055) B310055
theorem B207079 : Blo 203807 207079 := bstep (se 1 (by rfl) ⟨155309, by rfl⟩ : syracuseStep 207079 = 310619) B310619
theorem B3516695 : Blo 203807 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B207327 : Blo 203807 207327 := bstep (se 1 (by rfl) ⟨155495, by rfl⟩ : syracuseStep 207327 = 310991) B310991
theorem B207599 : Blo 203807 207599 := bstep (se 1 (by rfl) ⟨155699, by rfl⟩ : syracuseStep 207599 = 311399) B311399
theorem B207615 : Blo 203807 207615 := bstep (se 1 (by rfl) ⟨155711, by rfl⟩ : syracuseStep 207615 = 311423) B311423
theorem B207743 : Blo 203807 207743 := bstep (se 1 (by rfl) ⟨155807, by rfl⟩ : syracuseStep 207743 = 311615) B311615
theorem B666715 : Blo 203807 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B306431 : Blo 203807 306431 := bstep (se 1 (by rfl) ⟨229823, by rfl⟩ : syracuseStep 306431 = 459647) B459647
theorem B700271 : Blo 203807 700271 := bstep (se 1 (by rfl) ⟨525203, by rfl⟩ : syracuseStep 700271 = 1050407) B1050407
theorem B13447037 : Blo 203807 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B6696989 : Blo 203807 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B1978451 : Blo 203807 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B307391 : Blo 203807 307391 := bstep (se 1 (by rfl) ⟨230543, by rfl⟩ : syracuseStep 307391 = 461087) B461087
theorem B5288165 : Blo 203807 5288165 := bstep (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) B991531
theorem B373339 : Blo 203807 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B307943 : Blo 203807 307943 := bstep (se 1 (by rfl) ⟨230957, by rfl⟩ : syracuseStep 307943 = 461915) B461915
theorem B72790811 : Blo 203807 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B308159 : Blo 203807 308159 := bstep (se 1 (by rfl) ⟨231119, by rfl⟩ : syracuseStep 308159 = 462239) B462239
theorem B308393 : Blo 203807 308393 := bstep (se 2 (by rfl) ⟨115647, by rfl⟩ : syracuseStep 308393 = 231295) B231295
theorem B7156943 : Blo 203807 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B1684961 : Blo 203807 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B931547 : Blo 203807 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B309113 : Blo 203807 309113 := bstep (se 2 (by rfl) ⟨115917, by rfl⟩ : syracuseStep 309113 = 231835) B231835
theorem B309161 : Blo 203807 309161 := bstep (se 2 (by rfl) ⟨115935, by rfl⟩ : syracuseStep 309161 = 231871) B231871
theorem B309359 : Blo 203807 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B309743 : Blo 203807 309743 := bstep (se 1 (by rfl) ⟨232307, by rfl⟩ : syracuseStep 309743 = 464615) B464615
theorem B309863 : Blo 203807 309863 := bstep (se 1 (by rfl) ⟨232397, by rfl⟩ : syracuseStep 309863 = 464795) B464795
theorem B11483801 : Blo 203807 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B310043 : Blo 203807 310043 := bstep (se 1 (by rfl) ⟨232532, by rfl⟩ : syracuseStep 310043 = 465065) B465065
theorem B1489823 : Blo 203807 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B310265 : Blo 203807 310265 := bstep (se 2 (by rfl) ⟨116349, by rfl⟩ : syracuseStep 310265 = 232699) B232699
theorem B310511 : Blo 203807 310511 := bstep (se 1 (by rfl) ⟨232883, by rfl⟩ : syracuseStep 310511 = 465767) B465767
theorem B310889 : Blo 203807 310889 := bstep (se 2 (by rfl) ⟨116583, by rfl⟩ : syracuseStep 310889 = 233167) B233167
theorem B310943 : Blo 203807 310943 := bstep (se 1 (by rfl) ⟨233207, by rfl⟩ : syracuseStep 310943 = 466415) B466415
theorem B3325607 : Blo 203807 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B311387 : Blo 203807 311387 := bstep (se 1 (by rfl) ⟨233540, by rfl⟩ : syracuseStep 311387 = 467081) B467081
theorem B344479 : Blo 203807 344479 := bstep (se 1 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 344479 = 516719) B516719
theorem B345755 : Blo 203807 345755 := bstep (se 1 (by rfl) ⟨259316, by rfl⟩ : syracuseStep 345755 = 518633) B518633
theorem B838163 : Blo 203807 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B346855 : Blo 203807 346855 := bstep (se 1 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 346855 = 520283) B520283
theorem B871145 : Blo 203807 871145 := bstep (se 2 (by rfl) ⟨326679, by rfl⟩ : syracuseStep 871145 = 653359) B653359
theorem B347719 : Blo 203807 347719 := bstep (se 1 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 347719 = 521579) B521579
theorem B938153 : Blo 203807 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B4412069 : Blo 203807 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B19190891 : Blo 203807 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B775595 : Blo 203807 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B8968067 : Blo 203807 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B1103867 : Blo 203807 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B448583 : Blo 203807 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B415855 : Blo 203807 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B516203 : Blo 203807 516203 := bstep (se 1 (by rfl) ⟨387152, by rfl⟩ : syracuseStep 516203 = 774305) B774305
theorem B4121027 : Blo 203807 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B3596831 : Blo 203807 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B1762175 : Blo 203807 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1926281 : Blo 203807 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B4449437 : Blo 203807 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B517823 : Blo 203807 517823 := bstep (se 1 (by rfl) ⟨388367, by rfl⟩ : syracuseStep 517823 = 776735) B776735
theorem B518471 : Blo 203807 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B584111 : Blo 203807 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B1306307 : Blo 203807 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B522227 : Blo 203807 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B522409 : Blo 203807 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B1571237 : Blo 203807 1571237 := bstep (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) B294607
theorem B63765143 : Blo 203807 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B916235 : Blo 203807 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B1965383 : Blo 203807 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B589295 : Blo 203807 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B392825 : Blo 203807 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B327743 : Blo 203807 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B459305 : Blo 203807 459305 := bstep (se 2 (by rfl) ⟨172239, by rfl⟩ : syracuseStep 459305 = 344479) B344479
theorem B230503 : Blo 203807 230503 := bstep (se 1 (by rfl) ⟨172877, by rfl⟩ : syracuseStep 230503 = 345755) B345755
theorem B558775 : Blo 203807 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B788413 : Blo 203807 788413 := bstep (se 3 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 788413 = 295655) B295655
theorem B461735 : Blo 203807 461735 := bstep (se 1 (by rfl) ⟨346301, by rfl⟩ : syracuseStep 461735 = 692603) B692603
theorem B1183031 : Blo 203807 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B462473 : Blo 203807 462473 := bstep (se 2 (by rfl) ⟨173427, by rfl⟩ : syracuseStep 462473 = 346855) B346855
theorem B888953 : Blo 203807 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B463625 : Blo 203807 463625 := bstep (se 2 (by rfl) ⟨173859, by rfl⟩ : syracuseStep 463625 = 347719) B347719
theorem B2397887 : Blo 203807 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B464831 : Blo 203807 464831 := bstep (se 1 (by rfl) ⟨348623, by rfl⟩ : syracuseStep 464831 = 697247) B697247
theorem B1284187 : Blo 203807 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1054889 : Blo 203807 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B204287 : Blo 203807 204287 := bstep (se 1 (by rfl) ⟨153215, by rfl⟩ : syracuseStep 204287 = 306431) B306431
theorem B466847 : Blo 203807 466847 := bstep (se 1 (by rfl) ⟨350135, by rfl⟩ : syracuseStep 466847 = 700271) B700271
theorem B4464659 : Blo 203807 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B1318967 : Blo 203807 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B204927 : Blo 203807 204927 := bstep (se 1 (by rfl) ⟨153695, by rfl⟩ : syracuseStep 204927 = 307391) B307391
theorem B696545 : Blo 203807 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B205295 : Blo 203807 205295 := bstep (se 1 (by rfl) ⟨153971, by rfl⟩ : syracuseStep 205295 = 307943) B307943
theorem B205439 : Blo 203807 205439 := bstep (se 1 (by rfl) ⟨154079, by rfl⟩ : syracuseStep 205439 = 308159) B308159
theorem B205595 : Blo 203807 205595 := bstep (se 1 (by rfl) ⟨154196, by rfl⟩ : syracuseStep 205595 = 308393) B308393
theorem B1123307 : Blo 203807 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B206075 : Blo 203807 206075 := bstep (se 1 (by rfl) ⟨154556, by rfl⟩ : syracuseStep 206075 = 309113) B309113
theorem B206107 : Blo 203807 206107 := bstep (se 1 (by rfl) ⟨154580, by rfl⟩ : syracuseStep 206107 = 309161) B309161
theorem B206239 : Blo 203807 206239 := bstep (se 1 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 206239 = 309359) B309359
theorem B206495 : Blo 203807 206495 := bstep (se 1 (by rfl) ⟨154871, by rfl⟩ : syracuseStep 206495 = 309743) B309743
theorem B206575 : Blo 203807 206575 := bstep (se 1 (by rfl) ⟨154931, by rfl⟩ : syracuseStep 206575 = 309863) B309863
theorem B149038841 : Blo 203807 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B42510095 : Blo 203807 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B206695 : Blo 203807 206695 := bstep (se 1 (by rfl) ⟨155021, by rfl⟩ : syracuseStep 206695 = 310043) B310043
theorem B993215 : Blo 203807 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B206843 : Blo 203807 206843 := bstep (se 1 (by rfl) ⟨155132, by rfl⟩ : syracuseStep 206843 = 310265) B310265
theorem B207007 : Blo 203807 207007 := bstep (se 1 (by rfl) ⟨155255, by rfl⟩ : syracuseStep 207007 = 310511) B310511
theorem B35858765 : Blo 203807 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B207259 : Blo 203807 207259 := bstep (se 1 (by rfl) ⟨155444, by rfl⟩ : syracuseStep 207259 = 310889) B310889
theorem B207295 : Blo 203807 207295 := bstep (se 1 (by rfl) ⟨155471, by rfl⟩ : syracuseStep 207295 = 310943) B310943
theorem B207591 : Blo 203807 207591 := bstep (se 1 (by rfl) ⟨155693, by rfl⟩ : syracuseStep 207591 = 311387) B311387
theorem B2501741 : Blo 203807 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B437503 : Blo 203807 437503 := bstep (se 1 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 437503 = 656255) B656255
theorem B306473 : Blo 203807 306473 := bstep (se 2 (by rfl) ⟨114927, by rfl⟩ : syracuseStep 306473 = 229855) B229855
theorem B306671 : Blo 203807 306671 := bstep (se 1 (by rfl) ⟨230003, by rfl⟩ : syracuseStep 306671 = 460007) B460007
theorem B306791 : Blo 203807 306791 := bstep (se 1 (by rfl) ⟨230093, by rfl⟩ : syracuseStep 306791 = 460187) B460187
theorem B306971 : Blo 203807 306971 := bstep (se 1 (by rfl) ⟨230228, by rfl⟩ : syracuseStep 306971 = 460457) B460457
theorem B307439 : Blo 203807 307439 := bstep (se 1 (by rfl) ⟨230579, by rfl⟩ : syracuseStep 307439 = 461159) B461159
theorem B307625 : Blo 203807 307625 := bstep (se 2 (by rfl) ⟨115359, by rfl⟩ : syracuseStep 307625 = 230719) B230719
theorem B308327 : Blo 203807 308327 := bstep (se 1 (by rfl) ⟨231245, by rfl⟩ : syracuseStep 308327 = 462491) B462491
theorem B308447 : Blo 203807 308447 := bstep (se 1 (by rfl) ⟨231335, by rfl⟩ : syracuseStep 308447 = 462671) B462671
theorem B5617309 : Blo 203807 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B309095 : Blo 203807 309095 := bstep (se 1 (by rfl) ⟨231821, by rfl⟩ : syracuseStep 309095 = 463643) B463643
theorem B309275 : Blo 203807 309275 := bstep (se 1 (by rfl) ⟨231956, by rfl⟩ : syracuseStep 309275 = 463913) B463913
theorem B5978711 : Blo 203807 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B735911 : Blo 203807 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B1555199 : Blo 203807 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B834401 : Blo 203807 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B310127 : Blo 203807 310127 := bstep (se 1 (by rfl) ⟨232595, by rfl⟩ : syracuseStep 310127 = 465191) B465191
theorem B310427 : Blo 203807 310427 := bstep (se 1 (by rfl) ⟨232820, by rfl⟩ : syracuseStep 310427 = 465641) B465641
theorem B310631 : Blo 203807 310631 := bstep (se 1 (by rfl) ⟨232973, by rfl⟩ : syracuseStep 310631 = 465947) B465947
theorem B311351 : Blo 203807 311351 := bstep (se 1 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 311351 = 467027) B467027
theorem B344135 : Blo 203807 344135 := bstep (se 1 (by rfl) ⟨258101, by rfl⟩ : syracuseStep 344135 = 516203) B516203
theorem B1196221 : Blo 203807 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B2966291 : Blo 203807 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1557629 : Blo 203807 1557629 := bstep (se 3 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 1557629 = 584111) B584111
theorem B345215 : Blo 203807 345215 := bstep (se 1 (by rfl) ⟨258911, by rfl⟩ : syracuseStep 345215 = 517823) B517823
theorem B2344463 : Blo 203807 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B345647 : Blo 203807 345647 := bstep (se 1 (by rfl) ⟨259235, by rfl⟩ : syracuseStep 345647 = 518471) B518471
theorem B870871 : Blo 203807 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B3525443 : Blo 203807 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B4771295 : Blo 203807 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B348151 : Blo 203807 348151 := bstep (se 1 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 348151 = 522227) B522227
theorem B7655867 : Blo 203807 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B610823 : Blo 203807 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B2217071 : Blo 203807 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B809615 : Blo 203807 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B580763 : Blo 203807 580763 := bstep (se 1 (by rfl) ⟨435572, by rfl⟩ : syracuseStep 580763 = 871145) B871145
theorem B51175709 : Blo 203807 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B2941379 : Blo 203807 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1991141 : Blo 203807 1991141 := bstep (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) B373339
theorem B517063 : Blo 203807 517063 := bstep (se 1 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 517063 = 775595) B775595
theorem B2484125 : Blo 203807 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B2747351 : Blo 203807 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B5958845 : Blo 203807 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B1174783 : Blo 203807 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B1405097 : Blo 203807 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B881225 : Blo 203807 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B554473 : Blo 203807 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B48527207 : Blo 203807 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B1047491 : Blo 203807 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B1310255 : Blo 203807 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B392863 : Blo 203807 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B261883 : Blo 203807 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B229423 : Blo 203807 229423 := bstep (se 1 (by rfl) ⟨172067, by rfl⟩ : syracuseStep 229423 = 344135) B344135
theorem B230143 : Blo 203807 230143 := bstep (se 1 (by rfl) ⟨172607, by rfl⟩ : syracuseStep 230143 = 345215) B345215
theorem B230431 : Blo 203807 230431 := bstep (se 1 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 230431 = 345647) B345647
theorem B689417 : Blo 203807 689417 := bstep (se 2 (by rfl) ⟨258531, by rfl⟩ : syracuseStep 689417 = 517063) B517063
theorem B788687 : Blo 203807 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B3180863 : Blo 203807 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B1051217 : Blo 203807 1051217 := bstep (se 2 (by rfl) ⟨394206, by rfl⟩ : syracuseStep 1051217 = 788413) B788413
theorem B1478047 : Blo 203807 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B464201 : Blo 203807 464201 := bstep (se 2 (by rfl) ⟨174075, by rfl⟩ : syracuseStep 464201 = 348151) B348151
theorem B464363 : Blo 203807 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B34117139 : Blo 203807 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B99359227 : Blo 203807 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B662143 : Blo 203807 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B3972563 : Blo 203807 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B204315 : Blo 203807 204315 := bstep (se 1 (by rfl) ⟨153236, by rfl⟩ : syracuseStep 204315 = 306473) B306473
theorem B827005 : Blo 203807 827005 := bstep (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) B310127
theorem B204447 : Blo 203807 204447 := bstep (se 1 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 204447 = 306671) B306671
theorem B204527 : Blo 203807 204527 := bstep (se 1 (by rfl) ⟨153395, by rfl⟩ : syracuseStep 204527 = 306791) B306791
theorem B204647 : Blo 203807 204647 := bstep (se 1 (by rfl) ⟨153485, by rfl⟩ : syracuseStep 204647 = 306971) B306971
theorem B1712249 : Blo 203807 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B204959 : Blo 203807 204959 := bstep (se 1 (by rfl) ⟨153719, by rfl⟩ : syracuseStep 204959 = 307439) B307439
theorem B205083 : Blo 203807 205083 := bstep (se 1 (by rfl) ⟨153812, by rfl⟩ : syracuseStep 205083 = 307625) B307625
theorem B205551 : Blo 203807 205551 := bstep (se 1 (by rfl) ⟨154163, by rfl⟩ : syracuseStep 205551 = 308327) B308327
theorem B205631 : Blo 203807 205631 := bstep (se 1 (by rfl) ⟨154223, by rfl⟩ : syracuseStep 205631 = 308447) B308447
theorem B206063 : Blo 203807 206063 := bstep (se 1 (by rfl) ⟨154547, by rfl⟩ : syracuseStep 206063 = 309095) B309095
theorem B32351471 : Blo 203807 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B206183 : Blo 203807 206183 := bstep (se 1 (by rfl) ⟨154637, by rfl⟩ : syracuseStep 206183 = 309275) B309275
theorem B206751 : Blo 203807 206751 := bstep (se 1 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 206751 = 310127) B310127
theorem B698327 : Blo 203807 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B206951 : Blo 203807 206951 := bstep (se 1 (by rfl) ⟨155213, by rfl⟩ : syracuseStep 206951 = 310427) B310427
theorem B207087 : Blo 203807 207087 := bstep (se 1 (by rfl) ⟨155315, by rfl⟩ : syracuseStep 207087 = 310631) B310631
theorem B207567 : Blo 203807 207567 := bstep (se 1 (by rfl) ⟨155675, by rfl⟩ : syracuseStep 207567 = 311351) B311351
theorem B2370541 : Blo 203807 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B306203 : Blo 203807 306203 := bstep (se 1 (by rfl) ⟨229652, by rfl⟩ : syracuseStep 306203 = 459305) B459305
theorem B1977527 : Blo 203807 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B307337 : Blo 203807 307337 := bstep (se 2 (by rfl) ⟨115251, by rfl⟩ : syracuseStep 307337 = 230503) B230503
theorem B307823 : Blo 203807 307823 := bstep (se 1 (by rfl) ⟨230867, by rfl⟩ : syracuseStep 307823 = 461735) B461735
theorem B308315 : Blo 203807 308315 := bstep (se 1 (by rfl) ⟨231236, by rfl⟩ : syracuseStep 308315 = 462473) B462473
theorem B407215 : Blo 203807 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B309083 : Blo 203807 309083 := bstep (se 1 (by rfl) ⟨231812, by rfl⟩ : syracuseStep 309083 = 463625) B463625
theorem B1161161 : Blo 203807 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B309887 : Blo 203807 309887 := bstep (se 1 (by rfl) ⟨232415, by rfl⟩ : syracuseStep 309887 = 464831) B464831
theorem B703259 : Blo 203807 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B539743 : Blo 203807 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B311231 : Blo 203807 311231 := bstep (se 1 (by rfl) ⟨233423, by rfl⟩ : syracuseStep 311231 = 466847) B466847
theorem B1327427 : Blo 203807 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B1656083 : Blo 203807 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B23905843 : Blo 203807 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B739297 : Blo 203807 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B7489745 : Blo 203807 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B936731 : Blo 203807 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B3985807 : Blo 203807 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B1036799 : Blo 203807 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B349177 : Blo 203807 349177 := bstep (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) B261883
theorem B873503 : Blo 203807 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B218495 : Blo 203807 218495 := bstep (se 1 (by rfl) ⟨163871, by rfl⟩ : syracuseStep 218495 = 327743) B327743
theorem B1594961 : Blo 203807 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B1038419 : Blo 203807 1038419 := bstep (se 1 (by rfl) ⟨778814, by rfl⟩ : syracuseStep 1038419 = 1557629) B1557629
theorem B1562975 : Blo 203807 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B2350295 : Blo 203807 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B745033 : Blo 203807 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B5103911 : Blo 203807 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B1598591 : Blo 203807 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B583337 : Blo 203807 583337 := bstep (se 2 (by rfl) ⟨218751, by rfl⟩ : syracuseStep 583337 = 437503) B437503
theorem B1566377 : Blo 203807 1566377 := bstep (se 2 (by rfl) ⟨587391, by rfl⟩ : syracuseStep 1566377 = 1174783) B1174783
theorem B387175 : Blo 203807 387175 := bstep (se 1 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 387175 = 580763) B580763
theorem B2976439 : Blo 203807 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B879311 : Blo 203807 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B1960919 : Blo 203807 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B748871 : Blo 203807 748871 := bstep (se 1 (by rfl) ⟨561653, by rfl⟩ : syracuseStep 748871 = 1123307) B1123307
theorem B28340063 : Blo 203807 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B1831567 : Blo 203807 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B1667827 : Blo 203807 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B2225069 : Blo 203807 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B587483 : Blo 203807 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B490607 : Blo 203807 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B523817 : Blo 203807 523817 := bstep (se 2 (by rfl) ⟨196431, by rfl⟩ : syracuseStep 523817 = 392863) B392863
theorem B884951 : Blo 203807 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B459611 : Blo 203807 459611 := bstep (se 1 (by rfl) ⟨344708, by rfl⟩ : syracuseStep 459611 = 689417) B689417
theorem B525791 : Blo 203807 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B985729 : Blo 203807 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B691199 : Blo 203807 691199 := bstep (se 1 (by rfl) ⟨518399, by rfl⟩ : syracuseStep 691199 = 1036799) B1036799
theorem B3968585 : Blo 203807 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B22744759 : Blo 203807 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B692279 : Blo 203807 692279 := bstep (se 1 (by rfl) ⟨519209, by rfl⟩ : syracuseStep 692279 = 1038419) B1038419
theorem B1970729 : Blo 203807 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B5314409 : Blo 203807 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B21567647 : Blo 203807 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B465551 : Blo 203807 465551 := bstep (se 1 (by rfl) ⟨349163, by rfl⟩ : syracuseStep 465551 = 698327) B698327
theorem B465569 : Blo 203807 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B204135 : Blo 203807 204135 := bstep (se 1 (by rfl) ⟨153101, by rfl⟩ : syracuseStep 204135 = 306203) B306203
theorem B2497949 : Blo 203807 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B1318351 : Blo 203807 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B499247 : Blo 203807 499247 := bstep (se 1 (by rfl) ⟨374435, by rfl⟩ : syracuseStep 499247 = 748871) B748871
theorem B204891 : Blo 203807 204891 := bstep (se 1 (by rfl) ⟨153668, by rfl⟩ : syracuseStep 204891 = 307337) B307337
theorem B205215 : Blo 203807 205215 := bstep (se 1 (by rfl) ⟨153911, by rfl⟩ : syracuseStep 205215 = 307823) B307823
theorem B1483379 : Blo 203807 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B205543 : Blo 203807 205543 := bstep (se 1 (by rfl) ⟨154157, by rfl⟩ : syracuseStep 205543 = 308315) B308315
theorem B206055 : Blo 203807 206055 := bstep (se 1 (by rfl) ⟨154541, by rfl⟩ : syracuseStep 206055 = 309083) B309083
theorem B206591 : Blo 203807 206591 := bstep (se 1 (by rfl) ⟨154943, by rfl⟩ : syracuseStep 206591 = 309887) B309887
theorem B468839 : Blo 203807 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B993377 : Blo 203807 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B207487 : Blo 203807 207487 := bstep (se 1 (by rfl) ⟨155615, by rfl⟩ : syracuseStep 207487 = 311231) B311231
theorem B305897 : Blo 203807 305897 := bstep (se 2 (by rfl) ⟨114711, by rfl⟩ : syracuseStep 305897 = 229423) B229423
theorem B306857 : Blo 203807 306857 := bstep (se 2 (by rfl) ⟨115071, by rfl⟩ : syracuseStep 306857 = 230143) B230143
theorem B307241 : Blo 203807 307241 := bstep (se 2 (by rfl) ⟨115215, by rfl⟩ : syracuseStep 307241 = 230431) B230431
theorem B4993163 : Blo 203807 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B700811 : Blo 203807 700811 := bstep (se 1 (by rfl) ⟨525608, by rfl⟩ : syracuseStep 700811 = 1051217) B1051217
theorem B309467 : Blo 203807 309467 := bstep (se 1 (by rfl) ⟨232100, by rfl⟩ : syracuseStep 309467 = 464201) B464201
theorem B309575 : Blo 203807 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B1063307 : Blo 203807 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B3160721 : Blo 203807 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B1065727 : Blo 203807 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B2442089 : Blo 203807 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B542953 : Blo 203807 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B18893375 : Blo 203807 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B774107 : Blo 203807 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B1102673 : Blo 203807 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B349211 : Blo 203807 349211 := bstep (se 1 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 349211 = 523817) B523817
theorem B2120575 : Blo 203807 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B529915877 : Blo 203807 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B516233 : Blo 203807 516233 := bstep (se 2 (by rfl) ⟨193587, by rfl⟩ : syracuseStep 516233 = 387175) B387175
theorem B582335 : Blo 203807 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B4416221 : Blo 203807 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B582653 : Blo 203807 582653 := bstep (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) B218495
theorem B1041983 : Blo 203807 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B1566863 : Blo 203807 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B2648375 : Blo 203807 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B1141499 : Blo 203807 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B3402607 : Blo 203807 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B2223769 : Blo 203807 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B388891 : Blo 203807 388891 := bstep (se 1 (by rfl) ⟨291668, by rfl⟩ : syracuseStep 388891 = 583337) B583337
theorem B1044251 : Blo 203807 1044251 := bstep (se 1 (by rfl) ⟨783188, by rfl⟩ : syracuseStep 1044251 = 1566377) B1566377
theorem B586207 : Blo 203807 586207 := bstep (se 1 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 586207 = 879311) B879311
theorem B1307279 : Blo 203807 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B127497829 : Blo 203807 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B882857 : Blo 203807 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B391655 : Blo 203807 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B719657 : Blo 203807 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B327071 : Blo 203807 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B589967 : Blo 203807 589967 := bstep (se 1 (by rfl) ⟨442475, by rfl⟩ : syracuseStep 589967 = 884951) B884951
theorem B460799 : Blo 203807 460799 := bstep (se 1 (by rfl) ⟨345599, by rfl⟩ : syracuseStep 460799 = 691199) B691199
theorem B461519 : Blo 203807 461519 := bstep (se 1 (by rfl) ⟨346139, by rfl⟩ : syracuseStep 461519 = 692279) B692279
theorem B1313819 : Blo 203807 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B232807 : Blo 203807 232807 := bstep (se 1 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 232807 = 349211) B349211
theorem B1314305 : Blo 203807 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B3542939 : Blo 203807 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B1250237 : Blo 203807 1250237 := bstep (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) B468839
theorem B332831 : Blo 203807 332831 := bstep (se 1 (by rfl) ⟨249623, by rfl⟩ : syracuseStep 332831 = 499247) B499247
theorem B353277251 : Blo 203807 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B988919 : Blo 203807 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B57513725 : Blo 203807 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B694655 : Blo 203807 694655 := bstep (se 1 (by rfl) ⟨520991, by rfl⟩ : syracuseStep 694655 = 1041983) B1041983
theorem B662251 : Blo 203807 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B203931 : Blo 203807 203931 := bstep (se 1 (by rfl) ⟨152948, by rfl⟩ : syracuseStep 203931 = 305897) B305897
theorem B204571 : Blo 203807 204571 := bstep (se 1 (by rfl) ⟨153428, by rfl⟩ : syracuseStep 204571 = 306857) B306857
theorem B696167 : Blo 203807 696167 := bstep (se 1 (by rfl) ⟨522125, by rfl⟩ : syracuseStep 696167 = 1044251) B1044251
theorem B204827 : Blo 203807 204827 := bstep (se 1 (by rfl) ⟨153620, by rfl⟩ : syracuseStep 204827 = 307241) B307241
theorem B467207 : Blo 203807 467207 := bstep (se 1 (by rfl) ⟨350405, by rfl⟩ : syracuseStep 467207 = 700811) B700811
theorem B2827433 : Blo 203807 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B206311 : Blo 203807 206311 := bstep (se 1 (by rfl) ⟨154733, by rfl⟩ : syracuseStep 206311 = 309467) B309467
theorem B206383 : Blo 203807 206383 := bstep (se 1 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 206383 = 309575) B309575
theorem B2107147 : Blo 203807 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B306407 : Blo 203807 306407 := bstep (se 1 (by rfl) ⟨229805, by rfl⟩ : syracuseStep 306407 = 459611) B459611
theorem B2895749 : Blo 203807 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B3486077 : Blo 203807 3486077 := bstep (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) B1307279
theorem B12595583 : Blo 203807 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B1553741 : Blo 203807 1553741 := bstep (se 3 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 1553741 = 582653) B582653
theorem B735115 : Blo 203807 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B4536809 : Blo 203807 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B5683877 : Blo 203807 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B310367 : Blo 203807 310367 := bstep (se 1 (by rfl) ⟨232775, by rfl⟩ : syracuseStep 310367 = 465551) B465551
theorem B310379 : Blo 203807 310379 := bstep (se 1 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 310379 = 465569) B465569
theorem B2965025 : Blo 203807 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B30326345 : Blo 203807 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B344155 : Blo 203807 344155 := bstep (se 1 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 344155 = 516233) B516233
theorem B3328775 : Blo 203807 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B708871 : Blo 203807 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B479771 : Blo 203807 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B1757801 : Blo 203807 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B218047 : Blo 203807 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B1628059 : Blo 203807 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B350527 : Blo 203807 350527 := bstep (se 1 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 350527 = 525791) B525791
theorem B2645723 : Blo 203807 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B516071 : Blo 203807 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B1665299 : Blo 203807 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B518521 : Blo 203807 518521 := bstep (se 2 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 518521 = 388891) B388891
theorem B2354285 : Blo 203807 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B388223 : Blo 203807 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B2944147 : Blo 203807 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B781609 : Blo 203807 781609 := bstep (se 2 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 781609 = 586207) B586207
theorem B1044413 : Blo 203807 1044413 := bstep (se 3 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 1044413 = 391655) B391655
theorem B1044575 : Blo 203807 1044575 := bstep (se 1 (by rfl) ⟨783431, by rfl⟩ : syracuseStep 1044575 = 1566863) B1566863
theorem B1765583 : Blo 203807 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B3043997 : Blo 203807 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B169997105 : Blo 203807 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B393311 : Blo 203807 393311 := bstep (se 1 (by rfl) ⟨294983, by rfl⟩ : syracuseStep 393311 = 589967) B589967
theorem B458873 : Blo 203807 458873 := bstep (se 2 (by rfl) ⟨172077, by rfl⟩ : syracuseStep 458873 = 344155) B344155
theorem B2361959 : Blo 203807 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B691361 : Blo 203807 691361 := bstep (se 2 (by rfl) ⟨259260, by rfl⟩ : syracuseStep 691361 = 518521) B518521
theorem B659279 : Blo 203807 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B38342483 : Blo 203807 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B463103 : Blo 203807 463103 := bstep (se 1 (by rfl) ⟨347327, by rfl⟩ : syracuseStep 463103 = 694655) B694655
theorem B464111 : Blo 203807 464111 := bstep (se 1 (by rfl) ⟨348083, by rfl⟩ : syracuseStep 464111 = 696167) B696167
theorem B204271 : Blo 203807 204271 := bstep (se 1 (by rfl) ⟨153203, by rfl⟩ : syracuseStep 204271 = 306407) B306407
theorem B2170745 : Blo 203807 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B696275 : Blo 203807 696275 := bstep (se 1 (by rfl) ⟨522206, by rfl⟩ : syracuseStep 696275 = 1044413) B1044413
theorem B696383 : Blo 203807 696383 := bstep (se 1 (by rfl) ⟨522287, by rfl⟩ : syracuseStep 696383 = 1044575) B1044575
theorem B8397055 : Blo 203807 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B467369 : Blo 203807 467369 := bstep (se 2 (by rfl) ⟨175263, by rfl⟩ : syracuseStep 467369 = 350527) B350527
theorem B3024539 : Blo 203807 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B206911 : Blo 203807 206911 := bstep (se 1 (by rfl) ⟨155183, by rfl⟩ : syracuseStep 206911 = 310367) B310367
theorem B206919 : Blo 203807 206919 := bstep (se 1 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 206919 = 310379) B310379
theorem B1976683 : Blo 203807 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B307199 : Blo 203807 307199 := bstep (se 1 (by rfl) ⟨230399, by rfl⟩ : syracuseStep 307199 = 460799) B460799
theorem B307679 : Blo 203807 307679 := bstep (se 1 (by rfl) ⟨230759, by rfl⟩ : syracuseStep 307679 = 461519) B461519
theorem B833491 : Blo 203807 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B235518167 : Blo 203807 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B310409 : Blo 203807 310409 := bstep (se 2 (by rfl) ⟨116403, by rfl⟩ : syracuseStep 310409 = 232807) B232807
theorem B344047 : Blo 203807 344047 := bstep (se 1 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 344047 = 516071) B516071
theorem B311471 : Blo 203807 311471 := bstep (se 1 (by rfl) ⟨233603, by rfl⟩ : syracuseStep 311471 = 467207) B467207
theorem B1884955 : Blo 203807 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B6278093 : Blo 203807 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B113331403 : Blo 203807 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B1035827 : Blo 203807 1035827 := bstep (se 1 (by rfl) ⟨776870, by rfl⟩ : syracuseStep 1035827 = 1553741) B1553741
theorem B3789251 : Blo 203807 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B2219183 : Blo 203807 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B875879 : Blo 203807 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B876203 : Blo 203807 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B2809529 : Blo 203807 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B319847 : Blo 203807 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B1171867 : Blo 203807 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B221887 : Blo 203807 221887 := bstep (se 1 (by rfl) ⟨166415, by rfl⟩ : syracuseStep 221887 = 332831) B332831
theorem B3925529 : Blo 203807 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B1042145 : Blo 203807 1042145 := bstep (se 2 (by rfl) ⟨390804, by rfl⟩ : syracuseStep 1042145 = 781609) B781609
theorem B1763815 : Blo 203807 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B945161 : Blo 203807 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B290729 : Blo 203807 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B1110199 : Blo 203807 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B258815 : Blo 203807 258815 := bstep (se 1 (by rfl) ⟨194111, by rfl⟩ : syracuseStep 258815 = 388223) B388223
theorem B980153 : Blo 203807 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B1930499 : Blo 203807 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1177055 : Blo 203807 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B2324051 : Blo 203807 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B2029331 : Blo 203807 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B883001 : Blo 203807 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B20217563 : Blo 203807 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B262207 : Blo 203807 262207 := bstep (se 1 (by rfl) ⟨196655, by rfl⟩ : syracuseStep 262207 = 393311) B393311
theorem B295849 : Blo 203807 295849 := bstep (se 2 (by rfl) ⟨110943, by rfl⟩ : syracuseStep 295849 = 221887) B221887
theorem B852925 : Blo 203807 852925 := bstep (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) B319847
theorem B1574639 : Blo 203807 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B690173 : Blo 203807 690173 := bstep (se 3 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 690173 = 258815) B258815
theorem B460907 : Blo 203807 460907 := bstep (se 1 (by rfl) ⟨345680, by rfl⟩ : syracuseStep 460907 = 691361) B691361
theorem B690551 : Blo 203807 690551 := bstep (se 1 (by rfl) ⟨517913, by rfl⟩ : syracuseStep 690551 = 1035827) B1035827
theorem B25561655 : Blo 203807 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B2526167 : Blo 203807 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B5411549 : Blo 203807 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B1479455 : Blo 203807 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1873019 : Blo 203807 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B1447163 : Blo 203807 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B464183 : Blo 203807 464183 := bstep (se 1 (by rfl) ⟨348137, by rfl⟩ : syracuseStep 464183 = 696275) B696275
theorem B464255 : Blo 203807 464255 := bstep (se 1 (by rfl) ⟨348191, by rfl⟩ : syracuseStep 464255 = 696383) B696383
theorem B1480265 : Blo 203807 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B694763 : Blo 203807 694763 := bstep (se 1 (by rfl) ⟨521072, by rfl⟩ : syracuseStep 694763 = 1042145) B1042145
theorem B630107 : Blo 203807 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B204799 : Blo 203807 204799 := bstep (se 1 (by rfl) ⟨153599, by rfl⟩ : syracuseStep 204799 = 307199) B307199
theorem B205119 : Blo 203807 205119 := bstep (se 1 (by rfl) ⟨153839, by rfl⟩ : syracuseStep 205119 = 307679) B307679
theorem B1286999 : Blo 203807 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B1549367 : Blo 203807 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B206939 : Blo 203807 206939 := bstep (se 1 (by rfl) ⟨155204, by rfl⟩ : syracuseStep 206939 = 310409) B310409
theorem B13478375 : Blo 203807 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B305915 : Blo 203807 305915 := bstep (se 1 (by rfl) ⟨229436, by rfl⟩ : syracuseStep 305915 = 458873) B458873
theorem B207647 : Blo 203807 207647 := bstep (se 1 (by rfl) ⟨155735, by rfl⟩ : syracuseStep 207647 = 311471) B311471
theorem B439519 : Blo 203807 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B308735 : Blo 203807 308735 := bstep (se 1 (by rfl) ⟨231551, by rfl⟩ : syracuseStep 308735 = 463103) B463103
theorem B2635577 : Blo 203807 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B309407 : Blo 203807 309407 := bstep (se 1 (by rfl) ⟨232055, by rfl⟩ : syracuseStep 309407 = 464111) B464111
theorem B151108537 : Blo 203807 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B311579 : Blo 203807 311579 := bstep (se 1 (by rfl) ⟨233684, by rfl⟩ : syracuseStep 311579 = 467369) B467369
theorem B2016359 : Blo 203807 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B157012111 : Blo 203807 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B775277 : Blo 203807 775277 := bstep (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) B290729
theorem B11196073 : Blo 203807 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B1562489 : Blo 203807 1562489 := bstep (se 2 (by rfl) ⟨585933, by rfl⟩ : syracuseStep 1562489 = 1171867) B1171867
theorem B2513273 : Blo 203807 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B4185395 : Blo 203807 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B2351753 : Blo 203807 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B583919 : Blo 203807 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B584135 : Blo 203807 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B2354669 : Blo 203807 2354669 := bstep (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) B883001
theorem B2617019 : Blo 203807 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B1111321 : Blo 203807 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B653435 : Blo 203807 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B784703 : Blo 203807 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B458729 : Blo 203807 458729 := bstep (se 2 (by rfl) ⟨172023, by rfl⟩ : syracuseStep 458729 = 344047) B344047
theorem B1344239 : Blo 203807 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B1049759 : Blo 203807 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B394465 : Blo 203807 394465 := bstep (se 2 (by rfl) ⟨147924, by rfl⟩ : syracuseStep 394465 = 295849) B295849
theorem B460115 : Blo 203807 460115 := bstep (se 1 (by rfl) ⟨345086, by rfl⟩ : syracuseStep 460115 = 690173) B690173
theorem B460367 : Blo 203807 460367 := bstep (se 1 (by rfl) ⟨345275, by rfl⟩ : syracuseStep 460367 = 690551) B690551
theorem B17041103 : Blo 203807 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B986303 : Blo 203807 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B1248679 : Blo 203807 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B986843 : Blo 203807 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B463175 : Blo 203807 463175 := bstep (se 1 (by rfl) ⟨347381, by rfl⟩ : syracuseStep 463175 = 694763) B694763
theorem B2790263 : Blo 203807 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B857999 : Blo 203807 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B8985583 : Blo 203807 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B1481761 : Blo 203807 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B203943 : Blo 203807 203943 := bstep (se 1 (by rfl) ⟨152957, by rfl⟩ : syracuseStep 203943 = 305915) B305915
theorem B1744679 : Blo 203807 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B205823 : Blo 203807 205823 := bstep (se 1 (by rfl) ⟨154367, by rfl⟩ : syracuseStep 205823 = 308735) B308735
theorem B435623 : Blo 203807 435623 := bstep (se 1 (by rfl) ⟨326717, by rfl⟩ : syracuseStep 435623 = 653435) B653435
theorem B206271 : Blo 203807 206271 := bstep (se 1 (by rfl) ⟨154703, by rfl⟩ : syracuseStep 206271 = 309407) B309407
theorem B305819 : Blo 203807 305819 := bstep (se 1 (by rfl) ⟨229364, by rfl⟩ : syracuseStep 305819 = 458729) B458729
theorem B207719 : Blo 203807 207719 := bstep (se 1 (by rfl) ⟨155789, by rfl⟩ : syracuseStep 207719 = 311579) B311579
theorem B837397925 : Blo 203807 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B307271 : Blo 203807 307271 := bstep (se 1 (by rfl) ⟨230453, by rfl⟩ : syracuseStep 307271 = 460907) B460907
theorem B14430797 : Blo 203807 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B1684111 : Blo 203807 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B964775 : Blo 203807 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B309455 : Blo 203807 309455 := bstep (se 1 (by rfl) ⟨232091, by rfl⟩ : syracuseStep 309455 = 464183) B464183
theorem B309503 : Blo 203807 309503 := bstep (se 1 (by rfl) ⟨232127, by rfl⟩ : syracuseStep 309503 = 464255) B464255
theorem B1032911 : Blo 203807 1032911 := bstep (se 1 (by rfl) ⟨774683, by rfl⟩ : syracuseStep 1032911 = 1549367) B1549367
theorem B6702061 : Blo 203807 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B14928097 : Blo 203807 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B1757051 : Blo 203807 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B201478049 : Blo 203807 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B349609 : Blo 203807 349609 := bstep (se 2 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 349609 = 262207) B262207
theorem B1137233 : Blo 203807 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B516851 : Blo 203807 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B1041659 : Blo 203807 1041659 := bstep (se 1 (by rfl) ⟨781244, by rfl⟩ : syracuseStep 1041659 = 1562489) B1562489
theorem B420071 : Blo 203807 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B1567835 : Blo 203807 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B389279 : Blo 203807 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B586025 : Blo 203807 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B389423 : Blo 203807 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B1569779 : Blo 203807 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B523135 : Blo 203807 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B688607 : Blo 203807 688607 := bstep (se 1 (by rfl) ⟨516455, by rfl⟩ : syracuseStep 688607 = 1032911) B1032911
theorem B525953 : Blo 203807 525953 := bstep (se 2 (by rfl) ⟨197232, by rfl⟩ : syracuseStep 525953 = 394465) B394465
theorem B657895 : Blo 203807 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B134318699 : Blo 203807 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B758155 : Blo 203807 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1120189 : Blo 203807 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B694439 : Blo 203807 694439 := bstep (se 1 (by rfl) ⟨520829, by rfl⟩ : syracuseStep 694439 = 1041659) B1041659
theorem B203879 : Blo 203807 203879 := bstep (se 1 (by rfl) ⟨152909, by rfl⟩ : syracuseStep 203879 = 305819) B305819
theorem B466145 : Blo 203807 466145 := bstep (se 2 (by rfl) ⟨174804, by rfl⟩ : syracuseStep 466145 = 349609) B349609
theorem B6659621 : Blo 203807 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B204847 : Blo 203807 204847 := bstep (se 1 (by rfl) ⟨153635, by rfl⟩ : syracuseStep 204847 = 307271) B307271
theorem B2630141 : Blo 203807 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B697513 : Blo 203807 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B1975681 : Blo 203807 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B206303 : Blo 203807 206303 := bstep (se 1 (by rfl) ⟨154727, by rfl⟩ : syracuseStep 206303 = 309455) B309455
theorem B206335 : Blo 203807 206335 := bstep (se 1 (by rfl) ⟨154751, by rfl⟩ : syracuseStep 206335 = 309503) B309503
theorem B896159 : Blo 203807 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B699839 : Blo 203807 699839 := bstep (se 1 (by rfl) ⟨524879, by rfl⟩ : syracuseStep 699839 = 1049759) B1049759
theorem B306743 : Blo 203807 306743 := bstep (se 1 (by rfl) ⟨230057, by rfl⟩ : syracuseStep 306743 = 460115) B460115
theorem B306911 : Blo 203807 306911 := bstep (se 1 (by rfl) ⟨230183, by rfl⟩ : syracuseStep 306911 = 460367) B460367
theorem B308783 : Blo 203807 308783 := bstep (se 1 (by rfl) ⟨231587, by rfl⟩ : syracuseStep 308783 = 463175) B463175
theorem B19904129 : Blo 203807 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B1161661 : Blo 203807 1161661 := bstep (se 3 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 1161661 = 435623) B435623
theorem B1163119 : Blo 203807 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B47923109 : Blo 203807 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B344567 : Blo 203807 344567 := bstep (se 1 (by rfl) ⟨258425, by rfl⟩ : syracuseStep 344567 = 516851) B516851
theorem B2245481 : Blo 203807 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B9620531 : Blo 203807 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B643183 : Blo 203807 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B11360735 : Blo 203807 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B8936081 : Blo 203807 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B1171367 : Blo 203807 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B1860175 : Blo 203807 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B2287997 : Blo 203807 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1045223 : Blo 203807 1045223 := bstep (se 1 (by rfl) ⟨783917, by rfl⟩ : syracuseStep 1045223 = 1567835) B1567835
theorem B558265283 : Blo 203807 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B259519 : Blo 203807 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B390683 : Blo 203807 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B259615 : Blo 203807 259615 := bstep (se 1 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 259615 = 389423) B389423
theorem B1046519 : Blo 203807 1046519 := bstep (se 1 (by rfl) ⟨784889, by rfl⟩ : syracuseStep 1046519 = 1569779) B1569779
theorem B459071 : Blo 203807 459071 := bstep (se 1 (by rfl) ⟨344303, by rfl⟩ : syracuseStep 459071 = 688607) B688607
theorem B229711 : Blo 203807 229711 := bstep (se 1 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 229711 = 344567) B344567
theorem B462959 : Blo 203807 462959 := bstep (se 1 (by rfl) ⟨347219, by rfl⟩ : syracuseStep 462959 = 694439) B694439
theorem B7573823 : Blo 203807 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B597439 : Blo 203807 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B466559 : Blo 203807 466559 := bstep (se 1 (by rfl) ⟨349919, by rfl⟩ : syracuseStep 466559 = 699839) B699839
theorem B204495 : Blo 203807 204495 := bstep (se 1 (by rfl) ⟨153371, by rfl⟩ : syracuseStep 204495 = 306743) B306743
theorem B204607 : Blo 203807 204607 := bstep (se 1 (by rfl) ⟨153455, by rfl⟩ : syracuseStep 204607 = 306911) B306911
theorem B696815 : Blo 203807 696815 := bstep (se 1 (by rfl) ⟨522611, by rfl⟩ : syracuseStep 696815 = 1045223) B1045223
theorem B1548881 : Blo 203807 1548881 := bstep (se 2 (by rfl) ⟨580830, by rfl⟩ : syracuseStep 1548881 = 1161661) B1161661
theorem B205855 : Blo 203807 205855 := bstep (se 1 (by rfl) ⟨154391, by rfl⟩ : syracuseStep 205855 = 308783) B308783
theorem B697679 : Blo 203807 697679 := bstep (se 1 (by rfl) ⟨523259, by rfl⟩ : syracuseStep 697679 = 1046519) B1046519
theorem B1550825 : Blo 203807 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B930017 : Blo 203807 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B2634241 : Blo 203807 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B310763 : Blo 203807 310763 := bstep (se 1 (by rfl) ⟨233072, by rfl⟩ : syracuseStep 310763 = 466145) B466145
theorem B4439747 : Blo 203807 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B1753427 : Blo 203807 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B1525331 : Blo 203807 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B346025 : Blo 203807 346025 := bstep (se 2 (by rfl) ⟨129759, by rfl⟩ : syracuseStep 346025 = 259519) B259519
theorem B346153 : Blo 203807 346153 := bstep (se 2 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 346153 = 259615) B259615
theorem B1493585 : Blo 203807 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B1496987 : Blo 203807 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B2480233 : Blo 203807 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B350635 : Blo 203807 350635 := bstep (se 1 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 350635 = 525953) B525953
theorem B89545799 : Blo 203807 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B6413687 : Blo 203807 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B13721237 : Blo 203807 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B877193 : Blo 203807 877193 := bstep (se 2 (by rfl) ⟨328947, by rfl⟩ : syracuseStep 877193 = 657895) B657895
theorem B1041821 : Blo 203807 1041821 := bstep (se 3 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 1041821 = 390683) B390683
theorem B5957387 : Blo 203807 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B780911 : Blo 203807 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B1010873 : Blo 203807 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B372176855 : Blo 203807 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B13269419 : Blo 203807 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B31948739 : Blo 203807 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B1016887 : Blo 203807 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B230683 : Blo 203807 230683 := bstep (se 1 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 230683 = 346025) B346025
theorem B461537 : Blo 203807 461537 := bstep (se 2 (by rfl) ⟨173076, by rfl⟩ : syracuseStep 461537 = 346153) B346153
theorem B5049215 : Blo 203807 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B9147491 : Blo 203807 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B464543 : Blo 203807 464543 := bstep (se 1 (by rfl) ⟨348407, by rfl⟩ : syracuseStep 464543 = 696815) B696815
theorem B3512321 : Blo 203807 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B465119 : Blo 203807 465119 := bstep (se 1 (by rfl) ⟨348839, by rfl⟩ : syracuseStep 465119 = 697679) B697679
theorem B694547 : Blo 203807 694547 := bstep (se 1 (by rfl) ⟨520910, by rfl⟩ : syracuseStep 694547 = 1041821) B1041821
theorem B3971591 : Blo 203807 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B3186341 : Blo 203807 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B467513 : Blo 203807 467513 := bstep (se 2 (by rfl) ⟨175317, by rfl⟩ : syracuseStep 467513 = 350635) B350635
theorem B207175 : Blo 203807 207175 := bstep (se 1 (by rfl) ⟨155381, by rfl⟩ : syracuseStep 207175 = 310763) B310763
theorem B2959831 : Blo 203807 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B306047 : Blo 203807 306047 := bstep (se 1 (by rfl) ⟨229535, by rfl⟩ : syracuseStep 306047 = 459071) B459071
theorem B306281 : Blo 203807 306281 := bstep (se 2 (by rfl) ⟨114855, by rfl⟩ : syracuseStep 306281 = 229711) B229711
theorem B995723 : Blo 203807 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B308639 : Blo 203807 308639 := bstep (se 1 (by rfl) ⟨231479, by rfl⟩ : syracuseStep 308639 = 462959) B462959
theorem B997991 : Blo 203807 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B4275791 : Blo 203807 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B311039 : Blo 203807 311039 := bstep (se 1 (by rfl) ⟨233279, by rfl⟩ : syracuseStep 311039 = 466559) B466559
theorem B1032587 : Blo 203807 1032587 := bstep (se 1 (by rfl) ⟨774440, by rfl⟩ : syracuseStep 1032587 = 1548881) B1548881
theorem B1033883 : Blo 203807 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B673915 : Blo 203807 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B1168951 : Blo 203807 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B59697199 : Blo 203807 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B584795 : Blo 203807 584795 := bstep (se 1 (by rfl) ⟨438596, by rfl⟩ : syracuseStep 584795 = 877193) B877193
theorem B520607 : Blo 203807 520607 := bstep (se 1 (by rfl) ⟨390455, by rfl⟩ : syracuseStep 520607 = 780911) B780911
theorem B3306977 : Blo 203807 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B620011 : Blo 203807 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B248117903 : Blo 203807 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B8846279 : Blo 203807 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B21299159 : Blo 203807 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B688391 : Blo 203807 688391 := bstep (se 1 (by rfl) ⟨516293, by rfl⟩ : syracuseStep 688391 = 1032587) B1032587
theorem B689255 : Blo 203807 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B79596265 : Blo 203807 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B6098327 : Blo 203807 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B463031 : Blo 203807 463031 := bstep (se 1 (by rfl) ⟨347273, by rfl⟩ : syracuseStep 463031 = 694547) B694547
theorem B204031 : Blo 203807 204031 := bstep (se 1 (by rfl) ⟨153023, by rfl⟩ : syracuseStep 204031 = 306047) B306047
theorem B826681 : Blo 203807 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B204187 : Blo 203807 204187 := bstep (se 1 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 204187 = 306281) B306281
theorem B663815 : Blo 203807 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B205759 : Blo 203807 205759 := bstep (se 1 (by rfl) ⟨154319, by rfl⟩ : syracuseStep 205759 = 308639) B308639
theorem B2204651 : Blo 203807 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B665327 : Blo 203807 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B207359 : Blo 203807 207359 := bstep (se 1 (by rfl) ⟨155519, by rfl⟩ : syracuseStep 207359 = 311039) B311039
theorem B56797757 : Blo 203807 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B1355849 : Blo 203807 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B307577 : Blo 203807 307577 := bstep (se 2 (by rfl) ⟨115341, by rfl⟩ : syracuseStep 307577 = 230683) B230683
theorem B307691 : Blo 203807 307691 := bstep (se 1 (by rfl) ⟨230768, by rfl⟩ : syracuseStep 307691 = 461537) B461537
theorem B898553 : Blo 203807 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B3946441 : Blo 203807 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B309695 : Blo 203807 309695 := bstep (se 1 (by rfl) ⟨232271, by rfl⟩ : syracuseStep 309695 = 464543) B464543
theorem B2341547 : Blo 203807 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B310079 : Blo 203807 310079 := bstep (se 1 (by rfl) ⟨232559, by rfl⟩ : syracuseStep 310079 = 465119) B465119
theorem B311675 : Blo 203807 311675 := bstep (se 1 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 311675 = 467513) B467513
theorem B1558601 : Blo 203807 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B347071 : Blo 203807 347071 := bstep (se 1 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 347071 = 520607) B520607
theorem B3366143 : Blo 203807 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B2647727 : Blo 203807 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B2124227 : Blo 203807 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B389863 : Blo 203807 389863 := bstep (se 1 (by rfl) ⟨292397, by rfl⟩ : syracuseStep 389863 = 584795) B584795
theorem B165411935 : Blo 203807 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B5897519 : Blo 203807 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B2850527 : Blo 203807 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B458927 : Blo 203807 458927 := bstep (se 1 (by rfl) ⟨344195, by rfl⟩ : syracuseStep 458927 = 688391) B688391
theorem B1770173 : Blo 203807 1770173 := bstep (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) B663815
theorem B459503 : Blo 203807 459503 := bstep (se 1 (by rfl) ⟨344627, by rfl⟩ : syracuseStep 459503 = 689255) B689255
theorem B4065551 : Blo 203807 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B462761 : Blo 203807 462761 := bstep (se 2 (by rfl) ⟨173535, by rfl⟩ : syracuseStep 462761 = 347071) B347071
theorem B2396141 : Blo 203807 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B1416151 : Blo 203807 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B205051 : Blo 203807 205051 := bstep (se 1 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 205051 = 307577) B307577
theorem B205127 : Blo 203807 205127 := bstep (se 1 (by rfl) ⟨153845, by rfl⟩ : syracuseStep 205127 = 307691) B307691
theorem B206463 : Blo 203807 206463 := bstep (se 1 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 206463 = 309695) B309695
theorem B206719 : Blo 203807 206719 := bstep (se 1 (by rfl) ⟨155039, by rfl⟩ : syracuseStep 206719 = 310079) B310079
theorem B110274623 : Blo 203807 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B207783 : Blo 203807 207783 := bstep (se 1 (by rfl) ⟨155837, by rfl⟩ : syracuseStep 207783 = 311675) B311675
theorem B308687 : Blo 203807 308687 := bstep (se 1 (by rfl) ⟨231515, by rfl⟩ : syracuseStep 308687 = 463031) B463031
theorem B2244095 : Blo 203807 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B443551 : Blo 203807 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B37865171 : Blo 203807 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B5261921 : Blo 203807 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B903899 : Blo 203807 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B1102241 : Blo 203807 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B1561031 : Blo 203807 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B1039067 : Blo 203807 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B106128353 : Blo 203807 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B1469767 : Blo 203807 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B519817 : Blo 203807 519817 := bstep (se 2 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 519817 = 389863) B389863
theorem B1765151 : Blo 203807 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B3931679 : Blo 203807 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B1900351 : Blo 203807 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B1180115 : Blo 203807 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B591401 : Blo 203807 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B3507947 : Blo 203807 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B692711 : Blo 203807 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B693089 : Blo 203807 693089 := bstep (se 2 (by rfl) ⟨259908, by rfl⟩ : syracuseStep 693089 = 519817) B519817
theorem B205791 : Blo 203807 205791 := bstep (se 1 (by rfl) ⟨154343, by rfl⟩ : syracuseStep 205791 = 308687) B308687
theorem B10135205 : Blo 203807 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B305951 : Blo 203807 305951 := bstep (se 1 (by rfl) ⟨229463, by rfl⟩ : syracuseStep 305951 = 458927) B458927
theorem B306335 : Blo 203807 306335 := bstep (se 1 (by rfl) ⟨229751, by rfl⟩ : syracuseStep 306335 = 459503) B459503
theorem B25243447 : Blo 203807 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B602599 : Blo 203807 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B308507 : Blo 203807 308507 := bstep (se 1 (by rfl) ⟨231380, by rfl⟩ : syracuseStep 308507 = 462761) B462761
theorem B734827 : Blo 203807 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B73516415 : Blo 203807 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B1888201 : Blo 203807 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1496063 : Blo 203807 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B2710367 : Blo 203807 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B283008941 : Blo 203807 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1597427 : Blo 203807 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1040687 : Blo 203807 1040687 := bstep (se 1 (by rfl) ⟨780515, by rfl⟩ : syracuseStep 1040687 = 1561031) B1561031
theorem B1959689 : Blo 203807 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B1176767 : Blo 203807 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B2621119 : Blo 203807 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B786743 : Blo 203807 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B461807 : Blo 203807 461807 := bstep (se 1 (by rfl) ⟨346355, by rfl⟩ : syracuseStep 461807 = 692711) B692711
theorem B462059 : Blo 203807 462059 := bstep (se 1 (by rfl) ⟨346544, by rfl⟩ : syracuseStep 462059 = 693089) B693089
theorem B1577069 : Blo 203807 1577069 := bstep (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) B591401
theorem B1806911 : Blo 203807 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B33657929 : Blo 203807 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B693791 : Blo 203807 693791 := bstep (se 1 (by rfl) ⟨520343, by rfl⟩ : syracuseStep 693791 = 1040687) B1040687
theorem B6756803 : Blo 203807 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B203967 : Blo 203807 203967 := bstep (se 1 (by rfl) ⟨152975, by rfl⟩ : syracuseStep 203967 = 305951) B305951
theorem B204223 : Blo 203807 204223 := bstep (se 1 (by rfl) ⟨153167, by rfl⟩ : syracuseStep 204223 = 306335) B306335
theorem B205671 : Blo 203807 205671 := bstep (se 1 (by rfl) ⟨154253, by rfl⟩ : syracuseStep 205671 = 308507) B308507
theorem B2338631 : Blo 203807 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B997375 : Blo 203807 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B1064951 : Blo 203807 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B803465 : Blo 203807 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B3494825 : Blo 203807 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B196043773 : Blo 203807 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B2517601 : Blo 203807 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B188672627 : Blo 203807 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B1306459 : Blo 203807 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B979769 : Blo 203807 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B784511 : Blo 203807 784511 := bstep (se 1 (by rfl) ⟨588383, by rfl⟩ : syracuseStep 784511 = 1176767) B1176767
theorem B524495 : Blo 203807 524495 := bstep (se 1 (by rfl) ⟨393371, by rfl⟩ : syracuseStep 524495 = 786743) B786743
theorem B261391697 : Blo 203807 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B1051379 : Blo 203807 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B2329883 : Blo 203807 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B462527 : Blo 203807 462527 := bstep (se 1 (by rfl) ⟨346895, by rfl⟩ : syracuseStep 462527 = 693791) B693791
theorem B1741945 : Blo 203807 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B535643 : Blo 203807 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B307871 : Blo 203807 307871 := bstep (se 1 (by rfl) ⟨230903, by rfl⟩ : syracuseStep 307871 = 461807) B461807
theorem B308039 : Blo 203807 308039 := bstep (se 1 (by rfl) ⟨231029, by rfl⟩ : syracuseStep 308039 = 462059) B462059
theorem B3356801 : Blo 203807 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B4504535 : Blo 203807 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B125781751 : Blo 203807 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B1559087 : Blo 203807 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B1329833 : Blo 203807 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B709967 : Blo 203807 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B1204607 : Blo 203807 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B22438619 : Blo 203807 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B653179 : Blo 203807 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B523007 : Blo 203807 523007 := bstep (se 1 (by rfl) ⟨392255, by rfl⟩ : syracuseStep 523007 = 784511) B784511
theorem B174261131 : Blo 203807 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B886555 : Blo 203807 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B167709001 : Blo 203807 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B205247 : Blo 203807 205247 := bstep (se 1 (by rfl) ⟨153935, by rfl⟩ : syracuseStep 205247 = 307871) B307871
theorem B205359 : Blo 203807 205359 := bstep (se 1 (by rfl) ⟨154019, by rfl⟩ : syracuseStep 205359 = 308039) B308039
theorem B2237867 : Blo 203807 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B700919 : Blo 203807 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B1553255 : Blo 203807 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B308351 : Blo 203807 308351 := bstep (se 1 (by rfl) ⟨231263, by rfl⟩ : syracuseStep 308351 = 462527) B462527
theorem B473311 : Blo 203807 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B803071 : Blo 203807 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B14959079 : Blo 203807 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B870905 : Blo 203807 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B348671 : Blo 203807 348671 := bstep (se 1 (by rfl) ⟨261503, by rfl⟩ : syracuseStep 348671 = 523007) B523007
theorem B3003023 : Blo 203807 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B349663 : Blo 203807 349663 := bstep (se 1 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 349663 = 524495) B524495
theorem B1039391 : Blo 203807 1039391 := bstep (se 1 (by rfl) ⟨779543, by rfl⟩ : syracuseStep 1039391 = 1559087) B1559087
theorem B2322593 : Blo 203807 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B357095 : Blo 203807 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B1182073 : Blo 203807 1182073 := bstep (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) B886555
theorem B232447 : Blo 203807 232447 := bstep (se 1 (by rfl) ⟨174335, by rfl⟩ : syracuseStep 232447 = 348671) B348671
theorem B2002015 : Blo 203807 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B223612001 : Blo 203807 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B692927 : Blo 203807 692927 := bstep (se 1 (by rfl) ⟨519695, by rfl⟩ : syracuseStep 692927 = 1039391) B1039391
theorem B466217 : Blo 203807 466217 := bstep (se 2 (by rfl) ⟨174831, by rfl⟩ : syracuseStep 466217 = 349663) B349663
theorem B1548395 : Blo 203807 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B631081 : Blo 203807 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B467279 : Blo 203807 467279 := bstep (se 1 (by rfl) ⟨350459, by rfl⟩ : syracuseStep 467279 = 700919) B700919
theorem B238063 : Blo 203807 238063 := bstep (se 1 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 238063 = 357095) B357095
theorem B205567 : Blo 203807 205567 := bstep (se 1 (by rfl) ⟨154175, by rfl⟩ : syracuseStep 205567 = 308351) B308351
theorem B9972719 : Blo 203807 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B116174087 : Blo 203807 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B1491911 : Blo 203807 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B1035503 : Blo 203807 1035503 := bstep (se 1 (by rfl) ⟨776627, by rfl⟩ : syracuseStep 1035503 = 1553255) B1553255
theorem B1070761 : Blo 203807 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B580603 : Blo 203807 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B690335 : Blo 203807 690335 := bstep (se 1 (by rfl) ⟨517751, by rfl⟩ : syracuseStep 690335 = 1035503) B1035503
theorem B461951 : Blo 203807 461951 := bstep (se 1 (by rfl) ⟨346463, by rfl⟩ : syracuseStep 461951 = 692927) B692927
theorem B1576097 : Blo 203807 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B994607 : Blo 203807 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B149074667 : Blo 203807 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B309929 : Blo 203807 309929 := bstep (se 2 (by rfl) ⟨116223, by rfl⟩ : syracuseStep 309929 = 232447) B232447
theorem B310811 : Blo 203807 310811 := bstep (se 1 (by rfl) ⟨233108, by rfl⟩ : syracuseStep 310811 = 466217) B466217
theorem B1032263 : Blo 203807 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B311519 : Blo 203807 311519 := bstep (se 1 (by rfl) ⟨233639, by rfl⟩ : syracuseStep 311519 = 467279) B467279
theorem B77449391 : Blo 203807 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B1427681 : Blo 203807 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B774137 : Blo 203807 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B841441 : Blo 203807 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B317417 : Blo 203807 317417 := bstep (se 2 (by rfl) ⟨119031, by rfl⟩ : syracuseStep 317417 = 238063) B238063
theorem B10677413 : Blo 203807 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B6648479 : Blo 203807 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B688175 : Blo 203807 688175 := bstep (se 1 (by rfl) ⟨516131, by rfl⟩ : syracuseStep 688175 = 1032263) B1032263
theorem B460223 : Blo 203807 460223 := bstep (se 1 (by rfl) ⟨345167, by rfl⟩ : syracuseStep 460223 = 690335) B690335
theorem B951787 : Blo 203807 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B1050731 : Blo 203807 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B7118275 : Blo 203807 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B663071 : Blo 203807 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B1121921 : Blo 203807 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B4432319 : Blo 203807 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B206619 : Blo 203807 206619 := bstep (se 1 (by rfl) ⟨154964, by rfl⟩ : syracuseStep 206619 = 309929) B309929
theorem B207207 : Blo 203807 207207 := bstep (se 1 (by rfl) ⟨155405, by rfl⟩ : syracuseStep 207207 = 310811) B310811
theorem B207679 : Blo 203807 207679 := bstep (se 1 (by rfl) ⟨155759, by rfl⟩ : syracuseStep 207679 = 311519) B311519
theorem B307967 : Blo 203807 307967 := bstep (se 1 (by rfl) ⟨230975, by rfl⟩ : syracuseStep 307967 = 461951) B461951
theorem B51632927 : Blo 203807 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B516091 : Blo 203807 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B846445 : Blo 203807 846445 := bstep (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) B317417
theorem B99383111 : Blo 203807 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B458783 : Blo 203807 458783 := bstep (se 1 (by rfl) ⟨344087, by rfl⟩ : syracuseStep 458783 = 688175) B688175
theorem B2954879 : Blo 203807 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B205311 : Blo 203807 205311 := bstep (se 1 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 205311 = 307967) B307967
theorem B306815 : Blo 203807 306815 := bstep (se 1 (by rfl) ⟨230111, by rfl⟩ : syracuseStep 306815 = 460223) B460223
theorem B700487 : Blo 203807 700487 := bstep (se 1 (by rfl) ⟨525365, by rfl⟩ : syracuseStep 700487 = 1050731) B1050731
theorem B1128593 : Blo 203807 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B34421951 : Blo 203807 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B9491033 : Blo 203807 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B688121 : Blo 203807 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B1269049 : Blo 203807 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B747947 : Blo 203807 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B66255407 : Blo 203807 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B1768189 : Blo 203807 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B1969919 : Blo 203807 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B498631 : Blo 203807 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B204543 : Blo 203807 204543 := bstep (se 1 (by rfl) ⟨153407, by rfl⟩ : syracuseStep 204543 = 306815) B306815
theorem B466991 : Blo 203807 466991 := bstep (se 1 (by rfl) ⟨350243, by rfl⟩ : syracuseStep 466991 = 700487) B700487
theorem B22947967 : Blo 203807 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B305855 : Blo 203807 305855 := bstep (se 1 (by rfl) ⟨229391, by rfl⟩ : syracuseStep 305855 = 458783) B458783
theorem B25309421 : Blo 203807 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B1692065 : Blo 203807 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B2357585 : Blo 203807 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B752395 : Blo 203807 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B44170271 : Blo 203807 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B458747 : Blo 203807 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B122389157 : Blo 203807 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B1313279 : Blo 203807 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B203903 : Blo 203807 203903 := bstep (se 1 (by rfl) ⟨152927, by rfl⟩ : syracuseStep 203903 = 305855) B305855
theorem B664841 : Blo 203807 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B305831 : Blo 203807 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B1128043 : Blo 203807 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B311327 : Blo 203807 311327 := bstep (se 1 (by rfl) ⟨233495, by rfl⟩ : syracuseStep 311327 = 466991) B466991
theorem B1003193 : Blo 203807 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B29446847 : Blo 203807 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B16872947 : Blo 203807 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B1571723 : Blo 203807 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B81592771 : Blo 203807 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B19631231 : Blo 203807 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B203887 : Blo 203807 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B11248631 : Blo 203807 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B207551 : Blo 203807 207551 := bstep (se 1 (by rfl) ⟨155663, by rfl⟩ : syracuseStep 207551 = 311327) B311327
theorem B668795 : Blo 203807 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B443227 : Blo 203807 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B875519 : Blo 203807 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B1504057 : Blo 203807 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B1047815 : Blo 203807 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B108790361 : Blo 203807 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B590969 : Blo 203807 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B2005409 : Blo 203807 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B698543 : Blo 203807 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B13087487 : Blo 203807 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B1783453 : Blo 203807 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B583679 : Blo 203807 583679 := bstep (se 1 (by rfl) ⟨437759, by rfl⟩ : syracuseStep 583679 = 875519) B875519
theorem B7499087 : Blo 203807 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B393979 : Blo 203807 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B5347757 : Blo 203807 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B465695 : Blo 203807 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B8724991 : Blo 203807 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B72526907 : Blo 203807 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B2377937 : Blo 203807 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B4999391 : Blo 203807 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B389119 : Blo 203807 389119 := bstep (se 1 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 389119 = 583679) B583679
theorem B11633321 : Blo 203807 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B525305 : Blo 203807 525305 := bstep (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) B393979
theorem B1585291 : Blo 203807 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B310463 : Blo 203807 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B48351271 : Blo 203807 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B3332927 : Blo 203807 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B3565171 : Blo 203807 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B518825 : Blo 203807 518825 := bstep (se 2 (by rfl) ⟨194559, by rfl⟩ : syracuseStep 518825 = 389119) B389119
theorem B4753561 : Blo 203807 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B206975 : Blo 203807 206975 := bstep (se 1 (by rfl) ⟨155231, by rfl⟩ : syracuseStep 206975 = 310463) B310463
theorem B64468361 : Blo 203807 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B2113721 : Blo 203807 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B345883 : Blo 203807 345883 := bstep (se 1 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 345883 = 518825) B518825
theorem B7755547 : Blo 203807 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B350203 : Blo 203807 350203 := bstep (se 1 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 350203 = 525305) B525305
theorem B2221951 : Blo 203807 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B1409147 : Blo 203807 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B461177 : Blo 203807 461177 := bstep (se 2 (by rfl) ⟨172941, by rfl⟩ : syracuseStep 461177 = 345883) B345883
theorem B466937 : Blo 203807 466937 := bstep (se 2 (by rfl) ⟨175101, by rfl⟩ : syracuseStep 466937 = 350203) B350203
theorem B2962601 : Blo 203807 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B6338081 : Blo 203807 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B10340729 : Blo 203807 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B42978907 : Blo 203807 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B229220837 : Blo 203807 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1975067 : Blo 203807 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B307451 : Blo 203807 307451 := bstep (se 1 (by rfl) ⟨230588, by rfl⟩ : syracuseStep 307451 = 461177) B461177
theorem B6893819 : Blo 203807 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B311291 : Blo 203807 311291 := bstep (se 1 (by rfl) ⟨233468, by rfl⟩ : syracuseStep 311291 = 466937) B466937
theorem B939431 : Blo 203807 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B4225387 : Blo 203807 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B626287 : Blo 203807 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B1316711 : Blo 203807 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B204967 : Blo 203807 204967 := bstep (se 1 (by rfl) ⟨153725, by rfl⟩ : syracuseStep 204967 = 307451) B307451
theorem B4595879 : Blo 203807 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B207527 : Blo 203807 207527 := bstep (se 1 (by rfl) ⟨155645, by rfl⟩ : syracuseStep 207527 = 311291) B311291
theorem B152813891 : Blo 203807 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B5633849 : Blo 203807 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B101875927 : Blo 203807 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B835049 : Blo 203807 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B3063919 : Blo 203807 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B3755899 : Blo 203807 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B877807 : Blo 203807 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B135834569 : Blo 203807 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B4085225 : Blo 203807 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1170409 : Blo 203807 1170409 := bstep (se 2 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 1170409 = 877807) B877807
theorem B5007865 : Blo 203807 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B556699 : Blo 203807 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B2723483 : Blo 203807 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B90556379 : Blo 203807 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B1560545 : Blo 203807 1560545 := bstep (se 2 (by rfl) ⟨585204, by rfl⟩ : syracuseStep 1560545 = 1170409) B1170409
theorem B742265 : Blo 203807 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B6677153 : Blo 203807 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B494843 : Blo 203807 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B60370919 : Blo 203807 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B1815655 : Blo 203807 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1040363 : Blo 203807 1040363 := bstep (se 1 (by rfl) ⟨780272, by rfl⟩ : syracuseStep 1040363 = 1560545) B1560545
theorem B4451435 : Blo 203807 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B693575 : Blo 203807 693575 := bstep (se 1 (by rfl) ⟨520181, by rfl⟩ : syracuseStep 693575 = 1040363) B1040363
theorem B40247279 : Blo 203807 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B1319581 : Blo 203807 1319581 := bstep (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) B494843
theorem B2967623 : Blo 203807 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B2420873 : Blo 203807 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B462383 : Blo 203807 462383 := bstep (se 1 (by rfl) ⟨346787, by rfl⟩ : syracuseStep 462383 = 693575) B693575
theorem B1613915 : Blo 203807 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B1978415 : Blo 203807 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B1759441 : Blo 203807 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B26831519 : Blo 203807 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1318943 : Blo 203807 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B308255 : Blo 203807 308255 := bstep (se 1 (by rfl) ⟨231191, by rfl⟩ : syracuseStep 308255 = 462383) B462383
theorem B2345921 : Blo 203807 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B1075943 : Blo 203807 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B17887679 : Blo 203807 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B205503 : Blo 203807 205503 := bstep (se 1 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 205503 = 308255) B308255
theorem B1563947 : Blo 203807 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B879295 : Blo 203807 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B717295 : Blo 203807 717295 := bstep (se 1 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 717295 = 1075943) B1075943
theorem B11925119 : Blo 203807 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B956393 : Blo 203807 956393 := bstep (se 2 (by rfl) ⟨358647, by rfl⟩ : syracuseStep 956393 = 717295) B717295
theorem B7950079 : Blo 203807 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B1172393 : Blo 203807 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B1042631 : Blo 203807 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B695087 : Blo 203807 695087 := bstep (se 1 (by rfl) ⟨521315, by rfl⟩ : syracuseStep 695087 = 1042631) B1042631
theorem B637595 : Blo 203807 637595 := bstep (se 1 (by rfl) ⟨478196, by rfl⟩ : syracuseStep 637595 = 956393) B956393
theorem B10600105 : Blo 203807 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B781595 : Blo 203807 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B463391 : Blo 203807 463391 := bstep (se 1 (by rfl) ⟨347543, by rfl⟩ : syracuseStep 463391 = 695087) B695087
theorem B14133473 : Blo 203807 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B521063 : Blo 203807 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B425063 : Blo 203807 425063 := bstep (se 1 (by rfl) ⟨318797, by rfl⟩ : syracuseStep 425063 = 637595) B637595
theorem B308927 : Blo 203807 308927 := bstep (se 1 (by rfl) ⟨231695, by rfl⟩ : syracuseStep 308927 = 463391) B463391
theorem B9422315 : Blo 203807 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B347375 : Blo 203807 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B283375 : Blo 203807 283375 := bstep (se 1 (by rfl) ⟨212531, by rfl⟩ : syracuseStep 283375 = 425063) B425063
theorem B231583 : Blo 203807 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B205951 : Blo 203807 205951 := bstep (se 1 (by rfl) ⟨154463, by rfl⟩ : syracuseStep 205951 = 308927) B308927
theorem B377833 : Blo 203807 377833 := bstep (se 2 (by rfl) ⟨141687, by rfl⟩ : syracuseStep 377833 = 283375) B283375
theorem B6281543 : Blo 203807 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B503777 : Blo 203807 503777 := bstep (se 2 (by rfl) ⟨188916, by rfl⟩ : syracuseStep 503777 = 377833) B377833
theorem B308777 : Blo 203807 308777 := bstep (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) B231583
theorem B4187695 : Blo 203807 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B205851 : Blo 203807 205851 := bstep (se 1 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 205851 = 308777) B308777
theorem B5583593 : Blo 203807 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B1343405 : Blo 203807 1343405 := bstep (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) B503777
theorem B3582413 : Blo 203807 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B3722395 : Blo 203807 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 203807 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B2388275 : Blo 203807 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1592183 : Blo 203807 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B3308795 : Blo 203807 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 203807 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B4245821 : Blo 203807 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B2830547 : Blo 203807 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1470575 : Blo 203807 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B1887031 : Blo 203807 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B3921533 : Blo 203807 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B2516041 : Blo 203807 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B2614355 : Blo 203807 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B1742903 : Blo 203807 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B13418885 : Blo 203807 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B8945923 : Blo 203807 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B1161935 : Blo 203807 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B11927897 : Blo 203807 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B774623 : Blo 203807 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B7951931 : Blo 203807 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B516415 : Blo 203807 516415 := bstep (se 1 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 516415 = 774623) B774623
theorem B688553 : Blo 203807 688553 := bstep (se 2 (by rfl) ⟨258207, by rfl⟩ : syracuseStep 688553 = 516415) B516415
theorem B5301287 : Blo 203807 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B459035 : Blo 203807 459035 := bstep (se 1 (by rfl) ⟨344276, by rfl⟩ : syracuseStep 459035 = 688553) B688553
theorem B3534191 : Blo 203807 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B306023 : Blo 203807 306023 := bstep (se 1 (by rfl) ⟨229517, by rfl⟩ : syracuseStep 306023 = 459035) B459035
theorem B2356127 : Blo 203807 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B204015 : Blo 203807 204015 := bstep (se 1 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 204015 = 306023) B306023
theorem B1570751 : Blo 203807 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B1047167 : Blo 203807 1047167 := bstep (se 1 (by rfl) ⟨785375, by rfl⟩ : syracuseStep 1047167 = 1570751) B1570751
theorem B698111 : Blo 203807 698111 := bstep (se 1 (by rfl) ⟨523583, by rfl⟩ : syracuseStep 698111 = 1047167) B1047167
theorem B465407 : Blo 203807 465407 := bstep (se 1 (by rfl) ⟨349055, by rfl⟩ : syracuseStep 465407 = 698111) B698111
theorem B310271 : Blo 203807 310271 := bstep (se 1 (by rfl) ⟨232703, by rfl⟩ : syracuseStep 310271 = 465407) B465407
theorem B206847 : Blo 203807 206847 := bstep (se 1 (by rfl) ⟨155135, by rfl⟩ : syracuseStep 206847 = 310271) B310271

theorem C0 (j : ℕ) (h1 : 50951 ≤ j) (h2 : j ≤ 51650) : Blo 203807 (4 * j + 3) := by
  interval_cases j
  · exact B203807
  · exact B203811
  · exact B203815
  · exact B203819
  · exact B203823
  · exact B203827
  · exact B203831
  · exact B203835
  · exact B203839
  · exact B203843
  · exact B203847
  · exact B203851
  · exact B203855
  · exact B203859
  · exact B203863
  · exact B203867
  · exact B203871
  · exact B203875
  · exact B203879
  · exact B203883
  · exact B203887
  · exact B203891
  · exact B203895
  · exact B203899
  · exact B203903
  · exact B203907
  · exact B203911
  · exact B203915
  · exact B203919
  · exact B203923
  · exact B203927
  · exact B203931
  · exact B203935
  · exact B203939
  · exact B203943
  · exact B203947
  · exact B203951
  · exact B203955
  · exact B203959
  · exact B203963
  · exact B203967
  · exact B203971
  · exact B203975
  · exact B203979
  · exact B203983
  · exact B203987
  · exact B203991
  · exact B203995
  · exact B203999
  · exact B204003
  · exact B204007
  · exact B204011
  · exact B204015
  · exact B204019
  · exact B204023
  · exact B204027
  · exact B204031
  · exact B204035
  · exact B204039
  · exact B204043
  · exact B204047
  · exact B204051
  · exact B204055
  · exact B204059
  · exact B204063
  · exact B204067
  · exact B204071
  · exact B204075
  · exact B204079
  · exact B204083
  · exact B204087
  · exact B204091
  · exact B204095
  · exact B204099
  · exact B204103
  · exact B204107
  · exact B204111
  · exact B204115
  · exact B204119
  · exact B204123
  · exact B204127
  · exact B204131
  · exact B204135
  · exact B204139
  · exact B204143
  · exact B204147
  · exact B204151
  · exact B204155
  · exact B204159
  · exact B204163
  · exact B204167
  · exact B204171
  · exact B204175
  · exact B204179
  · exact B204183
  · exact B204187
  · exact B204191
  · exact B204195
  · exact B204199
  · exact B204203
  · exact B204207
  · exact B204211
  · exact B204215
  · exact B204219
  · exact B204223
  · exact B204227
  · exact B204231
  · exact B204235
  · exact B204239
  · exact B204243
  · exact B204247
  · exact B204251
  · exact B204255
  · exact B204259
  · exact B204263
  · exact B204267
  · exact B204271
  · exact B204275
  · exact B204279
  · exact B204283
  · exact B204287
  · exact B204291
  · exact B204295
  · exact B204299
  · exact B204303
  · exact B204307
  · exact B204311
  · exact B204315
  · exact B204319
  · exact B204323
  · exact B204327
  · exact B204331
  · exact B204335
  · exact B204339
  · exact B204343
  · exact B204347
  · exact B204351
  · exact B204355
  · exact B204359
  · exact B204363
  · exact B204367
  · exact B204371
  · exact B204375
  · exact B204379
  · exact B204383
  · exact B204387
  · exact B204391
  · exact B204395
  · exact B204399
  · exact B204403
  · exact B204407
  · exact B204411
  · exact B204415
  · exact B204419
  · exact B204423
  · exact B204427
  · exact B204431
  · exact B204435
  · exact B204439
  · exact B204443
  · exact B204447
  · exact B204451
  · exact B204455
  · exact B204459
  · exact B204463
  · exact B204467
  · exact B204471
  · exact B204475
  · exact B204479
  · exact B204483
  · exact B204487
  · exact B204491
  · exact B204495
  · exact B204499
  · exact B204503
  · exact B204507
  · exact B204511
  · exact B204515
  · exact B204519
  · exact B204523
  · exact B204527
  · exact B204531
  · exact B204535
  · exact B204539
  · exact B204543
  · exact B204547
  · exact B204551
  · exact B204555
  · exact B204559
  · exact B204563
  · exact B204567
  · exact B204571
  · exact B204575
  · exact B204579
  · exact B204583
  · exact B204587
  · exact B204591
  · exact B204595
  · exact B204599
  · exact B204603
  · exact B204607
  · exact B204611
  · exact B204615
  · exact B204619
  · exact B204623
  · exact B204627
  · exact B204631
  · exact B204635
  · exact B204639
  · exact B204643
  · exact B204647
  · exact B204651
  · exact B204655
  · exact B204659
  · exact B204663
  · exact B204667
  · exact B204671
  · exact B204675
  · exact B204679
  · exact B204683
  · exact B204687
  · exact B204691
  · exact B204695
  · exact B204699
  · exact B204703
  · exact B204707
  · exact B204711
  · exact B204715
  · exact B204719
  · exact B204723
  · exact B204727
  · exact B204731
  · exact B204735
  · exact B204739
  · exact B204743
  · exact B204747
  · exact B204751
  · exact B204755
  · exact B204759
  · exact B204763
  · exact B204767
  · exact B204771
  · exact B204775
  · exact B204779
  · exact B204783
  · exact B204787
  · exact B204791
  · exact B204795
  · exact B204799
  · exact B204803
  · exact B204807
  · exact B204811
  · exact B204815
  · exact B204819
  · exact B204823
  · exact B204827
  · exact B204831
  · exact B204835
  · exact B204839
  · exact B204843
  · exact B204847
  · exact B204851
  · exact B204855
  · exact B204859
  · exact B204863
  · exact B204867
  · exact B204871
  · exact B204875
  · exact B204879
  · exact B204883
  · exact B204887
  · exact B204891
  · exact B204895
  · exact B204899
  · exact B204903
  · exact B204907
  · exact B204911
  · exact B204915
  · exact B204919
  · exact B204923
  · exact B204927
  · exact B204931
  · exact B204935
  · exact B204939
  · exact B204943
  · exact B204947
  · exact B204951
  · exact B204955
  · exact B204959
  · exact B204963
  · exact B204967
  · exact B204971
  · exact B204975
  · exact B204979
  · exact B204983
  · exact B204987
  · exact B204991
  · exact B204995
  · exact B204999
  · exact B205003
  · exact B205007
  · exact B205011
  · exact B205015
  · exact B205019
  · exact B205023
  · exact B205027
  · exact B205031
  · exact B205035
  · exact B205039
  · exact B205043
  · exact B205047
  · exact B205051
  · exact B205055
  · exact B205059
  · exact B205063
  · exact B205067
  · exact B205071
  · exact B205075
  · exact B205079
  · exact B205083
  · exact B205087
  · exact B205091
  · exact B205095
  · exact B205099
  · exact B205103
  · exact B205107
  · exact B205111
  · exact B205115
  · exact B205119
  · exact B205123
  · exact B205127
  · exact B205131
  · exact B205135
  · exact B205139
  · exact B205143
  · exact B205147
  · exact B205151
  · exact B205155
  · exact B205159
  · exact B205163
  · exact B205167
  · exact B205171
  · exact B205175
  · exact B205179
  · exact B205183
  · exact B205187
  · exact B205191
  · exact B205195
  · exact B205199
  · exact B205203
  · exact B205207
  · exact B205211
  · exact B205215
  · exact B205219
  · exact B205223
  · exact B205227
  · exact B205231
  · exact B205235
  · exact B205239
  · exact B205243
  · exact B205247
  · exact B205251
  · exact B205255
  · exact B205259
  · exact B205263
  · exact B205267
  · exact B205271
  · exact B205275
  · exact B205279
  · exact B205283
  · exact B205287
  · exact B205291
  · exact B205295
  · exact B205299
  · exact B205303
  · exact B205307
  · exact B205311
  · exact B205315
  · exact B205319
  · exact B205323
  · exact B205327
  · exact B205331
  · exact B205335
  · exact B205339
  · exact B205343
  · exact B205347
  · exact B205351
  · exact B205355
  · exact B205359
  · exact B205363
  · exact B205367
  · exact B205371
  · exact B205375
  · exact B205379
  · exact B205383
  · exact B205387
  · exact B205391
  · exact B205395
  · exact B205399
  · exact B205403
  · exact B205407
  · exact B205411
  · exact B205415
  · exact B205419
  · exact B205423
  · exact B205427
  · exact B205431
  · exact B205435
  · exact B205439
  · exact B205443
  · exact B205447
  · exact B205451
  · exact B205455
  · exact B205459
  · exact B205463
  · exact B205467
  · exact B205471
  · exact B205475
  · exact B205479
  · exact B205483
  · exact B205487
  · exact B205491
  · exact B205495
  · exact B205499
  · exact B205503
  · exact B205507
  · exact B205511
  · exact B205515
  · exact B205519
  · exact B205523
  · exact B205527
  · exact B205531
  · exact B205535
  · exact B205539
  · exact B205543
  · exact B205547
  · exact B205551
  · exact B205555
  · exact B205559
  · exact B205563
  · exact B205567
  · exact B205571
  · exact B205575
  · exact B205579
  · exact B205583
  · exact B205587
  · exact B205591
  · exact B205595
  · exact B205599
  · exact B205603
  · exact B205607
  · exact B205611
  · exact B205615
  · exact B205619
  · exact B205623
  · exact B205627
  · exact B205631
  · exact B205635
  · exact B205639
  · exact B205643
  · exact B205647
  · exact B205651
  · exact B205655
  · exact B205659
  · exact B205663
  · exact B205667
  · exact B205671
  · exact B205675
  · exact B205679
  · exact B205683
  · exact B205687
  · exact B205691
  · exact B205695
  · exact B205699
  · exact B205703
  · exact B205707
  · exact B205711
  · exact B205715
  · exact B205719
  · exact B205723
  · exact B205727
  · exact B205731
  · exact B205735
  · exact B205739
  · exact B205743
  · exact B205747
  · exact B205751
  · exact B205755
  · exact B205759
  · exact B205763
  · exact B205767
  · exact B205771
  · exact B205775
  · exact B205779
  · exact B205783
  · exact B205787
  · exact B205791
  · exact B205795
  · exact B205799
  · exact B205803
  · exact B205807
  · exact B205811
  · exact B205815
  · exact B205819
  · exact B205823
  · exact B205827
  · exact B205831
  · exact B205835
  · exact B205839
  · exact B205843
  · exact B205847
  · exact B205851
  · exact B205855
  · exact B205859
  · exact B205863
  · exact B205867
  · exact B205871
  · exact B205875
  · exact B205879
  · exact B205883
  · exact B205887
  · exact B205891
  · exact B205895
  · exact B205899
  · exact B205903
  · exact B205907
  · exact B205911
  · exact B205915
  · exact B205919
  · exact B205923
  · exact B205927
  · exact B205931
  · exact B205935
  · exact B205939
  · exact B205943
  · exact B205947
  · exact B205951
  · exact B205955
  · exact B205959
  · exact B205963
  · exact B205967
  · exact B205971
  · exact B205975
  · exact B205979
  · exact B205983
  · exact B205987
  · exact B205991
  · exact B205995
  · exact B205999
  · exact B206003
  · exact B206007
  · exact B206011
  · exact B206015
  · exact B206019
  · exact B206023
  · exact B206027
  · exact B206031
  · exact B206035
  · exact B206039
  · exact B206043
  · exact B206047
  · exact B206051
  · exact B206055
  · exact B206059
  · exact B206063
  · exact B206067
  · exact B206071
  · exact B206075
  · exact B206079
  · exact B206083
  · exact B206087
  · exact B206091
  · exact B206095
  · exact B206099
  · exact B206103
  · exact B206107
  · exact B206111
  · exact B206115
  · exact B206119
  · exact B206123
  · exact B206127
  · exact B206131
  · exact B206135
  · exact B206139
  · exact B206143
  · exact B206147
  · exact B206151
  · exact B206155
  · exact B206159
  · exact B206163
  · exact B206167
  · exact B206171
  · exact B206175
  · exact B206179
  · exact B206183
  · exact B206187
  · exact B206191
  · exact B206195
  · exact B206199
  · exact B206203
  · exact B206207
  · exact B206211
  · exact B206215
  · exact B206219
  · exact B206223
  · exact B206227
  · exact B206231
  · exact B206235
  · exact B206239
  · exact B206243
  · exact B206247
  · exact B206251
  · exact B206255
  · exact B206259
  · exact B206263
  · exact B206267
  · exact B206271
  · exact B206275
  · exact B206279
  · exact B206283
  · exact B206287
  · exact B206291
  · exact B206295
  · exact B206299
  · exact B206303
  · exact B206307
  · exact B206311
  · exact B206315
  · exact B206319
  · exact B206323
  · exact B206327
  · exact B206331
  · exact B206335
  · exact B206339
  · exact B206343
  · exact B206347
  · exact B206351
  · exact B206355
  · exact B206359
  · exact B206363
  · exact B206367
  · exact B206371
  · exact B206375
  · exact B206379
  · exact B206383
  · exact B206387
  · exact B206391
  · exact B206395
  · exact B206399
  · exact B206403
  · exact B206407
  · exact B206411
  · exact B206415
  · exact B206419
  · exact B206423
  · exact B206427
  · exact B206431
  · exact B206435
  · exact B206439
  · exact B206443
  · exact B206447
  · exact B206451
  · exact B206455
  · exact B206459
  · exact B206463
  · exact B206467
  · exact B206471
  · exact B206475
  · exact B206479
  · exact B206483
  · exact B206487
  · exact B206491
  · exact B206495
  · exact B206499
  · exact B206503
  · exact B206507
  · exact B206511
  · exact B206515
  · exact B206519
  · exact B206523
  · exact B206527
  · exact B206531
  · exact B206535
  · exact B206539
  · exact B206543
  · exact B206547
  · exact B206551
  · exact B206555
  · exact B206559
  · exact B206563
  · exact B206567
  · exact B206571
  · exact B206575
  · exact B206579
  · exact B206583
  · exact B206587
  · exact B206591
  · exact B206595
  · exact B206599
  · exact B206603

theorem C1 (j : ℕ) (h1 : 51651 ≤ j) (h2 : j ≤ 51951) : Blo 203807 (4 * j + 3) := by
  interval_cases j
  · exact B206607
  · exact B206611
  · exact B206615
  · exact B206619
  · exact B206623
  · exact B206627
  · exact B206631
  · exact B206635
  · exact B206639
  · exact B206643
  · exact B206647
  · exact B206651
  · exact B206655
  · exact B206659
  · exact B206663
  · exact B206667
  · exact B206671
  · exact B206675
  · exact B206679
  · exact B206683
  · exact B206687
  · exact B206691
  · exact B206695
  · exact B206699
  · exact B206703
  · exact B206707
  · exact B206711
  · exact B206715
  · exact B206719
  · exact B206723
  · exact B206727
  · exact B206731
  · exact B206735
  · exact B206739
  · exact B206743
  · exact B206747
  · exact B206751
  · exact B206755
  · exact B206759
  · exact B206763
  · exact B206767
  · exact B206771
  · exact B206775
  · exact B206779
  · exact B206783
  · exact B206787
  · exact B206791
  · exact B206795
  · exact B206799
  · exact B206803
  · exact B206807
  · exact B206811
  · exact B206815
  · exact B206819
  · exact B206823
  · exact B206827
  · exact B206831
  · exact B206835
  · exact B206839
  · exact B206843
  · exact B206847
  · exact B206851
  · exact B206855
  · exact B206859
  · exact B206863
  · exact B206867
  · exact B206871
  · exact B206875
  · exact B206879
  · exact B206883
  · exact B206887
  · exact B206891
  · exact B206895
  · exact B206899
  · exact B206903
  · exact B206907
  · exact B206911
  · exact B206915
  · exact B206919
  · exact B206923
  · exact B206927
  · exact B206931
  · exact B206935
  · exact B206939
  · exact B206943
  · exact B206947
  · exact B206951
  · exact B206955
  · exact B206959
  · exact B206963
  · exact B206967
  · exact B206971
  · exact B206975
  · exact B206979
  · exact B206983
  · exact B206987
  · exact B206991
  · exact B206995
  · exact B206999
  · exact B207003
  · exact B207007
  · exact B207011
  · exact B207015
  · exact B207019
  · exact B207023
  · exact B207027
  · exact B207031
  · exact B207035
  · exact B207039
  · exact B207043
  · exact B207047
  · exact B207051
  · exact B207055
  · exact B207059
  · exact B207063
  · exact B207067
  · exact B207071
  · exact B207075
  · exact B207079
  · exact B207083
  · exact B207087
  · exact B207091
  · exact B207095
  · exact B207099
  · exact B207103
  · exact B207107
  · exact B207111
  · exact B207115
  · exact B207119
  · exact B207123
  · exact B207127
  · exact B207131
  · exact B207135
  · exact B207139
  · exact B207143
  · exact B207147
  · exact B207151
  · exact B207155
  · exact B207159
  · exact B207163
  · exact B207167
  · exact B207171
  · exact B207175
  · exact B207179
  · exact B207183
  · exact B207187
  · exact B207191
  · exact B207195
  · exact B207199
  · exact B207203
  · exact B207207
  · exact B207211
  · exact B207215
  · exact B207219
  · exact B207223
  · exact B207227
  · exact B207231
  · exact B207235
  · exact B207239
  · exact B207243
  · exact B207247
  · exact B207251
  · exact B207255
  · exact B207259
  · exact B207263
  · exact B207267
  · exact B207271
  · exact B207275
  · exact B207279
  · exact B207283
  · exact B207287
  · exact B207291
  · exact B207295
  · exact B207299
  · exact B207303
  · exact B207307
  · exact B207311
  · exact B207315
  · exact B207319
  · exact B207323
  · exact B207327
  · exact B207331
  · exact B207335
  · exact B207339
  · exact B207343
  · exact B207347
  · exact B207351
  · exact B207355
  · exact B207359
  · exact B207363
  · exact B207367
  · exact B207371
  · exact B207375
  · exact B207379
  · exact B207383
  · exact B207387
  · exact B207391
  · exact B207395
  · exact B207399
  · exact B207403
  · exact B207407
  · exact B207411
  · exact B207415
  · exact B207419
  · exact B207423
  · exact B207427
  · exact B207431
  · exact B207435
  · exact B207439
  · exact B207443
  · exact B207447
  · exact B207451
  · exact B207455
  · exact B207459
  · exact B207463
  · exact B207467
  · exact B207471
  · exact B207475
  · exact B207479
  · exact B207483
  · exact B207487
  · exact B207491
  · exact B207495
  · exact B207499
  · exact B207503
  · exact B207507
  · exact B207511
  · exact B207515
  · exact B207519
  · exact B207523
  · exact B207527
  · exact B207531
  · exact B207535
  · exact B207539
  · exact B207543
  · exact B207547
  · exact B207551
  · exact B207555
  · exact B207559
  · exact B207563
  · exact B207567
  · exact B207571
  · exact B207575
  · exact B207579
  · exact B207583
  · exact B207587
  · exact B207591
  · exact B207595
  · exact B207599
  · exact B207603
  · exact B207607
  · exact B207611
  · exact B207615
  · exact B207619
  · exact B207623
  · exact B207627
  · exact B207631
  · exact B207635
  · exact B207639
  · exact B207643
  · exact B207647
  · exact B207651
  · exact B207655
  · exact B207659
  · exact B207663
  · exact B207667
  · exact B207671
  · exact B207675
  · exact B207679
  · exact B207683
  · exact B207687
  · exact B207691
  · exact B207695
  · exact B207699
  · exact B207703
  · exact B207707
  · exact B207711
  · exact B207715
  · exact B207719
  · exact B207723
  · exact B207727
  · exact B207731
  · exact B207735
  · exact B207739
  · exact B207743
  · exact B207747
  · exact B207751
  · exact B207755
  · exact B207759
  · exact B207763
  · exact B207767
  · exact B207771
  · exact B207775
  · exact B207779
  · exact B207783
  · exact B207787
  · exact B207791
  · exact B207795
  · exact B207799
  · exact B207803
  · exact B207807

theorem solution (m : ℕ) (hlo : 203807 ≤ m) (hhi : m ≤ 207807) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 50951 ≤ j := by omega
    have hj2 : j ≤ 51951 := by omega
    have hb : Blo 203807 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 51651 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
