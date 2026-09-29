-- Prove2me | solution 1 for syracuse_descends_range_107783_111783
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:26.750604+00:00
-- url     : https://prove2.me/submissions/a0877c84-5b07-4f00-8b6f-4e9f043015c1

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


theorem B163853 : Blo 107783 163853 := bbase (se 3 (by rfl) ⟨30722, by rfl⟩ : syracuseStep 163853 = 61445) (by norm_num)
theorem B163877 : Blo 107783 163877 := bbase (se 4 (by rfl) ⟨15363, by rfl⟩ : syracuseStep 163877 = 30727) (by norm_num)
theorem B163901 : Blo 107783 163901 := bbase (se 3 (by rfl) ⟨30731, by rfl⟩ : syracuseStep 163901 = 61463) (by norm_num)
theorem B163925 : Blo 107783 163925 := bbase (se 8 (by rfl) ⟨960, by rfl⟩ : syracuseStep 163925 = 1921) (by norm_num)
theorem B262253 : Blo 107783 262253 := bbase (se 3 (by rfl) ⟨49172, by rfl⟩ : syracuseStep 262253 = 98345) (by norm_num)
theorem B163949 : Blo 107783 163949 := bbase (se 3 (by rfl) ⟨30740, by rfl⟩ : syracuseStep 163949 = 61481) (by norm_num)
theorem B163973 : Blo 107783 163973 := bbase (se 4 (by rfl) ⟨15372, by rfl⟩ : syracuseStep 163973 = 30745) (by norm_num)
theorem B163981 : Blo 107783 163981 := bbase (se 3 (by rfl) ⟨30746, by rfl⟩ : syracuseStep 163981 = 61493) (by norm_num)
theorem B163997 : Blo 107783 163997 := bbase (se 3 (by rfl) ⟨30749, by rfl⟩ : syracuseStep 163997 = 61499) (by norm_num)
theorem B164021 : Blo 107783 164021 := bbase (se 5 (by rfl) ⟨7688, by rfl⟩ : syracuseStep 164021 = 15377) (by norm_num)
theorem B196805 : Blo 107783 196805 := bbase (se 4 (by rfl) ⟨18450, by rfl⟩ : syracuseStep 196805 = 36901) (by norm_num)
theorem B164045 : Blo 107783 164045 := bbase (se 3 (by rfl) ⟨30758, by rfl⟩ : syracuseStep 164045 = 61517) (by norm_num)
theorem B164069 : Blo 107783 164069 := bbase (se 4 (by rfl) ⟨15381, by rfl⟩ : syracuseStep 164069 = 30763) (by norm_num)
theorem B164093 : Blo 107783 164093 := bbase (se 3 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 164093 = 61535) (by norm_num)
theorem B164117 : Blo 107783 164117 := bbase (se 6 (by rfl) ⟨3846, by rfl⟩ : syracuseStep 164117 = 7693) (by norm_num)
theorem B164141 : Blo 107783 164141 := bbase (se 3 (by rfl) ⟨30776, by rfl⟩ : syracuseStep 164141 = 61553) (by norm_num)
theorem B164165 : Blo 107783 164165 := bbase (se 4 (by rfl) ⟨15390, by rfl⟩ : syracuseStep 164165 = 30781) (by norm_num)
theorem B164189 : Blo 107783 164189 := bbase (se 3 (by rfl) ⟨30785, by rfl⟩ : syracuseStep 164189 = 61571) (by norm_num)
theorem B164213 : Blo 107783 164213 := bbase (se 5 (by rfl) ⟨7697, by rfl⟩ : syracuseStep 164213 = 15395) (by norm_num)
theorem B164237 : Blo 107783 164237 := bbase (se 3 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 164237 = 61589) (by norm_num)
theorem B164261 : Blo 107783 164261 := bbase (se 4 (by rfl) ⟨15399, by rfl⟩ : syracuseStep 164261 = 30799) (by norm_num)
theorem B393653 : Blo 107783 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B164285 : Blo 107783 164285 := bbase (se 3 (by rfl) ⟨30803, by rfl⟩ : syracuseStep 164285 = 61607) (by norm_num)
theorem B164309 : Blo 107783 164309 := bbase (se 7 (by rfl) ⟨1925, by rfl⟩ : syracuseStep 164309 = 3851) (by norm_num)
theorem B164333 : Blo 107783 164333 := bbase (se 3 (by rfl) ⟨30812, by rfl⟩ : syracuseStep 164333 = 61625) (by norm_num)
theorem B262645 : Blo 107783 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B164357 : Blo 107783 164357 := bbase (se 4 (by rfl) ⟨15408, by rfl⟩ : syracuseStep 164357 = 30817) (by norm_num)
theorem B164381 : Blo 107783 164381 := bbase (se 3 (by rfl) ⟨30821, by rfl⟩ : syracuseStep 164381 = 61643) (by norm_num)
theorem B164405 : Blo 107783 164405 := bbase (se 5 (by rfl) ⟨7706, by rfl⟩ : syracuseStep 164405 = 15413) (by norm_num)
theorem B393797 : Blo 107783 393797 := bbase (se 4 (by rfl) ⟨36918, by rfl⟩ : syracuseStep 393797 = 73837) (by norm_num)
theorem B164429 : Blo 107783 164429 := bbase (se 3 (by rfl) ⟨30830, by rfl⟩ : syracuseStep 164429 = 61661) (by norm_num)
theorem B164453 : Blo 107783 164453 := bbase (se 4 (by rfl) ⟨15417, by rfl⟩ : syracuseStep 164453 = 30835) (by norm_num)
theorem B164477 : Blo 107783 164477 := bbase (se 3 (by rfl) ⟨30839, by rfl⟩ : syracuseStep 164477 = 61679) (by norm_num)
theorem B164501 : Blo 107783 164501 := bbase (se 6 (by rfl) ⟨3855, by rfl⟩ : syracuseStep 164501 = 7711) (by norm_num)
theorem B164525 : Blo 107783 164525 := bbase (se 3 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 164525 = 61697) (by norm_num)
theorem B131765 : Blo 107783 131765 := bbase (se 5 (by rfl) ⟨6176, by rfl⟩ : syracuseStep 131765 = 12353) (by norm_num)
theorem B164549 : Blo 107783 164549 := bbase (se 4 (by rfl) ⟨15426, by rfl⟩ : syracuseStep 164549 = 30853) (by norm_num)
theorem B557765 : Blo 107783 557765 := bbase (se 4 (by rfl) ⟨52290, by rfl⟩ : syracuseStep 557765 = 104581) (by norm_num)
theorem B164573 : Blo 107783 164573 := bbase (se 3 (by rfl) ⟨30857, by rfl⟩ : syracuseStep 164573 = 61715) (by norm_num)
theorem B164597 : Blo 107783 164597 := bbase (se 5 (by rfl) ⟨7715, by rfl⟩ : syracuseStep 164597 = 15431) (by norm_num)
theorem B164621 : Blo 107783 164621 := bbase (se 3 (by rfl) ⟨30866, by rfl⟩ : syracuseStep 164621 = 61733) (by norm_num)
theorem B131861 : Blo 107783 131861 := bbase (se 6 (by rfl) ⟨3090, by rfl⟩ : syracuseStep 131861 = 6181) (by norm_num)
theorem B164645 : Blo 107783 164645 := bbase (se 4 (by rfl) ⟨15435, by rfl⟩ : syracuseStep 164645 = 30871) (by norm_num)
theorem B131881 : Blo 107783 131881 := bbase (se 2 (by rfl) ⟨49455, by rfl⟩ : syracuseStep 131881 = 98911) (by norm_num)
theorem B164669 : Blo 107783 164669 := bbase (se 3 (by rfl) ⟨30875, by rfl⟩ : syracuseStep 164669 = 61751) (by norm_num)
theorem B164693 : Blo 107783 164693 := bbase (se 9 (by rfl) ⟨482, by rfl⟩ : syracuseStep 164693 = 965) (by norm_num)
theorem B394085 : Blo 107783 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B164717 : Blo 107783 164717 := bbase (se 3 (by rfl) ⟨30884, by rfl⟩ : syracuseStep 164717 = 61769) (by norm_num)
theorem B623477 : Blo 107783 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B164741 : Blo 107783 164741 := bbase (se 4 (by rfl) ⟨15444, by rfl⟩ : syracuseStep 164741 = 30889) (by norm_num)
theorem B230285 : Blo 107783 230285 := bbase (se 3 (by rfl) ⟨43178, by rfl⟩ : syracuseStep 230285 = 86357) (by norm_num)
theorem B885653 : Blo 107783 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B164765 : Blo 107783 164765 := bbase (se 3 (by rfl) ⟨30893, by rfl⟩ : syracuseStep 164765 = 61787) (by norm_num)
theorem B164789 : Blo 107783 164789 := bbase (se 5 (by rfl) ⟨7724, by rfl⟩ : syracuseStep 164789 = 15449) (by norm_num)
theorem B132025 : Blo 107783 132025 := bbase (se 2 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 132025 = 99019) (by norm_num)
theorem B164813 : Blo 107783 164813 := bbase (se 3 (by rfl) ⟨30902, by rfl⟩ : syracuseStep 164813 = 61805) (by norm_num)
theorem B164837 : Blo 107783 164837 := bbase (se 4 (by rfl) ⟨15453, by rfl⟩ : syracuseStep 164837 = 30907) (by norm_num)
theorem B164861 : Blo 107783 164861 := bbase (se 3 (by rfl) ⟨30911, by rfl⟩ : syracuseStep 164861 = 61823) (by norm_num)
theorem B164885 : Blo 107783 164885 := bbase (se 6 (by rfl) ⟨3864, by rfl⟩ : syracuseStep 164885 = 7729) (by norm_num)
theorem B164909 : Blo 107783 164909 := bbase (se 3 (by rfl) ⟨30920, by rfl⟩ : syracuseStep 164909 = 61841) (by norm_num)
theorem B164933 : Blo 107783 164933 := bbase (se 4 (by rfl) ⟨15462, by rfl⟩ : syracuseStep 164933 = 30925) (by norm_num)
theorem B164957 : Blo 107783 164957 := bbase (se 3 (by rfl) ⟨30929, by rfl⟩ : syracuseStep 164957 = 61859) (by norm_num)
theorem B197749 : Blo 107783 197749 := bbase (se 5 (by rfl) ⟨9269, by rfl⟩ : syracuseStep 197749 = 18539) (by norm_num)
theorem B164981 : Blo 107783 164981 := bbase (se 5 (by rfl) ⟨7733, by rfl⟩ : syracuseStep 164981 = 15467) (by norm_num)
theorem B165005 : Blo 107783 165005 := bbase (se 3 (by rfl) ⟨30938, by rfl⟩ : syracuseStep 165005 = 61877) (by norm_num)
theorem B165029 : Blo 107783 165029 := bbase (se 4 (by rfl) ⟨15471, by rfl⟩ : syracuseStep 165029 = 30943) (by norm_num)
theorem B165053 : Blo 107783 165053 := bbase (se 3 (by rfl) ⟨30947, by rfl⟩ : syracuseStep 165053 = 61895) (by norm_num)
theorem B165077 : Blo 107783 165077 := bbase (se 7 (by rfl) ⟨1934, by rfl⟩ : syracuseStep 165077 = 3869) (by norm_num)
theorem B165101 : Blo 107783 165101 := bbase (se 3 (by rfl) ⟨30956, by rfl⟩ : syracuseStep 165101 = 61913) (by norm_num)
theorem B165125 : Blo 107783 165125 := bbase (se 4 (by rfl) ⟨15480, by rfl⟩ : syracuseStep 165125 = 30961) (by norm_num)
theorem B165149 : Blo 107783 165149 := bbase (se 3 (by rfl) ⟨30965, by rfl⟩ : syracuseStep 165149 = 61931) (by norm_num)
theorem B787765 : Blo 107783 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B296245 : Blo 107783 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B165173 : Blo 107783 165173 := bbase (se 5 (by rfl) ⟨7742, by rfl⟩ : syracuseStep 165173 = 15485) (by norm_num)
theorem B165197 : Blo 107783 165197 := bbase (se 3 (by rfl) ⟨30974, by rfl⟩ : syracuseStep 165197 = 61949) (by norm_num)
theorem B165221 : Blo 107783 165221 := bbase (se 4 (by rfl) ⟨15489, by rfl⟩ : syracuseStep 165221 = 30979) (by norm_num)
theorem B132473 : Blo 107783 132473 := bbase (se 2 (by rfl) ⟨49677, by rfl⟩ : syracuseStep 132473 = 99355) (by norm_num)
theorem B165245 : Blo 107783 165245 := bbase (se 3 (by rfl) ⟨30983, by rfl⟩ : syracuseStep 165245 = 61967) (by norm_num)
theorem B230789 : Blo 107783 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B230797 : Blo 107783 230797 := bbase (se 3 (by rfl) ⟨43274, by rfl⟩ : syracuseStep 230797 = 86549) (by norm_num)
theorem B165269 : Blo 107783 165269 := bbase (se 6 (by rfl) ⟨3873, by rfl⟩ : syracuseStep 165269 = 7747) (by norm_num)
theorem B165293 : Blo 107783 165293 := bbase (se 3 (by rfl) ⟨30992, by rfl⟩ : syracuseStep 165293 = 61985) (by norm_num)
theorem B165317 : Blo 107783 165317 := bbase (se 4 (by rfl) ⟨15498, by rfl⟩ : syracuseStep 165317 = 30997) (by norm_num)
theorem B165341 : Blo 107783 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B165365 : Blo 107783 165365 := bbase (se 5 (by rfl) ⟨7751, by rfl⟩ : syracuseStep 165365 = 15503) (by norm_num)
theorem B165389 : Blo 107783 165389 := bbase (se 3 (by rfl) ⟨31010, by rfl⟩ : syracuseStep 165389 = 62021) (by norm_num)
theorem B165413 : Blo 107783 165413 := bbase (se 4 (by rfl) ⟨15507, by rfl⟩ : syracuseStep 165413 = 31015) (by norm_num)
theorem B165437 : Blo 107783 165437 := bbase (se 3 (by rfl) ⟨31019, by rfl⟩ : syracuseStep 165437 = 62039) (by norm_num)
theorem B165461 : Blo 107783 165461 := bbase (se 8 (by rfl) ⟨969, by rfl⟩ : syracuseStep 165461 = 1939) (by norm_num)
theorem B165485 : Blo 107783 165485 := bbase (se 3 (by rfl) ⟨31028, by rfl⟩ : syracuseStep 165485 = 62057) (by norm_num)
theorem B820853 : Blo 107783 820853 := bbase (se 5 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 820853 = 76955) (by norm_num)
theorem B165509 : Blo 107783 165509 := bbase (se 4 (by rfl) ⟨15516, by rfl⟩ : syracuseStep 165509 = 31033) (by norm_num)
theorem B165533 : Blo 107783 165533 := bbase (se 3 (by rfl) ⟨31037, by rfl⟩ : syracuseStep 165533 = 62075) (by norm_num)
theorem B165557 : Blo 107783 165557 := bbase (se 5 (by rfl) ⟨7760, by rfl⟩ : syracuseStep 165557 = 15521) (by norm_num)
theorem B165581 : Blo 107783 165581 := bbase (se 3 (by rfl) ⟨31046, by rfl⟩ : syracuseStep 165581 = 62093) (by norm_num)
theorem B165605 : Blo 107783 165605 := bbase (se 4 (by rfl) ⟨15525, by rfl⟩ : syracuseStep 165605 = 31051) (by norm_num)
theorem B165629 : Blo 107783 165629 := bbase (se 3 (by rfl) ⟨31055, by rfl⟩ : syracuseStep 165629 = 62111) (by norm_num)
theorem B165653 : Blo 107783 165653 := bbase (se 6 (by rfl) ⟨3882, by rfl⟩ : syracuseStep 165653 = 7765) (by norm_num)
theorem B165677 : Blo 107783 165677 := bbase (se 3 (by rfl) ⟨31064, by rfl⟩ : syracuseStep 165677 = 62129) (by norm_num)
theorem B165701 : Blo 107783 165701 := bbase (se 4 (by rfl) ⟨15534, by rfl⟩ : syracuseStep 165701 = 31069) (by norm_num)
theorem B165725 : Blo 107783 165725 := bbase (se 3 (by rfl) ⟨31073, by rfl⟩ : syracuseStep 165725 = 62147) (by norm_num)
theorem B165749 : Blo 107783 165749 := bbase (se 5 (by rfl) ⟨7769, by rfl⟩ : syracuseStep 165749 = 15539) (by norm_num)
theorem B526213 : Blo 107783 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B165773 : Blo 107783 165773 := bbase (se 3 (by rfl) ⟨31082, by rfl⟩ : syracuseStep 165773 = 62165) (by norm_num)
theorem B165797 : Blo 107783 165797 := bbase (se 4 (by rfl) ⟨15543, by rfl⟩ : syracuseStep 165797 = 31087) (by norm_num)
theorem B165821 : Blo 107783 165821 := bbase (se 3 (by rfl) ⟨31091, by rfl⟩ : syracuseStep 165821 = 62183) (by norm_num)
theorem B755669 : Blo 107783 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B559061 : Blo 107783 559061 := bbase (se 7 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 559061 = 13103) (by norm_num)
theorem B165845 : Blo 107783 165845 := bbase (se 7 (by rfl) ⟨1943, by rfl⟩ : syracuseStep 165845 = 3887) (by norm_num)
theorem B165869 : Blo 107783 165869 := bbase (se 3 (by rfl) ⟨31100, by rfl⟩ : syracuseStep 165869 = 62201) (by norm_num)
theorem B165893 : Blo 107783 165893 := bbase (se 4 (by rfl) ⟨15552, by rfl⟩ : syracuseStep 165893 = 31105) (by norm_num)
theorem B165917 : Blo 107783 165917 := bbase (se 3 (by rfl) ⟨31109, by rfl⟩ : syracuseStep 165917 = 62219) (by norm_num)
theorem B165941 : Blo 107783 165941 := bbase (se 5 (by rfl) ⟨7778, by rfl⟩ : syracuseStep 165941 = 15557) (by norm_num)
theorem B165965 : Blo 107783 165965 := bbase (se 3 (by rfl) ⟨31118, by rfl⟩ : syracuseStep 165965 = 62237) (by norm_num)
theorem B165989 : Blo 107783 165989 := bbase (se 4 (by rfl) ⟨15561, by rfl⟩ : syracuseStep 165989 = 31123) (by norm_num)
theorem B166013 : Blo 107783 166013 := bbase (se 3 (by rfl) ⟨31127, by rfl⟩ : syracuseStep 166013 = 62255) (by norm_num)
theorem B166037 : Blo 107783 166037 := bbase (se 6 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 166037 = 7783) (by norm_num)
theorem B166061 : Blo 107783 166061 := bbase (se 3 (by rfl) ⟨31136, by rfl⟩ : syracuseStep 166061 = 62273) (by norm_num)
theorem B166085 : Blo 107783 166085 := bbase (se 4 (by rfl) ⟨15570, by rfl⟩ : syracuseStep 166085 = 31141) (by norm_num)
theorem B166109 : Blo 107783 166109 := bbase (se 3 (by rfl) ⟨31145, by rfl⟩ : syracuseStep 166109 = 62291) (by norm_num)
theorem B166133 : Blo 107783 166133 := bbase (se 5 (by rfl) ⟨7787, by rfl⟩ : syracuseStep 166133 = 15575) (by norm_num)
theorem B166157 : Blo 107783 166157 := bbase (se 3 (by rfl) ⟨31154, by rfl⟩ : syracuseStep 166157 = 62309) (by norm_num)
theorem B166181 : Blo 107783 166181 := bbase (se 4 (by rfl) ⟨15579, by rfl⟩ : syracuseStep 166181 = 31159) (by norm_num)
theorem B166205 : Blo 107783 166205 := bbase (se 3 (by rfl) ⟨31163, by rfl⟩ : syracuseStep 166205 = 62327) (by norm_num)
theorem B166229 : Blo 107783 166229 := bbase (se 10 (by rfl) ⟨243, by rfl⟩ : syracuseStep 166229 = 487) (by norm_num)
theorem B297317 : Blo 107783 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B166253 : Blo 107783 166253 := bbase (se 3 (by rfl) ⟨31172, by rfl⟩ : syracuseStep 166253 = 62345) (by norm_num)
theorem B166277 : Blo 107783 166277 := bbase (se 4 (by rfl) ⟨15588, by rfl⟩ : syracuseStep 166277 = 31177) (by norm_num)
theorem B166301 : Blo 107783 166301 := bbase (se 3 (by rfl) ⟨31181, by rfl⟩ : syracuseStep 166301 = 62363) (by norm_num)
theorem B166325 : Blo 107783 166325 := bbase (se 5 (by rfl) ⟨7796, by rfl⟩ : syracuseStep 166325 = 15593) (by norm_num)
theorem B166349 : Blo 107783 166349 := bbase (se 3 (by rfl) ⟨31190, by rfl⟩ : syracuseStep 166349 = 62381) (by norm_num)
theorem B166373 : Blo 107783 166373 := bbase (se 4 (by rfl) ⟨15597, by rfl⟩ : syracuseStep 166373 = 31195) (by norm_num)
theorem B231925 : Blo 107783 231925 := bbase (se 5 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 231925 = 21743) (by norm_num)
theorem B166397 : Blo 107783 166397 := bbase (se 3 (by rfl) ⟨31199, by rfl⟩ : syracuseStep 166397 = 62399) (by norm_num)
theorem B166421 : Blo 107783 166421 := bbase (se 6 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 166421 = 7801) (by norm_num)
theorem B395813 : Blo 107783 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B166445 : Blo 107783 166445 := bbase (se 3 (by rfl) ⟨31208, by rfl⟩ : syracuseStep 166445 = 62417) (by norm_num)
theorem B166469 : Blo 107783 166469 := bbase (se 4 (by rfl) ⟨15606, by rfl⟩ : syracuseStep 166469 = 31213) (by norm_num)
theorem B166493 : Blo 107783 166493 := bbase (se 3 (by rfl) ⟨31217, by rfl⟩ : syracuseStep 166493 = 62435) (by norm_num)
theorem B166517 : Blo 107783 166517 := bbase (se 5 (by rfl) ⟨7805, by rfl⟩ : syracuseStep 166517 = 15611) (by norm_num)
theorem B166541 : Blo 107783 166541 := bbase (se 3 (by rfl) ⟨31226, by rfl⟩ : syracuseStep 166541 = 62453) (by norm_num)
theorem B166565 : Blo 107783 166565 := bbase (se 4 (by rfl) ⟨15615, by rfl⟩ : syracuseStep 166565 = 31231) (by norm_num)
theorem B199349 : Blo 107783 199349 := bbase (se 5 (by rfl) ⟨9344, by rfl⟩ : syracuseStep 199349 = 18689) (by norm_num)
theorem B133817 : Blo 107783 133817 := bbase (se 2 (by rfl) ⟨50181, by rfl⟩ : syracuseStep 133817 = 100363) (by norm_num)
theorem B166589 : Blo 107783 166589 := bbase (se 3 (by rfl) ⟨31235, by rfl⟩ : syracuseStep 166589 = 62471) (by norm_num)
theorem B166613 : Blo 107783 166613 := bbase (se 7 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 166613 = 3905) (by norm_num)
theorem B166637 : Blo 107783 166637 := bbase (se 3 (by rfl) ⟨31244, by rfl⟩ : syracuseStep 166637 = 62489) (by norm_num)
theorem B166661 : Blo 107783 166661 := bbase (se 4 (by rfl) ⟨15624, by rfl⟩ : syracuseStep 166661 = 31249) (by norm_num)
theorem B166685 : Blo 107783 166685 := bbase (se 3 (by rfl) ⟨31253, by rfl⟩ : syracuseStep 166685 = 62507) (by norm_num)
theorem B166709 : Blo 107783 166709 := bbase (se 5 (by rfl) ⟨7814, by rfl⟩ : syracuseStep 166709 = 15629) (by norm_num)
theorem B166733 : Blo 107783 166733 := bbase (se 3 (by rfl) ⟨31262, by rfl⟩ : syracuseStep 166733 = 62525) (by norm_num)
theorem B166757 : Blo 107783 166757 := bbase (se 4 (by rfl) ⟨15633, by rfl⟩ : syracuseStep 166757 = 31267) (by norm_num)
theorem B232301 : Blo 107783 232301 := bbase (se 3 (by rfl) ⟨43556, by rfl⟩ : syracuseStep 232301 = 87113) (by norm_num)
theorem B166781 : Blo 107783 166781 := bbase (se 3 (by rfl) ⟨31271, by rfl⟩ : syracuseStep 166781 = 62543) (by norm_num)
theorem B166805 : Blo 107783 166805 := bbase (se 6 (by rfl) ⟨3909, by rfl⟩ : syracuseStep 166805 = 7819) (by norm_num)
theorem B166829 : Blo 107783 166829 := bbase (se 3 (by rfl) ⟨31280, by rfl⟩ : syracuseStep 166829 = 62561) (by norm_num)
theorem B166853 : Blo 107783 166853 := bbase (se 4 (by rfl) ⟨15642, by rfl⟩ : syracuseStep 166853 = 31285) (by norm_num)
theorem B166877 : Blo 107783 166877 := bbase (se 3 (by rfl) ⟨31289, by rfl⟩ : syracuseStep 166877 = 62579) (by norm_num)
theorem B166901 : Blo 107783 166901 := bbase (se 5 (by rfl) ⟨7823, by rfl⟩ : syracuseStep 166901 = 15647) (by norm_num)
theorem B134149 : Blo 107783 134149 := bbase (se 4 (by rfl) ⟨12576, by rfl⟩ : syracuseStep 134149 = 25153) (by norm_num)
theorem B166925 : Blo 107783 166925 := bbase (se 3 (by rfl) ⟨31298, by rfl⟩ : syracuseStep 166925 = 62597) (by norm_num)
theorem B166949 : Blo 107783 166949 := bbase (se 4 (by rfl) ⟨15651, by rfl⟩ : syracuseStep 166949 = 31303) (by norm_num)
theorem B166973 : Blo 107783 166973 := bbase (se 3 (by rfl) ⟨31307, by rfl⟩ : syracuseStep 166973 = 62615) (by norm_num)
theorem B166997 : Blo 107783 166997 := bbase (se 8 (by rfl) ⟨978, by rfl⟩ : syracuseStep 166997 = 1957) (by norm_num)
theorem B167021 : Blo 107783 167021 := bbase (se 3 (by rfl) ⟨31316, by rfl⟩ : syracuseStep 167021 = 62633) (by norm_num)
theorem B167045 : Blo 107783 167045 := bbase (se 4 (by rfl) ⟨15660, by rfl⟩ : syracuseStep 167045 = 31321) (by norm_num)
theorem B134293 : Blo 107783 134293 := bbase (se 6 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 134293 = 6295) (by norm_num)
theorem B167069 : Blo 107783 167069 := bbase (se 3 (by rfl) ⟨31325, by rfl⟩ : syracuseStep 167069 = 62651) (by norm_num)
theorem B167093 : Blo 107783 167093 := bbase (se 5 (by rfl) ⟨7832, by rfl⟩ : syracuseStep 167093 = 15665) (by norm_num)
theorem B298181 : Blo 107783 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B167117 : Blo 107783 167117 := bbase (se 3 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 167117 = 62669) (by norm_num)
theorem B560357 : Blo 107783 560357 := bbase (se 4 (by rfl) ⟨52533, by rfl⟩ : syracuseStep 560357 = 105067) (by norm_num)
theorem B167141 : Blo 107783 167141 := bbase (se 4 (by rfl) ⟨15669, by rfl⟩ : syracuseStep 167141 = 31339) (by norm_num)
theorem B167165 : Blo 107783 167165 := bbase (se 3 (by rfl) ⟨31343, by rfl⟩ : syracuseStep 167165 = 62687) (by norm_num)
theorem B363797 : Blo 107783 363797 := bbase (se 6 (by rfl) ⟨8526, by rfl⟩ : syracuseStep 363797 = 17053) (by norm_num)
theorem B167189 : Blo 107783 167189 := bbase (se 6 (by rfl) ⟨3918, by rfl⟩ : syracuseStep 167189 = 7837) (by norm_num)
theorem B167213 : Blo 107783 167213 := bbase (se 3 (by rfl) ⟨31352, by rfl⟩ : syracuseStep 167213 = 62705) (by norm_num)
theorem B167237 : Blo 107783 167237 := bbase (se 4 (by rfl) ⟨15678, by rfl⟩ : syracuseStep 167237 = 31357) (by norm_num)
theorem B167261 : Blo 107783 167261 := bbase (se 3 (by rfl) ⟨31361, by rfl⟩ : syracuseStep 167261 = 62723) (by norm_num)
theorem B167285 : Blo 107783 167285 := bbase (se 5 (by rfl) ⟨7841, by rfl⟩ : syracuseStep 167285 = 15683) (by norm_num)
theorem B167309 : Blo 107783 167309 := bbase (se 3 (by rfl) ⟨31370, by rfl⟩ : syracuseStep 167309 = 62741) (by norm_num)
theorem B167333 : Blo 107783 167333 := bbase (se 4 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 167333 = 31375) (by norm_num)
theorem B167357 : Blo 107783 167357 := bbase (se 3 (by rfl) ⟨31379, by rfl⟩ : syracuseStep 167357 = 62759) (by norm_num)
theorem B462277 : Blo 107783 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B167381 : Blo 107783 167381 := bbase (se 7 (by rfl) ⟨1961, by rfl⟩ : syracuseStep 167381 = 3923) (by norm_num)
theorem B167405 : Blo 107783 167405 := bbase (se 3 (by rfl) ⟨31388, by rfl⟩ : syracuseStep 167405 = 62777) (by norm_num)
theorem B167429 : Blo 107783 167429 := bbase (se 4 (by rfl) ⟨15696, by rfl⟩ : syracuseStep 167429 = 31393) (by norm_num)
theorem B200213 : Blo 107783 200213 := bbase (se 6 (by rfl) ⟨4692, by rfl⟩ : syracuseStep 200213 = 9385) (by norm_num)
theorem B167453 : Blo 107783 167453 := bbase (se 3 (by rfl) ⟨31397, by rfl⟩ : syracuseStep 167453 = 62795) (by norm_num)
theorem B167477 : Blo 107783 167477 := bbase (se 5 (by rfl) ⟨7850, by rfl⟩ : syracuseStep 167477 = 15701) (by norm_num)
theorem B265789 : Blo 107783 265789 := bbase (se 3 (by rfl) ⟨49835, by rfl⟩ : syracuseStep 265789 = 99671) (by norm_num)
theorem B167501 : Blo 107783 167501 := bbase (se 3 (by rfl) ⟨31406, by rfl⟩ : syracuseStep 167501 = 62813) (by norm_num)
theorem B167525 : Blo 107783 167525 := bbase (se 4 (by rfl) ⟨15705, by rfl⟩ : syracuseStep 167525 = 31411) (by norm_num)
theorem B265837 : Blo 107783 265837 := bbase (se 3 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 265837 = 99689) (by norm_num)
theorem B167549 : Blo 107783 167549 := bbase (se 3 (by rfl) ⟨31415, by rfl⟩ : syracuseStep 167549 = 62831) (by norm_num)
theorem B167573 : Blo 107783 167573 := bbase (se 6 (by rfl) ⟨3927, by rfl⟩ : syracuseStep 167573 = 7855) (by norm_num)
theorem B167597 : Blo 107783 167597 := bbase (se 3 (by rfl) ⟨31424, by rfl⟩ : syracuseStep 167597 = 62849) (by norm_num)
theorem B364229 : Blo 107783 364229 := bbase (se 4 (by rfl) ⟨34146, by rfl⟩ : syracuseStep 364229 = 68293) (by norm_num)
theorem B167621 : Blo 107783 167621 := bbase (se 4 (by rfl) ⟨15714, by rfl⟩ : syracuseStep 167621 = 31429) (by norm_num)
theorem B167645 : Blo 107783 167645 := bbase (se 3 (by rfl) ⟨31433, by rfl⟩ : syracuseStep 167645 = 62867) (by norm_num)
theorem B167669 : Blo 107783 167669 := bbase (se 5 (by rfl) ⟨7859, by rfl⟩ : syracuseStep 167669 = 15719) (by norm_num)
theorem B15109973 : Blo 107783 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B364661 : Blo 107783 364661 := bbase (se 5 (by rfl) ⟨17093, by rfl⟩ : syracuseStep 364661 = 34187) (by norm_num)
theorem B266453 : Blo 107783 266453 := bbase (se 7 (by rfl) ⟨3122, by rfl⟩ : syracuseStep 266453 = 6245) (by norm_num)
theorem B168293 : Blo 107783 168293 := bbase (se 4 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 168293 = 31555) (by norm_num)
theorem B233941 : Blo 107783 233941 := bbase (se 7 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 233941 = 5483) (by norm_num)
theorem B561653 : Blo 107783 561653 := bbase (se 5 (by rfl) ⟨26327, by rfl⟩ : syracuseStep 561653 = 52655) (by norm_num)
theorem B365093 : Blo 107783 365093 := bbase (se 4 (by rfl) ⟨34227, by rfl⟩ : syracuseStep 365093 = 68455) (by norm_num)
theorem B266797 : Blo 107783 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B168517 : Blo 107783 168517 := bbase (se 4 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 168517 = 31597) (by norm_num)
theorem B267029 : Blo 107783 267029 := bbase (se 6 (by rfl) ⟨6258, by rfl⟩ : syracuseStep 267029 = 12517) (by norm_num)
theorem B2036501 : Blo 107783 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B463765 : Blo 107783 463765 := bbase (se 6 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 463765 = 21739) (by norm_num)
theorem B463781 : Blo 107783 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B365525 : Blo 107783 365525 := bbase (se 7 (by rfl) ⟨4283, by rfl⟩ : syracuseStep 365525 = 8567) (by norm_num)
theorem B267221 : Blo 107783 267221 := bbase (se 7 (by rfl) ⟨3131, by rfl⟩ : syracuseStep 267221 = 6263) (by norm_num)
theorem B300277 : Blo 107783 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B267509 : Blo 107783 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B136505 : Blo 107783 136505 := bbase (se 2 (by rfl) ⟨51189, by rfl⟩ : syracuseStep 136505 = 102379) (by norm_num)
theorem B529733 : Blo 107783 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B234829 : Blo 107783 234829 := bbase (se 3 (by rfl) ⟨44030, by rfl⟩ : syracuseStep 234829 = 88061) (by norm_num)
theorem B136561 : Blo 107783 136561 := bbase (se 2 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 136561 = 102421) (by norm_num)
theorem B365957 : Blo 107783 365957 := bbase (se 4 (by rfl) ⟨34308, by rfl⟩ : syracuseStep 365957 = 68617) (by norm_num)
theorem B136657 : Blo 107783 136657 := bbase (se 2 (by rfl) ⟨51246, by rfl⟩ : syracuseStep 136657 = 102493) (by norm_num)
theorem B136829 : Blo 107783 136829 := bbase (se 3 (by rfl) ⟨25655, by rfl⟩ : syracuseStep 136829 = 51311) (by norm_num)
theorem B136885 : Blo 107783 136885 := bbase (se 5 (by rfl) ⟨6416, by rfl⟩ : syracuseStep 136885 = 12833) (by norm_num)
theorem B169661 : Blo 107783 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B235229 : Blo 107783 235229 := bbase (se 3 (by rfl) ⟨44105, by rfl⟩ : syracuseStep 235229 = 88211) (by norm_num)
theorem B562949 : Blo 107783 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B136981 : Blo 107783 136981 := bbase (se 6 (by rfl) ⟨3210, by rfl⟩ : syracuseStep 136981 = 6421) (by norm_num)
theorem B366389 : Blo 107783 366389 := bbase (se 5 (by rfl) ⟨17174, by rfl⟩ : syracuseStep 366389 = 34349) (by norm_num)
theorem B235325 : Blo 107783 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B137153 : Blo 107783 137153 := bbase (se 2 (by rfl) ⟨51432, by rfl⟩ : syracuseStep 137153 = 102865) (by norm_num)
theorem B137209 : Blo 107783 137209 := bbase (se 2 (by rfl) ⟨51453, by rfl⟩ : syracuseStep 137209 = 102907) (by norm_num)
theorem B137305 : Blo 107783 137305 := bbase (se 2 (by rfl) ⟨51489, by rfl⟩ : syracuseStep 137305 = 102979) (by norm_num)
theorem B366821 : Blo 107783 366821 := bbase (se 4 (by rfl) ⟨34389, by rfl⟩ : syracuseStep 366821 = 68779) (by norm_num)
theorem B137477 : Blo 107783 137477 := bbase (se 4 (by rfl) ⟨12888, by rfl⟩ : syracuseStep 137477 = 25777) (by norm_num)
theorem B137533 : Blo 107783 137533 := bbase (se 3 (by rfl) ⟨25787, by rfl⟩ : syracuseStep 137533 = 51575) (by norm_num)
theorem B137629 : Blo 107783 137629 := bbase (se 3 (by rfl) ⟨25805, by rfl⟩ : syracuseStep 137629 = 51611) (by norm_num)
theorem B530981 : Blo 107783 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B137801 : Blo 107783 137801 := bbase (se 2 (by rfl) ⟨51675, by rfl⟩ : syracuseStep 137801 = 103351) (by norm_num)
theorem B137857 : Blo 107783 137857 := bbase (se 2 (by rfl) ⟨51696, by rfl⟩ : syracuseStep 137857 = 103393) (by norm_num)
theorem B367253 : Blo 107783 367253 := bbase (se 6 (by rfl) ⟨8607, by rfl⟩ : syracuseStep 367253 = 17215) (by norm_num)
theorem B498325 : Blo 107783 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B236189 : Blo 107783 236189 := bbase (se 3 (by rfl) ⟨44285, by rfl⟩ : syracuseStep 236189 = 88571) (by norm_num)
theorem B301781 : Blo 107783 301781 := bbase (se 7 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 301781 = 7073) (by norm_num)
theorem B137953 : Blo 107783 137953 := bbase (se 2 (by rfl) ⟨51732, by rfl⟩ : syracuseStep 137953 = 103465) (by norm_num)
theorem B236333 : Blo 107783 236333 := bbase (se 3 (by rfl) ⟨44312, by rfl⟩ : syracuseStep 236333 = 88625) (by norm_num)
theorem B170837 : Blo 107783 170837 := bbase (se 9 (by rfl) ⟨500, by rfl⟩ : syracuseStep 170837 = 1001) (by norm_num)
theorem B138125 : Blo 107783 138125 := bbase (se 3 (by rfl) ⟨25898, by rfl⟩ : syracuseStep 138125 = 51797) (by norm_num)
theorem B138181 : Blo 107783 138181 := bbase (se 4 (by rfl) ⟨12954, by rfl⟩ : syracuseStep 138181 = 25909) (by norm_num)
theorem B564245 : Blo 107783 564245 := bbase (se 6 (by rfl) ⟨13224, by rfl⟩ : syracuseStep 564245 = 26449) (by norm_num)
theorem B138277 : Blo 107783 138277 := bbase (se 4 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 138277 = 25927) (by norm_num)
theorem B367685 : Blo 107783 367685 := bbase (se 4 (by rfl) ⟨34470, by rfl⟩ : syracuseStep 367685 = 68941) (by norm_num)
theorem B466037 : Blo 107783 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B138449 : Blo 107783 138449 := bbase (se 2 (by rfl) ⟨51918, by rfl⟩ : syracuseStep 138449 = 103837) (by norm_num)
theorem B269525 : Blo 107783 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B138505 : Blo 107783 138505 := bbase (se 2 (by rfl) ⟨51939, by rfl⟩ : syracuseStep 138505 = 103879) (by norm_num)
theorem B138601 : Blo 107783 138601 := bbase (se 2 (by rfl) ⟨51975, by rfl⟩ : syracuseStep 138601 = 103951) (by norm_num)
theorem B368117 : Blo 107783 368117 := bbase (se 5 (by rfl) ⟨17255, by rfl⟩ : syracuseStep 368117 = 34511) (by norm_num)
theorem B171533 : Blo 107783 171533 := bbase (se 3 (by rfl) ⟨32162, by rfl⟩ : syracuseStep 171533 = 64325) (by norm_num)
theorem B138773 : Blo 107783 138773 := bbase (se 6 (by rfl) ⟨3252, by rfl⟩ : syracuseStep 138773 = 6505) (by norm_num)
theorem B237077 : Blo 107783 237077 := bbase (se 6 (by rfl) ⟨5556, by rfl⟩ : syracuseStep 237077 = 11113) (by norm_num)
theorem B138829 : Blo 107783 138829 := bbase (se 3 (by rfl) ⟨26030, by rfl⟩ : syracuseStep 138829 = 52061) (by norm_num)
theorem B335477 : Blo 107783 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B138925 : Blo 107783 138925 := bbase (se 3 (by rfl) ⟨26048, by rfl⟩ : syracuseStep 138925 = 52097) (by norm_num)
theorem B139097 : Blo 107783 139097 := bbase (se 2 (by rfl) ⟨52161, by rfl⟩ : syracuseStep 139097 = 104323) (by norm_num)
theorem B139153 : Blo 107783 139153 := bbase (se 2 (by rfl) ⟨52182, by rfl⟩ : syracuseStep 139153 = 104365) (by norm_num)
theorem B434069 : Blo 107783 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B368549 : Blo 107783 368549 := bbase (se 4 (by rfl) ⟨34551, by rfl⟩ : syracuseStep 368549 = 69103) (by norm_num)
theorem B204781 : Blo 107783 204781 := bbase (se 3 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 204781 = 76793) (by norm_num)
theorem B139249 : Blo 107783 139249 := bbase (se 2 (by rfl) ⟨52218, by rfl⟩ : syracuseStep 139249 = 104437) (by norm_num)
theorem B204925 : Blo 107783 204925 := bbase (se 3 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 204925 = 76847) (by norm_num)
theorem B139421 : Blo 107783 139421 := bbase (se 3 (by rfl) ⟨26141, by rfl⟩ : syracuseStep 139421 = 52283) (by norm_num)
theorem B139477 : Blo 107783 139477 := bbase (se 7 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 139477 = 3269) (by norm_num)
theorem B237829 : Blo 107783 237829 := bbase (se 4 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 237829 = 44593) (by norm_num)
theorem B205085 : Blo 107783 205085 := bbase (se 3 (by rfl) ⟨38453, by rfl⟩ : syracuseStep 205085 = 76907) (by norm_num)
theorem B565541 : Blo 107783 565541 := bbase (se 4 (by rfl) ⟨53019, by rfl⟩ : syracuseStep 565541 = 106039) (by norm_num)
theorem B139573 : Blo 107783 139573 := bbase (se 5 (by rfl) ⟨6542, by rfl⟩ : syracuseStep 139573 = 13085) (by norm_num)
theorem B368981 : Blo 107783 368981 := bbase (se 10 (by rfl) ⟨540, by rfl⟩ : syracuseStep 368981 = 1081) (by norm_num)
theorem B237973 : Blo 107783 237973 := bbase (se 6 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 237973 = 11155) (by norm_num)
theorem B205229 : Blo 107783 205229 := bbase (se 3 (by rfl) ⟨38480, by rfl⟩ : syracuseStep 205229 = 76961) (by norm_num)
theorem B139745 : Blo 107783 139745 := bbase (se 2 (by rfl) ⟨52404, by rfl⟩ : syracuseStep 139745 = 104809) (by norm_num)
theorem B139801 : Blo 107783 139801 := bbase (se 2 (by rfl) ⟨52425, by rfl⟩ : syracuseStep 139801 = 104851) (by norm_num)
theorem B139897 : Blo 107783 139897 := bbase (se 2 (by rfl) ⟨52461, by rfl⟩ : syracuseStep 139897 = 104923) (by norm_num)
theorem B205517 : Blo 107783 205517 := bbase (se 3 (by rfl) ⟨38534, by rfl⟩ : syracuseStep 205517 = 77069) (by norm_num)
theorem B402149 : Blo 107783 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B369413 : Blo 107783 369413 := bbase (se 4 (by rfl) ⟨34632, by rfl⟩ : syracuseStep 369413 = 69265) (by norm_num)
theorem B238349 : Blo 107783 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B140069 : Blo 107783 140069 := bbase (se 4 (by rfl) ⟨13131, by rfl⟩ : syracuseStep 140069 = 26263) (by norm_num)
theorem B140125 : Blo 107783 140125 := bbase (se 3 (by rfl) ⟨26273, by rfl⟩ : syracuseStep 140125 = 52547) (by norm_num)
theorem B205669 : Blo 107783 205669 := bbase (se 4 (by rfl) ⟨19281, by rfl⟩ : syracuseStep 205669 = 38563) (by norm_num)
theorem B140221 : Blo 107783 140221 := bbase (se 3 (by rfl) ⟨26291, by rfl⟩ : syracuseStep 140221 = 52583) (by norm_num)
theorem B173021 : Blo 107783 173021 := bbase (se 3 (by rfl) ⟨32441, by rfl⟩ : syracuseStep 173021 = 64883) (by norm_num)
theorem B926741 : Blo 107783 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B140393 : Blo 107783 140393 := bbase (se 2 (by rfl) ⟨52647, by rfl⟩ : syracuseStep 140393 = 105295) (by norm_num)
theorem B140401 : Blo 107783 140401 := bbase (se 2 (by rfl) ⟨52650, by rfl⟩ : syracuseStep 140401 = 105301) (by norm_num)
theorem B238717 : Blo 107783 238717 := bbase (se 3 (by rfl) ⟨44759, by rfl⟩ : syracuseStep 238717 = 89519) (by norm_num)
theorem B205973 : Blo 107783 205973 := bbase (se 6 (by rfl) ⟨4827, by rfl⟩ : syracuseStep 205973 = 9655) (by norm_num)
theorem B140449 : Blo 107783 140449 := bbase (se 2 (by rfl) ⟨52668, by rfl⟩ : syracuseStep 140449 = 105337) (by norm_num)
theorem B369845 : Blo 107783 369845 := bbase (se 5 (by rfl) ⟨17336, by rfl⟩ : syracuseStep 369845 = 34673) (by norm_num)
theorem B828629 : Blo 107783 828629 := bbase (se 7 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 828629 = 19421) (by norm_num)
theorem B533749 : Blo 107783 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B402677 : Blo 107783 402677 := bbase (se 5 (by rfl) ⟨18875, by rfl⟩ : syracuseStep 402677 = 37751) (by norm_num)
theorem B140545 : Blo 107783 140545 := bbase (se 2 (by rfl) ⟨52704, by rfl⟩ : syracuseStep 140545 = 105409) (by norm_num)
theorem B992533 : Blo 107783 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B206189 : Blo 107783 206189 := bbase (se 3 (by rfl) ⟨38660, by rfl⟩ : syracuseStep 206189 = 77321) (by norm_num)
theorem B763253 : Blo 107783 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B140717 : Blo 107783 140717 := bbase (se 3 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 140717 = 52769) (by norm_num)
theorem B140773 : Blo 107783 140773 := bbase (se 4 (by rfl) ⟨13197, by rfl⟩ : syracuseStep 140773 = 26395) (by norm_num)
theorem B173573 : Blo 107783 173573 := bbase (se 4 (by rfl) ⟨16272, by rfl⟩ : syracuseStep 173573 = 32545) (by norm_num)
theorem B173605 : Blo 107783 173605 := bbase (se 4 (by rfl) ⟨16275, by rfl⟩ : syracuseStep 173605 = 32551) (by norm_num)
theorem B140869 : Blo 107783 140869 := bbase (se 4 (by rfl) ⟨13206, by rfl⟩ : syracuseStep 140869 = 26413) (by norm_num)
theorem B370277 : Blo 107783 370277 := bbase (se 4 (by rfl) ⟨34713, by rfl⟩ : syracuseStep 370277 = 69427) (by norm_num)
theorem B141041 : Blo 107783 141041 := bbase (se 2 (by rfl) ⟨52890, by rfl⟩ : syracuseStep 141041 = 105781) (by norm_num)
theorem B141097 : Blo 107783 141097 := bbase (se 2 (by rfl) ⟨52911, by rfl⟩ : syracuseStep 141097 = 105823) (by norm_num)
theorem B206725 : Blo 107783 206725 := bbase (se 4 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 206725 = 38761) (by norm_num)
theorem B141193 : Blo 107783 141193 := bbase (se 2 (by rfl) ⟨52947, by rfl⟩ : syracuseStep 141193 = 105895) (by norm_num)
theorem B206869 : Blo 107783 206869 := bbase (se 6 (by rfl) ⟨4848, by rfl⟩ : syracuseStep 206869 = 9697) (by norm_num)
theorem B370709 : Blo 107783 370709 := bbase (se 6 (by rfl) ⟨8688, by rfl⟩ : syracuseStep 370709 = 17377) (by norm_num)
theorem B141365 : Blo 107783 141365 := bbase (se 5 (by rfl) ⟨6626, by rfl⟩ : syracuseStep 141365 = 13253) (by norm_num)
theorem B141421 : Blo 107783 141421 := bbase (se 3 (by rfl) ⟨26516, by rfl⟩ : syracuseStep 141421 = 53033) (by norm_num)
theorem B207029 : Blo 107783 207029 := bbase (se 5 (by rfl) ⟨9704, by rfl⟩ : syracuseStep 207029 = 19409) (by norm_num)
theorem B698645 : Blo 107783 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B207173 : Blo 107783 207173 := bbase (se 4 (by rfl) ⟨19422, by rfl⟩ : syracuseStep 207173 = 38845) (by norm_num)
theorem B502213 : Blo 107783 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B174533 : Blo 107783 174533 := bbase (se 4 (by rfl) ⟨16362, by rfl⟩ : syracuseStep 174533 = 32725) (by norm_num)
theorem B371141 : Blo 107783 371141 := bbase (se 4 (by rfl) ⟨34794, by rfl⟩ : syracuseStep 371141 = 69589) (by norm_num)
theorem B272909 : Blo 107783 272909 := bbase (se 3 (by rfl) ⟨51170, by rfl⟩ : syracuseStep 272909 = 102341) (by norm_num)
theorem B633365 : Blo 107783 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B207461 : Blo 107783 207461 := bbase (se 4 (by rfl) ⟨19449, by rfl⟩ : syracuseStep 207461 = 38899) (by norm_num)
theorem B207613 : Blo 107783 207613 := bbase (se 3 (by rfl) ⟨38927, by rfl⟩ : syracuseStep 207613 = 77855) (by norm_num)
theorem B109409 : Blo 107783 109409 := bbase (se 2 (by rfl) ⟨41028, by rfl⟩ : syracuseStep 109409 = 82057) (by norm_num)
theorem B273253 : Blo 107783 273253 := bbase (se 4 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 273253 = 51235) (by norm_num)
theorem B371573 : Blo 107783 371573 := bbase (se 5 (by rfl) ⟨17417, by rfl⟩ : syracuseStep 371573 = 34835) (by norm_num)
theorem B273365 : Blo 107783 273365 := bbase (se 7 (by rfl) ⟨3203, by rfl⟩ : syracuseStep 273365 = 6407) (by norm_num)
theorem B207917 : Blo 107783 207917 := bbase (se 3 (by rfl) ⟨38984, by rfl⟩ : syracuseStep 207917 = 77969) (by norm_num)
theorem B470069 : Blo 107783 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B601141 : Blo 107783 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B339029 : Blo 107783 339029 := bbase (se 8 (by rfl) ⟨1986, by rfl⟩ : syracuseStep 339029 = 3973) (by norm_num)
theorem B175213 : Blo 107783 175213 := bbase (se 3 (by rfl) ⟨32852, by rfl⟩ : syracuseStep 175213 = 65705) (by norm_num)
theorem B273557 : Blo 107783 273557 := bbase (se 6 (by rfl) ⟨6411, by rfl⟩ : syracuseStep 273557 = 12823) (by norm_num)
theorem B175277 : Blo 107783 175277 := bbase (se 3 (by rfl) ⟨32864, by rfl⟩ : syracuseStep 175277 = 65729) (by norm_num)
theorem B372005 : Blo 107783 372005 := bbase (se 4 (by rfl) ⟨34875, by rfl⟩ : syracuseStep 372005 = 69751) (by norm_num)
theorem B109937 : Blo 107783 109937 := bbase (se 2 (by rfl) ⟨41226, by rfl⟩ : syracuseStep 109937 = 82453) (by norm_num)
theorem B273901 : Blo 107783 273901 := bbase (se 3 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 273901 = 102713) (by norm_num)
theorem B274013 : Blo 107783 274013 := bbase (se 3 (by rfl) ⟨51377, by rfl⟩ : syracuseStep 274013 = 102755) (by norm_num)
theorem B142997 : Blo 107783 142997 := bbase (se 6 (by rfl) ⟨3351, by rfl⟩ : syracuseStep 142997 = 6703) (by norm_num)
theorem B372437 : Blo 107783 372437 := bbase (se 7 (by rfl) ⟨4364, by rfl⟩ : syracuseStep 372437 = 8729) (by norm_num)
theorem B143077 : Blo 107783 143077 := bbase (se 4 (by rfl) ⟨13413, by rfl⟩ : syracuseStep 143077 = 26827) (by norm_num)
theorem B274205 : Blo 107783 274205 := bbase (se 3 (by rfl) ⟨51413, by rfl⟩ : syracuseStep 274205 = 102827) (by norm_num)
theorem B208669 : Blo 107783 208669 := bbase (se 3 (by rfl) ⟨39125, by rfl⟩ : syracuseStep 208669 = 78251) (by norm_num)
theorem B208813 : Blo 107783 208813 := bbase (se 3 (by rfl) ⟨39152, by rfl⟩ : syracuseStep 208813 = 78305) (by norm_num)
theorem B929717 : Blo 107783 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B110521 : Blo 107783 110521 := bbase (se 2 (by rfl) ⟨41445, by rfl⟩ : syracuseStep 110521 = 82891) (by norm_num)
theorem B208973 : Blo 107783 208973 := bbase (se 3 (by rfl) ⟨39182, by rfl⟩ : syracuseStep 208973 = 78365) (by norm_num)
theorem B274549 : Blo 107783 274549 := bbase (se 5 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 274549 = 25739) (by norm_num)
theorem B372869 : Blo 107783 372869 := bbase (se 4 (by rfl) ⟨34956, by rfl⟩ : syracuseStep 372869 = 69913) (by norm_num)
theorem B209117 : Blo 107783 209117 := bbase (se 3 (by rfl) ⟨39209, by rfl⟩ : syracuseStep 209117 = 78419) (by norm_num)
theorem B274661 : Blo 107783 274661 := bbase (se 4 (by rfl) ⟨25749, by rfl⟩ : syracuseStep 274661 = 51499) (by norm_num)
theorem B143617 : Blo 107783 143617 := bbase (se 2 (by rfl) ⟨53856, by rfl⟩ : syracuseStep 143617 = 107713) (by norm_num)
theorem B274853 : Blo 107783 274853 := bbase (se 4 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 274853 = 51535) (by norm_num)
theorem B176597 : Blo 107783 176597 := bbase (se 7 (by rfl) ⟨2069, by rfl⟩ : syracuseStep 176597 = 4139) (by norm_num)
theorem B209405 : Blo 107783 209405 := bbase (se 3 (by rfl) ⟨39263, by rfl⟩ : syracuseStep 209405 = 78527) (by norm_num)
theorem B373301 : Blo 107783 373301 := bbase (se 5 (by rfl) ⟨17498, by rfl⟩ : syracuseStep 373301 = 34997) (by norm_num)
theorem B176789 : Blo 107783 176789 := bbase (se 6 (by rfl) ⟨4143, by rfl⟩ : syracuseStep 176789 = 8287) (by norm_num)
theorem B209557 : Blo 107783 209557 := bbase (se 6 (by rfl) ⟨4911, by rfl⟩ : syracuseStep 209557 = 9823) (by norm_num)
theorem B307957 : Blo 107783 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B275197 : Blo 107783 275197 := bbase (se 3 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 275197 = 103199) (by norm_num)
theorem B176917 : Blo 107783 176917 := bbase (se 6 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 176917 = 8293) (by norm_num)
theorem B471845 : Blo 107783 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B275309 : Blo 107783 275309 := bbase (se 3 (by rfl) ⟨51620, by rfl⟩ : syracuseStep 275309 = 103241) (by norm_num)
theorem B242549 : Blo 107783 242549 := bbase (se 5 (by rfl) ⟨11369, by rfl⟩ : syracuseStep 242549 = 22739) (by norm_num)
theorem B308117 : Blo 107783 308117 := bbase (se 6 (by rfl) ⟨7221, by rfl⟩ : syracuseStep 308117 = 14443) (by norm_num)
theorem B242621 : Blo 107783 242621 := bbase (se 3 (by rfl) ⟨45491, by rfl⟩ : syracuseStep 242621 = 90983) (by norm_num)
theorem B209861 : Blo 107783 209861 := bbase (se 4 (by rfl) ⟨19674, by rfl⟩ : syracuseStep 209861 = 39349) (by norm_num)
theorem B373733 : Blo 107783 373733 := bbase (se 4 (by rfl) ⟨35037, by rfl⟩ : syracuseStep 373733 = 70075) (by norm_num)
theorem B242693 : Blo 107783 242693 := bbase (se 4 (by rfl) ⟨22752, by rfl⟩ : syracuseStep 242693 = 45505) (by norm_num)
theorem B275501 : Blo 107783 275501 := bbase (se 3 (by rfl) ⟨51656, by rfl⟩ : syracuseStep 275501 = 103313) (by norm_num)
theorem B242765 : Blo 107783 242765 := bbase (se 3 (by rfl) ⟨45518, by rfl⟩ : syracuseStep 242765 = 91037) (by norm_num)
theorem B308357 : Blo 107783 308357 := bbase (se 4 (by rfl) ⟨28908, by rfl⟩ : syracuseStep 308357 = 57817) (by norm_num)
theorem B242837 : Blo 107783 242837 := bbase (se 6 (by rfl) ⟨5691, by rfl⟩ : syracuseStep 242837 = 11383) (by norm_num)
theorem B373909 : Blo 107783 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B242909 : Blo 107783 242909 := bbase (se 3 (by rfl) ⟨45545, by rfl⟩ : syracuseStep 242909 = 91091) (by norm_num)
theorem B242981 : Blo 107783 242981 := bbase (se 4 (by rfl) ⟨22779, by rfl⟩ : syracuseStep 242981 = 45559) (by norm_num)
theorem B308549 : Blo 107783 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B243053 : Blo 107783 243053 := bbase (se 3 (by rfl) ⟨45572, by rfl⟩ : syracuseStep 243053 = 91145) (by norm_num)
theorem B275845 : Blo 107783 275845 := bbase (se 4 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 275845 = 51721) (by norm_num)
theorem B177557 : Blo 107783 177557 := bbase (se 6 (by rfl) ⟨4161, by rfl⟩ : syracuseStep 177557 = 8323) (by norm_num)
theorem B374165 : Blo 107783 374165 := bbase (se 6 (by rfl) ⟨8769, by rfl⟩ : syracuseStep 374165 = 17539) (by norm_num)
theorem B243125 : Blo 107783 243125 := bbase (se 5 (by rfl) ⟨11396, by rfl⟩ : syracuseStep 243125 = 22793) (by norm_num)
theorem B275957 : Blo 107783 275957 := bbase (se 5 (by rfl) ⟨12935, by rfl⟩ : syracuseStep 275957 = 25871) (by norm_num)
theorem B243197 : Blo 107783 243197 := bbase (se 3 (by rfl) ⟨45599, by rfl⟩ : syracuseStep 243197 = 91199) (by norm_num)
theorem B243269 : Blo 107783 243269 := bbase (se 4 (by rfl) ⟨22806, by rfl⟩ : syracuseStep 243269 = 45613) (by norm_num)
theorem B243341 : Blo 107783 243341 := bbase (se 3 (by rfl) ⟨45626, by rfl⟩ : syracuseStep 243341 = 91253) (by norm_num)
theorem B276149 : Blo 107783 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B210613 : Blo 107783 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B112313 : Blo 107783 112313 := bbase (se 2 (by rfl) ⟨42117, by rfl⟩ : syracuseStep 112313 = 84235) (by norm_num)
theorem B243413 : Blo 107783 243413 := bbase (se 7 (by rfl) ⟨2852, by rfl⟩ : syracuseStep 243413 = 5705) (by norm_num)
theorem B669397 : Blo 107783 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B472837 : Blo 107783 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B243485 : Blo 107783 243485 := bbase (se 3 (by rfl) ⟨45653, by rfl⟩ : syracuseStep 243485 = 91307) (by norm_num)
theorem B374597 : Blo 107783 374597 := bbase (se 4 (by rfl) ⟨35118, by rfl⟩ : syracuseStep 374597 = 70237) (by norm_num)
theorem B210757 : Blo 107783 210757 := bbase (se 4 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 210757 = 39517) (by norm_num)
theorem B178013 : Blo 107783 178013 := bbase (se 3 (by rfl) ⟨33377, by rfl⟩ : syracuseStep 178013 = 66755) (by norm_num)
theorem B243557 : Blo 107783 243557 := bbase (se 4 (by rfl) ⟨22833, by rfl⟩ : syracuseStep 243557 = 45667) (by norm_num)
theorem B243629 : Blo 107783 243629 := bbase (se 3 (by rfl) ⟨45680, by rfl⟩ : syracuseStep 243629 = 91361) (by norm_num)
theorem B210917 : Blo 107783 210917 := bbase (se 4 (by rfl) ⟨19773, by rfl⟩ : syracuseStep 210917 = 39547) (by norm_num)
theorem B243701 : Blo 107783 243701 := bbase (se 5 (by rfl) ⟨11423, by rfl⟩ : syracuseStep 243701 = 22847) (by norm_num)
theorem B276493 : Blo 107783 276493 := bbase (se 3 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 276493 = 103685) (by norm_num)
theorem B243773 : Blo 107783 243773 := bbase (se 3 (by rfl) ⟨45707, by rfl⟩ : syracuseStep 243773 = 91415) (by norm_num)
theorem B178237 : Blo 107783 178237 := bbase (se 3 (by rfl) ⟨33419, by rfl⟩ : syracuseStep 178237 = 66839) (by norm_num)
theorem B211061 : Blo 107783 211061 := bbase (se 5 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 211061 = 19787) (by norm_num)
theorem B276605 : Blo 107783 276605 := bbase (se 3 (by rfl) ⟨51863, by rfl⟩ : syracuseStep 276605 = 103727) (by norm_num)
theorem B178301 : Blo 107783 178301 := bbase (se 3 (by rfl) ⟨33431, by rfl⟩ : syracuseStep 178301 = 66863) (by norm_num)
theorem B243845 : Blo 107783 243845 := bbase (se 4 (by rfl) ⟨22860, by rfl⟩ : syracuseStep 243845 = 45721) (by norm_num)
theorem B243917 : Blo 107783 243917 := bbase (se 3 (by rfl) ⟨45734, by rfl⟩ : syracuseStep 243917 = 91469) (by norm_num)
theorem B375029 : Blo 107783 375029 := bbase (se 5 (by rfl) ⟨17579, by rfl⟩ : syracuseStep 375029 = 35159) (by norm_num)
theorem B178429 : Blo 107783 178429 := bbase (se 3 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 178429 = 66911) (by norm_num)
theorem B243989 : Blo 107783 243989 := bbase (se 6 (by rfl) ⟨5718, by rfl⟩ : syracuseStep 243989 = 11437) (by norm_num)
theorem B309541 : Blo 107783 309541 := bbase (se 4 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 309541 = 58039) (by norm_num)
theorem B899381 : Blo 107783 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B276797 : Blo 107783 276797 := bbase (se 3 (by rfl) ⟨51899, by rfl⟩ : syracuseStep 276797 = 103799) (by norm_num)
theorem B244061 : Blo 107783 244061 := bbase (se 3 (by rfl) ⟨45761, by rfl⟩ : syracuseStep 244061 = 91523) (by norm_num)
theorem B211349 : Blo 107783 211349 := bbase (se 6 (by rfl) ⟨4953, by rfl⟩ : syracuseStep 211349 = 9907) (by norm_num)
theorem B244133 : Blo 107783 244133 := bbase (se 4 (by rfl) ⟨22887, by rfl⟩ : syracuseStep 244133 = 45775) (by norm_num)
theorem B244205 : Blo 107783 244205 := bbase (se 3 (by rfl) ⟨45788, by rfl⟩ : syracuseStep 244205 = 91577) (by norm_num)
theorem B211501 : Blo 107783 211501 := bbase (se 3 (by rfl) ⟨39656, by rfl⟩ : syracuseStep 211501 = 79313) (by norm_num)
theorem B244277 : Blo 107783 244277 := bbase (se 5 (by rfl) ⟨11450, by rfl⟩ : syracuseStep 244277 = 22901) (by norm_num)
theorem B113269 : Blo 107783 113269 := bbase (se 5 (by rfl) ⟨5309, by rfl⟩ : syracuseStep 113269 = 10619) (by norm_num)
theorem B244349 : Blo 107783 244349 := bbase (se 3 (by rfl) ⟨45815, by rfl⟩ : syracuseStep 244349 = 91631) (by norm_num)
theorem B277141 : Blo 107783 277141 := bbase (se 6 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 277141 = 12991) (by norm_num)
theorem B375461 : Blo 107783 375461 := bbase (se 4 (by rfl) ⟨35199, by rfl⟩ : syracuseStep 375461 = 70399) (by norm_num)
theorem B244421 : Blo 107783 244421 := bbase (se 4 (by rfl) ⟨22914, by rfl⟩ : syracuseStep 244421 = 45829) (by norm_num)
theorem B277253 : Blo 107783 277253 := bbase (se 4 (by rfl) ⟨25992, by rfl⟩ : syracuseStep 277253 = 51985) (by norm_num)
theorem B244493 : Blo 107783 244493 := bbase (se 3 (by rfl) ⟨45842, by rfl⟩ : syracuseStep 244493 = 91685) (by norm_num)
theorem B244565 : Blo 107783 244565 := bbase (se 9 (by rfl) ⟨716, by rfl⟩ : syracuseStep 244565 = 1433) (by norm_num)
theorem B211805 : Blo 107783 211805 := bbase (se 3 (by rfl) ⟨39713, by rfl⟩ : syracuseStep 211805 = 79427) (by norm_num)
theorem B146333 : Blo 107783 146333 := bbase (se 3 (by rfl) ⟨27437, by rfl⟩ : syracuseStep 146333 = 54875) (by norm_num)
theorem B244637 : Blo 107783 244637 := bbase (se 3 (by rfl) ⟨45869, by rfl⟩ : syracuseStep 244637 = 91739) (by norm_num)
theorem B277445 : Blo 107783 277445 := bbase (se 4 (by rfl) ⟨26010, by rfl⟩ : syracuseStep 277445 = 52021) (by norm_num)
theorem B1391573 : Blo 107783 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B244709 : Blo 107783 244709 := bbase (se 4 (by rfl) ⟨22941, by rfl⟩ : syracuseStep 244709 = 45883) (by norm_num)
theorem B703477 : Blo 107783 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B244781 : Blo 107783 244781 := bbase (se 3 (by rfl) ⟨45896, by rfl⟩ : syracuseStep 244781 = 91793) (by norm_num)
theorem B375893 : Blo 107783 375893 := bbase (se 8 (by rfl) ⟨2202, by rfl⟩ : syracuseStep 375893 = 4405) (by norm_num)
theorem B244853 : Blo 107783 244853 := bbase (se 5 (by rfl) ⟨11477, by rfl⟩ : syracuseStep 244853 = 22955) (by norm_num)
theorem B244925 : Blo 107783 244925 := bbase (se 3 (by rfl) ⟨45923, by rfl⟩ : syracuseStep 244925 = 91847) (by norm_num)
theorem B244997 : Blo 107783 244997 := bbase (se 4 (by rfl) ⟨22968, by rfl⟩ : syracuseStep 244997 = 45937) (by norm_num)
theorem B277789 : Blo 107783 277789 := bbase (se 3 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 277789 = 104171) (by norm_num)
theorem B245069 : Blo 107783 245069 := bbase (se 3 (by rfl) ⟨45950, by rfl⟩ : syracuseStep 245069 = 91901) (by norm_num)
theorem B310645 : Blo 107783 310645 := bbase (se 5 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 310645 = 29123) (by norm_num)
theorem B277901 : Blo 107783 277901 := bbase (se 3 (by rfl) ⟨52106, by rfl⟩ : syracuseStep 277901 = 104213) (by norm_num)
theorem B245141 : Blo 107783 245141 := bbase (se 6 (by rfl) ⟨5745, by rfl⟩ : syracuseStep 245141 = 11491) (by norm_num)
theorem B245213 : Blo 107783 245213 := bbase (se 3 (by rfl) ⟨45977, by rfl⟩ : syracuseStep 245213 = 91955) (by norm_num)
theorem B376325 : Blo 107783 376325 := bbase (se 4 (by rfl) ⟨35280, by rfl⟩ : syracuseStep 376325 = 70561) (by norm_num)
theorem B900629 : Blo 107783 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B245285 : Blo 107783 245285 := bbase (se 4 (by rfl) ⟨22995, by rfl⟩ : syracuseStep 245285 = 45991) (by norm_num)
theorem B1064501 : Blo 107783 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B278093 : Blo 107783 278093 := bbase (se 3 (by rfl) ⟨52142, by rfl⟩ : syracuseStep 278093 = 104285) (by norm_num)
theorem B245357 : Blo 107783 245357 := bbase (se 3 (by rfl) ⟨46004, by rfl⟩ : syracuseStep 245357 = 92009) (by norm_num)
theorem B245429 : Blo 107783 245429 := bbase (se 5 (by rfl) ⟨11504, by rfl⟩ : syracuseStep 245429 = 23009) (by norm_num)
theorem B147133 : Blo 107783 147133 := bbase (se 3 (by rfl) ⟨27587, by rfl⟩ : syracuseStep 147133 = 55175) (by norm_num)
theorem B409333 : Blo 107783 409333 := bbase (se 5 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 409333 = 38375) (by norm_num)
theorem B245501 : Blo 107783 245501 := bbase (se 3 (by rfl) ⟨46031, by rfl⟩ : syracuseStep 245501 = 92063) (by norm_num)
theorem B245573 : Blo 107783 245573 := bbase (se 4 (by rfl) ⟨23022, by rfl⟩ : syracuseStep 245573 = 46045) (by norm_num)
theorem B245645 : Blo 107783 245645 := bbase (se 3 (by rfl) ⟨46058, by rfl⟩ : syracuseStep 245645 = 92117) (by norm_num)
theorem B278437 : Blo 107783 278437 := bbase (se 4 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 278437 = 52207) (by norm_num)
theorem B376757 : Blo 107783 376757 := bbase (se 5 (by rfl) ⟨17660, by rfl⟩ : syracuseStep 376757 = 35321) (by norm_num)
theorem B245717 : Blo 107783 245717 := bbase (se 7 (by rfl) ⟨2879, by rfl⟩ : syracuseStep 245717 = 5759) (by norm_num)
theorem B278549 : Blo 107783 278549 := bbase (se 6 (by rfl) ⟨6528, by rfl⟩ : syracuseStep 278549 = 13057) (by norm_num)
theorem B245789 : Blo 107783 245789 := bbase (se 3 (by rfl) ⟨46085, by rfl⟩ : syracuseStep 245789 = 92171) (by norm_num)
theorem B409637 : Blo 107783 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B245861 : Blo 107783 245861 := bbase (se 4 (by rfl) ⟨23049, by rfl⟩ : syracuseStep 245861 = 46099) (by norm_num)
theorem B147565 : Blo 107783 147565 := bbase (se 3 (by rfl) ⟨27668, by rfl⟩ : syracuseStep 147565 = 55337) (by norm_num)
theorem B213125 : Blo 107783 213125 := bbase (se 4 (by rfl) ⟨19980, by rfl⟩ : syracuseStep 213125 = 39961) (by norm_num)
theorem B245933 : Blo 107783 245933 := bbase (se 3 (by rfl) ⟨46112, by rfl⟩ : syracuseStep 245933 = 92225) (by norm_num)
theorem B704693 : Blo 107783 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B278741 : Blo 107783 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B246005 : Blo 107783 246005 := bbase (se 5 (by rfl) ⟨11531, by rfl⟩ : syracuseStep 246005 = 23063) (by norm_num)
theorem B475445 : Blo 107783 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B246077 : Blo 107783 246077 := bbase (se 3 (by rfl) ⟨46139, by rfl⟩ : syracuseStep 246077 = 92279) (by norm_num)
theorem B377189 : Blo 107783 377189 := bbase (se 4 (by rfl) ⟨35361, by rfl⟩ : syracuseStep 377189 = 70723) (by norm_num)
theorem B246149 : Blo 107783 246149 := bbase (se 4 (by rfl) ⟨23076, by rfl⟩ : syracuseStep 246149 = 46153) (by norm_num)
theorem B246221 : Blo 107783 246221 := bbase (se 3 (by rfl) ⟨46166, by rfl⟩ : syracuseStep 246221 = 92333) (by norm_num)
theorem B4047317 : Blo 107783 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B246293 : Blo 107783 246293 := bbase (se 6 (by rfl) ⟨5772, by rfl⟩ : syracuseStep 246293 = 11545) (by norm_num)
theorem B279085 : Blo 107783 279085 := bbase (se 3 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 279085 = 104657) (by norm_num)
theorem B246365 : Blo 107783 246365 := bbase (se 3 (by rfl) ⟨46193, by rfl⟩ : syracuseStep 246365 = 92387) (by norm_num)
theorem B279197 : Blo 107783 279197 := bbase (se 3 (by rfl) ⟨52349, by rfl⟩ : syracuseStep 279197 = 104699) (by norm_num)
theorem B246437 : Blo 107783 246437 := bbase (se 4 (by rfl) ⟨23103, by rfl⟩ : syracuseStep 246437 = 46207) (by norm_num)
theorem B246509 : Blo 107783 246509 := bbase (se 3 (by rfl) ⟨46220, by rfl⟩ : syracuseStep 246509 = 92441) (by norm_num)
theorem B246581 : Blo 107783 246581 := bbase (se 5 (by rfl) ⟨11558, by rfl⟩ : syracuseStep 246581 = 23117) (by norm_num)
theorem B836405 : Blo 107783 836405 := bbase (se 5 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 836405 = 78413) (by norm_num)
theorem B312149 : Blo 107783 312149 := bbase (se 9 (by rfl) ⟨914, by rfl⟩ : syracuseStep 312149 = 1829) (by norm_num)
theorem B279389 : Blo 107783 279389 := bbase (se 3 (by rfl) ⟨52385, by rfl⟩ : syracuseStep 279389 = 104771) (by norm_num)
theorem B246653 : Blo 107783 246653 := bbase (se 3 (by rfl) ⟨46247, by rfl⟩ : syracuseStep 246653 = 92495) (by norm_num)
theorem B246725 : Blo 107783 246725 := bbase (se 4 (by rfl) ⟨23130, by rfl⟩ : syracuseStep 246725 = 46261) (by norm_num)
theorem B246797 : Blo 107783 246797 := bbase (se 3 (by rfl) ⟨46274, by rfl⟩ : syracuseStep 246797 = 92549) (by norm_num)
theorem B246869 : Blo 107783 246869 := bbase (se 8 (by rfl) ⟨1446, by rfl⟩ : syracuseStep 246869 = 2893) (by norm_num)
theorem B181397 : Blo 107783 181397 := bbase (se 6 (by rfl) ⟨4251, by rfl⟩ : syracuseStep 181397 = 8503) (by norm_num)
theorem B246941 : Blo 107783 246941 := bbase (se 3 (by rfl) ⟨46301, by rfl⟩ : syracuseStep 246941 = 92603) (by norm_num)
theorem B115877 : Blo 107783 115877 := bbase (se 4 (by rfl) ⟨10863, by rfl⟩ : syracuseStep 115877 = 21727) (by norm_num)
theorem B279733 : Blo 107783 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B247013 : Blo 107783 247013 := bbase (se 4 (by rfl) ⟨23157, by rfl⟩ : syracuseStep 247013 = 46315) (by norm_num)
theorem B279845 : Blo 107783 279845 := bbase (se 4 (by rfl) ⟨26235, by rfl⟩ : syracuseStep 279845 = 52471) (by norm_num)
theorem B247085 : Blo 107783 247085 := bbase (se 3 (by rfl) ⟨46328, by rfl⟩ : syracuseStep 247085 = 92657) (by norm_num)
theorem B247157 : Blo 107783 247157 := bbase (se 5 (by rfl) ⟨11585, by rfl⟩ : syracuseStep 247157 = 23171) (by norm_num)
theorem B247229 : Blo 107783 247229 := bbase (se 3 (by rfl) ⟨46355, by rfl⟩ : syracuseStep 247229 = 92711) (by norm_num)
theorem B148933 : Blo 107783 148933 := bbase (se 4 (by rfl) ⟨13962, by rfl⟩ : syracuseStep 148933 = 27925) (by norm_num)
theorem B378341 : Blo 107783 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B280037 : Blo 107783 280037 := bbase (se 4 (by rfl) ⟨26253, by rfl⟩ : syracuseStep 280037 = 52507) (by norm_num)
theorem B247301 : Blo 107783 247301 := bbase (se 4 (by rfl) ⟨23184, by rfl⟩ : syracuseStep 247301 = 46369) (by norm_num)
theorem B149021 : Blo 107783 149021 := bbase (se 3 (by rfl) ⟨27941, by rfl⟩ : syracuseStep 149021 = 55883) (by norm_num)
theorem B247373 : Blo 107783 247373 := bbase (se 3 (by rfl) ⟨46382, by rfl⟩ : syracuseStep 247373 = 92765) (by norm_num)
theorem B116321 : Blo 107783 116321 := bbase (se 2 (by rfl) ⟨43620, by rfl⟩ : syracuseStep 116321 = 87241) (by norm_num)
theorem B181885 : Blo 107783 181885 := bbase (se 3 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 181885 = 68207) (by norm_num)
theorem B247445 : Blo 107783 247445 := bbase (se 6 (by rfl) ⟨5799, by rfl⟩ : syracuseStep 247445 = 11599) (by norm_num)
theorem B181973 : Blo 107783 181973 := bbase (se 7 (by rfl) ⟨2132, by rfl⟩ : syracuseStep 181973 = 4265) (by norm_num)
theorem B247517 : Blo 107783 247517 := bbase (se 3 (by rfl) ⟨46409, by rfl⟩ : syracuseStep 247517 = 92819) (by norm_num)
theorem B247589 : Blo 107783 247589 := bbase (se 4 (by rfl) ⟨23211, by rfl⟩ : syracuseStep 247589 = 46423) (by norm_num)
theorem B280381 : Blo 107783 280381 := bbase (se 3 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 280381 = 105143) (by norm_num)
theorem B182101 : Blo 107783 182101 := bbase (se 9 (by rfl) ⟨533, by rfl⟩ : syracuseStep 182101 = 1067) (by norm_num)
theorem B345941 : Blo 107783 345941 := bbase (se 9 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 345941 = 2027) (by norm_num)
theorem B116569 : Blo 107783 116569 := bbase (se 2 (by rfl) ⟨43713, by rfl⟩ : syracuseStep 116569 = 87427) (by norm_num)
theorem B247661 : Blo 107783 247661 := bbase (se 3 (by rfl) ⟨46436, by rfl⟩ : syracuseStep 247661 = 92873) (by norm_num)
theorem B182189 : Blo 107783 182189 := bbase (se 3 (by rfl) ⟨34160, by rfl⟩ : syracuseStep 182189 = 68321) (by norm_num)
theorem B280493 : Blo 107783 280493 := bbase (se 3 (by rfl) ⟨52592, by rfl⟩ : syracuseStep 280493 = 105185) (by norm_num)
theorem B247733 : Blo 107783 247733 := bbase (se 5 (by rfl) ⟨11612, by rfl⟩ : syracuseStep 247733 = 23225) (by norm_num)
theorem B247805 : Blo 107783 247805 := bbase (se 3 (by rfl) ⟨46463, by rfl⟩ : syracuseStep 247805 = 92927) (by norm_num)
theorem B182317 : Blo 107783 182317 := bbase (se 3 (by rfl) ⟨34184, by rfl⟩ : syracuseStep 182317 = 68369) (by norm_num)
theorem B280637 : Blo 107783 280637 := bbase (se 3 (by rfl) ⟨52619, by rfl⟩ : syracuseStep 280637 = 105239) (by norm_num)
theorem B247877 : Blo 107783 247877 := bbase (se 4 (by rfl) ⟨23238, by rfl⟩ : syracuseStep 247877 = 46477) (by norm_num)
theorem B411749 : Blo 107783 411749 := bbase (se 4 (by rfl) ⟨38601, by rfl⟩ : syracuseStep 411749 = 77203) (by norm_num)
theorem B280685 : Blo 107783 280685 := bbase (se 3 (by rfl) ⟨52628, by rfl⟩ : syracuseStep 280685 = 105257) (by norm_num)
theorem B182405 : Blo 107783 182405 := bbase (se 4 (by rfl) ⟨17100, by rfl⟩ : syracuseStep 182405 = 34201) (by norm_num)
theorem B247949 : Blo 107783 247949 := bbase (se 3 (by rfl) ⟨46490, by rfl⟩ : syracuseStep 247949 = 92981) (by norm_num)
theorem B444629 : Blo 107783 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B248021 : Blo 107783 248021 := bbase (se 7 (by rfl) ⟨2906, by rfl⟩ : syracuseStep 248021 = 5813) (by norm_num)
theorem B182533 : Blo 107783 182533 := bbase (se 4 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 182533 = 34225) (by norm_num)
theorem B117001 : Blo 107783 117001 := bbase (se 2 (by rfl) ⟨43875, by rfl⟩ : syracuseStep 117001 = 87751) (by norm_num)
theorem B248093 : Blo 107783 248093 := bbase (se 3 (by rfl) ⟨46517, by rfl⟩ : syracuseStep 248093 = 93035) (by norm_num)
theorem B248141 : Blo 107783 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B117073 : Blo 107783 117073 := bbase (se 2 (by rfl) ⟨43902, by rfl⟩ : syracuseStep 117073 = 87805) (by norm_num)
theorem B117077 : Blo 107783 117077 := bbase (se 10 (by rfl) ⟨171, by rfl⟩ : syracuseStep 117077 = 343) (by norm_num)
theorem B313685 : Blo 107783 313685 := bbase (se 10 (by rfl) ⟨459, by rfl⟩ : syracuseStep 313685 = 919) (by norm_num)
theorem B182621 : Blo 107783 182621 := bbase (se 3 (by rfl) ⟨34241, by rfl⟩ : syracuseStep 182621 = 68483) (by norm_num)
theorem B248165 : Blo 107783 248165 := bbase (se 4 (by rfl) ⟨23265, by rfl⟩ : syracuseStep 248165 = 46531) (by norm_num)
theorem B412037 : Blo 107783 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B313733 : Blo 107783 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B248237 : Blo 107783 248237 := bbase (se 3 (by rfl) ⟨46544, by rfl⟩ : syracuseStep 248237 = 93089) (by norm_num)
theorem B281029 : Blo 107783 281029 := bbase (se 4 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 281029 = 52693) (by norm_num)
theorem B1264085 : Blo 107783 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B182749 : Blo 107783 182749 := bbase (se 3 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 182749 = 68531) (by norm_num)
theorem B444901 : Blo 107783 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B248309 : Blo 107783 248309 := bbase (se 5 (by rfl) ⟨11639, by rfl⟩ : syracuseStep 248309 = 23279) (by norm_num)
theorem B182837 : Blo 107783 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B281141 : Blo 107783 281141 := bbase (se 5 (by rfl) ⟨13178, by rfl⟩ : syracuseStep 281141 = 26357) (by norm_num)
theorem B248381 : Blo 107783 248381 := bbase (se 3 (by rfl) ⟨46571, by rfl⟩ : syracuseStep 248381 = 93143) (by norm_num)
theorem B248453 : Blo 107783 248453 := bbase (se 4 (by rfl) ⟨23292, by rfl⟩ : syracuseStep 248453 = 46585) (by norm_num)
theorem B182965 : Blo 107783 182965 := bbase (se 5 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 182965 = 17153) (by norm_num)
theorem B117445 : Blo 107783 117445 := bbase (se 4 (by rfl) ⟨11010, by rfl⟩ : syracuseStep 117445 = 22021) (by norm_num)
theorem B248525 : Blo 107783 248525 := bbase (se 3 (by rfl) ⟨46598, by rfl⟩ : syracuseStep 248525 = 93197) (by norm_num)
theorem B346837 : Blo 107783 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B281333 : Blo 107783 281333 := bbase (se 5 (by rfl) ⟨13187, by rfl⟩ : syracuseStep 281333 = 26375) (by norm_num)
theorem B183053 : Blo 107783 183053 := bbase (se 3 (by rfl) ⟨34322, by rfl⟩ : syracuseStep 183053 = 68645) (by norm_num)
theorem B248597 : Blo 107783 248597 := bbase (se 6 (by rfl) ⟨5826, by rfl⟩ : syracuseStep 248597 = 11653) (by norm_num)
theorem B117593 : Blo 107783 117593 := bbase (se 2 (by rfl) ⟨44097, by rfl⟩ : syracuseStep 117593 = 88195) (by norm_num)
theorem B248669 : Blo 107783 248669 := bbase (se 3 (by rfl) ⟨46625, by rfl⟩ : syracuseStep 248669 = 93251) (by norm_num)
theorem B183181 : Blo 107783 183181 := bbase (se 3 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 183181 = 68693) (by norm_num)
theorem B248741 : Blo 107783 248741 := bbase (se 4 (by rfl) ⟨23319, by rfl⟩ : syracuseStep 248741 = 46639) (by norm_num)
theorem B183269 : Blo 107783 183269 := bbase (se 4 (by rfl) ⟨17181, by rfl⟩ : syracuseStep 183269 = 34363) (by norm_num)
theorem B248813 : Blo 107783 248813 := bbase (se 3 (by rfl) ⟨46652, by rfl⟩ : syracuseStep 248813 = 93305) (by norm_num)
theorem B248845 : Blo 107783 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B314405 : Blo 107783 314405 := bbase (se 4 (by rfl) ⟨29475, by rfl⟩ : syracuseStep 314405 = 58951) (by norm_num)
theorem B248885 : Blo 107783 248885 := bbase (se 5 (by rfl) ⟨11666, by rfl⟩ : syracuseStep 248885 = 23333) (by norm_num)
theorem B117821 : Blo 107783 117821 := bbase (se 3 (by rfl) ⟨22091, by rfl⟩ : syracuseStep 117821 = 44183) (by norm_num)
theorem B281677 : Blo 107783 281677 := bbase (se 3 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 281677 = 105629) (by norm_num)
theorem B183397 : Blo 107783 183397 := bbase (se 4 (by rfl) ⟨17193, by rfl⟩ : syracuseStep 183397 = 34387) (by norm_num)
theorem B248957 : Blo 107783 248957 := bbase (se 3 (by rfl) ⟨46679, by rfl⟩ : syracuseStep 248957 = 93359) (by norm_num)
theorem B117893 : Blo 107783 117893 := bbase (se 4 (by rfl) ⟨11052, by rfl⟩ : syracuseStep 117893 = 22105) (by norm_num)
theorem B183485 : Blo 107783 183485 := bbase (se 3 (by rfl) ⟨34403, by rfl⟩ : syracuseStep 183485 = 68807) (by norm_num)
theorem B281789 : Blo 107783 281789 := bbase (se 3 (by rfl) ⟨52835, by rfl⟩ : syracuseStep 281789 = 105671) (by norm_num)
theorem B249029 : Blo 107783 249029 := bbase (se 4 (by rfl) ⟨23346, by rfl⟩ : syracuseStep 249029 = 46693) (by norm_num)
theorem B249101 : Blo 107783 249101 := bbase (se 3 (by rfl) ⟨46706, by rfl⟩ : syracuseStep 249101 = 93413) (by norm_num)
theorem B183613 : Blo 107783 183613 := bbase (se 3 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 183613 = 68855) (by norm_num)
theorem B118081 : Blo 107783 118081 := bbase (se 2 (by rfl) ⟨44280, by rfl⟩ : syracuseStep 118081 = 88561) (by norm_num)
theorem B544085 : Blo 107783 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B249173 : Blo 107783 249173 := bbase (se 11 (by rfl) ⟨182, by rfl⟩ : syracuseStep 249173 = 365) (by norm_num)
theorem B281981 : Blo 107783 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B183701 : Blo 107783 183701 := bbase (se 6 (by rfl) ⟨4305, by rfl⟩ : syracuseStep 183701 = 8611) (by norm_num)
theorem B249245 : Blo 107783 249245 := bbase (se 3 (by rfl) ⟨46733, by rfl⟩ : syracuseStep 249245 = 93467) (by norm_num)
theorem B282053 : Blo 107783 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B249301 : Blo 107783 249301 := bbase (se 7 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 249301 = 5843) (by norm_num)
theorem B314837 : Blo 107783 314837 := bbase (se 7 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 314837 = 7379) (by norm_num)
theorem B249317 : Blo 107783 249317 := bbase (se 4 (by rfl) ⟨23373, by rfl⟩ : syracuseStep 249317 = 46747) (by norm_num)
theorem B118265 : Blo 107783 118265 := bbase (se 2 (by rfl) ⟨44349, by rfl⟩ : syracuseStep 118265 = 88699) (by norm_num)
theorem B183829 : Blo 107783 183829 := bbase (se 6 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 183829 = 8617) (by norm_num)
theorem B413221 : Blo 107783 413221 := bbase (se 4 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 413221 = 77479) (by norm_num)
theorem B249389 : Blo 107783 249389 := bbase (se 3 (by rfl) ⟨46760, by rfl⟩ : syracuseStep 249389 = 93521) (by norm_num)
theorem B151093 : Blo 107783 151093 := bbase (se 5 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 151093 = 14165) (by norm_num)
theorem B216677 : Blo 107783 216677 := bbase (se 4 (by rfl) ⟨20313, by rfl⟩ : syracuseStep 216677 = 40627) (by norm_num)
theorem B183917 : Blo 107783 183917 := bbase (se 3 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 183917 = 68969) (by norm_num)
theorem B446069 : Blo 107783 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B249461 : Blo 107783 249461 := bbase (se 5 (by rfl) ⟨11693, by rfl⟩ : syracuseStep 249461 = 23387) (by norm_num)
theorem B249533 : Blo 107783 249533 := bbase (se 3 (by rfl) ⟨46787, by rfl⟩ : syracuseStep 249533 = 93575) (by norm_num)
theorem B282325 : Blo 107783 282325 := bbase (se 7 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 282325 = 6617) (by norm_num)
theorem B184045 : Blo 107783 184045 := bbase (se 3 (by rfl) ⟨34508, by rfl⟩ : syracuseStep 184045 = 69017) (by norm_num)
theorem B249605 : Blo 107783 249605 := bbase (se 4 (by rfl) ⟨23400, by rfl⟩ : syracuseStep 249605 = 46801) (by norm_num)
theorem B184133 : Blo 107783 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B282437 : Blo 107783 282437 := bbase (se 4 (by rfl) ⟨26478, by rfl⟩ : syracuseStep 282437 = 52957) (by norm_num)
theorem B249677 : Blo 107783 249677 := bbase (se 3 (by rfl) ⟨46814, by rfl⟩ : syracuseStep 249677 = 93629) (by norm_num)
theorem B413525 : Blo 107783 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B5820245 : Blo 107783 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B511861 : Blo 107783 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B249749 : Blo 107783 249749 := bbase (se 6 (by rfl) ⟨5853, by rfl⟩ : syracuseStep 249749 = 11707) (by norm_num)
theorem B184261 : Blo 107783 184261 := bbase (se 4 (by rfl) ⟨17274, by rfl⟩ : syracuseStep 184261 = 34549) (by norm_num)
theorem B249821 : Blo 107783 249821 := bbase (se 3 (by rfl) ⟨46841, by rfl⟩ : syracuseStep 249821 = 93683) (by norm_num)
theorem B282629 : Blo 107783 282629 := bbase (se 4 (by rfl) ⟨26496, by rfl⟩ : syracuseStep 282629 = 52993) (by norm_num)
theorem B184349 : Blo 107783 184349 := bbase (se 3 (by rfl) ⟨34565, by rfl⟩ : syracuseStep 184349 = 69131) (by norm_num)
theorem B249893 : Blo 107783 249893 := bbase (se 4 (by rfl) ⟨23427, by rfl⟩ : syracuseStep 249893 = 46855) (by norm_num)
theorem B249965 : Blo 107783 249965 := bbase (se 3 (by rfl) ⟨46868, by rfl⟩ : syracuseStep 249965 = 93737) (by norm_num)
theorem B184477 : Blo 107783 184477 := bbase (se 3 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 184477 = 69179) (by norm_num)
theorem B250037 : Blo 107783 250037 := bbase (se 5 (by rfl) ⟨11720, by rfl⟩ : syracuseStep 250037 = 23441) (by norm_num)
theorem B315589 : Blo 107783 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B119017 : Blo 107783 119017 := bbase (se 2 (by rfl) ⟨44631, by rfl⟩ : syracuseStep 119017 = 89263) (by norm_num)
theorem B184565 : Blo 107783 184565 := bbase (se 5 (by rfl) ⟨8651, by rfl⟩ : syracuseStep 184565 = 17303) (by norm_num)
theorem B250109 : Blo 107783 250109 := bbase (se 3 (by rfl) ⟨46895, by rfl⟩ : syracuseStep 250109 = 93791) (by norm_num)
theorem B119089 : Blo 107783 119089 := bbase (se 2 (by rfl) ⟨44658, by rfl⟩ : syracuseStep 119089 = 89317) (by norm_num)
theorem B250181 : Blo 107783 250181 := bbase (se 4 (by rfl) ⟨23454, by rfl⟩ : syracuseStep 250181 = 46909) (by norm_num)
theorem B184693 : Blo 107783 184693 := bbase (se 5 (by rfl) ⟨8657, by rfl⟩ : syracuseStep 184693 = 17315) (by norm_num)
theorem B250253 : Blo 107783 250253 := bbase (se 3 (by rfl) ⟨46922, by rfl⟩ : syracuseStep 250253 = 93845) (by norm_num)
theorem B184781 : Blo 107783 184781 := bbase (se 3 (by rfl) ⟨34646, by rfl⟩ : syracuseStep 184781 = 69293) (by norm_num)
theorem B250325 : Blo 107783 250325 := bbase (se 7 (by rfl) ⟨2933, by rfl⟩ : syracuseStep 250325 = 5867) (by norm_num)
theorem B119269 : Blo 107783 119269 := bbase (se 4 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 119269 = 22363) (by norm_num)
theorem B250397 : Blo 107783 250397 := bbase (se 3 (by rfl) ⟨46949, by rfl⟩ : syracuseStep 250397 = 93899) (by norm_num)
theorem B184909 : Blo 107783 184909 := bbase (se 3 (by rfl) ⟨34670, by rfl⟩ : syracuseStep 184909 = 69341) (by norm_num)
theorem B250469 : Blo 107783 250469 := bbase (se 4 (by rfl) ⟨23481, by rfl⟩ : syracuseStep 250469 = 46963) (by norm_num)
theorem B184997 : Blo 107783 184997 := bbase (se 4 (by rfl) ⟨17343, by rfl⟩ : syracuseStep 184997 = 34687) (by norm_num)
theorem B250541 : Blo 107783 250541 := bbase (se 3 (by rfl) ⟨46976, by rfl⟩ : syracuseStep 250541 = 93953) (by norm_num)
theorem B250613 : Blo 107783 250613 := bbase (se 5 (by rfl) ⟨11747, by rfl⟩ : syracuseStep 250613 = 23495) (by norm_num)
theorem B185125 : Blo 107783 185125 := bbase (se 4 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 185125 = 34711) (by norm_num)
theorem B250685 : Blo 107783 250685 := bbase (se 3 (by rfl) ⟨47003, by rfl⟩ : syracuseStep 250685 = 94007) (by norm_num)
theorem B185213 : Blo 107783 185213 := bbase (se 3 (by rfl) ⟨34727, by rfl⟩ : syracuseStep 185213 = 69455) (by norm_num)
theorem B250757 : Blo 107783 250757 := bbase (se 4 (by rfl) ⟨23508, by rfl⟩ : syracuseStep 250757 = 47017) (by norm_num)
theorem B250829 : Blo 107783 250829 := bbase (se 3 (by rfl) ⟨47030, by rfl⟩ : syracuseStep 250829 = 94061) (by norm_num)
theorem B1004501 : Blo 107783 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B185341 : Blo 107783 185341 := bbase (se 3 (by rfl) ⟨34751, by rfl⟩ : syracuseStep 185341 = 69503) (by norm_num)
theorem B250901 : Blo 107783 250901 := bbase (se 6 (by rfl) ⟨5880, by rfl⟩ : syracuseStep 250901 = 11761) (by norm_num)
theorem B185429 : Blo 107783 185429 := bbase (se 8 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 185429 = 2173) (by norm_num)
theorem B250973 : Blo 107783 250973 := bbase (se 3 (by rfl) ⟨47057, by rfl⟩ : syracuseStep 250973 = 94115) (by norm_num)
theorem B251045 : Blo 107783 251045 := bbase (se 4 (by rfl) ⟨23535, by rfl⟩ : syracuseStep 251045 = 47071) (by norm_num)
theorem B185557 : Blo 107783 185557 := bbase (se 7 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 185557 = 4349) (by norm_num)
theorem B251117 : Blo 107783 251117 := bbase (se 3 (by rfl) ⟨47084, by rfl⟩ : syracuseStep 251117 = 94169) (by norm_num)
theorem B185645 : Blo 107783 185645 := bbase (se 3 (by rfl) ⟨34808, by rfl⟩ : syracuseStep 185645 = 69617) (by norm_num)
theorem B546101 : Blo 107783 546101 := bbase (se 5 (by rfl) ⟨25598, by rfl⟩ : syracuseStep 546101 = 51197) (by norm_num)
theorem B251189 : Blo 107783 251189 := bbase (se 5 (by rfl) ⟨11774, by rfl⟩ : syracuseStep 251189 = 23549) (by norm_num)
theorem B251261 : Blo 107783 251261 := bbase (se 3 (by rfl) ⟨47111, by rfl⟩ : syracuseStep 251261 = 94223) (by norm_num)
theorem B185773 : Blo 107783 185773 := bbase (se 3 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 185773 = 69665) (by norm_num)
theorem B251333 : Blo 107783 251333 := bbase (se 4 (by rfl) ⟨23562, by rfl⟩ : syracuseStep 251333 = 47125) (by norm_num)
theorem B185861 : Blo 107783 185861 := bbase (se 4 (by rfl) ⟨17424, by rfl⟩ : syracuseStep 185861 = 34849) (by norm_num)
theorem B251405 : Blo 107783 251405 := bbase (se 3 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 251405 = 94277) (by norm_num)
theorem B349733 : Blo 107783 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B120361 : Blo 107783 120361 := bbase (se 2 (by rfl) ⟨45135, by rfl⟩ : syracuseStep 120361 = 90271) (by norm_num)
theorem B251477 : Blo 107783 251477 := bbase (se 8 (by rfl) ⟨1473, by rfl⟩ : syracuseStep 251477 = 2947) (by norm_num)
theorem B185989 : Blo 107783 185989 := bbase (se 4 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 185989 = 34873) (by norm_num)
theorem B186077 : Blo 107783 186077 := bbase (se 3 (by rfl) ⟨34889, by rfl⟩ : syracuseStep 186077 = 69779) (by norm_num)
theorem B186205 : Blo 107783 186205 := bbase (se 3 (by rfl) ⟨34913, by rfl⟩ : syracuseStep 186205 = 69827) (by norm_num)
theorem B415637 : Blo 107783 415637 := bbase (se 6 (by rfl) ⟨9741, by rfl⟩ : syracuseStep 415637 = 19483) (by norm_num)
theorem B186293 : Blo 107783 186293 := bbase (se 5 (by rfl) ⟨8732, by rfl⟩ : syracuseStep 186293 = 17465) (by norm_num)
theorem B186421 : Blo 107783 186421 := bbase (se 5 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 186421 = 17477) (by norm_num)
theorem B153677 : Blo 107783 153677 := bbase (se 3 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 153677 = 57629) (by norm_num)
theorem B252029 : Blo 107783 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B186509 : Blo 107783 186509 := bbase (se 3 (by rfl) ⟨34970, by rfl⟩ : syracuseStep 186509 = 69941) (by norm_num)
theorem B415925 : Blo 107783 415925 := bbase (se 5 (by rfl) ⟨19496, by rfl⟩ : syracuseStep 415925 = 38993) (by norm_num)
theorem B186637 : Blo 107783 186637 := bbase (se 3 (by rfl) ⟨34994, by rfl⟩ : syracuseStep 186637 = 69989) (by norm_num)
theorem B186725 : Blo 107783 186725 := bbase (se 4 (by rfl) ⟨17505, by rfl⟩ : syracuseStep 186725 = 35011) (by norm_num)
theorem B121261 : Blo 107783 121261 := bbase (se 3 (by rfl) ⟨22736, by rfl⟩ : syracuseStep 121261 = 45473) (by norm_num)
theorem B121297 : Blo 107783 121297 := bbase (se 2 (by rfl) ⟨45486, by rfl⟩ : syracuseStep 121297 = 90973) (by norm_num)
theorem B186853 : Blo 107783 186853 := bbase (se 4 (by rfl) ⟨17517, by rfl⟩ : syracuseStep 186853 = 35035) (by norm_num)
theorem B121333 : Blo 107783 121333 := bbase (se 5 (by rfl) ⟨5687, by rfl⟩ : syracuseStep 121333 = 11375) (by norm_num)
theorem B121369 : Blo 107783 121369 := bbase (se 2 (by rfl) ⟨45513, by rfl⟩ : syracuseStep 121369 = 91027) (by norm_num)
theorem B121405 : Blo 107783 121405 := bbase (se 3 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 121405 = 45527) (by norm_num)
theorem B186941 : Blo 107783 186941 := bbase (se 3 (by rfl) ⟨35051, by rfl⟩ : syracuseStep 186941 = 70103) (by norm_num)
theorem B547397 : Blo 107783 547397 := bbase (se 4 (by rfl) ⟨51318, by rfl⟩ : syracuseStep 547397 = 102637) (by norm_num)
theorem B121441 : Blo 107783 121441 := bbase (se 2 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 121441 = 91081) (by norm_num)
theorem B154229 : Blo 107783 154229 := bbase (se 5 (by rfl) ⟨7229, by rfl⟩ : syracuseStep 154229 = 14459) (by norm_num)
theorem B121477 : Blo 107783 121477 := bbase (se 4 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 121477 = 22777) (by norm_num)
theorem B121513 : Blo 107783 121513 := bbase (se 2 (by rfl) ⟨45567, by rfl⟩ : syracuseStep 121513 = 91135) (by norm_num)
theorem B187069 : Blo 107783 187069 := bbase (se 3 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 187069 = 70151) (by norm_num)
theorem B121549 : Blo 107783 121549 := bbase (se 3 (by rfl) ⟨22790, by rfl⟩ : syracuseStep 121549 = 45581) (by norm_num)
theorem B121585 : Blo 107783 121585 := bbase (se 2 (by rfl) ⟨45594, by rfl⟩ : syracuseStep 121585 = 91189) (by norm_num)
theorem B121621 : Blo 107783 121621 := bbase (se 6 (by rfl) ⟨2850, by rfl⟩ : syracuseStep 121621 = 5701) (by norm_num)
theorem B187157 : Blo 107783 187157 := bbase (se 6 (by rfl) ⟨4386, by rfl⟩ : syracuseStep 187157 = 8773) (by norm_num)
theorem B121657 : Blo 107783 121657 := bbase (se 2 (by rfl) ⟨45621, by rfl⟩ : syracuseStep 121657 = 91243) (by norm_num)
theorem B121693 : Blo 107783 121693 := bbase (se 3 (by rfl) ⟨22817, by rfl⟩ : syracuseStep 121693 = 45635) (by norm_num)
theorem B121729 : Blo 107783 121729 := bbase (se 2 (by rfl) ⟨45648, by rfl⟩ : syracuseStep 121729 = 91297) (by norm_num)
theorem B187285 : Blo 107783 187285 := bbase (se 6 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 187285 = 8779) (by norm_num)
theorem B121765 : Blo 107783 121765 := bbase (se 4 (by rfl) ⟨11415, by rfl⟩ : syracuseStep 121765 = 22831) (by norm_num)
theorem B121801 : Blo 107783 121801 := bbase (se 2 (by rfl) ⟨45675, by rfl⟩ : syracuseStep 121801 = 91351) (by norm_num)
theorem B121837 : Blo 107783 121837 := bbase (se 3 (by rfl) ⟨22844, by rfl⟩ : syracuseStep 121837 = 45689) (by norm_num)
theorem B187373 : Blo 107783 187373 := bbase (se 3 (by rfl) ⟨35132, by rfl⟩ : syracuseStep 187373 = 70265) (by norm_num)
theorem B121873 : Blo 107783 121873 := bbase (se 2 (by rfl) ⟨45702, by rfl⟩ : syracuseStep 121873 = 91405) (by norm_num)
theorem B121909 : Blo 107783 121909 := bbase (se 5 (by rfl) ⟨5714, by rfl⟩ : syracuseStep 121909 = 11429) (by norm_num)
theorem B121945 : Blo 107783 121945 := bbase (se 2 (by rfl) ⟨45729, by rfl⟩ : syracuseStep 121945 = 91459) (by norm_num)
theorem B187501 : Blo 107783 187501 := bbase (se 3 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 187501 = 70313) (by norm_num)
theorem B121981 : Blo 107783 121981 := bbase (se 3 (by rfl) ⟨22871, by rfl⟩ : syracuseStep 121981 = 45743) (by norm_num)
theorem B122017 : Blo 107783 122017 := bbase (se 2 (by rfl) ⟨45756, by rfl⟩ : syracuseStep 122017 = 91513) (by norm_num)
theorem B122053 : Blo 107783 122053 := bbase (se 4 (by rfl) ⟨11442, by rfl⟩ : syracuseStep 122053 = 22885) (by norm_num)
theorem B187589 : Blo 107783 187589 := bbase (se 4 (by rfl) ⟨17586, by rfl⟩ : syracuseStep 187589 = 35173) (by norm_num)
theorem B122089 : Blo 107783 122089 := bbase (se 2 (by rfl) ⟨45783, by rfl⟩ : syracuseStep 122089 = 91567) (by norm_num)
theorem B122125 : Blo 107783 122125 := bbase (se 3 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 122125 = 45797) (by norm_num)
theorem B122161 : Blo 107783 122161 := bbase (se 2 (by rfl) ⟨45810, by rfl⟩ : syracuseStep 122161 = 91621) (by norm_num)
theorem B187717 : Blo 107783 187717 := bbase (se 4 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 187717 = 35197) (by norm_num)
theorem B122197 : Blo 107783 122197 := bbase (se 11 (by rfl) ⟨89, by rfl⟩ : syracuseStep 122197 = 179) (by norm_num)
theorem B417109 : Blo 107783 417109 := bbase (se 11 (by rfl) ⟨305, by rfl⟩ : syracuseStep 417109 = 611) (by norm_num)
theorem B154981 : Blo 107783 154981 := bbase (se 4 (by rfl) ⟨14529, by rfl⟩ : syracuseStep 154981 = 29059) (by norm_num)
theorem B122233 : Blo 107783 122233 := bbase (se 2 (by rfl) ⟨45837, by rfl⟩ : syracuseStep 122233 = 91675) (by norm_num)
theorem B122269 : Blo 107783 122269 := bbase (se 3 (by rfl) ⟨22925, by rfl⟩ : syracuseStep 122269 = 45851) (by norm_num)
theorem B187805 : Blo 107783 187805 := bbase (se 3 (by rfl) ⟨35213, by rfl⟩ : syracuseStep 187805 = 70427) (by norm_num)
theorem B122305 : Blo 107783 122305 := bbase (se 2 (by rfl) ⟨45864, by rfl⟩ : syracuseStep 122305 = 91729) (by norm_num)
theorem B2252245 : Blo 107783 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B122341 : Blo 107783 122341 := bbase (se 4 (by rfl) ⟨11469, by rfl⟩ : syracuseStep 122341 = 22939) (by norm_num)
theorem B122377 : Blo 107783 122377 := bbase (se 2 (by rfl) ⟨45891, by rfl⟩ : syracuseStep 122377 = 91783) (by norm_num)
theorem B187933 : Blo 107783 187933 := bbase (se 3 (by rfl) ⟨35237, by rfl⟩ : syracuseStep 187933 = 70475) (by norm_num)
theorem B122413 : Blo 107783 122413 := bbase (se 3 (by rfl) ⟨22952, by rfl⟩ : syracuseStep 122413 = 45905) (by norm_num)
theorem B122449 : Blo 107783 122449 := bbase (se 2 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 122449 = 91837) (by norm_num)
theorem B220781 : Blo 107783 220781 := bbase (se 3 (by rfl) ⟨41396, by rfl⟩ : syracuseStep 220781 = 82793) (by norm_num)
theorem B122485 : Blo 107783 122485 := bbase (se 5 (by rfl) ⟨5741, by rfl⟩ : syracuseStep 122485 = 11483) (by norm_num)
theorem B188021 : Blo 107783 188021 := bbase (se 5 (by rfl) ⟨8813, by rfl⟩ : syracuseStep 188021 = 17627) (by norm_num)
theorem B417413 : Blo 107783 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B122521 : Blo 107783 122521 := bbase (se 2 (by rfl) ⟨45945, by rfl⟩ : syracuseStep 122521 = 91891) (by norm_num)
theorem B122557 : Blo 107783 122557 := bbase (se 3 (by rfl) ⟨22979, by rfl⟩ : syracuseStep 122557 = 45959) (by norm_num)
theorem B122593 : Blo 107783 122593 := bbase (se 2 (by rfl) ⟨45972, by rfl⟩ : syracuseStep 122593 = 91945) (by norm_num)
theorem B351989 : Blo 107783 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B188149 : Blo 107783 188149 := bbase (se 5 (by rfl) ⟨8819, by rfl⟩ : syracuseStep 188149 = 17639) (by norm_num)
theorem B122629 : Blo 107783 122629 := bbase (se 4 (by rfl) ⟨11496, by rfl⟩ : syracuseStep 122629 = 22993) (by norm_num)
theorem B122665 : Blo 107783 122665 := bbase (se 2 (by rfl) ⟨45999, by rfl⟩ : syracuseStep 122665 = 91999) (by norm_num)
theorem B122701 : Blo 107783 122701 := bbase (se 3 (by rfl) ⟨23006, by rfl⟩ : syracuseStep 122701 = 46013) (by norm_num)
theorem B188237 : Blo 107783 188237 := bbase (se 3 (by rfl) ⟨35294, by rfl⟩ : syracuseStep 188237 = 70589) (by norm_num)
theorem B548693 : Blo 107783 548693 := bbase (se 9 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 548693 = 3215) (by norm_num)
theorem B122737 : Blo 107783 122737 := bbase (se 2 (by rfl) ⟨46026, by rfl⟩ : syracuseStep 122737 = 92053) (by norm_num)
theorem B122773 : Blo 107783 122773 := bbase (se 6 (by rfl) ⟨2877, by rfl⟩ : syracuseStep 122773 = 5755) (by norm_num)
theorem B286621 : Blo 107783 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B122809 : Blo 107783 122809 := bbase (se 2 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 122809 = 92107) (by norm_num)
theorem B188365 : Blo 107783 188365 := bbase (se 3 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 188365 = 70637) (by norm_num)
theorem B122845 : Blo 107783 122845 := bbase (se 3 (by rfl) ⟨23033, by rfl⟩ : syracuseStep 122845 = 46067) (by norm_num)
theorem B122881 : Blo 107783 122881 := bbase (se 2 (by rfl) ⟨46080, by rfl⟩ : syracuseStep 122881 = 92161) (by norm_num)
theorem B122917 : Blo 107783 122917 := bbase (se 4 (by rfl) ⟨11523, by rfl⟩ : syracuseStep 122917 = 23047) (by norm_num)
theorem B188453 : Blo 107783 188453 := bbase (se 4 (by rfl) ⟨17667, by rfl⟩ : syracuseStep 188453 = 35335) (by norm_num)
theorem B122953 : Blo 107783 122953 := bbase (se 2 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 122953 = 92215) (by norm_num)
theorem B122989 : Blo 107783 122989 := bbase (se 3 (by rfl) ⟨23060, by rfl⟩ : syracuseStep 122989 = 46121) (by norm_num)
theorem B450677 : Blo 107783 450677 := bbase (se 5 (by rfl) ⟨21125, by rfl⟩ : syracuseStep 450677 = 42251) (by norm_num)
theorem B155773 : Blo 107783 155773 := bbase (se 3 (by rfl) ⟨29207, by rfl⟩ : syracuseStep 155773 = 58415) (by norm_num)
theorem B123025 : Blo 107783 123025 := bbase (se 2 (by rfl) ⟨46134, by rfl⟩ : syracuseStep 123025 = 92269) (by norm_num)
theorem B188581 : Blo 107783 188581 := bbase (se 4 (by rfl) ⟨17679, by rfl⟩ : syracuseStep 188581 = 35359) (by norm_num)
theorem B123049 : Blo 107783 123049 := bbase (se 2 (by rfl) ⟨46143, by rfl⟩ : syracuseStep 123049 = 92287) (by norm_num)
theorem B123061 : Blo 107783 123061 := bbase (se 5 (by rfl) ⟨5768, by rfl⟩ : syracuseStep 123061 = 11537) (by norm_num)
theorem B123097 : Blo 107783 123097 := bbase (se 2 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 123097 = 92323) (by norm_num)
theorem B123133 : Blo 107783 123133 := bbase (se 3 (by rfl) ⟨23087, by rfl⟩ : syracuseStep 123133 = 46175) (by norm_num)
theorem B123169 : Blo 107783 123169 := bbase (se 2 (by rfl) ⟨46188, by rfl⟩ : syracuseStep 123169 = 92377) (by norm_num)
theorem B123205 : Blo 107783 123205 := bbase (se 4 (by rfl) ⟨11550, by rfl⟩ : syracuseStep 123205 = 23101) (by norm_num)
theorem B483685 : Blo 107783 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B123241 : Blo 107783 123241 := bbase (se 2 (by rfl) ⟨46215, by rfl⟩ : syracuseStep 123241 = 92431) (by norm_num)
theorem B123277 : Blo 107783 123277 := bbase (se 3 (by rfl) ⟨23114, by rfl⟩ : syracuseStep 123277 = 46229) (by norm_num)
theorem B844181 : Blo 107783 844181 := bbase (se 6 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 844181 = 39571) (by norm_num)
theorem B123313 : Blo 107783 123313 := bbase (se 2 (by rfl) ⟨46242, by rfl⟩ : syracuseStep 123313 = 92485) (by norm_num)
theorem B156109 : Blo 107783 156109 := bbase (se 3 (by rfl) ⟨29270, by rfl⟩ : syracuseStep 156109 = 58541) (by norm_num)
theorem B778709 : Blo 107783 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B123349 : Blo 107783 123349 := bbase (se 7 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 123349 = 2891) (by norm_num)
theorem B123377 : Blo 107783 123377 := bbase (se 2 (by rfl) ⟨46266, by rfl⟩ : syracuseStep 123377 = 92533) (by norm_num)
theorem B352757 : Blo 107783 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B123385 : Blo 107783 123385 := bbase (se 2 (by rfl) ⟨46269, by rfl⟩ : syracuseStep 123385 = 92539) (by norm_num)
theorem B123421 : Blo 107783 123421 := bbase (se 3 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 123421 = 46283) (by norm_num)
theorem B123457 : Blo 107783 123457 := bbase (se 2 (by rfl) ⟨46296, by rfl⟩ : syracuseStep 123457 = 92593) (by norm_num)
theorem B123493 : Blo 107783 123493 := bbase (se 4 (by rfl) ⟨11577, by rfl⟩ : syracuseStep 123493 = 23155) (by norm_num)
theorem B123529 : Blo 107783 123529 := bbase (se 2 (by rfl) ⟨46323, by rfl⟩ : syracuseStep 123529 = 92647) (by norm_num)
theorem B156325 : Blo 107783 156325 := bbase (se 4 (by rfl) ⟨14655, by rfl⟩ : syracuseStep 156325 = 29311) (by norm_num)
theorem B221869 : Blo 107783 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B123565 : Blo 107783 123565 := bbase (se 3 (by rfl) ⟨23168, by rfl⟩ : syracuseStep 123565 = 46337) (by norm_num)
theorem B123601 : Blo 107783 123601 := bbase (se 2 (by rfl) ⟨46350, by rfl⟩ : syracuseStep 123601 = 92701) (by norm_num)
theorem B123637 : Blo 107783 123637 := bbase (se 5 (by rfl) ⟨5795, by rfl⟩ : syracuseStep 123637 = 11591) (by norm_num)
theorem B123673 : Blo 107783 123673 := bbase (se 2 (by rfl) ⟨46377, by rfl⟩ : syracuseStep 123673 = 92755) (by norm_num)
theorem B123709 : Blo 107783 123709 := bbase (se 3 (by rfl) ⟨23195, by rfl⟩ : syracuseStep 123709 = 46391) (by norm_num)
theorem B123745 : Blo 107783 123745 := bbase (se 2 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 123745 = 92809) (by norm_num)
theorem B123781 : Blo 107783 123781 := bbase (se 4 (by rfl) ⟨11604, by rfl⟩ : syracuseStep 123781 = 23209) (by norm_num)
theorem B123817 : Blo 107783 123817 := bbase (se 2 (by rfl) ⟨46431, by rfl⟩ : syracuseStep 123817 = 92863) (by norm_num)
theorem B123853 : Blo 107783 123853 := bbase (se 3 (by rfl) ⟨23222, by rfl⟩ : syracuseStep 123853 = 46445) (by norm_num)
theorem B123889 : Blo 107783 123889 := bbase (se 2 (by rfl) ⟨46458, by rfl⟩ : syracuseStep 123889 = 92917) (by norm_num)
theorem B353269 : Blo 107783 353269 := bbase (se 5 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 353269 = 33119) (by norm_num)
theorem B123925 : Blo 107783 123925 := bbase (se 6 (by rfl) ⟨2904, by rfl⟩ : syracuseStep 123925 = 5809) (by norm_num)
theorem B156701 : Blo 107783 156701 := bbase (se 3 (by rfl) ⟨29381, by rfl⟩ : syracuseStep 156701 = 58763) (by norm_num)
theorem B123961 : Blo 107783 123961 := bbase (se 2 (by rfl) ⟨46485, by rfl⟩ : syracuseStep 123961 = 92971) (by norm_num)
theorem B123997 : Blo 107783 123997 := bbase (se 3 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 123997 = 46499) (by norm_num)
theorem B549989 : Blo 107783 549989 := bbase (se 4 (by rfl) ⟨51561, by rfl⟩ : syracuseStep 549989 = 103123) (by norm_num)
theorem B124033 : Blo 107783 124033 := bbase (se 2 (by rfl) ⟨46512, by rfl⟩ : syracuseStep 124033 = 93025) (by norm_num)
theorem B124069 : Blo 107783 124069 := bbase (se 4 (by rfl) ⟨11631, by rfl⟩ : syracuseStep 124069 = 23263) (by norm_num)
theorem B124105 : Blo 107783 124105 := bbase (se 2 (by rfl) ⟨46539, by rfl⟩ : syracuseStep 124105 = 93079) (by norm_num)
theorem B451813 : Blo 107783 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B124141 : Blo 107783 124141 := bbase (se 3 (by rfl) ⟨23276, by rfl⟩ : syracuseStep 124141 = 46553) (by norm_num)
theorem B124177 : Blo 107783 124177 := bbase (se 2 (by rfl) ⟨46566, by rfl⟩ : syracuseStep 124177 = 93133) (by norm_num)
theorem B124213 : Blo 107783 124213 := bbase (se 5 (by rfl) ⟨5822, by rfl⟩ : syracuseStep 124213 = 11645) (by norm_num)
theorem B255293 : Blo 107783 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B124249 : Blo 107783 124249 := bbase (se 2 (by rfl) ⟨46593, by rfl⟩ : syracuseStep 124249 = 93187) (by norm_num)
theorem B124285 : Blo 107783 124285 := bbase (se 3 (by rfl) ⟨23303, by rfl⟩ : syracuseStep 124285 = 46607) (by norm_num)
theorem B124321 : Blo 107783 124321 := bbase (se 2 (by rfl) ⟨46620, by rfl⟩ : syracuseStep 124321 = 93241) (by norm_num)
theorem B124357 : Blo 107783 124357 := bbase (se 4 (by rfl) ⟨11658, by rfl⟩ : syracuseStep 124357 = 23317) (by norm_num)
theorem B124393 : Blo 107783 124393 := bbase (se 2 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 124393 = 93295) (by norm_num)
theorem B976373 : Blo 107783 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B124429 : Blo 107783 124429 := bbase (se 3 (by rfl) ⟨23330, by rfl⟩ : syracuseStep 124429 = 46661) (by norm_num)
theorem B124465 : Blo 107783 124465 := bbase (se 2 (by rfl) ⟨46674, by rfl⟩ : syracuseStep 124465 = 93349) (by norm_num)
theorem B124501 : Blo 107783 124501 := bbase (se 8 (by rfl) ⟨729, by rfl⟩ : syracuseStep 124501 = 1459) (by norm_num)
theorem B124537 : Blo 107783 124537 := bbase (se 2 (by rfl) ⟨46701, by rfl⟩ : syracuseStep 124537 = 93403) (by norm_num)
theorem B124573 : Blo 107783 124573 := bbase (se 3 (by rfl) ⟨23357, by rfl⟩ : syracuseStep 124573 = 46715) (by norm_num)
theorem B124609 : Blo 107783 124609 := bbase (se 2 (by rfl) ⟨46728, by rfl⟩ : syracuseStep 124609 = 93457) (by norm_num)
theorem B419525 : Blo 107783 419525 := bbase (se 4 (by rfl) ⟨39330, by rfl⟩ : syracuseStep 419525 = 78661) (by norm_num)
theorem B124645 : Blo 107783 124645 := bbase (se 4 (by rfl) ⟨11685, by rfl⟩ : syracuseStep 124645 = 23371) (by norm_num)
theorem B124681 : Blo 107783 124681 := bbase (se 2 (by rfl) ⟨46755, by rfl⟩ : syracuseStep 124681 = 93511) (by norm_num)
theorem B124717 : Blo 107783 124717 := bbase (se 3 (by rfl) ⟨23384, by rfl⟩ : syracuseStep 124717 = 46769) (by norm_num)
theorem B124753 : Blo 107783 124753 := bbase (se 2 (by rfl) ⟨46782, by rfl⟩ : syracuseStep 124753 = 93565) (by norm_num)
theorem B223069 : Blo 107783 223069 := bbase (se 3 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 223069 = 83651) (by norm_num)
theorem B124789 : Blo 107783 124789 := bbase (se 5 (by rfl) ⟨5849, by rfl⟩ : syracuseStep 124789 = 11699) (by norm_num)
theorem B124825 : Blo 107783 124825 := bbase (se 2 (by rfl) ⟨46809, by rfl⟩ : syracuseStep 124825 = 93619) (by norm_num)
theorem B124861 : Blo 107783 124861 := bbase (se 3 (by rfl) ⟨23411, by rfl⟩ : syracuseStep 124861 = 46823) (by norm_num)
theorem B124897 : Blo 107783 124897 := bbase (se 2 (by rfl) ⟨46836, by rfl⟩ : syracuseStep 124897 = 93673) (by norm_num)
theorem B419813 : Blo 107783 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B124933 : Blo 107783 124933 := bbase (se 4 (by rfl) ⟨11712, by rfl⟩ : syracuseStep 124933 = 23425) (by norm_num)
theorem B124969 : Blo 107783 124969 := bbase (se 2 (by rfl) ⟨46863, by rfl⟩ : syracuseStep 124969 = 93727) (by norm_num)
theorem B125005 : Blo 107783 125005 := bbase (se 3 (by rfl) ⟨23438, by rfl⟩ : syracuseStep 125005 = 46877) (by norm_num)
theorem B125041 : Blo 107783 125041 := bbase (se 2 (by rfl) ⟨46890, by rfl⟩ : syracuseStep 125041 = 93781) (by norm_num)
theorem B256117 : Blo 107783 256117 := bbase (se 5 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 256117 = 24011) (by norm_num)
theorem B125077 : Blo 107783 125077 := bbase (se 6 (by rfl) ⟨2931, by rfl⟩ : syracuseStep 125077 = 5863) (by norm_num)
theorem B583861 : Blo 107783 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B125113 : Blo 107783 125113 := bbase (se 2 (by rfl) ⟨46917, by rfl⟩ : syracuseStep 125113 = 93835) (by norm_num)
theorem B125149 : Blo 107783 125149 := bbase (se 3 (by rfl) ⟨23465, by rfl⟩ : syracuseStep 125149 = 46931) (by norm_num)
theorem B125185 : Blo 107783 125185 := bbase (se 2 (by rfl) ⟨46944, by rfl⟩ : syracuseStep 125185 = 93889) (by norm_num)
theorem B125221 : Blo 107783 125221 := bbase (se 4 (by rfl) ⟨11739, by rfl⟩ : syracuseStep 125221 = 23479) (by norm_num)
theorem B125257 : Blo 107783 125257 := bbase (se 2 (by rfl) ⟨46971, by rfl⟩ : syracuseStep 125257 = 93943) (by norm_num)
theorem B125293 : Blo 107783 125293 := bbase (se 3 (by rfl) ⟨23492, by rfl⟩ : syracuseStep 125293 = 46985) (by norm_num)
theorem B551285 : Blo 107783 551285 := bbase (se 5 (by rfl) ⟨25841, by rfl⟩ : syracuseStep 551285 = 51683) (by norm_num)
theorem B125329 : Blo 107783 125329 := bbase (se 2 (by rfl) ⟨46998, by rfl⟩ : syracuseStep 125329 = 93997) (by norm_num)
theorem B158125 : Blo 107783 158125 := bbase (se 3 (by rfl) ⟨29648, by rfl⟩ : syracuseStep 158125 = 59297) (by norm_num)
theorem B125365 : Blo 107783 125365 := bbase (se 5 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 125365 = 11753) (by norm_num)
theorem B125401 : Blo 107783 125401 := bbase (se 2 (by rfl) ⟨47025, by rfl⟩ : syracuseStep 125401 = 94051) (by norm_num)
theorem B125437 : Blo 107783 125437 := bbase (se 3 (by rfl) ⟨23519, by rfl⟩ : syracuseStep 125437 = 47039) (by norm_num)
theorem B125473 : Blo 107783 125473 := bbase (se 2 (by rfl) ⟨47052, by rfl⟩ : syracuseStep 125473 = 94105) (by norm_num)
theorem B125509 : Blo 107783 125509 := bbase (se 4 (by rfl) ⟨11766, by rfl⟩ : syracuseStep 125509 = 23533) (by norm_num)
theorem B453205 : Blo 107783 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B125545 : Blo 107783 125545 := bbase (se 2 (by rfl) ⟨47079, by rfl⟩ : syracuseStep 125545 = 94159) (by norm_num)
theorem B125581 : Blo 107783 125581 := bbase (se 3 (by rfl) ⟨23546, by rfl⟩ : syracuseStep 125581 = 47093) (by norm_num)
theorem B125617 : Blo 107783 125617 := bbase (se 2 (by rfl) ⟨47106, by rfl⟩ : syracuseStep 125617 = 94213) (by norm_num)
theorem B355013 : Blo 107783 355013 := bbase (se 4 (by rfl) ⟨33282, by rfl⟩ : syracuseStep 355013 = 66565) (by norm_num)
theorem B125653 : Blo 107783 125653 := bbase (se 7 (by rfl) ⟨1472, by rfl⟩ : syracuseStep 125653 = 2945) (by norm_num)
theorem B125689 : Blo 107783 125689 := bbase (se 2 (by rfl) ⟨47133, by rfl⟩ : syracuseStep 125689 = 94267) (by norm_num)
theorem B125713 : Blo 107783 125713 := bbase (se 2 (by rfl) ⟨47142, by rfl⟩ : syracuseStep 125713 = 94285) (by norm_num)
theorem B125725 : Blo 107783 125725 := bbase (se 3 (by rfl) ⟨23573, by rfl⟩ : syracuseStep 125725 = 47147) (by norm_num)
theorem B355205 : Blo 107783 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B584597 : Blo 107783 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B420821 : Blo 107783 420821 := bbase (se 7 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 420821 = 9863) (by norm_num)
theorem B158717 : Blo 107783 158717 := bbase (se 3 (by rfl) ⟨29759, by rfl⟩ : syracuseStep 158717 = 59519) (by norm_num)
theorem B158797 : Blo 107783 158797 := bbase (se 3 (by rfl) ⟨29774, by rfl⟩ : syracuseStep 158797 = 59549) (by norm_num)
theorem B126041 : Blo 107783 126041 := bbase (se 2 (by rfl) ⟨47265, by rfl⟩ : syracuseStep 126041 = 94531) (by norm_num)
theorem B420997 : Blo 107783 420997 := bbase (se 4 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 420997 = 78937) (by norm_num)
theorem B158917 : Blo 107783 158917 := bbase (se 4 (by rfl) ⟨14898, by rfl⟩ : syracuseStep 158917 = 29797) (by norm_num)
theorem B159013 : Blo 107783 159013 := bbase (se 4 (by rfl) ⟨14907, by rfl⟩ : syracuseStep 159013 = 29815) (by norm_num)
theorem B421301 : Blo 107783 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B355909 : Blo 107783 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B224869 : Blo 107783 224869 := bbase (se 4 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 224869 = 42163) (by norm_num)
theorem B618101 : Blo 107783 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B126589 : Blo 107783 126589 := bbase (se 3 (by rfl) ⟨23735, by rfl⟩ : syracuseStep 126589 = 47471) (by norm_num)
theorem B552581 : Blo 107783 552581 := bbase (se 4 (by rfl) ⟨51804, by rfl⟩ : syracuseStep 552581 = 103609) (by norm_num)
theorem B945877 : Blo 107783 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B716597 : Blo 107783 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B127013 : Blo 107783 127013 := bbase (se 4 (by rfl) ⟨11907, by rfl⟩ : syracuseStep 127013 = 23815) (by norm_num)
theorem B619285 : Blo 107783 619285 := bbase (se 6 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 619285 = 29029) (by norm_num)
theorem B750389 : Blo 107783 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B553877 : Blo 107783 553877 := bbase (se 6 (by rfl) ⟨12981, by rfl⟩ : syracuseStep 553877 = 25963) (by norm_num)
theorem B259109 : Blo 107783 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B259205 : Blo 107783 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B390277 : Blo 107783 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B423413 : Blo 107783 423413 := bbase (se 5 (by rfl) ⟨19847, by rfl⟩ : syracuseStep 423413 = 39695) (by norm_num)
theorem B947861 : Blo 107783 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B521909 : Blo 107783 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B423701 : Blo 107783 423701 := bbase (se 6 (by rfl) ⟨9930, by rfl⟩ : syracuseStep 423701 = 19861) (by norm_num)
theorem B1046357 : Blo 107783 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B522101 : Blo 107783 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B161693 : Blo 107783 161693 := bbase (se 3 (by rfl) ⟨30317, by rfl⟩ : syracuseStep 161693 = 60635) (by norm_num)
theorem B161717 : Blo 107783 161717 := bbase (se 5 (by rfl) ⟨7580, by rfl⟩ : syracuseStep 161717 = 15161) (by norm_num)
theorem B161741 : Blo 107783 161741 := bbase (se 3 (by rfl) ⟨30326, by rfl⟩ : syracuseStep 161741 = 60653) (by norm_num)
theorem B161765 : Blo 107783 161765 := bbase (se 4 (by rfl) ⟨15165, by rfl⟩ : syracuseStep 161765 = 30331) (by norm_num)
theorem B161789 : Blo 107783 161789 := bbase (se 3 (by rfl) ⟨30335, by rfl⟩ : syracuseStep 161789 = 60671) (by norm_num)
theorem B161813 : Blo 107783 161813 := bbase (se 6 (by rfl) ⟨3792, by rfl⟩ : syracuseStep 161813 = 7585) (by norm_num)
theorem B391189 : Blo 107783 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B161837 : Blo 107783 161837 := bbase (se 3 (by rfl) ⟨30344, by rfl⟩ : syracuseStep 161837 = 60689) (by norm_num)
theorem B161861 : Blo 107783 161861 := bbase (se 4 (by rfl) ⟨15174, by rfl⟩ : syracuseStep 161861 = 30349) (by norm_num)
theorem B161885 : Blo 107783 161885 := bbase (se 3 (by rfl) ⟨30353, by rfl⟩ : syracuseStep 161885 = 60707) (by norm_num)
theorem B161909 : Blo 107783 161909 := bbase (se 5 (by rfl) ⟨7589, by rfl⟩ : syracuseStep 161909 = 15179) (by norm_num)
theorem B161933 : Blo 107783 161933 := bbase (se 3 (by rfl) ⟨30362, by rfl⟩ : syracuseStep 161933 = 60725) (by norm_num)
theorem B161957 : Blo 107783 161957 := bbase (se 4 (by rfl) ⟨15183, by rfl⟩ : syracuseStep 161957 = 30367) (by norm_num)
theorem B555173 : Blo 107783 555173 := bbase (se 4 (by rfl) ⟨52047, by rfl⟩ : syracuseStep 555173 = 104095) (by norm_num)
theorem B161981 : Blo 107783 161981 := bbase (se 3 (by rfl) ⟨30371, by rfl⟩ : syracuseStep 161981 = 60743) (by norm_num)
theorem B162005 : Blo 107783 162005 := bbase (se 7 (by rfl) ⟨1898, by rfl⟩ : syracuseStep 162005 = 3797) (by norm_num)
theorem B162029 : Blo 107783 162029 := bbase (se 3 (by rfl) ⟨30380, by rfl⟩ : syracuseStep 162029 = 60761) (by norm_num)
theorem B162053 : Blo 107783 162053 := bbase (se 4 (by rfl) ⟨15192, by rfl⟩ : syracuseStep 162053 = 30385) (by norm_num)
theorem B162077 : Blo 107783 162077 := bbase (se 3 (by rfl) ⟨30389, by rfl⟩ : syracuseStep 162077 = 60779) (by norm_num)
theorem B194845 : Blo 107783 194845 := bbase (se 3 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 194845 = 73067) (by norm_num)
theorem B162101 : Blo 107783 162101 := bbase (se 5 (by rfl) ⟨7598, by rfl⟩ : syracuseStep 162101 = 15197) (by norm_num)
theorem B162125 : Blo 107783 162125 := bbase (se 3 (by rfl) ⟨30398, by rfl⟩ : syracuseStep 162125 = 60797) (by norm_num)
theorem B162149 : Blo 107783 162149 := bbase (se 4 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 162149 = 30403) (by norm_num)
theorem B162173 : Blo 107783 162173 := bbase (se 3 (by rfl) ⟨30407, by rfl⟩ : syracuseStep 162173 = 60815) (by norm_num)
theorem B162197 : Blo 107783 162197 := bbase (se 6 (by rfl) ⟨3801, by rfl⟩ : syracuseStep 162197 = 7603) (by norm_num)
theorem B162221 : Blo 107783 162221 := bbase (se 3 (by rfl) ⟨30416, by rfl⟩ : syracuseStep 162221 = 60833) (by norm_num)
theorem B162245 : Blo 107783 162245 := bbase (se 4 (by rfl) ⟨15210, by rfl⟩ : syracuseStep 162245 = 30421) (by norm_num)
theorem B162269 : Blo 107783 162269 := bbase (se 3 (by rfl) ⟨30425, by rfl⟩ : syracuseStep 162269 = 60851) (by norm_num)
theorem B195053 : Blo 107783 195053 := bbase (se 3 (by rfl) ⟨36572, by rfl⟩ : syracuseStep 195053 = 73145) (by norm_num)
theorem B162293 : Blo 107783 162293 := bbase (se 5 (by rfl) ⟨7607, by rfl⟩ : syracuseStep 162293 = 15215) (by norm_num)
theorem B162317 : Blo 107783 162317 := bbase (se 3 (by rfl) ⟨30434, by rfl⟩ : syracuseStep 162317 = 60869) (by norm_num)
theorem B162341 : Blo 107783 162341 := bbase (se 4 (by rfl) ⟨15219, by rfl⟩ : syracuseStep 162341 = 30439) (by norm_num)
theorem B162365 : Blo 107783 162365 := bbase (se 3 (by rfl) ⟨30443, by rfl⟩ : syracuseStep 162365 = 60887) (by norm_num)
theorem B162389 : Blo 107783 162389 := bbase (se 8 (by rfl) ⟨951, by rfl⟩ : syracuseStep 162389 = 1903) (by norm_num)
theorem B162413 : Blo 107783 162413 := bbase (se 3 (by rfl) ⟨30452, by rfl⟩ : syracuseStep 162413 = 60905) (by norm_num)
theorem B162437 : Blo 107783 162437 := bbase (se 4 (by rfl) ⟨15228, by rfl⟩ : syracuseStep 162437 = 30457) (by norm_num)
theorem B162461 : Blo 107783 162461 := bbase (se 3 (by rfl) ⟨30461, by rfl⟩ : syracuseStep 162461 = 60923) (by norm_num)
theorem B162485 : Blo 107783 162485 := bbase (se 5 (by rfl) ⟨7616, by rfl⟩ : syracuseStep 162485 = 15233) (by norm_num)
theorem B162509 : Blo 107783 162509 := bbase (se 3 (by rfl) ⟨30470, by rfl⟩ : syracuseStep 162509 = 60941) (by norm_num)
theorem B621269 : Blo 107783 621269 := bbase (se 7 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 621269 = 14561) (by norm_num)
theorem B129757 : Blo 107783 129757 := bbase (se 3 (by rfl) ⟨24329, by rfl⟩ : syracuseStep 129757 = 48659) (by norm_num)
theorem B162533 : Blo 107783 162533 := bbase (se 4 (by rfl) ⟨15237, by rfl⟩ : syracuseStep 162533 = 30475) (by norm_num)
theorem B162557 : Blo 107783 162557 := bbase (se 3 (by rfl) ⟨30479, by rfl⟩ : syracuseStep 162557 = 60959) (by norm_num)
theorem B162581 : Blo 107783 162581 := bbase (se 6 (by rfl) ⟨3810, by rfl⟩ : syracuseStep 162581 = 7621) (by norm_num)
theorem B162605 : Blo 107783 162605 := bbase (se 3 (by rfl) ⟨30488, by rfl⟩ : syracuseStep 162605 = 60977) (by norm_num)
theorem B162629 : Blo 107783 162629 := bbase (se 4 (by rfl) ⟨15246, by rfl⟩ : syracuseStep 162629 = 30493) (by norm_num)
theorem B162653 : Blo 107783 162653 := bbase (se 3 (by rfl) ⟨30497, by rfl⟩ : syracuseStep 162653 = 60995) (by norm_num)
theorem B162677 : Blo 107783 162677 := bbase (se 5 (by rfl) ⟨7625, by rfl⟩ : syracuseStep 162677 = 15251) (by norm_num)
theorem B162701 : Blo 107783 162701 := bbase (se 3 (by rfl) ⟨30506, by rfl⟩ : syracuseStep 162701 = 61013) (by norm_num)
theorem B162725 : Blo 107783 162725 := bbase (se 4 (by rfl) ⟨15255, by rfl⟩ : syracuseStep 162725 = 30511) (by norm_num)
theorem B129973 : Blo 107783 129973 := bbase (se 5 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 129973 = 12185) (by norm_num)
theorem B162749 : Blo 107783 162749 := bbase (se 3 (by rfl) ⟨30515, by rfl⟩ : syracuseStep 162749 = 61031) (by norm_num)
theorem B162773 : Blo 107783 162773 := bbase (se 7 (by rfl) ⟨1907, by rfl⟩ : syracuseStep 162773 = 3815) (by norm_num)
theorem B162797 : Blo 107783 162797 := bbase (se 3 (by rfl) ⟨30524, by rfl⟩ : syracuseStep 162797 = 61049) (by norm_num)
theorem B162821 : Blo 107783 162821 := bbase (se 4 (by rfl) ⟨15264, by rfl⟩ : syracuseStep 162821 = 30529) (by norm_num)
theorem B162845 : Blo 107783 162845 := bbase (se 3 (by rfl) ⟨30533, by rfl⟩ : syracuseStep 162845 = 61067) (by norm_num)
theorem B162869 : Blo 107783 162869 := bbase (se 5 (by rfl) ⟨7634, by rfl⟩ : syracuseStep 162869 = 15269) (by norm_num)
theorem B162893 : Blo 107783 162893 := bbase (se 3 (by rfl) ⟨30542, by rfl⟩ : syracuseStep 162893 = 61085) (by norm_num)
theorem B162917 : Blo 107783 162917 := bbase (se 4 (by rfl) ⟨15273, by rfl⟩ : syracuseStep 162917 = 30547) (by norm_num)
theorem B162941 : Blo 107783 162941 := bbase (se 3 (by rfl) ⟨30551, by rfl⟩ : syracuseStep 162941 = 61103) (by norm_num)
theorem B162965 : Blo 107783 162965 := bbase (se 6 (by rfl) ⟨3819, by rfl⟩ : syracuseStep 162965 = 7639) (by norm_num)
theorem B162989 : Blo 107783 162989 := bbase (se 3 (by rfl) ⟨30560, by rfl⟩ : syracuseStep 162989 = 61121) (by norm_num)
theorem B261301 : Blo 107783 261301 := bbase (se 5 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 261301 = 24497) (by norm_num)
theorem B163013 : Blo 107783 163013 := bbase (se 4 (by rfl) ⟨15282, by rfl⟩ : syracuseStep 163013 = 30565) (by norm_num)
theorem B163037 : Blo 107783 163037 := bbase (se 3 (by rfl) ⟨30569, by rfl⟩ : syracuseStep 163037 = 61139) (by norm_num)
theorem B130285 : Blo 107783 130285 := bbase (se 3 (by rfl) ⟨24428, by rfl⟩ : syracuseStep 130285 = 48857) (by norm_num)
theorem B163061 : Blo 107783 163061 := bbase (se 5 (by rfl) ⟨7643, by rfl⟩ : syracuseStep 163061 = 15287) (by norm_num)
theorem B163085 : Blo 107783 163085 := bbase (se 3 (by rfl) ⟨30578, by rfl⟩ : syracuseStep 163085 = 61157) (by norm_num)
theorem B163109 : Blo 107783 163109 := bbase (se 4 (by rfl) ⟨15291, by rfl⟩ : syracuseStep 163109 = 30583) (by norm_num)
theorem B163133 : Blo 107783 163133 := bbase (se 3 (by rfl) ⟨30587, by rfl⟩ : syracuseStep 163133 = 61175) (by norm_num)
theorem B163157 : Blo 107783 163157 := bbase (se 11 (by rfl) ⟨119, by rfl⟩ : syracuseStep 163157 = 239) (by norm_num)
theorem B163181 : Blo 107783 163181 := bbase (se 3 (by rfl) ⟨30596, by rfl⟩ : syracuseStep 163181 = 61193) (by norm_num)
theorem B163205 : Blo 107783 163205 := bbase (se 4 (by rfl) ⟨15300, by rfl⟩ : syracuseStep 163205 = 30601) (by norm_num)
theorem B163229 : Blo 107783 163229 := bbase (se 3 (by rfl) ⟨30605, by rfl⟩ : syracuseStep 163229 = 61211) (by norm_num)
theorem B163253 : Blo 107783 163253 := bbase (se 5 (by rfl) ⟨7652, by rfl⟩ : syracuseStep 163253 = 15305) (by norm_num)
theorem B556469 : Blo 107783 556469 := bbase (se 5 (by rfl) ⟨26084, by rfl⟩ : syracuseStep 556469 = 52169) (by norm_num)
theorem B163277 : Blo 107783 163277 := bbase (se 3 (by rfl) ⟨30614, by rfl⟩ : syracuseStep 163277 = 61229) (by norm_num)
theorem B163301 : Blo 107783 163301 := bbase (se 4 (by rfl) ⟨15309, by rfl⟩ : syracuseStep 163301 = 30619) (by norm_num)
theorem B163325 : Blo 107783 163325 := bbase (se 3 (by rfl) ⟨30623, by rfl⟩ : syracuseStep 163325 = 61247) (by norm_num)
theorem B163349 : Blo 107783 163349 := bbase (se 6 (by rfl) ⟨3828, by rfl⟩ : syracuseStep 163349 = 7657) (by norm_num)
theorem B163373 : Blo 107783 163373 := bbase (se 3 (by rfl) ⟨30632, by rfl⟩ : syracuseStep 163373 = 61265) (by norm_num)
theorem B163397 : Blo 107783 163397 := bbase (se 4 (by rfl) ⟨15318, by rfl⟩ : syracuseStep 163397 = 30637) (by norm_num)
theorem B163421 : Blo 107783 163421 := bbase (se 3 (by rfl) ⟨30641, by rfl⟩ : syracuseStep 163421 = 61283) (by norm_num)
theorem B163445 : Blo 107783 163445 := bbase (se 5 (by rfl) ⟨7661, by rfl⟩ : syracuseStep 163445 = 15323) (by norm_num)
theorem B163469 : Blo 107783 163469 := bbase (se 3 (by rfl) ⟨30650, by rfl⟩ : syracuseStep 163469 = 61301) (by norm_num)
theorem B163493 : Blo 107783 163493 := bbase (se 4 (by rfl) ⟨15327, by rfl⟩ : syracuseStep 163493 = 30655) (by norm_num)
theorem B163517 : Blo 107783 163517 := bbase (se 3 (by rfl) ⟨30659, by rfl⟩ : syracuseStep 163517 = 61319) (by norm_num)
theorem B163541 : Blo 107783 163541 := bbase (se 7 (by rfl) ⟨1916, by rfl⟩ : syracuseStep 163541 = 3833) (by norm_num)
theorem B163565 : Blo 107783 163565 := bbase (se 3 (by rfl) ⟨30668, by rfl⟩ : syracuseStep 163565 = 61337) (by norm_num)
theorem B130817 : Blo 107783 130817 := bbase (se 2 (by rfl) ⟨49056, by rfl⟩ : syracuseStep 130817 = 98113) (by norm_num)
theorem B163589 : Blo 107783 163589 := bbase (se 4 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 163589 = 30673) (by norm_num)
theorem B261917 : Blo 107783 261917 := bbase (se 3 (by rfl) ⟨49109, by rfl⟩ : syracuseStep 261917 = 98219) (by norm_num)
theorem B163613 : Blo 107783 163613 := bbase (se 3 (by rfl) ⟨30677, by rfl⟩ : syracuseStep 163613 = 61355) (by norm_num)
theorem B163637 : Blo 107783 163637 := bbase (se 5 (by rfl) ⟨7670, by rfl⟩ : syracuseStep 163637 = 15341) (by norm_num)
theorem B163661 : Blo 107783 163661 := bbase (se 3 (by rfl) ⟨30686, by rfl⟩ : syracuseStep 163661 = 61373) (by norm_num)
theorem B3211093 : Blo 107783 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B163685 : Blo 107783 163685 := bbase (se 4 (by rfl) ⟨15345, by rfl⟩ : syracuseStep 163685 = 30691) (by norm_num)
theorem B163709 : Blo 107783 163709 := bbase (se 3 (by rfl) ⟨30695, by rfl⟩ : syracuseStep 163709 = 61391) (by norm_num)
theorem B163733 : Blo 107783 163733 := bbase (se 6 (by rfl) ⟨3837, by rfl⟩ : syracuseStep 163733 = 7675) (by norm_num)
theorem B163757 : Blo 107783 163757 := bbase (se 3 (by rfl) ⟨30704, by rfl⟩ : syracuseStep 163757 = 61409) (by norm_num)
theorem B163781 : Blo 107783 163781 := bbase (se 4 (by rfl) ⟨15354, by rfl⟩ : syracuseStep 163781 = 30709) (by norm_num)
theorem B163805 : Blo 107783 163805 := bbase (se 3 (by rfl) ⟨30713, by rfl⟩ : syracuseStep 163805 = 61427) (by norm_num)
theorem B163829 : Blo 107783 163829 := bbase (se 5 (by rfl) ⟨7679, by rfl⟩ : syracuseStep 163829 = 15359) (by norm_num)
theorem B163841 : Blo 107783 163841 := bstep (se 2 (by rfl) ⟨61440, by rfl⟩ : syracuseStep 163841 = 122881) B122881
theorem B163859 : Blo 107783 163859 := bstep (se 1 (by rfl) ⟨122894, by rfl⟩ : syracuseStep 163859 = 245789) B245789
theorem B163889 : Blo 107783 163889 := bstep (se 2 (by rfl) ⟨61458, by rfl⟩ : syracuseStep 163889 = 122917) B122917
theorem B163907 : Blo 107783 163907 := bstep (se 1 (by rfl) ⟨122930, by rfl⟩ : syracuseStep 163907 = 245861) B245861
theorem B163937 : Blo 107783 163937 := bstep (se 2 (by rfl) ⟨61476, by rfl⟩ : syracuseStep 163937 = 122953) B122953
theorem B163955 : Blo 107783 163955 := bstep (se 1 (by rfl) ⟨122966, by rfl⟩ : syracuseStep 163955 = 245933) B245933
theorem B131203 : Blo 107783 131203 := bstep (se 1 (by rfl) ⟨98402, by rfl⟩ : syracuseStep 131203 = 196805) B196805
theorem B163985 : Blo 107783 163985 := bstep (se 2 (by rfl) ⟨61494, by rfl⟩ : syracuseStep 163985 = 122989) B122989
theorem B164003 : Blo 107783 164003 := bstep (se 1 (by rfl) ⟨123002, by rfl⟩ : syracuseStep 164003 = 246005) B246005
theorem B164033 : Blo 107783 164033 := bstep (se 2 (by rfl) ⟨61512, by rfl⟩ : syracuseStep 164033 = 123025) B123025
theorem B164051 : Blo 107783 164051 := bstep (se 1 (by rfl) ⟨123038, by rfl⟩ : syracuseStep 164051 = 246077) B246077
theorem B164081 : Blo 107783 164081 := bstep (se 2 (by rfl) ⟨61530, by rfl⟩ : syracuseStep 164081 = 123061) B123061
theorem B164099 : Blo 107783 164099 := bstep (se 1 (by rfl) ⟨123074, by rfl⟩ : syracuseStep 164099 = 246149) B246149
theorem B164129 : Blo 107783 164129 := bstep (se 2 (by rfl) ⟨61548, by rfl⟩ : syracuseStep 164129 = 123097) B123097
theorem B262435 : Blo 107783 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B164147 : Blo 107783 164147 := bstep (se 1 (by rfl) ⟨123110, by rfl⟩ : syracuseStep 164147 = 246221) B246221
theorem B164177 : Blo 107783 164177 := bstep (se 2 (by rfl) ⟨61566, by rfl⟩ : syracuseStep 164177 = 123133) B123133
theorem B164195 : Blo 107783 164195 := bstep (se 1 (by rfl) ⟨123146, by rfl⟩ : syracuseStep 164195 = 246293) B246293
theorem B164225 : Blo 107783 164225 := bstep (se 2 (by rfl) ⟨61584, by rfl⟩ : syracuseStep 164225 = 123169) B123169
theorem B262531 : Blo 107783 262531 := bstep (se 1 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 262531 = 393797) B393797
theorem B164243 : Blo 107783 164243 := bstep (se 1 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 164243 = 246365) B246365
theorem B164273 : Blo 107783 164273 := bstep (se 2 (by rfl) ⟨61602, by rfl⟩ : syracuseStep 164273 = 123205) B123205
theorem B164291 : Blo 107783 164291 := bstep (se 1 (by rfl) ⟨123218, by rfl⟩ : syracuseStep 164291 = 246437) B246437
theorem B164321 : Blo 107783 164321 := bstep (se 2 (by rfl) ⟨61620, by rfl⟩ : syracuseStep 164321 = 123241) B123241
theorem B164339 : Blo 107783 164339 := bstep (se 1 (by rfl) ⟨123254, by rfl⟩ : syracuseStep 164339 = 246509) B246509
theorem B164369 : Blo 107783 164369 := bstep (se 2 (by rfl) ⟨61638, by rfl⟩ : syracuseStep 164369 = 123277) B123277
theorem B164387 : Blo 107783 164387 := bstep (se 1 (by rfl) ⟨123290, by rfl⟩ : syracuseStep 164387 = 246581) B246581
theorem B557603 : Blo 107783 557603 := bstep (se 1 (by rfl) ⟨418202, by rfl⟩ : syracuseStep 557603 = 836405) B836405
theorem B164417 : Blo 107783 164417 := bstep (se 2 (by rfl) ⟨61656, by rfl⟩ : syracuseStep 164417 = 123313) B123313
theorem B262723 : Blo 107783 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B787013 : Blo 107783 787013 := bstep (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) B147565
theorem B164435 : Blo 107783 164435 := bstep (se 1 (by rfl) ⟨123326, by rfl⟩ : syracuseStep 164435 = 246653) B246653
theorem B590435 : Blo 107783 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B164465 : Blo 107783 164465 := bstep (se 2 (by rfl) ⟨61674, by rfl⟩ : syracuseStep 164465 = 123349) B123349
theorem B164483 : Blo 107783 164483 := bstep (se 1 (by rfl) ⟨123362, by rfl⟩ : syracuseStep 164483 = 246725) B246725
theorem B164513 : Blo 107783 164513 := bstep (se 2 (by rfl) ⟨61692, by rfl⟩ : syracuseStep 164513 = 123385) B123385
theorem B164531 : Blo 107783 164531 := bstep (se 1 (by rfl) ⟨123398, by rfl⟩ : syracuseStep 164531 = 246797) B246797
theorem B164561 : Blo 107783 164561 := bstep (se 2 (by rfl) ⟨61710, by rfl⟩ : syracuseStep 164561 = 123421) B123421
theorem B164579 : Blo 107783 164579 := bstep (se 1 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 164579 = 246869) B246869
theorem B164609 : Blo 107783 164609 := bstep (se 2 (by rfl) ⟨61728, by rfl⟩ : syracuseStep 164609 = 123457) B123457
theorem B164627 : Blo 107783 164627 := bstep (se 1 (by rfl) ⟨123470, by rfl⟩ : syracuseStep 164627 = 246941) B246941
theorem B164657 : Blo 107783 164657 := bstep (se 2 (by rfl) ⟨61746, by rfl⟩ : syracuseStep 164657 = 123493) B123493
theorem B164675 : Blo 107783 164675 := bstep (se 1 (by rfl) ⟨123506, by rfl⟩ : syracuseStep 164675 = 247013) B247013
theorem B164705 : Blo 107783 164705 := bstep (se 2 (by rfl) ⟨61764, by rfl⟩ : syracuseStep 164705 = 123529) B123529
theorem B164723 : Blo 107783 164723 := bstep (se 1 (by rfl) ⟨123542, by rfl⟩ : syracuseStep 164723 = 247085) B247085
theorem B656261 : Blo 107783 656261 := bstep (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) B123049
theorem B295825 : Blo 107783 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B164753 : Blo 107783 164753 := bstep (se 2 (by rfl) ⟨61782, by rfl⟩ : syracuseStep 164753 = 123565) B123565
theorem B164771 : Blo 107783 164771 := bstep (se 1 (by rfl) ⟨123578, by rfl⟩ : syracuseStep 164771 = 247157) B247157
theorem B1344437 : Blo 107783 1344437 := bstep (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) B126041
theorem B164801 : Blo 107783 164801 := bstep (se 2 (by rfl) ⟨61800, by rfl⟩ : syracuseStep 164801 = 123601) B123601
theorem B164819 : Blo 107783 164819 := bstep (se 1 (by rfl) ⟨123614, by rfl⟩ : syracuseStep 164819 = 247229) B247229
theorem B164849 : Blo 107783 164849 := bstep (se 2 (by rfl) ⟨61818, by rfl⟩ : syracuseStep 164849 = 123637) B123637
theorem B164867 : Blo 107783 164867 := bstep (se 1 (by rfl) ⟨123650, by rfl⟩ : syracuseStep 164867 = 247301) B247301
theorem B164897 : Blo 107783 164897 := bstep (se 2 (by rfl) ⟨61836, by rfl⟩ : syracuseStep 164897 = 123673) B123673
theorem B164915 : Blo 107783 164915 := bstep (se 1 (by rfl) ⟨123686, by rfl⟩ : syracuseStep 164915 = 247373) B247373
theorem B164945 : Blo 107783 164945 := bstep (se 2 (by rfl) ⟨61854, by rfl⟩ : syracuseStep 164945 = 123709) B123709
theorem B164963 : Blo 107783 164963 := bstep (se 1 (by rfl) ⟨123722, by rfl⟩ : syracuseStep 164963 = 247445) B247445
theorem B164993 : Blo 107783 164993 := bstep (se 2 (by rfl) ⟨61872, by rfl⟩ : syracuseStep 164993 = 123745) B123745
theorem B165011 : Blo 107783 165011 := bstep (se 1 (by rfl) ⟨123758, by rfl⟩ : syracuseStep 165011 = 247517) B247517
theorem B165041 : Blo 107783 165041 := bstep (se 2 (by rfl) ⟨61890, by rfl⟩ : syracuseStep 165041 = 123781) B123781
theorem B165059 : Blo 107783 165059 := bstep (se 1 (by rfl) ⟨123794, by rfl⟩ : syracuseStep 165059 = 247589) B247589
theorem B165089 : Blo 107783 165089 := bstep (se 2 (by rfl) ⟨61908, by rfl⟩ : syracuseStep 165089 = 123817) B123817
theorem B230627 : Blo 107783 230627 := bstep (se 1 (by rfl) ⟨172970, by rfl⟩ : syracuseStep 230627 = 345941) B345941
theorem B165107 : Blo 107783 165107 := bstep (se 1 (by rfl) ⟨123830, by rfl⟩ : syracuseStep 165107 = 247661) B247661
theorem B165137 : Blo 107783 165137 := bstep (se 2 (by rfl) ⟨61926, by rfl⟩ : syracuseStep 165137 = 123853) B123853
theorem B165155 : Blo 107783 165155 := bstep (se 1 (by rfl) ⟨123866, by rfl⟩ : syracuseStep 165155 = 247733) B247733
theorem B329005 : Blo 107783 329005 := bstep (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) B123377
theorem B165185 : Blo 107783 165185 := bstep (se 2 (by rfl) ⟨61944, by rfl⟩ : syracuseStep 165185 = 123889) B123889
theorem B558413 : Blo 107783 558413 := bstep (se 3 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 558413 = 209405) B209405
theorem B165203 : Blo 107783 165203 := bstep (se 1 (by rfl) ⟨123902, by rfl⟩ : syracuseStep 165203 = 247805) B247805
theorem B165233 : Blo 107783 165233 := bstep (se 2 (by rfl) ⟨61962, by rfl⟩ : syracuseStep 165233 = 123925) B123925
theorem B165251 : Blo 107783 165251 := bstep (se 1 (by rfl) ⟨123938, by rfl⟩ : syracuseStep 165251 = 247877) B247877
theorem B165281 : Blo 107783 165281 := bstep (se 2 (by rfl) ⟨61980, by rfl⟩ : syracuseStep 165281 = 123961) B123961
theorem B165299 : Blo 107783 165299 := bstep (se 1 (by rfl) ⟨123974, by rfl⟩ : syracuseStep 165299 = 247949) B247949
theorem B165329 : Blo 107783 165329 := bstep (se 2 (by rfl) ⟨61998, by rfl⟩ : syracuseStep 165329 = 123997) B123997
theorem B296419 : Blo 107783 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B165347 : Blo 107783 165347 := bstep (se 1 (by rfl) ⟨124010, by rfl⟩ : syracuseStep 165347 = 248021) B248021
theorem B263665 : Blo 107783 263665 := bstep (se 2 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 263665 = 197749) B197749
theorem B165377 : Blo 107783 165377 := bstep (se 2 (by rfl) ⟨62016, by rfl⟩ : syracuseStep 165377 = 124033) B124033
theorem B165395 : Blo 107783 165395 := bstep (se 1 (by rfl) ⟨124046, by rfl⟩ : syracuseStep 165395 = 248093) B248093
theorem B165425 : Blo 107783 165425 := bstep (se 2 (by rfl) ⟨62034, by rfl⟩ : syracuseStep 165425 = 124069) B124069
theorem B165443 : Blo 107783 165443 := bstep (se 1 (by rfl) ⟨124082, by rfl⟩ : syracuseStep 165443 = 248165) B248165
theorem B165473 : Blo 107783 165473 := bstep (se 2 (by rfl) ⟨62052, by rfl⟩ : syracuseStep 165473 = 124105) B124105
theorem B165491 : Blo 107783 165491 := bstep (se 1 (by rfl) ⟨124118, by rfl⟩ : syracuseStep 165491 = 248237) B248237
theorem B165521 : Blo 107783 165521 := bstep (se 2 (by rfl) ⟨62070, by rfl⟩ : syracuseStep 165521 = 124141) B124141
theorem B165539 : Blo 107783 165539 := bstep (se 1 (by rfl) ⟨124154, by rfl⟩ : syracuseStep 165539 = 248309) B248309
theorem B165569 : Blo 107783 165569 := bstep (se 2 (by rfl) ⟨62088, by rfl⟩ : syracuseStep 165569 = 124177) B124177
theorem B165587 : Blo 107783 165587 := bstep (se 1 (by rfl) ⟨124190, by rfl⟩ : syracuseStep 165587 = 248381) B248381
theorem B1050353 : Blo 107783 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B394993 : Blo 107783 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B165617 : Blo 107783 165617 := bstep (se 2 (by rfl) ⟨62106, by rfl⟩ : syracuseStep 165617 = 124213) B124213
theorem B165635 : Blo 107783 165635 := bstep (se 1 (by rfl) ⟨124226, by rfl⟩ : syracuseStep 165635 = 248453) B248453
theorem B165665 : Blo 107783 165665 := bstep (se 2 (by rfl) ⟨62124, by rfl⟩ : syracuseStep 165665 = 124249) B124249
theorem B132899 : Blo 107783 132899 := bstep (se 1 (by rfl) ⟨99674, by rfl⟩ : syracuseStep 132899 = 199349) B199349
theorem B165683 : Blo 107783 165683 := bstep (se 1 (by rfl) ⟨124262, by rfl⟩ : syracuseStep 165683 = 248525) B248525
theorem B165713 : Blo 107783 165713 := bstep (se 2 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 165713 = 124285) B124285
theorem B165731 : Blo 107783 165731 := bstep (se 1 (by rfl) ⟨124298, by rfl⟩ : syracuseStep 165731 = 248597) B248597
theorem B165761 : Blo 107783 165761 := bstep (se 2 (by rfl) ⟨62160, by rfl⟩ : syracuseStep 165761 = 124321) B124321
theorem B165779 : Blo 107783 165779 := bstep (se 1 (by rfl) ⟨124334, by rfl⟩ : syracuseStep 165779 = 248669) B248669
theorem B198577 : Blo 107783 198577 := bstep (se 2 (by rfl) ⟨74466, by rfl⟩ : syracuseStep 198577 = 148933) B148933
theorem B165809 : Blo 107783 165809 := bstep (se 2 (by rfl) ⟨62178, by rfl⟩ : syracuseStep 165809 = 124357) B124357
theorem B165827 : Blo 107783 165827 := bstep (se 1 (by rfl) ⟨124370, by rfl⟩ : syracuseStep 165827 = 248741) B248741
theorem B165857 : Blo 107783 165857 := bstep (se 2 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 165857 = 124393) B124393
theorem B165875 : Blo 107783 165875 := bstep (se 1 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 165875 = 248813) B248813
theorem B165905 : Blo 107783 165905 := bstep (se 2 (by rfl) ⟨62214, by rfl⟩ : syracuseStep 165905 = 124429) B124429
theorem B165923 : Blo 107783 165923 := bstep (se 1 (by rfl) ⟨124442, by rfl⟩ : syracuseStep 165923 = 248885) B248885
theorem B231473 : Blo 107783 231473 := bstep (se 2 (by rfl) ⟨86802, by rfl⟩ : syracuseStep 231473 = 173605) B173605
theorem B165953 : Blo 107783 165953 := bstep (se 2 (by rfl) ⟨62232, by rfl⟩ : syracuseStep 165953 = 124465) B124465
theorem B165971 : Blo 107783 165971 := bstep (se 1 (by rfl) ⟨124478, by rfl⟩ : syracuseStep 165971 = 248957) B248957
theorem B166001 : Blo 107783 166001 := bstep (se 2 (by rfl) ⟨62250, by rfl⟩ : syracuseStep 166001 = 124501) B124501
theorem B198787 : Blo 107783 198787 := bstep (se 1 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 198787 = 298181) B298181
theorem B166019 : Blo 107783 166019 := bstep (se 1 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 166019 = 249029) B249029
theorem B2001037 : Blo 107783 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B166049 : Blo 107783 166049 := bstep (se 2 (by rfl) ⟨62268, by rfl⟩ : syracuseStep 166049 = 124537) B124537
theorem B166067 : Blo 107783 166067 := bstep (se 1 (by rfl) ⟨124550, by rfl⟩ : syracuseStep 166067 = 249101) B249101
theorem B166097 : Blo 107783 166097 := bstep (se 2 (by rfl) ⟨62286, by rfl⟩ : syracuseStep 166097 = 124573) B124573
theorem B362723 : Blo 107783 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B166115 : Blo 107783 166115 := bstep (se 1 (by rfl) ⟨124586, by rfl⟩ : syracuseStep 166115 = 249173) B249173
theorem B166145 : Blo 107783 166145 := bstep (se 2 (by rfl) ⟨62304, by rfl⟩ : syracuseStep 166145 = 124609) B124609
theorem B166163 : Blo 107783 166163 := bstep (se 1 (by rfl) ⟨124622, by rfl⟩ : syracuseStep 166163 = 249245) B249245
theorem B166193 : Blo 107783 166193 := bstep (se 2 (by rfl) ⟨62322, by rfl⟩ : syracuseStep 166193 = 124645) B124645
theorem B166211 : Blo 107783 166211 := bstep (se 1 (by rfl) ⟨124658, by rfl⟩ : syracuseStep 166211 = 249317) B249317
theorem B166241 : Blo 107783 166241 := bstep (se 2 (by rfl) ⟨62340, by rfl⟩ : syracuseStep 166241 = 124681) B124681
theorem B166259 : Blo 107783 166259 := bstep (se 1 (by rfl) ⟨124694, by rfl⟩ : syracuseStep 166259 = 249389) B249389
theorem B166289 : Blo 107783 166289 := bstep (se 2 (by rfl) ⟨62358, by rfl⟩ : syracuseStep 166289 = 124717) B124717
theorem B297379 : Blo 107783 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B166307 : Blo 107783 166307 := bstep (se 1 (by rfl) ⟨124730, by rfl⟩ : syracuseStep 166307 = 249461) B249461
theorem B166337 : Blo 107783 166337 := bstep (se 2 (by rfl) ⟨62376, by rfl⟩ : syracuseStep 166337 = 124753) B124753
theorem B297425 : Blo 107783 297425 := bstep (se 2 (by rfl) ⟨111534, by rfl⟩ : syracuseStep 297425 = 223069) B223069
theorem B166355 : Blo 107783 166355 := bstep (se 1 (by rfl) ⟨124766, by rfl⟩ : syracuseStep 166355 = 249533) B249533
theorem B166385 : Blo 107783 166385 := bstep (se 2 (by rfl) ⟨62394, by rfl⟩ : syracuseStep 166385 = 124789) B124789
theorem B166403 : Blo 107783 166403 := bstep (se 1 (by rfl) ⟨124802, by rfl⟩ : syracuseStep 166403 = 249605) B249605
theorem B166433 : Blo 107783 166433 := bstep (se 2 (by rfl) ⟨62412, by rfl⟩ : syracuseStep 166433 = 124825) B124825
theorem B166451 : Blo 107783 166451 := bstep (se 1 (by rfl) ⟨124838, by rfl⟩ : syracuseStep 166451 = 249677) B249677
theorem B461389 : Blo 107783 461389 := bstep (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) B173021
theorem B166481 : Blo 107783 166481 := bstep (se 2 (by rfl) ⟨62430, by rfl⟩ : syracuseStep 166481 = 124861) B124861
theorem B166499 : Blo 107783 166499 := bstep (se 1 (by rfl) ⟨124874, by rfl⟩ : syracuseStep 166499 = 249749) B249749
theorem B166529 : Blo 107783 166529 := bstep (se 2 (by rfl) ⟨62448, by rfl⟩ : syracuseStep 166529 = 124897) B124897
theorem B166547 : Blo 107783 166547 := bstep (se 1 (by rfl) ⟨124910, by rfl⟩ : syracuseStep 166547 = 249821) B249821
theorem B166577 : Blo 107783 166577 := bstep (se 2 (by rfl) ⟨62466, by rfl⟩ : syracuseStep 166577 = 124933) B124933
theorem B166595 : Blo 107783 166595 := bstep (se 1 (by rfl) ⟨124946, by rfl⟩ : syracuseStep 166595 = 249893) B249893
theorem B166625 : Blo 107783 166625 := bstep (se 2 (by rfl) ⟨62484, by rfl⟩ : syracuseStep 166625 = 124969) B124969
theorem B166643 : Blo 107783 166643 := bstep (se 1 (by rfl) ⟨124982, by rfl⟩ : syracuseStep 166643 = 249965) B249965
theorem B166673 : Blo 107783 166673 := bstep (se 2 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 166673 = 125005) B125005
theorem B166691 : Blo 107783 166691 := bstep (se 1 (by rfl) ⟨125018, by rfl⟩ : syracuseStep 166691 = 250037) B250037
theorem B166721 : Blo 107783 166721 := bstep (se 2 (by rfl) ⟨62520, by rfl⟩ : syracuseStep 166721 = 125041) B125041
theorem B166739 : Blo 107783 166739 := bstep (se 1 (by rfl) ⟨125054, by rfl⟩ : syracuseStep 166739 = 250109) B250109
theorem B166769 : Blo 107783 166769 := bstep (se 2 (by rfl) ⟨62538, by rfl⟩ : syracuseStep 166769 = 125077) B125077
theorem B166787 : Blo 107783 166787 := bstep (se 1 (by rfl) ⟨125090, by rfl⟩ : syracuseStep 166787 = 250181) B250181
theorem B166817 : Blo 107783 166817 := bstep (se 2 (by rfl) ⟨62556, by rfl⟩ : syracuseStep 166817 = 125113) B125113
theorem B166835 : Blo 107783 166835 := bstep (se 1 (by rfl) ⟨125126, by rfl⟩ : syracuseStep 166835 = 250253) B250253
theorem B166865 : Blo 107783 166865 := bstep (se 2 (by rfl) ⟨62574, by rfl⟩ : syracuseStep 166865 = 125149) B125149
theorem B166883 : Blo 107783 166883 := bstep (se 1 (by rfl) ⟨125162, by rfl⟩ : syracuseStep 166883 = 250325) B250325
theorem B166913 : Blo 107783 166913 := bstep (se 2 (by rfl) ⟨62592, by rfl⟩ : syracuseStep 166913 = 125185) B125185
theorem B691213 : Blo 107783 691213 := bstep (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) B259205
theorem B166931 : Blo 107783 166931 := bstep (se 1 (by rfl) ⟨125198, by rfl⟩ : syracuseStep 166931 = 250397) B250397
theorem B166961 : Blo 107783 166961 := bstep (se 2 (by rfl) ⟨62610, by rfl⟩ : syracuseStep 166961 = 125221) B125221
theorem B166979 : Blo 107783 166979 := bstep (se 1 (by rfl) ⟨125234, by rfl⟩ : syracuseStep 166979 = 250469) B250469
theorem B167009 : Blo 107783 167009 := bstep (se 2 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 167009 = 125257) B125257
theorem B167027 : Blo 107783 167027 := bstep (se 1 (by rfl) ⟨125270, by rfl⟩ : syracuseStep 167027 = 250541) B250541
theorem B167057 : Blo 107783 167057 := bstep (se 2 (by rfl) ⟨62646, by rfl⟩ : syracuseStep 167057 = 125293) B125293
theorem B167075 : Blo 107783 167075 := bstep (se 1 (by rfl) ⟨125306, by rfl⟩ : syracuseStep 167075 = 250613) B250613
theorem B167105 : Blo 107783 167105 := bstep (se 2 (by rfl) ⟨62664, by rfl⟩ : syracuseStep 167105 = 125329) B125329
theorem B167123 : Blo 107783 167123 := bstep (se 1 (by rfl) ⟨125342, by rfl⟩ : syracuseStep 167123 = 250685) B250685
theorem B167153 : Blo 107783 167153 := bstep (se 2 (by rfl) ⟨62682, by rfl⟩ : syracuseStep 167153 = 125365) B125365
theorem B167171 : Blo 107783 167171 := bstep (se 1 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 167171 = 250757) B250757
theorem B167201 : Blo 107783 167201 := bstep (se 2 (by rfl) ⟨62700, by rfl⟩ : syracuseStep 167201 = 125401) B125401
theorem B593201 : Blo 107783 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B167219 : Blo 107783 167219 := bstep (se 1 (by rfl) ⟨125414, by rfl⟩ : syracuseStep 167219 = 250829) B250829
theorem B167249 : Blo 107783 167249 := bstep (se 2 (by rfl) ⟨62718, by rfl⟩ : syracuseStep 167249 = 125437) B125437
theorem B167267 : Blo 107783 167267 := bstep (se 1 (by rfl) ⟨125450, by rfl⟩ : syracuseStep 167267 = 250901) B250901
theorem B167297 : Blo 107783 167297 := bstep (se 2 (by rfl) ⟨62736, by rfl⟩ : syracuseStep 167297 = 125473) B125473
theorem B167315 : Blo 107783 167315 := bstep (se 1 (by rfl) ⟨125486, by rfl⟩ : syracuseStep 167315 = 250973) B250973
theorem B167345 : Blo 107783 167345 := bstep (se 2 (by rfl) ⟨62754, by rfl⟩ : syracuseStep 167345 = 125509) B125509
theorem B167363 : Blo 107783 167363 := bstep (se 1 (by rfl) ⟨125522, by rfl⟩ : syracuseStep 167363 = 251045) B251045
theorem B167393 : Blo 107783 167393 := bstep (se 2 (by rfl) ⟨62772, by rfl⟩ : syracuseStep 167393 = 125545) B125545
theorem B364013 : Blo 107783 364013 := bstep (se 3 (by rfl) ⟨68252, by rfl⟩ : syracuseStep 364013 = 136505) B136505
theorem B167411 : Blo 107783 167411 := bstep (se 1 (by rfl) ⟨125558, by rfl⟩ : syracuseStep 167411 = 251117) B251117
theorem B822797 : Blo 107783 822797 := bstep (se 3 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 822797 = 308549) B308549
theorem B167441 : Blo 107783 167441 := bstep (se 2 (by rfl) ⟨62790, by rfl⟩ : syracuseStep 167441 = 125581) B125581
theorem B364067 : Blo 107783 364067 := bstep (se 1 (by rfl) ⟨273050, by rfl⟩ : syracuseStep 364067 = 546101) B546101
theorem B167459 : Blo 107783 167459 := bstep (se 1 (by rfl) ⟨125594, by rfl⟩ : syracuseStep 167459 = 251189) B251189
theorem B1248821 : Blo 107783 1248821 := bstep (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) B117077
theorem B167489 : Blo 107783 167489 := bstep (se 2 (by rfl) ⟨62808, by rfl⟩ : syracuseStep 167489 = 125617) B125617
theorem B167507 : Blo 107783 167507 := bstep (se 1 (by rfl) ⟨125630, by rfl⟩ : syracuseStep 167507 = 251261) B251261
theorem B462449 : Blo 107783 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B167537 : Blo 107783 167537 := bstep (se 2 (by rfl) ⟨62826, by rfl⟩ : syracuseStep 167537 = 125653) B125653
theorem B167555 : Blo 107783 167555 := bstep (se 1 (by rfl) ⟨125666, by rfl⟩ : syracuseStep 167555 = 251333) B251333
theorem B167585 : Blo 107783 167585 := bstep (se 2 (by rfl) ⟨62844, by rfl⟩ : syracuseStep 167585 = 125689) B125689
theorem B167603 : Blo 107783 167603 := bstep (se 1 (by rfl) ⟨125702, by rfl⟩ : syracuseStep 167603 = 251405) B251405
theorem B167617 : Blo 107783 167617 := bstep (se 2 (by rfl) ⟨62856, by rfl⟩ : syracuseStep 167617 = 125713) B125713
theorem B233155 : Blo 107783 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B167633 : Blo 107783 167633 := bstep (se 2 (by rfl) ⟨62862, by rfl⟩ : syracuseStep 167633 = 125725) B125725
theorem B167651 : Blo 107783 167651 := bstep (se 1 (by rfl) ⟨125738, by rfl⟩ : syracuseStep 167651 = 251477) B251477
theorem B364337 : Blo 107783 364337 := bstep (se 2 (by rfl) ⟨136626, by rfl⟩ : syracuseStep 364337 = 273253) B273253
theorem B331793 : Blo 107783 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B233617 : Blo 107783 233617 := bstep (se 2 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 233617 = 175213) B175213
theorem B561329 : Blo 107783 561329 := bstep (se 2 (by rfl) ⟨210498, by rfl⟩ : syracuseStep 561329 = 420997) B420997
theorem B364877 : Blo 107783 364877 := bstep (se 3 (by rfl) ⟨68414, by rfl⟩ : syracuseStep 364877 = 136829) B136829
theorem B364931 : Blo 107783 364931 := bstep (se 1 (by rfl) ⟨273698, by rfl⟩ : syracuseStep 364931 = 547397) B547397
theorem B201187 : Blo 107783 201187 := bstep (se 1 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 201187 = 301781) B301781
theorem B299501 : Blo 107783 299501 := bstep (se 3 (by rfl) ⟨56156, by rfl⟩ : syracuseStep 299501 = 112313) B112313
theorem B627277 : Blo 107783 627277 := bstep (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) B235229
theorem B365201 : Blo 107783 365201 := bstep (se 2 (by rfl) ⟨136950, by rfl⟩ : syracuseStep 365201 = 273901) B273901
theorem B201457 : Blo 107783 201457 := bstep (se 2 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 201457 = 151093) B151093
theorem B299825 : Blo 107783 299825 := bstep (se 2 (by rfl) ⟨112434, by rfl⟩ : syracuseStep 299825 = 224869) B224869
theorem B627533 : Blo 107783 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B168785 : Blo 107783 168785 := bstep (se 2 (by rfl) ⟨63294, by rfl⟩ : syracuseStep 168785 = 126589) B126589
theorem B234659 : Blo 107783 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B365741 : Blo 107783 365741 := bstep (se 3 (by rfl) ⟨68576, by rfl⟩ : syracuseStep 365741 = 137153) B137153
theorem B365795 : Blo 107783 365795 := bstep (se 1 (by rfl) ⟨274346, by rfl⟩ : syracuseStep 365795 = 548693) B548693
theorem B300451 : Blo 107783 300451 := bstep (se 1 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 300451 = 450677) B450677
theorem B366065 : Blo 107783 366065 := bstep (se 2 (by rfl) ⟨137274, by rfl⟩ : syracuseStep 366065 = 274549) B274549
theorem B136723 : Blo 107783 136723 := bstep (se 1 (by rfl) ⟨102542, by rfl⟩ : syracuseStep 136723 = 205085) B205085
theorem B2135605 : Blo 107783 2135605 := bstep (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) B200213
theorem B562787 : Blo 107783 562787 := bstep (se 1 (by rfl) ⟨422090, by rfl⟩ : syracuseStep 562787 = 844181) B844181
theorem B136819 : Blo 107783 136819 := bstep (se 1 (by rfl) ⟨102614, by rfl⟩ : syracuseStep 136819 = 205229) B205229
theorem B235171 : Blo 107783 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B366605 : Blo 107783 366605 := bstep (se 3 (by rfl) ⟨68738, by rfl⟩ : syracuseStep 366605 = 137477) B137477
theorem B366659 : Blo 107783 366659 := bstep (se 1 (by rfl) ⟨274994, by rfl⟩ : syracuseStep 366659 = 549989) B549989
theorem B137315 : Blo 107783 137315 := bstep (se 1 (by rfl) ⟨102986, by rfl⟩ : syracuseStep 137315 = 205973) B205973
theorem B2398349 : Blo 107783 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B268451 : Blo 107783 268451 := bstep (se 1 (by rfl) ⟨201338, by rfl⟩ : syracuseStep 268451 = 402677) B402677
theorem B661709 : Blo 107783 661709 := bstep (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) B248141
theorem B170195 : Blo 107783 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B137459 : Blo 107783 137459 := bstep (se 1 (by rfl) ⟨103094, by rfl⟩ : syracuseStep 137459 = 206189) B206189
theorem B792845 : Blo 107783 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B366929 : Blo 107783 366929 := bstep (se 2 (by rfl) ⟨137598, by rfl⟩ : syracuseStep 366929 = 275197) B275197
theorem B825713 : Blo 107783 825713 := bstep (se 2 (by rfl) ⟨309642, by rfl⟩ : syracuseStep 825713 = 619285) B619285
theorem B235889 : Blo 107783 235889 := bstep (se 2 (by rfl) ⟨88458, by rfl⟩ : syracuseStep 235889 = 176917) B176917
theorem B563597 : Blo 107783 563597 := bstep (se 3 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 563597 = 211349) B211349
theorem B465421 : Blo 107783 465421 := bstep (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) B174533
theorem B1055501 : Blo 107783 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B138019 : Blo 107783 138019 := bstep (se 1 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 138019 = 207029) B207029
theorem B465763 : Blo 107783 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B367469 : Blo 107783 367469 := bstep (se 3 (by rfl) ⟨68900, by rfl⟩ : syracuseStep 367469 = 137801) B137801
theorem B498545 : Blo 107783 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B138115 : Blo 107783 138115 := bstep (se 1 (by rfl) ⟨103586, by rfl⟩ : syracuseStep 138115 = 207173) B207173
theorem B367523 : Blo 107783 367523 := bstep (se 1 (by rfl) ⟨275642, by rfl⟩ : syracuseStep 367523 = 551285) B551285
theorem B629765 : Blo 107783 629765 := bstep (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) B118081
theorem B1252421 : Blo 107783 1252421 := bstep (se 4 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 1252421 = 234829) B234829
theorem B236675 : Blo 107783 236675 := bstep (se 1 (by rfl) ⟨177506, by rfl⟩ : syracuseStep 236675 = 355013) B355013
theorem B367793 : Blo 107783 367793 := bstep (se 2 (by rfl) ⟨137922, by rfl⟩ : syracuseStep 367793 = 275845) B275845
theorem B138611 : Blo 107783 138611 := bstep (se 1 (by rfl) ⟨103958, by rfl⟩ : syracuseStep 138611 = 207917) B207917
theorem B892529 : Blo 107783 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B630449 : Blo 107783 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B368333 : Blo 107783 368333 := bstep (se 3 (by rfl) ⟨69062, by rfl⟩ : syracuseStep 368333 = 138125) B138125
theorem B368387 : Blo 107783 368387 := bstep (se 1 (by rfl) ⟨276290, by rfl⟩ : syracuseStep 368387 = 552581) B552581
theorem B3710861 : Blo 107783 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B368657 : Blo 107783 368657 := bstep (se 2 (by rfl) ⟨138246, by rfl⟩ : syracuseStep 368657 = 276493) B276493
theorem B139315 : Blo 107783 139315 := bstep (se 1 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 139315 = 208973) B208973
theorem B237649 : Blo 107783 237649 := bstep (se 2 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 237649 = 178237) B178237
theorem B139411 : Blo 107783 139411 := bstep (se 1 (by rfl) ⟨104558, by rfl⟩ : syracuseStep 139411 = 209117) B209117
theorem B237905 : Blo 107783 237905 := bstep (se 2 (by rfl) ⟨89214, by rfl⟩ : syracuseStep 237905 = 178429) B178429
theorem B369197 : Blo 107783 369197 := bstep (se 3 (by rfl) ⟨69224, by rfl⟩ : syracuseStep 369197 = 138449) B138449
theorem B205411 : Blo 107783 205411 := bstep (se 1 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 205411 = 308117) B308117
theorem B369251 : Blo 107783 369251 := bstep (se 1 (by rfl) ⟨276938, by rfl⟩ : syracuseStep 369251 = 553877) B553877
theorem B139907 : Blo 107783 139907 := bstep (se 1 (by rfl) ⟨104930, by rfl⟩ : syracuseStep 139907 = 209861) B209861
theorem B172739 : Blo 107783 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B205571 : Blo 107783 205571 := bstep (se 1 (by rfl) ⟨154178, by rfl⟩ : syracuseStep 205571 = 308357) B308357
theorem B664433 : Blo 107783 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B369521 : Blo 107783 369521 := bstep (se 2 (by rfl) ⟨138570, by rfl⟩ : syracuseStep 369521 = 277141) B277141
theorem B1254325 : Blo 107783 1254325 := bstep (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) B117593
theorem B173009 : Blo 107783 173009 := bstep (se 2 (by rfl) ⟨64878, by rfl⟩ : syracuseStep 173009 = 129757) B129757
theorem B631907 : Blo 107783 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B697571 : Blo 107783 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B173297 : Blo 107783 173297 := bstep (se 2 (by rfl) ⟨64986, by rfl⟩ : syracuseStep 173297 = 129973) B129973
theorem B107795 : Blo 107783 107795 := bstep (se 1 (by rfl) ⟨80846, by rfl⟩ : syracuseStep 107795 = 161693) B161693
theorem B107811 : Blo 107783 107811 := bstep (se 1 (by rfl) ⟨80858, by rfl⟩ : syracuseStep 107811 = 161717) B161717
theorem B107827 : Blo 107783 107827 := bstep (se 1 (by rfl) ⟨80870, by rfl⟩ : syracuseStep 107827 = 161741) B161741
theorem B107843 : Blo 107783 107843 := bstep (se 1 (by rfl) ⟨80882, by rfl⟩ : syracuseStep 107843 = 161765) B161765
theorem B140611 : Blo 107783 140611 := bstep (se 1 (by rfl) ⟨105458, by rfl⟩ : syracuseStep 140611 = 210917) B210917
theorem B107859 : Blo 107783 107859 := bstep (se 1 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 107859 = 161789) B161789
theorem B107875 : Blo 107783 107875 := bstep (se 1 (by rfl) ⟨80906, by rfl⟩ : syracuseStep 107875 = 161813) B161813
theorem B107891 : Blo 107783 107891 := bstep (se 1 (by rfl) ⟨80918, by rfl⟩ : syracuseStep 107891 = 161837) B161837
theorem B107907 : Blo 107783 107907 := bstep (se 1 (by rfl) ⟨80930, by rfl⟩ : syracuseStep 107907 = 161861) B161861
theorem B370061 : Blo 107783 370061 := bstep (se 3 (by rfl) ⟨69386, by rfl⟩ : syracuseStep 370061 = 138773) B138773
theorem B107923 : Blo 107783 107923 := bstep (se 1 (by rfl) ⟨80942, by rfl⟩ : syracuseStep 107923 = 161885) B161885
theorem B107939 : Blo 107783 107939 := bstep (se 1 (by rfl) ⟨80954, by rfl⟩ : syracuseStep 107939 = 161909) B161909
theorem B140707 : Blo 107783 140707 := bstep (se 1 (by rfl) ⟨105530, by rfl⟩ : syracuseStep 140707 = 211061) B211061
theorem B107955 : Blo 107783 107955 := bstep (se 1 (by rfl) ⟨80966, by rfl⟩ : syracuseStep 107955 = 161933) B161933
theorem B107971 : Blo 107783 107971 := bstep (se 1 (by rfl) ⟨80978, by rfl⟩ : syracuseStep 107971 = 161957) B161957
theorem B370115 : Blo 107783 370115 := bstep (se 1 (by rfl) ⟨277586, by rfl⟩ : syracuseStep 370115 = 555173) B555173
theorem B107987 : Blo 107783 107987 := bstep (se 1 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 107987 = 161981) B161981
theorem B108003 : Blo 107783 108003 := bstep (se 1 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 108003 = 162005) B162005
theorem B108019 : Blo 107783 108019 := bstep (se 1 (by rfl) ⟨81014, by rfl⟩ : syracuseStep 108019 = 162029) B162029
theorem B108035 : Blo 107783 108035 := bstep (se 1 (by rfl) ⟨81026, by rfl⟩ : syracuseStep 108035 = 162053) B162053
theorem B108051 : Blo 107783 108051 := bstep (se 1 (by rfl) ⟨81038, by rfl⟩ : syracuseStep 108051 = 162077) B162077
theorem B108067 : Blo 107783 108067 := bstep (se 1 (by rfl) ⟨81050, by rfl⟩ : syracuseStep 108067 = 162101) B162101
theorem B108083 : Blo 107783 108083 := bstep (se 1 (by rfl) ⟨81062, by rfl⟩ : syracuseStep 108083 = 162125) B162125
theorem B108099 : Blo 107783 108099 := bstep (se 1 (by rfl) ⟨81074, by rfl⟩ : syracuseStep 108099 = 162149) B162149
theorem B108115 : Blo 107783 108115 := bstep (se 1 (by rfl) ⟨81086, by rfl⟩ : syracuseStep 108115 = 162173) B162173
theorem B108131 : Blo 107783 108131 := bstep (se 1 (by rfl) ⟨81098, by rfl⟩ : syracuseStep 108131 = 162197) B162197
theorem B108147 : Blo 107783 108147 := bstep (se 1 (by rfl) ⟨81110, by rfl⟩ : syracuseStep 108147 = 162221) B162221
theorem B108163 : Blo 107783 108163 := bstep (se 1 (by rfl) ⟨81122, by rfl⟩ : syracuseStep 108163 = 162245) B162245
theorem B173713 : Blo 107783 173713 := bstep (se 2 (by rfl) ⟨65142, by rfl⟩ : syracuseStep 173713 = 130285) B130285
theorem B108179 : Blo 107783 108179 := bstep (se 1 (by rfl) ⟨81134, by rfl⟩ : syracuseStep 108179 = 162269) B162269
theorem B108195 : Blo 107783 108195 := bstep (se 1 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 108195 = 162293) B162293
theorem B108211 : Blo 107783 108211 := bstep (se 1 (by rfl) ⟨81158, by rfl⟩ : syracuseStep 108211 = 162317) B162317
theorem B108227 : Blo 107783 108227 := bstep (se 1 (by rfl) ⟨81170, by rfl⟩ : syracuseStep 108227 = 162341) B162341
theorem B370385 : Blo 107783 370385 := bstep (se 2 (by rfl) ⟨138894, by rfl⟩ : syracuseStep 370385 = 277789) B277789
theorem B108243 : Blo 107783 108243 := bstep (se 1 (by rfl) ⟨81182, by rfl⟩ : syracuseStep 108243 = 162365) B162365
theorem B108259 : Blo 107783 108259 := bstep (se 1 (by rfl) ⟨81194, by rfl⟩ : syracuseStep 108259 = 162389) B162389
theorem B108275 : Blo 107783 108275 := bstep (se 1 (by rfl) ⟨81206, by rfl⟩ : syracuseStep 108275 = 162413) B162413
theorem B108291 : Blo 107783 108291 := bstep (se 1 (by rfl) ⟨81218, by rfl⟩ : syracuseStep 108291 = 162437) B162437
theorem B108307 : Blo 107783 108307 := bstep (se 1 (by rfl) ⟨81230, by rfl⟩ : syracuseStep 108307 = 162461) B162461
theorem B108323 : Blo 107783 108323 := bstep (se 1 (by rfl) ⟨81242, by rfl⟩ : syracuseStep 108323 = 162485) B162485
theorem B206641 : Blo 107783 206641 := bstep (se 2 (by rfl) ⟨77490, by rfl⟩ : syracuseStep 206641 = 154981) B154981
theorem B108339 : Blo 107783 108339 := bstep (se 1 (by rfl) ⟨81254, by rfl⟩ : syracuseStep 108339 = 162509) B162509
theorem B108355 : Blo 107783 108355 := bstep (se 1 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 108355 = 162533) B162533
theorem B108371 : Blo 107783 108371 := bstep (se 1 (by rfl) ⟨81278, by rfl⟩ : syracuseStep 108371 = 162557) B162557
theorem B108387 : Blo 107783 108387 := bstep (se 1 (by rfl) ⟨81290, by rfl⟩ : syracuseStep 108387 = 162581) B162581
theorem B108403 : Blo 107783 108403 := bstep (se 1 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 108403 = 162605) B162605
theorem B108419 : Blo 107783 108419 := bstep (se 1 (by rfl) ⟨81314, by rfl⟩ : syracuseStep 108419 = 162629) B162629
theorem B108435 : Blo 107783 108435 := bstep (se 1 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 108435 = 162653) B162653
theorem B141203 : Blo 107783 141203 := bstep (se 1 (by rfl) ⟨105902, by rfl⟩ : syracuseStep 141203 = 211805) B211805
theorem B108451 : Blo 107783 108451 := bstep (se 1 (by rfl) ⟨81338, by rfl⟩ : syracuseStep 108451 = 162677) B162677
theorem B108467 : Blo 107783 108467 := bstep (se 1 (by rfl) ⟨81350, by rfl⟩ : syracuseStep 108467 = 162701) B162701
theorem B108483 : Blo 107783 108483 := bstep (se 1 (by rfl) ⟨81362, by rfl⟩ : syracuseStep 108483 = 162725) B162725
theorem B108499 : Blo 107783 108499 := bstep (se 1 (by rfl) ⟨81374, by rfl⟩ : syracuseStep 108499 = 162749) B162749
theorem B108515 : Blo 107783 108515 := bstep (se 1 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 108515 = 162773) B162773
theorem B108531 : Blo 107783 108531 := bstep (se 1 (by rfl) ⟨81398, by rfl⟩ : syracuseStep 108531 = 162797) B162797
theorem B108547 : Blo 107783 108547 := bstep (se 1 (by rfl) ⟨81410, by rfl⟩ : syracuseStep 108547 = 162821) B162821
theorem B108563 : Blo 107783 108563 := bstep (se 1 (by rfl) ⟨81422, by rfl⟩ : syracuseStep 108563 = 162845) B162845
theorem B108579 : Blo 107783 108579 := bstep (se 1 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 108579 = 162869) B162869
theorem B108595 : Blo 107783 108595 := bstep (se 1 (by rfl) ⟨81446, by rfl⟩ : syracuseStep 108595 = 162893) B162893
theorem B108611 : Blo 107783 108611 := bstep (se 1 (by rfl) ⟨81458, by rfl⟩ : syracuseStep 108611 = 162917) B162917
theorem B108627 : Blo 107783 108627 := bstep (se 1 (by rfl) ⟨81470, by rfl⟩ : syracuseStep 108627 = 162941) B162941
theorem B108643 : Blo 107783 108643 := bstep (se 1 (by rfl) ⟨81482, by rfl⟩ : syracuseStep 108643 = 162965) B162965
theorem B108659 : Blo 107783 108659 := bstep (se 1 (by rfl) ⟨81494, by rfl⟩ : syracuseStep 108659 = 162989) B162989
theorem B108675 : Blo 107783 108675 := bstep (se 1 (by rfl) ⟨81506, by rfl⟩ : syracuseStep 108675 = 163013) B163013
theorem B108691 : Blo 107783 108691 := bstep (se 1 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 108691 = 163037) B163037
theorem B108707 : Blo 107783 108707 := bstep (se 1 (by rfl) ⟨81530, by rfl⟩ : syracuseStep 108707 = 163061) B163061
theorem B108723 : Blo 107783 108723 := bstep (se 1 (by rfl) ⟨81542, by rfl⟩ : syracuseStep 108723 = 163085) B163085
theorem B108739 : Blo 107783 108739 := bstep (se 1 (by rfl) ⟨81554, by rfl⟩ : syracuseStep 108739 = 163109) B163109
theorem B108755 : Blo 107783 108755 := bstep (se 1 (by rfl) ⟨81566, by rfl⟩ : syracuseStep 108755 = 163133) B163133
theorem B108771 : Blo 107783 108771 := bstep (se 1 (by rfl) ⟨81578, by rfl⟩ : syracuseStep 108771 = 163157) B163157
theorem B370925 : Blo 107783 370925 := bstep (se 3 (by rfl) ⟨69548, by rfl⟩ : syracuseStep 370925 = 139097) B139097
theorem B108787 : Blo 107783 108787 := bstep (se 1 (by rfl) ⟨81590, by rfl⟩ : syracuseStep 108787 = 163181) B163181
theorem B108803 : Blo 107783 108803 := bstep (se 1 (by rfl) ⟨81602, by rfl⟩ : syracuseStep 108803 = 163205) B163205
theorem B108819 : Blo 107783 108819 := bstep (se 1 (by rfl) ⟨81614, by rfl⟩ : syracuseStep 108819 = 163229) B163229
theorem B108835 : Blo 107783 108835 := bstep (se 1 (by rfl) ⟨81626, by rfl⟩ : syracuseStep 108835 = 163253) B163253
theorem B370979 : Blo 107783 370979 := bstep (se 1 (by rfl) ⟨278234, by rfl⟩ : syracuseStep 370979 = 556469) B556469
theorem B108851 : Blo 107783 108851 := bstep (se 1 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 108851 = 163277) B163277
theorem B108867 : Blo 107783 108867 := bstep (se 1 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 108867 = 163301) B163301
theorem B108883 : Blo 107783 108883 := bstep (se 1 (by rfl) ⟨81662, by rfl⟩ : syracuseStep 108883 = 163325) B163325
theorem B108899 : Blo 107783 108899 := bstep (se 1 (by rfl) ⟨81674, by rfl⟩ : syracuseStep 108899 = 163349) B163349
theorem B600419 : Blo 107783 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B108915 : Blo 107783 108915 := bstep (se 1 (by rfl) ⟨81686, by rfl⟩ : syracuseStep 108915 = 163373) B163373
theorem B108931 : Blo 107783 108931 := bstep (se 1 (by rfl) ⟨81698, by rfl⟩ : syracuseStep 108931 = 163397) B163397
theorem B108947 : Blo 107783 108947 := bstep (se 1 (by rfl) ⟨81710, by rfl⟩ : syracuseStep 108947 = 163421) B163421
theorem B108963 : Blo 107783 108963 := bstep (se 1 (by rfl) ⟨81722, by rfl⟩ : syracuseStep 108963 = 163445) B163445
theorem B108979 : Blo 107783 108979 := bstep (se 1 (by rfl) ⟨81734, by rfl⟩ : syracuseStep 108979 = 163469) B163469
theorem B108995 : Blo 107783 108995 := bstep (se 1 (by rfl) ⟨81746, by rfl⟩ : syracuseStep 108995 = 163493) B163493
theorem B109011 : Blo 107783 109011 := bstep (se 1 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 109011 = 163517) B163517
theorem B109027 : Blo 107783 109027 := bstep (se 1 (by rfl) ⟨81770, by rfl⟩ : syracuseStep 109027 = 163541) B163541
theorem B109043 : Blo 107783 109043 := bstep (se 1 (by rfl) ⟨81782, by rfl⟩ : syracuseStep 109043 = 163565) B163565
theorem B109059 : Blo 107783 109059 := bstep (se 1 (by rfl) ⟨81794, by rfl⟩ : syracuseStep 109059 = 163589) B163589
theorem B174611 : Blo 107783 174611 := bstep (se 1 (by rfl) ⟨130958, by rfl⟩ : syracuseStep 174611 = 261917) B261917
theorem B109075 : Blo 107783 109075 := bstep (se 1 (by rfl) ⟨81806, by rfl⟩ : syracuseStep 109075 = 163613) B163613
theorem B109091 : Blo 107783 109091 := bstep (se 1 (by rfl) ⟨81818, by rfl⟩ : syracuseStep 109091 = 163637) B163637
theorem B371249 : Blo 107783 371249 := bstep (se 2 (by rfl) ⟨139218, by rfl⟩ : syracuseStep 371249 = 278437) B278437
theorem B109107 : Blo 107783 109107 := bstep (se 1 (by rfl) ⟨81830, by rfl⟩ : syracuseStep 109107 = 163661) B163661
theorem B109123 : Blo 107783 109123 := bstep (se 1 (by rfl) ⟨81842, by rfl⟩ : syracuseStep 109123 = 163685) B163685
theorem B109139 : Blo 107783 109139 := bstep (se 1 (by rfl) ⟨81854, by rfl⟩ : syracuseStep 109139 = 163709) B163709
theorem B109155 : Blo 107783 109155 := bstep (se 1 (by rfl) ⟨81866, by rfl⟩ : syracuseStep 109155 = 163733) B163733
theorem B109171 : Blo 107783 109171 := bstep (se 1 (by rfl) ⟨81878, by rfl⟩ : syracuseStep 109171 = 163757) B163757
theorem B109187 : Blo 107783 109187 := bstep (se 1 (by rfl) ⟨81890, by rfl⟩ : syracuseStep 109187 = 163781) B163781
theorem B273041 : Blo 107783 273041 := bstep (se 2 (by rfl) ⟨102390, by rfl⟩ : syracuseStep 273041 = 204781) B204781
theorem B109203 : Blo 107783 109203 := bstep (se 1 (by rfl) ⟨81902, by rfl⟩ : syracuseStep 109203 = 163805) B163805
theorem B109219 : Blo 107783 109219 := bstep (se 1 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 109219 = 163829) B163829
theorem B109235 : Blo 107783 109235 := bstep (se 1 (by rfl) ⟨81926, by rfl⟩ : syracuseStep 109235 = 163853) B163853
theorem B273091 : Blo 107783 273091 := bstep (se 1 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 273091 = 409637) B409637
theorem B109251 : Blo 107783 109251 := bstep (se 1 (by rfl) ⟨81938, by rfl⟩ : syracuseStep 109251 = 163877) B163877
theorem B109267 : Blo 107783 109267 := bstep (se 1 (by rfl) ⟨81950, by rfl⟩ : syracuseStep 109267 = 163901) B163901
theorem B109283 : Blo 107783 109283 := bstep (se 1 (by rfl) ⟨81962, by rfl⟩ : syracuseStep 109283 = 163925) B163925
theorem B174835 : Blo 107783 174835 := bstep (se 1 (by rfl) ⟨131126, by rfl⟩ : syracuseStep 174835 = 262253) B262253
theorem B109299 : Blo 107783 109299 := bstep (se 1 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 109299 = 163949) B163949
theorem B109315 : Blo 107783 109315 := bstep (se 1 (by rfl) ⟨81986, by rfl⟩ : syracuseStep 109315 = 163973) B163973
theorem B338701 : Blo 107783 338701 := bstep (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) B127013
theorem B109331 : Blo 107783 109331 := bstep (se 1 (by rfl) ⟨81998, by rfl⟩ : syracuseStep 109331 = 163997) B163997
theorem B109347 : Blo 107783 109347 := bstep (se 1 (by rfl) ⟨82010, by rfl⟩ : syracuseStep 109347 = 164021) B164021
theorem B469795 : Blo 107783 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B109363 : Blo 107783 109363 := bstep (se 1 (by rfl) ⟨82022, by rfl⟩ : syracuseStep 109363 = 164045) B164045
theorem B109379 : Blo 107783 109379 := bstep (se 1 (by rfl) ⟨82034, by rfl⟩ : syracuseStep 109379 = 164069) B164069
theorem B273233 : Blo 107783 273233 := bstep (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) B204925
theorem B207697 : Blo 107783 207697 := bstep (se 2 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 207697 = 155773) B155773
theorem B109395 : Blo 107783 109395 := bstep (se 1 (by rfl) ⟨82046, by rfl⟩ : syracuseStep 109395 = 164093) B164093
theorem B109411 : Blo 107783 109411 := bstep (se 1 (by rfl) ⟨82058, by rfl⟩ : syracuseStep 109411 = 164117) B164117
theorem B109427 : Blo 107783 109427 := bstep (se 1 (by rfl) ⟨82070, by rfl⟩ : syracuseStep 109427 = 164141) B164141
theorem B109443 : Blo 107783 109443 := bstep (se 1 (by rfl) ⟨82082, by rfl⟩ : syracuseStep 109443 = 164165) B164165
theorem B109459 : Blo 107783 109459 := bstep (se 1 (by rfl) ⟨82094, by rfl⟩ : syracuseStep 109459 = 164189) B164189
theorem B109475 : Blo 107783 109475 := bstep (se 1 (by rfl) ⟨82106, by rfl⟩ : syracuseStep 109475 = 164213) B164213
theorem B109491 : Blo 107783 109491 := bstep (se 1 (by rfl) ⟨82118, by rfl⟩ : syracuseStep 109491 = 164237) B164237
theorem B109507 : Blo 107783 109507 := bstep (se 1 (by rfl) ⟨82130, by rfl⟩ : syracuseStep 109507 = 164261) B164261
theorem B109523 : Blo 107783 109523 := bstep (se 1 (by rfl) ⟨82142, by rfl⟩ : syracuseStep 109523 = 164285) B164285
theorem B109539 : Blo 107783 109539 := bstep (se 1 (by rfl) ⟨82154, by rfl⟩ : syracuseStep 109539 = 164309) B164309
theorem B2698211 : Blo 107783 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B109555 : Blo 107783 109555 := bstep (se 1 (by rfl) ⟨82166, by rfl⟩ : syracuseStep 109555 = 164333) B164333
theorem B109571 : Blo 107783 109571 := bstep (se 1 (by rfl) ⟨82178, by rfl⟩ : syracuseStep 109571 = 164357) B164357
theorem B568333 : Blo 107783 568333 := bstep (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) B213125
theorem B109587 : Blo 107783 109587 := bstep (se 1 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 109587 = 164381) B164381
theorem B109603 : Blo 107783 109603 := bstep (se 1 (by rfl) ⟨82202, by rfl⟩ : syracuseStep 109603 = 164405) B164405
theorem B109619 : Blo 107783 109619 := bstep (se 1 (by rfl) ⟨82214, by rfl⟩ : syracuseStep 109619 = 164429) B164429
theorem B109635 : Blo 107783 109635 := bstep (se 1 (by rfl) ⟨82226, by rfl⟩ : syracuseStep 109635 = 164453) B164453
theorem B371789 : Blo 107783 371789 := bstep (se 3 (by rfl) ⟨69710, by rfl⟩ : syracuseStep 371789 = 139421) B139421
theorem B109651 : Blo 107783 109651 := bstep (se 1 (by rfl) ⟨82238, by rfl⟩ : syracuseStep 109651 = 164477) B164477
theorem B109667 : Blo 107783 109667 := bstep (se 1 (by rfl) ⟨82250, by rfl⟩ : syracuseStep 109667 = 164501) B164501
theorem B109683 : Blo 107783 109683 := bstep (se 1 (by rfl) ⟨82262, by rfl⟩ : syracuseStep 109683 = 164525) B164525
theorem B109699 : Blo 107783 109699 := bstep (se 1 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 109699 = 164549) B164549
theorem B371843 : Blo 107783 371843 := bstep (se 1 (by rfl) ⟨278882, by rfl⟩ : syracuseStep 371843 = 557765) B557765
theorem B109715 : Blo 107783 109715 := bstep (se 1 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 109715 = 164573) B164573
theorem B109731 : Blo 107783 109731 := bstep (se 1 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 109731 = 164597) B164597
theorem B109747 : Blo 107783 109747 := bstep (se 1 (by rfl) ⟨82310, by rfl⟩ : syracuseStep 109747 = 164621) B164621
theorem B109763 : Blo 107783 109763 := bstep (se 1 (by rfl) ⟨82322, by rfl⟩ : syracuseStep 109763 = 164645) B164645
theorem B109779 : Blo 107783 109779 := bstep (se 1 (by rfl) ⟨82334, by rfl⟩ : syracuseStep 109779 = 164669) B164669
theorem B208099 : Blo 107783 208099 := bstep (se 1 (by rfl) ⟨156074, by rfl⟩ : syracuseStep 208099 = 312149) B312149
theorem B109795 : Blo 107783 109795 := bstep (se 1 (by rfl) ⟨82346, by rfl⟩ : syracuseStep 109795 = 164693) B164693
theorem B109811 : Blo 107783 109811 := bstep (se 1 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 109811 = 164717) B164717
theorem B109827 : Blo 107783 109827 := bstep (se 1 (by rfl) ⟨82370, by rfl⟩ : syracuseStep 109827 = 164741) B164741
theorem B208145 : Blo 107783 208145 := bstep (se 2 (by rfl) ⟨78054, by rfl⟩ : syracuseStep 208145 = 156109) B156109
theorem B109843 : Blo 107783 109843 := bstep (se 1 (by rfl) ⟨82382, by rfl⟩ : syracuseStep 109843 = 164765) B164765
theorem B109859 : Blo 107783 109859 := bstep (se 1 (by rfl) ⟨82394, by rfl⟩ : syracuseStep 109859 = 164789) B164789
theorem B109875 : Blo 107783 109875 := bstep (se 1 (by rfl) ⟨82406, by rfl⟩ : syracuseStep 109875 = 164813) B164813
theorem B109891 : Blo 107783 109891 := bstep (se 1 (by rfl) ⟨82418, by rfl⟩ : syracuseStep 109891 = 164837) B164837
theorem B109907 : Blo 107783 109907 := bstep (se 1 (by rfl) ⟨82430, by rfl⟩ : syracuseStep 109907 = 164861) B164861
theorem B109923 : Blo 107783 109923 := bstep (se 1 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 109923 = 164885) B164885
theorem B109939 : Blo 107783 109939 := bstep (se 1 (by rfl) ⟨82454, by rfl⟩ : syracuseStep 109939 = 164909) B164909
theorem B109955 : Blo 107783 109955 := bstep (se 1 (by rfl) ⟨82466, by rfl⟩ : syracuseStep 109955 = 164933) B164933
theorem B372113 : Blo 107783 372113 := bstep (se 2 (by rfl) ⟨139542, by rfl⟩ : syracuseStep 372113 = 279085) B279085
theorem B109971 : Blo 107783 109971 := bstep (se 1 (by rfl) ⟨82478, by rfl⟩ : syracuseStep 109971 = 164957) B164957
theorem B109987 : Blo 107783 109987 := bstep (se 1 (by rfl) ⟨82490, by rfl⟩ : syracuseStep 109987 = 164981) B164981
theorem B110003 : Blo 107783 110003 := bstep (se 1 (by rfl) ⟨82502, by rfl⟩ : syracuseStep 110003 = 165005) B165005
theorem B110019 : Blo 107783 110019 := bstep (se 1 (by rfl) ⟨82514, by rfl⟩ : syracuseStep 110019 = 165029) B165029
theorem B110035 : Blo 107783 110035 := bstep (se 1 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 110035 = 165053) B165053
theorem B110051 : Blo 107783 110051 := bstep (se 1 (by rfl) ⟨82538, by rfl⟩ : syracuseStep 110051 = 165077) B165077
theorem B110067 : Blo 107783 110067 := bstep (se 1 (by rfl) ⟨82550, by rfl⟩ : syracuseStep 110067 = 165101) B165101
theorem B110083 : Blo 107783 110083 := bstep (se 1 (by rfl) ⟨82562, by rfl⟩ : syracuseStep 110083 = 165125) B165125
theorem B110099 : Blo 107783 110099 := bstep (se 1 (by rfl) ⟨82574, by rfl⟩ : syracuseStep 110099 = 165149) B165149
theorem B110115 : Blo 107783 110115 := bstep (se 1 (by rfl) ⟨82586, by rfl⟩ : syracuseStep 110115 = 165173) B165173
theorem B208433 : Blo 107783 208433 := bstep (se 2 (by rfl) ⟨78162, by rfl⟩ : syracuseStep 208433 = 156325) B156325
theorem B110131 : Blo 107783 110131 := bstep (se 1 (by rfl) ⟨82598, by rfl⟩ : syracuseStep 110131 = 165197) B165197
theorem B110147 : Blo 107783 110147 := bstep (se 1 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 110147 = 165221) B165221
theorem B110163 : Blo 107783 110163 := bstep (se 1 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 110163 = 165245) B165245
theorem B110179 : Blo 107783 110179 := bstep (se 1 (by rfl) ⟨82634, by rfl⟩ : syracuseStep 110179 = 165269) B165269
theorem B110195 : Blo 107783 110195 := bstep (se 1 (by rfl) ⟨82646, by rfl⟩ : syracuseStep 110195 = 165293) B165293
theorem B110211 : Blo 107783 110211 := bstep (se 1 (by rfl) ⟨82658, by rfl⟩ : syracuseStep 110211 = 165317) B165317
theorem B110227 : Blo 107783 110227 := bstep (se 1 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 110227 = 165341) B165341
theorem B110243 : Blo 107783 110243 := bstep (se 1 (by rfl) ⟨82682, by rfl⟩ : syracuseStep 110243 = 165365) B165365
theorem B110259 : Blo 107783 110259 := bstep (se 1 (by rfl) ⟨82694, by rfl⟩ : syracuseStep 110259 = 165389) B165389
theorem B110275 : Blo 107783 110275 := bstep (se 1 (by rfl) ⟨82706, by rfl⟩ : syracuseStep 110275 = 165413) B165413
theorem B110291 : Blo 107783 110291 := bstep (se 1 (by rfl) ⟨82718, by rfl⟩ : syracuseStep 110291 = 165437) B165437
theorem B175841 : Blo 107783 175841 := bstep (se 2 (by rfl) ⟨65940, by rfl⟩ : syracuseStep 175841 = 131881) B131881
theorem B110307 : Blo 107783 110307 := bstep (se 1 (by rfl) ⟨82730, by rfl⟩ : syracuseStep 110307 = 165461) B165461
theorem B110323 : Blo 107783 110323 := bstep (se 1 (by rfl) ⟨82742, by rfl⟩ : syracuseStep 110323 = 165485) B165485
theorem B110339 : Blo 107783 110339 := bstep (se 1 (by rfl) ⟨82754, by rfl⟩ : syracuseStep 110339 = 165509) B165509
theorem B110355 : Blo 107783 110355 := bstep (se 1 (by rfl) ⟨82766, by rfl⟩ : syracuseStep 110355 = 165533) B165533
theorem B110371 : Blo 107783 110371 := bstep (se 1 (by rfl) ⟨82778, by rfl⟩ : syracuseStep 110371 = 165557) B165557
theorem B274225 : Blo 107783 274225 := bstep (se 2 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 274225 = 205669) B205669
theorem B110387 : Blo 107783 110387 := bstep (se 1 (by rfl) ⟨82790, by rfl⟩ : syracuseStep 110387 = 165581) B165581
theorem B110403 : Blo 107783 110403 := bstep (se 1 (by rfl) ⟨82802, by rfl⟩ : syracuseStep 110403 = 165605) B165605
theorem B110419 : Blo 107783 110419 := bstep (se 1 (by rfl) ⟨82814, by rfl⟩ : syracuseStep 110419 = 165629) B165629
theorem B110435 : Blo 107783 110435 := bstep (se 1 (by rfl) ⟨82826, by rfl⟩ : syracuseStep 110435 = 165653) B165653
theorem B110451 : Blo 107783 110451 := bstep (se 1 (by rfl) ⟨82838, by rfl⟩ : syracuseStep 110451 = 165677) B165677
theorem B110467 : Blo 107783 110467 := bstep (se 1 (by rfl) ⟨82850, by rfl⟩ : syracuseStep 110467 = 165701) B165701
theorem B110483 : Blo 107783 110483 := bstep (se 1 (by rfl) ⟨82862, by rfl⟩ : syracuseStep 110483 = 165725) B165725
theorem B176033 : Blo 107783 176033 := bstep (se 2 (by rfl) ⟨66012, by rfl⟩ : syracuseStep 176033 = 132025) B132025
theorem B110499 : Blo 107783 110499 := bstep (se 1 (by rfl) ⟨82874, by rfl⟩ : syracuseStep 110499 = 165749) B165749
theorem B372653 : Blo 107783 372653 := bstep (se 3 (by rfl) ⟨69872, by rfl⟩ : syracuseStep 372653 = 139745) B139745
theorem B110515 : Blo 107783 110515 := bstep (se 1 (by rfl) ⟨82886, by rfl⟩ : syracuseStep 110515 = 165773) B165773
theorem B110531 : Blo 107783 110531 := bstep (se 1 (by rfl) ⟨82898, by rfl⟩ : syracuseStep 110531 = 165797) B165797
theorem B110547 : Blo 107783 110547 := bstep (se 1 (by rfl) ⟨82910, by rfl⟩ : syracuseStep 110547 = 165821) B165821
theorem B372707 : Blo 107783 372707 := bstep (se 1 (by rfl) ⟨279530, by rfl⟩ : syracuseStep 372707 = 559061) B559061
theorem B110563 : Blo 107783 110563 := bstep (se 1 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 110563 = 165845) B165845
theorem B471025 : Blo 107783 471025 := bstep (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) B353269
theorem B110579 : Blo 107783 110579 := bstep (se 1 (by rfl) ⟨82934, by rfl⟩ : syracuseStep 110579 = 165869) B165869
theorem B110595 : Blo 107783 110595 := bstep (se 1 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 110595 = 165893) B165893
theorem B110611 : Blo 107783 110611 := bstep (se 1 (by rfl) ⟨82958, by rfl⟩ : syracuseStep 110611 = 165917) B165917
theorem B110627 : Blo 107783 110627 := bstep (se 1 (by rfl) ⟨82970, by rfl⟩ : syracuseStep 110627 = 165941) B165941
theorem B110643 : Blo 107783 110643 := bstep (se 1 (by rfl) ⟨82982, by rfl⟩ : syracuseStep 110643 = 165965) B165965
theorem B274499 : Blo 107783 274499 := bstep (se 1 (by rfl) ⟨205874, by rfl⟩ : syracuseStep 274499 = 411749) B411749
theorem B110659 : Blo 107783 110659 := bstep (se 1 (by rfl) ⟨82994, by rfl⟩ : syracuseStep 110659 = 165989) B165989
theorem B110675 : Blo 107783 110675 := bstep (se 1 (by rfl) ⟨83006, by rfl⟩ : syracuseStep 110675 = 166013) B166013
theorem B110691 : Blo 107783 110691 := bstep (se 1 (by rfl) ⟨83018, by rfl⟩ : syracuseStep 110691 = 166037) B166037
theorem B110707 : Blo 107783 110707 := bstep (se 1 (by rfl) ⟨83030, by rfl⟩ : syracuseStep 110707 = 166061) B166061
theorem B110723 : Blo 107783 110723 := bstep (se 1 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 110723 = 166085) B166085
theorem B110739 : Blo 107783 110739 := bstep (se 1 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 110739 = 166109) B166109
theorem B110755 : Blo 107783 110755 := bstep (se 1 (by rfl) ⟨83066, by rfl⟩ : syracuseStep 110755 = 166133) B166133
theorem B110771 : Blo 107783 110771 := bstep (se 1 (by rfl) ⟨83078, by rfl⟩ : syracuseStep 110771 = 166157) B166157
theorem B110787 : Blo 107783 110787 := bstep (se 1 (by rfl) ⟨83090, by rfl⟩ : syracuseStep 110787 = 166181) B166181
theorem B110803 : Blo 107783 110803 := bstep (se 1 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 110803 = 166205) B166205
theorem B209123 : Blo 107783 209123 := bstep (se 1 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 209123 = 313685) B313685
theorem B110819 : Blo 107783 110819 := bstep (se 1 (by rfl) ⟨83114, by rfl⟩ : syracuseStep 110819 = 166229) B166229
theorem B372977 : Blo 107783 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B110835 : Blo 107783 110835 := bstep (se 1 (by rfl) ⟨83126, by rfl⟩ : syracuseStep 110835 = 166253) B166253
theorem B274691 : Blo 107783 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B209155 : Blo 107783 209155 := bstep (se 1 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 209155 = 313733) B313733
theorem B110851 : Blo 107783 110851 := bstep (se 1 (by rfl) ⟨83138, by rfl⟩ : syracuseStep 110851 = 166277) B166277
theorem B635141 : Blo 107783 635141 := bstep (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) B119089
theorem B110867 : Blo 107783 110867 := bstep (se 1 (by rfl) ⟨83150, by rfl⟩ : syracuseStep 110867 = 166301) B166301
theorem B110883 : Blo 107783 110883 := bstep (se 1 (by rfl) ⟨83162, by rfl⟩ : syracuseStep 110883 = 166325) B166325
theorem B602417 : Blo 107783 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B110899 : Blo 107783 110899 := bstep (se 1 (by rfl) ⟨83174, by rfl⟩ : syracuseStep 110899 = 166349) B166349
theorem B110915 : Blo 107783 110915 := bstep (se 1 (by rfl) ⟨83186, by rfl⟩ : syracuseStep 110915 = 166373) B166373
theorem B110931 : Blo 107783 110931 := bstep (se 1 (by rfl) ⟨83198, by rfl⟩ : syracuseStep 110931 = 166397) B166397
theorem B110947 : Blo 107783 110947 := bstep (se 1 (by rfl) ⟨83210, by rfl⟩ : syracuseStep 110947 = 166421) B166421
theorem B1323377 : Blo 107783 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B110963 : Blo 107783 110963 := bstep (se 1 (by rfl) ⟨83222, by rfl⟩ : syracuseStep 110963 = 166445) B166445
theorem B110979 : Blo 107783 110979 := bstep (se 1 (by rfl) ⟨83234, by rfl⟩ : syracuseStep 110979 = 166469) B166469
theorem B110995 : Blo 107783 110995 := bstep (se 1 (by rfl) ⟨83246, by rfl⟩ : syracuseStep 110995 = 166493) B166493
theorem B111011 : Blo 107783 111011 := bstep (se 1 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 111011 = 166517) B166517
theorem B111027 : Blo 107783 111027 := bstep (se 1 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 111027 = 166541) B166541
theorem B111043 : Blo 107783 111043 := bstep (se 1 (by rfl) ⟨83282, by rfl⟩ : syracuseStep 111043 = 166565) B166565
theorem B111059 : Blo 107783 111059 := bstep (se 1 (by rfl) ⟨83294, by rfl⟩ : syracuseStep 111059 = 166589) B166589
theorem B111075 : Blo 107783 111075 := bstep (se 1 (by rfl) ⟨83306, by rfl⟩ : syracuseStep 111075 = 166613) B166613
theorem B111091 : Blo 107783 111091 := bstep (se 1 (by rfl) ⟨83318, by rfl⟩ : syracuseStep 111091 = 166637) B166637
theorem B111107 : Blo 107783 111107 := bstep (se 1 (by rfl) ⟨83330, by rfl⟩ : syracuseStep 111107 = 166661) B166661
theorem B307729 : Blo 107783 307729 := bstep (se 2 (by rfl) ⟨115398, by rfl⟩ : syracuseStep 307729 = 230797) B230797
theorem B111123 : Blo 107783 111123 := bstep (se 1 (by rfl) ⟨83342, by rfl⟩ : syracuseStep 111123 = 166685) B166685
theorem B111139 : Blo 107783 111139 := bstep (se 1 (by rfl) ⟨83354, by rfl⟩ : syracuseStep 111139 = 166709) B166709
theorem B111155 : Blo 107783 111155 := bstep (se 1 (by rfl) ⟨83366, by rfl⟩ : syracuseStep 111155 = 166733) B166733
theorem B111171 : Blo 107783 111171 := bstep (se 1 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 111171 = 166757) B166757
theorem B111187 : Blo 107783 111187 := bstep (se 1 (by rfl) ⟨83390, by rfl⟩ : syracuseStep 111187 = 166781) B166781
theorem B111203 : Blo 107783 111203 := bstep (se 1 (by rfl) ⟨83402, by rfl⟩ : syracuseStep 111203 = 166805) B166805
theorem B111219 : Blo 107783 111219 := bstep (se 1 (by rfl) ⟨83414, by rfl⟩ : syracuseStep 111219 = 166829) B166829
theorem B111235 : Blo 107783 111235 := bstep (se 1 (by rfl) ⟨83426, by rfl⟩ : syracuseStep 111235 = 166853) B166853
theorem B111251 : Blo 107783 111251 := bstep (se 1 (by rfl) ⟨83438, by rfl⟩ : syracuseStep 111251 = 166877) B166877
theorem B111267 : Blo 107783 111267 := bstep (se 1 (by rfl) ⟨83450, by rfl⟩ : syracuseStep 111267 = 166901) B166901
theorem B111283 : Blo 107783 111283 := bstep (se 1 (by rfl) ⟨83462, by rfl⟩ : syracuseStep 111283 = 166925) B166925
theorem B111299 : Blo 107783 111299 := bstep (se 1 (by rfl) ⟨83474, by rfl⟩ : syracuseStep 111299 = 166949) B166949
theorem B209603 : Blo 107783 209603 := bstep (se 1 (by rfl) ⟨157202, by rfl⟩ : syracuseStep 209603 = 314405) B314405
theorem B635597 : Blo 107783 635597 := bstep (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) B238349
theorem B111315 : Blo 107783 111315 := bstep (se 1 (by rfl) ⟨83486, by rfl⟩ : syracuseStep 111315 = 166973) B166973
theorem B111331 : Blo 107783 111331 := bstep (se 1 (by rfl) ⟨83498, by rfl⟩ : syracuseStep 111331 = 166997) B166997
theorem B111347 : Blo 107783 111347 := bstep (se 1 (by rfl) ⟨83510, by rfl⟩ : syracuseStep 111347 = 167021) B167021
theorem B111363 : Blo 107783 111363 := bstep (se 1 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 111363 = 167045) B167045
theorem B1258253 : Blo 107783 1258253 := bstep (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) B471845
theorem B373517 : Blo 107783 373517 := bstep (se 3 (by rfl) ⟨70034, by rfl⟩ : syracuseStep 373517 = 140069) B140069
theorem B111379 : Blo 107783 111379 := bstep (se 1 (by rfl) ⟨83534, by rfl⟩ : syracuseStep 111379 = 167069) B167069
theorem B111395 : Blo 107783 111395 := bstep (se 1 (by rfl) ⟨83546, by rfl⟩ : syracuseStep 111395 = 167093) B167093
theorem B111411 : Blo 107783 111411 := bstep (se 1 (by rfl) ⟨83558, by rfl⟩ : syracuseStep 111411 = 167117) B167117
theorem B373571 : Blo 107783 373571 := bstep (se 1 (by rfl) ⟨280178, by rfl⟩ : syracuseStep 373571 = 560357) B560357
theorem B111427 : Blo 107783 111427 := bstep (se 1 (by rfl) ⟨83570, by rfl⟩ : syracuseStep 111427 = 167141) B167141
theorem B242513 : Blo 107783 242513 := bstep (se 2 (by rfl) ⟨90942, by rfl⟩ : syracuseStep 242513 = 181885) B181885
theorem B111443 : Blo 107783 111443 := bstep (se 1 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 111443 = 167165) B167165
theorem B242531 : Blo 107783 242531 := bstep (se 1 (by rfl) ⟨181898, by rfl⟩ : syracuseStep 242531 = 363797) B363797
theorem B111459 : Blo 107783 111459 := bstep (se 1 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 111459 = 167189) B167189
theorem B111475 : Blo 107783 111475 := bstep (se 1 (by rfl) ⟨83606, by rfl⟩ : syracuseStep 111475 = 167213) B167213
theorem B111491 : Blo 107783 111491 := bstep (se 1 (by rfl) ⟨83618, by rfl⟩ : syracuseStep 111491 = 167237) B167237
theorem B111507 : Blo 107783 111507 := bstep (se 1 (by rfl) ⟨83630, by rfl⟩ : syracuseStep 111507 = 167261) B167261
theorem B111523 : Blo 107783 111523 := bstep (se 1 (by rfl) ⟨83642, by rfl⟩ : syracuseStep 111523 = 167285) B167285
theorem B111539 : Blo 107783 111539 := bstep (se 1 (by rfl) ⟨83654, by rfl⟩ : syracuseStep 111539 = 167309) B167309
theorem B111555 : Blo 107783 111555 := bstep (se 1 (by rfl) ⟨83666, by rfl⟩ : syracuseStep 111555 = 167333) B167333
theorem B111571 : Blo 107783 111571 := bstep (se 1 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 111571 = 167357) B167357
theorem B209891 : Blo 107783 209891 := bstep (se 1 (by rfl) ⟨157418, by rfl⟩ : syracuseStep 209891 = 314837) B314837
theorem B111587 : Blo 107783 111587 := bstep (se 1 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 111587 = 167381) B167381
theorem B111603 : Blo 107783 111603 := bstep (se 1 (by rfl) ⟨83702, by rfl⟩ : syracuseStep 111603 = 167405) B167405
theorem B111619 : Blo 107783 111619 := bstep (se 1 (by rfl) ⟨83714, by rfl⟩ : syracuseStep 111619 = 167429) B167429
theorem B111635 : Blo 107783 111635 := bstep (se 1 (by rfl) ⟨83726, by rfl⟩ : syracuseStep 111635 = 167453) B167453
theorem B111651 : Blo 107783 111651 := bstep (se 1 (by rfl) ⟨83738, by rfl⟩ : syracuseStep 111651 = 167477) B167477
theorem B111667 : Blo 107783 111667 := bstep (se 1 (by rfl) ⟨83750, by rfl⟩ : syracuseStep 111667 = 167501) B167501
theorem B144451 : Blo 107783 144451 := bstep (se 1 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 144451 = 216677) B216677
theorem B111683 : Blo 107783 111683 := bstep (se 1 (by rfl) ⟨83762, by rfl⟩ : syracuseStep 111683 = 167525) B167525
theorem B373841 : Blo 107783 373841 := bstep (se 2 (by rfl) ⟨140190, by rfl⟩ : syracuseStep 373841 = 280381) B280381
theorem B111699 : Blo 107783 111699 := bstep (se 1 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 111699 = 167549) B167549
theorem B111715 : Blo 107783 111715 := bstep (se 1 (by rfl) ⟨83786, by rfl⟩ : syracuseStep 111715 = 167573) B167573
theorem B242801 : Blo 107783 242801 := bstep (se 2 (by rfl) ⟨91050, by rfl⟩ : syracuseStep 242801 = 182101) B182101
theorem B111731 : Blo 107783 111731 := bstep (se 1 (by rfl) ⟨83798, by rfl⟩ : syracuseStep 111731 = 167597) B167597
theorem B242819 : Blo 107783 242819 := bstep (se 1 (by rfl) ⟨182114, by rfl⟩ : syracuseStep 242819 = 364229) B364229
theorem B111747 : Blo 107783 111747 := bstep (se 1 (by rfl) ⟨83810, by rfl⟩ : syracuseStep 111747 = 167621) B167621
theorem B111763 : Blo 107783 111763 := bstep (se 1 (by rfl) ⟨83822, by rfl⟩ : syracuseStep 111763 = 167645) B167645
theorem B111779 : Blo 107783 111779 := bstep (se 1 (by rfl) ⟨83834, by rfl⟩ : syracuseStep 111779 = 167669) B167669
theorem B275633 : Blo 107783 275633 := bstep (se 2 (by rfl) ⟨103362, by rfl⟩ : syracuseStep 275633 = 206725) B206725
theorem B701617 : Blo 107783 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B275683 : Blo 107783 275683 := bstep (se 1 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 275683 = 413525) B413525
theorem B3880163 : Blo 107783 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B10073315 : Blo 107783 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B275825 : Blo 107783 275825 := bstep (se 2 (by rfl) ⟨103434, by rfl⟩ : syracuseStep 275825 = 206869) B206869
theorem B243089 : Blo 107783 243089 := bstep (se 2 (by rfl) ⟨91158, by rfl⟩ : syracuseStep 243089 = 182317) B182317
theorem B243107 : Blo 107783 243107 := bstep (se 1 (by rfl) ⟨182330, by rfl⟩ : syracuseStep 243107 = 364661) B364661
theorem B177635 : Blo 107783 177635 := bstep (se 1 (by rfl) ⟨133226, by rfl⟩ : syracuseStep 177635 = 266453) B266453
theorem B341489 : Blo 107783 341489 := bstep (se 2 (by rfl) ⟨128058, by rfl⟩ : syracuseStep 341489 = 256117) B256117
theorem B112195 : Blo 107783 112195 := bstep (se 1 (by rfl) ⟨84146, by rfl⟩ : syracuseStep 112195 = 168293) B168293
theorem B1422917 : Blo 107783 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B374381 : Blo 107783 374381 := bstep (se 3 (by rfl) ⟨70196, by rfl⟩ : syracuseStep 374381 = 140393) B140393
theorem B374435 : Blo 107783 374435 := bstep (se 1 (by rfl) ⟨280826, by rfl⟩ : syracuseStep 374435 = 561653) B561653
theorem B243377 : Blo 107783 243377 := bstep (se 2 (by rfl) ⟨91266, by rfl⟩ : syracuseStep 243377 = 182533) B182533
theorem B243395 : Blo 107783 243395 := bstep (se 1 (by rfl) ⟨182546, by rfl⟩ : syracuseStep 243395 = 365093) B365093
theorem B309005 : Blo 107783 309005 := bstep (se 3 (by rfl) ⟨57938, by rfl⟩ : syracuseStep 309005 = 115877) B115877
theorem B178019 : Blo 107783 178019 := bstep (se 1 (by rfl) ⟨133514, by rfl⟩ : syracuseStep 178019 = 267029) B267029
theorem B1357667 : Blo 107783 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B210833 : Blo 107783 210833 := bstep (se 2 (by rfl) ⟨79062, by rfl⟩ : syracuseStep 210833 = 158125) B158125
theorem B669617 : Blo 107783 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B374705 : Blo 107783 374705 := bstep (se 2 (by rfl) ⟨140514, by rfl⟩ : syracuseStep 374705 = 281029) B281029
theorem B309187 : Blo 107783 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B243665 : Blo 107783 243665 := bstep (se 2 (by rfl) ⟨91374, by rfl⟩ : syracuseStep 243665 = 182749) B182749
theorem B243683 : Blo 107783 243683 := bstep (se 1 (by rfl) ⟨182762, by rfl⟩ : syracuseStep 243683 = 365525) B365525
theorem B669667 : Blo 107783 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B178147 : Blo 107783 178147 := bstep (se 1 (by rfl) ⟨133610, by rfl⟩ : syracuseStep 178147 = 267221) B267221
theorem B309233 : Blo 107783 309233 := bstep (se 2 (by rfl) ⟨115962, by rfl⟩ : syracuseStep 309233 = 231925) B231925
theorem B604273 : Blo 107783 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B243953 : Blo 107783 243953 := bstep (se 2 (by rfl) ⟨91482, by rfl⟩ : syracuseStep 243953 = 182965) B182965
theorem B243971 : Blo 107783 243971 := bstep (se 1 (by rfl) ⟨182978, by rfl⟩ : syracuseStep 243971 = 365957) B365957
theorem B276817 : Blo 107783 276817 := bstep (se 2 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 276817 = 207613) B207613
theorem B375245 : Blo 107783 375245 := bstep (se 3 (by rfl) ⟨70358, by rfl⟩ : syracuseStep 375245 = 140717) B140717
theorem B375299 : Blo 107783 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B244241 : Blo 107783 244241 := bstep (se 2 (by rfl) ⟨91590, by rfl⟩ : syracuseStep 244241 = 183181) B183181
theorem B244259 : Blo 107783 244259 := bstep (se 1 (by rfl) ⟨183194, by rfl⟩ : syracuseStep 244259 = 366389) B366389
theorem B277091 : Blo 107783 277091 := bstep (se 1 (by rfl) ⟨207818, by rfl⟩ : syracuseStep 277091 = 415637) B415637
theorem B178865 : Blo 107783 178865 := bstep (se 2 (by rfl) ⟨67074, by rfl⟩ : syracuseStep 178865 = 134149) B134149
theorem B801521 : Blo 107783 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B375569 : Blo 107783 375569 := bstep (se 2 (by rfl) ⟨140838, by rfl⟩ : syracuseStep 375569 = 281677) B281677
theorem B211729 : Blo 107783 211729 := bstep (se 2 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 211729 = 158797) B158797
theorem B277283 : Blo 107783 277283 := bstep (se 1 (by rfl) ⟨207962, by rfl⟩ : syracuseStep 277283 = 415925) B415925
theorem B244529 : Blo 107783 244529 := bstep (se 2 (by rfl) ⟨91698, by rfl⟩ : syracuseStep 244529 = 183397) B183397
theorem B244547 : Blo 107783 244547 := bstep (se 1 (by rfl) ⟨183410, by rfl⟩ : syracuseStep 244547 = 366821) B366821
theorem B179057 : Blo 107783 179057 := bstep (se 2 (by rfl) ⟨67146, by rfl⟩ : syracuseStep 179057 = 134293) B134293
theorem B211889 : Blo 107783 211889 := bstep (se 2 (by rfl) ⟨79458, by rfl⟩ : syracuseStep 211889 = 158917) B158917
theorem B244817 : Blo 107783 244817 := bstep (se 2 (by rfl) ⟨91806, by rfl⟩ : syracuseStep 244817 = 183613) B183613
theorem B244835 : Blo 107783 244835 := bstep (se 1 (by rfl) ⟨183626, by rfl⟩ : syracuseStep 244835 = 367253) B367253
theorem B113891 : Blo 107783 113891 := bstep (se 1 (by rfl) ⟨85418, by rfl⟩ : syracuseStep 113891 = 170837) B170837
theorem B376109 : Blo 107783 376109 := bstep (se 3 (by rfl) ⟨70520, by rfl⟩ : syracuseStep 376109 = 141041) B141041
theorem B376163 : Blo 107783 376163 := bstep (se 1 (by rfl) ⟨282122, by rfl⟩ : syracuseStep 376163 = 564245) B564245
theorem B245105 : Blo 107783 245105 := bstep (se 2 (by rfl) ⟨91914, by rfl⟩ : syracuseStep 245105 = 183829) B183829
theorem B245123 : Blo 107783 245123 := bstep (se 1 (by rfl) ⟨183842, by rfl⟩ : syracuseStep 245123 = 367685) B367685
theorem B310691 : Blo 107783 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B474545 : Blo 107783 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B1261169 : Blo 107783 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B376433 : Blo 107783 376433 := bstep (se 2 (by rfl) ⟨141162, by rfl⟩ : syracuseStep 376433 = 282325) B282325
theorem B245393 : Blo 107783 245393 := bstep (se 2 (by rfl) ⟨92022, by rfl⟩ : syracuseStep 245393 = 184045) B184045
theorem B245411 : Blo 107783 245411 := bstep (se 1 (by rfl) ⟨184058, by rfl⟩ : syracuseStep 245411 = 368117) B368117
theorem B114355 : Blo 107783 114355 := bstep (se 1 (by rfl) ⟨85766, by rfl⟩ : syracuseStep 114355 = 171533) B171533
theorem B278225 : Blo 107783 278225 := bstep (se 2 (by rfl) ⟨104334, by rfl⟩ : syracuseStep 278225 = 208669) B208669
theorem B147187 : Blo 107783 147187 := bstep (se 1 (by rfl) ⟨110390, by rfl⟩ : syracuseStep 147187 = 220781) B220781
theorem B278275 : Blo 107783 278275 := bstep (se 1 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 278275 = 417413) B417413
theorem B2015117 : Blo 107783 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B278417 : Blo 107783 278417 := bstep (se 2 (by rfl) ⟨104406, by rfl⟩ : syracuseStep 278417 = 208813) B208813
theorem B147361 : Blo 107783 147361 := bstep (se 2 (by rfl) ⟨55260, by rfl⟩ : syracuseStep 147361 = 110521) B110521
theorem B245681 : Blo 107783 245681 := bstep (se 2 (by rfl) ⟨92130, by rfl⟩ : syracuseStep 245681 = 184261) B184261
theorem B245699 : Blo 107783 245699 := bstep (se 1 (by rfl) ⟨184274, by rfl⟩ : syracuseStep 245699 = 368549) B368549
theorem B376973 : Blo 107783 376973 := bstep (se 3 (by rfl) ⟨70682, by rfl⟩ : syracuseStep 376973 = 141365) B141365
theorem B377027 : Blo 107783 377027 := bstep (se 1 (by rfl) ⟨282770, by rfl⟩ : syracuseStep 377027 = 565541) B565541
theorem B409805 : Blo 107783 409805 := bstep (se 3 (by rfl) ⟨76838, by rfl⟩ : syracuseStep 409805 = 153677) B153677
theorem B245969 : Blo 107783 245969 := bstep (se 2 (by rfl) ⟨92238, by rfl⟩ : syracuseStep 245969 = 184477) B184477
theorem B245987 : Blo 107783 245987 := bstep (se 1 (by rfl) ⟨184490, by rfl⟩ : syracuseStep 245987 = 368981) B368981
theorem B1589557 : Blo 107783 1589557 := bstep (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) B149021
theorem B672077 : Blo 107783 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B475469 : Blo 107783 475469 := bstep (se 3 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 475469 = 178301) B178301
theorem B246257 : Blo 107783 246257 := bstep (se 2 (by rfl) ⟨92346, by rfl⟩ : syracuseStep 246257 = 184693) B184693
theorem B246275 : Blo 107783 246275 := bstep (se 1 (by rfl) ⟨184706, by rfl⟩ : syracuseStep 246275 = 369413) B369413
theorem B311921 : Blo 107783 311921 := bstep (se 2 (by rfl) ⟨116970, by rfl⟩ : syracuseStep 311921 = 233941) B233941
theorem B2081477 : Blo 107783 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B246545 : Blo 107783 246545 := bstep (se 2 (by rfl) ⟨92454, by rfl⟩ : syracuseStep 246545 = 184909) B184909
theorem B246563 : Blo 107783 246563 := bstep (se 1 (by rfl) ⟨184922, by rfl⟩ : syracuseStep 246563 = 369845) B369845
theorem B279409 : Blo 107783 279409 := bstep (se 2 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 279409 = 209557) B209557
theorem B508835 : Blo 107783 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B410609 : Blo 107783 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B115715 : Blo 107783 115715 := bstep (se 1 (by rfl) ⟨86786, by rfl⟩ : syracuseStep 115715 = 173573) B173573
theorem B246833 : Blo 107783 246833 := bstep (se 2 (by rfl) ⟨92562, by rfl⟩ : syracuseStep 246833 = 185125) B185125
theorem B246851 : Blo 107783 246851 := bstep (se 1 (by rfl) ⟨185138, by rfl⟩ : syracuseStep 246851 = 370277) B370277
theorem B279683 : Blo 107783 279683 := bstep (se 1 (by rfl) ⟨209762, by rfl⟩ : syracuseStep 279683 = 419525) B419525
theorem B279875 : Blo 107783 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B247121 : Blo 107783 247121 := bstep (se 2 (by rfl) ⟨92670, by rfl⟩ : syracuseStep 247121 = 185341) B185341
theorem B247139 : Blo 107783 247139 := bstep (se 1 (by rfl) ⟨185354, by rfl⟩ : syracuseStep 247139 = 370709) B370709
theorem B1525301 : Blo 107783 1525301 := bstep (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) B142997
theorem B247409 : Blo 107783 247409 := bstep (se 2 (by rfl) ⟨92778, by rfl⟩ : syracuseStep 247409 = 185557) B185557
theorem B247427 : Blo 107783 247427 := bstep (se 1 (by rfl) ⟨185570, by rfl⟩ : syracuseStep 247427 = 371141) B371141
theorem B411277 : Blo 107783 411277 := bstep (se 3 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 411277 = 154229) B154229
theorem B181939 : Blo 107783 181939 := bstep (se 1 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 181939 = 272909) B272909
theorem B182081 : Blo 107783 182081 := bstep (se 2 (by rfl) ⟨68280, by rfl⟩ : syracuseStep 182081 = 136561) B136561
theorem B247697 : Blo 107783 247697 := bstep (se 2 (by rfl) ⟨92886, by rfl⟩ : syracuseStep 247697 = 185773) B185773
theorem B247715 : Blo 107783 247715 := bstep (se 1 (by rfl) ⟨185786, by rfl⟩ : syracuseStep 247715 = 371573) B371573
theorem B1427381 : Blo 107783 1427381 := bstep (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) B133817
theorem B182209 : Blo 107783 182209 := bstep (se 2 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 182209 = 136657) B136657
theorem B182243 : Blo 107783 182243 := bstep (se 1 (by rfl) ⟨136682, by rfl⟩ : syracuseStep 182243 = 273365) B273365
theorem B280547 : Blo 107783 280547 := bstep (se 1 (by rfl) ⟨210410, by rfl⟩ : syracuseStep 280547 = 420821) B420821
theorem B313379 : Blo 107783 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B182371 : Blo 107783 182371 := bstep (se 1 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 182371 = 273557) B273557
theorem B116851 : Blo 107783 116851 := bstep (se 1 (by rfl) ⟨87638, by rfl⟩ : syracuseStep 116851 = 175277) B175277
theorem B247985 : Blo 107783 247985 := bstep (se 2 (by rfl) ⟨92994, by rfl⟩ : syracuseStep 247985 = 185989) B185989
theorem B248003 : Blo 107783 248003 := bstep (se 1 (by rfl) ⟨186002, by rfl⟩ : syracuseStep 248003 = 372005) B372005
theorem B182513 : Blo 107783 182513 := bstep (se 2 (by rfl) ⟨68442, by rfl⟩ : syracuseStep 182513 = 136885) B136885
theorem B280817 : Blo 107783 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B280867 : Blo 107783 280867 := bstep (se 1 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 280867 = 421301) B421301
theorem B182641 : Blo 107783 182641 := bstep (se 2 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 182641 = 136981) B136981
theorem B182675 : Blo 107783 182675 := bstep (se 1 (by rfl) ⟨137006, by rfl⟩ : syracuseStep 182675 = 274013) B274013
theorem B412067 : Blo 107783 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B281009 : Blo 107783 281009 := bstep (se 2 (by rfl) ⟨105378, by rfl⟩ : syracuseStep 281009 = 210757) B210757
theorem B1329605 : Blo 107783 1329605 := bstep (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) B249301
theorem B248273 : Blo 107783 248273 := bstep (se 2 (by rfl) ⟨93102, by rfl⟩ : syracuseStep 248273 = 186205) B186205
theorem B248291 : Blo 107783 248291 := bstep (se 1 (by rfl) ⟨186218, by rfl⟩ : syracuseStep 248291 = 372437) B372437
theorem B182803 : Blo 107783 182803 := bstep (se 1 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 182803 = 274205) B274205
theorem B477731 : Blo 107783 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B182945 : Blo 107783 182945 := bstep (se 2 (by rfl) ⟨68604, by rfl⟩ : syracuseStep 182945 = 137209) B137209
theorem B248561 : Blo 107783 248561 := bstep (se 2 (by rfl) ⟨93210, by rfl⟩ : syracuseStep 248561 = 186421) B186421
theorem B248579 : Blo 107783 248579 := bstep (se 1 (by rfl) ⟨186434, by rfl⟩ : syracuseStep 248579 = 372869) B372869
theorem B183073 : Blo 107783 183073 := bstep (se 2 (by rfl) ⟨68652, by rfl⟩ : syracuseStep 183073 = 137305) B137305
theorem B183107 : Blo 107783 183107 := bstep (se 1 (by rfl) ⟨137330, by rfl⟩ : syracuseStep 183107 = 274661) B274661
theorem B314189 : Blo 107783 314189 := bstep (se 3 (by rfl) ⟨58910, by rfl⟩ : syracuseStep 314189 = 117821) B117821
theorem B183235 : Blo 107783 183235 := bstep (se 1 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 183235 = 274853) B274853
theorem B117731 : Blo 107783 117731 := bstep (se 1 (by rfl) ⟨88298, by rfl⟩ : syracuseStep 117731 = 176597) B176597
theorem B314381 : Blo 107783 314381 := bstep (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) B117893
theorem B248849 : Blo 107783 248849 := bstep (se 2 (by rfl) ⟨93318, by rfl⟩ : syracuseStep 248849 = 186637) B186637
theorem B248867 : Blo 107783 248867 := bstep (se 1 (by rfl) ⟨186650, by rfl⟩ : syracuseStep 248867 = 373301) B373301
theorem B412721 : Blo 107783 412721 := bstep (se 2 (by rfl) ⟨154770, by rfl⟩ : syracuseStep 412721 = 309541) B309541
theorem B183377 : Blo 107783 183377 := bstep (se 2 (by rfl) ⟨68766, by rfl⟩ : syracuseStep 183377 = 137533) B137533
theorem B117859 : Blo 107783 117859 := bstep (se 1 (by rfl) ⟨88394, by rfl⟩ : syracuseStep 117859 = 176789) B176789
theorem B183505 : Blo 107783 183505 := bstep (se 2 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 183505 = 137629) B137629
theorem B183539 : Blo 107783 183539 := bstep (se 1 (by rfl) ⟨137654, by rfl⟩ : syracuseStep 183539 = 275309) B275309
theorem B249137 : Blo 107783 249137 := bstep (se 2 (by rfl) ⟨93426, by rfl⟩ : syracuseStep 249137 = 186853) B186853
theorem B249155 : Blo 107783 249155 := bstep (se 1 (by rfl) ⟨186866, by rfl⟩ : syracuseStep 249155 = 373733) B373733
theorem B183667 : Blo 107783 183667 := bstep (se 1 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 183667 = 275501) B275501
theorem B282001 : Blo 107783 282001 := bstep (se 2 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 282001 = 211501) B211501
theorem B151025 : Blo 107783 151025 := bstep (se 2 (by rfl) ⟨56634, by rfl⟩ : syracuseStep 151025 = 113269) B113269
theorem B183809 : Blo 107783 183809 := bstep (se 2 (by rfl) ⟨68928, by rfl⟩ : syracuseStep 183809 = 137857) B137857
theorem B249425 : Blo 107783 249425 := bstep (se 2 (by rfl) ⟨93534, by rfl⟩ : syracuseStep 249425 = 187069) B187069
theorem B249443 : Blo 107783 249443 := bstep (se 1 (by rfl) ⟨187082, by rfl⟩ : syracuseStep 249443 = 374165) B374165
theorem B183937 : Blo 107783 183937 := bstep (se 2 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 183937 = 137953) B137953
theorem B183971 : Blo 107783 183971 := bstep (se 1 (by rfl) ⟨137978, by rfl⟩ : syracuseStep 183971 = 275957) B275957
theorem B282275 : Blo 107783 282275 := bstep (se 1 (by rfl) ⟨211706, by rfl⟩ : syracuseStep 282275 = 423413) B423413
theorem B347939 : Blo 107783 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B184099 : Blo 107783 184099 := bstep (se 1 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 184099 = 276149) B276149
theorem B282467 : Blo 107783 282467 := bstep (se 1 (by rfl) ⟨211850, by rfl⟩ : syracuseStep 282467 = 423701) B423701
theorem B249713 : Blo 107783 249713 := bstep (se 2 (by rfl) ⟨93642, by rfl⟩ : syracuseStep 249713 = 187285) B187285
theorem B249731 : Blo 107783 249731 := bstep (se 1 (by rfl) ⟨187298, by rfl⟩ : syracuseStep 249731 = 374597) B374597
theorem B118675 : Blo 107783 118675 := bstep (se 1 (by rfl) ⟨89006, by rfl⟩ : syracuseStep 118675 = 178013) B178013
theorem B348067 : Blo 107783 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B184241 : Blo 107783 184241 := bstep (se 2 (by rfl) ⟨69090, by rfl⟩ : syracuseStep 184241 = 138181) B138181
theorem B315373 : Blo 107783 315373 := bstep (se 3 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 315373 = 118265) B118265
theorem B937969 : Blo 107783 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B184369 : Blo 107783 184369 := bstep (se 2 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 184369 = 138277) B138277
theorem B184403 : Blo 107783 184403 := bstep (se 1 (by rfl) ⟨138302, by rfl⟩ : syracuseStep 184403 = 276605) B276605
theorem B250001 : Blo 107783 250001 := bstep (se 2 (by rfl) ⟨93750, by rfl⟩ : syracuseStep 250001 = 187501) B187501
theorem B250019 : Blo 107783 250019 := bstep (se 1 (by rfl) ⟨187514, by rfl⟩ : syracuseStep 250019 = 375029) B375029
theorem B184531 : Blo 107783 184531 := bstep (se 1 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 184531 = 276797) B276797
theorem B348401 : Blo 107783 348401 := bstep (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) B261301
theorem B184673 : Blo 107783 184673 := bstep (se 2 (by rfl) ⟨69252, by rfl⟩ : syracuseStep 184673 = 138505) B138505
theorem B250289 : Blo 107783 250289 := bstep (se 2 (by rfl) ⟨93858, by rfl⟩ : syracuseStep 250289 = 187717) B187717
theorem B250307 : Blo 107783 250307 := bstep (se 1 (by rfl) ⟨187730, by rfl⟩ : syracuseStep 250307 = 375461) B375461
theorem B17125829 : Blo 107783 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B184801 : Blo 107783 184801 := bstep (se 2 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 184801 = 138601) B138601
theorem B414179 : Blo 107783 414179 := bstep (se 1 (by rfl) ⟨310634, by rfl⟩ : syracuseStep 414179 = 621269) B621269
theorem B414193 : Blo 107783 414193 := bstep (se 2 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 414193 = 310645) B310645
theorem B184835 : Blo 107783 184835 := bstep (se 1 (by rfl) ⟨138626, by rfl⟩ : syracuseStep 184835 = 277253) B277253
theorem B3002993 : Blo 107783 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B184963 : Blo 107783 184963 := bstep (se 1 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 184963 = 277445) B277445
theorem B348845 : Blo 107783 348845 := bstep (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) B130817
theorem B250577 : Blo 107783 250577 := bstep (se 2 (by rfl) ⟨93966, by rfl⟩ : syracuseStep 250577 = 187933) B187933
theorem B250595 : Blo 107783 250595 := bstep (se 1 (by rfl) ⟨187946, by rfl⟩ : syracuseStep 250595 = 375893) B375893
theorem B185105 : Blo 107783 185105 := bstep (se 2 (by rfl) ⟨69414, by rfl⟩ : syracuseStep 185105 = 138829) B138829
theorem B1528645 : Blo 107783 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B185233 : Blo 107783 185233 := bstep (se 2 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 185233 = 138925) B138925
theorem B185267 : Blo 107783 185267 := bstep (se 1 (by rfl) ⟨138950, by rfl⟩ : syracuseStep 185267 = 277901) B277901
theorem B545777 : Blo 107783 545777 := bstep (se 2 (by rfl) ⟨204666, by rfl⟩ : syracuseStep 545777 = 409333) B409333
theorem B250865 : Blo 107783 250865 := bstep (se 2 (by rfl) ⟨94074, by rfl⟩ : syracuseStep 250865 = 188149) B188149
theorem B250883 : Blo 107783 250883 := bstep (se 1 (by rfl) ⟨188162, by rfl⟩ : syracuseStep 250883 = 376325) B376325
theorem B709667 : Blo 107783 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B185395 : Blo 107783 185395 := bstep (se 1 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 185395 = 278093) B278093
theorem B185537 : Blo 107783 185537 := bstep (se 2 (by rfl) ⟨69576, by rfl⟩ : syracuseStep 185537 = 139153) B139153
theorem B251153 : Blo 107783 251153 := bstep (se 2 (by rfl) ⟨94182, by rfl⟩ : syracuseStep 251153 = 188365) B188365
theorem B251171 : Blo 107783 251171 := bstep (se 1 (by rfl) ⟨188378, by rfl⟩ : syracuseStep 251171 = 376757) B376757
theorem B185665 : Blo 107783 185665 := bstep (se 2 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 185665 = 139249) B139249
theorem B185699 : Blo 107783 185699 := bstep (se 1 (by rfl) ⟨139274, by rfl⟩ : syracuseStep 185699 = 278549) B278549
theorem B185827 : Blo 107783 185827 := bstep (se 1 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 185827 = 278741) B278741
theorem B218641 : Blo 107783 218641 := bstep (se 2 (by rfl) ⟨81990, by rfl⟩ : syracuseStep 218641 = 163981) B163981
theorem B316963 : Blo 107783 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B251441 : Blo 107783 251441 := bstep (se 2 (by rfl) ⟨94290, by rfl⟩ : syracuseStep 251441 = 188581) B188581
theorem B251459 : Blo 107783 251459 := bstep (se 1 (by rfl) ⟨188594, by rfl⟩ : syracuseStep 251459 = 377189) B377189
theorem B185969 : Blo 107783 185969 := bstep (se 2 (by rfl) ⟨69738, by rfl⟩ : syracuseStep 185969 = 139477) B139477
theorem B317105 : Blo 107783 317105 := bstep (se 2 (by rfl) ⟨118914, by rfl⟩ : syracuseStep 317105 = 237829) B237829
theorem B186097 : Blo 107783 186097 := bstep (se 2 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 186097 = 139573) B139573
theorem B186131 : Blo 107783 186131 := bstep (se 1 (by rfl) ⟨139598, by rfl⟩ : syracuseStep 186131 = 279197) B279197
theorem B317297 : Blo 107783 317297 := bstep (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) B237973
theorem B186259 : Blo 107783 186259 := bstep (se 1 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 186259 = 279389) B279389
theorem B415651 : Blo 107783 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B153523 : Blo 107783 153523 := bstep (se 1 (by rfl) ⟨115142, by rfl⟩ : syracuseStep 153523 = 230285) B230285
theorem B186401 : Blo 107783 186401 := bstep (se 2 (by rfl) ⟨69900, by rfl⟩ : syracuseStep 186401 = 139801) B139801
theorem B186529 : Blo 107783 186529 := bstep (se 2 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 186529 = 139897) B139897
theorem B186563 : Blo 107783 186563 := bstep (se 1 (by rfl) ⟨139922, by rfl⟩ : syracuseStep 186563 = 279845) B279845
theorem B252227 : Blo 107783 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B186691 : Blo 107783 186691 := bstep (se 1 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 186691 = 280037) B280037
theorem B547235 : Blo 107783 547235 := bstep (se 1 (by rfl) ⟨410426, by rfl⟩ : syracuseStep 547235 = 820853) B820853
theorem B186833 : Blo 107783 186833 := bstep (se 2 (by rfl) ⟨70062, by rfl⟩ : syracuseStep 186833 = 140125) B140125
theorem B121315 : Blo 107783 121315 := bstep (se 1 (by rfl) ⟨90986, by rfl⟩ : syracuseStep 121315 = 181973) B181973
theorem B186961 : Blo 107783 186961 := bstep (se 2 (by rfl) ⟨70110, by rfl⟩ : syracuseStep 186961 = 140221) B140221
theorem B121459 : Blo 107783 121459 := bstep (se 1 (by rfl) ⟨91094, by rfl⟩ : syracuseStep 121459 = 182189) B182189
theorem B186995 : Blo 107783 186995 := bstep (se 1 (by rfl) ⟨140246, by rfl⟩ : syracuseStep 186995 = 280493) B280493
theorem B187091 : Blo 107783 187091 := bstep (se 1 (by rfl) ⟨140318, by rfl⟩ : syracuseStep 187091 = 280637) B280637
theorem B187123 : Blo 107783 187123 := bstep (se 1 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 187123 = 280685) B280685
theorem B121603 : Blo 107783 121603 := bstep (se 1 (by rfl) ⟨91202, by rfl⟩ : syracuseStep 121603 = 182405) B182405
theorem B187201 : Blo 107783 187201 := bstep (se 2 (by rfl) ⟨70200, by rfl⟩ : syracuseStep 187201 = 140401) B140401
theorem B318289 : Blo 107783 318289 := bstep (se 2 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 318289 = 238717) B238717
theorem B187265 : Blo 107783 187265 := bstep (se 2 (by rfl) ⟨70224, by rfl⟩ : syracuseStep 187265 = 140449) B140449
theorem B121747 : Blo 107783 121747 := bstep (se 1 (by rfl) ⟨91310, by rfl⟩ : syracuseStep 121747 = 182621) B182621
theorem B842723 : Blo 107783 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B711665 : Blo 107783 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B187393 : Blo 107783 187393 := bstep (se 2 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 187393 = 140545) B140545
theorem B121891 : Blo 107783 121891 := bstep (se 1 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 121891 = 182837) B182837
theorem B187427 : Blo 107783 187427 := bstep (se 1 (by rfl) ⟨140570, by rfl⟩ : syracuseStep 187427 = 281141) B281141
theorem B351373 : Blo 107783 351373 := bstep (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) B131765
theorem B187555 : Blo 107783 187555 := bstep (se 1 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 187555 = 281333) B281333
theorem B122035 : Blo 107783 122035 := bstep (se 1 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 122035 = 183053) B183053
theorem B2579653 : Blo 107783 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B548045 : Blo 107783 548045 := bstep (se 3 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 548045 = 205517) B205517
theorem B154867 : Blo 107783 154867 := bstep (se 1 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 154867 = 232301) B232301
theorem B1072397 : Blo 107783 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B187697 : Blo 107783 187697 := bstep (se 2 (by rfl) ⟨70386, by rfl⟩ : syracuseStep 187697 = 140773) B140773
theorem B122179 : Blo 107783 122179 := bstep (se 1 (by rfl) ⟨91634, by rfl⟩ : syracuseStep 122179 = 183269) B183269
theorem B351629 : Blo 107783 351629 := bstep (se 3 (by rfl) ⟨65930, by rfl⟩ : syracuseStep 351629 = 131861) B131861
theorem B187825 : Blo 107783 187825 := bstep (se 2 (by rfl) ⟨70434, by rfl⟩ : syracuseStep 187825 = 140869) B140869
theorem B122323 : Blo 107783 122323 := bstep (se 1 (by rfl) ⟨91742, by rfl⟩ : syracuseStep 122323 = 183485) B183485
theorem B187859 : Blo 107783 187859 := bstep (se 1 (by rfl) ⟨140894, by rfl⟩ : syracuseStep 187859 = 281789) B281789
theorem B187987 : Blo 107783 187987 := bstep (se 1 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 187987 = 281981) B281981
theorem B122467 : Blo 107783 122467 := bstep (se 1 (by rfl) ⟨91850, by rfl⟩ : syracuseStep 122467 = 183701) B183701
theorem B188129 : Blo 107783 188129 := bstep (se 2 (by rfl) ⟨70548, by rfl⟩ : syracuseStep 188129 = 141097) B141097
theorem B122611 : Blo 107783 122611 := bstep (se 1 (by rfl) ⟨91958, by rfl⟩ : syracuseStep 122611 = 183917) B183917
theorem B188257 : Blo 107783 188257 := bstep (se 2 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 188257 = 141193) B141193
theorem B122755 : Blo 107783 122755 := bstep (se 1 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 122755 = 184133) B184133
theorem B188291 : Blo 107783 188291 := bstep (se 1 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 188291 = 282437) B282437
theorem B1400773 : Blo 107783 1400773 := bstep (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) B262645
theorem B188419 : Blo 107783 188419 := bstep (se 1 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 188419 = 282629) B282629
theorem B122899 : Blo 107783 122899 := bstep (se 1 (by rfl) ⟨92174, by rfl⟩ : syracuseStep 122899 = 184349) B184349
theorem B417869 : Blo 107783 417869 := bstep (se 3 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 417869 = 156701) B156701
theorem B188561 : Blo 107783 188561 := bstep (se 2 (by rfl) ⟨70710, by rfl⟩ : syracuseStep 188561 = 141421) B141421
theorem B123043 : Blo 107783 123043 := bstep (se 1 (by rfl) ⟨92282, by rfl⟩ : syracuseStep 123043 = 184565) B184565
theorem B778481 : Blo 107783 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B123187 : Blo 107783 123187 := bstep (se 1 (by rfl) ⟨92390, by rfl⟩ : syracuseStep 123187 = 184781) B184781
theorem B156001 : Blo 107783 156001 := bstep (se 2 (by rfl) ⟨58500, by rfl⟩ : syracuseStep 156001 = 117001) B117001
theorem B483725 : Blo 107783 483725 := bstep (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) B181397
theorem B156097 : Blo 107783 156097 := bstep (se 2 (by rfl) ⟨58536, by rfl⟩ : syracuseStep 156097 = 117073) B117073
theorem B123331 : Blo 107783 123331 := bstep (se 1 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 123331 = 184997) B184997
theorem B123475 : Blo 107783 123475 := bstep (se 1 (by rfl) ⟨92606, by rfl⟩ : syracuseStep 123475 = 185213) B185213
theorem B713357 : Blo 107783 713357 := bstep (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) B267509
theorem B123619 : Blo 107783 123619 := bstep (se 1 (by rfl) ⟨92714, by rfl⟩ : syracuseStep 123619 = 185429) B185429
theorem B123763 : Blo 107783 123763 := bstep (se 1 (by rfl) ⟨92822, by rfl⟩ : syracuseStep 123763 = 185645) B185645
theorem B353155 : Blo 107783 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B156593 : Blo 107783 156593 := bstep (se 2 (by rfl) ⟨58722, by rfl⟩ : syracuseStep 156593 = 117445) B117445
theorem B353261 : Blo 107783 353261 := bstep (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) B132473
theorem B123907 : Blo 107783 123907 := bstep (se 1 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 123907 = 185861) B185861
theorem B615437 : Blo 107783 615437 := bstep (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) B230789
theorem B124051 : Blo 107783 124051 := bstep (se 1 (by rfl) ⟨93038, by rfl⟩ : syracuseStep 124051 = 186077) B186077
theorem B124195 : Blo 107783 124195 := bstep (se 1 (by rfl) ⟨93146, by rfl⟩ : syracuseStep 124195 = 186293) B186293
theorem B124339 : Blo 107783 124339 := bstep (se 1 (by rfl) ⟨93254, by rfl⟩ : syracuseStep 124339 = 186509) B186509
theorem B1893941 : Blo 107783 1893941 := bstep (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) B177557
theorem B124483 : Blo 107783 124483 := bstep (se 1 (by rfl) ⟨93362, by rfl⟩ : syracuseStep 124483 = 186725) B186725
theorem B353987 : Blo 107783 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B124627 : Blo 107783 124627 := bstep (se 1 (by rfl) ⟨93470, by rfl⟩ : syracuseStep 124627 = 186941) B186941
theorem B157459 : Blo 107783 157459 := bstep (se 1 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 157459 = 236189) B236189
theorem B452429 : Blo 107783 452429 := bstep (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) B169661
theorem B124771 : Blo 107783 124771 := bstep (se 1 (by rfl) ⟨93578, by rfl⟩ : syracuseStep 124771 = 187157) B187157
theorem B157555 : Blo 107783 157555 := bstep (se 1 (by rfl) ⟨118166, by rfl⟩ : syracuseStep 157555 = 236333) B236333
theorem B616369 : Blo 107783 616369 := bstep (se 2 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 616369 = 462277) B462277
theorem B124915 : Blo 107783 124915 := bstep (se 1 (by rfl) ⟨93686, by rfl⟩ : syracuseStep 124915 = 187373) B187373
theorem B550961 : Blo 107783 550961 := bstep (se 2 (by rfl) ⟨206610, by rfl⟩ : syracuseStep 550961 = 413221) B413221
theorem B354385 : Blo 107783 354385 := bstep (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) B265789
theorem B125059 : Blo 107783 125059 := bstep (se 1 (by rfl) ⟨93794, by rfl⟩ : syracuseStep 125059 = 187589) B187589
theorem B354449 : Blo 107783 354449 := bstep (se 2 (by rfl) ⟨132918, by rfl⟩ : syracuseStep 354449 = 265837) B265837
theorem B125203 : Blo 107783 125203 := bstep (se 1 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 125203 = 187805) B187805
theorem B190769 : Blo 107783 190769 := bstep (se 2 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 190769 = 143077) B143077
theorem B158051 : Blo 107783 158051 := bstep (se 1 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 158051 = 237077) B237077
theorem B223651 : Blo 107783 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B125347 : Blo 107783 125347 := bstep (se 1 (by rfl) ⟨94010, by rfl⟩ : syracuseStep 125347 = 188021) B188021
theorem B682481 : Blo 107783 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B125491 : Blo 107783 125491 := bstep (se 1 (by rfl) ⟨94118, by rfl⟩ : syracuseStep 125491 = 188237) B188237
theorem B289379 : Blo 107783 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B125635 : Blo 107783 125635 := bstep (se 1 (by rfl) ⟨94226, by rfl⟩ : syracuseStep 125635 = 188453) B188453
theorem B420785 : Blo 107783 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B158689 : Blo 107783 158689 := bstep (se 2 (by rfl) ⟨59508, by rfl⟩ : syracuseStep 158689 = 119017) B119017
theorem B519139 : Blo 107783 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B191489 : Blo 107783 191489 := bstep (se 2 (by rfl) ⟨71808, by rfl⟩ : syracuseStep 191489 = 143617) B143617
theorem B159025 : Blo 107783 159025 := bstep (se 2 (by rfl) ⟨59634, by rfl⟩ : syracuseStep 159025 = 119269) B119269
theorem B617827 : Blo 107783 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B224689 : Blo 107783 224689 := bstep (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) B168517
theorem B552419 : Blo 107783 552419 := bstep (se 1 (by rfl) ⟨414314, by rfl⟩ : syracuseStep 552419 = 828629) B828629
theorem B650915 : Blo 107783 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B1240757 : Blo 107783 1240757 := bstep (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) B116321
theorem B618353 : Blo 107783 618353 := bstep (se 2 (by rfl) ⟨231882, by rfl⟩ : syracuseStep 618353 = 463765) B463765
theorem B1601477 : Blo 107783 1601477 := bstep (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) B300277
theorem B520141 : Blo 107783 520141 := bstep (se 3 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 520141 = 195053) B195053
theorem B749573 : Blo 107783 749573 := bstep (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) B140545
theorem B848069 : Blo 107783 848069 := bstep (se 4 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 848069 = 159013) B159013
theorem B553229 : Blo 107783 553229 := bstep (se 3 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 553229 = 207461) B207461
theorem B422243 : Blo 107783 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B389731 : Blo 107783 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B160481 : Blo 107783 160481 := bstep (se 2 (by rfl) ⟨60180, by rfl⟩ : syracuseStep 160481 = 120361) B120361
theorem B226019 : Blo 107783 226019 := bstep (se 1 (by rfl) ⟨169514, by rfl⟩ : syracuseStep 226019 = 339029) B339029
theorem B291757 : Blo 107783 291757 := bstep (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) B109409
theorem B947213 : Blo 107783 947213 := bstep (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) B355205
theorem B390221 : Blo 107783 390221 := bstep (se 3 (by rfl) ⟨73166, by rfl⟩ : syracuseStep 390221 = 146333) B146333
theorem B619811 : Blo 107783 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B423245 : Blo 107783 423245 := bstep (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) B158717
theorem B521585 : Blo 107783 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B259793 : Blo 107783 259793 := bstep (se 2 (by rfl) ⟨97422, by rfl⟩ : syracuseStep 259793 = 194845) B194845
theorem B718733 : Blo 107783 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B161681 : Blo 107783 161681 := bstep (se 2 (by rfl) ⟨60630, by rfl⟩ : syracuseStep 161681 = 121261) B121261
theorem B161699 : Blo 107783 161699 := bstep (se 1 (by rfl) ⟨121274, by rfl⟩ : syracuseStep 161699 = 242549) B242549
theorem B161729 : Blo 107783 161729 := bstep (se 2 (by rfl) ⟨60648, by rfl⟩ : syracuseStep 161729 = 121297) B121297
theorem B161747 : Blo 107783 161747 := bstep (se 1 (by rfl) ⟨121310, by rfl⟩ : syracuseStep 161747 = 242621) B242621
theorem B161777 : Blo 107783 161777 := bstep (se 2 (by rfl) ⟨60666, by rfl⟩ : syracuseStep 161777 = 121333) B121333
theorem B161795 : Blo 107783 161795 := bstep (se 1 (by rfl) ⟨121346, by rfl⟩ : syracuseStep 161795 = 242693) B242693
theorem B161825 : Blo 107783 161825 := bstep (se 2 (by rfl) ⟨60684, by rfl⟩ : syracuseStep 161825 = 121369) B121369
theorem B161843 : Blo 107783 161843 := bstep (se 1 (by rfl) ⟨121382, by rfl⟩ : syracuseStep 161843 = 242765) B242765
theorem B161873 : Blo 107783 161873 := bstep (se 2 (by rfl) ⟨60702, by rfl⟩ : syracuseStep 161873 = 121405) B121405
theorem B161891 : Blo 107783 161891 := bstep (se 1 (by rfl) ⟨121418, by rfl⟩ : syracuseStep 161891 = 242837) B242837
theorem B161921 : Blo 107783 161921 := bstep (se 2 (by rfl) ⟨60720, by rfl⟩ : syracuseStep 161921 = 121441) B121441
theorem B161939 : Blo 107783 161939 := bstep (se 1 (by rfl) ⟨121454, by rfl⟩ : syracuseStep 161939 = 242909) B242909
theorem B161969 : Blo 107783 161969 := bstep (se 2 (by rfl) ⟨60738, by rfl⟩ : syracuseStep 161969 = 121477) B121477
theorem B161987 : Blo 107783 161987 := bstep (se 1 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 161987 = 242981) B242981
theorem B162017 : Blo 107783 162017 := bstep (se 2 (by rfl) ⟨60756, by rfl⟩ : syracuseStep 162017 = 121513) B121513
theorem B162035 : Blo 107783 162035 := bstep (se 1 (by rfl) ⟨121526, by rfl⟩ : syracuseStep 162035 = 243053) B243053
theorem B162065 : Blo 107783 162065 := bstep (se 2 (by rfl) ⟨60774, by rfl⟩ : syracuseStep 162065 = 121549) B121549
theorem B162083 : Blo 107783 162083 := bstep (se 1 (by rfl) ⟨121562, by rfl⟩ : syracuseStep 162083 = 243125) B243125
theorem B293165 : Blo 107783 293165 := bstep (se 3 (by rfl) ⟨54968, by rfl⟩ : syracuseStep 293165 = 109937) B109937
theorem B162113 : Blo 107783 162113 := bstep (se 2 (by rfl) ⟨60792, by rfl⟩ : syracuseStep 162113 = 121585) B121585
theorem B162131 : Blo 107783 162131 := bstep (se 1 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 162131 = 243197) B243197
theorem B162161 : Blo 107783 162161 := bstep (se 2 (by rfl) ⟨60810, by rfl⟩ : syracuseStep 162161 = 121621) B121621
theorem B162179 : Blo 107783 162179 := bstep (se 1 (by rfl) ⟨121634, by rfl⟩ : syracuseStep 162179 = 243269) B243269
theorem B162209 : Blo 107783 162209 := bstep (se 2 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 162209 = 121657) B121657
theorem B162227 : Blo 107783 162227 := bstep (se 1 (by rfl) ⟨121670, by rfl⟩ : syracuseStep 162227 = 243341) B243341
theorem B162257 : Blo 107783 162257 := bstep (se 2 (by rfl) ⟨60846, by rfl⟩ : syracuseStep 162257 = 121693) B121693
theorem B162275 : Blo 107783 162275 := bstep (se 1 (by rfl) ⟨121706, by rfl⟩ : syracuseStep 162275 = 243413) B243413
theorem B162305 : Blo 107783 162305 := bstep (se 2 (by rfl) ⟨60864, by rfl⟩ : syracuseStep 162305 = 121729) B121729
theorem B752141 : Blo 107783 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B162323 : Blo 107783 162323 := bstep (se 1 (by rfl) ⟨121742, by rfl⟩ : syracuseStep 162323 = 243485) B243485
theorem B162353 : Blo 107783 162353 := bstep (se 2 (by rfl) ⟨60882, by rfl⟩ : syracuseStep 162353 = 121765) B121765
theorem B162371 : Blo 107783 162371 := bstep (se 1 (by rfl) ⟨121778, by rfl⟩ : syracuseStep 162371 = 243557) B243557
theorem B162401 : Blo 107783 162401 := bstep (se 2 (by rfl) ⟨60900, by rfl⟩ : syracuseStep 162401 = 121801) B121801
theorem B162419 : Blo 107783 162419 := bstep (se 1 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 162419 = 243629) B243629
theorem B162449 : Blo 107783 162449 := bstep (se 2 (by rfl) ⟨60918, by rfl⟩ : syracuseStep 162449 = 121837) B121837
theorem B162467 : Blo 107783 162467 := bstep (se 1 (by rfl) ⟨121850, by rfl⟩ : syracuseStep 162467 = 243701) B243701
theorem B162497 : Blo 107783 162497 := bstep (se 2 (by rfl) ⟨60936, by rfl⟩ : syracuseStep 162497 = 121873) B121873
theorem B162515 : Blo 107783 162515 := bstep (se 1 (by rfl) ⟨121886, by rfl⟩ : syracuseStep 162515 = 243773) B243773
theorem B162545 : Blo 107783 162545 := bstep (se 2 (by rfl) ⟨60954, by rfl⟩ : syracuseStep 162545 = 121909) B121909
theorem B162563 : Blo 107783 162563 := bstep (se 1 (by rfl) ⟨121922, by rfl⟩ : syracuseStep 162563 = 243845) B243845
theorem B162593 : Blo 107783 162593 := bstep (se 2 (by rfl) ⟨60972, by rfl⟩ : syracuseStep 162593 = 121945) B121945
theorem B162611 : Blo 107783 162611 := bstep (se 1 (by rfl) ⟨121958, by rfl⟩ : syracuseStep 162611 = 243917) B243917
theorem B162641 : Blo 107783 162641 := bstep (se 2 (by rfl) ⟨60990, by rfl⟩ : syracuseStep 162641 = 121981) B121981
theorem B162659 : Blo 107783 162659 := bstep (se 1 (by rfl) ⟨121994, by rfl⟩ : syracuseStep 162659 = 243989) B243989
theorem B162689 : Blo 107783 162689 := bstep (se 2 (by rfl) ⟨61008, by rfl⟩ : syracuseStep 162689 = 122017) B122017
theorem B162707 : Blo 107783 162707 := bstep (se 1 (by rfl) ⟨122030, by rfl⟩ : syracuseStep 162707 = 244061) B244061
theorem B162737 : Blo 107783 162737 := bstep (se 2 (by rfl) ⟨61026, by rfl⟩ : syracuseStep 162737 = 122053) B122053
theorem B162755 : Blo 107783 162755 := bstep (se 1 (by rfl) ⟨122066, by rfl⟩ : syracuseStep 162755 = 244133) B244133
theorem B162785 : Blo 107783 162785 := bstep (se 2 (by rfl) ⟨61044, by rfl⟩ : syracuseStep 162785 = 122089) B122089
theorem B162803 : Blo 107783 162803 := bstep (se 1 (by rfl) ⟨122102, by rfl⟩ : syracuseStep 162803 = 244205) B244205
theorem B162833 : Blo 107783 162833 := bstep (se 2 (by rfl) ⟨61062, by rfl⟩ : syracuseStep 162833 = 122125) B122125
theorem B162851 : Blo 107783 162851 := bstep (se 1 (by rfl) ⟨122138, by rfl⟩ : syracuseStep 162851 = 244277) B244277
theorem B162881 : Blo 107783 162881 := bstep (se 2 (by rfl) ⟨61080, by rfl⟩ : syracuseStep 162881 = 122161) B122161
theorem B162899 : Blo 107783 162899 := bstep (se 1 (by rfl) ⟨122174, by rfl⟩ : syracuseStep 162899 = 244349) B244349
theorem B162929 : Blo 107783 162929 := bstep (se 2 (by rfl) ⟨61098, by rfl⟩ : syracuseStep 162929 = 122197) B122197
theorem B556145 : Blo 107783 556145 := bstep (se 2 (by rfl) ⟨208554, by rfl⟩ : syracuseStep 556145 = 417109) B417109
theorem B162947 : Blo 107783 162947 := bstep (se 1 (by rfl) ⟨122210, by rfl⟩ : syracuseStep 162947 = 244421) B244421
theorem B621701 : Blo 107783 621701 := bstep (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) B116569
theorem B162977 : Blo 107783 162977 := bstep (se 2 (by rfl) ⟨61116, by rfl⟩ : syracuseStep 162977 = 122233) B122233
theorem B162995 : Blo 107783 162995 := bstep (se 1 (by rfl) ⟨122246, by rfl⟩ : syracuseStep 162995 = 244493) B244493
theorem B163025 : Blo 107783 163025 := bstep (se 2 (by rfl) ⟨61134, by rfl⟩ : syracuseStep 163025 = 122269) B122269
theorem B163043 : Blo 107783 163043 := bstep (se 1 (by rfl) ⟨122282, by rfl⟩ : syracuseStep 163043 = 244565) B244565
theorem B163073 : Blo 107783 163073 := bstep (se 2 (by rfl) ⟨61152, by rfl⟩ : syracuseStep 163073 = 122305) B122305
theorem B163091 : Blo 107783 163091 := bstep (se 1 (by rfl) ⟨122318, by rfl⟩ : syracuseStep 163091 = 244637) B244637
theorem B163121 : Blo 107783 163121 := bstep (se 2 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 163121 = 122341) B122341
theorem B163139 : Blo 107783 163139 := bstep (se 1 (by rfl) ⟨122354, by rfl⟩ : syracuseStep 163139 = 244709) B244709
theorem B163169 : Blo 107783 163169 := bstep (se 2 (by rfl) ⟨61188, by rfl⟩ : syracuseStep 163169 = 122377) B122377
theorem B163187 : Blo 107783 163187 := bstep (se 1 (by rfl) ⟨122390, by rfl⟩ : syracuseStep 163187 = 244781) B244781
theorem B163217 : Blo 107783 163217 := bstep (se 2 (by rfl) ⟨61206, by rfl⟩ : syracuseStep 163217 = 122413) B122413
theorem B163235 : Blo 107783 163235 := bstep (se 1 (by rfl) ⟨122426, by rfl⟩ : syracuseStep 163235 = 244853) B244853
theorem B163265 : Blo 107783 163265 := bstep (se 2 (by rfl) ⟨61224, by rfl⟩ : syracuseStep 163265 = 122449) B122449
theorem B163283 : Blo 107783 163283 := bstep (se 1 (by rfl) ⟨122462, by rfl⟩ : syracuseStep 163283 = 244925) B244925
theorem B163313 : Blo 107783 163313 := bstep (se 2 (by rfl) ⟨61242, by rfl⟩ : syracuseStep 163313 = 122485) B122485
theorem B163331 : Blo 107783 163331 := bstep (se 1 (by rfl) ⟨122498, by rfl⟩ : syracuseStep 163331 = 244997) B244997
theorem B163361 : Blo 107783 163361 := bstep (se 2 (by rfl) ⟨61260, by rfl⟩ : syracuseStep 163361 = 122521) B122521
theorem B163379 : Blo 107783 163379 := bstep (se 1 (by rfl) ⟨122534, by rfl⟩ : syracuseStep 163379 = 245069) B245069
theorem B196177 : Blo 107783 196177 := bstep (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) B147133
theorem B163409 : Blo 107783 163409 := bstep (se 2 (by rfl) ⟨61278, by rfl⟩ : syracuseStep 163409 = 122557) B122557
theorem B163427 : Blo 107783 163427 := bstep (se 1 (by rfl) ⟨122570, by rfl⟩ : syracuseStep 163427 = 245141) B245141
theorem B163457 : Blo 107783 163457 := bstep (se 2 (by rfl) ⟨61296, by rfl⟩ : syracuseStep 163457 = 122593) B122593
theorem B163475 : Blo 107783 163475 := bstep (se 1 (by rfl) ⟨122606, by rfl⟩ : syracuseStep 163475 = 245213) B245213
theorem B163505 : Blo 107783 163505 := bstep (se 2 (by rfl) ⟨61314, by rfl⟩ : syracuseStep 163505 = 122629) B122629
theorem B163523 : Blo 107783 163523 := bstep (se 1 (by rfl) ⟨122642, by rfl⟩ : syracuseStep 163523 = 245285) B245285
theorem B163553 : Blo 107783 163553 := bstep (se 2 (by rfl) ⟨61332, by rfl⟩ : syracuseStep 163553 = 122665) B122665
theorem B163571 : Blo 107783 163571 := bstep (se 1 (by rfl) ⟨122678, by rfl⟩ : syracuseStep 163571 = 245357) B245357
theorem B163601 : Blo 107783 163601 := bstep (se 2 (by rfl) ⟨61350, by rfl⟩ : syracuseStep 163601 = 122701) B122701
theorem B163619 : Blo 107783 163619 := bstep (se 1 (by rfl) ⟨122714, by rfl⟩ : syracuseStep 163619 = 245429) B245429
theorem B163649 : Blo 107783 163649 := bstep (se 2 (by rfl) ⟨61368, by rfl⟩ : syracuseStep 163649 = 122737) B122737
theorem B163667 : Blo 107783 163667 := bstep (se 1 (by rfl) ⟨122750, by rfl⟩ : syracuseStep 163667 = 245501) B245501
theorem B163697 : Blo 107783 163697 := bstep (se 2 (by rfl) ⟨61386, by rfl⟩ : syracuseStep 163697 = 122773) B122773
theorem B163715 : Blo 107783 163715 := bstep (se 1 (by rfl) ⟨122786, by rfl⟩ : syracuseStep 163715 = 245573) B245573
theorem B163745 : Blo 107783 163745 := bstep (se 2 (by rfl) ⟨61404, by rfl⟩ : syracuseStep 163745 = 122809) B122809
theorem B163763 : Blo 107783 163763 := bstep (se 1 (by rfl) ⟨122822, by rfl⟩ : syracuseStep 163763 = 245645) B245645
theorem B163793 : Blo 107783 163793 := bstep (se 2 (by rfl) ⟨61422, by rfl⟩ : syracuseStep 163793 = 122845) B122845
theorem B163811 : Blo 107783 163811 := bstep (se 1 (by rfl) ⟨122858, by rfl⟩ : syracuseStep 163811 = 245717) B245717
theorem B163865 : Blo 107783 163865 := bstep (se 2 (by rfl) ⟨61449, by rfl⟩ : syracuseStep 163865 = 122899) B122899
theorem B163979 : Blo 107783 163979 := bstep (se 1 (by rfl) ⟨122984, by rfl⟩ : syracuseStep 163979 = 245969) B245969
theorem B163991 : Blo 107783 163991 := bstep (se 1 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 163991 = 245987) B245987
theorem B164057 : Blo 107783 164057 := bstep (se 2 (by rfl) ⟨61521, by rfl⟩ : syracuseStep 164057 = 123043) B123043
theorem B164171 : Blo 107783 164171 := bstep (se 1 (by rfl) ⟨123128, by rfl⟩ : syracuseStep 164171 = 246257) B246257
theorem B164183 : Blo 107783 164183 := bstep (se 1 (by rfl) ⟨123137, by rfl⟩ : syracuseStep 164183 = 246275) B246275
theorem B524675 : Blo 107783 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B393623 : Blo 107783 393623 := bstep (se 1 (by rfl) ⟨295217, by rfl⟩ : syracuseStep 393623 = 590435) B590435
theorem B164249 : Blo 107783 164249 := bstep (se 2 (by rfl) ⟨61593, by rfl⟩ : syracuseStep 164249 = 123187) B123187
theorem B164363 : Blo 107783 164363 := bstep (se 1 (by rfl) ⟨123272, by rfl⟩ : syracuseStep 164363 = 246545) B246545
theorem B164375 : Blo 107783 164375 := bstep (se 1 (by rfl) ⟨123281, by rfl⟩ : syracuseStep 164375 = 246563) B246563
theorem B164441 : Blo 107783 164441 := bstep (se 2 (by rfl) ⟨61665, by rfl⟩ : syracuseStep 164441 = 123331) B123331
theorem B164555 : Blo 107783 164555 := bstep (se 1 (by rfl) ⟨123416, by rfl⟩ : syracuseStep 164555 = 246833) B246833
theorem B164567 : Blo 107783 164567 := bstep (se 1 (by rfl) ⟨123425, by rfl⟩ : syracuseStep 164567 = 246851) B246851
theorem B164633 : Blo 107783 164633 := bstep (se 2 (by rfl) ⟨61737, by rfl⟩ : syracuseStep 164633 = 123475) B123475
theorem B164747 : Blo 107783 164747 := bstep (se 1 (by rfl) ⟨123560, by rfl⟩ : syracuseStep 164747 = 247121) B247121
theorem B164759 : Blo 107783 164759 := bstep (se 1 (by rfl) ⟨123569, by rfl⟩ : syracuseStep 164759 = 247139) B247139
theorem B164825 : Blo 107783 164825 := bstep (se 2 (by rfl) ⟨61809, by rfl⟩ : syracuseStep 164825 = 123619) B123619
theorem B1016867 : Blo 107783 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B164939 : Blo 107783 164939 := bstep (se 1 (by rfl) ⟨123704, by rfl⟩ : syracuseStep 164939 = 247409) B247409
theorem B164951 : Blo 107783 164951 := bstep (se 1 (by rfl) ⟨123713, by rfl⟩ : syracuseStep 164951 = 247427) B247427
theorem B165017 : Blo 107783 165017 := bstep (se 2 (by rfl) ⟨61881, by rfl⟩ : syracuseStep 165017 = 123763) B123763
theorem B394433 : Blo 107783 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B1672433 : Blo 107783 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B165131 : Blo 107783 165131 := bstep (se 1 (by rfl) ⟨123848, by rfl⟩ : syracuseStep 165131 = 247697) B247697
theorem B165143 : Blo 107783 165143 := bstep (se 1 (by rfl) ⟨123857, by rfl⟩ : syracuseStep 165143 = 247715) B247715
theorem B951587 : Blo 107783 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B165209 : Blo 107783 165209 := bstep (se 2 (by rfl) ⟨61953, by rfl⟩ : syracuseStep 165209 = 123907) B123907
theorem B165323 : Blo 107783 165323 := bstep (se 1 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 165323 = 247985) B247985
theorem B165335 : Blo 107783 165335 := bstep (se 1 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 165335 = 248003) B248003
theorem B165401 : Blo 107783 165401 := bstep (se 2 (by rfl) ⟨62025, by rfl⟩ : syracuseStep 165401 = 124051) B124051
theorem B886403 : Blo 107783 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B198283 : Blo 107783 198283 := bstep (se 1 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 198283 = 297425) B297425
theorem B165515 : Blo 107783 165515 := bstep (se 1 (by rfl) ⟨124136, by rfl⟩ : syracuseStep 165515 = 248273) B248273
theorem B165527 : Blo 107783 165527 := bstep (se 1 (by rfl) ⟨124145, by rfl⟩ : syracuseStep 165527 = 248291) B248291
theorem B165593 : Blo 107783 165593 := bstep (se 2 (by rfl) ⟨62097, by rfl⟩ : syracuseStep 165593 = 124195) B124195
theorem B165707 : Blo 107783 165707 := bstep (se 1 (by rfl) ⟨124280, by rfl⟩ : syracuseStep 165707 = 248561) B248561
theorem B165719 : Blo 107783 165719 := bstep (se 1 (by rfl) ⟨124289, by rfl⟩ : syracuseStep 165719 = 248579) B248579
theorem B460637 : Blo 107783 460637 := bstep (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) B172739
theorem B296797 : Blo 107783 296797 := bstep (se 3 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 296797 = 111299) B111299
theorem B165785 : Blo 107783 165785 := bstep (se 2 (by rfl) ⟨62169, by rfl⟩ : syracuseStep 165785 = 124339) B124339
theorem B427949 : Blo 107783 427949 := bstep (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) B160481
theorem B395225 : Blo 107783 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B165899 : Blo 107783 165899 := bstep (se 1 (by rfl) ⟨124424, by rfl⟩ : syracuseStep 165899 = 248849) B248849
theorem B165911 : Blo 107783 165911 := bstep (se 1 (by rfl) ⟨124433, by rfl⟩ : syracuseStep 165911 = 248867) B248867
theorem B165977 : Blo 107783 165977 := bstep (se 2 (by rfl) ⟨62241, by rfl⟩ : syracuseStep 165977 = 124483) B124483
theorem B231617 : Blo 107783 231617 := bstep (se 2 (by rfl) ⟨86856, by rfl⟩ : syracuseStep 231617 = 173713) B173713
theorem B166091 : Blo 107783 166091 := bstep (se 1 (by rfl) ⟨124568, by rfl⟩ : syracuseStep 166091 = 249137) B249137
theorem B166103 : Blo 107783 166103 := bstep (se 1 (by rfl) ⟨124577, by rfl⟩ : syracuseStep 166103 = 249155) B249155
theorem B166169 : Blo 107783 166169 := bstep (se 2 (by rfl) ⟨62313, by rfl⟩ : syracuseStep 166169 = 124627) B124627
theorem B526657 : Blo 107783 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B3869045 : Blo 107783 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B166283 : Blo 107783 166283 := bstep (se 1 (by rfl) ⟨124712, by rfl⟩ : syracuseStep 166283 = 249425) B249425
theorem B166295 : Blo 107783 166295 := bstep (se 1 (by rfl) ⟨124721, by rfl⟩ : syracuseStep 166295 = 249443) B249443
theorem B166361 : Blo 107783 166361 := bstep (se 2 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 166361 = 124771) B124771
theorem B231959 : Blo 107783 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B821825 : Blo 107783 821825 := bstep (se 2 (by rfl) ⟨308184, by rfl⟩ : syracuseStep 821825 = 616369) B616369
theorem B166475 : Blo 107783 166475 := bstep (se 1 (by rfl) ⟨124856, by rfl⟩ : syracuseStep 166475 = 249713) B249713
theorem B166487 : Blo 107783 166487 := bstep (se 1 (by rfl) ⟨124865, by rfl⟩ : syracuseStep 166487 = 249731) B249731
theorem B559709 : Blo 107783 559709 := bstep (se 3 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 559709 = 209891) B209891
theorem B166553 : Blo 107783 166553 := bstep (se 2 (by rfl) ⟨62457, by rfl⟩ : syracuseStep 166553 = 124915) B124915
theorem B166667 : Blo 107783 166667 := bstep (se 1 (by rfl) ⟨125000, by rfl⟩ : syracuseStep 166667 = 250001) B250001
theorem B166679 : Blo 107783 166679 := bstep (se 1 (by rfl) ⟨125009, by rfl⟩ : syracuseStep 166679 = 250019) B250019
theorem B232267 : Blo 107783 232267 := bstep (se 1 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 232267 = 348401) B348401
theorem B265049 : Blo 107783 265049 := bstep (se 2 (by rfl) ⟨99393, by rfl⟩ : syracuseStep 265049 = 198787) B198787
theorem B166745 : Blo 107783 166745 := bstep (se 2 (by rfl) ⟨62529, by rfl⟩ : syracuseStep 166745 = 125059) B125059
theorem B166859 : Blo 107783 166859 := bstep (se 1 (by rfl) ⟨125144, by rfl⟩ : syracuseStep 166859 = 250289) B250289
theorem B166871 : Blo 107783 166871 := bstep (se 1 (by rfl) ⟨125153, by rfl⟩ : syracuseStep 166871 = 250307) B250307
theorem B199667 : Blo 107783 199667 := bstep (se 1 (by rfl) ⟨149750, by rfl⟩ : syracuseStep 199667 = 299501) B299501
theorem B166937 : Blo 107783 166937 := bstep (se 2 (by rfl) ⟨62601, by rfl⟩ : syracuseStep 166937 = 125203) B125203
theorem B2001995 : Blo 107783 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B167051 : Blo 107783 167051 := bstep (se 1 (by rfl) ⟨125288, by rfl⟩ : syracuseStep 167051 = 250577) B250577
theorem B167063 : Blo 107783 167063 := bstep (se 1 (by rfl) ⟨125297, by rfl⟩ : syracuseStep 167063 = 250595) B250595
theorem B199883 : Blo 107783 199883 := bstep (se 1 (by rfl) ⟨149912, by rfl⟩ : syracuseStep 199883 = 299825) B299825
theorem B396505 : Blo 107783 396505 := bstep (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) B297379
theorem B167129 : Blo 107783 167129 := bstep (se 2 (by rfl) ⟨62673, by rfl⟩ : syracuseStep 167129 = 125347) B125347
theorem B462125 : Blo 107783 462125 := bstep (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) B173297
theorem B363851 : Blo 107783 363851 := bstep (se 1 (by rfl) ⟨272888, by rfl⟩ : syracuseStep 363851 = 545777) B545777
theorem B167243 : Blo 107783 167243 := bstep (se 1 (by rfl) ⟨125432, by rfl⟩ : syracuseStep 167243 = 250865) B250865
theorem B167255 : Blo 107783 167255 := bstep (se 1 (by rfl) ⟨125441, by rfl⟩ : syracuseStep 167255 = 250883) B250883
theorem B167321 : Blo 107783 167321 := bstep (se 2 (by rfl) ⟨62745, by rfl⟩ : syracuseStep 167321 = 125491) B125491
theorem B167435 : Blo 107783 167435 := bstep (se 1 (by rfl) ⟨125576, by rfl⟩ : syracuseStep 167435 = 251153) B251153
theorem B167447 : Blo 107783 167447 := bstep (se 1 (by rfl) ⟨125585, by rfl⟩ : syracuseStep 167447 = 251171) B251171
theorem B364121 : Blo 107783 364121 := bstep (se 2 (by rfl) ⟨136545, by rfl⟩ : syracuseStep 364121 = 273091) B273091
theorem B167513 : Blo 107783 167513 := bstep (se 2 (by rfl) ⟨62817, by rfl⟩ : syracuseStep 167513 = 125635) B125635
theorem B233113 : Blo 107783 233113 := bstep (se 2 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 233113 = 174835) B174835
theorem B167627 : Blo 107783 167627 := bstep (se 1 (by rfl) ⟨125720, by rfl⟩ : syracuseStep 167627 = 251441) B251441
theorem B167639 : Blo 107783 167639 := bstep (se 1 (by rfl) ⟨125729, by rfl⟩ : syracuseStep 167639 = 251459) B251459
theorem B626393 : Blo 107783 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B921617 : Blo 107783 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B757777 : Blo 107783 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B528563 : Blo 107783 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B364823 : Blo 107783 364823 := bstep (se 1 (by rfl) ⟨273617, by rfl⟩ : syracuseStep 364823 = 547235) B547235
theorem B823769 : Blo 107783 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B299585 : Blo 107783 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B332363 : Blo 107783 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B561815 : Blo 107783 561815 := bstep (se 1 (by rfl) ⟨421361, by rfl⟩ : syracuseStep 561815 = 842723) B842723
theorem B365363 : Blo 107783 365363 := bstep (se 1 (by rfl) ⟨274022, by rfl⟩ : syracuseStep 365363 = 548045) B548045
theorem B234419 : Blo 107783 234419 := bstep (se 1 (by rfl) ⟨175814, by rfl⟩ : syracuseStep 234419 = 351629) B351629
theorem B365633 : Blo 107783 365633 := bstep (se 2 (by rfl) ⟨137112, by rfl⟩ : syracuseStep 365633 = 274225) B274225
theorem B595019 : Blo 107783 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B464089 : Blo 107783 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B693521 : Blo 107783 693521 := bstep (se 2 (by rfl) ⟨260070, by rfl⟩ : syracuseStep 693521 = 520141) B520141
theorem B628033 : Blo 107783 628033 := bstep (se 2 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 628033 = 471025) B471025
theorem B366173 : Blo 107783 366173 := bstep (se 3 (by rfl) ⟨68657, by rfl⟩ : syracuseStep 366173 = 137315) B137315
theorem B137047 : Blo 107783 137047 := bstep (se 1 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 137047 = 205571) B205571
theorem B366557 : Blo 107783 366557 := bstep (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) B137459
theorem B465047 : Blo 107783 465047 := bstep (se 1 (by rfl) ⟨348785, by rfl⟩ : syracuseStep 465047 = 697571) B697571
theorem B268609 : Blo 107783 268609 := bstep (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) B201457
theorem B2038193 : Blo 107783 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B235991 : Blo 107783 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B301619 : Blo 107783 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B367307 : Blo 107783 367307 := bstep (se 1 (by rfl) ⟨275480, by rfl⟩ : syracuseStep 367307 = 550961) B550961
theorem B236299 : Blo 107783 236299 := bstep (se 1 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 236299 = 354449) B354449
theorem B367577 : Blo 107783 367577 := bstep (se 2 (by rfl) ⟨137841, by rfl⟩ : syracuseStep 367577 = 275683) B275683
theorem B400601 : Blo 107783 400601 := bstep (se 2 (by rfl) ⟨150225, by rfl⟩ : syracuseStep 400601 = 300451) B300451
theorem B138763 : Blo 107783 138763 := bstep (se 1 (by rfl) ⟨104072, by rfl⟩ : syracuseStep 138763 = 208145) B208145
theorem B368279 : Blo 107783 368279 := bstep (se 1 (by rfl) ⟨276209, by rfl⟩ : syracuseStep 368279 = 552419) B552419
theorem B433943 : Blo 107783 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B827171 : Blo 107783 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B204697 : Blo 107783 204697 := bstep (se 2 (by rfl) ⟨76761, by rfl⟩ : syracuseStep 204697 = 153523) B153523
theorem B892889 : Blo 107783 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B237529 : Blo 107783 237529 := bstep (se 2 (by rfl) ⟨89073, by rfl⟩ : syracuseStep 237529 = 178147) B178147
theorem B499715 : Blo 107783 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B565379 : Blo 107783 565379 := bstep (se 1 (by rfl) ⟨424034, by rfl⟩ : syracuseStep 565379 = 848069) B848069
theorem B139415 : Blo 107783 139415 := bstep (se 1 (by rfl) ⟨104561, by rfl⟩ : syracuseStep 139415 = 209123) B209123
theorem B368819 : Blo 107783 368819 := bstep (se 1 (by rfl) ⟨276614, by rfl⟩ : syracuseStep 368819 = 553229) B553229
theorem B401611 : Blo 107783 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B598373 : Blo 107783 598373 := bstep (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) B112195
theorem B369089 : Blo 107783 369089 := bstep (se 2 (by rfl) ⟨138408, by rfl⟩ : syracuseStep 369089 = 276817) B276817
theorem B139735 : Blo 107783 139735 := bstep (se 1 (by rfl) ⟨104801, by rfl⟩ : syracuseStep 139735 = 209603) B209603
theorem B303709 : Blo 107783 303709 := bstep (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) B113891
theorem B631475 : Blo 107783 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B2859725 : Blo 107783 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B1581869 : Blo 107783 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B369629 : Blo 107783 369629 := bstep (se 3 (by rfl) ⟨69305, by rfl⟩ : syracuseStep 369629 = 138611) B138611
theorem B173195 : Blo 107783 173195 := bstep (se 1 (by rfl) ⟨129896, by rfl⟩ : syracuseStep 173195 = 259793) B259793
theorem B206003 : Blo 107783 206003 := bstep (se 1 (by rfl) ⟨154502, by rfl⟩ : syracuseStep 206003 = 309005) B309005
theorem B107787 : Blo 107783 107787 := bstep (se 1 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 107787 = 161681) B161681
theorem B140555 : Blo 107783 140555 := bstep (se 1 (by rfl) ⟨105416, by rfl⟩ : syracuseStep 140555 = 210833) B210833
theorem B107799 : Blo 107783 107799 := bstep (se 1 (by rfl) ⟨80849, by rfl⟩ : syracuseStep 107799 = 161699) B161699
theorem B107819 : Blo 107783 107819 := bstep (se 1 (by rfl) ⟨80864, by rfl⟩ : syracuseStep 107819 = 161729) B161729
theorem B402733 : Blo 107783 402733 := bstep (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) B151025
theorem B107831 : Blo 107783 107831 := bstep (se 1 (by rfl) ⟨80873, by rfl⟩ : syracuseStep 107831 = 161747) B161747
theorem B107851 : Blo 107783 107851 := bstep (se 1 (by rfl) ⟨80888, by rfl⟩ : syracuseStep 107851 = 161777) B161777
theorem B206155 : Blo 107783 206155 := bstep (se 1 (by rfl) ⟨154616, by rfl⟩ : syracuseStep 206155 = 309233) B309233
theorem B107863 : Blo 107783 107863 := bstep (se 1 (by rfl) ⟨80897, by rfl⟩ : syracuseStep 107863 = 161795) B161795
theorem B107883 : Blo 107783 107883 := bstep (se 1 (by rfl) ⟨80912, by rfl⟩ : syracuseStep 107883 = 161825) B161825
theorem B107895 : Blo 107783 107895 := bstep (se 1 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 107895 = 161843) B161843
theorem B107915 : Blo 107783 107915 := bstep (se 1 (by rfl) ⟨80936, by rfl⟩ : syracuseStep 107915 = 161873) B161873
theorem B107927 : Blo 107783 107927 := bstep (se 1 (by rfl) ⟨80945, by rfl⟩ : syracuseStep 107927 = 161891) B161891
theorem B107947 : Blo 107783 107947 := bstep (se 1 (by rfl) ⟨80960, by rfl⟩ : syracuseStep 107947 = 161921) B161921
theorem B107959 : Blo 107783 107959 := bstep (se 1 (by rfl) ⟨80969, by rfl⟩ : syracuseStep 107959 = 161939) B161939
theorem B107979 : Blo 107783 107979 := bstep (se 1 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 107979 = 161969) B161969
theorem B107991 : Blo 107783 107991 := bstep (se 1 (by rfl) ⟨80993, by rfl⟩ : syracuseStep 107991 = 161987) B161987
theorem B108011 : Blo 107783 108011 := bstep (se 1 (by rfl) ⟨81008, by rfl⟩ : syracuseStep 108011 = 162017) B162017
theorem B108023 : Blo 107783 108023 := bstep (se 1 (by rfl) ⟨81017, by rfl⟩ : syracuseStep 108023 = 162035) B162035
theorem B108043 : Blo 107783 108043 := bstep (se 1 (by rfl) ⟨81032, by rfl⟩ : syracuseStep 108043 = 162065) B162065
theorem B468497 : Blo 107783 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B108055 : Blo 107783 108055 := bstep (se 1 (by rfl) ⟨81041, by rfl⟩ : syracuseStep 108055 = 162083) B162083
theorem B108075 : Blo 107783 108075 := bstep (se 1 (by rfl) ⟨81056, by rfl⟩ : syracuseStep 108075 = 162113) B162113
theorem B108087 : Blo 107783 108087 := bstep (se 1 (by rfl) ⟨81065, by rfl⟩ : syracuseStep 108087 = 162131) B162131
theorem B108107 : Blo 107783 108107 := bstep (se 1 (by rfl) ⟨81080, by rfl⟩ : syracuseStep 108107 = 162161) B162161
theorem B108119 : Blo 107783 108119 := bstep (se 1 (by rfl) ⟨81089, by rfl⟩ : syracuseStep 108119 = 162179) B162179
theorem B108139 : Blo 107783 108139 := bstep (se 1 (by rfl) ⟨81104, by rfl⟩ : syracuseStep 108139 = 162209) B162209
theorem B108151 : Blo 107783 108151 := bstep (se 1 (by rfl) ⟨81113, by rfl⟩ : syracuseStep 108151 = 162227) B162227
theorem B108171 : Blo 107783 108171 := bstep (se 1 (by rfl) ⟨81128, by rfl⟩ : syracuseStep 108171 = 162257) B162257
theorem B108183 : Blo 107783 108183 := bstep (se 1 (by rfl) ⟨81137, by rfl⟩ : syracuseStep 108183 = 162275) B162275
theorem B206489 : Blo 107783 206489 := bstep (se 2 (by rfl) ⟨77433, by rfl⟩ : syracuseStep 206489 = 154867) B154867
theorem B108203 : Blo 107783 108203 := bstep (se 1 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 108203 = 162305) B162305
theorem B501427 : Blo 107783 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B108215 : Blo 107783 108215 := bstep (se 1 (by rfl) ⟨81161, by rfl⟩ : syracuseStep 108215 = 162323) B162323
theorem B108235 : Blo 107783 108235 := bstep (se 1 (by rfl) ⟨81176, by rfl⟩ : syracuseStep 108235 = 162353) B162353
theorem B108247 : Blo 107783 108247 := bstep (se 1 (by rfl) ⟨81185, by rfl⟩ : syracuseStep 108247 = 162371) B162371
theorem B108267 : Blo 107783 108267 := bstep (se 1 (by rfl) ⟨81200, by rfl⟩ : syracuseStep 108267 = 162401) B162401
theorem B108279 : Blo 107783 108279 := bstep (se 1 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 108279 = 162419) B162419
theorem B108299 : Blo 107783 108299 := bstep (se 1 (by rfl) ⟨81224, by rfl⟩ : syracuseStep 108299 = 162449) B162449
theorem B108311 : Blo 107783 108311 := bstep (se 1 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 108311 = 162467) B162467
theorem B108331 : Blo 107783 108331 := bstep (se 1 (by rfl) ⟨81248, by rfl⟩ : syracuseStep 108331 = 162497) B162497
theorem B108343 : Blo 107783 108343 := bstep (se 1 (by rfl) ⟨81257, by rfl⟩ : syracuseStep 108343 = 162515) B162515
theorem B108363 : Blo 107783 108363 := bstep (se 1 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 108363 = 162545) B162545
theorem B534347 : Blo 107783 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B108375 : Blo 107783 108375 := bstep (se 1 (by rfl) ⟨81281, by rfl⟩ : syracuseStep 108375 = 162563) B162563
theorem B108395 : Blo 107783 108395 := bstep (se 1 (by rfl) ⟨81296, by rfl⟩ : syracuseStep 108395 = 162593) B162593
theorem B108407 : Blo 107783 108407 := bstep (se 1 (by rfl) ⟨81305, by rfl⟩ : syracuseStep 108407 = 162611) B162611
theorem B108427 : Blo 107783 108427 := bstep (se 1 (by rfl) ⟨81320, by rfl⟩ : syracuseStep 108427 = 162641) B162641
theorem B108439 : Blo 107783 108439 := bstep (se 1 (by rfl) ⟨81329, by rfl⟩ : syracuseStep 108439 = 162659) B162659
theorem B108459 : Blo 107783 108459 := bstep (se 1 (by rfl) ⟨81344, by rfl⟩ : syracuseStep 108459 = 162689) B162689
theorem B108471 : Blo 107783 108471 := bstep (se 1 (by rfl) ⟨81353, by rfl⟩ : syracuseStep 108471 = 162707) B162707
theorem B108491 : Blo 107783 108491 := bstep (se 1 (by rfl) ⟨81368, by rfl⟩ : syracuseStep 108491 = 162737) B162737
theorem B141259 : Blo 107783 141259 := bstep (se 1 (by rfl) ⟨105944, by rfl⟩ : syracuseStep 141259 = 211889) B211889
theorem B108503 : Blo 107783 108503 := bstep (se 1 (by rfl) ⟨81377, by rfl⟩ : syracuseStep 108503 = 162755) B162755
theorem B108523 : Blo 107783 108523 := bstep (se 1 (by rfl) ⟨81392, by rfl⟩ : syracuseStep 108523 = 162785) B162785
theorem B108535 : Blo 107783 108535 := bstep (se 1 (by rfl) ⟨81401, by rfl⟩ : syracuseStep 108535 = 162803) B162803
theorem B108555 : Blo 107783 108555 := bstep (se 1 (by rfl) ⟨81416, by rfl⟩ : syracuseStep 108555 = 162833) B162833
theorem B108567 : Blo 107783 108567 := bstep (se 1 (by rfl) ⟨81425, by rfl⟩ : syracuseStep 108567 = 162851) B162851
theorem B108587 : Blo 107783 108587 := bstep (se 1 (by rfl) ⟨81440, by rfl⟩ : syracuseStep 108587 = 162881) B162881
theorem B108599 : Blo 107783 108599 := bstep (se 1 (by rfl) ⟨81449, by rfl⟩ : syracuseStep 108599 = 162899) B162899
theorem B108619 : Blo 107783 108619 := bstep (se 1 (by rfl) ⟨81464, by rfl⟩ : syracuseStep 108619 = 162929) B162929
theorem B370763 : Blo 107783 370763 := bstep (se 1 (by rfl) ⟨278072, by rfl⟩ : syracuseStep 370763 = 556145) B556145
theorem B108631 : Blo 107783 108631 := bstep (se 1 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 108631 = 162947) B162947
theorem B632933 : Blo 107783 632933 := bstep (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) B118675
theorem B108651 : Blo 107783 108651 := bstep (se 1 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 108651 = 162977) B162977
theorem B108663 : Blo 107783 108663 := bstep (se 1 (by rfl) ⟨81497, by rfl⟩ : syracuseStep 108663 = 162995) B162995
theorem B108683 : Blo 107783 108683 := bstep (se 1 (by rfl) ⟨81512, by rfl⟩ : syracuseStep 108683 = 163025) B163025
theorem B108695 : Blo 107783 108695 := bstep (se 1 (by rfl) ⟨81521, by rfl⟩ : syracuseStep 108695 = 163043) B163043
theorem B108715 : Blo 107783 108715 := bstep (se 1 (by rfl) ⟨81536, by rfl⟩ : syracuseStep 108715 = 163073) B163073
theorem B108727 : Blo 107783 108727 := bstep (se 1 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 108727 = 163091) B163091
theorem B108747 : Blo 107783 108747 := bstep (se 1 (by rfl) ⟨81560, by rfl⟩ : syracuseStep 108747 = 163121) B163121
theorem B108759 : Blo 107783 108759 := bstep (se 1 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 108759 = 163139) B163139
theorem B108779 : Blo 107783 108779 := bstep (se 1 (by rfl) ⟨81584, by rfl⟩ : syracuseStep 108779 = 163169) B163169
theorem B108791 : Blo 107783 108791 := bstep (se 1 (by rfl) ⟨81593, by rfl⟩ : syracuseStep 108791 = 163187) B163187
theorem B1059077 : Blo 107783 1059077 := bstep (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) B198577
theorem B108811 : Blo 107783 108811 := bstep (se 1 (by rfl) ⟨81608, by rfl⟩ : syracuseStep 108811 = 163217) B163217
theorem B108823 : Blo 107783 108823 := bstep (se 1 (by rfl) ⟨81617, by rfl⟩ : syracuseStep 108823 = 163235) B163235
theorem B207127 : Blo 107783 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B108843 : Blo 107783 108843 := bstep (se 1 (by rfl) ⟨81632, by rfl⟩ : syracuseStep 108843 = 163265) B163265
theorem B108855 : Blo 107783 108855 := bstep (se 1 (by rfl) ⟨81641, by rfl⟩ : syracuseStep 108855 = 163283) B163283
theorem B108875 : Blo 107783 108875 := bstep (se 1 (by rfl) ⟨81656, by rfl⟩ : syracuseStep 108875 = 163313) B163313
theorem B108887 : Blo 107783 108887 := bstep (se 1 (by rfl) ⟨81665, by rfl⟩ : syracuseStep 108887 = 163331) B163331
theorem B371033 : Blo 107783 371033 := bstep (se 2 (by rfl) ⟨139137, by rfl⟩ : syracuseStep 371033 = 278275) B278275
theorem B108907 : Blo 107783 108907 := bstep (se 1 (by rfl) ⟨81680, by rfl⟩ : syracuseStep 108907 = 163361) B163361
theorem B108919 : Blo 107783 108919 := bstep (se 1 (by rfl) ⟨81689, by rfl⟩ : syracuseStep 108919 = 163379) B163379
theorem B108939 : Blo 107783 108939 := bstep (se 1 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 108939 = 163409) B163409
theorem B2337173 : Blo 107783 2337173 := bstep (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) B109555
theorem B108951 : Blo 107783 108951 := bstep (se 1 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 108951 = 163427) B163427
theorem B108971 : Blo 107783 108971 := bstep (se 1 (by rfl) ⟨81728, by rfl⟩ : syracuseStep 108971 = 163457) B163457
theorem B469421 : Blo 107783 469421 := bstep (se 3 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 469421 = 176033) B176033
theorem B108983 : Blo 107783 108983 := bstep (se 1 (by rfl) ⟨81737, by rfl⟩ : syracuseStep 108983 = 163475) B163475
theorem B109003 : Blo 107783 109003 := bstep (se 1 (by rfl) ⟨81752, by rfl⟩ : syracuseStep 109003 = 163505) B163505
theorem B109015 : Blo 107783 109015 := bstep (se 1 (by rfl) ⟨81761, by rfl⟩ : syracuseStep 109015 = 163523) B163523
theorem B109035 : Blo 107783 109035 := bstep (se 1 (by rfl) ⟨81776, by rfl⟩ : syracuseStep 109035 = 163553) B163553
theorem B109047 : Blo 107783 109047 := bstep (se 1 (by rfl) ⟨81785, by rfl⟩ : syracuseStep 109047 = 163571) B163571
theorem B109067 : Blo 107783 109067 := bstep (se 1 (by rfl) ⟨81800, by rfl⟩ : syracuseStep 109067 = 163601) B163601
theorem B109079 : Blo 107783 109079 := bstep (se 1 (by rfl) ⟨81809, by rfl⟩ : syracuseStep 109079 = 163619) B163619
theorem B109099 : Blo 107783 109099 := bstep (se 1 (by rfl) ⟨81824, by rfl⟩ : syracuseStep 109099 = 163649) B163649
theorem B109111 : Blo 107783 109111 := bstep (se 1 (by rfl) ⟨81833, by rfl⟩ : syracuseStep 109111 = 163667) B163667
theorem B109131 : Blo 107783 109131 := bstep (se 1 (by rfl) ⟨81848, by rfl⟩ : syracuseStep 109131 = 163697) B163697
theorem B109143 : Blo 107783 109143 := bstep (se 1 (by rfl) ⟨81857, by rfl⟩ : syracuseStep 109143 = 163715) B163715
theorem B109163 : Blo 107783 109163 := bstep (se 1 (by rfl) ⟨81872, by rfl⟩ : syracuseStep 109163 = 163745) B163745
theorem B109175 : Blo 107783 109175 := bstep (se 1 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 109175 = 163763) B163763
theorem B109195 : Blo 107783 109195 := bstep (se 1 (by rfl) ⟨81896, by rfl⟩ : syracuseStep 109195 = 163793) B163793
theorem B109207 : Blo 107783 109207 := bstep (se 1 (by rfl) ⟨81905, by rfl⟩ : syracuseStep 109207 = 163811) B163811
theorem B109227 : Blo 107783 109227 := bstep (se 1 (by rfl) ⟨81920, by rfl⟩ : syracuseStep 109227 = 163841) B163841
theorem B109239 : Blo 107783 109239 := bstep (se 1 (by rfl) ⟨81929, by rfl⟩ : syracuseStep 109239 = 163859) B163859
theorem B109259 : Blo 107783 109259 := bstep (se 1 (by rfl) ⟨81944, by rfl⟩ : syracuseStep 109259 = 163889) B163889
theorem B109271 : Blo 107783 109271 := bstep (se 1 (by rfl) ⟨81953, by rfl⟩ : syracuseStep 109271 = 163907) B163907
theorem B109291 : Blo 107783 109291 := bstep (se 1 (by rfl) ⟨81968, by rfl⟩ : syracuseStep 109291 = 163937) B163937
theorem B109303 : Blo 107783 109303 := bstep (se 1 (by rfl) ⟨81977, by rfl⟩ : syracuseStep 109303 = 163955) B163955
theorem B109323 : Blo 107783 109323 := bstep (se 1 (by rfl) ⟨81992, by rfl⟩ : syracuseStep 109323 = 163985) B163985
theorem B109335 : Blo 107783 109335 := bstep (se 1 (by rfl) ⟨82001, by rfl⟩ : syracuseStep 109335 = 164003) B164003
theorem B109355 : Blo 107783 109355 := bstep (se 1 (by rfl) ⟨82016, by rfl⟩ : syracuseStep 109355 = 164033) B164033
theorem B273203 : Blo 107783 273203 := bstep (se 1 (by rfl) ⟨204902, by rfl⟩ : syracuseStep 273203 = 409805) B409805
theorem B109367 : Blo 107783 109367 := bstep (se 1 (by rfl) ⟨82025, by rfl⟩ : syracuseStep 109367 = 164051) B164051
theorem B109387 : Blo 107783 109387 := bstep (se 1 (by rfl) ⟨82040, by rfl⟩ : syracuseStep 109387 = 164081) B164081
theorem B109399 : Blo 107783 109399 := bstep (se 1 (by rfl) ⟨82049, by rfl⟩ : syracuseStep 109399 = 164099) B164099
theorem B109419 : Blo 107783 109419 := bstep (se 1 (by rfl) ⟨82064, by rfl⟩ : syracuseStep 109419 = 164129) B164129
theorem B109431 : Blo 107783 109431 := bstep (se 1 (by rfl) ⟨82073, by rfl⟩ : syracuseStep 109431 = 164147) B164147
theorem B109451 : Blo 107783 109451 := bstep (se 1 (by rfl) ⟨82088, by rfl⟩ : syracuseStep 109451 = 164177) B164177
theorem B109463 : Blo 107783 109463 := bstep (se 1 (by rfl) ⟨82097, by rfl⟩ : syracuseStep 109463 = 164195) B164195
theorem B109483 : Blo 107783 109483 := bstep (se 1 (by rfl) ⟨82112, by rfl⟩ : syracuseStep 109483 = 164225) B164225
theorem B109495 : Blo 107783 109495 := bstep (se 1 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 109495 = 164243) B164243
theorem B109515 : Blo 107783 109515 := bstep (se 1 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 109515 = 164273) B164273
theorem B109527 : Blo 107783 109527 := bstep (se 1 (by rfl) ⟨82145, by rfl⟩ : syracuseStep 109527 = 164291) B164291
theorem B109547 : Blo 107783 109547 := bstep (se 1 (by rfl) ⟨82160, by rfl⟩ : syracuseStep 109547 = 164321) B164321
theorem B109559 : Blo 107783 109559 := bstep (se 1 (by rfl) ⟨82169, by rfl⟩ : syracuseStep 109559 = 164339) B164339
theorem B109579 : Blo 107783 109579 := bstep (se 1 (by rfl) ⟨82184, by rfl⟩ : syracuseStep 109579 = 164369) B164369
theorem B109591 : Blo 107783 109591 := bstep (se 1 (by rfl) ⟨82193, by rfl⟩ : syracuseStep 109591 = 164387) B164387
theorem B371735 : Blo 107783 371735 := bstep (se 1 (by rfl) ⟨278801, by rfl⟩ : syracuseStep 371735 = 557603) B557603
theorem B109611 : Blo 107783 109611 := bstep (se 1 (by rfl) ⟨82208, by rfl⟩ : syracuseStep 109611 = 164417) B164417
theorem B109623 : Blo 107783 109623 := bstep (se 1 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 109623 = 164435) B164435
theorem B207947 : Blo 107783 207947 := bstep (se 1 (by rfl) ⟨155960, by rfl⟩ : syracuseStep 207947 = 311921) B311921
theorem B109643 : Blo 107783 109643 := bstep (se 1 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 109643 = 164465) B164465
theorem B109655 : Blo 107783 109655 := bstep (se 1 (by rfl) ⟨82241, by rfl⟩ : syracuseStep 109655 = 164483) B164483
theorem B109675 : Blo 107783 109675 := bstep (se 1 (by rfl) ⟨82256, by rfl⟩ : syracuseStep 109675 = 164513) B164513
theorem B109687 : Blo 107783 109687 := bstep (se 1 (by rfl) ⟨82265, by rfl⟩ : syracuseStep 109687 = 164531) B164531
theorem B208001 : Blo 107783 208001 := bstep (se 2 (by rfl) ⟨78000, by rfl⟩ : syracuseStep 208001 = 156001) B156001
theorem B1387651 : Blo 107783 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B109707 : Blo 107783 109707 := bstep (se 1 (by rfl) ⟨82280, by rfl⟩ : syracuseStep 109707 = 164561) B164561
theorem B109719 : Blo 107783 109719 := bstep (se 1 (by rfl) ⟨82289, by rfl⟩ : syracuseStep 109719 = 164579) B164579
theorem B109739 : Blo 107783 109739 := bstep (se 1 (by rfl) ⟨82304, by rfl⟩ : syracuseStep 109739 = 164609) B164609
theorem B109751 : Blo 107783 109751 := bstep (se 1 (by rfl) ⟨82313, by rfl⟩ : syracuseStep 109751 = 164627) B164627
theorem B109771 : Blo 107783 109771 := bstep (se 1 (by rfl) ⟨82328, by rfl⟩ : syracuseStep 109771 = 164657) B164657
theorem B109783 : Blo 107783 109783 := bstep (se 1 (by rfl) ⟨82337, by rfl⟩ : syracuseStep 109783 = 164675) B164675
theorem B109803 : Blo 107783 109803 := bstep (se 1 (by rfl) ⟨82352, by rfl⟩ : syracuseStep 109803 = 164705) B164705
theorem B109815 : Blo 107783 109815 := bstep (se 1 (by rfl) ⟨82361, by rfl⟩ : syracuseStep 109815 = 164723) B164723
theorem B437507 : Blo 107783 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B109835 : Blo 107783 109835 := bstep (se 1 (by rfl) ⟨82376, by rfl⟩ : syracuseStep 109835 = 164753) B164753
theorem B109847 : Blo 107783 109847 := bstep (se 1 (by rfl) ⟨82385, by rfl⟩ : syracuseStep 109847 = 164771) B164771
theorem B339223 : Blo 107783 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B896291 : Blo 107783 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B109867 : Blo 107783 109867 := bstep (se 1 (by rfl) ⟨82400, by rfl⟩ : syracuseStep 109867 = 164801) B164801
theorem B109879 : Blo 107783 109879 := bstep (se 1 (by rfl) ⟨82409, by rfl⟩ : syracuseStep 109879 = 164819) B164819
theorem B273739 : Blo 107783 273739 := bstep (se 1 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 273739 = 410609) B410609
theorem B109899 : Blo 107783 109899 := bstep (se 1 (by rfl) ⟨82424, by rfl⟩ : syracuseStep 109899 = 164849) B164849
theorem B109911 : Blo 107783 109911 := bstep (se 1 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 109911 = 164867) B164867
theorem B699749 : Blo 107783 699749 := bstep (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) B131203
theorem B109931 : Blo 107783 109931 := bstep (se 1 (by rfl) ⟨82448, by rfl⟩ : syracuseStep 109931 = 164897) B164897
theorem B109943 : Blo 107783 109943 := bstep (se 1 (by rfl) ⟨82457, by rfl⟩ : syracuseStep 109943 = 164915) B164915
theorem B109963 : Blo 107783 109963 := bstep (se 1 (by rfl) ⟨82472, by rfl⟩ : syracuseStep 109963 = 164945) B164945
theorem B109975 : Blo 107783 109975 := bstep (se 1 (by rfl) ⟨82481, by rfl⟩ : syracuseStep 109975 = 164963) B164963
theorem B109995 : Blo 107783 109995 := bstep (se 1 (by rfl) ⟨82496, by rfl⟩ : syracuseStep 109995 = 164993) B164993
theorem B110007 : Blo 107783 110007 := bstep (se 1 (by rfl) ⟨82505, by rfl⟩ : syracuseStep 110007 = 165011) B165011
theorem B110027 : Blo 107783 110027 := bstep (se 1 (by rfl) ⟨82520, by rfl⟩ : syracuseStep 110027 = 165041) B165041
theorem B110039 : Blo 107783 110039 := bstep (se 1 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 110039 = 165059) B165059
theorem B273881 : Blo 107783 273881 := bstep (se 2 (by rfl) ⟨102705, by rfl⟩ : syracuseStep 273881 = 205411) B205411
theorem B110059 : Blo 107783 110059 := bstep (se 1 (by rfl) ⟨82544, by rfl⟩ : syracuseStep 110059 = 165089) B165089
theorem B110071 : Blo 107783 110071 := bstep (se 1 (by rfl) ⟨82553, by rfl⟩ : syracuseStep 110071 = 165107) B165107
theorem B110091 : Blo 107783 110091 := bstep (se 1 (by rfl) ⟨82568, by rfl⟩ : syracuseStep 110091 = 165137) B165137
theorem B110103 : Blo 107783 110103 := bstep (se 1 (by rfl) ⟨82577, by rfl⟩ : syracuseStep 110103 = 165155) B165155
theorem B110123 : Blo 107783 110123 := bstep (se 1 (by rfl) ⟨82592, by rfl⟩ : syracuseStep 110123 = 165185) B165185
theorem B372275 : Blo 107783 372275 := bstep (se 1 (by rfl) ⟨279206, by rfl⟩ : syracuseStep 372275 = 558413) B558413
theorem B110135 : Blo 107783 110135 := bstep (se 1 (by rfl) ⟨82601, by rfl⟩ : syracuseStep 110135 = 165203) B165203
theorem B110155 : Blo 107783 110155 := bstep (se 1 (by rfl) ⟨82616, by rfl⟩ : syracuseStep 110155 = 165233) B165233
theorem B110167 : Blo 107783 110167 := bstep (se 1 (by rfl) ⟨82625, by rfl⟩ : syracuseStep 110167 = 165251) B165251
theorem B110187 : Blo 107783 110187 := bstep (se 1 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 110187 = 165281) B165281
theorem B110199 : Blo 107783 110199 := bstep (se 1 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 110199 = 165299) B165299
theorem B110219 : Blo 107783 110219 := bstep (se 1 (by rfl) ⟨82664, by rfl⟩ : syracuseStep 110219 = 165329) B165329
theorem B110231 : Blo 107783 110231 := bstep (se 1 (by rfl) ⟨82673, by rfl⟩ : syracuseStep 110231 = 165347) B165347
theorem B110251 : Blo 107783 110251 := bstep (se 1 (by rfl) ⟨82688, by rfl⟩ : syracuseStep 110251 = 165377) B165377
theorem B110263 : Blo 107783 110263 := bstep (se 1 (by rfl) ⟨82697, by rfl⟩ : syracuseStep 110263 = 165395) B165395
theorem B110283 : Blo 107783 110283 := bstep (se 1 (by rfl) ⟨82712, by rfl⟩ : syracuseStep 110283 = 165425) B165425
theorem B110295 : Blo 107783 110295 := bstep (se 1 (by rfl) ⟨82721, by rfl⟩ : syracuseStep 110295 = 165443) B165443
theorem B110315 : Blo 107783 110315 := bstep (se 1 (by rfl) ⟨82736, by rfl⟩ : syracuseStep 110315 = 165473) B165473
theorem B110327 : Blo 107783 110327 := bstep (se 1 (by rfl) ⟨82745, by rfl⟩ : syracuseStep 110327 = 165491) B165491
theorem B110347 : Blo 107783 110347 := bstep (se 1 (by rfl) ⟨82760, by rfl⟩ : syracuseStep 110347 = 165521) B165521
theorem B110359 : Blo 107783 110359 := bstep (se 1 (by rfl) ⟨82769, by rfl⟩ : syracuseStep 110359 = 165539) B165539
theorem B110379 : Blo 107783 110379 := bstep (se 1 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 110379 = 165569) B165569
theorem B110391 : Blo 107783 110391 := bstep (se 1 (by rfl) ⟨82793, by rfl⟩ : syracuseStep 110391 = 165587) B165587
theorem B372545 : Blo 107783 372545 := bstep (se 2 (by rfl) ⟨139704, by rfl⟩ : syracuseStep 372545 = 279409) B279409
theorem B700235 : Blo 107783 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B110411 : Blo 107783 110411 := bstep (se 1 (by rfl) ⟨82808, by rfl⟩ : syracuseStep 110411 = 165617) B165617
theorem B110423 : Blo 107783 110423 := bstep (se 1 (by rfl) ⟨82817, by rfl⟩ : syracuseStep 110423 = 165635) B165635
theorem B470873 : Blo 107783 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B110443 : Blo 107783 110443 := bstep (se 1 (by rfl) ⟨82832, by rfl⟩ : syracuseStep 110443 = 165665) B165665
theorem B1781621 : Blo 107783 1781621 := bstep (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) B167027
theorem B110455 : Blo 107783 110455 := bstep (se 1 (by rfl) ⟨82841, by rfl⟩ : syracuseStep 110455 = 165683) B165683
theorem B110475 : Blo 107783 110475 := bstep (se 1 (by rfl) ⟨82856, by rfl⟩ : syracuseStep 110475 = 165713) B165713
theorem B110487 : Blo 107783 110487 := bstep (se 1 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 110487 = 165731) B165731
theorem B110507 : Blo 107783 110507 := bstep (se 1 (by rfl) ⟨82880, by rfl⟩ : syracuseStep 110507 = 165761) B165761
theorem B110519 : Blo 107783 110519 := bstep (se 1 (by rfl) ⟨82889, by rfl⟩ : syracuseStep 110519 = 165779) B165779
theorem B110539 : Blo 107783 110539 := bstep (se 1 (by rfl) ⟨82904, by rfl⟩ : syracuseStep 110539 = 165809) B165809
theorem B110551 : Blo 107783 110551 := bstep (se 1 (by rfl) ⟨82913, by rfl⟩ : syracuseStep 110551 = 165827) B165827
theorem B110571 : Blo 107783 110571 := bstep (se 1 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 110571 = 165857) B165857
theorem B110583 : Blo 107783 110583 := bstep (se 1 (by rfl) ⟨82937, by rfl⟩ : syracuseStep 110583 = 165875) B165875
theorem B110603 : Blo 107783 110603 := bstep (se 1 (by rfl) ⟨82952, by rfl⟩ : syracuseStep 110603 = 165905) B165905
theorem B208919 : Blo 107783 208919 := bstep (se 1 (by rfl) ⟨156689, by rfl⟩ : syracuseStep 208919 = 313379) B313379
theorem B110615 : Blo 107783 110615 := bstep (se 1 (by rfl) ⟨82961, by rfl⟩ : syracuseStep 110615 = 165923) B165923
theorem B110635 : Blo 107783 110635 := bstep (se 1 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 110635 = 165953) B165953
theorem B110647 : Blo 107783 110647 := bstep (se 1 (by rfl) ⟨82985, by rfl⟩ : syracuseStep 110647 = 165971) B165971
theorem B110667 : Blo 107783 110667 := bstep (se 1 (by rfl) ⟨83000, by rfl⟩ : syracuseStep 110667 = 166001) B166001
theorem B110679 : Blo 107783 110679 := bstep (se 1 (by rfl) ⟨83009, by rfl⟩ : syracuseStep 110679 = 166019) B166019
theorem B110699 : Blo 107783 110699 := bstep (se 1 (by rfl) ⟨83024, by rfl⟩ : syracuseStep 110699 = 166049) B166049
theorem B110711 : Blo 107783 110711 := bstep (se 1 (by rfl) ⟨83033, by rfl⟩ : syracuseStep 110711 = 166067) B166067
theorem B110731 : Blo 107783 110731 := bstep (se 1 (by rfl) ⟨83048, by rfl⟩ : syracuseStep 110731 = 166097) B166097
theorem B110743 : Blo 107783 110743 := bstep (se 1 (by rfl) ⟨83057, by rfl⟩ : syracuseStep 110743 = 166115) B166115
theorem B110763 : Blo 107783 110763 := bstep (se 1 (by rfl) ⟨83072, by rfl⟩ : syracuseStep 110763 = 166145) B166145
theorem B110775 : Blo 107783 110775 := bstep (se 1 (by rfl) ⟨83081, by rfl⟩ : syracuseStep 110775 = 166163) B166163
theorem B110795 : Blo 107783 110795 := bstep (se 1 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 110795 = 166193) B166193
theorem B110807 : Blo 107783 110807 := bstep (se 1 (by rfl) ⟨83105, by rfl⟩ : syracuseStep 110807 = 166211) B166211
theorem B110827 : Blo 107783 110827 := bstep (se 1 (by rfl) ⟨83120, by rfl⟩ : syracuseStep 110827 = 166241) B166241
theorem B110839 : Blo 107783 110839 := bstep (se 1 (by rfl) ⟨83129, by rfl⟩ : syracuseStep 110839 = 166259) B166259
theorem B110859 : Blo 107783 110859 := bstep (se 1 (by rfl) ⟨83144, by rfl⟩ : syracuseStep 110859 = 166289) B166289
theorem B274711 : Blo 107783 274711 := bstep (se 1 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 274711 = 412067) B412067
theorem B110871 : Blo 107783 110871 := bstep (se 1 (by rfl) ⟨83153, by rfl⟩ : syracuseStep 110871 = 166307) B166307
theorem B110891 : Blo 107783 110891 := bstep (se 1 (by rfl) ⟨83168, by rfl⟩ : syracuseStep 110891 = 166337) B166337
theorem B110903 : Blo 107783 110903 := bstep (se 1 (by rfl) ⟨83177, by rfl⟩ : syracuseStep 110903 = 166355) B166355
theorem B110923 : Blo 107783 110923 := bstep (se 1 (by rfl) ⟨83192, by rfl⟩ : syracuseStep 110923 = 166385) B166385
theorem B110935 : Blo 107783 110935 := bstep (se 1 (by rfl) ⟨83201, by rfl⟩ : syracuseStep 110935 = 166403) B166403
theorem B373085 : Blo 107783 373085 := bstep (se 3 (by rfl) ⟨69953, by rfl⟩ : syracuseStep 373085 = 139907) B139907
theorem B110955 : Blo 107783 110955 := bstep (se 1 (by rfl) ⟨83216, by rfl⟩ : syracuseStep 110955 = 166433) B166433
theorem B110967 : Blo 107783 110967 := bstep (se 1 (by rfl) ⟨83225, by rfl⟩ : syracuseStep 110967 = 166451) B166451
theorem B110987 : Blo 107783 110987 := bstep (se 1 (by rfl) ⟨83240, by rfl⟩ : syracuseStep 110987 = 166481) B166481
theorem B110999 : Blo 107783 110999 := bstep (se 1 (by rfl) ⟨83249, by rfl⟩ : syracuseStep 110999 = 166499) B166499
theorem B111019 : Blo 107783 111019 := bstep (se 1 (by rfl) ⟨83264, by rfl⟩ : syracuseStep 111019 = 166529) B166529
theorem B111031 : Blo 107783 111031 := bstep (se 1 (by rfl) ⟨83273, by rfl⟩ : syracuseStep 111031 = 166547) B166547
theorem B111051 : Blo 107783 111051 := bstep (se 1 (by rfl) ⟨83288, by rfl⟩ : syracuseStep 111051 = 166577) B166577
theorem B930253 : Blo 107783 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B111063 : Blo 107783 111063 := bstep (se 1 (by rfl) ⟨83297, by rfl⟩ : syracuseStep 111063 = 166595) B166595
theorem B111083 : Blo 107783 111083 := bstep (se 1 (by rfl) ⟨83312, by rfl⟩ : syracuseStep 111083 = 166625) B166625
theorem B111095 : Blo 107783 111095 := bstep (se 1 (by rfl) ⟨83321, by rfl⟩ : syracuseStep 111095 = 166643) B166643
theorem B111115 : Blo 107783 111115 := bstep (se 1 (by rfl) ⟨83336, by rfl⟩ : syracuseStep 111115 = 166673) B166673
theorem B111127 : Blo 107783 111127 := bstep (se 1 (by rfl) ⟨83345, by rfl⟩ : syracuseStep 111127 = 166691) B166691
theorem B111147 : Blo 107783 111147 := bstep (se 1 (by rfl) ⟨83360, by rfl⟩ : syracuseStep 111147 = 166721) B166721
theorem B209459 : Blo 107783 209459 := bstep (se 1 (by rfl) ⟨157094, by rfl⟩ : syracuseStep 209459 = 314189) B314189
theorem B111159 : Blo 107783 111159 := bstep (se 1 (by rfl) ⟨83369, by rfl⟩ : syracuseStep 111159 = 166739) B166739
theorem B111179 : Blo 107783 111179 := bstep (se 1 (by rfl) ⟨83384, by rfl⟩ : syracuseStep 111179 = 166769) B166769
theorem B111191 : Blo 107783 111191 := bstep (se 1 (by rfl) ⟨83393, by rfl⟩ : syracuseStep 111191 = 166787) B166787
theorem B111211 : Blo 107783 111211 := bstep (se 1 (by rfl) ⟨83408, by rfl⟩ : syracuseStep 111211 = 166817) B166817
theorem B111223 : Blo 107783 111223 := bstep (se 1 (by rfl) ⟨83417, by rfl⟩ : syracuseStep 111223 = 166835) B166835
theorem B111243 : Blo 107783 111243 := bstep (se 1 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 111243 = 166865) B166865
theorem B111255 : Blo 107783 111255 := bstep (se 1 (by rfl) ⟨83441, by rfl⟩ : syracuseStep 111255 = 166883) B166883
theorem B111275 : Blo 107783 111275 := bstep (se 1 (by rfl) ⟨83456, by rfl⟩ : syracuseStep 111275 = 166913) B166913
theorem B111287 : Blo 107783 111287 := bstep (se 1 (by rfl) ⟨83465, by rfl⟩ : syracuseStep 111287 = 166931) B166931
theorem B275147 : Blo 107783 275147 := bstep (se 1 (by rfl) ⟨206360, by rfl⟩ : syracuseStep 275147 = 412721) B412721
theorem B111307 : Blo 107783 111307 := bstep (se 1 (by rfl) ⟨83480, by rfl⟩ : syracuseStep 111307 = 166961) B166961
theorem B111319 : Blo 107783 111319 := bstep (se 1 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 111319 = 166979) B166979
theorem B111339 : Blo 107783 111339 := bstep (se 1 (by rfl) ⟨83504, by rfl⟩ : syracuseStep 111339 = 167009) B167009
theorem B111351 : Blo 107783 111351 := bstep (se 1 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 111351 = 167027) B167027
theorem B111371 : Blo 107783 111371 := bstep (se 1 (by rfl) ⟨83528, by rfl⟩ : syracuseStep 111371 = 167057) B167057
theorem B111383 : Blo 107783 111383 := bstep (se 1 (by rfl) ⟨83537, by rfl⟩ : syracuseStep 111383 = 167075) B167075
theorem B111403 : Blo 107783 111403 := bstep (se 1 (by rfl) ⟨83552, by rfl⟩ : syracuseStep 111403 = 167105) B167105
theorem B111415 : Blo 107783 111415 := bstep (se 1 (by rfl) ⟨83561, by rfl⟩ : syracuseStep 111415 = 167123) B167123
theorem B111435 : Blo 107783 111435 := bstep (se 1 (by rfl) ⟨83576, by rfl⟩ : syracuseStep 111435 = 167153) B167153
theorem B111447 : Blo 107783 111447 := bstep (se 1 (by rfl) ⟨83585, by rfl⟩ : syracuseStep 111447 = 167171) B167171
theorem B1192805 : Blo 107783 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B111467 : Blo 107783 111467 := bstep (se 1 (by rfl) ⟨83600, by rfl⟩ : syracuseStep 111467 = 167201) B167201
theorem B111479 : Blo 107783 111479 := bstep (se 1 (by rfl) ⟨83609, by rfl⟩ : syracuseStep 111479 = 167219) B167219
theorem B111499 : Blo 107783 111499 := bstep (se 1 (by rfl) ⟨83624, by rfl⟩ : syracuseStep 111499 = 167249) B167249
theorem B111511 : Blo 107783 111511 := bstep (se 1 (by rfl) ⟨83633, by rfl⟩ : syracuseStep 111511 = 167267) B167267
theorem B242585 : Blo 107783 242585 := bstep (se 2 (by rfl) ⟨90969, by rfl⟩ : syracuseStep 242585 = 181939) B181939
theorem B111531 : Blo 107783 111531 := bstep (se 1 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 111531 = 167297) B167297
theorem B111543 : Blo 107783 111543 := bstep (se 1 (by rfl) ⟨83657, by rfl⟩ : syracuseStep 111543 = 167315) B167315
theorem B111563 : Blo 107783 111563 := bstep (se 1 (by rfl) ⟨83672, by rfl⟩ : syracuseStep 111563 = 167345) B167345
theorem B111575 : Blo 107783 111575 := bstep (se 1 (by rfl) ⟨83681, by rfl⟩ : syracuseStep 111575 = 167363) B167363
theorem B111595 : Blo 107783 111595 := bstep (se 1 (by rfl) ⟨83696, by rfl⟩ : syracuseStep 111595 = 167393) B167393
theorem B242675 : Blo 107783 242675 := bstep (se 1 (by rfl) ⟨182006, by rfl⟩ : syracuseStep 242675 = 364013) B364013
theorem B111607 : Blo 107783 111607 := bstep (se 1 (by rfl) ⟨83705, by rfl⟩ : syracuseStep 111607 = 167411) B167411
theorem B832517 : Blo 107783 832517 := bstep (se 4 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 832517 = 156097) B156097
theorem B111627 : Blo 107783 111627 := bstep (se 1 (by rfl) ⟨83720, by rfl⟩ : syracuseStep 111627 = 167441) B167441
theorem B242711 : Blo 107783 242711 := bstep (se 1 (by rfl) ⟨182033, by rfl⟩ : syracuseStep 242711 = 364067) B364067
theorem B111639 : Blo 107783 111639 := bstep (se 1 (by rfl) ⟨83729, by rfl⟩ : syracuseStep 111639 = 167459) B167459
theorem B209945 : Blo 107783 209945 := bstep (se 2 (by rfl) ⟨78729, by rfl⟩ : syracuseStep 209945 = 157459) B157459
theorem B832547 : Blo 107783 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B111659 : Blo 107783 111659 := bstep (se 1 (by rfl) ⟨83744, by rfl⟩ : syracuseStep 111659 = 167489) B167489
theorem B111671 : Blo 107783 111671 := bstep (se 1 (by rfl) ⟨83753, by rfl⟩ : syracuseStep 111671 = 167507) B167507
theorem B275521 : Blo 107783 275521 := bstep (se 2 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 275521 = 206641) B206641
theorem B308299 : Blo 107783 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B111691 : Blo 107783 111691 := bstep (se 1 (by rfl) ⟨83768, by rfl⟩ : syracuseStep 111691 = 167537) B167537
theorem B111703 : Blo 107783 111703 := bstep (se 1 (by rfl) ⟨83777, by rfl⟩ : syracuseStep 111703 = 167555) B167555
theorem B111723 : Blo 107783 111723 := bstep (se 1 (by rfl) ⟨83792, by rfl⟩ : syracuseStep 111723 = 167585) B167585
theorem B111735 : Blo 107783 111735 := bstep (se 1 (by rfl) ⟨83801, by rfl⟩ : syracuseStep 111735 = 167603) B167603
theorem B111755 : Blo 107783 111755 := bstep (se 1 (by rfl) ⟨83816, by rfl⟩ : syracuseStep 111755 = 167633) B167633
theorem B111767 : Blo 107783 111767 := bstep (se 1 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 111767 = 167651) B167651
theorem B242891 : Blo 107783 242891 := bstep (se 1 (by rfl) ⟨182168, by rfl⟩ : syracuseStep 242891 = 364337) B364337
theorem B242945 : Blo 107783 242945 := bstep (se 2 (by rfl) ⟨91104, by rfl⟩ : syracuseStep 242945 = 182209) B182209
theorem B308573 : Blo 107783 308573 := bstep (se 3 (by rfl) ⟨57857, by rfl⟩ : syracuseStep 308573 = 115715) B115715
theorem B472513 : Blo 107783 472513 := bstep (se 2 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 472513 = 354385) B354385
theorem B374219 : Blo 107783 374219 := bstep (se 1 (by rfl) ⟨280664, by rfl⟩ : syracuseStep 374219 = 561329) B561329
theorem B243161 : Blo 107783 243161 := bstep (se 2 (by rfl) ⟨91185, by rfl⟩ : syracuseStep 243161 = 182371) B182371
theorem B2668049 : Blo 107783 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B243251 : Blo 107783 243251 := bstep (se 1 (by rfl) ⟨182438, by rfl⟩ : syracuseStep 243251 = 364877) B364877
theorem B243287 : Blo 107783 243287 := bstep (se 1 (by rfl) ⟨182465, by rfl⟩ : syracuseStep 243287 = 364931) B364931
theorem B11417219 : Blo 107783 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B276119 : Blo 107783 276119 := bstep (se 1 (by rfl) ⟨207089, by rfl⟩ : syracuseStep 276119 = 414179) B414179
theorem B374489 : Blo 107783 374489 := bstep (se 2 (by rfl) ⟨140433, by rfl⟩ : syracuseStep 374489 = 280867) B280867
theorem B243467 : Blo 107783 243467 := bstep (se 1 (by rfl) ⟨182600, by rfl⟩ : syracuseStep 243467 = 365201) B365201
theorem B243521 : Blo 107783 243521 := bstep (se 2 (by rfl) ⟨91320, by rfl⟩ : syracuseStep 243521 = 182641) B182641
theorem B112523 : Blo 107783 112523 := bstep (se 1 (by rfl) ⟨84392, by rfl⟩ : syracuseStep 112523 = 168785) B168785
theorem B473111 : Blo 107783 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B243737 : Blo 107783 243737 := bstep (se 2 (by rfl) ⟨91401, by rfl⟩ : syracuseStep 243737 = 182803) B182803
theorem B243827 : Blo 107783 243827 := bstep (se 1 (by rfl) ⟨182870, by rfl⟩ : syracuseStep 243827 = 365741) B365741
theorem B243863 : Blo 107783 243863 := bstep (se 1 (by rfl) ⟨182897, by rfl⟩ : syracuseStep 243863 = 365795) B365795
theorem B244043 : Blo 107783 244043 := bstep (se 1 (by rfl) ⟨183032, by rfl⟩ : syracuseStep 244043 = 366065) B366065
theorem B244097 : Blo 107783 244097 := bstep (se 2 (by rfl) ⟨91536, by rfl⟩ : syracuseStep 244097 = 183073) B183073
theorem B375191 : Blo 107783 375191 := bstep (se 1 (by rfl) ⟨281393, by rfl⟩ : syracuseStep 375191 = 562787) B562787
theorem B440749 : Blo 107783 440749 := bstep (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) B165281
theorem B276929 : Blo 107783 276929 := bstep (se 2 (by rfl) ⟨103848, by rfl⟩ : syracuseStep 276929 = 207697) B207697
theorem B211403 : Blo 107783 211403 := bstep (se 1 (by rfl) ⟨158552, by rfl⟩ : syracuseStep 211403 = 317105) B317105
theorem B244313 : Blo 107783 244313 := bstep (se 2 (by rfl) ⟨91617, by rfl⟩ : syracuseStep 244313 = 183235) B183235
theorem B211585 : Blo 107783 211585 := bstep (se 2 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 211585 = 158689) B158689
theorem B244403 : Blo 107783 244403 := bstep (se 1 (by rfl) ⟨183302, by rfl⟩ : syracuseStep 244403 = 366605) B366605
theorem B244439 : Blo 107783 244439 := bstep (se 1 (by rfl) ⟨183329, by rfl⟩ : syracuseStep 244439 = 366659) B366659
theorem B178967 : Blo 107783 178967 := bstep (se 1 (by rfl) ⟨134225, by rfl⟩ : syracuseStep 178967 = 268451) B268451
theorem B441139 : Blo 107783 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B244619 : Blo 107783 244619 := bstep (se 1 (by rfl) ⟨183464, by rfl⟩ : syracuseStep 244619 = 366929) B366929
theorem B375731 : Blo 107783 375731 := bstep (se 1 (by rfl) ⟨281798, by rfl⟩ : syracuseStep 375731 = 563597) B563597
theorem B244673 : Blo 107783 244673 := bstep (se 2 (by rfl) ⟨91752, by rfl⟩ : syracuseStep 244673 = 183505) B183505
theorem B277465 : Blo 107783 277465 := bstep (se 2 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 277465 = 208099) B208099
theorem B212033 : Blo 107783 212033 := bstep (se 2 (by rfl) ⟨79512, by rfl⟩ : syracuseStep 212033 = 159025) B159025
theorem B244889 : Blo 107783 244889 := bstep (se 2 (by rfl) ⟨91833, by rfl⟩ : syracuseStep 244889 = 183667) B183667
theorem B703667 : Blo 107783 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B376001 : Blo 107783 376001 := bstep (se 2 (by rfl) ⟨141000, by rfl⟩ : syracuseStep 376001 = 282001) B282001
theorem B244979 : Blo 107783 244979 := bstep (se 1 (by rfl) ⟨183734, by rfl⟩ : syracuseStep 244979 = 367469) B367469
theorem B245015 : Blo 107783 245015 := bstep (se 1 (by rfl) ⟨183761, by rfl⟩ : syracuseStep 245015 = 367523) B367523
theorem B474443 : Blo 107783 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B834947 : Blo 107783 834947 := bstep (se 1 (by rfl) ⟨626210, by rfl⟩ : syracuseStep 834947 = 1252421) B1252421
theorem B245195 : Blo 107783 245195 := bstep (se 1 (by rfl) ⟨183896, by rfl⟩ : syracuseStep 245195 = 367793) B367793
theorem B245249 : Blo 107783 245249 := bstep (se 2 (by rfl) ⟨91968, by rfl⟩ : syracuseStep 245249 = 183937) B183937
theorem B310873 : Blo 107783 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B245465 : Blo 107783 245465 := bstep (se 2 (by rfl) ⟨92049, by rfl⟩ : syracuseStep 245465 = 184099) B184099
theorem B376541 : Blo 107783 376541 := bstep (se 3 (by rfl) ⟨70601, by rfl⟩ : syracuseStep 376541 = 141203) B141203
theorem B245555 : Blo 107783 245555 := bstep (se 1 (by rfl) ⟨184166, by rfl⟩ : syracuseStep 245555 = 368333) B368333
theorem B245591 : Blo 107783 245591 := bstep (se 1 (by rfl) ⟨184193, by rfl⟩ : syracuseStep 245591 = 368387) B368387
theorem B2768741 : Blo 107783 2768741 := bstep (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) B519139
theorem B2473907 : Blo 107783 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B245771 : Blo 107783 245771 := bstep (se 1 (by rfl) ⟨184328, by rfl⟩ : syracuseStep 245771 = 368657) B368657
theorem B278579 : Blo 107783 278579 := bstep (se 1 (by rfl) ⟨208934, by rfl⟩ : syracuseStep 278579 = 417869) B417869
theorem B245825 : Blo 107783 245825 := bstep (se 2 (by rfl) ⟨92184, by rfl⟩ : syracuseStep 245825 = 184369) B184369
theorem B311489 : Blo 107783 311489 := bstep (se 2 (by rfl) ⟨116808, by rfl⟩ : syracuseStep 311489 = 233617) B233617
theorem B246041 : Blo 107783 246041 := bstep (se 2 (by rfl) ⟨92265, by rfl⟩ : syracuseStep 246041 = 184531) B184531
theorem B278873 : Blo 107783 278873 := bstep (se 2 (by rfl) ⟨104577, by rfl⟩ : syracuseStep 278873 = 209155) B209155
theorem B246131 : Blo 107783 246131 := bstep (se 1 (by rfl) ⟨184598, by rfl⟩ : syracuseStep 246131 = 369197) B369197
theorem B246167 : Blo 107783 246167 := bstep (se 1 (by rfl) ⟨184625, by rfl⟩ : syracuseStep 246167 = 369251) B369251
theorem B475571 : Blo 107783 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B442955 : Blo 107783 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B246347 : Blo 107783 246347 := bstep (se 1 (by rfl) ⟨184760, by rfl⟩ : syracuseStep 246347 = 369521) B369521
theorem B246401 : Blo 107783 246401 := bstep (se 2 (by rfl) ⟨92400, by rfl⟩ : syracuseStep 246401 = 184801) B184801
theorem B115339 : Blo 107783 115339 := bstep (se 1 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 115339 = 173009) B173009
theorem B410291 : Blo 107783 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B410305 : Blo 107783 410305 := bstep (se 2 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 410305 = 307729) B307729
theorem B836369 : Blo 107783 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B508717 : Blo 107783 508717 := bstep (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) B190769
theorem B246617 : Blo 107783 246617 := bstep (se 2 (by rfl) ⟨92481, by rfl⟩ : syracuseStep 246617 = 184963) B184963
theorem B672605 : Blo 107783 672605 := bstep (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) B252227
theorem B246707 : Blo 107783 246707 := bstep (se 1 (by rfl) ⟨185030, by rfl⟩ : syracuseStep 246707 = 370061) B370061
theorem B246743 : Blo 107783 246743 := bstep (se 1 (by rfl) ⟨185057, by rfl⟩ : syracuseStep 246743 = 370115) B370115
theorem B1262627 : Blo 107783 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B246923 : Blo 107783 246923 := bstep (se 1 (by rfl) ⟨185192, by rfl⟩ : syracuseStep 246923 = 370385) B370385
theorem B246977 : Blo 107783 246977 := bstep (se 2 (by rfl) ⟨92616, by rfl⟩ : syracuseStep 246977 = 185233) B185233
theorem B247193 : Blo 107783 247193 := bstep (se 2 (by rfl) ⟨92697, by rfl⟩ : syracuseStep 247193 = 185395) B185395
theorem B247283 : Blo 107783 247283 := bstep (se 1 (by rfl) ⟨185462, by rfl⟩ : syracuseStep 247283 = 370925) B370925
theorem B247319 : Blo 107783 247319 := bstep (se 1 (by rfl) ⟨185489, by rfl⟩ : syracuseStep 247319 = 370979) B370979
theorem B935489 : Blo 107783 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B1754693 : Blo 107783 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B771677 : Blo 107783 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B116407 : Blo 107783 116407 := bstep (se 1 (by rfl) ⟨87305, by rfl⟩ : syracuseStep 116407 = 174611) B174611
theorem B247499 : Blo 107783 247499 := bstep (se 1 (by rfl) ⟨185624, by rfl⟩ : syracuseStep 247499 = 371249) B371249
theorem B247553 : Blo 107783 247553 := bstep (se 2 (by rfl) ⟨92832, by rfl⟩ : syracuseStep 247553 = 185665) B185665
theorem B182027 : Blo 107783 182027 := bstep (se 1 (by rfl) ⟨136520, by rfl⟩ : syracuseStep 182027 = 273041) B273041
theorem B182155 : Blo 107783 182155 := bstep (se 1 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 182155 = 273233) B273233
theorem B280523 : Blo 107783 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B247769 : Blo 107783 247769 := bstep (se 2 (by rfl) ⟨92913, by rfl⟩ : syracuseStep 247769 = 185827) B185827
theorem B182297 : Blo 107783 182297 := bstep (se 2 (by rfl) ⟨68361, by rfl⟩ : syracuseStep 182297 = 136723) B136723
theorem B247859 : Blo 107783 247859 := bstep (se 1 (by rfl) ⟨185894, by rfl⟩ : syracuseStep 247859 = 371789) B371789
theorem B247895 : Blo 107783 247895 := bstep (se 1 (by rfl) ⟨185921, by rfl⟩ : syracuseStep 247895 = 371843) B371843
theorem B182425 : Blo 107783 182425 := bstep (se 2 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 182425 = 136819) B136819
theorem B313561 : Blo 107783 313561 := bstep (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) B235171
theorem B248075 : Blo 107783 248075 := bstep (se 1 (by rfl) ⟨186056, by rfl⟩ : syracuseStep 248075 = 372113) B372113
theorem B477485 : Blo 107783 477485 := bstep (se 3 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 477485 = 179057) B179057
theorem B248129 : Blo 107783 248129 := bstep (se 2 (by rfl) ⟨93048, by rfl⟩ : syracuseStep 248129 = 186097) B186097
theorem B117227 : Blo 107783 117227 := bstep (se 1 (by rfl) ⟨87920, by rfl⟩ : syracuseStep 117227 = 175841) B175841
theorem B248345 : Blo 107783 248345 := bstep (se 2 (by rfl) ⟨93129, by rfl⟩ : syracuseStep 248345 = 186259) B186259
theorem B412235 : Blo 107783 412235 := bstep (se 1 (by rfl) ⟨309176, by rfl⟩ : syracuseStep 412235 = 618353) B618353
theorem B412249 : Blo 107783 412249 := bstep (se 2 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 412249 = 309187) B309187
theorem B313949 : Blo 107783 313949 := bstep (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) B117731
theorem B248435 : Blo 107783 248435 := bstep (se 1 (by rfl) ⟨186326, by rfl⟩ : syracuseStep 248435 = 372653) B372653
theorem B1067651 : Blo 107783 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B248471 : Blo 107783 248471 := bstep (se 1 (by rfl) ⟨186353, by rfl⟩ : syracuseStep 248471 = 372707) B372707
theorem B510637 : Blo 107783 510637 := bstep (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) B191489
theorem B838349 : Blo 107783 838349 := bstep (se 3 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 838349 = 314381) B314381
theorem B182999 : Blo 107783 182999 := bstep (se 1 (by rfl) ⟨137249, by rfl⟩ : syracuseStep 182999 = 274499) B274499
theorem B805697 : Blo 107783 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B248651 : Blo 107783 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B183127 : Blo 107783 183127 := bstep (se 1 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 183127 = 274691) B274691
theorem B445277 : Blo 107783 445277 := bstep (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) B166979
theorem B248705 : Blo 107783 248705 := bstep (se 2 (by rfl) ⟨93264, by rfl⟩ : syracuseStep 248705 = 186529) B186529
theorem B281495 : Blo 107783 281495 := bstep (se 1 (by rfl) ⟨211121, by rfl⟩ : syracuseStep 281495 = 422243) B422243
theorem B248921 : Blo 107783 248921 := bstep (se 2 (by rfl) ⟨93345, by rfl⟩ : syracuseStep 248921 = 186691) B186691
theorem B150679 : Blo 107783 150679 := bstep (se 1 (by rfl) ⟨113009, by rfl⟩ : syracuseStep 150679 = 226019) B226019
theorem B838835 : Blo 107783 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B249011 : Blo 107783 249011 := bstep (se 1 (by rfl) ⟨186758, by rfl⟩ : syracuseStep 249011 = 373517) B373517
theorem B249047 : Blo 107783 249047 := bstep (se 1 (by rfl) ⟨186785, by rfl⟩ : syracuseStep 249047 = 373571) B373571
theorem B249227 : Blo 107783 249227 := bstep (se 1 (by rfl) ⟨186920, by rfl⟩ : syracuseStep 249227 = 373841) B373841
theorem B249281 : Blo 107783 249281 := bstep (se 2 (by rfl) ⟨93480, by rfl⟩ : syracuseStep 249281 = 186961) B186961
theorem B183755 : Blo 107783 183755 := bstep (se 1 (by rfl) ⟨137816, by rfl⟩ : syracuseStep 183755 = 275633) B275633
theorem B413207 : Blo 107783 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B282163 : Blo 107783 282163 := bstep (se 1 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 282163 = 423245) B423245
theorem B347723 : Blo 107783 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B183883 : Blo 107783 183883 := bstep (se 1 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 183883 = 275825) B275825
theorem B609893 : Blo 107783 609893 := bstep (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) B114355
theorem B118423 : Blo 107783 118423 := bstep (se 1 (by rfl) ⟨88817, by rfl⟩ : syracuseStep 118423 = 177635) B177635
theorem B249497 : Blo 107783 249497 := bstep (se 2 (by rfl) ⟨93561, by rfl⟩ : syracuseStep 249497 = 187123) B187123
theorem B282305 : Blo 107783 282305 := bstep (se 2 (by rfl) ⟨105864, by rfl⟩ : syracuseStep 282305 = 211729) B211729
theorem B184025 : Blo 107783 184025 := bstep (se 2 (by rfl) ⟨69009, by rfl⟩ : syracuseStep 184025 = 138019) B138019
theorem B249587 : Blo 107783 249587 := bstep (se 1 (by rfl) ⟨187190, by rfl⟩ : syracuseStep 249587 = 374381) B374381
theorem B249601 : Blo 107783 249601 := bstep (se 2 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 249601 = 187201) B187201
theorem B249623 : Blo 107783 249623 := bstep (se 1 (by rfl) ⟨187217, by rfl⟩ : syracuseStep 249623 = 374435) B374435
theorem B1265453 : Blo 107783 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B184153 : Blo 107783 184153 := bstep (se 2 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 184153 = 138115) B138115
theorem B118679 : Blo 107783 118679 := bstep (se 1 (by rfl) ⟨89009, by rfl⟩ : syracuseStep 118679 = 178019) B178019
theorem B905111 : Blo 107783 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B479155 : Blo 107783 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B446411 : Blo 107783 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B249803 : Blo 107783 249803 := bstep (se 1 (by rfl) ⟨187352, by rfl⟩ : syracuseStep 249803 = 374705) B374705
theorem B249857 : Blo 107783 249857 := bstep (se 2 (by rfl) ⟨93696, by rfl⟩ : syracuseStep 249857 = 187393) B187393
theorem B250073 : Blo 107783 250073 := bstep (se 2 (by rfl) ⟨93777, by rfl⟩ : syracuseStep 250073 = 187555) B187555
theorem B250163 : Blo 107783 250163 := bstep (se 1 (by rfl) ⟨187622, by rfl⟩ : syracuseStep 250163 = 375245) B375245
theorem B250199 : Blo 107783 250199 := bstep (se 1 (by rfl) ⟨187649, by rfl⟩ : syracuseStep 250199 = 375299) B375299
theorem B184727 : Blo 107783 184727 := bstep (se 1 (by rfl) ⟨138545, by rfl⟩ : syracuseStep 184727 = 277091) B277091
theorem B119243 : Blo 107783 119243 := bstep (se 1 (by rfl) ⟨89432, by rfl⟩ : syracuseStep 119243 = 178865) B178865
theorem B250379 : Blo 107783 250379 := bstep (se 1 (by rfl) ⟨187784, by rfl⟩ : syracuseStep 250379 = 375569) B375569
theorem B184855 : Blo 107783 184855 := bstep (se 1 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 184855 = 277283) B277283
theorem B250433 : Blo 107783 250433 := bstep (se 2 (by rfl) ⟨93912, by rfl⟩ : syracuseStep 250433 = 187825) B187825
theorem B840293 : Blo 107783 840293 := bstep (se 4 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 840293 = 157555) B157555
theorem B414467 : Blo 107783 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B250649 : Blo 107783 250649 := bstep (se 2 (by rfl) ⟨93993, by rfl⟩ : syracuseStep 250649 = 187987) B187987
theorem B250739 : Blo 107783 250739 := bstep (se 1 (by rfl) ⟨188054, by rfl⟩ : syracuseStep 250739 = 376109) B376109
theorem B250775 : Blo 107783 250775 := bstep (se 1 (by rfl) ⟨188081, by rfl⟩ : syracuseStep 250775 = 376163) B376163
theorem B840779 : Blo 107783 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B250955 : Blo 107783 250955 := bstep (se 1 (by rfl) ⟨188216, by rfl⟩ : syracuseStep 250955 = 376433) B376433
theorem B251009 : Blo 107783 251009 := bstep (se 2 (by rfl) ⟨94128, by rfl⟩ : syracuseStep 251009 = 188257) B188257
theorem B185483 : Blo 107783 185483 := bstep (se 1 (by rfl) ⟨139112, by rfl⟩ : syracuseStep 185483 = 278225) B278225
theorem B5002501 : Blo 107783 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B185611 : Blo 107783 185611 := bstep (se 1 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 185611 = 278417) B278417
theorem B251225 : Blo 107783 251225 := bstep (se 2 (by rfl) ⟨94209, by rfl⟩ : syracuseStep 251225 = 188419) B188419
theorem B185753 : Blo 107783 185753 := bstep (se 2 (by rfl) ⟨69657, by rfl⟩ : syracuseStep 185753 = 139315) B139315
theorem B251315 : Blo 107783 251315 := bstep (se 1 (by rfl) ⟨188486, by rfl⟩ : syracuseStep 251315 = 376973) B376973
theorem B316865 : Blo 107783 316865 := bstep (se 2 (by rfl) ⟨118824, by rfl⟩ : syracuseStep 316865 = 237649) B237649
theorem B251351 : Blo 107783 251351 := bstep (se 1 (by rfl) ⟨188513, by rfl⟩ : syracuseStep 251351 = 377027) B377027
theorem B185881 : Blo 107783 185881 := bstep (se 2 (by rfl) ⟨69705, by rfl⟩ : syracuseStep 185881 = 139411) B139411
theorem B448051 : Blo 107783 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B316979 : Blo 107783 316979 := bstep (se 1 (by rfl) ⟨237734, by rfl⟩ : syracuseStep 316979 = 475469) B475469
theorem B349913 : Blo 107783 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B2119409 : Blo 107783 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B350041 : Blo 107783 350041 := bstep (se 2 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 350041 = 262531) B262531
theorem B186455 : Blo 107783 186455 := bstep (se 1 (by rfl) ⟨139841, by rfl⟩ : syracuseStep 186455 = 279683) B279683
theorem B350297 : Blo 107783 350297 := bstep (se 2 (by rfl) ⟨131361, by rfl⟩ : syracuseStep 350297 = 262723) B262723
theorem B153751 : Blo 107783 153751 := bstep (se 1 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 153751 = 230627) B230627
theorem B186583 : Blo 107783 186583 := bstep (se 1 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 186583 = 279875) B279875
theorem B121387 : Blo 107783 121387 := bstep (se 1 (by rfl) ⟨91040, by rfl⟩ : syracuseStep 121387 = 182081) B182081
theorem B121495 : Blo 107783 121495 := bstep (se 1 (by rfl) ⟨91121, by rfl⟩ : syracuseStep 121495 = 182243) B182243
theorem B187031 : Blo 107783 187031 := bstep (se 1 (by rfl) ⟨140273, by rfl⟩ : syracuseStep 187031 = 280547) B280547
theorem B154315 : Blo 107783 154315 := bstep (se 1 (by rfl) ⟨115736, by rfl⟩ : syracuseStep 154315 = 231473) B231473
theorem B121675 : Blo 107783 121675 := bstep (se 1 (by rfl) ⟨91256, by rfl⟩ : syracuseStep 121675 = 182513) B182513
theorem B187211 : Blo 107783 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B121783 : Blo 107783 121783 := bstep (se 1 (by rfl) ⟨91337, by rfl⟩ : syracuseStep 121783 = 182675) B182675
theorem B187339 : Blo 107783 187339 := bstep (se 1 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 187339 = 281009) B281009
theorem B318487 : Blo 107783 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B187481 : Blo 107783 187481 := bstep (se 2 (by rfl) ⟨70305, by rfl⟩ : syracuseStep 187481 = 140611) B140611
theorem B121963 : Blo 107783 121963 := bstep (se 1 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 121963 = 182945) B182945
theorem B122071 : Blo 107783 122071 := bstep (se 1 (by rfl) ⟨91553, by rfl⟩ : syracuseStep 122071 = 183107) B183107
theorem B187609 : Blo 107783 187609 := bstep (se 2 (by rfl) ⟨70353, by rfl⟩ : syracuseStep 187609 = 140707) B140707
theorem B351553 : Blo 107783 351553 := bstep (se 2 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 351553 = 263665) B263665
theorem B122251 : Blo 107783 122251 := bstep (se 1 (by rfl) ⟨91688, by rfl⟩ : syracuseStep 122251 = 183377) B183377
theorem B122359 : Blo 107783 122359 := bstep (se 1 (by rfl) ⟨91769, by rfl⟩ : syracuseStep 122359 = 183539) B183539
theorem B548369 : Blo 107783 548369 := bstep (se 2 (by rfl) ⟨205638, by rfl⟩ : syracuseStep 548369 = 411277) B411277
theorem B122539 : Blo 107783 122539 := bstep (se 1 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 122539 = 183809) B183809
theorem B548531 : Blo 107783 548531 := bstep (se 1 (by rfl) ⟨411398, by rfl⟩ : syracuseStep 548531 = 822797) B822797
theorem B122647 : Blo 107783 122647 := bstep (se 1 (by rfl) ⟨91985, by rfl⟩ : syracuseStep 122647 = 183971) B183971
theorem B188183 : Blo 107783 188183 := bstep (se 1 (by rfl) ⟨141137, by rfl⟩ : syracuseStep 188183 = 282275) B282275
theorem B417581 : Blo 107783 417581 := bstep (se 3 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 417581 = 156593) B156593
theorem B1072997 : Blo 107783 1072997 := bstep (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) B201187
theorem B188311 : Blo 107783 188311 := bstep (se 1 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 188311 = 282467) B282467
theorem B122827 : Blo 107783 122827 := bstep (se 1 (by rfl) ⟨92120, by rfl⟩ : syracuseStep 122827 = 184241) B184241
theorem B942029 : Blo 107783 942029 := bstep (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) B353261
theorem B221195 : Blo 107783 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B122935 : Blo 107783 122935 := bstep (se 1 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 122935 = 184403) B184403
theorem B155801 : Blo 107783 155801 := bstep (se 2 (by rfl) ⟨58425, by rfl⟩ : syracuseStep 155801 = 116851) B116851
theorem B123115 : Blo 107783 123115 := bstep (se 1 (by rfl) ⟨92336, by rfl⟩ : syracuseStep 123115 = 184673) B184673
theorem B123223 : Blo 107783 123223 := bstep (se 1 (by rfl) ⟨92417, by rfl⟩ : syracuseStep 123223 = 184835) B184835
theorem B123403 : Blo 107783 123403 := bstep (se 1 (by rfl) ⟨92552, by rfl⟩ : syracuseStep 123403 = 185105) B185105
theorem B418355 : Blo 107783 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B123511 : Blo 107783 123511 := bstep (se 1 (by rfl) ⟨92633, by rfl⟩ : syracuseStep 123511 = 185267) B185267
theorem B615185 : Blo 107783 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B156439 : Blo 107783 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B123691 : Blo 107783 123691 := bstep (se 1 (by rfl) ⟨92768, by rfl⟩ : syracuseStep 123691 = 185537) B185537
theorem B123799 : Blo 107783 123799 := bstep (se 1 (by rfl) ⟨92849, by rfl⟩ : syracuseStep 123799 = 185699) B185699
theorem B451601 : Blo 107783 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B123979 : Blo 107783 123979 := bstep (se 1 (by rfl) ⟨92984, by rfl⟩ : syracuseStep 123979 = 185969) B185969
theorem B124087 : Blo 107783 124087 := bstep (se 1 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 124087 = 186131) B186131
theorem B124267 : Blo 107783 124267 := bstep (se 1 (by rfl) ⟨93200, by rfl⟩ : syracuseStep 124267 = 186401) B186401
theorem B1598899 : Blo 107783 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B124375 : Blo 107783 124375 := bstep (se 1 (by rfl) ⟨93281, by rfl⟩ : syracuseStep 124375 = 186563) B186563
theorem B157145 : Blo 107783 157145 := bstep (se 2 (by rfl) ⟨58929, by rfl⟩ : syracuseStep 157145 = 117859) B117859
theorem B550475 : Blo 107783 550475 := bstep (se 1 (by rfl) ⟨412856, by rfl⟩ : syracuseStep 550475 = 825713) B825713
theorem B157259 : Blo 107783 157259 := bstep (se 1 (by rfl) ⟨117944, by rfl⟩ : syracuseStep 157259 = 235889) B235889
theorem B124555 : Blo 107783 124555 := bstep (se 1 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 124555 = 186833) B186833
theorem B124663 : Blo 107783 124663 := bstep (se 1 (by rfl) ⟨93497, by rfl⟩ : syracuseStep 124663 = 186995) B186995
theorem B124843 : Blo 107783 124843 := bstep (se 1 (by rfl) ⟨93632, by rfl⟩ : syracuseStep 124843 = 187265) B187265
theorem B419843 : Blo 107783 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B124951 : Blo 107783 124951 := bstep (se 1 (by rfl) ⟨93713, by rfl⟩ : syracuseStep 124951 = 187427) B187427
theorem B157783 : Blo 107783 157783 := bstep (se 1 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 157783 = 236675) B236675
theorem B354397 : Blo 107783 354397 := bstep (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) B132899
theorem B125131 : Blo 107783 125131 := bstep (se 1 (by rfl) ⟨93848, by rfl⟩ : syracuseStep 125131 = 187697) B187697
theorem B223489 : Blo 107783 223489 := bstep (se 2 (by rfl) ⟨83808, by rfl⟩ : syracuseStep 223489 = 167617) B167617
theorem B846125 : Blo 107783 846125 := bstep (se 3 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 846125 = 317297) B317297
theorem B125239 : Blo 107783 125239 := bstep (se 1 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 125239 = 187859) B187859
theorem B420299 : Blo 107783 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B125419 : Blo 107783 125419 := bstep (se 1 (by rfl) ⟨94064, by rfl⟩ : syracuseStep 125419 = 188129) B188129
theorem B125527 : Blo 107783 125527 := bstep (se 1 (by rfl) ⟨94145, by rfl⟩ : syracuseStep 125527 = 188291) B188291
theorem B420497 : Blo 107783 420497 := bstep (se 2 (by rfl) ⟨157686, by rfl⟩ : syracuseStep 420497 = 315373) B315373
theorem B125707 : Blo 107783 125707 := bstep (se 1 (by rfl) ⟨94280, by rfl⟩ : syracuseStep 125707 = 188561) B188561
theorem B518987 : Blo 107783 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B158603 : Blo 107783 158603 := bstep (se 1 (by rfl) ⟨118952, by rfl⟩ : syracuseStep 158603 = 237905) B237905
theorem B322483 : Blo 107783 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B453853 : Blo 107783 453853 := bstep (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) B170195
theorem B552257 : Blo 107783 552257 := bstep (se 2 (by rfl) ⟨207096, by rfl⟩ : syracuseStep 552257 = 414193) B414193
theorem B421271 : Blo 107783 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B519641 : Blo 107783 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B1601117 : Blo 107783 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B421469 : Blo 107783 421469 := bstep (se 3 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 421469 = 158051) B158051
theorem B13758149 : Blo 107783 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B389009 : Blo 107783 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B192601 : Blo 107783 192601 := bstep (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) B144451
theorem B454987 : Blo 107783 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B1798807 : Blo 107783 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B291521 : Blo 107783 291521 := bstep (se 2 (by rfl) ⟨109320, by rfl⟩ : syracuseStep 291521 = 218641) B218641
theorem B422617 : Blo 107783 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B2847473 : Blo 107783 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1995637 : Blo 107783 1995637 := bstep (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) B187091
theorem B554201 : Blo 107783 554201 := bstep (se 2 (by rfl) ⟨207825, by rfl⟩ : syracuseStep 554201 = 415651) B415651
theorem B423427 : Blo 107783 423427 := bstep (se 1 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 423427 = 635141) B635141
theorem B882251 : Blo 107783 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B423731 : Blo 107783 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B161675 : Blo 107783 161675 := bstep (se 1 (by rfl) ⟨121256, by rfl⟩ : syracuseStep 161675 = 242513) B242513
theorem B161687 : Blo 107783 161687 := bstep (se 1 (by rfl) ⟨121265, by rfl⟩ : syracuseStep 161687 = 242531) B242531
theorem B161753 : Blo 107783 161753 := bstep (se 2 (by rfl) ⟨60657, by rfl⟩ : syracuseStep 161753 = 121315) B121315
theorem B620561 : Blo 107783 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B260147 : Blo 107783 260147 := bstep (se 1 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 260147 = 390221) B390221
theorem B161867 : Blo 107783 161867 := bstep (se 1 (by rfl) ⟨121400, by rfl⟩ : syracuseStep 161867 = 242801) B242801
theorem B161879 : Blo 107783 161879 := bstep (se 1 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 161879 = 242819) B242819
theorem B2586775 : Blo 107783 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B6715543 : Blo 107783 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B161945 : Blo 107783 161945 := bstep (se 2 (by rfl) ⟨60729, by rfl⟩ : syracuseStep 161945 = 121459) B121459
theorem B162059 : Blo 107783 162059 := bstep (se 1 (by rfl) ⟨121544, by rfl⟩ : syracuseStep 162059 = 243089) B243089
theorem B162071 : Blo 107783 162071 := bstep (se 1 (by rfl) ⟨121553, by rfl⟩ : syracuseStep 162071 = 243107) B243107
theorem B227659 : Blo 107783 227659 := bstep (se 1 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 227659 = 341489) B341489
theorem B162137 : Blo 107783 162137 := bstep (se 2 (by rfl) ⟨60801, by rfl⟩ : syracuseStep 162137 = 121603) B121603
theorem B948611 : Blo 107783 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B424385 : Blo 107783 424385 := bstep (se 2 (by rfl) ⟨159144, by rfl⟩ : syracuseStep 424385 = 318289) B318289
theorem B162251 : Blo 107783 162251 := bstep (se 1 (by rfl) ⟨121688, by rfl⟩ : syracuseStep 162251 = 243377) B243377
theorem B162263 : Blo 107783 162263 := bstep (se 1 (by rfl) ⟨121697, by rfl⟩ : syracuseStep 162263 = 243395) B243395
theorem B621017 : Blo 107783 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B162329 : Blo 107783 162329 := bstep (se 2 (by rfl) ⟨60873, by rfl⟩ : syracuseStep 162329 = 121747) B121747
theorem B784997 : Blo 107783 784997 := bstep (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) B147187
theorem B162443 : Blo 107783 162443 := bstep (se 1 (by rfl) ⟨121832, by rfl⟩ : syracuseStep 162443 = 243665) B243665
theorem B162455 : Blo 107783 162455 := bstep (se 1 (by rfl) ⟨121841, by rfl⟩ : syracuseStep 162455 = 243683) B243683
theorem B162521 : Blo 107783 162521 := bstep (se 2 (by rfl) ⟨60945, by rfl⟩ : syracuseStep 162521 = 121891) B121891
theorem B555821 : Blo 107783 555821 := bstep (se 3 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 555821 = 208433) B208433
theorem B162635 : Blo 107783 162635 := bstep (se 1 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 162635 = 243953) B243953
theorem B162647 : Blo 107783 162647 := bstep (se 1 (by rfl) ⟨121985, by rfl⟩ : syracuseStep 162647 = 243971) B243971
theorem B195443 : Blo 107783 195443 := bstep (se 1 (by rfl) ⟨146582, by rfl⟩ : syracuseStep 195443 = 293165) B293165
theorem B162713 : Blo 107783 162713 := bstep (se 2 (by rfl) ⟨61017, by rfl⟩ : syracuseStep 162713 = 122035) B122035
theorem B162827 : Blo 107783 162827 := bstep (se 1 (by rfl) ⟨122120, by rfl⟩ : syracuseStep 162827 = 244241) B244241
theorem B162839 : Blo 107783 162839 := bstep (se 1 (by rfl) ⟨122129, by rfl⟩ : syracuseStep 162839 = 244259) B244259
theorem B162905 : Blo 107783 162905 := bstep (se 2 (by rfl) ⟨61089, by rfl⟩ : syracuseStep 162905 = 122179) B122179
theorem B163019 : Blo 107783 163019 := bstep (se 1 (by rfl) ⟨122264, by rfl⟩ : syracuseStep 163019 = 244529) B244529
theorem B163031 : Blo 107783 163031 := bstep (se 1 (by rfl) ⟨122273, by rfl⟩ : syracuseStep 163031 = 244547) B244547
theorem B163097 : Blo 107783 163097 := bstep (se 2 (by rfl) ⟨61161, by rfl⟩ : syracuseStep 163097 = 122323) B122323
theorem B163211 : Blo 107783 163211 := bstep (se 1 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 163211 = 244817) B244817
theorem B163223 : Blo 107783 163223 := bstep (se 1 (by rfl) ⟨122417, by rfl⟩ : syracuseStep 163223 = 244835) B244835
theorem B261569 : Blo 107783 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B163289 : Blo 107783 163289 := bstep (se 2 (by rfl) ⟨61233, by rfl⟩ : syracuseStep 163289 = 122467) B122467
theorem B163403 : Blo 107783 163403 := bstep (se 1 (by rfl) ⟨122552, by rfl⟩ : syracuseStep 163403 = 245105) B245105
theorem B163415 : Blo 107783 163415 := bstep (se 1 (by rfl) ⟨122561, by rfl⟩ : syracuseStep 163415 = 245123) B245123
theorem B163481 : Blo 107783 163481 := bstep (se 2 (by rfl) ⟨61305, by rfl⟩ : syracuseStep 163481 = 122611) B122611
theorem B163595 : Blo 107783 163595 := bstep (se 1 (by rfl) ⟨122696, by rfl⟩ : syracuseStep 163595 = 245393) B245393
theorem B163607 : Blo 107783 163607 := bstep (se 1 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 163607 = 245411) B245411
theorem B163673 : Blo 107783 163673 := bstep (se 2 (by rfl) ⟨61377, by rfl⟩ : syracuseStep 163673 = 122755) B122755
theorem B196481 : Blo 107783 196481 := bstep (se 2 (by rfl) ⟨73680, by rfl⟩ : syracuseStep 196481 = 147361) B147361
theorem B1867697 : Blo 107783 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B1343411 : Blo 107783 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B163787 : Blo 107783 163787 := bstep (se 1 (by rfl) ⟨122840, by rfl⟩ : syracuseStep 163787 = 245681) B245681
theorem B163799 : Blo 107783 163799 := bstep (se 1 (by rfl) ⟨122849, by rfl⟩ : syracuseStep 163799 = 245699) B245699
theorem B163847 : Blo 107783 163847 := bstep (se 1 (by rfl) ⟨122885, by rfl⟩ : syracuseStep 163847 = 245771) B245771
theorem B589853 : Blo 107783 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B163883 : Blo 107783 163883 := bstep (se 1 (by rfl) ⟨122912, by rfl⟩ : syracuseStep 163883 = 245825) B245825
theorem B557117 : Blo 107783 557117 := bstep (se 3 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 557117 = 208919) B208919
theorem B163913 : Blo 107783 163913 := bstep (se 2 (by rfl) ⟨61467, by rfl⟩ : syracuseStep 163913 = 122935) B122935
theorem B164027 : Blo 107783 164027 := bstep (se 1 (by rfl) ⟨123020, by rfl⟩ : syracuseStep 164027 = 246041) B246041
theorem B164087 : Blo 107783 164087 := bstep (se 1 (by rfl) ⟨123065, by rfl⟩ : syracuseStep 164087 = 246131) B246131
theorem B262415 : Blo 107783 262415 := bstep (se 1 (by rfl) ⟨196811, by rfl⟩ : syracuseStep 262415 = 393623) B393623
theorem B164111 : Blo 107783 164111 := bstep (se 1 (by rfl) ⟨123083, by rfl⟩ : syracuseStep 164111 = 246167) B246167
theorem B164153 : Blo 107783 164153 := bstep (se 2 (by rfl) ⟨61557, by rfl⟩ : syracuseStep 164153 = 123115) B123115
theorem B164231 : Blo 107783 164231 := bstep (se 1 (by rfl) ⟨123173, by rfl⟩ : syracuseStep 164231 = 246347) B246347
theorem B164267 : Blo 107783 164267 := bstep (se 1 (by rfl) ⟨123200, by rfl⟩ : syracuseStep 164267 = 246401) B246401
theorem B164297 : Blo 107783 164297 := bstep (se 2 (by rfl) ⟨61611, by rfl⟩ : syracuseStep 164297 = 123223) B123223
theorem B1409501 : Blo 107783 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B557579 : Blo 107783 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B164411 : Blo 107783 164411 := bstep (se 1 (by rfl) ⟨123308, by rfl⟩ : syracuseStep 164411 = 246617) B246617
theorem B164471 : Blo 107783 164471 := bstep (se 1 (by rfl) ⟨123353, by rfl⟩ : syracuseStep 164471 = 246707) B246707
theorem B164495 : Blo 107783 164495 := bstep (se 1 (by rfl) ⟨123371, by rfl⟩ : syracuseStep 164495 = 246743) B246743
theorem B164537 : Blo 107783 164537 := bstep (se 2 (by rfl) ⟨61701, by rfl⟩ : syracuseStep 164537 = 123403) B123403
theorem B164615 : Blo 107783 164615 := bstep (se 1 (by rfl) ⟨123461, by rfl⟩ : syracuseStep 164615 = 246923) B246923
theorem B164651 : Blo 107783 164651 := bstep (se 1 (by rfl) ⟨123488, by rfl⟩ : syracuseStep 164651 = 246977) B246977
theorem B164681 : Blo 107783 164681 := bstep (se 2 (by rfl) ⟨61755, by rfl⟩ : syracuseStep 164681 = 123511) B123511
theorem B1114955 : Blo 107783 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B164795 : Blo 107783 164795 := bstep (se 1 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 164795 = 247193) B247193
theorem B164855 : Blo 107783 164855 := bstep (se 1 (by rfl) ⟨123641, by rfl⟩ : syracuseStep 164855 = 247283) B247283
theorem B164879 : Blo 107783 164879 := bstep (se 1 (by rfl) ⟨123659, by rfl⟩ : syracuseStep 164879 = 247319) B247319
theorem B623659 : Blo 107783 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B164921 : Blo 107783 164921 := bstep (se 2 (by rfl) ⟨61845, by rfl⟩ : syracuseStep 164921 = 123691) B123691
theorem B590935 : Blo 107783 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B164999 : Blo 107783 164999 := bstep (se 1 (by rfl) ⟨123749, by rfl⟩ : syracuseStep 164999 = 247499) B247499
theorem B165035 : Blo 107783 165035 := bstep (se 1 (by rfl) ⟨123776, by rfl⟩ : syracuseStep 165035 = 247553) B247553
theorem B165065 : Blo 107783 165065 := bstep (se 2 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 165065 = 123799) B123799
theorem B263483 : Blo 107783 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B165179 : Blo 107783 165179 := bstep (se 1 (by rfl) ⟨123884, by rfl⟩ : syracuseStep 165179 = 247769) B247769
theorem B165239 : Blo 107783 165239 := bstep (se 1 (by rfl) ⟨123929, by rfl⟩ : syracuseStep 165239 = 247859) B247859
theorem B165263 : Blo 107783 165263 := bstep (se 1 (by rfl) ⟨123947, by rfl⟩ : syracuseStep 165263 = 247895) B247895
theorem B165305 : Blo 107783 165305 := bstep (se 2 (by rfl) ⟨61989, by rfl⟩ : syracuseStep 165305 = 123979) B123979
theorem B165383 : Blo 107783 165383 := bstep (se 1 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 165383 = 248075) B248075
theorem B1181213 : Blo 107783 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B886301 : Blo 107783 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B165419 : Blo 107783 165419 := bstep (se 1 (by rfl) ⟨124064, by rfl⟩ : syracuseStep 165419 = 248129) B248129
theorem B165449 : Blo 107783 165449 := bstep (se 2 (by rfl) ⟨62043, by rfl⟩ : syracuseStep 165449 = 124087) B124087
theorem B165563 : Blo 107783 165563 := bstep (se 1 (by rfl) ⟨124172, by rfl⟩ : syracuseStep 165563 = 248345) B248345
theorem B165623 : Blo 107783 165623 := bstep (se 1 (by rfl) ⟨124217, by rfl⟩ : syracuseStep 165623 = 248435) B248435
theorem B165647 : Blo 107783 165647 := bstep (se 1 (by rfl) ⟨124235, by rfl⟩ : syracuseStep 165647 = 248471) B248471
theorem B558899 : Blo 107783 558899 := bstep (se 1 (by rfl) ⟨419174, by rfl⟩ : syracuseStep 558899 = 838349) B838349
theorem B165689 : Blo 107783 165689 := bstep (se 2 (by rfl) ⟨62133, by rfl⟩ : syracuseStep 165689 = 124267) B124267
theorem B165767 : Blo 107783 165767 := bstep (se 1 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 165767 = 248651) B248651
theorem B2131865 : Blo 107783 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B165803 : Blo 107783 165803 := bstep (se 1 (by rfl) ⟨124352, by rfl⟩ : syracuseStep 165803 = 248705) B248705
theorem B165833 : Blo 107783 165833 := bstep (se 2 (by rfl) ⟨62187, by rfl⟩ : syracuseStep 165833 = 124375) B124375
theorem B133111 : Blo 107783 133111 := bstep (se 1 (by rfl) ⟨99833, by rfl⟩ : syracuseStep 133111 = 199667) B199667
theorem B165947 : Blo 107783 165947 := bstep (se 1 (by rfl) ⟨124460, by rfl⟩ : syracuseStep 165947 = 248921) B248921
theorem B559223 : Blo 107783 559223 := bstep (se 1 (by rfl) ⟨419417, by rfl⟩ : syracuseStep 559223 = 838835) B838835
theorem B166007 : Blo 107783 166007 := bstep (se 1 (by rfl) ⟨124505, by rfl⟩ : syracuseStep 166007 = 249011) B249011
theorem B133255 : Blo 107783 133255 := bstep (se 1 (by rfl) ⟨99941, by rfl⟩ : syracuseStep 133255 = 199883) B199883
theorem B166031 : Blo 107783 166031 := bstep (se 1 (by rfl) ⟨124523, by rfl⟩ : syracuseStep 166031 = 249047) B249047
theorem B264377 : Blo 107783 264377 := bstep (se 2 (by rfl) ⟨99141, by rfl⟩ : syracuseStep 264377 = 198283) B198283
theorem B166073 : Blo 107783 166073 := bstep (se 2 (by rfl) ⟨62277, by rfl⟩ : syracuseStep 166073 = 124555) B124555
theorem B166151 : Blo 107783 166151 := bstep (se 1 (by rfl) ⟨124613, by rfl⟩ : syracuseStep 166151 = 249227) B249227
theorem B166187 : Blo 107783 166187 := bstep (se 1 (by rfl) ⟨124640, by rfl⟩ : syracuseStep 166187 = 249281) B249281
theorem B166217 : Blo 107783 166217 := bstep (se 2 (by rfl) ⟨62331, by rfl⟩ : syracuseStep 166217 = 124663) B124663
theorem B231815 : Blo 107783 231815 := bstep (se 1 (by rfl) ⟨173861, by rfl⟩ : syracuseStep 231815 = 347723) B347723
theorem B166331 : Blo 107783 166331 := bstep (se 1 (by rfl) ⟨124748, by rfl⟩ : syracuseStep 166331 = 249497) B249497
theorem B395729 : Blo 107783 395729 := bstep (se 2 (by rfl) ⟨148398, by rfl⟩ : syracuseStep 395729 = 296797) B296797
theorem B625117 : Blo 107783 625117 := bstep (se 3 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 625117 = 234419) B234419
theorem B166391 : Blo 107783 166391 := bstep (se 1 (by rfl) ⟨124793, by rfl⟩ : syracuseStep 166391 = 249587) B249587
theorem B166415 : Blo 107783 166415 := bstep (se 1 (by rfl) ⟨124811, by rfl⟩ : syracuseStep 166415 = 249623) B249623
theorem B166457 : Blo 107783 166457 := bstep (se 2 (by rfl) ⟨62421, by rfl⟩ : syracuseStep 166457 = 124843) B124843
theorem B297607 : Blo 107783 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B166535 : Blo 107783 166535 := bstep (se 1 (by rfl) ⟨124901, by rfl⟩ : syracuseStep 166535 = 249803) B249803
theorem B166571 : Blo 107783 166571 := bstep (se 1 (by rfl) ⟨124928, by rfl⟩ : syracuseStep 166571 = 249857) B249857
theorem B166601 : Blo 107783 166601 := bstep (se 2 (by rfl) ⟨62475, by rfl⟩ : syracuseStep 166601 = 124951) B124951
theorem B166715 : Blo 107783 166715 := bstep (se 1 (by rfl) ⟨125036, by rfl⟩ : syracuseStep 166715 = 250073) B250073
theorem B166775 : Blo 107783 166775 := bstep (se 1 (by rfl) ⟨125081, by rfl⟩ : syracuseStep 166775 = 250163) B250163
theorem B166799 : Blo 107783 166799 := bstep (se 1 (by rfl) ⟨125099, by rfl⟩ : syracuseStep 166799 = 250199) B250199
theorem B166841 : Blo 107783 166841 := bstep (se 2 (by rfl) ⟨62565, by rfl⟩ : syracuseStep 166841 = 125131) B125131
theorem B297985 : Blo 107783 297985 := bstep (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) B223489
theorem B166919 : Blo 107783 166919 := bstep (se 1 (by rfl) ⟨125189, by rfl⟩ : syracuseStep 166919 = 250379) B250379
theorem B166955 : Blo 107783 166955 := bstep (se 1 (by rfl) ⟨125216, by rfl⟩ : syracuseStep 166955 = 250433) B250433
theorem B560195 : Blo 107783 560195 := bstep (se 1 (by rfl) ⟨420146, by rfl⟩ : syracuseStep 560195 = 840293) B840293
theorem B166985 : Blo 107783 166985 := bstep (se 2 (by rfl) ⟨62619, by rfl⟩ : syracuseStep 166985 = 125239) B125239
theorem B167099 : Blo 107783 167099 := bstep (se 1 (by rfl) ⟨125324, by rfl⟩ : syracuseStep 167099 = 250649) B250649
theorem B167159 : Blo 107783 167159 := bstep (se 1 (by rfl) ⟨125369, by rfl⟩ : syracuseStep 167159 = 250739) B250739
theorem B167183 : Blo 107783 167183 := bstep (se 1 (by rfl) ⟨125387, by rfl⟩ : syracuseStep 167183 = 250775) B250775
theorem B167225 : Blo 107783 167225 := bstep (se 2 (by rfl) ⟨62709, by rfl⟩ : syracuseStep 167225 = 125419) B125419
theorem B396679 : Blo 107783 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B560519 : Blo 107783 560519 := bstep (se 1 (by rfl) ⟨420389, by rfl⟩ : syracuseStep 560519 = 840779) B840779
theorem B167303 : Blo 107783 167303 := bstep (se 1 (by rfl) ⟨125477, by rfl⟩ : syracuseStep 167303 = 250955) B250955
theorem B167339 : Blo 107783 167339 := bstep (se 1 (by rfl) ⟨125504, by rfl⟩ : syracuseStep 167339 = 251009) B251009
theorem B167369 : Blo 107783 167369 := bstep (se 2 (by rfl) ⟨62763, by rfl⟩ : syracuseStep 167369 = 125527) B125527
theorem B462347 : Blo 107783 462347 := bstep (se 1 (by rfl) ⟨346760, by rfl⟩ : syracuseStep 462347 = 693521) B693521
theorem B167483 : Blo 107783 167483 := bstep (se 1 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 167483 = 251225) B251225
theorem B167543 : Blo 107783 167543 := bstep (se 1 (by rfl) ⟨125657, by rfl⟩ : syracuseStep 167543 = 251315) B251315
theorem B167567 : Blo 107783 167567 := bstep (se 1 (by rfl) ⟨125675, by rfl⟩ : syracuseStep 167567 = 251351) B251351
theorem B167609 : Blo 107783 167609 := bstep (se 2 (by rfl) ⟨62853, by rfl⟩ : syracuseStep 167609 = 125707) B125707
theorem B233275 : Blo 107783 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B1412939 : Blo 107783 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B429977 : Blo 107783 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B233531 : Blo 107783 233531 := bstep (se 1 (by rfl) ⟨175148, by rfl⟩ : syracuseStep 233531 = 350297) B350297
theorem B201079 : Blo 107783 201079 := bstep (se 1 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 201079 = 301619) B301619
theorem B364985 : Blo 107783 364985 := bstep (se 2 (by rfl) ⟨136869, by rfl⟩ : syracuseStep 364985 = 273739) B273739
theorem B267067 : Blo 107783 267067 := bstep (se 1 (by rfl) ⟨200300, by rfl⟩ : syracuseStep 267067 = 400601) B400601
theorem B332801 : Blo 107783 332801 := bstep (se 2 (by rfl) ⟨124800, by rfl⟩ : syracuseStep 332801 = 249601) B249601
theorem B365579 : Blo 107783 365579 := bstep (se 1 (by rfl) ⟨274184, by rfl⟩ : syracuseStep 365579 = 548369) B548369
theorem B300061 : Blo 107783 300061 := bstep (se 3 (by rfl) ⟨56261, by rfl⟩ : syracuseStep 300061 = 112523) B112523
theorem B365687 : Blo 107783 365687 := bstep (se 1 (by rfl) ⟨274265, by rfl⟩ : syracuseStep 365687 = 548531) B548531
theorem B628019 : Blo 107783 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B595259 : Blo 107783 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B333143 : Blo 107783 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B398915 : Blo 107783 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B366281 : Blo 107783 366281 := bstep (se 2 (by rfl) ⟨137355, by rfl⟩ : syracuseStep 366281 = 274711) B274711
theorem B1054579 : Blo 107783 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B301067 : Blo 107783 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B2398409 : Blo 107783 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B563489 : Blo 107783 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B366983 : Blo 107783 366983 := bstep (se 1 (by rfl) ⟨275237, by rfl⟩ : syracuseStep 366983 = 550475) B550475
theorem B2660849 : Blo 107783 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B629309 : Blo 107783 629309 := bstep (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) B235991
theorem B367361 : Blo 107783 367361 := bstep (se 2 (by rfl) ⟨137760, by rfl⟩ : syracuseStep 367361 = 275521) B275521
theorem B564083 : Blo 107783 564083 := bstep (se 1 (by rfl) ⟨423062, by rfl⟩ : syracuseStep 564083 = 846125) B846125
theorem B630017 : Blo 107783 630017 := bstep (se 2 (by rfl) ⟨236256, by rfl⟩ : syracuseStep 630017 = 472513) B472513
theorem B564569 : Blo 107783 564569 := bstep (se 2 (by rfl) ⟨211713, by rfl⟩ : syracuseStep 564569 = 423427) B423427
theorem B597401 : Blo 107783 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B138667 : Blo 107783 138667 := bstep (se 1 (by rfl) ⟨104000, by rfl⟩ : syracuseStep 138667 = 208001) B208001
theorem B597527 : Blo 107783 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B368171 : Blo 107783 368171 := bstep (se 1 (by rfl) ⟨276128, by rfl⟩ : syracuseStep 368171 = 552257) B552257
theorem B466499 : Blo 107783 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B1187405 : Blo 107783 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B466721 : Blo 107783 466721 := bstep (se 2 (by rfl) ⟨175020, by rfl⟩ : syracuseStep 466721 = 350041) B350041
theorem B466823 : Blo 107783 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B1187747 : Blo 107783 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B205001 : Blo 107783 205001 := bstep (se 2 (by rfl) ⟨76875, by rfl⟩ : syracuseStep 205001 = 153751) B153751
theorem B3449033 : Blo 107783 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B8954057 : Blo 107783 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B139639 : Blo 107783 139639 := bstep (se 1 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 139639 = 209459) B209459
theorem B303545 : Blo 107783 303545 := bstep (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) B227659
theorem B1876445 : Blo 107783 1876445 := bstep (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) B703667
theorem B795203 : Blo 107783 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B139963 : Blo 107783 139963 := bstep (se 1 (by rfl) ⟨104972, by rfl⟩ : syracuseStep 139963 = 209945) B209945
theorem B369467 : Blo 107783 369467 := bstep (se 1 (by rfl) ⟨277100, by rfl⟩ : syracuseStep 369467 = 554201) B554201
theorem B205715 : Blo 107783 205715 := bstep (se 1 (by rfl) ⟨154286, by rfl⟩ : syracuseStep 205715 = 308573) B308573
theorem B205753 : Blo 107783 205753 := bstep (se 2 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 205753 = 154315) B154315
theorem B1778699 : Blo 107783 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B7611479 : Blo 107783 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B697517 : Blo 107783 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B107783 : Blo 107783 107783 := bstep (se 1 (by rfl) ⟨80837, by rfl⟩ : syracuseStep 107783 = 161675) B161675
theorem B107791 : Blo 107783 107791 := bstep (se 1 (by rfl) ⟨80843, by rfl⟩ : syracuseStep 107791 = 161687) B161687
theorem B369953 : Blo 107783 369953 := bstep (se 2 (by rfl) ⟨138732, by rfl⟩ : syracuseStep 369953 = 277465) B277465
theorem B107835 : Blo 107783 107835 := bstep (se 1 (by rfl) ⟨80876, by rfl⟩ : syracuseStep 107835 = 161753) B161753
theorem B173431 : Blo 107783 173431 := bstep (se 1 (by rfl) ⟨130073, by rfl⟩ : syracuseStep 173431 = 260147) B260147
theorem B107911 : Blo 107783 107911 := bstep (se 1 (by rfl) ⟨80933, by rfl⟩ : syracuseStep 107911 = 161867) B161867
theorem B107919 : Blo 107783 107919 := bstep (se 1 (by rfl) ⟨80939, by rfl⟩ : syracuseStep 107919 = 161879) B161879
theorem B107963 : Blo 107783 107963 := bstep (se 1 (by rfl) ⟨80972, by rfl⟩ : syracuseStep 107963 = 161945) B161945
theorem B108039 : Blo 107783 108039 := bstep (se 1 (by rfl) ⟨81029, by rfl⟩ : syracuseStep 108039 = 162059) B162059
theorem B108047 : Blo 107783 108047 := bstep (se 1 (by rfl) ⟨81035, by rfl⟩ : syracuseStep 108047 = 162071) B162071
theorem B108091 : Blo 107783 108091 := bstep (se 1 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 108091 = 162137) B162137
theorem B632407 : Blo 107783 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B108167 : Blo 107783 108167 := bstep (se 1 (by rfl) ⟨81125, by rfl⟩ : syracuseStep 108167 = 162251) B162251
theorem B140935 : Blo 107783 140935 := bstep (se 1 (by rfl) ⟨105701, by rfl⟩ : syracuseStep 140935 = 211403) B211403
theorem B108175 : Blo 107783 108175 := bstep (se 1 (by rfl) ⟨81131, by rfl⟩ : syracuseStep 108175 = 162263) B162263
theorem B108219 : Blo 107783 108219 := bstep (se 1 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 108219 = 162329) B162329
theorem B468737 : Blo 107783 468737 := bstep (se 2 (by rfl) ⟨175776, by rfl⟩ : syracuseStep 468737 = 351553) B351553
theorem B108295 : Blo 107783 108295 := bstep (se 1 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 108295 = 162443) B162443
theorem B108303 : Blo 107783 108303 := bstep (se 1 (by rfl) ⟨81227, by rfl⟩ : syracuseStep 108303 = 162455) B162455
theorem B108347 : Blo 107783 108347 := bstep (se 1 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 108347 = 162521) B162521
theorem B370547 : Blo 107783 370547 := bstep (se 1 (by rfl) ⟨277910, by rfl⟩ : syracuseStep 370547 = 555821) B555821
theorem B26388341 : Blo 107783 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B108423 : Blo 107783 108423 := bstep (se 1 (by rfl) ⟨81317, by rfl⟩ : syracuseStep 108423 = 162635) B162635
theorem B108431 : Blo 107783 108431 := bstep (se 1 (by rfl) ⟨81323, by rfl⟩ : syracuseStep 108431 = 162647) B162647
theorem B108475 : Blo 107783 108475 := bstep (se 1 (by rfl) ⟨81356, by rfl⟩ : syracuseStep 108475 = 162713) B162713
theorem B108551 : Blo 107783 108551 := bstep (se 1 (by rfl) ⟨81413, by rfl⟩ : syracuseStep 108551 = 162827) B162827
theorem B108559 : Blo 107783 108559 := bstep (se 1 (by rfl) ⟨81419, by rfl⟩ : syracuseStep 108559 = 162839) B162839
theorem B141355 : Blo 107783 141355 := bstep (se 1 (by rfl) ⟨106016, by rfl⟩ : syracuseStep 141355 = 212033) B212033
theorem B108603 : Blo 107783 108603 := bstep (se 1 (by rfl) ⟨81452, by rfl⟩ : syracuseStep 108603 = 162905) B162905
theorem B108679 : Blo 107783 108679 := bstep (se 1 (by rfl) ⟨81509, by rfl⟩ : syracuseStep 108679 = 163019) B163019
theorem B108687 : Blo 107783 108687 := bstep (se 1 (by rfl) ⟨81515, by rfl⟩ : syracuseStep 108687 = 163031) B163031
theorem B108731 : Blo 107783 108731 := bstep (se 1 (by rfl) ⟨81548, by rfl⟩ : syracuseStep 108731 = 163097) B163097
theorem B108807 : Blo 107783 108807 := bstep (se 1 (by rfl) ⟨81605, by rfl⟩ : syracuseStep 108807 = 163211) B163211
theorem B108815 : Blo 107783 108815 := bstep (se 1 (by rfl) ⟨81611, by rfl⟩ : syracuseStep 108815 = 163223) B163223
theorem B3909941 : Blo 107783 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B108859 : Blo 107783 108859 := bstep (se 1 (by rfl) ⟨81644, by rfl⟩ : syracuseStep 108859 = 163289) B163289
theorem B108935 : Blo 107783 108935 := bstep (se 1 (by rfl) ⟨81701, by rfl⟩ : syracuseStep 108935 = 163403) B163403
theorem B108943 : Blo 107783 108943 := bstep (se 1 (by rfl) ⟨81707, by rfl⟩ : syracuseStep 108943 = 163415) B163415
theorem B108987 : Blo 107783 108987 := bstep (se 1 (by rfl) ⟨81740, by rfl⟩ : syracuseStep 108987 = 163481) B163481
theorem B109063 : Blo 107783 109063 := bstep (se 1 (by rfl) ⟨81797, by rfl⟩ : syracuseStep 109063 = 163595) B163595
theorem B109071 : Blo 107783 109071 := bstep (se 1 (by rfl) ⟨81803, by rfl⟩ : syracuseStep 109071 = 163607) B163607
theorem B272929 : Blo 107783 272929 := bstep (se 2 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 272929 = 204697) B204697
theorem B109115 : Blo 107783 109115 := bstep (se 1 (by rfl) ⟨81836, by rfl⟩ : syracuseStep 109115 = 163673) B163673
theorem B1845827 : Blo 107783 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B895607 : Blo 107783 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B109191 : Blo 107783 109191 := bstep (se 1 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 109191 = 163787) B163787
theorem B109199 : Blo 107783 109199 := bstep (se 1 (by rfl) ⟨81899, by rfl⟩ : syracuseStep 109199 = 163799) B163799
theorem B109243 : Blo 107783 109243 := bstep (se 1 (by rfl) ⟨81932, by rfl⟩ : syracuseStep 109243 = 163865) B163865
theorem B109319 : Blo 107783 109319 := bstep (se 1 (by rfl) ⟨81989, by rfl⟩ : syracuseStep 109319 = 163979) B163979
theorem B109327 : Blo 107783 109327 := bstep (se 1 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 109327 = 163991) B163991
theorem B207659 : Blo 107783 207659 := bstep (se 1 (by rfl) ⟨155744, by rfl⟩ : syracuseStep 207659 = 311489) B311489
theorem B109371 : Blo 107783 109371 := bstep (se 1 (by rfl) ⟨82028, by rfl⟩ : syracuseStep 109371 = 164057) B164057
theorem B109447 : Blo 107783 109447 := bstep (se 1 (by rfl) ⟨82085, by rfl⟩ : syracuseStep 109447 = 164171) B164171
theorem B109455 : Blo 107783 109455 := bstep (se 1 (by rfl) ⟨82091, by rfl⟩ : syracuseStep 109455 = 164183) B164183
theorem B535481 : Blo 107783 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B109499 : Blo 107783 109499 := bstep (se 1 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 109499 = 164249) B164249
theorem B109575 : Blo 107783 109575 := bstep (se 1 (by rfl) ⟨82181, by rfl⟩ : syracuseStep 109575 = 164363) B164363
theorem B109583 : Blo 107783 109583 := bstep (se 1 (by rfl) ⟨82187, by rfl⟩ : syracuseStep 109583 = 164375) B164375
theorem B109627 : Blo 107783 109627 := bstep (se 1 (by rfl) ⟨82220, by rfl⟩ : syracuseStep 109627 = 164441) B164441
theorem B371773 : Blo 107783 371773 := bstep (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) B139415
theorem B273527 : Blo 107783 273527 := bstep (se 1 (by rfl) ⟨205145, by rfl⟩ : syracuseStep 273527 = 410291) B410291
theorem B109703 : Blo 107783 109703 := bstep (se 1 (by rfl) ⟨82277, by rfl⟩ : syracuseStep 109703 = 164555) B164555
theorem B109711 : Blo 107783 109711 := bstep (se 1 (by rfl) ⟨82283, by rfl⟩ : syracuseStep 109711 = 164567) B164567
theorem B109755 : Blo 107783 109755 := bstep (se 1 (by rfl) ⟨82316, by rfl⟩ : syracuseStep 109755 = 164633) B164633
theorem B109831 : Blo 107783 109831 := bstep (se 1 (by rfl) ⟨82373, by rfl⟩ : syracuseStep 109831 = 164747) B164747
theorem B109839 : Blo 107783 109839 := bstep (se 1 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 109839 = 164759) B164759
theorem B109883 : Blo 107783 109883 := bstep (se 1 (by rfl) ⟨82412, by rfl⟩ : syracuseStep 109883 = 164825) B164825
theorem B109959 : Blo 107783 109959 := bstep (se 1 (by rfl) ⟨82469, by rfl⟩ : syracuseStep 109959 = 164939) B164939
theorem B109967 : Blo 107783 109967 := bstep (se 1 (by rfl) ⟨82475, by rfl⟩ : syracuseStep 109967 = 164951) B164951
theorem B110011 : Blo 107783 110011 := bstep (se 1 (by rfl) ⟨82508, by rfl⟩ : syracuseStep 110011 = 165017) B165017
theorem B404945 : Blo 107783 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B110087 : Blo 107783 110087 := bstep (se 1 (by rfl) ⟨82565, by rfl⟩ : syracuseStep 110087 = 165131) B165131
theorem B110095 : Blo 107783 110095 := bstep (se 1 (by rfl) ⟨82571, by rfl⟩ : syracuseStep 110095 = 165143) B165143
theorem B634391 : Blo 107783 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B110139 : Blo 107783 110139 := bstep (se 1 (by rfl) ⟨82604, by rfl⟩ : syracuseStep 110139 = 165209) B165209
theorem B110215 : Blo 107783 110215 := bstep (se 1 (by rfl) ⟨82661, by rfl⟩ : syracuseStep 110215 = 165323) B165323
theorem B110223 : Blo 107783 110223 := bstep (se 1 (by rfl) ⟨82667, by rfl⟩ : syracuseStep 110223 = 165335) B165335
theorem B110267 : Blo 107783 110267 := bstep (se 1 (by rfl) ⟨82700, by rfl⟩ : syracuseStep 110267 = 165401) B165401
theorem B208585 : Blo 107783 208585 := bstep (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) B156439
theorem B110343 : Blo 107783 110343 := bstep (se 1 (by rfl) ⟨82757, by rfl⟩ : syracuseStep 110343 = 165515) B165515
theorem B110351 : Blo 107783 110351 := bstep (se 1 (by rfl) ⟨82763, by rfl⟩ : syracuseStep 110351 = 165527) B165527
theorem B110395 : Blo 107783 110395 := bstep (se 1 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 110395 = 165593) B165593
theorem B110471 : Blo 107783 110471 := bstep (se 1 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 110471 = 165707) B165707
theorem B110479 : Blo 107783 110479 := bstep (se 1 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 110479 = 165719) B165719
theorem B307091 : Blo 107783 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B110523 : Blo 107783 110523 := bstep (se 1 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 110523 = 165785) B165785
theorem B110599 : Blo 107783 110599 := bstep (se 1 (by rfl) ⟨82949, by rfl⟩ : syracuseStep 110599 = 165899) B165899
theorem B110607 : Blo 107783 110607 := bstep (se 1 (by rfl) ⟨82955, by rfl⟩ : syracuseStep 110607 = 165911) B165911
theorem B110651 : Blo 107783 110651 := bstep (se 1 (by rfl) ⟨82988, by rfl⟩ : syracuseStep 110651 = 165977) B165977
theorem B110727 : Blo 107783 110727 := bstep (se 1 (by rfl) ⟨83045, by rfl⟩ : syracuseStep 110727 = 166091) B166091
theorem B110735 : Blo 107783 110735 := bstep (se 1 (by rfl) ⟨83051, by rfl⟩ : syracuseStep 110735 = 166103) B166103
theorem B798893 : Blo 107783 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B110779 : Blo 107783 110779 := bstep (se 1 (by rfl) ⟨83084, by rfl⟩ : syracuseStep 110779 = 166169) B166169
theorem B110855 : Blo 107783 110855 := bstep (se 1 (by rfl) ⟨83141, by rfl⟩ : syracuseStep 110855 = 166283) B166283
theorem B110863 : Blo 107783 110863 := bstep (se 1 (by rfl) ⟨83147, by rfl⟩ : syracuseStep 110863 = 166295) B166295
theorem B110907 : Blo 107783 110907 := bstep (se 1 (by rfl) ⟨83180, by rfl⟩ : syracuseStep 110907 = 166361) B166361
theorem B274823 : Blo 107783 274823 := bstep (se 1 (by rfl) ⟨206117, by rfl⟩ : syracuseStep 274823 = 412235) B412235
theorem B110983 : Blo 107783 110983 := bstep (se 1 (by rfl) ⟨83237, by rfl⟩ : syracuseStep 110983 = 166475) B166475
theorem B110991 : Blo 107783 110991 := bstep (se 1 (by rfl) ⟨83243, by rfl⟩ : syracuseStep 110991 = 166487) B166487
theorem B536977 : Blo 107783 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B209299 : Blo 107783 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B373139 : Blo 107783 373139 := bstep (se 1 (by rfl) ⟨279854, by rfl⟩ : syracuseStep 373139 = 559709) B559709
theorem B274873 : Blo 107783 274873 := bstep (se 2 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 274873 = 206155) B206155
theorem B111035 : Blo 107783 111035 := bstep (se 1 (by rfl) ⟨83276, by rfl⟩ : syracuseStep 111035 = 166553) B166553
theorem B111111 : Blo 107783 111111 := bstep (se 1 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 111111 = 166667) B166667
theorem B111119 : Blo 107783 111119 := bstep (se 1 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 111119 = 166679) B166679
theorem B537131 : Blo 107783 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B176699 : Blo 107783 176699 := bstep (se 1 (by rfl) ⟨132524, by rfl⟩ : syracuseStep 176699 = 265049) B265049
theorem B111163 : Blo 107783 111163 := bstep (se 1 (by rfl) ⟨83372, by rfl⟩ : syracuseStep 111163 = 166745) B166745
theorem B111239 : Blo 107783 111239 := bstep (se 1 (by rfl) ⟨83429, by rfl⟩ : syracuseStep 111239 = 166859) B166859
theorem B111247 : Blo 107783 111247 := bstep (se 1 (by rfl) ⟨83435, by rfl⟩ : syracuseStep 111247 = 166871) B166871
theorem B4207285 : Blo 107783 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B111291 : Blo 107783 111291 := bstep (se 1 (by rfl) ⟨83468, by rfl⟩ : syracuseStep 111291 = 166937) B166937
theorem B111367 : Blo 107783 111367 := bstep (se 1 (by rfl) ⟨83525, by rfl⟩ : syracuseStep 111367 = 167051) B167051
theorem B111375 : Blo 107783 111375 := bstep (se 1 (by rfl) ⟨83531, by rfl⟩ : syracuseStep 111375 = 167063) B167063
theorem B111419 : Blo 107783 111419 := bstep (se 1 (by rfl) ⟨83564, by rfl⟩ : syracuseStep 111419 = 167129) B167129
theorem B308083 : Blo 107783 308083 := bstep (se 1 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 308083 = 462125) B462125
theorem B242567 : Blo 107783 242567 := bstep (se 1 (by rfl) ⟨181925, by rfl⟩ : syracuseStep 242567 = 363851) B363851
theorem B111495 : Blo 107783 111495 := bstep (se 1 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 111495 = 167243) B167243
theorem B111503 : Blo 107783 111503 := bstep (se 1 (by rfl) ⟨83627, by rfl⟩ : syracuseStep 111503 = 167255) B167255
theorem B668569 : Blo 107783 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B111547 : Blo 107783 111547 := bstep (se 1 (by rfl) ⟨83660, by rfl⟩ : syracuseStep 111547 = 167321) B167321
theorem B111623 : Blo 107783 111623 := bstep (se 1 (by rfl) ⟨83717, by rfl⟩ : syracuseStep 111623 = 167435) B167435
theorem B275471 : Blo 107783 275471 := bstep (se 1 (by rfl) ⟨206603, by rfl⟩ : syracuseStep 275471 = 413207) B413207
theorem B111631 : Blo 107783 111631 := bstep (se 1 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 111631 = 167447) B167447
theorem B242747 : Blo 107783 242747 := bstep (se 1 (by rfl) ⟨182060, by rfl⟩ : syracuseStep 242747 = 364121) B364121
theorem B111675 : Blo 107783 111675 := bstep (se 1 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 111675 = 167513) B167513
theorem B406595 : Blo 107783 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B111751 : Blo 107783 111751 := bstep (se 1 (by rfl) ⟨83813, by rfl⟩ : syracuseStep 111751 = 167627) B167627
theorem B111759 : Blo 107783 111759 := bstep (se 1 (by rfl) ⟨83819, by rfl⟩ : syracuseStep 111759 = 167639) B167639
theorem B242873 : Blo 107783 242873 := bstep (se 2 (by rfl) ⟨91077, by rfl⟩ : syracuseStep 242873 = 182155) B182155
theorem B603407 : Blo 107783 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B210377 : Blo 107783 210377 := bstep (se 2 (by rfl) ⟨78891, by rfl⟩ : syracuseStep 210377 = 157783) B157783
theorem B472529 : Blo 107783 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B243215 : Blo 107783 243215 := bstep (se 1 (by rfl) ⟨182411, by rfl⟩ : syracuseStep 243215 = 364823) B364823
theorem B243233 : Blo 107783 243233 := bstep (se 2 (by rfl) ⟨91212, by rfl⟩ : syracuseStep 243233 = 182425) B182425
theorem B276169 : Blo 107783 276169 := bstep (se 2 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 276169 = 207127) B207127
theorem B702209 : Blo 107783 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B374543 : Blo 107783 374543 := bstep (se 1 (by rfl) ⟨280907, by rfl⟩ : syracuseStep 374543 = 561815) B561815
theorem B276311 : Blo 107783 276311 := bstep (se 1 (by rfl) ⟨207233, by rfl⟩ : syracuseStep 276311 = 414467) B414467
theorem B243575 : Blo 107783 243575 := bstep (se 1 (by rfl) ⟨182681, by rfl⟩ : syracuseStep 243575 = 365363) B365363
theorem B374813 : Blo 107783 374813 := bstep (se 3 (by rfl) ⟨70277, by rfl⟩ : syracuseStep 374813 = 140555) B140555
theorem B243755 : Blo 107783 243755 := bstep (se 1 (by rfl) ⟨182816, by rfl⟩ : syracuseStep 243755 = 365633) B365633
theorem B211243 : Blo 107783 211243 := bstep (se 1 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 211243 = 316865) B316865
theorem B211319 : Blo 107783 211319 := bstep (se 1 (by rfl) ⟨158489, by rfl⟩ : syracuseStep 211319 = 316979) B316979
theorem B244115 : Blo 107783 244115 := bstep (se 1 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 244115 = 366173) B366173
theorem B309689 : Blo 107783 309689 := bstep (se 2 (by rfl) ⟨116133, by rfl⟩ : syracuseStep 309689 = 232267) B232267
theorem B244169 : Blo 107783 244169 := bstep (se 2 (by rfl) ⟨91563, by rfl⟩ : syracuseStep 244169 = 183127) B183127
theorem B310031 : Blo 107783 310031 := bstep (se 1 (by rfl) ⟨232523, by rfl⟩ : syracuseStep 310031 = 465047) B465047
theorem B1850201 : Blo 107783 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1358795 : Blo 107783 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B244871 : Blo 107783 244871 := bstep (se 1 (by rfl) ⟨183653, by rfl⟩ : syracuseStep 244871 = 367307) B367307
theorem B245051 : Blo 107783 245051 := bstep (se 1 (by rfl) ⟨183788, by rfl⟩ : syracuseStep 245051 = 367577) B367577
theorem B376217 : Blo 107783 376217 := bstep (se 2 (by rfl) ⟨141081, by rfl⟩ : syracuseStep 376217 = 282163) B282163
theorem B245177 : Blo 107783 245177 := bstep (se 2 (by rfl) ⟨91941, by rfl⟩ : syracuseStep 245177 = 183883) B183883
theorem B310817 : Blo 107783 310817 := bstep (se 2 (by rfl) ⟨116556, by rfl⟩ : syracuseStep 310817 = 233113) B233113
theorem B441917 : Blo 107783 441917 := bstep (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) B165719
theorem B245519 : Blo 107783 245519 := bstep (se 1 (by rfl) ⟨184139, by rfl⟩ : syracuseStep 245519 = 368279) B368279
theorem B245537 : Blo 107783 245537 := bstep (se 2 (by rfl) ⟨92076, by rfl⟩ : syracuseStep 245537 = 184153) B184153
theorem B278387 : Blo 107783 278387 := bstep (se 1 (by rfl) ⟨208790, by rfl⟩ : syracuseStep 278387 = 417581) B417581
theorem B638873 : Blo 107783 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B376919 : Blo 107783 376919 := bstep (se 1 (by rfl) ⟨282689, by rfl⟩ : syracuseStep 376919 = 565379) B565379
theorem B245879 : Blo 107783 245879 := bstep (se 1 (by rfl) ⟨184409, by rfl⟩ : syracuseStep 245879 = 368819) B368819
theorem B246059 : Blo 107783 246059 := bstep (se 1 (by rfl) ⟨184544, by rfl⟩ : syracuseStep 246059 = 369089) B369089
theorem B278903 : Blo 107783 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B606649 : Blo 107783 606649 := bstep (se 2 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 606649 = 454987) B454987
theorem B410123 : Blo 107783 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B246419 : Blo 107783 246419 := bstep (se 1 (by rfl) ⟨184814, by rfl⟩ : syracuseStep 246419 = 369629) B369629
theorem B246473 : Blo 107783 246473 := bstep (se 2 (by rfl) ⟨92427, by rfl⟩ : syracuseStep 246473 = 184855) B184855
theorem B115463 : Blo 107783 115463 := bstep (se 1 (by rfl) ⟨86597, by rfl⟩ : syracuseStep 115463 = 173195) B173195
theorem B803621 : Blo 107783 803621 := bstep (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) B150679
theorem B312331 : Blo 107783 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B2114693 : Blo 107783 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B312605 : Blo 107783 312605 := bstep (se 3 (by rfl) ⟨58613, by rfl⟩ : syracuseStep 312605 = 117227) B117227
theorem B279895 : Blo 107783 279895 := bstep (se 1 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 279895 = 419843) B419843
theorem B247175 : Blo 107783 247175 := bstep (se 1 (by rfl) ⟨185381, by rfl⟩ : syracuseStep 247175 = 370763) B370763
theorem B411065 : Blo 107783 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B706051 : Blo 107783 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B247355 : Blo 107783 247355 := bstep (se 1 (by rfl) ⟨185516, by rfl⟩ : syracuseStep 247355 = 371033) B371033
theorem B1558115 : Blo 107783 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B312947 : Blo 107783 312947 := bstep (se 1 (by rfl) ⟨234710, by rfl⟩ : syracuseStep 312947 = 469421) B469421
theorem B280199 : Blo 107783 280199 := bstep (se 1 (by rfl) ⟨210149, by rfl⟩ : syracuseStep 280199 = 420299) B420299
theorem B6670001 : Blo 107783 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B247481 : Blo 107783 247481 := bstep (se 2 (by rfl) ⟨92805, by rfl⟩ : syracuseStep 247481 = 185611) B185611
theorem B837377 : Blo 107783 837377 := bstep (se 2 (by rfl) ⟨314016, by rfl⟩ : syracuseStep 837377 = 628033) B628033
theorem B280331 : Blo 107783 280331 := bstep (se 1 (by rfl) ⟨210248, by rfl⟩ : syracuseStep 280331 = 420497) B420497
theorem B182135 : Blo 107783 182135 := bstep (se 1 (by rfl) ⟨136601, by rfl⟩ : syracuseStep 182135 = 273203) B273203
theorem B345991 : Blo 107783 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B247823 : Blo 107783 247823 := bstep (se 1 (by rfl) ⟨185867, by rfl⟩ : syracuseStep 247823 = 371735) B371735
theorem B247841 : Blo 107783 247841 := bstep (se 2 (by rfl) ⟨92940, by rfl⟩ : syracuseStep 247841 = 185881) B185881
theorem B477245 : Blo 107783 477245 := bstep (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) B178967
theorem B280847 : Blo 107783 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B346427 : Blo 107783 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B182587 : Blo 107783 182587 := bstep (se 1 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 182587 = 273881) B273881
theorem B248183 : Blo 107783 248183 := bstep (se 1 (by rfl) ⟨186137, by rfl⟩ : syracuseStep 248183 = 372275) B372275
theorem B1067411 : Blo 107783 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B280979 : Blo 107783 280979 := bstep (se 1 (by rfl) ⟨210734, by rfl⟩ : syracuseStep 280979 = 421469) B421469
theorem B182729 : Blo 107783 182729 := bstep (se 2 (by rfl) ⟨68523, by rfl⟩ : syracuseStep 182729 = 137047) B137047
theorem B248363 : Blo 107783 248363 := bstep (se 1 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 248363 = 372545) B372545
theorem B313915 : Blo 107783 313915 := bstep (se 1 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 313915 = 470873) B470873
theorem B248723 : Blo 107783 248723 := bstep (se 1 (by rfl) ⟨186542, by rfl⟩ : syracuseStep 248723 = 373085) B373085
theorem B248777 : Blo 107783 248777 := bstep (se 2 (by rfl) ⟨93291, by rfl⟩ : syracuseStep 248777 = 186583) B186583
theorem B183431 : Blo 107783 183431 := bstep (se 1 (by rfl) ⟨137573, by rfl⟩ : syracuseStep 183431 = 275147) B275147
theorem B282113 : Blo 107783 282113 := bstep (se 2 (by rfl) ⟨105792, by rfl⟩ : syracuseStep 282113 = 211585) B211585
theorem B249479 : Blo 107783 249479 := bstep (se 1 (by rfl) ⟨187109, by rfl⟩ : syracuseStep 249479 = 374219) B374219
theorem B315065 : Blo 107783 315065 := bstep (se 2 (by rfl) ⟨118149, by rfl⟩ : syracuseStep 315065 = 236299) B236299
theorem B184079 : Blo 107783 184079 := bstep (se 1 (by rfl) ⟨138059, by rfl⟩ : syracuseStep 184079 = 276119) B276119
theorem B249659 : Blo 107783 249659 := bstep (se 1 (by rfl) ⟨187244, by rfl⟩ : syracuseStep 249659 = 374489) B374489
theorem B282487 : Blo 107783 282487 := bstep (se 1 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 282487 = 423731) B423731
theorem B249785 : Blo 107783 249785 := bstep (se 2 (by rfl) ⟨93669, by rfl⟩ : syracuseStep 249785 = 187339) B187339
theorem B413707 : Blo 107783 413707 := bstep (se 1 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 413707 = 620561) B620561
theorem B315407 : Blo 107783 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B446525 : Blo 107783 446525 := bstep (se 3 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 446525 = 167447) B167447
theorem B250127 : Blo 107783 250127 := bstep (se 1 (by rfl) ⟨187595, by rfl⟩ : syracuseStep 250127 = 375191) B375191
theorem B250145 : Blo 107783 250145 := bstep (se 2 (by rfl) ⟨93804, by rfl⟩ : syracuseStep 250145 = 187609) B187609
theorem B184619 : Blo 107783 184619 := bstep (se 1 (by rfl) ⟨138464, by rfl⟩ : syracuseStep 184619 = 276929) B276929
theorem B282923 : Blo 107783 282923 := bstep (se 1 (by rfl) ⟨212192, by rfl⟩ : syracuseStep 282923 = 424385) B424385
theorem B414011 : Blo 107783 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B250487 : Blo 107783 250487 := bstep (se 1 (by rfl) ⟨187865, by rfl⟩ : syracuseStep 250487 = 375731) B375731
theorem B185017 : Blo 107783 185017 := bstep (se 2 (by rfl) ⟨69381, by rfl⟩ : syracuseStep 185017 = 138763) B138763
theorem B414497 : Blo 107783 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B250667 : Blo 107783 250667 := bstep (se 1 (by rfl) ⟨188000, by rfl⟩ : syracuseStep 250667 = 376001) B376001
theorem B316295 : Blo 107783 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B1037357 : Blo 107783 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B316477 : Blo 107783 316477 := bstep (se 3 (by rfl) ⟨59339, by rfl⟩ : syracuseStep 316477 = 118679) B118679
theorem B251027 : Blo 107783 251027 := bstep (se 1 (by rfl) ⟨188270, by rfl⟩ : syracuseStep 251027 = 376541) B376541
theorem B251081 : Blo 107783 251081 := bstep (se 2 (by rfl) ⟨94155, by rfl⟩ : syracuseStep 251081 = 188311) B188311
theorem B316705 : Blo 107783 316705 := bstep (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) B237529
theorem B185719 : Blo 107783 185719 := bstep (se 1 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 185719 = 278579) B278579
theorem B185915 : Blo 107783 185915 := bstep (se 1 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 185915 = 278873) B278873
theorem B317047 : Blo 107783 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B415469 : Blo 107783 415469 := bstep (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) B155801
theorem B186313 : Blo 107783 186313 := bstep (se 2 (by rfl) ⟨69867, by rfl⟩ : syracuseStep 186313 = 139735) B139735
theorem B841751 : Blo 107783 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B677911 : Blo 107783 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B153785 : Blo 107783 153785 := bstep (se 2 (by rfl) ⟨57669, by rfl⟩ : syracuseStep 153785 = 115339) B115339
theorem B547073 : Blo 107783 547073 := bstep (se 2 (by rfl) ⟨205152, by rfl⟩ : syracuseStep 547073 = 410305) B410305
theorem B1399133 : Blo 107783 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B1169795 : Blo 107783 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B678289 : Blo 107783 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B514451 : Blo 107783 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B121351 : Blo 107783 121351 := bstep (se 1 (by rfl) ⟨91013, by rfl⟩ : syracuseStep 121351 = 182027) B182027
theorem B317981 : Blo 107783 317981 := bstep (se 3 (by rfl) ⟨59621, by rfl⟩ : syracuseStep 317981 = 119243) B119243
theorem B285299 : Blo 107783 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B187015 : Blo 107783 187015 := bstep (se 1 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 187015 = 280523) B280523
theorem B121531 : Blo 107783 121531 := bstep (se 1 (by rfl) ⟨91148, by rfl⟩ : syracuseStep 121531 = 182297) B182297
theorem B318323 : Blo 107783 318323 := bstep (se 1 (by rfl) ⟨238742, by rfl⟩ : syracuseStep 318323 = 477485) B477485
theorem B2579363 : Blo 107783 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B154639 : Blo 107783 154639 := bstep (se 1 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 154639 = 231959) B231959
theorem B547883 : Blo 107783 547883 := bstep (se 1 (by rfl) ⟨410912, by rfl⟩ : syracuseStep 547883 = 821825) B821825
theorem B711767 : Blo 107783 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B121999 : Blo 107783 121999 := bstep (se 1 (by rfl) ⟨91499, by rfl⟩ : syracuseStep 121999 = 182999) B182999
theorem B7625933 : Blo 107783 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B187663 : Blo 107783 187663 := bstep (se 1 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 187663 = 281495) B281495
theorem B1334663 : Blo 107783 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B155209 : Blo 107783 155209 := bstep (se 2 (by rfl) ⟨58203, by rfl⟩ : syracuseStep 155209 = 116407) B116407
theorem B122503 : Blo 107783 122503 := bstep (se 1 (by rfl) ⟨91877, by rfl⟩ : syracuseStep 122503 = 183755) B183755
theorem B188203 : Blo 107783 188203 := bstep (se 1 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 188203 = 282305) B282305
theorem B122683 : Blo 107783 122683 := bstep (se 1 (by rfl) ⟨92012, by rfl⟩ : syracuseStep 122683 = 184025) B184025
theorem B417595 : Blo 107783 417595 := bstep (se 1 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 417595 = 626393) B626393
theorem B843635 : Blo 107783 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B188345 : Blo 107783 188345 := bstep (se 2 (by rfl) ⟨70629, by rfl⟩ : syracuseStep 188345 = 141259) B141259
theorem B614411 : Blo 107783 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B123151 : Blo 107783 123151 := bstep (se 1 (by rfl) ⟨92363, by rfl⟩ : syracuseStep 123151 = 184727) B184727
theorem B418081 : Blo 107783 418081 := bstep (se 2 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 418081 = 313561) B313561
theorem B549179 : Blo 107783 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B549341 : Blo 107783 549341 := bstep (se 3 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 549341 = 206003) B206003
theorem B123655 : Blo 107783 123655 := bstep (se 1 (by rfl) ⟨92741, by rfl⟩ : syracuseStep 123655 = 185483) B185483
theorem B549665 : Blo 107783 549665 := bstep (se 2 (by rfl) ⟨206124, by rfl⟩ : syracuseStep 549665 = 412249) B412249
theorem B680849 : Blo 107783 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B123835 : Blo 107783 123835 := bstep (se 1 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 123835 = 185753) B185753
theorem B419053 : Blo 107783 419053 := bstep (se 3 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 419053 = 157145) B157145
theorem B124303 : Blo 107783 124303 := bstep (se 1 (by rfl) ⟨93227, by rfl⟩ : syracuseStep 124303 = 186455) B186455
theorem B419357 : Blo 107783 419357 := bstep (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) B157259
theorem B452297 : Blo 107783 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B550637 : Blo 107783 550637 := bstep (se 3 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 550637 = 206489) B206489
theorem B124687 : Blo 107783 124687 := bstep (se 1 (by rfl) ⟨93515, by rfl⟩ : syracuseStep 124687 = 187031) B187031
theorem B124807 : Blo 107783 124807 := bstep (se 1 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 124807 = 187211) B187211
theorem B124987 : Blo 107783 124987 := bstep (se 1 (by rfl) ⟨93740, by rfl⟩ : syracuseStep 124987 = 187481) B187481
theorem B157897 : Blo 107783 157897 := bstep (se 2 (by rfl) ⟨59211, by rfl⟩ : syracuseStep 157897 = 118423) B118423
theorem B289295 : Blo 107783 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B125455 : Blo 107783 125455 := bstep (se 1 (by rfl) ⟨94091, by rfl⟩ : syracuseStep 125455 = 188183) B188183
theorem B551447 : Blo 107783 551447 := bstep (se 1 (by rfl) ⟨413585, by rfl⟩ : syracuseStep 551447 = 827171) B827171
theorem B715331 : Blo 107783 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B1010369 : Blo 107783 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B256801 : Blo 107783 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B420983 : Blo 107783 420983 := bstep (se 1 (by rfl) ⟨315737, by rfl⟩ : syracuseStep 420983 = 631475) B631475
theorem B617645 : Blo 107783 617645 := bstep (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) B231617
theorem B1240337 : Blo 107783 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B2420549 : Blo 107783 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B356231 : Blo 107783 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B421955 : Blo 107783 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B618785 : Blo 107783 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B291671 : Blo 107783 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B422941 : Blo 107783 422941 := bstep (se 3 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 422941 = 158603) B158603
theorem B9172099 : Blo 107783 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B554525 : Blo 107783 554525 := bstep (se 3 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 554525 = 207947) B207947
theorem B358145 : Blo 107783 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B194347 : Blo 107783 194347 := bstep (se 1 (by rfl) ⟨145760, by rfl⟩ : syracuseStep 194347 = 291521) B291521
theorem B1898315 : Blo 107783 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B587665 : Blo 107783 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B161723 : Blo 107783 161723 := bstep (se 1 (by rfl) ⟨121292, by rfl⟩ : syracuseStep 161723 = 242585) B242585
theorem B161783 : Blo 107783 161783 := bstep (se 1 (by rfl) ⟨121337, by rfl⟩ : syracuseStep 161783 = 242675) B242675
theorem B555011 : Blo 107783 555011 := bstep (se 1 (by rfl) ⟨416258, by rfl⟩ : syracuseStep 555011 = 832517) B832517
theorem B161807 : Blo 107783 161807 := bstep (se 1 (by rfl) ⟨121355, by rfl⟩ : syracuseStep 161807 = 242711) B242711
theorem B555031 : Blo 107783 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B161849 : Blo 107783 161849 := bstep (se 2 (by rfl) ⟨60693, by rfl⟩ : syracuseStep 161849 = 121387) B121387
theorem B161927 : Blo 107783 161927 := bstep (se 1 (by rfl) ⟨121445, by rfl⟩ : syracuseStep 161927 = 242891) B242891
theorem B161963 : Blo 107783 161963 := bstep (se 1 (by rfl) ⟨121472, by rfl⟩ : syracuseStep 161963 = 242945) B242945
theorem B161993 : Blo 107783 161993 := bstep (se 2 (by rfl) ⟨60747, by rfl⟩ : syracuseStep 161993 = 121495) B121495
theorem B7174453 : Blo 107783 7174453 := bstep (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) B672605
theorem B162107 : Blo 107783 162107 := bstep (se 1 (by rfl) ⟨121580, by rfl⟩ : syracuseStep 162107 = 243161) B243161
theorem B162167 : Blo 107783 162167 := bstep (se 1 (by rfl) ⟨121625, by rfl⟩ : syracuseStep 162167 = 243251) B243251
theorem B588167 : Blo 107783 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B162191 : Blo 107783 162191 := bstep (se 1 (by rfl) ⟨121643, by rfl⟩ : syracuseStep 162191 = 243287) B243287
theorem B588185 : Blo 107783 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B162233 : Blo 107783 162233 := bstep (se 2 (by rfl) ⟨60837, by rfl⟩ : syracuseStep 162233 = 121675) B121675
theorem B162311 : Blo 107783 162311 := bstep (se 1 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 162311 = 243467) B243467
theorem B162347 : Blo 107783 162347 := bstep (se 1 (by rfl) ⟨121760, by rfl⟩ : syracuseStep 162347 = 243521) B243521
theorem B162377 : Blo 107783 162377 := bstep (se 2 (by rfl) ⟨60891, by rfl⟩ : syracuseStep 162377 = 121783) B121783
theorem B162491 : Blo 107783 162491 := bstep (se 1 (by rfl) ⟨121868, by rfl⟩ : syracuseStep 162491 = 243737) B243737
theorem B424649 : Blo 107783 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B162551 : Blo 107783 162551 := bstep (se 1 (by rfl) ⟨121913, by rfl⟩ : syracuseStep 162551 = 243827) B243827
theorem B162575 : Blo 107783 162575 := bstep (se 1 (by rfl) ⟨121931, by rfl⟩ : syracuseStep 162575 = 243863) B243863
theorem B162617 : Blo 107783 162617 := bstep (se 2 (by rfl) ⟨60981, by rfl⟩ : syracuseStep 162617 = 121963) B121963
theorem B162695 : Blo 107783 162695 := bstep (se 1 (by rfl) ⟨122021, by rfl⟩ : syracuseStep 162695 = 244043) B244043
theorem B162731 : Blo 107783 162731 := bstep (se 1 (by rfl) ⟨122048, by rfl⟩ : syracuseStep 162731 = 244097) B244097
theorem B162761 : Blo 107783 162761 := bstep (se 2 (by rfl) ⟨61035, by rfl⟩ : syracuseStep 162761 = 122071) B122071
theorem B162875 : Blo 107783 162875 := bstep (se 1 (by rfl) ⟨122156, by rfl⟩ : syracuseStep 162875 = 244313) B244313
theorem B523331 : Blo 107783 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B162935 : Blo 107783 162935 := bstep (se 1 (by rfl) ⟨122201, by rfl⟩ : syracuseStep 162935 = 244403) B244403
theorem B162959 : Blo 107783 162959 := bstep (se 1 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 162959 = 244439) B244439
theorem B163001 : Blo 107783 163001 := bstep (se 2 (by rfl) ⟨61125, by rfl⟩ : syracuseStep 163001 = 122251) B122251
theorem B130295 : Blo 107783 130295 := bstep (se 1 (by rfl) ⟨97721, by rfl⟩ : syracuseStep 130295 = 195443) B195443
theorem B163079 : Blo 107783 163079 := bstep (se 1 (by rfl) ⟨122309, by rfl⟩ : syracuseStep 163079 = 244619) B244619
theorem B163115 : Blo 107783 163115 := bstep (se 1 (by rfl) ⟨122336, by rfl⟩ : syracuseStep 163115 = 244673) B244673
theorem B163145 : Blo 107783 163145 := bstep (se 2 (by rfl) ⟨61179, by rfl⟩ : syracuseStep 163145 = 122359) B122359
theorem B163259 : Blo 107783 163259 := bstep (se 1 (by rfl) ⟨122444, by rfl⟩ : syracuseStep 163259 = 244889) B244889
theorem B163319 : Blo 107783 163319 := bstep (se 1 (by rfl) ⟨122489, by rfl⟩ : syracuseStep 163319 = 244979) B244979
theorem B163343 : Blo 107783 163343 := bstep (se 1 (by rfl) ⟨122507, by rfl⟩ : syracuseStep 163343 = 245015) B245015
theorem B163385 : Blo 107783 163385 := bstep (se 2 (by rfl) ⟨61269, by rfl⟩ : syracuseStep 163385 = 122539) B122539
theorem B556631 : Blo 107783 556631 := bstep (se 1 (by rfl) ⟨417473, by rfl⟩ : syracuseStep 556631 = 834947) B834947
theorem B163463 : Blo 107783 163463 := bstep (se 1 (by rfl) ⟨122597, by rfl⟩ : syracuseStep 163463 = 245195) B245195
theorem B163499 : Blo 107783 163499 := bstep (se 1 (by rfl) ⟨122624, by rfl⟩ : syracuseStep 163499 = 245249) B245249
theorem B163529 : Blo 107783 163529 := bstep (se 2 (by rfl) ⟨61323, by rfl⟩ : syracuseStep 163529 = 122647) B122647
theorem B163643 : Blo 107783 163643 := bstep (se 1 (by rfl) ⟨122732, by rfl⟩ : syracuseStep 163643 = 245465) B245465
theorem B163703 : Blo 107783 163703 := bstep (se 1 (by rfl) ⟨122777, by rfl⟩ : syracuseStep 163703 = 245555) B245555
theorem B163727 : Blo 107783 163727 := bstep (se 1 (by rfl) ⟨122795, by rfl⟩ : syracuseStep 163727 = 245591) B245591
theorem B130987 : Blo 107783 130987 := bstep (se 1 (by rfl) ⟨98240, by rfl⟩ : syracuseStep 130987 = 196481) B196481
theorem B163769 : Blo 107783 163769 := bstep (se 2 (by rfl) ⟨61413, by rfl⟩ : syracuseStep 163769 = 122827) B122827
theorem B1245131 : Blo 107783 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B1572941 : Blo 107783 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B163919 : Blo 107783 163919 := bstep (se 1 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 163919 = 245879) B245879
theorem B164039 : Blo 107783 164039 := bstep (se 1 (by rfl) ⟨123029, by rfl⟩ : syracuseStep 164039 = 246059) B246059
theorem B164201 : Blo 107783 164201 := bstep (se 2 (by rfl) ⟨61575, by rfl⟩ : syracuseStep 164201 = 123151) B123151
theorem B557441 : Blo 107783 557441 := bstep (se 2 (by rfl) ⟨209040, by rfl⟩ : syracuseStep 557441 = 418081) B418081
theorem B164279 : Blo 107783 164279 := bstep (se 1 (by rfl) ⟨123209, by rfl⟩ : syracuseStep 164279 = 246419) B246419
theorem B164315 : Blo 107783 164315 := bstep (se 1 (by rfl) ⟨123236, by rfl⟩ : syracuseStep 164315 = 246473) B246473
theorem B1409795 : Blo 107783 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B164783 : Blo 107783 164783 := bstep (se 1 (by rfl) ⟨123587, by rfl⟩ : syracuseStep 164783 = 247175) B247175
theorem B164873 : Blo 107783 164873 := bstep (se 2 (by rfl) ⟨61827, by rfl⟩ : syracuseStep 164873 = 123655) B123655
theorem B787475 : Blo 107783 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B590867 : Blo 107783 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B164903 : Blo 107783 164903 := bstep (se 1 (by rfl) ⟨123677, by rfl⟩ : syracuseStep 164903 = 247355) B247355
theorem B164987 : Blo 107783 164987 := bstep (se 1 (by rfl) ⟨123740, by rfl⟩ : syracuseStep 164987 = 247481) B247481
theorem B558251 : Blo 107783 558251 := bstep (se 1 (by rfl) ⟨418688, by rfl⟩ : syracuseStep 558251 = 837377) B837377
theorem B165113 : Blo 107783 165113 := bstep (se 2 (by rfl) ⟨61917, by rfl⟩ : syracuseStep 165113 = 123835) B123835
theorem B165215 : Blo 107783 165215 := bstep (se 1 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 165215 = 247823) B247823
theorem B165227 : Blo 107783 165227 := bstep (se 1 (by rfl) ⟨123920, by rfl⟩ : syracuseStep 165227 = 247841) B247841
theorem B787913 : Blo 107783 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B230951 : Blo 107783 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B165455 : Blo 107783 165455 := bstep (se 1 (by rfl) ⟨124091, by rfl⟩ : syracuseStep 165455 = 248183) B248183
theorem B263819 : Blo 107783 263819 := bstep (se 1 (by rfl) ⟨197864, by rfl⟩ : syracuseStep 263819 = 395729) B395729
theorem B558737 : Blo 107783 558737 := bstep (se 2 (by rfl) ⟨209526, by rfl⟩ : syracuseStep 558737 = 419053) B419053
theorem B165575 : Blo 107783 165575 := bstep (se 1 (by rfl) ⟨124181, by rfl⟩ : syracuseStep 165575 = 248363) B248363
theorem B165737 : Blo 107783 165737 := bstep (se 2 (by rfl) ⟨62151, by rfl⟩ : syracuseStep 165737 = 124303) B124303
theorem B165815 : Blo 107783 165815 := bstep (se 1 (by rfl) ⟨124361, by rfl⟩ : syracuseStep 165815 = 248723) B248723
theorem B165851 : Blo 107783 165851 := bstep (se 1 (by rfl) ⟨124388, by rfl⟩ : syracuseStep 165851 = 248777) B248777
theorem B166249 : Blo 107783 166249 := bstep (se 2 (by rfl) ⟨62343, by rfl⟩ : syracuseStep 166249 = 124687) B124687
theorem B166319 : Blo 107783 166319 := bstep (se 1 (by rfl) ⟨124739, by rfl⟩ : syracuseStep 166319 = 249479) B249479
theorem B461321 : Blo 107783 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B166409 : Blo 107783 166409 := bstep (se 2 (by rfl) ⟨62403, by rfl⟩ : syracuseStep 166409 = 124807) B124807
theorem B166439 : Blo 107783 166439 := bstep (se 1 (by rfl) ⟨124829, by rfl⟩ : syracuseStep 166439 = 249659) B249659
theorem B166523 : Blo 107783 166523 := bstep (se 1 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 166523 = 249785) B249785
theorem B297683 : Blo 107783 297683 := bstep (se 1 (by rfl) ⟨223262, by rfl⟩ : syracuseStep 297683 = 446525) B446525
theorem B166649 : Blo 107783 166649 := bstep (se 2 (by rfl) ⟨62493, by rfl⟩ : syracuseStep 166649 = 124987) B124987
theorem B166751 : Blo 107783 166751 := bstep (se 1 (by rfl) ⟨125063, by rfl⟩ : syracuseStep 166751 = 250127) B250127
theorem B166763 : Blo 107783 166763 := bstep (se 1 (by rfl) ⟨125072, by rfl⟩ : syracuseStep 166763 = 250145) B250145
theorem B166991 : Blo 107783 166991 := bstep (se 1 (by rfl) ⟨125243, by rfl⟩ : syracuseStep 166991 = 250487) B250487
theorem B167111 : Blo 107783 167111 := bstep (se 1 (by rfl) ⟨125333, by rfl⟩ : syracuseStep 167111 = 250667) B250667
theorem B167273 : Blo 107783 167273 := bstep (se 2 (by rfl) ⟨62727, by rfl⟩ : syracuseStep 167273 = 125455) B125455
theorem B691571 : Blo 107783 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B1609085 : Blo 107783 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B363905 : Blo 107783 363905 := bstep (se 2 (by rfl) ⟨136464, by rfl⟩ : syracuseStep 363905 = 272929) B272929
theorem B167351 : Blo 107783 167351 := bstep (se 1 (by rfl) ⟨125513, by rfl⟩ : syracuseStep 167351 = 251027) B251027
theorem B167387 : Blo 107783 167387 := bstep (se 1 (by rfl) ⟨125540, by rfl⟩ : syracuseStep 167387 = 251081) B251081
theorem B396809 : Blo 107783 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B396839 : Blo 107783 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B265943 : Blo 107783 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B561005 : Blo 107783 561005 := bstep (se 3 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 561005 = 210377) B210377
theorem B397313 : Blo 107783 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B200711 : Blo 107783 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B561167 : Blo 107783 561167 := bstep (se 1 (by rfl) ⟨420875, by rfl⟩ : syracuseStep 561167 = 841751) B841751
theorem B364715 : Blo 107783 364715 := bstep (se 1 (by rfl) ⟨273536, by rfl⟩ : syracuseStep 364715 = 547073) B547073
theorem B1773899 : Blo 107783 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B528905 : Blo 107783 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B365255 : Blo 107783 365255 := bstep (se 1 (by rfl) ⟨273941, by rfl⟩ : syracuseStep 365255 = 547883) B547883
theorem B5083955 : Blo 107783 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B889775 : Blo 107783 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B398267 : Blo 107783 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B398351 : Blo 107783 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B791603 : Blo 107783 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B791831 : Blo 107783 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B824741 : Blo 107783 824741 := bstep (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) B154639
theorem B136667 : Blo 107783 136667 := bstep (se 1 (by rfl) ⟨102500, by rfl⟩ : syracuseStep 136667 = 205001) B205001
theorem B2299355 : Blo 107783 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B5969371 : Blo 107783 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B366119 : Blo 107783 366119 := bstep (se 1 (by rfl) ⟨274589, by rfl⟩ : syracuseStep 366119 = 549179) B549179
theorem B366227 : Blo 107783 366227 := bstep (se 1 (by rfl) ⟨274670, by rfl⟩ : syracuseStep 366227 = 549341) B549341
theorem B1250963 : Blo 107783 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B530135 : Blo 107783 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B268105 : Blo 107783 268105 := bstep (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) B201079
theorem B366443 : Blo 107783 366443 := bstep (se 1 (by rfl) ⟨274832, by rfl⟩ : syracuseStep 366443 = 549665) B549665
theorem B366497 : Blo 107783 366497 := bstep (se 2 (by rfl) ⟨137436, by rfl⟩ : syracuseStep 366497 = 274873) B274873
theorem B137143 : Blo 107783 137143 := bstep (se 1 (by rfl) ⟨102857, by rfl⟩ : syracuseStep 137143 = 205715) B205715
theorem B1185799 : Blo 107783 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B465011 : Blo 107783 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B301531 : Blo 107783 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B367091 : Blo 107783 367091 := bstep (se 1 (by rfl) ⟨275318, by rfl⟩ : syracuseStep 367091 = 550637) B550637
theorem B891425 : Blo 107783 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B400081 : Blo 107783 400081 := bstep (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) B300061
theorem B563921 : Blo 107783 563921 := bstep (se 2 (by rfl) ⟨211470, by rfl⟩ : syracuseStep 563921 = 422941) B422941
theorem B12229465 : Blo 107783 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B367631 : Blo 107783 367631 := bstep (se 1 (by rfl) ⟨275723, by rfl⟩ : syracuseStep 367631 = 551447) B551447
theorem B597071 : Blo 107783 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B138439 : Blo 107783 138439 := bstep (se 1 (by rfl) ⟨103829, by rfl⟩ : syracuseStep 138439 = 207659) B207659
theorem B924965 : Blo 107783 924965 := bstep (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) B173431
theorem B826891 : Blo 107783 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B368225 : Blo 107783 368225 := bstep (se 2 (by rfl) ⟨138084, by rfl⟩ : syracuseStep 368225 = 276169) B276169
theorem B269963 : Blo 107783 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B1613699 : Blo 107783 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B237487 : Blo 107783 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B532595 : Blo 107783 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B271063 : Blo 107783 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B369683 : Blo 107783 369683 := bstep (se 1 (by rfl) ⟨277262, by rfl⟩ : syracuseStep 369683 = 554525) B554525
theorem B468139 : Blo 107783 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B238763 : Blo 107783 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B107815 : Blo 107783 107815 := bstep (se 1 (by rfl) ⟨80861, by rfl⟩ : syracuseStep 107815 = 161723) B161723
theorem B107855 : Blo 107783 107855 := bstep (se 1 (by rfl) ⟨80891, by rfl⟩ : syracuseStep 107855 = 161783) B161783
theorem B370007 : Blo 107783 370007 := bstep (se 1 (by rfl) ⟨277505, by rfl⟩ : syracuseStep 370007 = 555011) B555011
theorem B107871 : Blo 107783 107871 := bstep (se 1 (by rfl) ⟨80903, by rfl⟩ : syracuseStep 107871 = 161807) B161807
theorem B107899 : Blo 107783 107899 := bstep (se 1 (by rfl) ⟨80924, by rfl⟩ : syracuseStep 107899 = 161849) B161849
theorem B107951 : Blo 107783 107951 := bstep (se 1 (by rfl) ⟨80963, by rfl⟩ : syracuseStep 107951 = 161927) B161927
theorem B107975 : Blo 107783 107975 := bstep (se 1 (by rfl) ⟨80981, by rfl⟩ : syracuseStep 107975 = 161963) B161963
theorem B107995 : Blo 107783 107995 := bstep (se 1 (by rfl) ⟨80996, by rfl⟩ : syracuseStep 107995 = 161993) B161993
theorem B108071 : Blo 107783 108071 := bstep (se 1 (by rfl) ⟨81053, by rfl⟩ : syracuseStep 108071 = 162107) B162107
theorem B108111 : Blo 107783 108111 := bstep (se 1 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 108111 = 162167) B162167
theorem B140879 : Blo 107783 140879 := bstep (se 1 (by rfl) ⟨105659, by rfl⟩ : syracuseStep 140879 = 211319) B211319
theorem B108127 : Blo 107783 108127 := bstep (se 1 (by rfl) ⟨81095, by rfl⟩ : syracuseStep 108127 = 162191) B162191
theorem B108155 : Blo 107783 108155 := bstep (se 1 (by rfl) ⟨81116, by rfl⟩ : syracuseStep 108155 = 162233) B162233
theorem B206459 : Blo 107783 206459 := bstep (se 1 (by rfl) ⟨154844, by rfl⟩ : syracuseStep 206459 = 309689) B309689
theorem B108207 : Blo 107783 108207 := bstep (se 1 (by rfl) ⟨81155, by rfl⟩ : syracuseStep 108207 = 162311) B162311
theorem B108231 : Blo 107783 108231 := bstep (se 1 (by rfl) ⟨81173, by rfl⟩ : syracuseStep 108231 = 162347) B162347
theorem B108251 : Blo 107783 108251 := bstep (se 1 (by rfl) ⟨81188, by rfl⟩ : syracuseStep 108251 = 162377) B162377
theorem B108327 : Blo 107783 108327 := bstep (se 1 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 108327 = 162491) B162491
theorem B108367 : Blo 107783 108367 := bstep (se 1 (by rfl) ⟨81275, by rfl⟩ : syracuseStep 108367 = 162551) B162551
theorem B108383 : Blo 107783 108383 := bstep (se 1 (by rfl) ⟨81287, by rfl⟩ : syracuseStep 108383 = 162575) B162575
theorem B206687 : Blo 107783 206687 := bstep (se 1 (by rfl) ⟨155015, by rfl⟩ : syracuseStep 206687 = 310031) B310031
theorem B108411 : Blo 107783 108411 := bstep (se 1 (by rfl) ⟨81308, by rfl⟩ : syracuseStep 108411 = 162617) B162617
theorem B108463 : Blo 107783 108463 := bstep (se 1 (by rfl) ⟨81347, by rfl⟩ : syracuseStep 108463 = 162695) B162695
theorem B108487 : Blo 107783 108487 := bstep (se 1 (by rfl) ⟨81365, by rfl⟩ : syracuseStep 108487 = 162731) B162731
theorem B108507 : Blo 107783 108507 := bstep (se 1 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 108507 = 162761) B162761
theorem B108583 : Blo 107783 108583 := bstep (se 1 (by rfl) ⟨81437, by rfl⟩ : syracuseStep 108583 = 162875) B162875
theorem B108623 : Blo 107783 108623 := bstep (se 1 (by rfl) ⟨81467, by rfl⟩ : syracuseStep 108623 = 162935) B162935
theorem B108639 : Blo 107783 108639 := bstep (se 1 (by rfl) ⟨81479, by rfl⟩ : syracuseStep 108639 = 162959) B162959
theorem B206945 : Blo 107783 206945 := bstep (se 2 (by rfl) ⟨77604, by rfl⟩ : syracuseStep 206945 = 155209) B155209
theorem B108667 : Blo 107783 108667 := bstep (se 1 (by rfl) ⟨81500, by rfl⟩ : syracuseStep 108667 = 163001) B163001
theorem B108719 : Blo 107783 108719 := bstep (se 1 (by rfl) ⟨81539, by rfl⟩ : syracuseStep 108719 = 163079) B163079
theorem B108743 : Blo 107783 108743 := bstep (se 1 (by rfl) ⟨81557, by rfl⟩ : syracuseStep 108743 = 163115) B163115
theorem B108763 : Blo 107783 108763 := bstep (se 1 (by rfl) ⟨81572, by rfl⟩ : syracuseStep 108763 = 163145) B163145
theorem B108839 : Blo 107783 108839 := bstep (se 1 (by rfl) ⟨81629, by rfl⟩ : syracuseStep 108839 = 163259) B163259
theorem B108879 : Blo 107783 108879 := bstep (se 1 (by rfl) ⟨81659, by rfl⟩ : syracuseStep 108879 = 163319) B163319
theorem B108895 : Blo 107783 108895 := bstep (se 1 (by rfl) ⟨81671, by rfl⟩ : syracuseStep 108895 = 163343) B163343
theorem B207211 : Blo 107783 207211 := bstep (se 1 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 207211 = 310817) B310817
theorem B108923 : Blo 107783 108923 := bstep (se 1 (by rfl) ⟨81692, by rfl⟩ : syracuseStep 108923 = 163385) B163385
theorem B371087 : Blo 107783 371087 := bstep (se 1 (by rfl) ⟨278315, by rfl⟩ : syracuseStep 371087 = 556631) B556631
theorem B108975 : Blo 107783 108975 := bstep (se 1 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 108975 = 163463) B163463
theorem B108999 : Blo 107783 108999 := bstep (se 1 (by rfl) ⟨81749, by rfl⟩ : syracuseStep 108999 = 163499) B163499
theorem B109019 : Blo 107783 109019 := bstep (se 1 (by rfl) ⟨81764, by rfl⟩ : syracuseStep 109019 = 163529) B163529
theorem B109095 : Blo 107783 109095 := bstep (se 1 (by rfl) ⟨81821, by rfl⟩ : syracuseStep 109095 = 163643) B163643
theorem B174649 : Blo 107783 174649 := bstep (se 2 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 174649 = 130987) B130987
theorem B109135 : Blo 107783 109135 := bstep (se 1 (by rfl) ⟨81851, by rfl⟩ : syracuseStep 109135 = 163703) B163703
theorem B109151 : Blo 107783 109151 := bstep (se 1 (by rfl) ⟨81863, by rfl⟩ : syracuseStep 109151 = 163727) B163727
theorem B109179 : Blo 107783 109179 := bstep (se 1 (by rfl) ⟨81884, by rfl⟩ : syracuseStep 109179 = 163769) B163769
theorem B830087 : Blo 107783 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B109231 : Blo 107783 109231 := bstep (se 1 (by rfl) ⟨81923, by rfl⟩ : syracuseStep 109231 = 163847) B163847
theorem B109255 : Blo 107783 109255 := bstep (se 1 (by rfl) ⟨81941, by rfl⟩ : syracuseStep 109255 = 163883) B163883
theorem B371411 : Blo 107783 371411 := bstep (se 1 (by rfl) ⟨278558, by rfl⟩ : syracuseStep 371411 = 557117) B557117
theorem B109275 : Blo 107783 109275 := bstep (se 1 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 109275 = 163913) B163913
theorem B2960165 : Blo 107783 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B109351 : Blo 107783 109351 := bstep (se 1 (by rfl) ⟨82013, by rfl⟩ : syracuseStep 109351 = 164027) B164027
theorem B109391 : Blo 107783 109391 := bstep (se 1 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 109391 = 164087) B164087
theorem B174943 : Blo 107783 174943 := bstep (se 1 (by rfl) ⟨131207, by rfl⟩ : syracuseStep 174943 = 262415) B262415
theorem B109407 : Blo 107783 109407 := bstep (se 1 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 109407 = 164111) B164111
theorem B109435 : Blo 107783 109435 := bstep (se 1 (by rfl) ⟨82076, by rfl⟩ : syracuseStep 109435 = 164153) B164153
theorem B109487 : Blo 107783 109487 := bstep (se 1 (by rfl) ⟨82115, by rfl⟩ : syracuseStep 109487 = 164231) B164231
theorem B109511 : Blo 107783 109511 := bstep (se 1 (by rfl) ⟨82133, by rfl⟩ : syracuseStep 109511 = 164267) B164267
theorem B109531 : Blo 107783 109531 := bstep (se 1 (by rfl) ⟨82148, by rfl⟩ : syracuseStep 109531 = 164297) B164297
theorem B273415 : Blo 107783 273415 := bstep (se 1 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 273415 = 410123) B410123
theorem B371719 : Blo 107783 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B109607 : Blo 107783 109607 := bstep (se 1 (by rfl) ⟨82205, by rfl⟩ : syracuseStep 109607 = 164411) B164411
theorem B109647 : Blo 107783 109647 := bstep (se 1 (by rfl) ⟨82235, by rfl⟩ : syracuseStep 109647 = 164471) B164471
theorem B109663 : Blo 107783 109663 := bstep (se 1 (by rfl) ⟨82247, by rfl⟩ : syracuseStep 109663 = 164495) B164495
theorem B109691 : Blo 107783 109691 := bstep (se 1 (by rfl) ⟨82268, by rfl⟩ : syracuseStep 109691 = 164537) B164537
theorem B109743 : Blo 107783 109743 := bstep (se 1 (by rfl) ⟨82307, by rfl⟩ : syracuseStep 109743 = 164615) B164615
theorem B535747 : Blo 107783 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B109767 : Blo 107783 109767 := bstep (se 1 (by rfl) ⟨82325, by rfl⟩ : syracuseStep 109767 = 164651) B164651
theorem B109787 : Blo 107783 109787 := bstep (se 1 (by rfl) ⟨82340, by rfl⟩ : syracuseStep 109787 = 164681) B164681
theorem B109863 : Blo 107783 109863 := bstep (se 1 (by rfl) ⟨82397, by rfl⟩ : syracuseStep 109863 = 164795) B164795
theorem B109903 : Blo 107783 109903 := bstep (se 1 (by rfl) ⟨82427, by rfl⟩ : syracuseStep 109903 = 164855) B164855
theorem B109919 : Blo 107783 109919 := bstep (se 1 (by rfl) ⟨82439, by rfl⟩ : syracuseStep 109919 = 164879) B164879
theorem B109947 : Blo 107783 109947 := bstep (se 1 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 109947 = 164921) B164921
theorem B109999 : Blo 107783 109999 := bstep (se 1 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 109999 = 164999) B164999
theorem B1748405 : Blo 107783 1748405 := bstep (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) B163913
theorem B110023 : Blo 107783 110023 := bstep (se 1 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 110023 = 165035) B165035
theorem B110043 : Blo 107783 110043 := bstep (se 1 (by rfl) ⟨82532, by rfl⟩ : syracuseStep 110043 = 165065) B165065
theorem B208403 : Blo 107783 208403 := bstep (se 1 (by rfl) ⟨156302, by rfl⟩ : syracuseStep 208403 = 312605) B312605
theorem B175655 : Blo 107783 175655 := bstep (se 1 (by rfl) ⟨131741, by rfl⟩ : syracuseStep 175655 = 263483) B263483
theorem B110119 : Blo 107783 110119 := bstep (se 1 (by rfl) ⟨82589, by rfl⟩ : syracuseStep 110119 = 165179) B165179
theorem B110159 : Blo 107783 110159 := bstep (se 1 (by rfl) ⟨82619, by rfl⟩ : syracuseStep 110159 = 165239) B165239
theorem B110175 : Blo 107783 110175 := bstep (se 1 (by rfl) ⟨82631, by rfl⟩ : syracuseStep 110175 = 165263) B165263
theorem B274043 : Blo 107783 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B110203 : Blo 107783 110203 := bstep (se 1 (by rfl) ⟨82652, by rfl⟩ : syracuseStep 110203 = 165305) B165305
theorem B110255 : Blo 107783 110255 := bstep (se 1 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 110255 = 165383) B165383
theorem B110279 : Blo 107783 110279 := bstep (se 1 (by rfl) ⟨82709, by rfl⟩ : syracuseStep 110279 = 165419) B165419
theorem B110299 : Blo 107783 110299 := bstep (se 1 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 110299 = 165449) B165449
theorem B208631 : Blo 107783 208631 := bstep (se 1 (by rfl) ⟨156473, by rfl⟩ : syracuseStep 208631 = 312947) B312947
theorem B110375 : Blo 107783 110375 := bstep (se 1 (by rfl) ⟨82781, by rfl⟩ : syracuseStep 110375 = 165563) B165563
theorem B110415 : Blo 107783 110415 := bstep (se 1 (by rfl) ⟨82811, by rfl⟩ : syracuseStep 110415 = 165623) B165623
theorem B110431 : Blo 107783 110431 := bstep (se 1 (by rfl) ⟨82823, by rfl⟩ : syracuseStep 110431 = 165647) B165647
theorem B372599 : Blo 107783 372599 := bstep (se 1 (by rfl) ⟨279449, by rfl⟩ : syracuseStep 372599 = 558899) B558899
theorem B110459 : Blo 107783 110459 := bstep (se 1 (by rfl) ⟨82844, by rfl⟩ : syracuseStep 110459 = 165689) B165689
theorem B274337 : Blo 107783 274337 := bstep (se 2 (by rfl) ⟨102876, by rfl⟩ : syracuseStep 274337 = 205753) B205753
theorem B110511 : Blo 107783 110511 := bstep (se 1 (by rfl) ⟨82883, by rfl⟩ : syracuseStep 110511 = 165767) B165767
theorem B1421243 : Blo 107783 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B110535 : Blo 107783 110535 := bstep (se 1 (by rfl) ⟨82901, by rfl⟩ : syracuseStep 110535 = 165803) B165803
theorem B110555 : Blo 107783 110555 := bstep (se 1 (by rfl) ⟨82916, by rfl⟩ : syracuseStep 110555 = 165833) B165833
theorem B110631 : Blo 107783 110631 := bstep (se 1 (by rfl) ⟨82973, by rfl⟩ : syracuseStep 110631 = 165947) B165947
theorem B831545 : Blo 107783 831545 := bstep (se 2 (by rfl) ⟨311829, by rfl⟩ : syracuseStep 831545 = 623659) B623659
theorem B372815 : Blo 107783 372815 := bstep (se 1 (by rfl) ⟨279611, by rfl⟩ : syracuseStep 372815 = 559223) B559223
theorem B110671 : Blo 107783 110671 := bstep (se 1 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 110671 = 166007) B166007
theorem B110687 : Blo 107783 110687 := bstep (se 1 (by rfl) ⟨83015, by rfl⟩ : syracuseStep 110687 = 166031) B166031
theorem B176251 : Blo 107783 176251 := bstep (se 1 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 176251 = 264377) B264377
theorem B110715 : Blo 107783 110715 := bstep (se 1 (by rfl) ⟨83036, by rfl⟩ : syracuseStep 110715 = 166073) B166073
theorem B471197 : Blo 107783 471197 := bstep (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) B176699
theorem B110767 : Blo 107783 110767 := bstep (se 1 (by rfl) ⟨83075, by rfl⟩ : syracuseStep 110767 = 166151) B166151
theorem B110791 : Blo 107783 110791 := bstep (se 1 (by rfl) ⟨83093, by rfl⟩ : syracuseStep 110791 = 166187) B166187
theorem B110811 : Blo 107783 110811 := bstep (se 1 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 110811 = 166217) B166217
theorem B110887 : Blo 107783 110887 := bstep (se 1 (by rfl) ⟨83165, by rfl⟩ : syracuseStep 110887 = 166331) B166331
theorem B110927 : Blo 107783 110927 := bstep (se 1 (by rfl) ⟨83195, by rfl⟩ : syracuseStep 110927 = 166391) B166391
theorem B110943 : Blo 107783 110943 := bstep (se 1 (by rfl) ⟨83207, by rfl⟩ : syracuseStep 110943 = 166415) B166415
theorem B110971 : Blo 107783 110971 := bstep (se 1 (by rfl) ⟨83228, by rfl⟩ : syracuseStep 110971 = 166457) B166457
theorem B111023 : Blo 107783 111023 := bstep (se 1 (by rfl) ⟨83267, by rfl⟩ : syracuseStep 111023 = 166535) B166535
theorem B111047 : Blo 107783 111047 := bstep (se 1 (by rfl) ⟨83285, by rfl⟩ : syracuseStep 111047 = 166571) B166571
theorem B373193 : Blo 107783 373193 := bstep (se 2 (by rfl) ⟨139947, by rfl⟩ : syracuseStep 373193 = 279895) B279895
theorem B111067 : Blo 107783 111067 := bstep (se 1 (by rfl) ⟨83300, by rfl⟩ : syracuseStep 111067 = 166601) B166601
theorem B111143 : Blo 107783 111143 := bstep (se 1 (by rfl) ⟨83357, by rfl⟩ : syracuseStep 111143 = 166715) B166715
theorem B111183 : Blo 107783 111183 := bstep (se 1 (by rfl) ⟨83387, by rfl⟩ : syracuseStep 111183 = 166775) B166775
theorem B111199 : Blo 107783 111199 := bstep (se 1 (by rfl) ⟨83399, by rfl⟩ : syracuseStep 111199 = 166799) B166799
theorem B111227 : Blo 107783 111227 := bstep (se 1 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 111227 = 166841) B166841
theorem B111279 : Blo 107783 111279 := bstep (se 1 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 111279 = 166919) B166919
theorem B307901 : Blo 107783 307901 := bstep (se 3 (by rfl) ⟨57731, by rfl⟩ : syracuseStep 307901 = 115463) B115463
theorem B111303 : Blo 107783 111303 := bstep (se 1 (by rfl) ⟨83477, by rfl⟩ : syracuseStep 111303 = 166955) B166955
theorem B373463 : Blo 107783 373463 := bstep (se 1 (by rfl) ⟨280097, by rfl⟩ : syracuseStep 373463 = 560195) B560195
theorem B111323 : Blo 107783 111323 := bstep (se 1 (by rfl) ⟨83492, by rfl⟩ : syracuseStep 111323 = 166985) B166985
theorem B111399 : Blo 107783 111399 := bstep (se 1 (by rfl) ⟨83549, by rfl⟩ : syracuseStep 111399 = 167099) B167099
theorem B111439 : Blo 107783 111439 := bstep (se 1 (by rfl) ⟨83579, by rfl⟩ : syracuseStep 111439 = 167159) B167159
theorem B111455 : Blo 107783 111455 := bstep (se 1 (by rfl) ⟨83591, by rfl⟩ : syracuseStep 111455 = 167183) B167183
theorem B111483 : Blo 107783 111483 := bstep (se 1 (by rfl) ⟨83612, by rfl⟩ : syracuseStep 111483 = 167225) B167225
theorem B373679 : Blo 107783 373679 := bstep (se 1 (by rfl) ⟨280259, by rfl⟩ : syracuseStep 373679 = 560519) B560519
theorem B111535 : Blo 107783 111535 := bstep (se 1 (by rfl) ⟨83651, by rfl⟩ : syracuseStep 111535 = 167303) B167303
theorem B111559 : Blo 107783 111559 := bstep (se 1 (by rfl) ⟨83669, by rfl⟩ : syracuseStep 111559 = 167339) B167339
theorem B111579 : Blo 107783 111579 := bstep (se 1 (by rfl) ⟨83684, by rfl⟩ : syracuseStep 111579 = 167369) B167369
theorem B308231 : Blo 107783 308231 := bstep (se 1 (by rfl) ⟨231173, by rfl⟩ : syracuseStep 308231 = 462347) B462347
theorem B111655 : Blo 107783 111655 := bstep (se 1 (by rfl) ⟨83741, by rfl⟩ : syracuseStep 111655 = 167483) B167483
theorem B111695 : Blo 107783 111695 := bstep (se 1 (by rfl) ⟨83771, by rfl⟩ : syracuseStep 111695 = 167543) B167543
theorem B111711 : Blo 107783 111711 := bstep (se 1 (by rfl) ⟨83783, by rfl⟩ : syracuseStep 111711 = 167567) B167567
theorem B210043 : Blo 107783 210043 := bstep (se 1 (by rfl) ⟨157532, by rfl⟩ : syracuseStep 210043 = 315065) B315065
theorem B111739 : Blo 107783 111739 := bstep (se 1 (by rfl) ⟨83804, by rfl⟩ : syracuseStep 111739 = 167609) B167609
theorem B177481 : Blo 107783 177481 := bstep (se 2 (by rfl) ⟨66555, by rfl⟩ : syracuseStep 177481 = 133111) B133111
theorem B210271 : Blo 107783 210271 := bstep (se 1 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 210271 = 315407) B315407
theorem B276007 : Blo 107783 276007 := bstep (se 1 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 276007 = 414011) B414011
theorem B210529 : Blo 107783 210529 := bstep (se 2 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 210529 = 157897) B157897
theorem B243323 : Blo 107783 243323 := bstep (se 1 (by rfl) ⟨182492, by rfl⟩ : syracuseStep 243323 = 364985) B364985
theorem B243449 : Blo 107783 243449 := bstep (se 2 (by rfl) ⟨91293, by rfl⟩ : syracuseStep 243449 = 182587) B182587
theorem B276331 : Blo 107783 276331 := bstep (se 1 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 276331 = 414497) B414497
theorem B210863 : Blo 107783 210863 := bstep (se 1 (by rfl) ⟨158147, by rfl⟩ : syracuseStep 210863 = 316295) B316295
theorem B833489 : Blo 107783 833489 := bstep (se 2 (by rfl) ⟨312558, by rfl⟩ : syracuseStep 833489 = 625117) B625117
theorem B243719 : Blo 107783 243719 := bstep (se 1 (by rfl) ⟨182789, by rfl⟩ : syracuseStep 243719 = 365579) B365579
theorem B243791 : Blo 107783 243791 := bstep (se 1 (by rfl) ⟨182843, by rfl⟩ : syracuseStep 243791 = 365687) B365687
theorem B342401 : Blo 107783 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B244187 : Blo 107783 244187 := bstep (se 1 (by rfl) ⟨183140, by rfl⟩ : syracuseStep 244187 = 366281) B366281
theorem B276979 : Blo 107783 276979 := bstep (se 1 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 276979 = 415469) B415469
theorem B375659 : Blo 107783 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B932755 : Blo 107783 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B244655 : Blo 107783 244655 := bstep (se 1 (by rfl) ⟨183491, by rfl⟩ : syracuseStep 244655 = 366983) B366983
theorem B342967 : Blo 107783 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B211987 : Blo 107783 211987 := bstep (se 1 (by rfl) ⟨158990, by rfl⟩ : syracuseStep 211987 = 317981) B317981
theorem B244907 : Blo 107783 244907 := bstep (se 1 (by rfl) ⟨183680, by rfl⟩ : syracuseStep 244907 = 367361) B367361
theorem B376055 : Blo 107783 376055 := bstep (se 1 (by rfl) ⟨282041, by rfl⟩ : syracuseStep 376055 = 564083) B564083
theorem B212215 : Blo 107783 212215 := bstep (se 1 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 212215 = 318323) B318323
theorem B1719575 : Blo 107783 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B474511 : Blo 107783 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B376379 : Blo 107783 376379 := bstep (se 1 (by rfl) ⟨282284, by rfl⟩ : syracuseStep 376379 = 564569) B564569
theorem B278113 : Blo 107783 278113 := bstep (se 2 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 278113 = 208585) B208585
theorem B245447 : Blo 107783 245447 := bstep (se 1 (by rfl) ⟨184085, by rfl⟩ : syracuseStep 245447 = 368171) B368171
theorem B310999 : Blo 107783 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B311033 : Blo 107783 311033 := bstep (se 2 (by rfl) ⟨116637, by rfl⟩ : syracuseStep 311033 = 233275) B233275
theorem B376649 : Blo 107783 376649 := bstep (se 2 (by rfl) ⟨141243, by rfl⟩ : syracuseStep 376649 = 282487) B282487
theorem B311147 : Blo 107783 311147 := bstep (se 1 (by rfl) ⟨233360, by rfl⟩ : syracuseStep 311147 = 466721) B466721
theorem B311215 : Blo 107783 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B409607 : Blo 107783 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B1982789 : Blo 107783 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B410093 : Blo 107783 410093 := bstep (se 3 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 410093 = 153785) B153785
theorem B279065 : Blo 107783 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B246311 : Blo 107783 246311 := bstep (se 1 (by rfl) ⟨184733, by rfl⟩ : syracuseStep 246311 = 369467) B369467
theorem B246635 : Blo 107783 246635 := bstep (se 1 (by rfl) ⟨184976, by rfl⟩ : syracuseStep 246635 = 369953) B369953
theorem B246689 : Blo 107783 246689 := bstep (se 2 (by rfl) ⟨92508, by rfl⟩ : syracuseStep 246689 = 185017) B185017
theorem B279571 : Blo 107783 279571 := bstep (se 1 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 279571 = 419357) B419357
theorem B410777 : Blo 107783 410777 := bstep (se 2 (by rfl) ⟨154041, by rfl⟩ : syracuseStep 410777 = 308083) B308083
theorem B312491 : Blo 107783 312491 := bstep (se 1 (by rfl) ⟨234368, by rfl⟩ : syracuseStep 312491 = 468737) B468737
theorem B247031 : Blo 107783 247031 := bstep (se 1 (by rfl) ⟨185273, by rfl⟩ : syracuseStep 247031 = 370547) B370547
theorem B2606627 : Blo 107783 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1230551 : Blo 107783 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B476887 : Blo 107783 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B673579 : Blo 107783 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B247625 : Blo 107783 247625 := bstep (se 2 (by rfl) ⟨92859, by rfl⟩ : syracuseStep 247625 = 185719) B185719
theorem B182351 : Blo 107783 182351 := bstep (se 1 (by rfl) ⟨136763, by rfl⟩ : syracuseStep 182351 = 273527) B273527
theorem B280655 : Blo 107783 280655 := bstep (se 1 (by rfl) ⟨210491, by rfl⟩ : syracuseStep 280655 = 420983) B420983
theorem B411763 : Blo 107783 411763 := bstep (se 1 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 411763 = 617645) B617645
theorem B248417 : Blo 107783 248417 := bstep (se 2 (by rfl) ⟨93156, by rfl⟩ : syracuseStep 248417 = 186313) B186313
theorem B903881 : Blo 107783 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B281303 : Blo 107783 281303 := bstep (se 1 (by rfl) ⟨210977, by rfl⟩ : syracuseStep 281303 = 421955) B421955
theorem B412523 : Blo 107783 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B183215 : Blo 107783 183215 := bstep (se 1 (by rfl) ⟨137411, by rfl⟩ : syracuseStep 183215 = 274823) B274823
theorem B248759 : Blo 107783 248759 := bstep (se 1 (by rfl) ⟨186569, by rfl⟩ : syracuseStep 248759 = 373139) B373139
theorem B281657 : Blo 107783 281657 := bstep (se 2 (by rfl) ⟨105621, by rfl⟩ : syracuseStep 281657 = 211243) B211243
theorem B904385 : Blo 107783 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B347453 : Blo 107783 347453 := bstep (se 3 (by rfl) ⟨65147, by rfl⟩ : syracuseStep 347453 = 130295) B130295
theorem B183647 : Blo 107783 183647 := bstep (se 1 (by rfl) ⟨137735, by rfl⟩ : syracuseStep 183647 = 275471) B275471
theorem B249353 : Blo 107783 249353 := bstep (se 2 (by rfl) ⟨93507, by rfl⟩ : syracuseStep 249353 = 187015) B187015
theorem B315019 : Blo 107783 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B249695 : Blo 107783 249695 := bstep (se 1 (by rfl) ⟨187271, by rfl⟩ : syracuseStep 249695 = 374543) B374543
theorem B1265543 : Blo 107783 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B184207 : Blo 107783 184207 := bstep (se 1 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 184207 = 276311) B276311
theorem B249875 : Blo 107783 249875 := bstep (se 1 (by rfl) ⟨187406, by rfl⟩ : syracuseStep 249875 = 374813) B374813
theorem B250217 : Blo 107783 250217 := bstep (se 2 (by rfl) ⟨93831, by rfl⟩ : syracuseStep 250217 = 187663) B187663
theorem B283099 : Blo 107783 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B184889 : Blo 107783 184889 := bstep (se 2 (by rfl) ⟨69333, by rfl⟩ : syracuseStep 184889 = 138667) B138667
theorem B1233467 : Blo 107783 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B905863 : Blo 107783 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B348887 : Blo 107783 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B3134213 : Blo 107783 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B250811 : Blo 107783 250811 := bstep (se 1 (by rfl) ⟨188108, by rfl⟩ : syracuseStep 250811 = 376217) B376217
theorem B2249693 : Blo 107783 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B250937 : Blo 107783 250937 := bstep (se 2 (by rfl) ⟨94101, by rfl⟩ : syracuseStep 250937 = 188203) B188203
theorem B185591 : Blo 107783 185591 := bstep (se 1 (by rfl) ⟨139193, by rfl⟩ : syracuseStep 185591 = 278387) B278387
theorem B251279 : Blo 107783 251279 := bstep (se 1 (by rfl) ⟨188459, by rfl⟩ : syracuseStep 251279 = 376919) B376919
theorem B185935 : Blo 107783 185935 := bstep (se 1 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 185935 = 278903) B278903
theorem B186185 : Blo 107783 186185 := bstep (se 2 (by rfl) ⟨69819, by rfl⟩ : syracuseStep 186185 = 139639) B139639
theorem B743303 : Blo 107783 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B808865 : Blo 107783 808865 := bstep (se 2 (by rfl) ⟨303324, by rfl⟩ : syracuseStep 808865 = 606649) B606649
theorem B710693 : Blo 107783 710693 := bstep (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) B133255
theorem B186617 : Blo 107783 186617 := bstep (se 2 (by rfl) ⟨69981, by rfl⟩ : syracuseStep 186617 = 139963) B139963
theorem B1038743 : Blo 107783 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B186799 : Blo 107783 186799 := bstep (se 1 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 186799 = 280199) B280199
theorem B4446667 : Blo 107783 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B809453 : Blo 107783 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B186887 : Blo 107783 186887 := bstep (se 1 (by rfl) ⟨140165, by rfl⟩ : syracuseStep 186887 = 280331) B280331
theorem B3758669 : Blo 107783 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B121423 : Blo 107783 121423 := bstep (se 1 (by rfl) ⟨91067, by rfl⟩ : syracuseStep 121423 = 182135) B182135
theorem B416441 : Blo 107783 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B318163 : Blo 107783 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B1432349 : Blo 107783 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B187231 : Blo 107783 187231 := bstep (se 1 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 187231 = 280847) B280847
theorem B154543 : Blo 107783 154543 := bstep (se 1 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 154543 = 231815) B231815
theorem B711607 : Blo 107783 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B187319 : Blo 107783 187319 := bstep (se 1 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 187319 = 280979) B280979
theorem B121819 : Blo 107783 121819 := bstep (se 1 (by rfl) ⟨91364, by rfl⟩ : syracuseStep 121819 = 182729) B182729
theorem B941401 : Blo 107783 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B122287 : Blo 107783 122287 := bstep (se 1 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 122287 = 183431) B183431
theorem B843209 : Blo 107783 843209 := bstep (se 2 (by rfl) ⟨316203, by rfl⟩ : syracuseStep 843209 = 632407) B632407
theorem B187913 : Blo 107783 187913 := bstep (se 2 (by rfl) ⟨70467, by rfl⟩ : syracuseStep 187913 = 140935) B140935
theorem B188075 : Blo 107783 188075 := bstep (se 1 (by rfl) ⟨141056, by rfl⟩ : syracuseStep 188075 = 282113) B282113
theorem B122719 : Blo 107783 122719 := bstep (se 1 (by rfl) ⟨92039, by rfl⟩ : syracuseStep 122719 = 184079) B184079
theorem B941959 : Blo 107783 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B286651 : Blo 107783 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B155687 : Blo 107783 155687 := bstep (se 1 (by rfl) ⟨116765, by rfl⟩ : syracuseStep 155687 = 233531) B233531
theorem B188473 : Blo 107783 188473 := bstep (se 2 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 188473 = 141355) B141355
theorem B123079 : Blo 107783 123079 := bstep (se 1 (by rfl) ⟨92309, by rfl⟩ : syracuseStep 123079 = 184619) B184619
theorem B188615 : Blo 107783 188615 := bstep (se 1 (by rfl) ⟨141461, by rfl⟩ : syracuseStep 188615 = 282923) B282923
theorem B221867 : Blo 107783 221867 := bstep (se 1 (by rfl) ⟨166400, by rfl⟩ : syracuseStep 221867 = 332801) B332801
theorem B418553 : Blo 107783 418553 := bstep (se 2 (by rfl) ⟨156957, by rfl⟩ : syracuseStep 418553 = 313915) B313915
theorem B418679 : Blo 107783 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B222095 : Blo 107783 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B22438853 : Blo 107783 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B123943 : Blo 107783 123943 := bstep (se 1 (by rfl) ⟨92957, by rfl⟩ : syracuseStep 123943 = 185915) B185915
theorem B1598939 : Blo 107783 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B779863 : Blo 107783 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B419539 : Blo 107783 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B190199 : Blo 107783 190199 := bstep (se 1 (by rfl) ⟨142649, by rfl⟩ : syracuseStep 190199 = 285299) B285299
theorem B420011 : Blo 107783 420011 := bstep (se 1 (by rfl) ⟨315008, by rfl⟩ : syracuseStep 420011 = 630017) B630017
theorem B125563 : Blo 107783 125563 := bstep (se 1 (by rfl) ⟨94172, by rfl⟩ : syracuseStep 125563 = 188345) B188345
theorem B551609 : Blo 107783 551609 := bstep (se 2 (by rfl) ⟨206853, by rfl⟩ : syracuseStep 551609 = 413707) B413707
theorem B715969 : Blo 107783 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B453899 : Blo 107783 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B5074319 : Blo 107783 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B356089 : Blo 107783 356089 := bstep (se 2 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 356089 = 267067) B267067
theorem B17592227 : Blo 107783 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B421969 : Blo 107783 421969 := bstep (se 2 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 421969 = 316477) B316477
theorem B192863 : Blo 107783 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B422273 : Blo 107783 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B356987 : Blo 107783 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B422729 : Blo 107783 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B422927 : Blo 107783 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B259129 : Blo 107783 259129 := bstep (se 2 (by rfl) ⟨97173, by rfl⟩ : syracuseStep 259129 = 194347) B194347
theorem B1406105 : Blo 107783 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B9565937 : Blo 107783 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B194447 : Blo 107783 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B161711 : Blo 107783 161711 := bstep (se 1 (by rfl) ⟨121283, by rfl⟩ : syracuseStep 161711 = 242567) B242567
theorem B161801 : Blo 107783 161801 := bstep (se 2 (by rfl) ⟨60675, by rfl⟩ : syracuseStep 161801 = 121351) B121351
theorem B161831 : Blo 107783 161831 := bstep (se 1 (by rfl) ⟨121373, by rfl⟩ : syracuseStep 161831 = 242747) B242747
theorem B161915 : Blo 107783 161915 := bstep (se 1 (by rfl) ⟨121436, by rfl⟩ : syracuseStep 161915 = 242873) B242873
theorem B162041 : Blo 107783 162041 := bstep (se 2 (by rfl) ⟨60765, by rfl⟩ : syracuseStep 162041 = 121531) B121531
theorem B162143 : Blo 107783 162143 := bstep (se 1 (by rfl) ⟨121607, by rfl⟩ : syracuseStep 162143 = 243215) B243215
theorem B162155 : Blo 107783 162155 := bstep (se 1 (by rfl) ⟨121616, by rfl⟩ : syracuseStep 162155 = 243233) B243233
theorem B162383 : Blo 107783 162383 := bstep (se 1 (by rfl) ⟨121787, by rfl⟩ : syracuseStep 162383 = 243575) B243575
theorem B162503 : Blo 107783 162503 := bstep (se 1 (by rfl) ⟨121877, by rfl⟩ : syracuseStep 162503 = 243755) B243755
theorem B162665 : Blo 107783 162665 := bstep (se 2 (by rfl) ⟨60999, by rfl⟩ : syracuseStep 162665 = 121999) B121999
theorem B392111 : Blo 107783 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B162743 : Blo 107783 162743 := bstep (se 1 (by rfl) ⟨122057, by rfl⟩ : syracuseStep 162743 = 244115) B244115
theorem B392123 : Blo 107783 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B162779 : Blo 107783 162779 := bstep (se 1 (by rfl) ⟨122084, by rfl⟩ : syracuseStep 162779 = 244169) B244169
theorem B163247 : Blo 107783 163247 := bstep (se 1 (by rfl) ⟨122435, by rfl⟩ : syracuseStep 163247 = 244871) B244871
theorem B163337 : Blo 107783 163337 := bstep (se 2 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 163337 = 122503) B122503
theorem B163367 : Blo 107783 163367 := bstep (se 1 (by rfl) ⟨122525, by rfl⟩ : syracuseStep 163367 = 245051) B245051
theorem B163451 : Blo 107783 163451 := bstep (se 1 (by rfl) ⟨122588, by rfl⟩ : syracuseStep 163451 = 245177) B245177
theorem B294611 : Blo 107783 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B818909 : Blo 107783 818909 := bstep (se 3 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 818909 = 307091) B307091
theorem B163577 : Blo 107783 163577 := bstep (se 2 (by rfl) ⟨61341, by rfl⟩ : syracuseStep 163577 = 122683) B122683
theorem B556793 : Blo 107783 556793 := bstep (se 2 (by rfl) ⟨208797, by rfl⟩ : syracuseStep 556793 = 417595) B417595
theorem B163679 : Blo 107783 163679 := bstep (se 1 (by rfl) ⟨122759, by rfl⟩ : syracuseStep 163679 = 245519) B245519
theorem B163691 : Blo 107783 163691 := bstep (se 1 (by rfl) ⟨122768, by rfl⟩ : syracuseStep 163691 = 245537) B245537
theorem B425915 : Blo 107783 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1048627 : Blo 107783 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B164105 : Blo 107783 164105 := bstep (se 2 (by rfl) ⟨61539, by rfl⟩ : syracuseStep 164105 = 123079) B123079
theorem B164207 : Blo 107783 164207 := bstep (se 1 (by rfl) ⟨123155, by rfl⟩ : syracuseStep 164207 = 246311) B246311
theorem B164423 : Blo 107783 164423 := bstep (se 1 (by rfl) ⟨123317, by rfl⟩ : syracuseStep 164423 = 246635) B246635
theorem B164459 : Blo 107783 164459 := bstep (se 1 (by rfl) ⟨123344, by rfl⟩ : syracuseStep 164459 = 246689) B246689
theorem B524983 : Blo 107783 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B393911 : Blo 107783 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B164687 : Blo 107783 164687 := bstep (se 1 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 164687 = 247031) B247031
theorem B361417 : Blo 107783 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B525275 : Blo 107783 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B820367 : Blo 107783 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B165083 : Blo 107783 165083 := bstep (se 1 (by rfl) ⟨123812, by rfl⟩ : syracuseStep 165083 = 247625) B247625
theorem B165257 : Blo 107783 165257 := bstep (se 2 (by rfl) ⟨61971, by rfl⟩ : syracuseStep 165257 = 123943) B123943
theorem B624185 : Blo 107783 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B165611 : Blo 107783 165611 := bstep (se 1 (by rfl) ⟨124208, by rfl⟩ : syracuseStep 165611 = 248417) B248417
theorem B198455 : Blo 107783 198455 := bstep (se 1 (by rfl) ⟨148841, by rfl⟩ : syracuseStep 198455 = 297683) B297683
theorem B165839 : Blo 107783 165839 := bstep (se 1 (by rfl) ⟨124379, by rfl⟩ : syracuseStep 165839 = 248759) B248759
theorem B231635 : Blo 107783 231635 := bstep (se 1 (by rfl) ⟨173726, by rfl⟩ : syracuseStep 231635 = 347453) B347453
theorem B461047 : Blo 107783 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B559385 : Blo 107783 559385 := bstep (se 2 (by rfl) ⟨209769, by rfl⟩ : syracuseStep 559385 = 419539) B419539
theorem B264539 : Blo 107783 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B166235 : Blo 107783 166235 := bstep (se 1 (by rfl) ⟨124676, by rfl⟩ : syracuseStep 166235 = 249353) B249353
theorem B264559 : Blo 107783 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B166463 : Blo 107783 166463 := bstep (se 1 (by rfl) ⟨124847, by rfl⟩ : syracuseStep 166463 = 249695) B249695
theorem B264875 : Blo 107783 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B133807 : Blo 107783 133807 := bstep (se 1 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 133807 = 200711) B200711
theorem B166583 : Blo 107783 166583 := bstep (se 1 (by rfl) ⟨124937, by rfl⟩ : syracuseStep 166583 = 249875) B249875
theorem B1182599 : Blo 107783 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B166811 : Blo 107783 166811 := bstep (se 1 (by rfl) ⟨125108, by rfl⟩ : syracuseStep 166811 = 250217) B250217
theorem B822311 : Blo 107783 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B593183 : Blo 107783 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B265511 : Blo 107783 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B167207 : Blo 107783 167207 := bstep (se 1 (by rfl) ⟨125405, by rfl⟩ : syracuseStep 167207 = 250811) B250811
theorem B265567 : Blo 107783 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B527735 : Blo 107783 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B167291 : Blo 107783 167291 := bstep (se 1 (by rfl) ⟨125468, by rfl⟩ : syracuseStep 167291 = 250937) B250937
theorem B232865 : Blo 107783 232865 := bstep (se 2 (by rfl) ⟨87324, by rfl⟩ : syracuseStep 232865 = 174649) B174649
theorem B167417 : Blo 107783 167417 := bstep (se 2 (by rfl) ⟨62781, by rfl⟩ : syracuseStep 167417 = 125563) B125563
theorem B527887 : Blo 107783 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B167519 : Blo 107783 167519 := bstep (se 1 (by rfl) ⟨125639, by rfl⟩ : syracuseStep 167519 = 251279) B251279
theorem B364445 : Blo 107783 364445 := bstep (se 3 (by rfl) ⟨68333, by rfl⟩ : syracuseStep 364445 = 136667) B136667
theorem B364553 : Blo 107783 364553 := bstep (se 2 (by rfl) ⟨136707, by rfl⟩ : syracuseStep 364553 = 273415) B273415
theorem B6951005 : Blo 107783 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B954625 : Blo 107783 954625 := bstep (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) B715969
theorem B692495 : Blo 107783 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B954899 : Blo 107783 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B398047 : Blo 107783 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B562139 : Blo 107783 562139 := bstep (se 1 (by rfl) ⟨421604, by rfl⟩ : syracuseStep 562139 = 843209) B843209
theorem B562301 : Blo 107783 562301 := bstep (se 3 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 562301 = 210863) B210863
theorem B562625 : Blo 107783 562625 := bstep (se 2 (by rfl) ⟨210984, by rfl⟩ : syracuseStep 562625 = 421969) B421969
theorem B235001 : Blo 107783 235001 := bstep (se 2 (by rfl) ⟨88125, by rfl⟩ : syracuseStep 235001 = 176251) B176251
theorem B137639 : Blo 107783 137639 := bstep (se 1 (by rfl) ⟨103229, by rfl⟩ : syracuseStep 137639 = 206459) B206459
theorem B137791 : Blo 107783 137791 := bstep (se 1 (by rfl) ⟨103343, by rfl⟩ : syracuseStep 137791 = 206687) B206687
theorem B137963 : Blo 107783 137963 := bstep (se 1 (by rfl) ⟨103472, by rfl⟩ : syracuseStep 137963 = 206945) B206945
theorem B236641 : Blo 107783 236641 := bstep (se 2 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 236641 = 177481) B177481
theorem B367739 : Blo 107783 367739 := bstep (se 1 (by rfl) ⟨275804, by rfl⟩ : syracuseStep 367739 = 551609) B551609
theorem B5020805 : Blo 107783 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B368009 : Blo 107783 368009 := bstep (se 2 (by rfl) ⟨138003, by rfl⟩ : syracuseStep 368009 = 276007) B276007
theorem B302599 : Blo 107783 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B3382879 : Blo 107783 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B138935 : Blo 107783 138935 := bstep (se 1 (by rfl) ⟨104201, by rfl⟩ : syracuseStep 138935 = 208403) B208403
theorem B368441 : Blo 107783 368441 := bstep (se 2 (by rfl) ⟨138165, by rfl⟩ : syracuseStep 368441 = 276331) B276331
theorem B139087 : Blo 107783 139087 := bstep (se 1 (by rfl) ⟨104315, by rfl⟩ : syracuseStep 139087 = 208631) B208631
theorem B1581065 : Blo 107783 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B237991 : Blo 107783 237991 := bstep (se 1 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 237991 = 356987) B356987
theorem B205267 : Blo 107783 205267 := bstep (se 1 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 205267 = 307901) B307901
theorem B402041 : Blo 107783 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B369305 : Blo 107783 369305 := bstep (se 2 (by rfl) ⟨138489, by rfl⟩ : syracuseStep 369305 = 276979) B276979
theorem B205487 : Blo 107783 205487 := bstep (se 1 (by rfl) ⟨154115, by rfl⟩ : syracuseStep 205487 = 308231) B308231
theorem B533441 : Blo 107783 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B4007029 : Blo 107783 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B206057 : Blo 107783 206057 := bstep (se 2 (by rfl) ⟨77271, by rfl⟩ : syracuseStep 206057 = 154543) B154543
theorem B107807 : Blo 107783 107807 := bstep (se 1 (by rfl) ⟨80855, by rfl⟩ : syracuseStep 107807 = 161711) B161711
theorem B107867 : Blo 107783 107867 := bstep (se 1 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 107867 = 161801) B161801
theorem B107887 : Blo 107783 107887 := bstep (se 1 (by rfl) ⟨80915, by rfl⟩ : syracuseStep 107887 = 161831) B161831
theorem B107943 : Blo 107783 107943 := bstep (se 1 (by rfl) ⟨80957, by rfl⟩ : syracuseStep 107943 = 161915) B161915
theorem B468413 : Blo 107783 468413 := bstep (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) B175655
theorem B108027 : Blo 107783 108027 := bstep (se 1 (by rfl) ⟨81020, by rfl⟩ : syracuseStep 108027 = 162041) B162041
theorem B108095 : Blo 107783 108095 := bstep (se 1 (by rfl) ⟨81071, by rfl⟩ : syracuseStep 108095 = 162143) B162143
theorem B108103 : Blo 107783 108103 := bstep (se 1 (by rfl) ⟨81077, by rfl⟩ : syracuseStep 108103 = 162155) B162155
theorem B108255 : Blo 107783 108255 := bstep (se 1 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 108255 = 162383) B162383
theorem B108335 : Blo 107783 108335 := bstep (se 1 (by rfl) ⟨81251, by rfl⟩ : syracuseStep 108335 = 162503) B162503
theorem B632681 : Blo 107783 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B108443 : Blo 107783 108443 := bstep (se 1 (by rfl) ⟨81332, by rfl⟩ : syracuseStep 108443 = 162665) B162665
theorem B108495 : Blo 107783 108495 := bstep (se 1 (by rfl) ⟨81371, by rfl⟩ : syracuseStep 108495 = 162743) B162743
theorem B108519 : Blo 107783 108519 := bstep (se 1 (by rfl) ⟨81389, by rfl⟩ : syracuseStep 108519 = 162779) B162779
theorem B5023781 : Blo 107783 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B370817 : Blo 107783 370817 := bstep (se 2 (by rfl) ⟨139056, by rfl⟩ : syracuseStep 370817 = 278113) B278113
theorem B108831 : Blo 107783 108831 := bstep (se 1 (by rfl) ⟨81623, by rfl⟩ : syracuseStep 108831 = 163247) B163247
theorem B108891 : Blo 107783 108891 := bstep (se 1 (by rfl) ⟨81668, by rfl⟩ : syracuseStep 108891 = 163337) B163337
theorem B108911 : Blo 107783 108911 := bstep (se 1 (by rfl) ⟨81683, by rfl⟩ : syracuseStep 108911 = 163367) B163367
theorem B108967 : Blo 107783 108967 := bstep (se 1 (by rfl) ⟨81725, by rfl⟩ : syracuseStep 108967 = 163451) B163451
theorem B109051 : Blo 107783 109051 := bstep (se 1 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 109051 = 163577) B163577
theorem B207355 : Blo 107783 207355 := bstep (se 1 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 207355 = 311033) B311033
theorem B371195 : Blo 107783 371195 := bstep (se 1 (by rfl) ⟨278396, by rfl⟩ : syracuseStep 371195 = 556793) B556793
theorem B109119 : Blo 107783 109119 := bstep (se 1 (by rfl) ⟨81839, by rfl⟩ : syracuseStep 109119 = 163679) B163679
theorem B109127 : Blo 107783 109127 := bstep (se 1 (by rfl) ⟨81845, by rfl⟩ : syracuseStep 109127 = 163691) B163691
theorem B207431 : Blo 107783 207431 := bstep (se 1 (by rfl) ⟨155573, by rfl⟩ : syracuseStep 207431 = 311147) B311147
theorem B273071 : Blo 107783 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B109279 : Blo 107783 109279 := bstep (se 1 (by rfl) ⟨81959, by rfl⟩ : syracuseStep 109279 = 163919) B163919
theorem B109359 : Blo 107783 109359 := bstep (se 1 (by rfl) ⟨82019, by rfl⟩ : syracuseStep 109359 = 164039) B164039
theorem B1321859 : Blo 107783 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B109467 : Blo 107783 109467 := bstep (se 1 (by rfl) ⟨82100, by rfl⟩ : syracuseStep 109467 = 164201) B164201
theorem B371627 : Blo 107783 371627 := bstep (se 1 (by rfl) ⟨278720, by rfl⟩ : syracuseStep 371627 = 557441) B557441
theorem B109519 : Blo 107783 109519 := bstep (se 1 (by rfl) ⟨82139, by rfl⟩ : syracuseStep 109519 = 164279) B164279
theorem B1420253 : Blo 107783 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B109543 : Blo 107783 109543 := bstep (se 1 (by rfl) ⟨82157, by rfl⟩ : syracuseStep 109543 = 164315) B164315
theorem B273395 : Blo 107783 273395 := bstep (se 1 (by rfl) ⟨205046, by rfl⟩ : syracuseStep 273395 = 410093) B410093
theorem B109855 : Blo 107783 109855 := bstep (se 1 (by rfl) ⟨82391, by rfl⟩ : syracuseStep 109855 = 164783) B164783
theorem B109915 : Blo 107783 109915 := bstep (se 1 (by rfl) ⟨82436, by rfl⟩ : syracuseStep 109915 = 164873) B164873
theorem B109935 : Blo 107783 109935 := bstep (se 1 (by rfl) ⟨82451, by rfl⟩ : syracuseStep 109935 = 164903) B164903
theorem B109991 : Blo 107783 109991 := bstep (se 1 (by rfl) ⟨82493, by rfl⟩ : syracuseStep 109991 = 164987) B164987
theorem B273851 : Blo 107783 273851 := bstep (se 1 (by rfl) ⟨205388, by rfl⟩ : syracuseStep 273851 = 410777) B410777
theorem B208327 : Blo 107783 208327 := bstep (se 1 (by rfl) ⟨156245, by rfl⟩ : syracuseStep 208327 = 312491) B312491
theorem B372167 : Blo 107783 372167 := bstep (se 1 (by rfl) ⟨279125, by rfl⟩ : syracuseStep 372167 = 558251) B558251
theorem B110075 : Blo 107783 110075 := bstep (se 1 (by rfl) ⟨82556, by rfl⟩ : syracuseStep 110075 = 165113) B165113
theorem B110143 : Blo 107783 110143 := bstep (se 1 (by rfl) ⟨82607, by rfl⟩ : syracuseStep 110143 = 165215) B165215
theorem B110151 : Blo 107783 110151 := bstep (se 1 (by rfl) ⟨82613, by rfl⟩ : syracuseStep 110151 = 165227) B165227
theorem B110303 : Blo 107783 110303 := bstep (se 1 (by rfl) ⟨82727, by rfl⟩ : syracuseStep 110303 = 165455) B165455
theorem B175879 : Blo 107783 175879 := bstep (se 1 (by rfl) ⟨131909, by rfl⟩ : syracuseStep 175879 = 263819) B263819
theorem B372491 : Blo 107783 372491 := bstep (se 1 (by rfl) ⟨279368, by rfl⟩ : syracuseStep 372491 = 558737) B558737
theorem B110383 : Blo 107783 110383 := bstep (se 1 (by rfl) ⟨82787, by rfl⟩ : syracuseStep 110383 = 165575) B165575
theorem B110491 : Blo 107783 110491 := bstep (se 1 (by rfl) ⟨82868, by rfl⟩ : syracuseStep 110491 = 165737) B165737
theorem B110543 : Blo 107783 110543 := bstep (se 1 (by rfl) ⟨82907, by rfl⟩ : syracuseStep 110543 = 165815) B165815
theorem B110567 : Blo 107783 110567 := bstep (se 1 (by rfl) ⟨82925, by rfl⟩ : syracuseStep 110567 = 165851) B165851
theorem B372761 : Blo 107783 372761 := bstep (se 2 (by rfl) ⟨139785, by rfl⟩ : syracuseStep 372761 = 279571) B279571
theorem B110879 : Blo 107783 110879 := bstep (se 1 (by rfl) ⟨83159, by rfl⟩ : syracuseStep 110879 = 166319) B166319
theorem B307547 : Blo 107783 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B110939 : Blo 107783 110939 := bstep (se 1 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 110939 = 166409) B166409
theorem B110959 : Blo 107783 110959 := bstep (se 1 (by rfl) ⟨83219, by rfl⟩ : syracuseStep 110959 = 166439) B166439
theorem B111015 : Blo 107783 111015 := bstep (se 1 (by rfl) ⟨83261, by rfl⟩ : syracuseStep 111015 = 166523) B166523
theorem B602587 : Blo 107783 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B111099 : Blo 107783 111099 := bstep (se 1 (by rfl) ⟨83324, by rfl⟩ : syracuseStep 111099 = 166649) B166649
theorem B930365 : Blo 107783 930365 := bstep (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) B348887
theorem B111167 : Blo 107783 111167 := bstep (se 1 (by rfl) ⟨83375, by rfl⟩ : syracuseStep 111167 = 166751) B166751
theorem B275015 : Blo 107783 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B111175 : Blo 107783 111175 := bstep (se 1 (by rfl) ⟨83381, by rfl⟩ : syracuseStep 111175 = 166763) B166763
theorem B111327 : Blo 107783 111327 := bstep (se 1 (by rfl) ⟨83495, by rfl⟩ : syracuseStep 111327 = 166991) B166991
theorem B111407 : Blo 107783 111407 := bstep (se 1 (by rfl) ⟨83555, by rfl⟩ : syracuseStep 111407 = 167111) B167111
theorem B111515 : Blo 107783 111515 := bstep (se 1 (by rfl) ⟨83636, by rfl⟩ : syracuseStep 111515 = 167273) B167273
theorem B242603 : Blo 107783 242603 := bstep (se 1 (by rfl) ⟨181952, by rfl⟩ : syracuseStep 242603 = 363905) B363905
theorem B635849 : Blo 107783 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B111567 : Blo 107783 111567 := bstep (se 1 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 111567 = 167351) B167351
theorem B111591 : Blo 107783 111591 := bstep (se 1 (by rfl) ⟨83693, by rfl⟩ : syracuseStep 111591 = 167387) B167387
theorem B374003 : Blo 107783 374003 := bstep (se 1 (by rfl) ⟨280502, by rfl⟩ : syracuseStep 374003 = 561005) B561005
theorem B374111 : Blo 107783 374111 := bstep (se 1 (by rfl) ⟨280583, by rfl⟩ : syracuseStep 374111 = 561167) B561167
theorem B243143 : Blo 107783 243143 := bstep (se 1 (by rfl) ⟨182357, by rfl⟩ : syracuseStep 243143 = 364715) B364715
theorem B243503 : Blo 107783 243503 := bstep (se 1 (by rfl) ⟨182627, by rfl⟩ : syracuseStep 243503 = 365255) B365255
theorem B276281 : Blo 107783 276281 := bstep (se 2 (by rfl) ⟨103605, by rfl⟩ : syracuseStep 276281 = 207211) B207211
theorem B3389303 : Blo 107783 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B244079 : Blo 107783 244079 := bstep (se 1 (by rfl) ⟨183059, by rfl⟩ : syracuseStep 244079 = 366119) B366119
theorem B244151 : Blo 107783 244151 := bstep (se 1 (by rfl) ⟨183113, by rfl⟩ : syracuseStep 244151 = 366227) B366227
theorem B833975 : Blo 107783 833975 := bstep (se 1 (by rfl) ⟨625481, by rfl⟩ : syracuseStep 833975 = 1250963) B1250963
theorem B244295 : Blo 107783 244295 := bstep (se 1 (by rfl) ⟨183221, by rfl⟩ : syracuseStep 244295 = 366443) B366443
theorem B244331 : Blo 107783 244331 := bstep (se 1 (by rfl) ⟨183248, by rfl⟩ : syracuseStep 244331 = 366497) B366497
theorem B539243 : Blo 107783 539243 := bstep (se 1 (by rfl) ⟨404432, by rfl⟩ : syracuseStep 539243 = 808865) B808865
theorem B473795 : Blo 107783 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B310007 : Blo 107783 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B375677 : Blo 107783 375677 := bstep (se 3 (by rfl) ⟨70439, by rfl⟩ : syracuseStep 375677 = 140879) B140879
theorem B539635 : Blo 107783 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B244727 : Blo 107783 244727 := bstep (se 1 (by rfl) ⟨183545, by rfl⟩ : syracuseStep 244727 = 367091) B367091
theorem B2505779 : Blo 107783 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B277627 : Blo 107783 277627 := bstep (se 1 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 277627 = 416441) B416441
theorem B375947 : Blo 107783 375947 := bstep (se 1 (by rfl) ⟨281960, by rfl⟩ : syracuseStep 375947 = 563921) B563921
theorem B933029 : Blo 107783 933029 := bstep (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) B174943
theorem B507197 : Blo 107783 507197 := bstep (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) B190199
theorem B245087 : Blo 107783 245087 := bstep (se 1 (by rfl) ⟨183815, by rfl⟩ : syracuseStep 245087 = 367631) B367631
theorem B474785 : Blo 107783 474785 := bstep (se 2 (by rfl) ⟨178044, by rfl⟩ : syracuseStep 474785 = 356089) B356089
theorem B1982141 : Blo 107783 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B245483 : Blo 107783 245483 := bstep (se 1 (by rfl) ⟨184112, by rfl⟩ : syracuseStep 245483 = 368225) B368225
theorem B179975 : Blo 107783 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B245609 : Blo 107783 245609 := bstep (se 2 (by rfl) ⟨92103, by rfl⟩ : syracuseStep 245609 = 184207) B184207
theorem B1982501 : Blo 107783 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B147911 : Blo 107783 147911 := bstep (se 1 (by rfl) ⟨110933, by rfl⟩ : syracuseStep 147911 = 221867) B221867
theorem B279035 : Blo 107783 279035 := bstep (se 1 (by rfl) ⟨209276, by rfl⟩ : syracuseStep 279035 = 418553) B418553
theorem B279119 : Blo 107783 279119 := bstep (se 1 (by rfl) ⟨209339, by rfl⟩ : syracuseStep 279119 = 418679) B418679
theorem B148063 : Blo 107783 148063 := bstep (se 1 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 148063 = 222095) B222095
theorem B377465 : Blo 107783 377465 := bstep (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) B283099
theorem B14959235 : Blo 107783 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B246455 : Blo 107783 246455 := bstep (se 1 (by rfl) ⟨184841, by rfl⟩ : syracuseStep 246455 = 369683) B369683
theorem B246671 : Blo 107783 246671 := bstep (se 1 (by rfl) ⟨185003, by rfl⟩ : syracuseStep 246671 = 370007) B370007
theorem B1065959 : Blo 107783 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B345505 : Blo 107783 345505 := bstep (se 2 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 345505 = 259129) B259129
theorem B2377133 : Blo 107783 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B280007 : Blo 107783 280007 := bstep (se 1 (by rfl) ⟨210005, by rfl⟩ : syracuseStep 280007 = 420011) B420011
theorem B280057 : Blo 107783 280057 := bstep (se 2 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 280057 = 210043) B210043
theorem B247391 : Blo 107783 247391 := bstep (se 1 (by rfl) ⟨185543, by rfl⟩ : syracuseStep 247391 = 371087) B371087
theorem B280361 : Blo 107783 280361 := bstep (se 2 (by rfl) ⟨105135, by rfl⟩ : syracuseStep 280361 = 210271) B210271
theorem B247607 : Blo 107783 247607 := bstep (se 1 (by rfl) ⟨185705, by rfl⟩ : syracuseStep 247607 = 371411) B371411
theorem B247913 : Blo 107783 247913 := bstep (se 2 (by rfl) ⟨92967, by rfl⟩ : syracuseStep 247913 = 185935) B185935
theorem B280705 : Blo 107783 280705 := bstep (se 2 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 280705 = 210529) B210529
theorem B1165603 : Blo 107783 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B182695 : Blo 107783 182695 := bstep (se 1 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 182695 = 274043) B274043
theorem B182857 : Blo 107783 182857 := bstep (se 2 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 182857 = 137143) B137143
theorem B248399 : Blo 107783 248399 := bstep (se 1 (by rfl) ⟨186299, by rfl⟩ : syracuseStep 248399 = 372599) B372599
theorem B182891 : Blo 107783 182891 := bstep (se 1 (by rfl) ⟨137168, by rfl⟩ : syracuseStep 182891 = 274337) B274337
theorem B248543 : Blo 107783 248543 := bstep (se 1 (by rfl) ⟨186407, by rfl⟩ : syracuseStep 248543 = 372815) B372815
theorem B4410085 : Blo 107783 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B314131 : Blo 107783 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B281515 : Blo 107783 281515 := bstep (se 1 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 281515 = 422273) B422273
theorem B248795 : Blo 107783 248795 := bstep (se 1 (by rfl) ⟨186596, by rfl⟩ : syracuseStep 248795 = 373193) B373193
theorem B248975 : Blo 107783 248975 := bstep (se 1 (by rfl) ⟨186731, by rfl⟩ : syracuseStep 248975 = 373463) B373463
theorem B2411693 : Blo 107783 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B281819 : Blo 107783 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B249065 : Blo 107783 249065 := bstep (se 2 (by rfl) ⟨93399, by rfl⟩ : syracuseStep 249065 = 186799) B186799
theorem B249119 : Blo 107783 249119 := bstep (se 1 (by rfl) ⟨186839, by rfl⟩ : syracuseStep 249119 = 373679) B373679
theorem B281951 : Blo 107783 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B937403 : Blo 107783 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B16305953 : Blo 107783 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B249641 : Blo 107783 249641 := bstep (se 2 (by rfl) ⟨93615, by rfl⟩ : syracuseStep 249641 = 187231) B187231
theorem B6377291 : Blo 107783 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B282649 : Blo 107783 282649 := bstep (se 2 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 282649 = 211987) B211987
theorem B3592421 : Blo 107783 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B184585 : Blo 107783 184585 := bstep (se 2 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 184585 = 138439) B138439
theorem B282953 : Blo 107783 282953 := bstep (se 2 (by rfl) ⟨106107, by rfl⟩ : syracuseStep 282953 = 212215) B212215
theorem B709181 : Blo 107783 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B250703 : Blo 107783 250703 := bstep (se 1 (by rfl) ⟨188027, by rfl⟩ : syracuseStep 250703 = 376055) B376055
theorem B414665 : Blo 107783 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B250919 : Blo 107783 250919 := bstep (se 1 (by rfl) ⟨188189, by rfl⟩ : syracuseStep 250919 = 376379) B376379
theorem B545939 : Blo 107783 545939 := bstep (se 1 (by rfl) ⟨409454, by rfl⟩ : syracuseStep 545939 = 818909) B818909
theorem B251099 : Blo 107783 251099 := bstep (se 1 (by rfl) ⟨188324, by rfl⟩ : syracuseStep 251099 = 376649) B376649
theorem B414953 : Blo 107783 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B316649 : Blo 107783 316649 := bstep (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) B237487
theorem B382201 : Blo 107783 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B283943 : Blo 107783 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B251297 : Blo 107783 251297 := bstep (se 2 (by rfl) ⟨94236, by rfl⟩ : syracuseStep 251297 = 188473) B188473
theorem B415165 : Blo 107783 415165 := bstep (se 3 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 415165 = 155687) B155687
theorem B186043 : Blo 107783 186043 := bstep (se 1 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 186043 = 279065) B279065
theorem B939863 : Blo 107783 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B121567 : Blo 107783 121567 := bstep (se 1 (by rfl) ⟨91175, by rfl⟩ : syracuseStep 121567 = 182351) B182351
theorem B187103 : Blo 107783 187103 := bstep (se 1 (by rfl) ⟨140327, by rfl⟩ : syracuseStep 187103 = 280655) B280655
theorem B187535 : Blo 107783 187535 := bstep (se 1 (by rfl) ⟨140651, by rfl⟩ : syracuseStep 187535 = 281303) B281303
theorem B122143 : Blo 107783 122143 := bstep (se 1 (by rfl) ⟨91607, by rfl⟩ : syracuseStep 122143 = 183215) B183215
theorem B187771 : Blo 107783 187771 := bstep (se 1 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 187771 = 281657) B281657
theorem B1039817 : Blo 107783 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B122431 : Blo 107783 122431 := bstep (se 1 (by rfl) ⟨91823, by rfl⟩ : syracuseStep 122431 = 183647) B183647
theorem B843695 : Blo 107783 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B549017 : Blo 107783 549017 := bstep (se 2 (by rfl) ⟨205881, by rfl⟩ : syracuseStep 549017 = 411763) B411763
theorem B352603 : Blo 107783 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B123259 : Blo 107783 123259 := bstep (se 1 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 123259 = 184889) B184889
theorem B221665 : Blo 107783 221665 := bstep (se 2 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 221665 = 166249) B166249
theorem B2089475 : Blo 107783 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1499795 : Blo 107783 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B123727 : Blo 107783 123727 := bstep (se 1 (by rfl) ⟨92795, by rfl⟩ : syracuseStep 123727 = 185591) B185591
theorem B549827 : Blo 107783 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B1532903 : Blo 107783 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B353423 : Blo 107783 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B124123 : Blo 107783 124123 := bstep (se 1 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 124123 = 186185) B186185
theorem B615869 : Blo 107783 615869 := bstep (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) B230951
theorem B124411 : Blo 107783 124411 := bstep (se 1 (by rfl) ⟨93308, by rfl⟩ : syracuseStep 124411 = 186617) B186617
theorem B714329 : Blo 107783 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B124591 : Blo 107783 124591 := bstep (se 1 (by rfl) ⟨93443, by rfl⟩ : syracuseStep 124591 = 186887) B186887
theorem B124879 : Blo 107783 124879 := bstep (se 1 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 124879 = 187319) B187319
theorem B420025 : Blo 107783 420025 := bstep (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) B315019
theorem B616643 : Blo 107783 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B125275 : Blo 107783 125275 := bstep (se 1 (by rfl) ⟨93956, by rfl⟩ : syracuseStep 125275 = 187913) B187913
theorem B518525 : Blo 107783 518525 := bstep (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) B194447
theorem B125383 : Blo 107783 125383 := bstep (se 1 (by rfl) ⟨94037, by rfl⟩ : syracuseStep 125383 = 188075) B188075
theorem B1075799 : Blo 107783 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B125743 : Blo 107783 125743 := bstep (se 1 (by rfl) ⟨94307, by rfl⟩ : syracuseStep 125743 = 188615) B188615
theorem B159175 : Blo 107783 159175 := bstep (se 1 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 159175 = 238763) B238763
theorem B1207817 : Blo 107783 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B913069 : Blo 107783 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B553391 : Blo 107783 553391 := bstep (se 1 (by rfl) ⟨415043, by rfl⟩ : syracuseStep 553391 = 830087) B830087
theorem B7959161 : Blo 107783 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B7893773 : Blo 107783 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B357473 : Blo 107783 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B11728151 : Blo 107783 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B947495 : Blo 107783 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B554363 : Blo 107783 554363 := bstep (se 1 (by rfl) ⟨415772, by rfl⟩ : syracuseStep 554363 = 831545) B831545
theorem B128575 : Blo 107783 128575 := bstep (se 1 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 128575 = 192863) B192863
theorem B5928889 : Blo 107783 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B161897 : Blo 107783 161897 := bstep (se 2 (by rfl) ⟨60711, by rfl⟩ : syracuseStep 161897 = 121423) B121423
theorem B424217 : Blo 107783 424217 := bstep (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) B318163
theorem B4290893 : Blo 107783 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B162215 : Blo 107783 162215 := bstep (se 1 (by rfl) ⟨121661, by rfl⟩ : syracuseStep 162215 = 243323) B243323
theorem B162299 : Blo 107783 162299 := bstep (se 1 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 162299 = 243449) B243449
theorem B1243673 : Blo 107783 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B948809 : Blo 107783 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B457289 : Blo 107783 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B162425 : Blo 107783 162425 := bstep (se 2 (by rfl) ⟨60909, by rfl⟩ : syracuseStep 162425 = 121819) B121819
theorem B555659 : Blo 107783 555659 := bstep (se 1 (by rfl) ⟨416744, by rfl⟩ : syracuseStep 555659 = 833489) B833489
theorem B162479 : Blo 107783 162479 := bstep (se 1 (by rfl) ⟨121859, by rfl⟩ : syracuseStep 162479 = 243719) B243719
theorem B162527 : Blo 107783 162527 := bstep (se 1 (by rfl) ⟨121895, by rfl⟩ : syracuseStep 162527 = 243791) B243791
theorem B162791 : Blo 107783 162791 := bstep (se 1 (by rfl) ⟨122093, by rfl⟩ : syracuseStep 162791 = 244187) B244187
theorem B785629 : Blo 107783 785629 := bstep (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) B294611
theorem B163049 : Blo 107783 163049 := bstep (se 2 (by rfl) ⟨61143, by rfl⟩ : syracuseStep 163049 = 122287) B122287
theorem B163103 : Blo 107783 163103 := bstep (se 1 (by rfl) ⟨122327, by rfl⟩ : syracuseStep 163103 = 244655) B244655
theorem B261407 : Blo 107783 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B261415 : Blo 107783 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B163271 : Blo 107783 163271 := bstep (se 1 (by rfl) ⟨122453, by rfl⟩ : syracuseStep 163271 = 244907) B244907
theorem B1146383 : Blo 107783 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B163625 : Blo 107783 163625 := bstep (se 2 (by rfl) ⟨61359, by rfl⟩ : syracuseStep 163625 = 122719) B122719
theorem B163631 : Blo 107783 163631 := bstep (se 1 (by rfl) ⟨122723, by rfl⟩ : syracuseStep 163631 = 245447) B245447
theorem B262607 : Blo 107783 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B164303 : Blo 107783 164303 := bstep (se 1 (by rfl) ⟨123227, by rfl⟩ : syracuseStep 164303 = 246455) B246455
theorem B164345 : Blo 107783 164345 := bstep (se 2 (by rfl) ⟨61629, by rfl⟩ : syracuseStep 164345 = 123259) B123259
theorem B164447 : Blo 107783 164447 := bstep (se 1 (by rfl) ⟨123335, by rfl⟩ : syracuseStep 164447 = 246671) B246671
theorem B295553 : Blo 107783 295553 := bstep (se 2 (by rfl) ⟨110832, by rfl⟩ : syracuseStep 295553 = 221665) B221665
theorem B197417 : Blo 107783 197417 := bstep (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) B148063
theorem B164927 : Blo 107783 164927 := bstep (se 1 (by rfl) ⟨123695, by rfl⟩ : syracuseStep 164927 = 247391) B247391
theorem B164969 : Blo 107783 164969 := bstep (se 2 (by rfl) ⟨61863, by rfl⟩ : syracuseStep 164969 = 123727) B123727
theorem B165071 : Blo 107783 165071 := bstep (se 1 (by rfl) ⟨123803, by rfl⟩ : syracuseStep 165071 = 247607) B247607
theorem B165275 : Blo 107783 165275 := bstep (se 1 (by rfl) ⟨123956, by rfl⟩ : syracuseStep 165275 = 247913) B247913
theorem B5342705 : Blo 107783 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B165497 : Blo 107783 165497 := bstep (se 2 (by rfl) ⟨62061, by rfl⟩ : syracuseStep 165497 = 124123) B124123
theorem B165599 : Blo 107783 165599 := bstep (se 1 (by rfl) ⟨124199, by rfl⟩ : syracuseStep 165599 = 248399) B248399
theorem B165695 : Blo 107783 165695 := bstep (se 1 (by rfl) ⟨124271, by rfl⟩ : syracuseStep 165695 = 248543) B248543
theorem B460673 : Blo 107783 460673 := bstep (se 2 (by rfl) ⟨172752, by rfl⟩ : syracuseStep 460673 = 345505) B345505
theorem B788399 : Blo 107783 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B165863 : Blo 107783 165863 := bstep (se 1 (by rfl) ⟨124397, by rfl⟩ : syracuseStep 165863 = 248795) B248795
theorem B165881 : Blo 107783 165881 := bstep (se 2 (by rfl) ⟨62205, by rfl⟩ : syracuseStep 165881 = 124411) B124411
theorem B165983 : Blo 107783 165983 := bstep (se 1 (by rfl) ⟨124487, by rfl⟩ : syracuseStep 165983 = 248975) B248975
theorem B1607795 : Blo 107783 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B166043 : Blo 107783 166043 := bstep (se 1 (by rfl) ⟨124532, by rfl⟩ : syracuseStep 166043 = 249065) B249065
theorem B395455 : Blo 107783 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B166079 : Blo 107783 166079 := bstep (se 1 (by rfl) ⟨124559, by rfl⟩ : syracuseStep 166079 = 249119) B249119
theorem B166121 : Blo 107783 166121 := bstep (se 2 (by rfl) ⟨62295, by rfl⟩ : syracuseStep 166121 = 124591) B124591
theorem B624935 : Blo 107783 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B166427 : Blo 107783 166427 := bstep (se 1 (by rfl) ⟨124820, by rfl⟩ : syracuseStep 166427 = 249641) B249641
theorem B166505 : Blo 107783 166505 := bstep (se 2 (by rfl) ⟨62439, by rfl⟩ : syracuseStep 166505 = 124879) B124879
theorem B2394947 : Blo 107783 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B461663 : Blo 107783 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B560033 : Blo 107783 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B167033 : Blo 107783 167033 := bstep (se 2 (by rfl) ⟨62637, by rfl⟩ : syracuseStep 167033 = 125275) B125275
theorem B167135 : Blo 107783 167135 := bstep (se 1 (by rfl) ⟨125351, by rfl⟩ : syracuseStep 167135 = 250703) B250703
theorem B167177 : Blo 107783 167177 := bstep (se 2 (by rfl) ⟨62691, by rfl⟩ : syracuseStep 167177 = 125383) B125383
theorem B167279 : Blo 107783 167279 := bstep (se 1 (by rfl) ⟨125459, by rfl⟩ : syracuseStep 167279 = 250919) B250919
theorem B363959 : Blo 107783 363959 := bstep (se 1 (by rfl) ⟨272969, by rfl⟩ : syracuseStep 363959 = 545939) B545939
theorem B2526653 : Blo 107783 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B757181 : Blo 107783 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B167399 : Blo 107783 167399 := bstep (se 1 (by rfl) ⟨125549, by rfl⟩ : syracuseStep 167399 = 251099) B251099
theorem B167531 : Blo 107783 167531 := bstep (se 1 (by rfl) ⟨125648, by rfl⟩ : syracuseStep 167531 = 251297) B251297
theorem B167657 : Blo 107783 167657 := bstep (se 2 (by rfl) ⟨62871, by rfl⟩ : syracuseStep 167657 = 125743) B125743
theorem B626575 : Blo 107783 626575 := bstep (se 1 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 626575 = 939863) B939863
theorem B1577717 : Blo 107783 1577717 := bstep (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) B147911
theorem B3347203 : Blo 107783 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B529213 : Blo 107783 529213 := bstep (se 3 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 529213 = 198455) B198455
theorem B1217425 : Blo 107783 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B693211 : Blo 107783 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B234505 : Blo 107783 234505 := bstep (se 2 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 234505 = 175879) B175879
theorem B562463 : Blo 107783 562463 := bstep (se 1 (by rfl) ⟨421847, by rfl⟩ : syracuseStep 562463 = 843695) B843695
theorem B1054043 : Blo 107783 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B366011 : Blo 107783 366011 := bstep (se 1 (by rfl) ⟨274508, by rfl⟩ : syracuseStep 366011 = 549017) B549017
theorem B136991 : Blo 107783 136991 := bstep (se 1 (by rfl) ⟨102743, by rfl⟩ : syracuseStep 136991 = 205487) B205487
theorem B366551 : Blo 107783 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B137371 : Blo 107783 137371 := bstep (se 1 (by rfl) ⟨103028, by rfl⟩ : syracuseStep 137371 = 206057) B206057
theorem B530729 : Blo 107783 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B367037 : Blo 107783 367037 := bstep (se 3 (by rfl) ⟨68819, by rfl⟩ : syracuseStep 367037 = 137639) B137639
theorem B2038405 : Blo 107783 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B3349187 : Blo 107783 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B138287 : Blo 107783 138287 := bstep (se 1 (by rfl) ⟨103715, by rfl⟩ : syracuseStep 138287 = 207431) B207431
theorem B367901 : Blo 107783 367901 := bstep (se 3 (by rfl) ⟨68981, by rfl⟩ : syracuseStep 367901 = 137963) B137963
theorem B826685 : Blo 107783 826685 := bstep (se 3 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 826685 = 310007) B310007
theorem B171433 : Blo 107783 171433 := bstep (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) B128575
theorem B7905185 : Blo 107783 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B205031 : Blo 107783 205031 := bstep (se 1 (by rfl) ⟨153773, by rfl⟩ : syracuseStep 205031 = 307547) B307547
theorem B368927 : Blo 107783 368927 := bstep (se 1 (by rfl) ⟨276695, by rfl⟩ : syracuseStep 368927 = 553391) B553391
theorem B238315 : Blo 107783 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B697085 : Blo 107783 697085 := bstep (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) B261407
theorem B369575 : Blo 107783 369575 := bstep (se 1 (by rfl) ⟨277181, by rfl⟩ : syracuseStep 369575 = 554363) B554363
theorem B107931 : Blo 107783 107931 := bstep (se 1 (by rfl) ⟨80948, by rfl⟩ : syracuseStep 107931 = 161897) B161897
theorem B370169 : Blo 107783 370169 := bstep (se 2 (by rfl) ⟨138813, by rfl⟩ : syracuseStep 370169 = 277627) B277627
theorem B2860595 : Blo 107783 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B108143 : Blo 107783 108143 := bstep (se 1 (by rfl) ⟨81107, by rfl⟩ : syracuseStep 108143 = 162215) B162215
theorem B108199 : Blo 107783 108199 := bstep (se 1 (by rfl) ⟨81149, by rfl⟩ : syracuseStep 108199 = 162299) B162299
theorem B829115 : Blo 107783 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B632539 : Blo 107783 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B304859 : Blo 107783 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B108283 : Blo 107783 108283 := bstep (se 1 (by rfl) ⟨81212, by rfl⟩ : syracuseStep 108283 = 162425) B162425
theorem B370439 : Blo 107783 370439 := bstep (se 1 (by rfl) ⟨277829, by rfl⟩ : syracuseStep 370439 = 555659) B555659
theorem B108319 : Blo 107783 108319 := bstep (se 1 (by rfl) ⟨81239, by rfl⟩ : syracuseStep 108319 = 162479) B162479
theorem B370493 : Blo 107783 370493 := bstep (se 3 (by rfl) ⟨69467, by rfl⟩ : syracuseStep 370493 = 138935) B138935
theorem B108351 : Blo 107783 108351 := bstep (se 1 (by rfl) ⟨81263, by rfl⟩ : syracuseStep 108351 = 162527) B162527
theorem B108527 : Blo 107783 108527 := bstep (se 1 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 108527 = 162791) B162791
theorem B403465 : Blo 107783 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B108699 : Blo 107783 108699 := bstep (se 1 (by rfl) ⟨81524, by rfl⟩ : syracuseStep 108699 = 163049) B163049
theorem B108735 : Blo 107783 108735 := bstep (se 1 (by rfl) ⟨81551, by rfl⟩ : syracuseStep 108735 = 163103) B163103
theorem B338131 : Blo 107783 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B108847 : Blo 107783 108847 := bstep (se 1 (by rfl) ⟨81635, by rfl⟩ : syracuseStep 108847 = 163271) B163271
theorem B764255 : Blo 107783 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B1321427 : Blo 107783 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B109083 : Blo 107783 109083 := bstep (se 1 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 109083 = 163625) B163625
theorem B109087 : Blo 107783 109087 := bstep (se 1 (by rfl) ⟨81815, by rfl⟩ : syracuseStep 109087 = 163631) B163631
theorem B1321667 : Blo 107783 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B109403 : Blo 107783 109403 := bstep (se 1 (by rfl) ⟨82052, by rfl⟩ : syracuseStep 109403 = 164105) B164105
theorem B109471 : Blo 107783 109471 := bstep (se 1 (by rfl) ⟨82103, by rfl⟩ : syracuseStep 109471 = 164207) B164207
theorem B109615 : Blo 107783 109615 := bstep (se 1 (by rfl) ⟨82211, by rfl⟩ : syracuseStep 109615 = 164423) B164423
theorem B109639 : Blo 107783 109639 := bstep (se 1 (by rfl) ⟨82229, by rfl⟩ : syracuseStep 109639 = 164459) B164459
theorem B9972823 : Blo 107783 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B470137 : Blo 107783 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B109791 : Blo 107783 109791 := bstep (se 1 (by rfl) ⟨82343, by rfl⟩ : syracuseStep 109791 = 164687) B164687
theorem B273689 : Blo 107783 273689 := bstep (se 2 (by rfl) ⟨102633, by rfl⟩ : syracuseStep 273689 = 205267) B205267
theorem B110055 : Blo 107783 110055 := bstep (se 1 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 110055 = 165083) B165083
theorem B699977 : Blo 107783 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B110171 : Blo 107783 110171 := bstep (se 1 (by rfl) ⟨82628, by rfl⟩ : syracuseStep 110171 = 165257) B165257
theorem B1584755 : Blo 107783 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B110407 : Blo 107783 110407 := bstep (se 1 (by rfl) ⟨82805, by rfl⟩ : syracuseStep 110407 = 165611) B165611
theorem B110559 : Blo 107783 110559 := bstep (se 1 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 110559 = 165839) B165839
theorem B372923 : Blo 107783 372923 := bstep (se 1 (by rfl) ⟨279692, by rfl⟩ : syracuseStep 372923 = 559385) B559385
theorem B176359 : Blo 107783 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B110823 : Blo 107783 110823 := bstep (se 1 (by rfl) ⟨83117, by rfl⟩ : syracuseStep 110823 = 166235) B166235
theorem B110975 : Blo 107783 110975 := bstep (se 1 (by rfl) ⟨83231, by rfl⟩ : syracuseStep 110975 = 166463) B166463
theorem B111055 : Blo 107783 111055 := bstep (se 1 (by rfl) ⟨83291, by rfl⟩ : syracuseStep 111055 = 166583) B166583
theorem B111207 : Blo 107783 111207 := bstep (se 1 (by rfl) ⟨83405, by rfl⟩ : syracuseStep 111207 = 166811) B166811
theorem B373409 : Blo 107783 373409 := bstep (se 2 (by rfl) ⟨140028, by rfl⟩ : syracuseStep 373409 = 280057) B280057
theorem B177007 : Blo 107783 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B111471 : Blo 107783 111471 := bstep (se 1 (by rfl) ⟨83603, by rfl⟩ : syracuseStep 111471 = 167207) B167207
theorem B111527 : Blo 107783 111527 := bstep (se 1 (by rfl) ⟨83645, by rfl⟩ : syracuseStep 111527 = 167291) B167291
theorem B111611 : Blo 107783 111611 := bstep (se 1 (by rfl) ⟨83708, by rfl⟩ : syracuseStep 111611 = 167417) B167417
theorem B111679 : Blo 107783 111679 := bstep (se 1 (by rfl) ⟨83759, by rfl⟩ : syracuseStep 111679 = 167519) B167519
theorem B242963 : Blo 107783 242963 := bstep (se 1 (by rfl) ⟨182222, by rfl⟩ : syracuseStep 242963 = 364445) B364445
theorem B243035 : Blo 107783 243035 := bstep (se 1 (by rfl) ⟨182276, by rfl⟩ : syracuseStep 243035 = 364553) B364553
theorem B4634003 : Blo 107783 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B374273 : Blo 107783 374273 := bstep (se 2 (by rfl) ⟨140352, by rfl⟩ : syracuseStep 374273 = 280705) B280705
theorem B636599 : Blo 107783 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B472787 : Blo 107783 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B1554137 : Blo 107783 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B243593 : Blo 107783 243593 := bstep (se 2 (by rfl) ⟨91347, by rfl⟩ : syracuseStep 243593 = 182695) B182695
theorem B276443 : Blo 107783 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B374759 : Blo 107783 374759 := bstep (se 1 (by rfl) ⟨281069, by rfl⟩ : syracuseStep 374759 = 562139) B562139
theorem B276473 : Blo 107783 276473 := bstep (se 2 (by rfl) ⟨103677, by rfl⟩ : syracuseStep 276473 = 207355) B207355
theorem B374867 : Blo 107783 374867 := bstep (se 1 (by rfl) ⟨281150, by rfl⟩ : syracuseStep 374867 = 562301) B562301
theorem B243809 : Blo 107783 243809 := bstep (se 2 (by rfl) ⟨91428, by rfl⟩ : syracuseStep 243809 = 182857) B182857
theorem B276635 : Blo 107783 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B211099 : Blo 107783 211099 := bstep (se 1 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 211099 = 316649) B316649
theorem B178409 : Blo 107783 178409 := bstep (se 2 (by rfl) ⟨66903, by rfl⟩ : syracuseStep 178409 = 133807) B133807
theorem B375083 : Blo 107783 375083 := bstep (se 1 (by rfl) ⟨281312, by rfl⟩ : syracuseStep 375083 = 562625) B562625
theorem B5880113 : Blo 107783 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B375353 : Blo 107783 375353 := bstep (se 2 (by rfl) ⟨140757, by rfl⟩ : syracuseStep 375353 = 281515) B281515
theorem B277769 : Blo 107783 277769 := bstep (se 2 (by rfl) ⟨104163, by rfl⟩ : syracuseStep 277769 = 208327) B208327
theorem B703849 : Blo 107783 703849 := bstep (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) B527887
theorem B245159 : Blo 107783 245159 := bstep (se 1 (by rfl) ⟨183869, by rfl⟩ : syracuseStep 245159 = 367739) B367739
theorem B245339 : Blo 107783 245339 := bstep (se 1 (by rfl) ⟨184004, by rfl⟩ : syracuseStep 245339 = 368009) B368009
theorem B245627 : Blo 107783 245627 := bstep (se 1 (by rfl) ⟨184220, by rfl⟩ : syracuseStep 245627 = 368441) B368441
theorem B376865 : Blo 107783 376865 := bstep (se 2 (by rfl) ⟨141324, by rfl⟩ : syracuseStep 376865 = 282649) B282649
theorem B1392983 : Blo 107783 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B246113 : Blo 107783 246113 := bstep (se 2 (by rfl) ⟨92292, by rfl⟩ : syracuseStep 246113 = 184585) B184585
theorem B999863 : Blo 107783 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B246203 : Blo 107783 246203 := bstep (se 1 (by rfl) ⟨184652, by rfl⟩ : syracuseStep 246203 = 369305) B369305
theorem B803449 : Blo 107783 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B410579 : Blo 107783 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B312275 : Blo 107783 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B476219 : Blo 107783 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B247211 : Blo 107783 247211 := bstep (se 1 (by rfl) ⟨185408, by rfl⟩ : syracuseStep 247211 = 370817) B370817
theorem B411095 : Blo 107783 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B2868797 : Blo 107783 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B345683 : Blo 107783 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B247463 : Blo 107783 247463 := bstep (se 1 (by rfl) ⟨185597, by rfl⟩ : syracuseStep 247463 = 371195) B371195
theorem B706333 : Blo 107783 706333 := bstep (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) B264875
theorem B182047 : Blo 107783 182047 := bstep (se 1 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 182047 = 273071) B273071
theorem B247751 : Blo 107783 247751 := bstep (se 1 (by rfl) ⟨185813, by rfl⟩ : syracuseStep 247751 = 371627) B371627
theorem B182263 : Blo 107783 182263 := bstep (se 1 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 182263 = 273395) B273395
theorem B248057 : Blo 107783 248057 := bstep (se 2 (by rfl) ⟨93021, by rfl⟩ : syracuseStep 248057 = 186043) B186043
theorem B182567 : Blo 107783 182567 := bstep (se 1 (by rfl) ⟨136925, by rfl⟩ : syracuseStep 182567 = 273851) B273851
theorem B248111 : Blo 107783 248111 := bstep (se 1 (by rfl) ⟨186083, by rfl⟩ : syracuseStep 248111 = 372167) B372167
theorem B805211 : Blo 107783 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B248327 : Blo 107783 248327 := bstep (se 1 (by rfl) ⟨186245, by rfl⟩ : syracuseStep 248327 = 372491) B372491
theorem B248507 : Blo 107783 248507 := bstep (se 1 (by rfl) ⟨186380, by rfl⟩ : syracuseStep 248507 = 372761) B372761
theorem B183343 : Blo 107783 183343 := bstep (se 1 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 183343 = 275015) B275015
theorem B5262515 : Blo 107783 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B183721 : Blo 107783 183721 := bstep (se 2 (by rfl) ⟨68895, by rfl⟩ : syracuseStep 183721 = 137791) B137791
theorem B249335 : Blo 107783 249335 := bstep (se 1 (by rfl) ⟨187001, by rfl⟩ : syracuseStep 249335 = 374003) B374003
theorem B7818767 : Blo 107783 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B249407 : Blo 107783 249407 := bstep (se 1 (by rfl) ⟨187055, by rfl⟩ : syracuseStep 249407 = 374111) B374111
theorem B184187 : Blo 107783 184187 := bstep (se 1 (by rfl) ⟨138140, by rfl⟩ : syracuseStep 184187 = 276281) B276281
theorem B315521 : Blo 107783 315521 := bstep (se 2 (by rfl) ⟨118320, by rfl⟩ : syracuseStep 315521 = 236641) B236641
theorem B282811 : Blo 107783 282811 := bstep (se 1 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 282811 = 424217) B424217
theorem B348553 : Blo 107783 348553 := bstep (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) B261415
theorem B741797 : Blo 107783 741797 := bstep (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) B139087
theorem B315863 : Blo 107783 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B250361 : Blo 107783 250361 := bstep (se 2 (by rfl) ⟨93885, by rfl⟩ : syracuseStep 250361 = 187771) B187771
theorem B250451 : Blo 107783 250451 := bstep (se 1 (by rfl) ⟨187838, by rfl⟩ : syracuseStep 250451 = 375677) B375677
theorem B479933 : Blo 107783 479933 := bstep (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) B179975
theorem B250631 : Blo 107783 250631 := bstep (se 1 (by rfl) ⟨187973, by rfl⟩ : syracuseStep 250631 = 375947) B375947
theorem B4510505 : Blo 107783 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B185449 : Blo 107783 185449 := bstep (se 2 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 185449 = 139087) B139087
theorem B316523 : Blo 107783 316523 := bstep (se 1 (by rfl) ⟨237392, by rfl⟩ : syracuseStep 316523 = 474785) B474785
theorem B1398169 : Blo 107783 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B186023 : Blo 107783 186023 := bstep (se 1 (by rfl) ⟨139517, by rfl⟩ : syracuseStep 186023 = 279035) B279035
theorem B186079 : Blo 107783 186079 := bstep (se 1 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 186079 = 279119) B279119
theorem B317321 : Blo 107783 317321 := bstep (se 2 (by rfl) ⟨118995, by rfl⟩ : syracuseStep 317321 = 237991) B237991
theorem B350183 : Blo 107783 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B710639 : Blo 107783 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B546911 : Blo 107783 546911 := bstep (se 1 (by rfl) ⟨410183, by rfl⟩ : syracuseStep 546911 = 820367) B820367
theorem B186671 : Blo 107783 186671 := bstep (se 1 (by rfl) ⟨140003, by rfl⟩ : syracuseStep 186671 = 280007) B280007
theorem B416123 : Blo 107783 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B186907 : Blo 107783 186907 := bstep (se 1 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 186907 = 280361) B280361
theorem B481889 : Blo 107783 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B154423 : Blo 107783 154423 := bstep (se 1 (by rfl) ⟨115817, by rfl⟩ : syracuseStep 154423 = 231635) B231635
theorem B1006573 : Blo 107783 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B1072109 : Blo 107783 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B121927 : Blo 107783 121927 := bstep (se 1 (by rfl) ⟨91445, by rfl⟩ : syracuseStep 121927 = 182891) B182891
theorem B548207 : Blo 107783 548207 := bstep (se 1 (by rfl) ⟨411155, by rfl⟩ : syracuseStep 548207 = 822311) B822311
theorem B187879 : Blo 107783 187879 := bstep (se 1 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 187879 = 281819) B281819
theorem B187967 : Blo 107783 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B351823 : Blo 107783 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B155243 : Blo 107783 155243 := bstep (se 1 (by rfl) ⟨116432, by rfl⟩ : syracuseStep 155243 = 232865) B232865
theorem B4251527 : Blo 107783 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B4087741 : Blo 107783 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B188635 : Blo 107783 188635 := bstep (se 1 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 188635 = 282953) B282953
theorem B614729 : Blo 107783 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B942461 : Blo 107783 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B352745 : Blo 107783 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B156667 : Blo 107783 156667 := bstep (se 1 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 156667 = 235001) B235001
theorem B418841 : Blo 107783 418841 := bstep (se 2 (by rfl) ⟨157065, by rfl⟩ : syracuseStep 418841 = 314131) B314131
theorem B354089 : Blo 107783 354089 := bstep (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) B265567
theorem B124735 : Blo 107783 124735 := bstep (se 1 (by rfl) ⟨93551, by rfl⟩ : syracuseStep 124735 = 187103) B187103
theorem B125023 : Blo 107783 125023 := bstep (se 1 (by rfl) ⟨93767, by rfl⟩ : syracuseStep 125023 = 187535) B187535
theorem B9038141 : Blo 107783 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1272833 : Blo 107783 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B355627 : Blo 107783 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B421787 : Blo 107783 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B553553 : Blo 107783 553553 := bstep (se 2 (by rfl) ⟨207582, by rfl⟩ : syracuseStep 553553 = 415165) B415165
theorem B881239 : Blo 107783 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B946835 : Blo 107783 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B848933 : Blo 107783 848933 := bstep (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) B159175
theorem B173930165 : Blo 107783 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B620243 : Blo 107783 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B5306107 : Blo 107783 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B161735 : Blo 107783 161735 := bstep (se 1 (by rfl) ⟨121301, by rfl⟩ : syracuseStep 161735 = 242603) B242603
theorem B423899 : Blo 107783 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B162089 : Blo 107783 162089 := bstep (se 2 (by rfl) ⟨60783, by rfl⟩ : syracuseStep 162089 = 121567) B121567
theorem B162095 : Blo 107783 162095 := bstep (se 1 (by rfl) ⟨121571, by rfl⟩ : syracuseStep 162095 = 243143) B243143
theorem B162335 : Blo 107783 162335 := bstep (se 1 (by rfl) ⟨121751, by rfl⟩ : syracuseStep 162335 = 243503) B243503
theorem B719513 : Blo 107783 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B162719 : Blo 107783 162719 := bstep (se 1 (by rfl) ⟨122039, by rfl⟩ : syracuseStep 162719 = 244079) B244079
theorem B162767 : Blo 107783 162767 := bstep (se 1 (by rfl) ⟨122075, by rfl⟩ : syracuseStep 162767 = 244151) B244151
theorem B555983 : Blo 107783 555983 := bstep (se 1 (by rfl) ⟨416987, by rfl⟩ : syracuseStep 555983 = 833975) B833975
theorem B1047505 : Blo 107783 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B162857 : Blo 107783 162857 := bstep (se 2 (by rfl) ⟨61071, by rfl⟩ : syracuseStep 162857 = 122143) B122143
theorem B162863 : Blo 107783 162863 := bstep (se 1 (by rfl) ⟨122147, by rfl⟩ : syracuseStep 162863 = 244295) B244295
theorem B162887 : Blo 107783 162887 := bstep (se 1 (by rfl) ⟨122165, by rfl⟩ : syracuseStep 162887 = 244331) B244331
theorem B359495 : Blo 107783 359495 := bstep (se 1 (by rfl) ⟨269621, by rfl⟩ : syracuseStep 359495 = 539243) B539243
theorem B163151 : Blo 107783 163151 := bstep (se 1 (by rfl) ⟨122363, by rfl⟩ : syracuseStep 163151 = 244727) B244727
theorem B1670519 : Blo 107783 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B163241 : Blo 107783 163241 := bstep (se 2 (by rfl) ⟨61215, by rfl⟩ : syracuseStep 163241 = 122431) B122431
theorem B622019 : Blo 107783 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B163391 : Blo 107783 163391 := bstep (se 1 (by rfl) ⟨122543, by rfl⟩ : syracuseStep 163391 = 245087) B245087
theorem B163655 : Blo 107783 163655 := bstep (se 1 (by rfl) ⟨122741, by rfl⟩ : syracuseStep 163655 = 245483) B245483
theorem B163739 : Blo 107783 163739 := bstep (se 1 (by rfl) ⟨122804, by rfl⟩ : syracuseStep 163739 = 245609) B245609
theorem B164075 : Blo 107783 164075 := bstep (se 1 (by rfl) ⟨123056, by rfl⟩ : syracuseStep 164075 = 246113) B246113
theorem B164135 : Blo 107783 164135 := bstep (se 1 (by rfl) ⟨123101, by rfl⟩ : syracuseStep 164135 = 246203) B246203
theorem B197035 : Blo 107783 197035 := bstep (se 1 (by rfl) ⟨147776, by rfl⟩ : syracuseStep 197035 = 295553) B295553
theorem B164807 : Blo 107783 164807 := bstep (se 1 (by rfl) ⟨123605, by rfl⟩ : syracuseStep 164807 = 247211) B247211
theorem B295933 : Blo 107783 295933 := bstep (se 3 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 295933 = 110975) B110975
theorem B230455 : Blo 107783 230455 := bstep (se 1 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 230455 = 345683) B345683
theorem B164975 : Blo 107783 164975 := bstep (se 1 (by rfl) ⟨123731, by rfl⟩ : syracuseStep 164975 = 247463) B247463
theorem B525599 : Blo 107783 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B165167 : Blo 107783 165167 := bstep (se 1 (by rfl) ⟨123875, by rfl⟩ : syracuseStep 165167 = 247751) B247751
theorem B165371 : Blo 107783 165371 := bstep (se 1 (by rfl) ⟨124028, by rfl⟩ : syracuseStep 165371 = 248057) B248057
theorem B165407 : Blo 107783 165407 := bstep (se 1 (by rfl) ⟨124055, by rfl⟩ : syracuseStep 165407 = 248111) B248111
theorem B165551 : Blo 107783 165551 := bstep (se 1 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 165551 = 248327) B248327
theorem B165671 : Blo 107783 165671 := bstep (se 1 (by rfl) ⟨124253, by rfl⟩ : syracuseStep 165671 = 248507) B248507
theorem B526445 : Blo 107783 526445 := bstep (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) B197417
theorem B3508343 : Blo 107783 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B166223 : Blo 107783 166223 := bstep (se 1 (by rfl) ⟨124667, by rfl⟩ : syracuseStep 166223 = 249335) B249335
theorem B5212511 : Blo 107783 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B166271 : Blo 107783 166271 := bstep (se 1 (by rfl) ⟨124703, by rfl⟩ : syracuseStep 166271 = 249407) B249407
theorem B166313 : Blo 107783 166313 := bstep (se 2 (by rfl) ⟨62367, by rfl⟩ : syracuseStep 166313 = 124735) B124735
theorem B166697 : Blo 107783 166697 := bstep (se 2 (by rfl) ⟨62511, by rfl⟩ : syracuseStep 166697 = 125023) B125023
theorem B527273 : Blo 107783 527273 := bstep (se 2 (by rfl) ⟨197727, by rfl⟩ : syracuseStep 527273 = 395455) B395455
theorem B494531 : Blo 107783 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B166907 : Blo 107783 166907 := bstep (se 1 (by rfl) ⟨125180, by rfl⟩ : syracuseStep 166907 = 250361) B250361
theorem B166967 : Blo 107783 166967 := bstep (se 1 (by rfl) ⟨125225, by rfl⟩ : syracuseStep 166967 = 250451) B250451
theorem B1051811 : Blo 107783 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B167087 : Blo 107783 167087 := bstep (se 1 (by rfl) ⟨125315, by rfl⟩ : syracuseStep 167087 = 250631) B250631
theorem B233455 : Blo 107783 233455 := bstep (se 1 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 233455 = 350183) B350183
theorem B364607 : Blo 107783 364607 := bstep (se 1 (by rfl) ⟨273455, by rfl⟩ : syracuseStep 364607 = 546911) B546911
theorem B626849 : Blo 107783 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B2232791 : Blo 107783 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B365309 : Blo 107783 365309 := bstep (se 3 (by rfl) ⟨68495, by rfl⟩ : syracuseStep 365309 = 136991) B136991
theorem B365471 : Blo 107783 365471 := bstep (se 1 (by rfl) ⟨274103, by rfl⟩ : syracuseStep 365471 = 548207) B548207
theorem B628307 : Blo 107783 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B235145 : Blo 107783 235145 := bstep (se 2 (by rfl) ⟨88179, by rfl⟩ : syracuseStep 235145 = 176359) B176359
theorem B235163 : Blo 107783 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B464723 : Blo 107783 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B4462937 : Blo 107783 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B1907063 : Blo 107783 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B203239 : Blo 107783 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B236009 : Blo 107783 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B924281 : Blo 107783 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B466651 : Blo 107783 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B1056503 : Blo 107783 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B368765 : Blo 107783 368765 := bstep (se 3 (by rfl) ⟨69143, by rfl⟩ : syracuseStep 368765 = 138287) B138287
theorem B369035 : Blo 107783 369035 := bstep (se 1 (by rfl) ⟨276776, by rfl⟩ : syracuseStep 369035 = 553553) B553553
theorem B631223 : Blo 107783 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B565955 : Blo 107783 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B3089335 : Blo 107783 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B205897 : Blo 107783 205897 := bstep (se 2 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 205897 = 154423) B154423
theorem B107823 : Blo 107783 107823 := bstep (se 1 (by rfl) ⟨80867, by rfl⟩ : syracuseStep 107823 = 161735) B161735
theorem B501245 : Blo 107783 501245 := bstep (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) B187967
theorem B108059 : Blo 107783 108059 := bstep (se 1 (by rfl) ⟨81044, by rfl⟩ : syracuseStep 108059 = 162089) B162089
theorem B108063 : Blo 107783 108063 := bstep (se 1 (by rfl) ⟨81047, by rfl⟩ : syracuseStep 108063 = 162095) B162095
theorem B108223 : Blo 107783 108223 := bstep (se 1 (by rfl) ⟨81167, by rfl⟩ : syracuseStep 108223 = 162335) B162335
theorem B108479 : Blo 107783 108479 := bstep (se 1 (by rfl) ⟨81359, by rfl⟩ : syracuseStep 108479 = 162719) B162719
theorem B108511 : Blo 107783 108511 := bstep (se 1 (by rfl) ⟨81383, by rfl⟩ : syracuseStep 108511 = 162767) B162767
theorem B370655 : Blo 107783 370655 := bstep (se 1 (by rfl) ⟨277991, by rfl⟩ : syracuseStep 370655 = 555983) B555983
theorem B108571 : Blo 107783 108571 := bstep (se 1 (by rfl) ⟨81428, by rfl⟩ : syracuseStep 108571 = 162857) B162857
theorem B108575 : Blo 107783 108575 := bstep (se 1 (by rfl) ⟨81431, by rfl⟩ : syracuseStep 108575 = 162863) B162863
theorem B108591 : Blo 107783 108591 := bstep (se 1 (by rfl) ⟨81443, by rfl⟩ : syracuseStep 108591 = 162887) B162887
theorem B239663 : Blo 107783 239663 := bstep (se 1 (by rfl) ⟨179747, by rfl⟩ : syracuseStep 239663 = 359495) B359495
theorem B469097 : Blo 107783 469097 := bstep (se 2 (by rfl) ⟨175911, by rfl⟩ : syracuseStep 469097 = 351823) B351823
theorem B108767 : Blo 107783 108767 := bstep (se 1 (by rfl) ⟨81575, by rfl⟩ : syracuseStep 108767 = 163151) B163151
theorem B108827 : Blo 107783 108827 := bstep (se 1 (by rfl) ⟨81620, by rfl⟩ : syracuseStep 108827 = 163241) B163241
theorem B108927 : Blo 107783 108927 := bstep (se 1 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 108927 = 163391) B163391
theorem B109103 : Blo 107783 109103 := bstep (se 1 (by rfl) ⟨81827, by rfl⟩ : syracuseStep 109103 = 163655) B163655
theorem B5450321 : Blo 107783 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B109159 : Blo 107783 109159 := bstep (se 1 (by rfl) ⟨81869, by rfl⟩ : syracuseStep 109159 = 163739) B163739
theorem B928655 : Blo 107783 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B666575 : Blo 107783 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B109535 : Blo 107783 109535 := bstep (se 1 (by rfl) ⟨82151, by rfl⟩ : syracuseStep 109535 = 164303) B164303
theorem B109563 : Blo 107783 109563 := bstep (se 1 (by rfl) ⟨82172, by rfl⟩ : syracuseStep 109563 = 164345) B164345
theorem B109631 : Blo 107783 109631 := bstep (se 1 (by rfl) ⟨82223, by rfl⟩ : syracuseStep 109631 = 164447) B164447
theorem B273719 : Blo 107783 273719 := bstep (se 1 (by rfl) ⟨205289, by rfl⟩ : syracuseStep 273719 = 410579) B410579
theorem B208183 : Blo 107783 208183 := bstep (se 1 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 208183 = 312275) B312275
theorem B109951 : Blo 107783 109951 := bstep (se 1 (by rfl) ⟨82463, by rfl⟩ : syracuseStep 109951 = 164927) B164927
theorem B109979 : Blo 107783 109979 := bstep (se 1 (by rfl) ⟨82484, by rfl⟩ : syracuseStep 109979 = 164969) B164969
theorem B110047 : Blo 107783 110047 := bstep (se 1 (by rfl) ⟨82535, by rfl⟩ : syracuseStep 110047 = 165071) B165071
theorem B110183 : Blo 107783 110183 := bstep (se 1 (by rfl) ⟨82637, by rfl⟩ : syracuseStep 110183 = 165275) B165275
theorem B274063 : Blo 107783 274063 := bstep (se 1 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 274063 = 411095) B411095
theorem B110331 : Blo 107783 110331 := bstep (se 1 (by rfl) ⟨82748, by rfl⟩ : syracuseStep 110331 = 165497) B165497
theorem B110399 : Blo 107783 110399 := bstep (se 1 (by rfl) ⟨82799, by rfl⟩ : syracuseStep 110399 = 165599) B165599
theorem B700285 : Blo 107783 700285 := bstep (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) B262607
theorem B110463 : Blo 107783 110463 := bstep (se 1 (by rfl) ⟨82847, by rfl⟩ : syracuseStep 110463 = 165695) B165695
theorem B307115 : Blo 107783 307115 := bstep (se 1 (by rfl) ⟨230336, by rfl⟩ : syracuseStep 307115 = 460673) B460673
theorem B110575 : Blo 107783 110575 := bstep (se 1 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 110575 = 165863) B165863
theorem B208889 : Blo 107783 208889 := bstep (se 2 (by rfl) ⟨78333, by rfl⟩ : syracuseStep 208889 = 156667) B156667
theorem B110587 : Blo 107783 110587 := bstep (se 1 (by rfl) ⟨82940, by rfl⟩ : syracuseStep 110587 = 165881) B165881
theorem B110655 : Blo 107783 110655 := bstep (se 1 (by rfl) ⟨82991, by rfl⟩ : syracuseStep 110655 = 165983) B165983
theorem B110695 : Blo 107783 110695 := bstep (se 1 (by rfl) ⟨83021, by rfl⟩ : syracuseStep 110695 = 166043) B166043
theorem B110719 : Blo 107783 110719 := bstep (se 1 (by rfl) ⟨83039, by rfl⟩ : syracuseStep 110719 = 166079) B166079
theorem B110747 : Blo 107783 110747 := bstep (se 1 (by rfl) ⟨83060, by rfl⟩ : syracuseStep 110747 = 166121) B166121
theorem B536807 : Blo 107783 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B110951 : Blo 107783 110951 := bstep (se 1 (by rfl) ⟨83213, by rfl⟩ : syracuseStep 110951 = 166427) B166427
theorem B111003 : Blo 107783 111003 := bstep (se 1 (by rfl) ⟨83252, by rfl⟩ : syracuseStep 111003 = 166505) B166505
theorem B307775 : Blo 107783 307775 := bstep (se 1 (by rfl) ⟨230831, by rfl⟩ : syracuseStep 307775 = 461663) B461663
theorem B373355 : Blo 107783 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B111355 : Blo 107783 111355 := bstep (se 1 (by rfl) ⟨83516, by rfl⟩ : syracuseStep 111355 = 167033) B167033
theorem B111423 : Blo 107783 111423 := bstep (se 1 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 111423 = 167135) B167135
theorem B111451 : Blo 107783 111451 := bstep (se 1 (by rfl) ⟨83588, by rfl⟩ : syracuseStep 111451 = 167177) B167177
theorem B111519 : Blo 107783 111519 := bstep (se 1 (by rfl) ⟨83639, by rfl⟩ : syracuseStep 111519 = 167279) B167279
theorem B242639 : Blo 107783 242639 := bstep (se 1 (by rfl) ⟨181979, by rfl⟩ : syracuseStep 242639 = 363959) B363959
theorem B1684435 : Blo 107783 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B504787 : Blo 107783 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B111599 : Blo 107783 111599 := bstep (se 1 (by rfl) ⟨83699, by rfl⟩ : syracuseStep 111599 = 167399) B167399
theorem B242729 : Blo 107783 242729 := bstep (se 2 (by rfl) ⟨91023, by rfl⟩ : syracuseStep 242729 = 182047) B182047
theorem B111687 : Blo 107783 111687 := bstep (se 1 (by rfl) ⟨83765, by rfl⟩ : syracuseStep 111687 = 167531) B167531
theorem B111771 : Blo 107783 111771 := bstep (se 1 (by rfl) ⟨83828, by rfl⟩ : syracuseStep 111771 = 167657) B167657
theorem B243017 : Blo 107783 243017 := bstep (se 2 (by rfl) ⟨91131, by rfl⟩ : syracuseStep 243017 = 182263) B182263
theorem B537953 : Blo 107783 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B210347 : Blo 107783 210347 := bstep (se 1 (by rfl) ⟨157760, by rfl⟩ : syracuseStep 210347 = 315521) B315521
theorem B210575 : Blo 107783 210575 := bstep (se 1 (by rfl) ⟨157931, by rfl⟩ : syracuseStep 210575 = 315863) B315863
theorem B211015 : Blo 107783 211015 := bstep (se 1 (by rfl) ⟨158261, by rfl⟩ : syracuseStep 211015 = 316523) B316523
theorem B374975 : Blo 107783 374975 := bstep (se 1 (by rfl) ⟨281231, by rfl⟩ : syracuseStep 374975 = 562463) B562463
theorem B702695 : Blo 107783 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B244007 : Blo 107783 244007 := bstep (se 1 (by rfl) ⟨183005, by rfl⟩ : syracuseStep 244007 = 366011) B366011
theorem B211547 : Blo 107783 211547 := bstep (se 1 (by rfl) ⟨158660, by rfl⟩ : syracuseStep 211547 = 317321) B317321
theorem B244367 : Blo 107783 244367 := bstep (se 1 (by rfl) ⟨183275, by rfl⟩ : syracuseStep 244367 = 366551) B366551
theorem B473759 : Blo 107783 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B244457 : Blo 107783 244457 := bstep (se 2 (by rfl) ⟨91671, by rfl⟩ : syracuseStep 244457 = 183343) B183343
theorem B7650125 : Blo 107783 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B277415 : Blo 107783 277415 := bstep (se 1 (by rfl) ⟨208061, by rfl⟩ : syracuseStep 277415 = 416123) B416123
theorem B244691 : Blo 107783 244691 := bstep (se 1 (by rfl) ⟨183518, by rfl⟩ : syracuseStep 244691 = 367037) B367037
theorem B474169 : Blo 107783 474169 := bstep (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) B355627
theorem B244961 : Blo 107783 244961 := bstep (se 2 (by rfl) ⟨91860, by rfl⟩ : syracuseStep 244961 = 183721) B183721
theorem B245267 : Blo 107783 245267 := bstep (se 1 (by rfl) ⟨183950, by rfl⟩ : syracuseStep 245267 = 367901) B367901
theorem B835433 : Blo 107783 835433 := bstep (se 2 (by rfl) ⟨313287, by rfl⟩ : syracuseStep 835433 = 626575) B626575
theorem B2834351 : Blo 107783 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B245951 : Blo 107783 245951 := bstep (se 1 (by rfl) ⟨184463, by rfl⟩ : syracuseStep 245951 = 368927) B368927
theorem B409819 : Blo 107783 409819 := bstep (se 1 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 409819 = 614729) B614729
theorem B377081 : Blo 107783 377081 := bstep (se 2 (by rfl) ⟨141405, by rfl⟩ : syracuseStep 377081 = 282811) B282811
theorem B246383 : Blo 107783 246383 := bstep (se 1 (by rfl) ⟨184787, by rfl⟩ : syracuseStep 246383 = 369575) B369575
theorem B279227 : Blo 107783 279227 := bstep (se 1 (by rfl) ⟨209420, by rfl⟩ : syracuseStep 279227 = 418841) B418841
theorem B246779 : Blo 107783 246779 := bstep (se 1 (by rfl) ⟨185084, by rfl⟩ : syracuseStep 246779 = 370169) B370169
theorem B705617 : Blo 107783 705617 := bstep (se 2 (by rfl) ⟨264606, by rfl⟩ : syracuseStep 705617 = 529213) B529213
theorem B246959 : Blo 107783 246959 := bstep (se 1 (by rfl) ⟨185219, by rfl⟩ : syracuseStep 246959 = 370439) B370439
theorem B1623233 : Blo 107783 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B246995 : Blo 107783 246995 := bstep (se 1 (by rfl) ⟨185246, by rfl⟩ : syracuseStep 246995 = 370493) B370493
theorem B312673 : Blo 107783 312673 := bstep (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) B234505
theorem B247265 : Blo 107783 247265 := bstep (se 2 (by rfl) ⟨92724, by rfl⟩ : syracuseStep 247265 = 185449) B185449
theorem B509503 : Blo 107783 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B182459 : Blo 107783 182459 := bstep (se 1 (by rfl) ⟨136844, by rfl⟩ : syracuseStep 182459 = 273689) B273689
theorem B248105 : Blo 107783 248105 := bstep (se 2 (by rfl) ⟨93039, by rfl⟩ : syracuseStep 248105 = 186079) B186079
theorem B281191 : Blo 107783 281191 := bstep (se 1 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 281191 = 421787) B421787
theorem B248615 : Blo 107783 248615 := bstep (se 1 (by rfl) ⟨186461, by rfl⟩ : syracuseStep 248615 = 372923) B372923
theorem B183161 : Blo 107783 183161 := bstep (se 2 (by rfl) ⟨68685, by rfl⟩ : syracuseStep 183161 = 137371) B137371
theorem B281465 : Blo 107783 281465 := bstep (se 2 (by rfl) ⟨105549, by rfl⟩ : syracuseStep 281465 = 211099) B211099
theorem B248939 : Blo 107783 248939 := bstep (se 1 (by rfl) ⟨186704, by rfl⟩ : syracuseStep 248939 = 373409) B373409
theorem B249209 : Blo 107783 249209 := bstep (se 2 (by rfl) ⟨93453, by rfl⟩ : syracuseStep 249209 = 186907) B186907
theorem B249515 : Blo 107783 249515 := bstep (se 1 (by rfl) ⟨187136, by rfl⟩ : syracuseStep 249515 = 374273) B374273
theorem B115953443 : Blo 107783 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B413495 : Blo 107783 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B315191 : Blo 107783 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B1036091 : Blo 107783 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B1396673 : Blo 107783 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B184295 : Blo 107783 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B282599 : Blo 107783 282599 := bstep (se 1 (by rfl) ⟨211949, by rfl⟩ : syracuseStep 282599 = 423899) B423899
theorem B249839 : Blo 107783 249839 := bstep (se 1 (by rfl) ⟨187379, by rfl⟩ : syracuseStep 249839 = 374759) B374759
theorem B184315 : Blo 107783 184315 := bstep (se 1 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 184315 = 276473) B276473
theorem B249911 : Blo 107783 249911 := bstep (se 1 (by rfl) ⟨187433, by rfl⟩ : syracuseStep 249911 = 374867) B374867
theorem B184423 : Blo 107783 184423 := bstep (se 1 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 184423 = 276635) B276635
theorem B118939 : Blo 107783 118939 := bstep (se 1 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 118939 = 178409) B178409
theorem B250055 : Blo 107783 250055 := bstep (se 1 (by rfl) ⟨187541, by rfl⟩ : syracuseStep 250055 = 375083) B375083
theorem B3920075 : Blo 107783 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B413981 : Blo 107783 413981 := bstep (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) B155243
theorem B250235 : Blo 107783 250235 := bstep (se 1 (by rfl) ⟨187676, by rfl⟩ : syracuseStep 250235 = 375353) B375353
theorem B479675 : Blo 107783 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B938465 : Blo 107783 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B250505 : Blo 107783 250505 := bstep (se 2 (by rfl) ⟨93939, by rfl⟩ : syracuseStep 250505 = 187879) B187879
theorem B185179 : Blo 107783 185179 := bstep (se 1 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 185179 = 277769) B277769
theorem B414679 : Blo 107783 414679 := bstep (se 1 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 414679 = 622019) B622019
theorem B251243 : Blo 107783 251243 := bstep (se 1 (by rfl) ⟨188432, by rfl⟩ : syracuseStep 251243 = 376865) B376865
theorem B251513 : Blo 107783 251513 := bstep (se 2 (by rfl) ⟨94317, by rfl⟩ : syracuseStep 251513 = 188635) B188635
theorem B546749 : Blo 107783 546749 := bstep (se 3 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 546749 = 205031) B205031
theorem B1071265 : Blo 107783 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B317753 : Blo 107783 317753 := bstep (se 2 (by rfl) ⟨119157, by rfl⟩ : syracuseStep 317753 = 238315) B238315
theorem B3561803 : Blo 107783 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1071863 : Blo 107783 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B121711 : Blo 107783 121711 := bstep (se 1 (by rfl) ⟨91283, by rfl⟩ : syracuseStep 121711 = 182567) B182567
theorem B416623 : Blo 107783 416623 := bstep (se 1 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 416623 = 624935) B624935
theorem B1596631 : Blo 107783 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B1858949 : Blo 107783 1858949 := bstep (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) B348553
theorem B843385 : Blo 107783 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B941777 : Blo 107783 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B122791 : Blo 107783 122791 := bstep (se 1 (by rfl) ⟨92093, by rfl⟩ : syracuseStep 122791 = 184187) B184187
theorem B1269917 : Blo 107783 1269917 := bstep (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) B476219
theorem B450841 : Blo 107783 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B319955 : Blo 107783 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B3007003 : Blo 107783 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B124015 : Blo 107783 124015 := bstep (se 1 (by rfl) ⟨93011, by rfl⟩ : syracuseStep 124015 = 186023) B186023
theorem B13297097 : Blo 107783 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B353819 : Blo 107783 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B124447 : Blo 107783 124447 := bstep (se 1 (by rfl) ⟨93335, by rfl⟩ : syracuseStep 124447 = 186671) B186671
theorem B321259 : Blo 107783 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B714739 : Blo 107783 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B944237 : Blo 107783 944237 := bstep (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) B354089
theorem B551123 : Blo 107783 551123 := bstep (se 1 (by rfl) ⟨413342, by rfl⟩ : syracuseStep 551123 = 826685) B826685
theorem B125311 : Blo 107783 125311 := bstep (se 1 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 125311 = 187967) B187967
theorem B5270123 : Blo 107783 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B1174985 : Blo 107783 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B552743 : Blo 107783 552743 := bstep (se 1 (by rfl) ⟨414557, by rfl⟩ : syracuseStep 552743 = 829115) B829115
theorem B6025427 : Blo 107783 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B880951 : Blo 107783 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B881111 : Blo 107783 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B1864225 : Blo 107783 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B848555 : Blo 107783 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B7074809 : Blo 107783 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B2717873 : Blo 107783 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B161975 : Blo 107783 161975 := bstep (se 1 (by rfl) ⟨121481, by rfl⟩ : syracuseStep 161975 = 242963) B242963
theorem B162023 : Blo 107783 162023 := bstep (se 1 (by rfl) ⟨121517, by rfl⟩ : syracuseStep 162023 = 243035) B243035
theorem B424399 : Blo 107783 424399 := bstep (se 1 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 424399 = 636599) B636599
theorem B162395 : Blo 107783 162395 := bstep (se 1 (by rfl) ⟨121796, by rfl⟩ : syracuseStep 162395 = 243593) B243593
theorem B1342097 : Blo 107783 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B162539 : Blo 107783 162539 := bstep (se 1 (by rfl) ⟨121904, by rfl⟩ : syracuseStep 162539 = 243809) B243809
theorem B162569 : Blo 107783 162569 := bstep (se 2 (by rfl) ⟨60963, by rfl⟩ : syracuseStep 162569 = 121927) B121927
theorem B228577 : Blo 107783 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B1113679 : Blo 107783 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B163439 : Blo 107783 163439 := bstep (se 1 (by rfl) ⟨122579, by rfl⟩ : syracuseStep 163439 = 245159) B245159
theorem B163559 : Blo 107783 163559 := bstep (se 1 (by rfl) ⟨122669, by rfl⟩ : syracuseStep 163559 = 245339) B245339
theorem B163751 : Blo 107783 163751 := bstep (se 1 (by rfl) ⟨122813, by rfl⟩ : syracuseStep 163751 = 245627) B245627
theorem B163967 : Blo 107783 163967 := bstep (se 1 (by rfl) ⟨122975, by rfl⟩ : syracuseStep 163967 = 245951) B245951
theorem B164255 : Blo 107783 164255 := bstep (se 1 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 164255 = 246383) B246383
theorem B164519 : Blo 107783 164519 := bstep (se 1 (by rfl) ⟨123389, by rfl⟩ : syracuseStep 164519 = 246779) B246779
theorem B164639 : Blo 107783 164639 := bstep (se 1 (by rfl) ⟨123479, by rfl⟩ : syracuseStep 164639 = 246959) B246959
theorem B1082155 : Blo 107783 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B164663 : Blo 107783 164663 := bstep (se 1 (by rfl) ⟨123497, by rfl⟩ : syracuseStep 164663 = 246995) B246995
theorem B164843 : Blo 107783 164843 := bstep (se 1 (by rfl) ⟨123632, by rfl⟩ : syracuseStep 164843 = 247265) B247265
theorem B853213 : Blo 107783 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B394577 : Blo 107783 394577 := bstep (se 2 (by rfl) ⟨147966, by rfl⟩ : syracuseStep 394577 = 295933) B295933
theorem B165353 : Blo 107783 165353 := bstep (se 2 (by rfl) ⟨62007, by rfl⟩ : syracuseStep 165353 = 124015) B124015
theorem B165403 : Blo 107783 165403 := bstep (se 1 (by rfl) ⟨124052, by rfl⟩ : syracuseStep 165403 = 248105) B248105
theorem B3475007 : Blo 107783 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B165743 : Blo 107783 165743 := bstep (se 1 (by rfl) ⟨124307, by rfl⟩ : syracuseStep 165743 = 248615) B248615
theorem B329687 : Blo 107783 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B165929 : Blo 107783 165929 := bstep (se 2 (by rfl) ⟨62223, by rfl⟩ : syracuseStep 165929 = 124447) B124447
theorem B165959 : Blo 107783 165959 := bstep (se 1 (by rfl) ⟨124469, by rfl⟩ : syracuseStep 165959 = 248939) B248939
theorem B1050853 : Blo 107783 1050853 := bstep (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) B197035
theorem B166139 : Blo 107783 166139 := bstep (se 1 (by rfl) ⟨124604, by rfl⟩ : syracuseStep 166139 = 249209) B249209
theorem B428345 : Blo 107783 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B166343 : Blo 107783 166343 := bstep (se 1 (by rfl) ⟨124757, by rfl⟩ : syracuseStep 166343 = 249515) B249515
theorem B77302295 : Blo 107783 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B1083941 : Blo 107783 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B690727 : Blo 107783 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B952985 : Blo 107783 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B166559 : Blo 107783 166559 := bstep (se 1 (by rfl) ⟨124919, by rfl⟩ : syracuseStep 166559 = 249839) B249839
theorem B166607 : Blo 107783 166607 := bstep (se 1 (by rfl) ⟨124955, by rfl⟩ : syracuseStep 166607 = 249911) B249911
theorem B166703 : Blo 107783 166703 := bstep (se 1 (by rfl) ⟨125027, by rfl⟩ : syracuseStep 166703 = 250055) B250055
theorem B166823 : Blo 107783 166823 := bstep (se 1 (by rfl) ⟨125117, by rfl⟩ : syracuseStep 166823 = 250235) B250235
theorem B625643 : Blo 107783 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B167003 : Blo 107783 167003 := bstep (se 1 (by rfl) ⟨125252, by rfl⟩ : syracuseStep 167003 = 250505) B250505
theorem B167081 : Blo 107783 167081 := bstep (se 2 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 167081 = 125311) B125311
theorem B167495 : Blo 107783 167495 := bstep (se 1 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 167495 = 251243) B251243
theorem B5738165 : Blo 107783 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B167675 : Blo 107783 167675 := bstep (se 1 (by rfl) ⟨125756, by rfl⟩ : syracuseStep 167675 = 251513) B251513
theorem B364499 : Blo 107783 364499 := bstep (se 1 (by rfl) ⟨273374, by rfl⟩ : syracuseStep 364499 = 546749) B546749
theorem B627101 : Blo 107783 627101 := bstep (se 3 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 627101 = 235163) B235163
theorem B365417 : Blo 107783 365417 := bstep (se 2 (by rfl) ⟨137031, by rfl⟩ : syracuseStep 365417 = 274063) B274063
theorem B627851 : Blo 107783 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B334163 : Blo 107783 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B235879 : Blo 107783 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B629491 : Blo 107783 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B367415 : Blo 107783 367415 := bstep (se 1 (by rfl) ⟨275561, by rfl⟩ : syracuseStep 367415 = 551123) B551123
theorem B3513415 : Blo 107783 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B368495 : Blo 107783 368495 := bstep (se 1 (by rfl) ⟨276371, by rfl⟩ : syracuseStep 368495 = 552743) B552743
theorem B204743 : Blo 107783 204743 := bstep (se 1 (by rfl) ⟨153557, by rfl⟩ : syracuseStep 204743 = 307115) B307115
theorem B139259 : Blo 107783 139259 := bstep (se 1 (by rfl) ⟨104444, by rfl⟩ : syracuseStep 139259 = 208889) B208889
theorem B205183 : Blo 107783 205183 := bstep (se 1 (by rfl) ⟨153887, by rfl⟩ : syracuseStep 205183 = 307775) B307775
theorem B565703 : Blo 107783 565703 := bstep (se 1 (by rfl) ⟨424277, by rfl⟩ : syracuseStep 565703 = 848555) B848555
theorem B565865 : Blo 107783 565865 := bstep (se 2 (by rfl) ⟨212199, by rfl⟩ : syracuseStep 565865 = 424399) B424399
theorem B140231 : Blo 107783 140231 := bstep (se 1 (by rfl) ⟨105173, by rfl⟩ : syracuseStep 140231 = 210347) B210347
theorem B140383 : Blo 107783 140383 := bstep (se 1 (by rfl) ⟨105287, by rfl⟩ : syracuseStep 140383 = 210575) B210575
theorem B632225 : Blo 107783 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B1811915 : Blo 107783 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B107983 : Blo 107783 107983 := bstep (se 1 (by rfl) ⟨80987, by rfl⟩ : syracuseStep 107983 = 161975) B161975
theorem B108015 : Blo 107783 108015 := bstep (se 1 (by rfl) ⟨81011, by rfl⟩ : syracuseStep 108015 = 162023) B162023
theorem B468463 : Blo 107783 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B304769 : Blo 107783 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B108263 : Blo 107783 108263 := bstep (se 1 (by rfl) ⟨81197, by rfl⟩ : syracuseStep 108263 = 162395) B162395
theorem B141031 : Blo 107783 141031 := bstep (se 1 (by rfl) ⟨105773, by rfl⟩ : syracuseStep 141031 = 211547) B211547
theorem B894731 : Blo 107783 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B108359 : Blo 107783 108359 := bstep (se 1 (by rfl) ⟨81269, by rfl⟩ : syracuseStep 108359 = 162539) B162539
theorem B108379 : Blo 107783 108379 := bstep (se 1 (by rfl) ⟨81284, by rfl⟩ : syracuseStep 108379 = 162569) B162569
theorem B1484905 : Blo 107783 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1124513 : Blo 107783 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B108959 : Blo 107783 108959 := bstep (se 1 (by rfl) ⟨81719, by rfl⟩ : syracuseStep 108959 = 163439) B163439
theorem B109039 : Blo 107783 109039 := bstep (se 1 (by rfl) ⟨81779, by rfl⟩ : syracuseStep 109039 = 163559) B163559
theorem B109167 : Blo 107783 109167 := bstep (se 1 (by rfl) ⟨81875, by rfl⟩ : syracuseStep 109167 = 163751) B163751
theorem B109383 : Blo 107783 109383 := bstep (se 1 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 109383 = 164075) B164075
theorem B109423 : Blo 107783 109423 := bstep (se 1 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 109423 = 164135) B164135
theorem B601121 : Blo 107783 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B109871 : Blo 107783 109871 := bstep (se 1 (by rfl) ⟨82403, by rfl⟩ : syracuseStep 109871 = 164807) B164807
theorem B4009337 : Blo 107783 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B470411 : Blo 107783 470411 := bstep (se 1 (by rfl) ⟨352808, by rfl⟩ : syracuseStep 470411 = 705617) B705617
theorem B109983 : Blo 107783 109983 := bstep (se 1 (by rfl) ⟨82487, by rfl⟩ : syracuseStep 109983 = 164975) B164975
theorem B110111 : Blo 107783 110111 := bstep (se 1 (by rfl) ⟨82583, by rfl⟩ : syracuseStep 110111 = 165167) B165167
theorem B110247 : Blo 107783 110247 := bstep (se 1 (by rfl) ⟨82685, by rfl⟩ : syracuseStep 110247 = 165371) B165371
theorem B110271 : Blo 107783 110271 := bstep (se 1 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 110271 = 165407) B165407
theorem B110367 : Blo 107783 110367 := bstep (se 1 (by rfl) ⟨82775, by rfl⟩ : syracuseStep 110367 = 165551) B165551
theorem B110447 : Blo 107783 110447 := bstep (se 1 (by rfl) ⟨82835, by rfl⟩ : syracuseStep 110447 = 165671) B165671
theorem B2338895 : Blo 107783 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B274529 : Blo 107783 274529 := bstep (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) B205897
theorem B110815 : Blo 107783 110815 := bstep (se 1 (by rfl) ⟨83111, by rfl⟩ : syracuseStep 110815 = 166223) B166223
theorem B110847 : Blo 107783 110847 := bstep (se 1 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 110847 = 166271) B166271
theorem B110875 : Blo 107783 110875 := bstep (se 1 (by rfl) ⟨83156, by rfl⟩ : syracuseStep 110875 = 166313) B166313
theorem B111131 : Blo 107783 111131 := bstep (se 1 (by rfl) ⟨83348, by rfl⟩ : syracuseStep 111131 = 166697) B166697
theorem B111271 : Blo 107783 111271 := bstep (se 1 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 111271 = 166907) B166907
theorem B111311 : Blo 107783 111311 := bstep (se 1 (by rfl) ⟨83483, by rfl⟩ : syracuseStep 111311 = 166967) B166967
theorem B701207 : Blo 107783 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B111391 : Blo 107783 111391 := bstep (se 1 (by rfl) ⟨83543, by rfl⟩ : syracuseStep 111391 = 167087) B167087
theorem B275663 : Blo 107783 275663 := bstep (se 1 (by rfl) ⟨206747, by rfl⟩ : syracuseStep 275663 = 413495) B413495
theorem B210127 : Blo 107783 210127 := bstep (se 1 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 210127 = 315191) B315191
theorem B931115 : Blo 107783 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B243071 : Blo 107783 243071 := bstep (se 1 (by rfl) ⟨182303, by rfl⟩ : syracuseStep 243071 = 364607) B364607
theorem B275987 : Blo 107783 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B1488527 : Blo 107783 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B243539 : Blo 107783 243539 := bstep (se 1 (by rfl) ⟨182654, by rfl⟩ : syracuseStep 243539 = 365309) B365309
theorem B2537365 : Blo 107783 2537365 := bstep (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) B118939
theorem B243647 : Blo 107783 243647 := bstep (se 1 (by rfl) ⟨182735, by rfl⟩ : syracuseStep 243647 = 365471) B365471
theorem B374921 : Blo 107783 374921 := bstep (se 2 (by rfl) ⟨140595, by rfl⟩ : syracuseStep 374921 = 281191) B281191
theorem B309815 : Blo 107783 309815 := bstep (se 1 (by rfl) ⟨232361, by rfl⟩ : syracuseStep 309815 = 464723) B464723
theorem B211835 : Blo 107783 211835 := bstep (se 1 (by rfl) ⟨158876, by rfl⟩ : syracuseStep 211835 = 317753) B317753
theorem B2374535 : Blo 107783 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B277577 : Blo 107783 277577 := bstep (se 2 (by rfl) ⟨104091, by rfl⟩ : syracuseStep 277577 = 208183) B208183
theorem B704335 : Blo 107783 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B933713 : Blo 107783 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B311273 : Blo 107783 311273 := bstep (se 2 (by rfl) ⟨116727, by rfl⟩ : syracuseStep 311273 = 233455) B233455
theorem B245753 : Blo 107783 245753 := bstep (se 2 (by rfl) ⟨92157, by rfl⟩ : syracuseStep 245753 = 184315) B184315
theorem B245843 : Blo 107783 245843 := bstep (se 1 (by rfl) ⟨184382, by rfl⟩ : syracuseStep 245843 = 368765) B368765
theorem B245897 : Blo 107783 245897 := bstep (se 2 (by rfl) ⟨92211, by rfl⟩ : syracuseStep 245897 = 184423) B184423
theorem B246023 : Blo 107783 246023 := bstep (se 1 (by rfl) ⟨184517, by rfl⟩ : syracuseStep 246023 = 369035) B369035
theorem B1229093 : Blo 107783 1229093 := bstep (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) B230455
theorem B377303 : Blo 107783 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B8864731 : Blo 107783 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B246905 : Blo 107783 246905 := bstep (se 2 (by rfl) ⟨92589, by rfl⟩ : syracuseStep 246905 = 185179) B185179
theorem B2245913 : Blo 107783 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B673049 : Blo 107783 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B247103 : Blo 107783 247103 := bstep (se 1 (by rfl) ⟨185327, by rfl⟩ : syracuseStep 247103 = 370655) B370655
theorem B312731 : Blo 107783 312731 := bstep (se 1 (by rfl) ⟨234548, by rfl⟩ : syracuseStep 312731 = 469097) B469097
theorem B444383 : Blo 107783 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B182479 : Blo 107783 182479 := bstep (se 1 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 182479 = 273719) B273719
theorem B281353 : Blo 107783 281353 := bstep (se 2 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 281353 = 211015) B211015
theorem B4016951 : Blo 107783 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B1428353 : Blo 107783 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B248903 : Blo 107783 248903 := bstep (se 1 (by rfl) ⟨186677, by rfl⟩ : syracuseStep 248903 = 373355) B373355
theorem B249983 : Blo 107783 249983 := bstep (se 1 (by rfl) ⟨187487, by rfl⟩ : syracuseStep 249983 = 374975) B374975
theorem B315839 : Blo 107783 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B5100083 : Blo 107783 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B184943 : Blo 107783 184943 := bstep (se 1 (by rfl) ⟨138707, by rfl⟩ : syracuseStep 184943 = 277415) B277415
theorem B1889567 : Blo 107783 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B251387 : Blo 107783 251387 := bstep (se 1 (by rfl) ⟨188540, by rfl⟩ : syracuseStep 251387 = 377081) B377081
theorem B546425 : Blo 107783 546425 := bstep (se 2 (by rfl) ⟨204909, by rfl⟩ : syracuseStep 546425 = 409819) B409819
theorem B186151 : Blo 107783 186151 := bstep (se 1 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 186151 = 279227) B279227
theorem B350399 : Blo 107783 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B4119113 : Blo 107783 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B350963 : Blo 107783 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B121639 : Blo 107783 121639 := bstep (se 1 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 121639 = 182459) B182459
theorem B416897 : Blo 107783 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B122107 : Blo 107783 122107 := bstep (se 1 (by rfl) ⟨91580, by rfl⟩ : syracuseStep 122107 = 183161) B183161
theorem B187643 : Blo 107783 187643 := bstep (se 1 (by rfl) ⟨140732, by rfl⟩ : syracuseStep 187643 = 281465) B281465
theorem B351515 : Blo 107783 351515 := bstep (se 1 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 351515 = 527273) B527273
theorem B679337 : Blo 107783 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B122863 : Blo 107783 122863 := bstep (se 1 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 122863 = 184295) B184295
theorem B188399 : Blo 107783 188399 := bstep (se 1 (by rfl) ⟨141299, by rfl⟩ : syracuseStep 188399 = 282599) B282599
theorem B417899 : Blo 107783 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B2613383 : Blo 107783 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B319783 : Blo 107783 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B418871 : Blo 107783 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B156763 : Blo 107783 156763 := bstep (se 1 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 156763 = 235145) B235145
theorem B2975291 : Blo 107783 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1271375 : Blo 107783 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B157339 : Blo 107783 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B616187 : Blo 107783 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B714575 : Blo 107783 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B1239299 : Blo 107783 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B846611 : Blo 107783 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B420815 : Blo 107783 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B1174601 : Blo 107783 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B2485633 : Blo 107783 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B552905 : Blo 107783 552905 := bstep (se 2 (by rfl) ⟨207339, by rfl⟩ : syracuseStep 552905 = 414679) B414679
theorem B159775 : Blo 107783 159775 := bstep (se 1 (by rfl) ⟨119831, by rfl⟩ : syracuseStep 159775 = 239663) B239663
theorem B3633547 : Blo 107783 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B619103 : Blo 107783 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B783323 : Blo 107783 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B357871 : Blo 107783 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B587407 : Blo 107783 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B161759 : Blo 107783 161759 := bstep (se 1 (by rfl) ⟨121319, by rfl⟩ : syracuseStep 161759 = 242639) B242639
theorem B4716539 : Blo 107783 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B161819 : Blo 107783 161819 := bstep (se 1 (by rfl) ⟨121364, by rfl⟩ : syracuseStep 161819 = 242729) B242729
theorem B162011 : Blo 107783 162011 := bstep (se 1 (by rfl) ⟨121508, by rfl⟩ : syracuseStep 162011 = 243017) B243017
theorem B162281 : Blo 107783 162281 := bstep (se 2 (by rfl) ⟨60855, by rfl⟩ : syracuseStep 162281 = 121711) B121711
theorem B555497 : Blo 107783 555497 := bstep (se 2 (by rfl) ⟨208311, by rfl⟩ : syracuseStep 555497 = 416623) B416623
theorem B162671 : Blo 107783 162671 := bstep (se 1 (by rfl) ⟨122003, by rfl⟩ : syracuseStep 162671 = 244007) B244007
theorem B2128841 : Blo 107783 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B162911 : Blo 107783 162911 := bstep (se 1 (by rfl) ⟨122183, by rfl⟩ : syracuseStep 162911 = 244367) B244367
theorem B162971 : Blo 107783 162971 := bstep (se 1 (by rfl) ⟨122228, by rfl⟩ : syracuseStep 162971 = 244457) B244457
theorem B163127 : Blo 107783 163127 := bstep (se 1 (by rfl) ⟨122345, by rfl⟩ : syracuseStep 163127 = 244691) B244691
theorem B163307 : Blo 107783 163307 := bstep (se 1 (by rfl) ⟨122480, by rfl⟩ : syracuseStep 163307 = 244961) B244961
theorem B622201 : Blo 107783 622201 := bstep (se 2 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 622201 = 466651) B466651
theorem B163511 : Blo 107783 163511 := bstep (se 1 (by rfl) ⟨122633, by rfl⟩ : syracuseStep 163511 = 245267) B245267
theorem B163721 : Blo 107783 163721 := bstep (se 2 (by rfl) ⟨61395, by rfl⟩ : syracuseStep 163721 = 122791) B122791
theorem B556955 : Blo 107783 556955 := bstep (se 1 (by rfl) ⟨417716, by rfl⟩ : syracuseStep 556955 = 835433) B835433
theorem B163895 : Blo 107783 163895 := bstep (se 1 (by rfl) ⟨122921, by rfl⟩ : syracuseStep 163895 = 245843) B245843
theorem B163931 : Blo 107783 163931 := bstep (se 1 (by rfl) ⟨122948, by rfl⟩ : syracuseStep 163931 = 245897) B245897
theorem B852133 : Blo 107783 852133 := bstep (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) B159775
theorem B164015 : Blo 107783 164015 := bstep (se 1 (by rfl) ⟨123011, by rfl⟩ : syracuseStep 164015 = 246023) B246023
theorem B819395 : Blo 107783 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B426377 : Blo 107783 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B164603 : Blo 107783 164603 := bstep (se 1 (by rfl) ⟨123452, by rfl⟩ : syracuseStep 164603 = 246905) B246905
theorem B164735 : Blo 107783 164735 := bstep (se 1 (by rfl) ⟨123551, by rfl⟩ : syracuseStep 164735 = 247103) B247103
theorem B263051 : Blo 107783 263051 := bstep (se 1 (by rfl) ⟨197288, by rfl⟩ : syracuseStep 263051 = 394577) B394577
theorem B1442873 : Blo 107783 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B296255 : Blo 107783 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B722627 : Blo 107783 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B952235 : Blo 107783 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B624617 : Blo 107783 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B165935 : Blo 107783 165935 := bstep (se 1 (by rfl) ⟨124451, by rfl⟩ : syracuseStep 165935 = 248903) B248903
theorem B166655 : Blo 107783 166655 := bstep (se 1 (by rfl) ⟨124991, by rfl⟩ : syracuseStep 166655 = 249983) B249983
theorem B920969 : Blo 107783 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B167591 : Blo 107783 167591 := bstep (se 1 (by rfl) ⟨125693, by rfl⟩ : syracuseStep 167591 = 251387) B251387
theorem B364283 : Blo 107783 364283 := bstep (se 1 (by rfl) ⟨273212, by rfl⟩ : syracuseStep 364283 = 546425) B546425
theorem B233599 : Blo 107783 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B233975 : Blo 107783 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B3314177 : Blo 107783 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B234343 : Blo 107783 234343 := bstep (se 1 (by rfl) ⟨175757, by rfl⟩ : syracuseStep 234343 = 351515) B351515
theorem B136495 : Blo 107783 136495 := bstep (se 1 (by rfl) ⟨102371, by rfl⟩ : syracuseStep 136495 = 204743) B204743
theorem B1742255 : Blo 107783 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B891101 : Blo 107783 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B826199 : Blo 107783 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B564407 : Blo 107783 564407 := bstep (se 1 (by rfl) ⟨423305, by rfl⟩ : syracuseStep 564407 = 846611) B846611
theorem B564893 : Blo 107783 564893 := bstep (se 3 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 564893 = 211835) B211835
theorem B3383153 : Blo 107783 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B368603 : Blo 107783 368603 := bstep (se 1 (by rfl) ⟨276452, by rfl⟩ : syracuseStep 368603 = 552905) B552905
theorem B467471 : Blo 107783 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B992351 : Blo 107783 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B107839 : Blo 107783 107839 := bstep (se 1 (by rfl) ⟨80879, by rfl⟩ : syracuseStep 107839 = 161759) B161759
theorem B107879 : Blo 107783 107879 := bstep (se 1 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 107879 = 161819) B161819
theorem B108007 : Blo 107783 108007 := bstep (se 1 (by rfl) ⟨81005, by rfl⟩ : syracuseStep 108007 = 162011) B162011
theorem B108187 : Blo 107783 108187 := bstep (se 1 (by rfl) ⟨81140, by rfl⟩ : syracuseStep 108187 = 162281) B162281
theorem B370331 : Blo 107783 370331 := bstep (se 1 (by rfl) ⟨277748, by rfl⟩ : syracuseStep 370331 = 555497) B555497
theorem B206543 : Blo 107783 206543 := bstep (se 1 (by rfl) ⟨154907, by rfl⟩ : syracuseStep 206543 = 309815) B309815
theorem B108447 : Blo 107783 108447 := bstep (se 1 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 108447 = 162671) B162671
theorem B1583023 : Blo 107783 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B1419227 : Blo 107783 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B108607 : Blo 107783 108607 := bstep (se 1 (by rfl) ⟨81455, by rfl⟩ : syracuseStep 108607 = 162911) B162911
theorem B108647 : Blo 107783 108647 := bstep (se 1 (by rfl) ⟨81485, by rfl⟩ : syracuseStep 108647 = 162971) B162971
theorem B829601 : Blo 107783 829601 := bstep (se 2 (by rfl) ⟨311100, by rfl⟩ : syracuseStep 829601 = 622201) B622201
theorem B108751 : Blo 107783 108751 := bstep (se 1 (by rfl) ⟨81563, by rfl⟩ : syracuseStep 108751 = 163127) B163127
theorem B108871 : Blo 107783 108871 := bstep (se 1 (by rfl) ⟨81653, by rfl⟩ : syracuseStep 108871 = 163307) B163307
theorem B109007 : Blo 107783 109007 := bstep (se 1 (by rfl) ⟨81755, by rfl⟩ : syracuseStep 109007 = 163511) B163511
theorem B109147 : Blo 107783 109147 := bstep (se 1 (by rfl) ⟨81860, by rfl⟩ : syracuseStep 109147 = 163721) B163721
theorem B371303 : Blo 107783 371303 := bstep (se 1 (by rfl) ⟨278477, by rfl⟩ : syracuseStep 371303 = 556955) B556955
theorem B207515 : Blo 107783 207515 := bstep (se 1 (by rfl) ⟨155636, by rfl⟩ : syracuseStep 207515 = 311273) B311273
theorem B371357 : Blo 107783 371357 := bstep (se 3 (by rfl) ⟨69629, by rfl⟩ : syracuseStep 371357 = 139259) B139259
theorem B109311 : Blo 107783 109311 := bstep (se 1 (by rfl) ⟨81983, by rfl⟩ : syracuseStep 109311 = 163967) B163967
theorem B109503 : Blo 107783 109503 := bstep (se 1 (by rfl) ⟨82127, by rfl⟩ : syracuseStep 109503 = 164255) B164255
theorem B109679 : Blo 107783 109679 := bstep (se 1 (by rfl) ⟨82259, by rfl⟩ : syracuseStep 109679 = 164519) B164519
theorem B273577 : Blo 107783 273577 := bstep (se 2 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 273577 = 205183) B205183
theorem B109759 : Blo 107783 109759 := bstep (se 1 (by rfl) ⟨82319, by rfl⟩ : syracuseStep 109759 = 164639) B164639
theorem B109775 : Blo 107783 109775 := bstep (se 1 (by rfl) ⟨82331, by rfl⟩ : syracuseStep 109775 = 164663) B164663
theorem B109895 : Blo 107783 109895 := bstep (se 1 (by rfl) ⟨82421, by rfl⟩ : syracuseStep 109895 = 164843) B164843
theorem B208487 : Blo 107783 208487 := bstep (se 1 (by rfl) ⟨156365, by rfl⟩ : syracuseStep 208487 = 312731) B312731
theorem B110235 : Blo 107783 110235 := bstep (se 1 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 110235 = 165353) B165353
theorem B110495 : Blo 107783 110495 := bstep (se 1 (by rfl) ⟨82871, by rfl⟩ : syracuseStep 110495 = 165743) B165743
theorem B110619 : Blo 107783 110619 := bstep (se 1 (by rfl) ⟨82964, by rfl⟩ : syracuseStep 110619 = 165929) B165929
theorem B110639 : Blo 107783 110639 := bstep (se 1 (by rfl) ⟨82979, by rfl⟩ : syracuseStep 110639 = 165959) B165959
theorem B209017 : Blo 107783 209017 := bstep (se 2 (by rfl) ⟨78381, by rfl⟩ : syracuseStep 209017 = 156763) B156763
theorem B110759 : Blo 107783 110759 := bstep (se 1 (by rfl) ⟨83069, by rfl⟩ : syracuseStep 110759 = 166139) B166139
theorem B110895 : Blo 107783 110895 := bstep (se 1 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 110895 = 166343) B166343
theorem B635323 : Blo 107783 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B111039 : Blo 107783 111039 := bstep (se 1 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 111039 = 166559) B166559
theorem B111071 : Blo 107783 111071 := bstep (se 1 (by rfl) ⟨83303, by rfl⟩ : syracuseStep 111071 = 166607) B166607
theorem B111135 : Blo 107783 111135 := bstep (se 1 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 111135 = 166703) B166703
theorem B1258021 : Blo 107783 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B111215 : Blo 107783 111215 := bstep (se 1 (by rfl) ⟨83411, by rfl⟩ : syracuseStep 111215 = 166823) B166823
theorem B111335 : Blo 107783 111335 := bstep (se 1 (by rfl) ⟨83501, by rfl⟩ : syracuseStep 111335 = 167003) B167003
theorem B111387 : Blo 107783 111387 := bstep (se 1 (by rfl) ⟨83540, by rfl⟩ : syracuseStep 111387 = 167081) B167081
theorem B209785 : Blo 107783 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B111663 : Blo 107783 111663 := bstep (se 1 (by rfl) ⟨83747, by rfl⟩ : syracuseStep 111663 = 167495) B167495
theorem B111783 : Blo 107783 111783 := bstep (se 1 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 111783 = 167675) B167675
theorem B373949 : Blo 107783 373949 := bstep (se 3 (by rfl) ⟨70115, by rfl⟩ : syracuseStep 373949 = 140231) B140231
theorem B242999 : Blo 107783 242999 := bstep (se 1 (by rfl) ⟨182249, by rfl⟩ : syracuseStep 242999 = 364499) B364499
theorem B1979873 : Blo 107783 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B243305 : Blo 107783 243305 := bstep (se 2 (by rfl) ⟨91239, by rfl⟩ : syracuseStep 243305 = 182479) B182479
theorem B243611 : Blo 107783 243611 := bstep (se 1 (by rfl) ⟨182708, by rfl⟩ : syracuseStep 243611 = 365417) B365417
theorem B1259711 : Blo 107783 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B375137 : Blo 107783 375137 := bstep (se 2 (by rfl) ⟨140676, by rfl⟩ : syracuseStep 375137 = 281353) B281353
theorem B244943 : Blo 107783 244943 := bstep (se 1 (by rfl) ⟨183707, by rfl⟩ : syracuseStep 244943 = 367415) B367415
theorem B277931 : Blo 107783 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B245663 : Blo 107783 245663 := bstep (se 1 (by rfl) ⟨184247, by rfl⟩ : syracuseStep 245663 = 368495) B368495
theorem B278599 : Blo 107783 278599 := bstep (se 1 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 278599 = 417899) B417899
theorem B377135 : Blo 107783 377135 := bstep (se 1 (by rfl) ⟨282851, by rfl⟩ : syracuseStep 377135 = 565703) B565703
theorem B377243 : Blo 107783 377243 := bstep (se 1 (by rfl) ⟨282932, by rfl⟩ : syracuseStep 377243 = 565865) B565865
theorem B279247 : Blo 107783 279247 := bstep (se 1 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 279247 = 418871) B418871
theorem B1983527 : Blo 107783 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B410791 : Blo 107783 410791 := bstep (se 1 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 410791 = 616187) B616187
theorem B476383 : Blo 107783 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B280169 : Blo 107783 280169 := bstep (se 2 (by rfl) ⟨105063, by rfl⟩ : syracuseStep 280169 = 210127) B210127
theorem B280543 : Blo 107783 280543 := bstep (se 1 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 280543 = 420815) B420815
theorem B477161 : Blo 107783 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B2672891 : Blo 107783 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B313607 : Blo 107783 313607 := bstep (se 1 (by rfl) ⟨235205, by rfl⟩ : syracuseStep 313607 = 470411) B470411
theorem B248201 : Blo 107783 248201 := bstep (se 2 (by rfl) ⟨93075, by rfl⟩ : syracuseStep 248201 = 186151) B186151
theorem B1559263 : Blo 107783 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B183019 : Blo 107783 183019 := bstep (se 1 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 183019 = 274529) B274529
theorem B412735 : Blo 107783 412735 := bstep (se 1 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 412735 = 619103) B619103
theorem B183775 : Blo 107783 183775 := bstep (se 1 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 183775 = 275663) B275663
theorem B839321 : Blo 107783 839321 := bstep (se 2 (by rfl) ⟨314745, by rfl⟩ : syracuseStep 839321 = 629491) B629491
theorem B183991 : Blo 107783 183991 := bstep (se 1 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 183991 = 275987) B275987
theorem B249947 : Blo 107783 249947 := bstep (se 1 (by rfl) ⟨187460, by rfl⟩ : syracuseStep 249947 = 374921) B374921
theorem B185051 : Blo 107783 185051 := bstep (se 1 (by rfl) ⟨138788, by rfl⟩ : syracuseStep 185051 = 277577) B277577
theorem B939113 : Blo 107783 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B1497275 : Blo 107783 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B2316671 : Blo 107783 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B842237 : Blo 107783 842237 := bstep (se 3 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 842237 = 315839) B315839
theorem B1006141 : Blo 107783 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B11819641 : Blo 107783 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B219791 : Blo 107783 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B187177 : Blo 107783 187177 := bstep (se 2 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 187177 = 140383) B140383
theorem B285563 : Blo 107783 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B1137617 : Blo 107783 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B51534863 : Blo 107783 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B2677967 : Blo 107783 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B417095 : Blo 107783 417095 := bstep (se 1 (by rfl) ⟨312821, by rfl⟩ : syracuseStep 417095 = 625643) B625643
theorem B220537 : Blo 107783 220537 := bstep (se 2 (by rfl) ⟨82701, by rfl⟩ : syracuseStep 220537 = 165403) B165403
theorem B188041 : Blo 107783 188041 := bstep (se 2 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 188041 = 141031) B141031
theorem B3825443 : Blo 107783 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B418067 : Blo 107783 418067 := bstep (se 1 (by rfl) ⟨313550, by rfl⟩ : syracuseStep 418067 = 627101) B627101
theorem B1401137 : Blo 107783 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B3400055 : Blo 107783 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B123295 : Blo 107783 123295 := bstep (se 1 (by rfl) ⟨92471, by rfl⟩ : syracuseStep 123295 = 184943) B184943
theorem B1794797 : Blo 107783 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B418567 : Blo 107783 418567 := bstep (se 1 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 418567 = 627851) B627851
theorem B812717 : Blo 107783 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B2746075 : Blo 107783 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B2385949 : Blo 107783 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B125095 : Blo 107783 125095 := bstep (se 1 (by rfl) ⟨93821, by rfl⟩ : syracuseStep 125095 = 187643) B187643
theorem B452891 : Blo 107783 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B125599 : Blo 107783 125599 := bstep (se 1 (by rfl) ⟨94199, by rfl⟩ : syracuseStep 125599 = 188399) B188399
theorem B4844729 : Blo 107783 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B421483 : Blo 107783 421483 := bstep (se 1 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 421483 = 632225) B632225
theorem B1207943 : Blo 107783 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B847583 : Blo 107783 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B749675 : Blo 107783 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B783067 : Blo 107783 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B783209 : Blo 107783 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B1602989 : Blo 107783 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B522215 : Blo 107783 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B620743 : Blo 107783 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B162047 : Blo 107783 162047 := bstep (se 1 (by rfl) ⟨121535, by rfl⟩ : syracuseStep 162047 = 243071) B243071
theorem B162185 : Blo 107783 162185 := bstep (se 2 (by rfl) ⟨60819, by rfl⟩ : syracuseStep 162185 = 121639) B121639
theorem B162359 : Blo 107783 162359 := bstep (se 1 (by rfl) ⟨121769, by rfl⟩ : syracuseStep 162359 = 243539) B243539
theorem B162431 : Blo 107783 162431 := bstep (se 1 (by rfl) ⟨121823, by rfl⟩ : syracuseStep 162431 = 243647) B243647
theorem B3144359 : Blo 107783 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4684553 : Blo 107783 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B162809 : Blo 107783 162809 := bstep (se 2 (by rfl) ⟨61053, by rfl⟩ : syracuseStep 162809 = 122107) B122107
theorem B622475 : Blo 107783 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B163817 : Blo 107783 163817 := bstep (se 2 (by rfl) ⟨61431, by rfl⟩ : syracuseStep 163817 = 122863) B122863
theorem B163835 : Blo 107783 163835 := bstep (se 1 (by rfl) ⟨122876, by rfl⟩ : syracuseStep 163835 = 245753) B245753
theorem B1999133 : Blo 107783 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B164393 : Blo 107783 164393 := bstep (se 2 (by rfl) ⟨61647, by rfl⟩ : syracuseStep 164393 = 123295) B123295
theorem B558089 : Blo 107783 558089 := bstep (se 2 (by rfl) ⟨209283, by rfl⟩ : syracuseStep 558089 = 418567) B418567
theorem B623933 : Blo 107783 623933 := bstep (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) B233975
theorem B1246589 : Blo 107783 1246589 := bstep (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) B467471
theorem B165467 : Blo 107783 165467 := bstep (se 1 (by rfl) ⟨124100, by rfl⟩ : syracuseStep 165467 = 248201) B248201
theorem B559547 : Blo 107783 559547 := bstep (se 1 (by rfl) ⟨419660, by rfl⟩ : syracuseStep 559547 = 839321) B839321
theorem B3181265 : Blo 107783 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B166631 : Blo 107783 166631 := bstep (se 1 (by rfl) ⟨124973, by rfl⟩ : syracuseStep 166631 = 249947) B249947
theorem B166793 : Blo 107783 166793 := bstep (se 2 (by rfl) ⟨62547, by rfl⟩ : syracuseStep 166793 = 125095) B125095
theorem B626075 : Blo 107783 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B790013 : Blo 107783 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B167465 : Blo 107783 167465 := bstep (se 2 (by rfl) ⟨62799, by rfl⟩ : syracuseStep 167465 = 125599) B125599
theorem B594067 : Blo 107783 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B364769 : Blo 107783 364769 := bstep (se 2 (by rfl) ⟨136788, by rfl⟩ : syracuseStep 364769 = 273577) B273577
theorem B1544447 : Blo 107783 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B561491 : Blo 107783 561491 := bstep (se 1 (by rfl) ⟨421118, by rfl⟩ : syracuseStep 561491 = 842237) B842237
theorem B758411 : Blo 107783 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B561977 : Blo 107783 561977 := bstep (se 2 (by rfl) ⟨210741, by rfl⟩ : syracuseStep 561977 = 421483) B421483
theorem B2266703 : Blo 107783 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B1677361 : Blo 107783 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B661567 : Blo 107783 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B137695 : Blo 107783 137695 := bstep (se 1 (by rfl) ⟨103271, by rfl⟩ : syracuseStep 137695 = 206543) B206543
theorem B301927 : Blo 107783 301927 := bstep (se 1 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 301927 = 452891) B452891
theorem B138343 : Blo 107783 138343 := bstep (se 1 (by rfl) ⟨103757, by rfl⟩ : syracuseStep 138343 = 207515) B207515
theorem B761501 : Blo 107783 761501 := bstep (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) B285563
theorem B138991 : Blo 107783 138991 := bstep (se 1 (by rfl) ⟨104243, by rfl⟩ : syracuseStep 138991 = 208487) B208487
theorem B565055 : Blo 107783 565055 := bstep (se 1 (by rfl) ⟨423791, by rfl⟩ : syracuseStep 565055 = 847583) B847583
theorem B827657 : Blo 107783 827657 := bstep (se 2 (by rfl) ⟨310371, by rfl⟩ : syracuseStep 827657 = 620743) B620743
theorem B12919277 : Blo 107783 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B1319915 : Blo 107783 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B108031 : Blo 107783 108031 := bstep (se 1 (by rfl) ⟨81023, by rfl⟩ : syracuseStep 108031 = 162047) B162047
theorem B108123 : Blo 107783 108123 := bstep (se 1 (by rfl) ⟨81092, by rfl⟩ : syracuseStep 108123 = 162185) B162185
theorem B108239 : Blo 107783 108239 := bstep (se 1 (by rfl) ⟨81179, by rfl⟩ : syracuseStep 108239 = 162359) B162359
theorem B108287 : Blo 107783 108287 := bstep (se 1 (by rfl) ⟨81215, by rfl⟩ : syracuseStep 108287 = 162431) B162431
theorem B3123035 : Blo 107783 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B108539 : Blo 107783 108539 := bstep (se 1 (by rfl) ⟨81404, by rfl⟩ : syracuseStep 108539 = 162809) B162809
theorem B109211 : Blo 107783 109211 := bstep (se 1 (by rfl) ⟨81908, by rfl⟩ : syracuseStep 109211 = 163817) B163817
theorem B109223 : Blo 107783 109223 := bstep (se 1 (by rfl) ⟨81917, by rfl⟩ : syracuseStep 109223 = 163835) B163835
theorem B109263 : Blo 107783 109263 := bstep (se 1 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 109263 = 163895) B163895
theorem B109287 : Blo 107783 109287 := bstep (se 1 (by rfl) ⟨81965, by rfl⟩ : syracuseStep 109287 = 163931) B163931
theorem B371465 : Blo 107783 371465 := bstep (se 2 (by rfl) ⟨139299, by rfl⟩ : syracuseStep 371465 = 278599) B278599
theorem B109343 : Blo 107783 109343 := bstep (se 1 (by rfl) ⟨82007, by rfl⟩ : syracuseStep 109343 = 164015) B164015
theorem B109735 : Blo 107783 109735 := bstep (se 1 (by rfl) ⟨82301, by rfl⟩ : syracuseStep 109735 = 164603) B164603
theorem B109823 : Blo 107783 109823 := bstep (se 1 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 109823 = 164735) B164735
theorem B175367 : Blo 107783 175367 := bstep (se 1 (by rfl) ⟨131525, by rfl⟩ : syracuseStep 175367 = 263051) B263051
theorem B1322351 : Blo 107783 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B961915 : Blo 107783 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B372329 : Blo 107783 372329 := bstep (se 2 (by rfl) ⟨139623, by rfl⟩ : syracuseStep 372329 = 279247) B279247
theorem B634823 : Blo 107783 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B110623 : Blo 107783 110623 := bstep (se 1 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 110623 = 165935) B165935
theorem B1781927 : Blo 107783 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B209071 : Blo 107783 209071 := bstep (se 1 (by rfl) ⟨156803, by rfl⟩ : syracuseStep 209071 = 313607) B313607
theorem B635177 : Blo 107783 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B111103 : Blo 107783 111103 := bstep (se 1 (by rfl) ⟨83327, by rfl⟩ : syracuseStep 111103 = 166655) B166655
theorem B111727 : Blo 107783 111727 := bstep (se 1 (by rfl) ⟨83795, by rfl⟩ : syracuseStep 111727 = 167591) B167591
theorem B242855 : Blo 107783 242855 := bstep (se 1 (by rfl) ⟨182141, by rfl⟩ : syracuseStep 242855 = 364283) B364283
theorem B2110697 : Blo 107783 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B374057 : Blo 107783 374057 := bstep (se 2 (by rfl) ⟨140271, by rfl⟩ : syracuseStep 374057 = 280543) B280543
theorem B2209451 : Blo 107783 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1161503 : Blo 107783 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B2079017 : Blo 107783 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B244025 : Blo 107783 244025 := bstep (se 2 (by rfl) ⟨91509, by rfl⟩ : syracuseStep 244025 = 183019) B183019
theorem B998183 : Blo 107783 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B245033 : Blo 107783 245033 := bstep (se 2 (by rfl) ⟨91887, by rfl⟩ : syracuseStep 245033 = 183775) B183775
theorem B34356575 : Blo 107783 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B376271 : Blo 107783 376271 := bstep (se 1 (by rfl) ⟨282203, by rfl⟩ : syracuseStep 376271 = 564407) B564407
theorem B1785311 : Blo 107783 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B278063 : Blo 107783 278063 := bstep (se 1 (by rfl) ⟨208547, by rfl⟩ : syracuseStep 278063 = 417095) B417095
theorem B245321 : Blo 107783 245321 := bstep (se 2 (by rfl) ⟨91995, by rfl⟩ : syracuseStep 245321 = 183991) B183991
theorem B376595 : Blo 107783 376595 := bstep (se 1 (by rfl) ⟨282446, by rfl⟩ : syracuseStep 376595 = 564893) B564893
theorem B245735 : Blo 107783 245735 := bstep (se 1 (by rfl) ⟨184301, by rfl⟩ : syracuseStep 245735 = 368603) B368603
theorem B278689 : Blo 107783 278689 := bstep (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) B209017
theorem B311465 : Blo 107783 311465 := bstep (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) B233599
theorem B278711 : Blo 107783 278711 := bstep (se 1 (by rfl) ⟨209033, by rfl⟩ : syracuseStep 278711 = 418067) B418067
theorem B934091 : Blo 107783 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B1196531 : Blo 107783 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B246887 : Blo 107783 246887 := bstep (se 1 (by rfl) ⟨185165, by rfl⟩ : syracuseStep 246887 = 370331) B370331
theorem B541811 : Blo 107783 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B312457 : Blo 107783 312457 := bstep (se 2 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 312457 = 234343) B234343
theorem B279713 : Blo 107783 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B181993 : Blo 107783 181993 := bstep (se 2 (by rfl) ⟨68247, by rfl⟩ : syracuseStep 181993 = 136495) B136495
theorem B247535 : Blo 107783 247535 := bstep (se 1 (by rfl) ⟨185651, by rfl⟩ : syracuseStep 247535 = 371303) B371303
theorem B247571 : Blo 107783 247571 := bstep (se 1 (by rfl) ⟨185678, by rfl⟩ : syracuseStep 247571 = 371357) B371357
theorem B805295 : Blo 107783 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B249299 : Blo 107783 249299 := bstep (se 1 (by rfl) ⟨186974, by rfl⟩ : syracuseStep 249299 = 373949) B373949
theorem B1068659 : Blo 107783 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B249569 : Blo 107783 249569 := bstep (se 2 (by rfl) ⟨93588, by rfl⟩ : syracuseStep 249569 = 187177) B187177
theorem B348143 : Blo 107783 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B839807 : Blo 107783 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B250091 : Blo 107783 250091 := bstep (se 1 (by rfl) ⟨187568, by rfl⟩ : syracuseStep 250091 = 375137) B375137
theorem B250721 : Blo 107783 250721 := bstep (se 2 (by rfl) ⟨94020, by rfl⟩ : syracuseStep 250721 = 188041) B188041
theorem B185287 : Blo 107783 185287 := bstep (se 1 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 185287 = 277931) B277931
theorem B414983 : Blo 107783 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B546263 : Blo 107783 546263 := bstep (se 1 (by rfl) ⟨409697, by rfl⟩ : syracuseStep 546263 = 819395) B819395
theorem B251423 : Blo 107783 251423 := bstep (se 1 (by rfl) ⟨188567, by rfl⟩ : syracuseStep 251423 = 377135) B377135
theorem B1136177 : Blo 107783 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B284251 : Blo 107783 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B251495 : Blo 107783 251495 := bstep (se 1 (by rfl) ⟨188621, by rfl⟩ : syracuseStep 251495 = 377243) B377243
theorem B186779 : Blo 107783 186779 := bstep (se 1 (by rfl) ⟨140084, by rfl⟩ : syracuseStep 186779 = 280169) B280169
theorem B481751 : Blo 107783 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B416411 : Blo 107783 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B318107 : Blo 107783 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B547721 : Blo 107783 547721 := bstep (se 2 (by rfl) ⟨205395, by rfl⟩ : syracuseStep 547721 = 410791) B410791
theorem B613979 : Blo 107783 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B3661433 : Blo 107783 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B123367 : Blo 107783 123367 := bstep (se 1 (by rfl) ⟨92525, by rfl⟩ : syracuseStep 123367 = 185051) B185051
theorem B550313 : Blo 107783 550313 := bstep (se 2 (by rfl) ⟨206367, by rfl⟩ : syracuseStep 550313 = 412735) B412735
theorem B550799 : Blo 107783 550799 := bstep (se 1 (by rfl) ⟨413099, by rfl⟩ : syracuseStep 550799 = 826199) B826199
theorem B2550295 : Blo 107783 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B2255435 : Blo 107783 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B847097 : Blo 107783 847097 := bstep (se 2 (by rfl) ⟨317661, by rfl⟩ : syracuseStep 847097 = 635323) B635323
theorem B1044089 : Blo 107783 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B946151 : Blo 107783 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B553067 : Blo 107783 553067 := bstep (se 1 (by rfl) ⟨414800, by rfl⟩ : syracuseStep 553067 = 829601) B829601
theorem B586109 : Blo 107783 586109 := bstep (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) B219791
theorem B522139 : Blo 107783 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B1341521 : Blo 107783 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B15759521 : Blo 107783 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B161999 : Blo 107783 161999 := bstep (se 1 (by rfl) ⟨121499, by rfl⟩ : syracuseStep 161999 = 242999) B242999
theorem B162203 : Blo 107783 162203 := bstep (se 1 (by rfl) ⟨121652, by rfl⟩ : syracuseStep 162203 = 243305) B243305
theorem B162407 : Blo 107783 162407 := bstep (se 1 (by rfl) ⟨121805, by rfl⟩ : syracuseStep 162407 = 243611) B243611
theorem B2096239 : Blo 107783 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B294049 : Blo 107783 294049 := bstep (se 2 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 294049 = 220537) B220537
theorem B163295 : Blo 107783 163295 := bstep (se 1 (by rfl) ⟨122471, by rfl⟩ : syracuseStep 163295 = 244943) B244943
theorem B163775 : Blo 107783 163775 := bstep (se 1 (by rfl) ⟨122831, by rfl⟩ : syracuseStep 163775 = 245663) B245663
theorem B622727 : Blo 107783 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B164489 : Blo 107783 164489 := bstep (se 2 (by rfl) ⟨61683, by rfl⟩ : syracuseStep 164489 = 123367) B123367
theorem B164591 : Blo 107783 164591 := bstep (se 1 (by rfl) ⟨123443, by rfl⟩ : syracuseStep 164591 = 246887) B246887
theorem B361207 : Blo 107783 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B165023 : Blo 107783 165023 := bstep (se 1 (by rfl) ⟨123767, by rfl⟩ : syracuseStep 165023 = 247535) B247535
theorem B165047 : Blo 107783 165047 := bstep (se 1 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 165047 = 247571) B247571
theorem B166199 : Blo 107783 166199 := bstep (se 1 (by rfl) ⟨124649, by rfl⟩ : syracuseStep 166199 = 249299) B249299
theorem B526675 : Blo 107783 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B166379 : Blo 107783 166379 := bstep (se 1 (by rfl) ⟨124784, by rfl⟩ : syracuseStep 166379 = 249569) B249569
theorem B559871 : Blo 107783 559871 := bstep (se 1 (by rfl) ⟨419903, by rfl⟩ : syracuseStep 559871 = 839807) B839807
theorem B166727 : Blo 107783 166727 := bstep (se 1 (by rfl) ⟨125045, by rfl⟩ : syracuseStep 166727 = 250091) B250091
theorem B167147 : Blo 107783 167147 := bstep (se 1 (by rfl) ⟨125360, by rfl⟩ : syracuseStep 167147 = 250721) B250721
theorem B364175 : Blo 107783 364175 := bstep (se 1 (by rfl) ⟨273131, by rfl⟩ : syracuseStep 364175 = 546263) B546263
theorem B167615 : Blo 107783 167615 := bstep (se 1 (by rfl) ⟨125711, by rfl⟩ : syracuseStep 167615 = 251423) B251423
theorem B757451 : Blo 107783 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B1511135 : Blo 107783 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B167663 : Blo 107783 167663 := bstep (se 1 (by rfl) ⟨125747, by rfl⟩ : syracuseStep 167663 = 251495) B251495
theorem B1282553 : Blo 107783 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B365147 : Blo 107783 365147 := bstep (se 1 (by rfl) ⟨273860, by rfl⟩ : syracuseStep 365147 = 547721) B547721
theorem B792089 : Blo 107783 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B366875 : Blo 107783 366875 := bstep (se 1 (by rfl) ⟨275156, by rfl⟩ : syracuseStep 366875 = 550313) B550313
theorem B367199 : Blo 107783 367199 := bstep (se 1 (by rfl) ⟨275399, by rfl⟩ : syracuseStep 367199 = 550799) B550799
theorem B2661821 : Blo 107783 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B564731 : Blo 107783 564731 := bstep (se 1 (by rfl) ⟨423548, by rfl⟩ : syracuseStep 564731 = 847097) B847097
theorem B696059 : Blo 107783 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B696185 : Blo 107783 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B630767 : Blo 107783 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B2236481 : Blo 107783 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B368711 : Blo 107783 368711 := bstep (se 1 (by rfl) ⟨276533, by rfl⟩ : syracuseStep 368711 = 553067) B553067
theorem B1187951 : Blo 107783 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B402569 : Blo 107783 402569 := bstep (se 2 (by rfl) ⟨150963, by rfl⟩ : syracuseStep 402569 = 301927) B301927
theorem B894347 : Blo 107783 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B107999 : Blo 107783 107999 := bstep (se 1 (by rfl) ⟨80999, by rfl⟩ : syracuseStep 107999 = 161999) B161999
theorem B2794985 : Blo 107783 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B1386011 : Blo 107783 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B108135 : Blo 107783 108135 := bstep (se 1 (by rfl) ⟨81101, by rfl⟩ : syracuseStep 108135 = 162203) B162203
theorem B108271 : Blo 107783 108271 := bstep (se 1 (by rfl) ⟨81203, by rfl⟩ : syracuseStep 108271 = 162407) B162407
theorem B108863 : Blo 107783 108863 := bstep (se 1 (by rfl) ⟨81647, by rfl⟩ : syracuseStep 108863 = 163295) B163295
theorem B1190207 : Blo 107783 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B928381 : Blo 107783 928381 := bstep (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) B348143
theorem B109183 : Blo 107783 109183 := bstep (se 1 (by rfl) ⟨81887, by rfl⟩ : syracuseStep 109183 = 163775) B163775
theorem B371585 : Blo 107783 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B797687 : Blo 107783 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B109595 : Blo 107783 109595 := bstep (se 1 (by rfl) ⟨82196, by rfl⟩ : syracuseStep 109595 = 164393) B164393
theorem B830573 : Blo 107783 830573 := bstep (se 3 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 830573 = 311465) B311465
theorem B372059 : Blo 107783 372059 := bstep (se 1 (by rfl) ⟨279044, by rfl⟩ : syracuseStep 372059 = 558089) B558089
theorem B831059 : Blo 107783 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B110311 : Blo 107783 110311 := bstep (se 1 (by rfl) ⟨82733, by rfl⟩ : syracuseStep 110311 = 165467) B165467
theorem B536863 : Blo 107783 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B373031 : Blo 107783 373031 := bstep (se 1 (by rfl) ⟨279773, by rfl⟩ : syracuseStep 373031 = 559547) B559547
theorem B111087 : Blo 107783 111087 := bstep (se 1 (by rfl) ⟨83315, by rfl⟩ : syracuseStep 111087 = 166631) B166631
theorem B111195 : Blo 107783 111195 := bstep (se 1 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 111195 = 166793) B166793
theorem B242657 : Blo 107783 242657 := bstep (se 2 (by rfl) ⟨90996, by rfl⟩ : syracuseStep 242657 = 181993) B181993
theorem B111643 : Blo 107783 111643 := bstep (se 1 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 111643 = 167465) B167465
theorem B3519773 : Blo 107783 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B243179 : Blo 107783 243179 := bstep (se 1 (by rfl) ⟨182384, by rfl⟩ : syracuseStep 243179 = 364769) B364769
theorem B1029631 : Blo 107783 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B374327 : Blo 107783 374327 := bstep (se 1 (by rfl) ⟨280745, by rfl⟩ : syracuseStep 374327 = 561491) B561491
theorem B505607 : Blo 107783 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B374651 : Blo 107783 374651 := bstep (se 1 (by rfl) ⟨280988, by rfl⟩ : syracuseStep 374651 = 561977) B561977
theorem B276655 : Blo 107783 276655 := bstep (se 1 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 276655 = 414983) B414983
theorem B277607 : Blo 107783 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B212071 : Blo 107783 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B409319 : Blo 107783 409319 := bstep (se 1 (by rfl) ⟨306989, by rfl⟩ : syracuseStep 409319 = 613979) B613979
theorem B2440955 : Blo 107783 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B507667 : Blo 107783 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B376703 : Blo 107783 376703 := bstep (se 1 (by rfl) ⟨282527, by rfl⟩ : syracuseStep 376703 = 565055) B565055
theorem B278761 : Blo 107783 278761 := bstep (se 2 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 278761 = 209071) B209071
theorem B2082023 : Blo 107783 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B247049 : Blo 107783 247049 := bstep (se 2 (by rfl) ⟨92643, by rfl⟩ : syracuseStep 247049 = 185287) B185287
theorem B247643 : Blo 107783 247643 := bstep (se 1 (by rfl) ⟨185732, by rfl⟩ : syracuseStep 247643 = 371465) B371465
theorem B379001 : Blo 107783 379001 := bstep (se 2 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 379001 = 284251) B284251
theorem B116911 : Blo 107783 116911 := bstep (se 1 (by rfl) ⟨87683, by rfl⟩ : syracuseStep 116911 = 175367) B175367
theorem B248219 : Blo 107783 248219 := bstep (se 1 (by rfl) ⟨186164, by rfl⟩ : syracuseStep 248219 = 372329) B372329
theorem B183593 : Blo 107783 183593 := bstep (se 2 (by rfl) ⟨68847, by rfl⟩ : syracuseStep 183593 = 137695) B137695
theorem B249371 : Blo 107783 249371 := bstep (se 1 (by rfl) ⟨187028, by rfl⟩ : syracuseStep 249371 = 374057) B374057
theorem B10506347 : Blo 107783 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B184457 : Blo 107783 184457 := bstep (se 2 (by rfl) ⟨69171, by rfl⟩ : syracuseStep 184457 = 138343) B138343
theorem B774335 : Blo 107783 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B250847 : Blo 107783 250847 := bstep (se 1 (by rfl) ⟨188135, by rfl⟩ : syracuseStep 250847 = 376271) B376271
theorem B185321 : Blo 107783 185321 := bstep (se 2 (by rfl) ⟨69495, by rfl⟩ : syracuseStep 185321 = 138991) B138991
theorem B185375 : Blo 107783 185375 := bstep (se 1 (by rfl) ⟨139031, by rfl⟩ : syracuseStep 185375 = 278063) B278063
theorem B251063 : Blo 107783 251063 := bstep (se 1 (by rfl) ⟨188297, by rfl⟩ : syracuseStep 251063 = 376595) B376595
theorem B185807 : Blo 107783 185807 := bstep (se 1 (by rfl) ⟨139355, by rfl⟩ : syracuseStep 185807 = 278711) B278711
theorem B1332755 : Blo 107783 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B186475 : Blo 107783 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B415955 : Blo 107783 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B416609 : Blo 107783 416609 := bstep (se 2 (by rfl) ⟨156228, by rfl⟩ : syracuseStep 416609 = 312457) B312457
theorem B2120843 : Blo 107783 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B417383 : Blo 107783 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B712439 : Blo 107783 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B3400393 : Blo 107783 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B124519 : Blo 107783 124519 := bstep (se 1 (by rfl) ⟨93389, by rfl⟩ : syracuseStep 124519 = 186779) B186779
theorem B321167 : Blo 107783 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B5891869 : Blo 107783 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B551771 : Blo 107783 551771 := bstep (se 1 (by rfl) ⟨413828, by rfl⟩ : syracuseStep 551771 = 827657) B827657
theorem B8612851 : Blo 107783 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B1568261 : Blo 107783 1568261 := bstep (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) B294049
theorem B1503623 : Blo 107783 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B881567 : Blo 107783 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B423215 : Blo 107783 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B882089 : Blo 107783 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B423451 : Blo 107783 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B390739 : Blo 107783 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B161903 : Blo 107783 161903 := bstep (se 1 (by rfl) ⟨121427, by rfl⟩ : syracuseStep 161903 = 242855) B242855
theorem B1407131 : Blo 107783 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B162683 : Blo 107783 162683 := bstep (se 1 (by rfl) ⟨122012, by rfl⟩ : syracuseStep 162683 = 244025) B244025
theorem B163355 : Blo 107783 163355 := bstep (se 1 (by rfl) ⟨122516, by rfl⟩ : syracuseStep 163355 = 245033) B245033
theorem B22904383 : Blo 107783 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B163547 : Blo 107783 163547 := bstep (se 1 (by rfl) ⟨122660, by rfl⟩ : syracuseStep 163547 = 245321) B245321
theorem B163823 : Blo 107783 163823 := bstep (se 1 (by rfl) ⟨122867, by rfl⟩ : syracuseStep 163823 = 245735) B245735
theorem B164699 : Blo 107783 164699 := bstep (se 1 (by rfl) ⟨123524, by rfl⟩ : syracuseStep 164699 = 247049) B247049
theorem B165095 : Blo 107783 165095 := bstep (se 1 (by rfl) ⟨123821, by rfl⟩ : syracuseStep 165095 = 247643) B247643
theorem B165479 : Blo 107783 165479 := bstep (se 1 (by rfl) ⟨124109, by rfl⟩ : syracuseStep 165479 = 248219) B248219
theorem B166025 : Blo 107783 166025 := bstep (se 2 (by rfl) ⟨62259, by rfl⟩ : syracuseStep 166025 = 124519) B124519
theorem B166247 : Blo 107783 166247 := bstep (se 1 (by rfl) ⟨124685, by rfl⟩ : syracuseStep 166247 = 249371) B249371
theorem B855035 : Blo 107783 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B167231 : Blo 107783 167231 := bstep (se 1 (by rfl) ⟨125423, by rfl⟩ : syracuseStep 167231 = 250847) B250847
theorem B167375 : Blo 107783 167375 := bstep (se 1 (by rfl) ⟨125531, by rfl⟩ : syracuseStep 167375 = 251063) B251063
theorem B888503 : Blo 107783 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B528059 : Blo 107783 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B1413895 : Blo 107783 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B1774547 : Blo 107783 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B464039 : Blo 107783 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B464123 : Blo 107783 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B268379 : Blo 107783 268379 := bstep (se 1 (by rfl) ⟨201284, by rfl⟩ : syracuseStep 268379 = 402569) B402569
theorem B596231 : Blo 107783 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B924007 : Blo 107783 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B793471 : Blo 107783 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B367847 : Blo 107783 367847 := bstep (se 1 (by rfl) ⟨275885, by rfl⟩ : syracuseStep 367847 = 551771) B551771
theorem B531791 : Blo 107783 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B990893 : Blo 107783 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B368873 : Blo 107783 368873 := bstep (se 2 (by rfl) ⟨138327, by rfl⟩ : syracuseStep 368873 = 276655) B276655
theorem B107935 : Blo 107783 107935 := bstep (se 1 (by rfl) ⟨80951, by rfl⟩ : syracuseStep 107935 = 161903) B161903
theorem B108455 : Blo 107783 108455 := bstep (se 1 (by rfl) ⟨81341, by rfl⟩ : syracuseStep 108455 = 162683) B162683
theorem B108903 : Blo 107783 108903 := bstep (se 1 (by rfl) ⟨81677, by rfl⟩ : syracuseStep 108903 = 163355) B163355
theorem B109031 : Blo 107783 109031 := bstep (se 1 (by rfl) ⟨81773, by rfl⟩ : syracuseStep 109031 = 163547) B163547
theorem B272879 : Blo 107783 272879 := bstep (se 1 (by rfl) ⟨204659, by rfl⟩ : syracuseStep 272879 = 409319) B409319
theorem B109215 : Blo 107783 109215 := bstep (se 1 (by rfl) ⟨81911, by rfl⟩ : syracuseStep 109215 = 163823) B163823
theorem B371681 : Blo 107783 371681 := bstep (se 2 (by rfl) ⟨139380, by rfl⟩ : syracuseStep 371681 = 278761) B278761
theorem B109659 : Blo 107783 109659 := bstep (se 1 (by rfl) ⟨82244, by rfl⟩ : syracuseStep 109659 = 164489) B164489
theorem B109727 : Blo 107783 109727 := bstep (se 1 (by rfl) ⟨82295, by rfl⟩ : syracuseStep 109727 = 164591) B164591
theorem B110015 : Blo 107783 110015 := bstep (se 1 (by rfl) ⟨82511, by rfl⟩ : syracuseStep 110015 = 165023) B165023
theorem B110031 : Blo 107783 110031 := bstep (se 1 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 110031 = 165047) B165047
theorem B1388015 : Blo 107783 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B4533857 : Blo 107783 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B4009661 : Blo 107783 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B110799 : Blo 107783 110799 := bstep (se 1 (by rfl) ⟨83099, by rfl⟩ : syracuseStep 110799 = 166199) B166199
theorem B110919 : Blo 107783 110919 := bstep (se 1 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 110919 = 166379) B166379
theorem B373247 : Blo 107783 373247 := bstep (se 1 (by rfl) ⟨279935, by rfl⟩ : syracuseStep 373247 = 559871) B559871
theorem B111151 : Blo 107783 111151 := bstep (se 1 (by rfl) ⟨83363, by rfl⟩ : syracuseStep 111151 = 166727) B166727
theorem B111431 : Blo 107783 111431 := bstep (se 1 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 111431 = 167147) B167147
theorem B242783 : Blo 107783 242783 := bstep (se 1 (by rfl) ⟨182087, by rfl⟩ : syracuseStep 242783 = 364175) B364175
theorem B111743 : Blo 107783 111743 := bstep (se 1 (by rfl) ⟨83807, by rfl⟩ : syracuseStep 111743 = 167615) B167615
theorem B504967 : Blo 107783 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B111775 : Blo 107783 111775 := bstep (se 1 (by rfl) ⟨83831, by rfl⟩ : syracuseStep 111775 = 167663) B167663
theorem B243431 : Blo 107783 243431 := bstep (se 1 (by rfl) ⟨182573, by rfl⟩ : syracuseStep 243431 = 365147) B365147
theorem B702233 : Blo 107783 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B11483801 : Blo 107783 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B277303 : Blo 107783 277303 := bstep (se 1 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 277303 = 415955) B415955
theorem B244583 : Blo 107783 244583 := bstep (se 1 (by rfl) ⟨183437, by rfl⟩ : syracuseStep 244583 = 366875) B366875
theorem B244799 : Blo 107783 244799 := bstep (se 1 (by rfl) ⟨183599, by rfl⟩ : syracuseStep 244799 = 367199) B367199
theorem B277739 : Blo 107783 277739 := bstep (se 1 (by rfl) ⟨208304, by rfl⟩ : syracuseStep 277739 = 416609) B416609
theorem B376487 : Blo 107783 376487 := bstep (se 1 (by rfl) ⟨282365, by rfl⟩ : syracuseStep 376487 = 564731) B564731
theorem B278255 : Blo 107783 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B474959 : Blo 107783 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B1490987 : Blo 107783 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B245807 : Blo 107783 245807 := bstep (se 1 (by rfl) ⟨184355, by rfl⟩ : syracuseStep 245807 = 368711) B368711
theorem B214111 : Blo 107783 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B248039 : Blo 107783 248039 := bstep (se 1 (by rfl) ⟨186029, by rfl⟩ : syracuseStep 248039 = 372059) B372059
theorem B5393141 : Blo 107783 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B248633 : Blo 107783 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B248687 : Blo 107783 248687 := bstep (se 1 (by rfl) ⟨186515, by rfl⟩ : syracuseStep 248687 = 373031) B373031
theorem B2346515 : Blo 107783 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B282143 : Blo 107783 282143 := bstep (se 1 (by rfl) ⟨211607, by rfl⟩ : syracuseStep 282143 = 423215) B423215
theorem B249551 : Blo 107783 249551 := bstep (se 1 (by rfl) ⟨187163, by rfl⟩ : syracuseStep 249551 = 374327) B374327
theorem B249767 : Blo 107783 249767 := bstep (se 1 (by rfl) ⟨187325, by rfl⟩ : syracuseStep 249767 = 374651) B374651
theorem B938087 : Blo 107783 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B282761 : Blo 107783 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B185071 : Blo 107783 185071 := bstep (se 1 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 185071 = 277607) B277607
theorem B676889 : Blo 107783 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B1627303 : Blo 107783 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B251135 : Blo 107783 251135 := bstep (se 1 (by rfl) ⟨188351, by rfl⟩ : syracuseStep 251135 = 376703) B376703
theorem B415151 : Blo 107783 415151 := bstep (se 1 (by rfl) ⟨311363, by rfl⟩ : syracuseStep 415151 = 622727) B622727
theorem B481609 : Blo 107783 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B12671477 : Blo 107783 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B252667 : Blo 107783 252667 := bstep (se 1 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 252667 = 379001) B379001
theorem B122395 : Blo 107783 122395 := bstep (se 1 (by rfl) ⟨91796, by rfl⟩ : syracuseStep 122395 = 183593) B183593
theorem B7855825 : Blo 107783 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B1007423 : Blo 107783 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B7004231 : Blo 107783 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B122971 : Blo 107783 122971 := bstep (se 1 (by rfl) ⟨92228, by rfl⟩ : syracuseStep 122971 = 184457) B184457
theorem B516223 : Blo 107783 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B155881 : Blo 107783 155881 := bstep (se 2 (by rfl) ⟨58455, by rfl⟩ : syracuseStep 155881 = 116911) B116911
theorem B123547 : Blo 107783 123547 := bstep (se 1 (by rfl) ⟨92660, by rfl⟩ : syracuseStep 123547 = 185321) B185321
theorem B123583 : Blo 107783 123583 := bstep (se 1 (by rfl) ⟨92687, by rfl⟩ : syracuseStep 123583 = 185375) B185375
theorem B1237841 : Blo 107783 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B123871 : Blo 107783 123871 := bstep (se 1 (by rfl) ⟨92903, by rfl⟩ : syracuseStep 123871 = 185807) B185807
theorem B420511 : Blo 107783 420511 := bstep (se 1 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 420511 = 630767) B630767
theorem B715817 : Blo 107783 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B1863323 : Blo 107783 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B1372841 : Blo 107783 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B553715 : Blo 107783 553715 := bstep (se 1 (by rfl) ⟨415286, by rfl⟩ : syracuseStep 553715 = 830573) B830573
theorem B520985 : Blo 107783 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B1045507 : Blo 107783 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B554039 : Blo 107783 554039 := bstep (se 1 (by rfl) ⟨415529, by rfl⟩ : syracuseStep 554039 = 831059) B831059
theorem B2258405 : Blo 107783 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B587711 : Blo 107783 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B161771 : Blo 107783 161771 := bstep (se 1 (by rfl) ⟨121328, by rfl⟩ : syracuseStep 161771 = 242657) B242657
theorem B588059 : Blo 107783 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B162119 : Blo 107783 162119 := bstep (se 1 (by rfl) ⟨121589, by rfl⟩ : syracuseStep 162119 = 243179) B243179
theorem B30539177 : Blo 107783 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B163871 : Blo 107783 163871 := bstep (se 1 (by rfl) ⟨122903, by rfl⟩ : syracuseStep 163871 = 245807) B245807
theorem B163961 : Blo 107783 163961 := bstep (se 2 (by rfl) ⟨61485, by rfl⟩ : syracuseStep 163961 = 122971) B122971
theorem B688297 : Blo 107783 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B164729 : Blo 107783 164729 := bstep (se 2 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 164729 = 123547) B123547
theorem B164777 : Blo 107783 164777 := bstep (se 2 (by rfl) ⟨61791, by rfl⟩ : syracuseStep 164777 = 123583) B123583
theorem B165161 : Blo 107783 165161 := bstep (se 2 (by rfl) ⟨61935, by rfl⟩ : syracuseStep 165161 = 123871) B123871
theorem B165359 : Blo 107783 165359 := bstep (se 1 (by rfl) ⟨124019, by rfl⟩ : syracuseStep 165359 = 248039) B248039
theorem B165755 : Blo 107783 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B165791 : Blo 107783 165791 := bstep (se 1 (by rfl) ⟨124343, by rfl⟩ : syracuseStep 165791 = 248687) B248687
theorem B166367 : Blo 107783 166367 := bstep (se 1 (by rfl) ⟨124775, by rfl⟩ : syracuseStep 166367 = 249551) B249551
theorem B166511 : Blo 107783 166511 := bstep (se 1 (by rfl) ⟨124883, by rfl⟩ : syracuseStep 166511 = 249767) B249767
theorem B625391 : Blo 107783 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B1183031 : Blo 107783 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B167423 : Blo 107783 167423 := bstep (se 1 (by rfl) ⟨125567, by rfl⟩ : syracuseStep 167423 = 251135) B251135
theorem B560681 : Blo 107783 560681 := bstep (se 2 (by rfl) ⟨210255, by rfl⟩ : syracuseStep 560681 = 420511) B420511
theorem B397487 : Blo 107783 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B660595 : Blo 107783 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B825227 : Blo 107783 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B2169737 : Blo 107783 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B925343 : Blo 107783 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B3022571 : Blo 107783 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B369143 : Blo 107783 369143 := bstep (se 1 (by rfl) ⟨276857, by rfl⟩ : syracuseStep 369143 = 553715) B553715
theorem B369359 : Blo 107783 369359 := bstep (se 1 (by rfl) ⟨277019, by rfl⟩ : syracuseStep 369359 = 554039) B554039
theorem B336889 : Blo 107783 336889 := bstep (se 2 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 336889 = 252667) B252667
theorem B369737 : Blo 107783 369737 := bstep (se 2 (by rfl) ⟨138651, by rfl⟩ : syracuseStep 369737 = 277303) B277303
theorem B1057961 : Blo 107783 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B468155 : Blo 107783 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B107847 : Blo 107783 107847 := bstep (se 1 (by rfl) ⟨80885, by rfl⟩ : syracuseStep 107847 = 161771) B161771
theorem B108079 : Blo 107783 108079 := bstep (se 1 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 108079 = 162119) B162119
theorem B2369341 : Blo 107783 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B20359451 : Blo 107783 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B3975965 : Blo 107783 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B207841 : Blo 107783 207841 := bstep (se 2 (by rfl) ⟨77940, by rfl⟩ : syracuseStep 207841 = 155881) B155881
theorem B109799 : Blo 107783 109799 := bstep (se 1 (by rfl) ⟨82349, by rfl⟩ : syracuseStep 109799 = 164699) B164699
theorem B110063 : Blo 107783 110063 := bstep (se 1 (by rfl) ⟨82547, by rfl⟩ : syracuseStep 110063 = 165095) B165095
theorem B110319 : Blo 107783 110319 := bstep (se 1 (by rfl) ⟨82739, by rfl⟩ : syracuseStep 110319 = 165479) B165479
theorem B110683 : Blo 107783 110683 := bstep (se 1 (by rfl) ⟨83012, by rfl⟩ : syracuseStep 110683 = 166025) B166025
theorem B110831 : Blo 107783 110831 := bstep (se 1 (by rfl) ⟨83123, by rfl⟩ : syracuseStep 110831 = 166247) B166247
theorem B2568581 : Blo 107783 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B570023 : Blo 107783 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B111487 : Blo 107783 111487 := bstep (se 1 (by rfl) ⟨83615, by rfl⟩ : syracuseStep 111487 = 167231) B167231
theorem B111583 : Blo 107783 111583 := bstep (se 1 (by rfl) ⟨83687, by rfl⟩ : syracuseStep 111583 = 167375) B167375
theorem B309359 : Blo 107783 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B309415 : Blo 107783 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B276767 : Blo 107783 276767 := bstep (se 1 (by rfl) ⟨207575, by rfl⟩ : syracuseStep 276767 = 415151) B415151
theorem B178919 : Blo 107783 178919 := bstep (se 1 (by rfl) ⟨134189, by rfl⟩ : syracuseStep 178919 = 268379) B268379
theorem B245231 : Blo 107783 245231 := bstep (se 1 (by rfl) ⟨183923, by rfl⟩ : syracuseStep 245231 = 367847) B367847
theorem B671615 : Blo 107783 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B4669487 : Blo 107783 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B245915 : Blo 107783 245915 := bstep (se 1 (by rfl) ⟨184436, by rfl⟩ : syracuseStep 245915 = 368873) B368873
theorem B246761 : Blo 107783 246761 := bstep (se 2 (by rfl) ⟨92535, by rfl⟩ : syracuseStep 246761 = 185071) B185071
theorem B1885193 : Blo 107783 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B1394009 : Blo 107783 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B673289 : Blo 107783 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B181919 : Blo 107783 181919 := bstep (se 1 (by rfl) ⟨136439, by rfl⟩ : syracuseStep 181919 = 272879) B272879
theorem B247787 : Blo 107783 247787 := bstep (se 1 (by rfl) ⟨185840, by rfl⟩ : syracuseStep 247787 = 371681) B371681
theorem B477211 : Blo 107783 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B2673107 : Blo 107783 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B248831 : Blo 107783 248831 := bstep (se 1 (by rfl) ⟨186623, by rfl⟩ : syracuseStep 248831 = 373247) B373247
theorem B1232009 : Blo 107783 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B347323 : Blo 107783 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B7655867 : Blo 107783 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B185159 : Blo 107783 185159 := bstep (se 1 (by rfl) ⟨138869, by rfl⟩ : syracuseStep 185159 = 277739) B277739
theorem B10474433 : Blo 107783 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B250991 : Blo 107783 250991 := bstep (se 1 (by rfl) ⟨188243, by rfl⟩ : syracuseStep 250991 = 376487) B376487
theorem B185503 : Blo 107783 185503 := bstep (se 1 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 185503 = 278255) B278255
theorem B316639 : Blo 107783 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B285481 : Blo 107783 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B3595427 : Blo 107783 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B1564343 : Blo 107783 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B188095 : Blo 107783 188095 := bstep (se 1 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 188095 = 282143) B282143
theorem B352039 : Blo 107783 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B188507 : Blo 107783 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B451259 : Blo 107783 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B8447651 : Blo 107783 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B354527 : Blo 107783 354527 := bstep (se 1 (by rfl) ⟨265895, by rfl⟩ : syracuseStep 354527 = 531791) B531791
theorem B1242215 : Blo 107783 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B915227 : Blo 107783 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B161855 : Blo 107783 161855 := bstep (se 1 (by rfl) ⟨121391, by rfl⟩ : syracuseStep 161855 = 242783) B242783
theorem B1505603 : Blo 107783 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B162287 : Blo 107783 162287 := bstep (se 1 (by rfl) ⟨121715, by rfl⟩ : syracuseStep 162287 = 243431) B243431
theorem B391807 : Blo 107783 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B392039 : Blo 107783 392039 := bstep (se 1 (by rfl) ⟨294029, by rfl⟩ : syracuseStep 392039 = 588059) B588059
theorem B163055 : Blo 107783 163055 := bstep (se 1 (by rfl) ⟨122291, by rfl⟩ : syracuseStep 163055 = 244583) B244583
theorem B163193 : Blo 107783 163193 := bstep (se 2 (by rfl) ⟨61197, by rfl⟩ : syracuseStep 163193 = 122395) B122395
theorem B163199 : Blo 107783 163199 := bstep (se 1 (by rfl) ⟨122399, by rfl⟩ : syracuseStep 163199 = 244799) B244799
theorem B3112991 : Blo 107783 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B163943 : Blo 107783 163943 := bstep (se 1 (by rfl) ⟨122957, by rfl⟩ : syracuseStep 163943 = 245915) B245915
theorem B917729 : Blo 107783 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B164507 : Blo 107783 164507 := bstep (se 1 (by rfl) ⟨123380, by rfl⟩ : syracuseStep 164507 = 246761) B246761
theorem B165191 : Blo 107783 165191 := bstep (se 1 (by rfl) ⟨123893, by rfl⟩ : syracuseStep 165191 = 247787) B247787
theorem B165887 : Blo 107783 165887 := bstep (se 1 (by rfl) ⟨124415, by rfl⟩ : syracuseStep 165887 = 248831) B248831
theorem B821339 : Blo 107783 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B788687 : Blo 107783 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B2821229 : Blo 107783 2821229 := bstep (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) B1057961
theorem B6982955 : Blo 107783 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B167327 : Blo 107783 167327 := bstep (se 1 (by rfl) ⟨125495, by rfl⟩ : syracuseStep 167327 = 250991) B250991
theorem B463097 : Blo 107783 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B1446491 : Blo 107783 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B2396951 : Blo 107783 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B300839 : Blo 107783 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B236351 : Blo 107783 236351 := bstep (se 1 (by rfl) ⟨177263, by rfl⟩ : syracuseStep 236351 = 354527) B354527
theorem B13572967 : Blo 107783 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B1712387 : Blo 107783 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B828143 : Blo 107783 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B107903 : Blo 107783 107903 := bstep (se 1 (by rfl) ⟨80927, by rfl⟩ : syracuseStep 107903 = 161855) B161855
theorem B206239 : Blo 107783 206239 := bstep (se 1 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 206239 = 309359) B309359
theorem B108191 : Blo 107783 108191 := bstep (se 1 (by rfl) ⟨81143, by rfl⟩ : syracuseStep 108191 = 162287) B162287
theorem B108703 : Blo 107783 108703 := bstep (se 1 (by rfl) ⟨81527, by rfl⟩ : syracuseStep 108703 = 163055) B163055
theorem B108795 : Blo 107783 108795 := bstep (se 1 (by rfl) ⟨81596, by rfl⟩ : syracuseStep 108795 = 163193) B163193
theorem B108799 : Blo 107783 108799 := bstep (se 1 (by rfl) ⟨81599, by rfl⟩ : syracuseStep 108799 = 163199) B163199
theorem B469385 : Blo 107783 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B109247 : Blo 107783 109247 := bstep (se 1 (by rfl) ⟨81935, by rfl⟩ : syracuseStep 109247 = 163871) B163871
theorem B109307 : Blo 107783 109307 := bstep (se 1 (by rfl) ⟨81980, by rfl⟩ : syracuseStep 109307 = 163961) B163961
theorem B1059965 : Blo 107783 1059965 := bstep (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) B397487
theorem B109819 : Blo 107783 109819 := bstep (se 1 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 109819 = 164729) B164729
theorem B109851 : Blo 107783 109851 := bstep (se 1 (by rfl) ⟨82388, by rfl⟩ : syracuseStep 109851 = 164777) B164777
theorem B1256795 : Blo 107783 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B110107 : Blo 107783 110107 := bstep (se 1 (by rfl) ⟨82580, by rfl⟩ : syracuseStep 110107 = 165161) B165161
theorem B929339 : Blo 107783 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B110239 : Blo 107783 110239 := bstep (se 1 (by rfl) ⟨82679, by rfl⟩ : syracuseStep 110239 = 165359) B165359
theorem B110503 : Blo 107783 110503 := bstep (se 1 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 110503 = 165755) B165755
theorem B110527 : Blo 107783 110527 := bstep (se 1 (by rfl) ⟨82895, by rfl⟩ : syracuseStep 110527 = 165791) B165791
theorem B1782071 : Blo 107783 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B110911 : Blo 107783 110911 := bstep (se 1 (by rfl) ⟨83183, by rfl⟩ : syracuseStep 110911 = 166367) B166367
theorem B111007 : Blo 107783 111007 := bstep (se 1 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 111007 = 166511) B166511
theorem B111615 : Blo 107783 111615 := bstep (se 1 (by rfl) ⟨83711, by rfl⟩ : syracuseStep 111615 = 167423) B167423
theorem B373787 : Blo 107783 373787 := bstep (se 1 (by rfl) ⟨280340, by rfl⟩ : syracuseStep 373787 = 560681) B560681
theorem B3159121 : Blo 107783 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B636281 : Blo 107783 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B277121 : Blo 107783 277121 := bstep (se 2 (by rfl) ⟨103920, by rfl⟩ : syracuseStep 277121 = 207841) B207841
theorem B2015047 : Blo 107783 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B246095 : Blo 107783 246095 := bstep (se 1 (by rfl) ⟨184571, by rfl⟩ : syracuseStep 246095 = 369143) B369143
theorem B246239 : Blo 107783 246239 := bstep (se 1 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 246239 = 369359) B369359
theorem B246491 : Blo 107783 246491 := bstep (se 1 (by rfl) ⟨184868, by rfl⟩ : syracuseStep 246491 = 369737) B369737
theorem B312103 : Blo 107783 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B1688741 : Blo 107783 1688741 := bstep (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) B316639
theorem B247337 : Blo 107783 247337 := bstep (se 2 (by rfl) ⟨92751, by rfl⟩ : syracuseStep 247337 = 185503) B185503
theorem B412553 : Blo 107783 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B380015 : Blo 107783 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B380641 : Blo 107783 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B610151 : Blo 107783 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B184511 : Blo 107783 184511 := bstep (se 1 (by rfl) ⟨138383, by rfl⟩ : syracuseStep 184511 = 276767) B276767
theorem B1003735 : Blo 107783 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B119279 : Blo 107783 119279 := bstep (se 1 (by rfl) ⟨89459, by rfl⟩ : syracuseStep 119279 = 178919) B178919
theorem B250793 : Blo 107783 250793 := bstep (se 2 (by rfl) ⟨94047, by rfl⟩ : syracuseStep 250793 = 188095) B188095
theorem B447743 : Blo 107783 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B448859 : Blo 107783 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B121279 : Blo 107783 121279 := bstep (se 1 (by rfl) ⟨90959, by rfl⟩ : syracuseStep 121279 = 181919) B181919
theorem B449185 : Blo 107783 449185 := bstep (se 2 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 449185 = 336889) B336889
theorem B416927 : Blo 107783 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B5103911 : Blo 107783 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B123439 : Blo 107783 123439 := bstep (se 1 (by rfl) ⟨92579, by rfl⟩ : syracuseStep 123439 = 185159) B185159
theorem B550151 : Blo 107783 550151 := bstep (se 1 (by rfl) ⟨412613, by rfl⟩ : syracuseStep 550151 = 825227) B825227
theorem B616895 : Blo 107783 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B1042895 : Blo 107783 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B125671 : Blo 107783 125671 := bstep (se 1 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 125671 = 188507) B188507
theorem B5631767 : Blo 107783 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B880793 : Blo 107783 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B2650643 : Blo 107783 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B522409 : Blo 107783 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B261359 : Blo 107783 261359 := bstep (se 1 (by rfl) ⟨196019, by rfl⟩ : syracuseStep 261359 = 392039) B392039
theorem B163487 : Blo 107783 163487 := bstep (se 1 (by rfl) ⟨122615, by rfl⟩ : syracuseStep 163487 = 245231) B245231
theorem B164063 : Blo 107783 164063 := bstep (se 1 (by rfl) ⟨123047, by rfl⟩ : syracuseStep 164063 = 246095) B246095
theorem B164159 : Blo 107783 164159 := bstep (se 1 (by rfl) ⟨123119, by rfl⟩ : syracuseStep 164159 = 246239) B246239
theorem B164327 : Blo 107783 164327 := bstep (se 1 (by rfl) ⟨123245, by rfl⟩ : syracuseStep 164327 = 246491) B246491
theorem B164585 : Blo 107783 164585 := bstep (se 2 (by rfl) ⟨61719, by rfl⟩ : syracuseStep 164585 = 123439) B123439
theorem B164891 : Blo 107783 164891 := bstep (se 1 (by rfl) ⟨123668, by rfl⟩ : syracuseStep 164891 = 247337) B247337
theorem B525791 : Blo 107783 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B4655303 : Blo 107783 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B167195 : Blo 107783 167195 := bstep (se 1 (by rfl) ⟨125396, by rfl⟩ : syracuseStep 167195 = 250793) B250793
theorem B298495 : Blo 107783 298495 := bstep (se 1 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 298495 = 447743) B447743
theorem B167561 : Blo 107783 167561 := bstep (se 2 (by rfl) ⟨62835, by rfl⟩ : syracuseStep 167561 = 125671) B125671
theorem B366767 : Blo 107783 366767 := bstep (se 1 (by rfl) ⟨275075, by rfl⟩ : syracuseStep 366767 = 550151) B550151
theorem B1188047 : Blo 107783 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B696545 : Blo 107783 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B598913 : Blo 107783 598913 := bstep (se 2 (by rfl) ⟨224592, by rfl⟩ : syracuseStep 598913 = 449185) B449185
theorem B18097289 : Blo 107783 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B174239 : Blo 107783 174239 := bstep (se 1 (by rfl) ⟨130679, by rfl⟩ : syracuseStep 174239 = 261359) B261359
theorem B108991 : Blo 107783 108991 := bstep (se 1 (by rfl) ⟨81743, by rfl⟩ : syracuseStep 108991 = 163487) B163487
theorem B2075327 : Blo 107783 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B109295 : Blo 107783 109295 := bstep (se 1 (by rfl) ⟨81971, by rfl⟩ : syracuseStep 109295 = 163943) B163943
theorem B109671 : Blo 107783 109671 := bstep (se 1 (by rfl) ⟨82253, by rfl⟩ : syracuseStep 109671 = 164507) B164507
theorem B4566365 : Blo 107783 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1125827 : Blo 107783 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B110127 : Blo 107783 110127 := bstep (se 1 (by rfl) ⟨82595, by rfl⟩ : syracuseStep 110127 = 165191) B165191
theorem B5353253 : Blo 107783 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B110591 : Blo 107783 110591 := bstep (se 1 (by rfl) ⟨82943, by rfl⟩ : syracuseStep 110591 = 165887) B165887
theorem B274985 : Blo 107783 274985 := bstep (se 2 (by rfl) ⟨103119, by rfl⟩ : syracuseStep 274985 = 206239) B206239
theorem B275035 : Blo 107783 275035 := bstep (se 1 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 275035 = 412553) B412553
theorem B1880819 : Blo 107783 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B111551 : Blo 107783 111551 := bstep (se 1 (by rfl) ⟨83663, by rfl⟩ : syracuseStep 111551 = 167327) B167327
theorem B964327 : Blo 107783 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B802237 : Blo 107783 802237 := bstep (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) B300839
theorem B277951 : Blo 107783 277951 := bstep (se 1 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 277951 = 416927) B416927
theorem B507521 : Blo 107783 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B1196957 : Blo 107783 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B4212161 : Blo 107783 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B312923 : Blo 107783 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B411263 : Blo 107783 411263 := bstep (se 1 (by rfl) ⟨308447, by rfl⟩ : syracuseStep 411263 = 616895) B616895
theorem B706643 : Blo 107783 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B837863 : Blo 107783 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B3754511 : Blo 107783 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B249191 : Blo 107783 249191 := bstep (se 1 (by rfl) ⟨186893, by rfl⟩ : syracuseStep 249191 = 373787) B373787
theorem B184747 : Blo 107783 184747 := bstep (se 1 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 184747 = 277121) B277121
theorem B1627069 : Blo 107783 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B611819 : Blo 107783 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B1234925 : Blo 107783 1234925 := bstep (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) B463097
theorem B416137 : Blo 107783 416137 := bstep (se 2 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 416137 = 312103) B312103
theorem B318077 : Blo 107783 318077 := bstep (se 3 (by rfl) ⟨59639, by rfl⟩ : syracuseStep 318077 = 119279) B119279
theorem B547559 : Blo 107783 547559 := bstep (se 1 (by rfl) ⟨410669, by rfl⟩ : syracuseStep 547559 = 821339) B821339
theorem B253343 : Blo 107783 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B123007 : Blo 107783 123007 := bstep (se 1 (by rfl) ⟨92255, by rfl⟩ : syracuseStep 123007 = 184511) B184511
theorem B1597967 : Blo 107783 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B157567 : Blo 107783 157567 := bstep (se 1 (by rfl) ⟨118175, by rfl⟩ : syracuseStep 157567 = 236351) B236351
theorem B3402607 : Blo 107783 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B552095 : Blo 107783 552095 := bstep (se 1 (by rfl) ⟨414071, by rfl⟩ : syracuseStep 552095 = 828143) B828143
theorem B2781053 : Blo 107783 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B619559 : Blo 107783 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B587195 : Blo 107783 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B1767095 : Blo 107783 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B161705 : Blo 107783 161705 := bstep (se 2 (by rfl) ⟨60639, by rfl⟩ : syracuseStep 161705 = 121279) B121279
theorem B424187 : Blo 107783 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B10746917 : Blo 107783 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B164009 : Blo 107783 164009 := bstep (se 2 (by rfl) ⟨61503, by rfl⟩ : syracuseStep 164009 = 123007) B123007
theorem B558575 : Blo 107783 558575 := bstep (se 1 (by rfl) ⟨418931, by rfl⟩ : syracuseStep 558575 = 837863) B837863
theorem B166127 : Blo 107783 166127 := bstep (se 1 (by rfl) ⟨124595, by rfl⟩ : syracuseStep 166127 = 249191) B249191
theorem B823283 : Blo 107783 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B365039 : Blo 107783 365039 := bstep (se 1 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 365039 = 547559) B547559
theorem B397993 : Blo 107783 397993 := bstep (se 2 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 397993 = 298495) B298495
theorem B168895 : Blo 107783 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B792031 : Blo 107783 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B464363 : Blo 107783 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B399275 : Blo 107783 399275 := bstep (se 1 (by rfl) ⟨299456, by rfl⟩ : syracuseStep 399275 = 598913) B598913
theorem B12064859 : Blo 107783 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B366713 : Blo 107783 366713 := bstep (se 2 (by rfl) ⟨137517, by rfl⟩ : syracuseStep 366713 = 275035) B275035
theorem B2169425 : Blo 107783 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B1383551 : Blo 107783 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B368063 : Blo 107783 368063 := bstep (se 1 (by rfl) ⟨276047, by rfl⟩ : syracuseStep 368063 = 552095) B552095
theorem B1285769 : Blo 107783 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B1253879 : Blo 107783 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B107803 : Blo 107783 107803 := bstep (se 1 (by rfl) ⟨80852, by rfl⟩ : syracuseStep 107803 = 161705) B161705
theorem B370601 : Blo 107783 370601 := bstep (se 2 (by rfl) ⟨138975, by rfl⟩ : syracuseStep 370601 = 277951) B277951
theorem B338347 : Blo 107783 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B109375 : Blo 107783 109375 := bstep (se 1 (by rfl) ⟨82031, by rfl⟩ : syracuseStep 109375 = 164063) B164063
theorem B109439 : Blo 107783 109439 := bstep (se 1 (by rfl) ⟨82079, by rfl⟩ : syracuseStep 109439 = 164159) B164159
theorem B109551 : Blo 107783 109551 := bstep (se 1 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 109551 = 164327) B164327
theorem B109723 : Blo 107783 109723 := bstep (se 1 (by rfl) ⟨82292, by rfl⟩ : syracuseStep 109723 = 164585) B164585
theorem B797971 : Blo 107783 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B109927 : Blo 107783 109927 := bstep (se 1 (by rfl) ⟨82445, by rfl⟩ : syracuseStep 109927 = 164891) B164891
theorem B274175 : Blo 107783 274175 := bstep (se 1 (by rfl) ⟨205631, by rfl⟩ : syracuseStep 274175 = 411263) B411263
theorem B471095 : Blo 107783 471095 := bstep (se 1 (by rfl) ⟨353321, by rfl⟩ : syracuseStep 471095 = 706643) B706643
theorem B2503007 : Blo 107783 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B111463 : Blo 107783 111463 := bstep (se 1 (by rfl) ⟨83597, by rfl⟩ : syracuseStep 111463 = 167195) B167195
theorem B111707 : Blo 107783 111707 := bstep (se 1 (by rfl) ⟨83780, by rfl⟩ : syracuseStep 111707 = 167561) B167561
theorem B210089 : Blo 107783 210089 := bstep (se 2 (by rfl) ⟨78783, by rfl⟩ : syracuseStep 210089 = 157567) B157567
theorem B407879 : Blo 107783 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B4536809 : Blo 107783 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B244511 : Blo 107783 244511 := bstep (se 1 (by rfl) ⟨183383, by rfl⟩ : syracuseStep 244511 = 366767) B366767
theorem B834461 : Blo 107783 834461 := bstep (se 3 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 834461 = 312923) B312923
theorem B212051 : Blo 107783 212051 := bstep (se 1 (by rfl) ⟨159038, by rfl⟩ : syracuseStep 212051 = 318077) B318077
theorem B1065311 : Blo 107783 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B246329 : Blo 107783 246329 := bstep (se 2 (by rfl) ⟨92373, by rfl⟩ : syracuseStep 246329 = 184747) B184747
theorem B116159 : Blo 107783 116159 := bstep (se 1 (by rfl) ⟨87119, by rfl⟩ : syracuseStep 116159 = 174239) B174239
theorem B1854035 : Blo 107783 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B183323 : Blo 107783 183323 := bstep (se 1 (by rfl) ⟨137492, by rfl⟩ : syracuseStep 183323 = 274985) B274985
theorem B413039 : Blo 107783 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B282791 : Blo 107783 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B1069649 : Blo 107783 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B7164611 : Blo 107783 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B2808107 : Blo 107783 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B3103535 : Blo 107783 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B1402109 : Blo 107783 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B3044243 : Blo 107783 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B750551 : Blo 107783 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B3568835 : Blo 107783 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B554849 : Blo 107783 554849 := bstep (se 2 (by rfl) ⟨208068, by rfl⟩ : syracuseStep 554849 = 416137) B416137
theorem B391463 : Blo 107783 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B1178063 : Blo 107783 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B164219 : Blo 107783 164219 := bstep (se 1 (by rfl) ⟨123164, by rfl⟩ : syracuseStep 164219 = 246329) B246329
theorem B1804517 : Blo 107783 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B266183 : Blo 107783 266183 := bstep (se 1 (by rfl) ⟨199637, by rfl⟩ : syracuseStep 266183 = 399275) B399275
theorem B1872071 : Blo 107783 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B1446283 : Blo 107783 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B2069023 : Blo 107783 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B922367 : Blo 107783 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B857179 : Blo 107783 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B530657 : Blo 107783 530657 := bstep (se 2 (by rfl) ⟨198996, by rfl⟩ : syracuseStep 530657 = 397993) B397993
theorem B1056041 : Blo 107783 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B140059 : Blo 107783 140059 := bstep (se 1 (by rfl) ⟨105044, by rfl⟩ : syracuseStep 140059 = 210089) B210089
theorem B369899 : Blo 107783 369899 := bstep (se 1 (by rfl) ⟨277424, by rfl⟩ : syracuseStep 369899 = 554849) B554849
theorem B271919 : Blo 107783 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B3024539 : Blo 107783 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B141367 : Blo 107783 141367 := bstep (se 1 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 141367 = 212051) B212051
theorem B8005877 : Blo 107783 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B109339 : Blo 107783 109339 := bstep (se 1 (by rfl) ⟨82004, by rfl⟩ : syracuseStep 109339 = 164009) B164009
theorem B372383 : Blo 107783 372383 := bstep (se 1 (by rfl) ⟨279287, by rfl⟩ : syracuseStep 372383 = 558575) B558575
theorem B110751 : Blo 107783 110751 := bstep (se 1 (by rfl) ⟨83063, by rfl⟩ : syracuseStep 110751 = 166127) B166127
theorem B275359 : Blo 107783 275359 := bstep (se 1 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 275359 = 413039) B413039
theorem B243359 : Blo 107783 243359 := bstep (se 1 (by rfl) ⟨182519, by rfl⟩ : syracuseStep 243359 = 365039) B365039
theorem B309575 : Blo 107783 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B309757 : Blo 107783 309757 := bstep (se 3 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 309757 = 116159) B116159
theorem B8043239 : Blo 107783 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B244475 : Blo 107783 244475 := bstep (se 1 (by rfl) ⟨183356, by rfl⟩ : syracuseStep 244475 = 366713) B366713
theorem B1063961 : Blo 107783 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B245375 : Blo 107783 245375 := bstep (se 1 (by rfl) ⟨184031, by rfl⟩ : syracuseStep 245375 = 368063) B368063
theorem B835919 : Blo 107783 835919 := bstep (se 1 (by rfl) ⟨626939, by rfl⟩ : syracuseStep 835919 = 1253879) B1253879
theorem B934739 : Blo 107783 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B247067 : Blo 107783 247067 := bstep (se 1 (by rfl) ⟨185300, by rfl⟩ : syracuseStep 247067 = 370601) B370601
theorem B182783 : Blo 107783 182783 := bstep (se 1 (by rfl) ⟨137087, by rfl⟩ : syracuseStep 182783 = 274175) B274175
theorem B314063 : Blo 107783 314063 := bstep (se 1 (by rfl) ⟨235547, by rfl⟩ : syracuseStep 314063 = 471095) B471095
theorem B2379223 : Blo 107783 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B710207 : Blo 107783 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B1236023 : Blo 107783 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B122215 : Blo 107783 122215 := bstep (se 1 (by rfl) ⟨91661, by rfl⟩ : syracuseStep 122215 = 183323) B183323
theorem B548855 : Blo 107783 548855 := bstep (se 1 (by rfl) ⟨411641, by rfl⟩ : syracuseStep 548855 = 823283) B823283
theorem B188527 : Blo 107783 188527 := bstep (se 1 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 188527 = 282791) B282791
theorem B713099 : Blo 107783 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B4776407 : Blo 107783 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B225193 : Blo 107783 225193 := bstep (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) B168895
theorem B1668671 : Blo 107783 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B2029495 : Blo 107783 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B260975 : Blo 107783 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B785375 : Blo 107783 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B163007 : Blo 107783 163007 := bstep (se 1 (by rfl) ⟨122255, by rfl⟩ : syracuseStep 163007 = 244511) B244511
theorem B556307 : Blo 107783 556307 := bstep (se 1 (by rfl) ⟨417230, by rfl⟩ : syracuseStep 556307 = 834461) B834461
theorem B557279 : Blo 107783 557279 := bstep (se 1 (by rfl) ⟨417959, by rfl⟩ : syracuseStep 557279 = 835919) B835919
theorem B623159 : Blo 107783 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B164711 : Blo 107783 164711 := bstep (se 1 (by rfl) ⟨123533, by rfl⟩ : syracuseStep 164711 = 247067) B247067
theorem B1248047 : Blo 107783 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B725117 : Blo 107783 725117 := bstep (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) B271919
theorem B824015 : Blo 107783 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B300257 : Blo 107783 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B365903 : Blo 107783 365903 := bstep (se 1 (by rfl) ⟨274427, by rfl⟩ : syracuseStep 365903 = 548855) B548855
theorem B3184271 : Blo 107783 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B2758697 : Blo 107783 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B367145 : Blo 107783 367145 := bstep (se 2 (by rfl) ⟨137679, by rfl⟩ : syracuseStep 367145 = 275359) B275359
theorem B206383 : Blo 107783 206383 := bstep (se 1 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 206383 = 309575) B309575
theorem B173983 : Blo 107783 173983 := bstep (se 1 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 173983 = 260975) B260975
theorem B108671 : Blo 107783 108671 := bstep (se 1 (by rfl) ⟨81503, by rfl⟩ : syracuseStep 108671 = 163007) B163007
theorem B370871 : Blo 107783 370871 := bstep (se 1 (by rfl) ⟨278153, by rfl⟩ : syracuseStep 370871 = 556307) B556307
theorem B109479 : Blo 107783 109479 := bstep (se 1 (by rfl) ⟨82109, by rfl⟩ : syracuseStep 109479 = 164219) B164219
theorem B209375 : Blo 107783 209375 := bstep (se 1 (by rfl) ⟨157031, by rfl⟩ : syracuseStep 209375 = 314063) B314063
theorem B177455 : Blo 107783 177455 := bstep (se 1 (by rfl) ⟨133091, by rfl⟩ : syracuseStep 177455 = 266183) B266183
theorem B473471 : Blo 107783 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B704027 : Blo 107783 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B475399 : Blo 107783 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B246599 : Blo 107783 246599 := bstep (se 1 (by rfl) ⟨184949, by rfl⟩ : syracuseStep 246599 = 369899) B369899
theorem B2016359 : Blo 107783 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B248255 : Blo 107783 248255 := bstep (se 1 (by rfl) ⟨186191, by rfl⟩ : syracuseStep 248255 = 372383) B372383
theorem B2705993 : Blo 107783 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B413009 : Blo 107783 413009 := bstep (se 2 (by rfl) ⟨154878, by rfl⟩ : syracuseStep 413009 = 309757) B309757
theorem B5362159 : Blo 107783 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B709307 : Blo 107783 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B251369 : Blo 107783 251369 := bstep (se 2 (by rfl) ⟨94263, by rfl⟩ : syracuseStep 251369 = 188527) B188527
theorem B186745 : Blo 107783 186745 := bstep (se 2 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 186745 = 140059) B140059
theorem B1203011 : Blo 107783 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B121855 : Blo 107783 121855 := bstep (se 1 (by rfl) ⟨91391, by rfl⟩ : syracuseStep 121855 = 182783) B182783
theorem B188489 : Blo 107783 188489 := bstep (se 2 (by rfl) ⟨70683, by rfl⟩ : syracuseStep 188489 = 141367) B141367
theorem B614911 : Blo 107783 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B353771 : Blo 107783 353771 := bstep (se 1 (by rfl) ⟨265328, by rfl⟩ : syracuseStep 353771 = 530657) B530657
theorem B3172297 : Blo 107783 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B1928377 : Blo 107783 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B1142905 : Blo 107783 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B5337251 : Blo 107783 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B1112447 : Blo 107783 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B162239 : Blo 107783 162239 := bstep (se 1 (by rfl) ⟨121679, by rfl⟩ : syracuseStep 162239 = 243359) B243359
theorem B162953 : Blo 107783 162953 := bstep (se 2 (by rfl) ⟨61107, by rfl⟩ : syracuseStep 162953 = 122215) B122215
theorem B162983 : Blo 107783 162983 := bstep (se 1 (by rfl) ⟨122237, by rfl⟩ : syracuseStep 162983 = 244475) B244475
theorem B523583 : Blo 107783 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B163583 : Blo 107783 163583 := bstep (se 1 (by rfl) ⟨122687, by rfl⟩ : syracuseStep 163583 = 245375) B245375
theorem B1933645 : Blo 107783 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B164399 : Blo 107783 164399 := bstep (se 1 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 164399 = 246599) B246599
theorem B819881 : Blo 107783 819881 := bstep (se 2 (by rfl) ⟨307455, by rfl⟩ : syracuseStep 819881 = 614911) B614911
theorem B1344239 : Blo 107783 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B165503 : Blo 107783 165503 := bstep (se 1 (by rfl) ⟨124127, by rfl⟩ : syracuseStep 165503 = 248255) B248255
theorem B1803995 : Blo 107783 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B231977 : Blo 107783 231977 := bstep (se 2 (by rfl) ⟨86991, by rfl⟩ : syracuseStep 231977 = 173983) B173983
theorem B4229729 : Blo 107783 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B200171 : Blo 107783 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B167579 : Blo 107783 167579 := bstep (se 1 (by rfl) ⟨125684, by rfl⟩ : syracuseStep 167579 = 251369) B251369
theorem B1839131 : Blo 107783 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B7149545 : Blo 107783 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B235847 : Blo 107783 235847 := bstep (se 1 (by rfl) ⟨176885, by rfl⟩ : syracuseStep 235847 = 353771) B353771
theorem B139583 : Blo 107783 139583 := bstep (se 1 (by rfl) ⟨104687, by rfl⟩ : syracuseStep 139583 = 209375) B209375
theorem B108159 : Blo 107783 108159 := bstep (se 1 (by rfl) ⟨81119, by rfl⟩ : syracuseStep 108159 = 162239) B162239
theorem B108635 : Blo 107783 108635 := bstep (se 1 (by rfl) ⟨81476, by rfl⟩ : syracuseStep 108635 = 162953) B162953
theorem B108655 : Blo 107783 108655 := bstep (se 1 (by rfl) ⟨81491, by rfl⟩ : syracuseStep 108655 = 162983) B162983
theorem B469351 : Blo 107783 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B109055 : Blo 107783 109055 := bstep (se 1 (by rfl) ⟨81791, by rfl⟩ : syracuseStep 109055 = 163583) B163583
theorem B371519 : Blo 107783 371519 := bstep (se 1 (by rfl) ⟨278639, by rfl⟩ : syracuseStep 371519 = 557279) B557279
theorem B633865 : Blo 107783 633865 := bstep (se 2 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 633865 = 475399) B475399
theorem B109807 : Blo 107783 109807 := bstep (se 1 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 109807 = 164711) B164711
theorem B832031 : Blo 107783 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B275177 : Blo 107783 275177 := bstep (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) B206383
theorem B275339 : Blo 107783 275339 := bstep (se 1 (by rfl) ⟨206504, by rfl⟩ : syracuseStep 275339 = 413009) B413009
theorem B472871 : Blo 107783 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B243935 : Blo 107783 243935 := bstep (se 1 (by rfl) ⟨182951, by rfl⟩ : syracuseStep 243935 = 365903) B365903
theorem B244763 : Blo 107783 244763 := bstep (se 1 (by rfl) ⟨183572, by rfl⟩ : syracuseStep 244763 = 367145) B367145
theorem B802007 : Blo 107783 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B1523873 : Blo 107783 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B247247 : Blo 107783 247247 := bstep (se 1 (by rfl) ⟨185435, by rfl⟩ : syracuseStep 247247 = 370871) B370871
theorem B3558167 : Blo 107783 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B248993 : Blo 107783 248993 := bstep (se 2 (by rfl) ⟨93372, by rfl⟩ : syracuseStep 248993 = 186745) B186745
theorem B118303 : Blo 107783 118303 := bstep (se 1 (by rfl) ⟨88727, by rfl⟩ : syracuseStep 118303 = 177455) B177455
theorem B741631 : Blo 107783 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B315647 : Blo 107783 315647 := bstep (se 1 (by rfl) ⟨236735, by rfl⟩ : syracuseStep 315647 = 473471) B473471
theorem B349055 : Blo 107783 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B415439 : Blo 107783 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B549343 : Blo 107783 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B2122847 : Blo 107783 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B125659 : Blo 107783 125659 := bstep (se 1 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 125659 = 188489) B188489
theorem B10284677 : Blo 107783 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B162473 : Blo 107783 162473 := bstep (se 2 (by rfl) ⟨60927, by rfl⟩ : syracuseStep 162473 = 121855) B121855
theorem B1015915 : Blo 107783 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B164831 : Blo 107783 164831 := bstep (se 1 (by rfl) ⟨123623, by rfl⟩ : syracuseStep 164831 = 247247) B247247
theorem B2819819 : Blo 107783 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B165995 : Blo 107783 165995 := bstep (se 1 (by rfl) ⟨124496, by rfl⟩ : syracuseStep 165995 = 248993) B248993
theorem B625801 : Blo 107783 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B232703 : Blo 107783 232703 := bstep (se 1 (by rfl) ⟨174527, by rfl⟩ : syracuseStep 232703 = 349055) B349055
theorem B167545 : Blo 107783 167545 := bstep (se 2 (by rfl) ⟨62829, by rfl⟩ : syracuseStep 167545 = 125659) B125659
theorem B988841 : Blo 107783 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B1415231 : Blo 107783 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B6856451 : Blo 107783 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B630949 : Blo 107783 630949 := bstep (se 4 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 630949 = 118303) B118303
theorem B533789 : Blo 107783 533789 := bstep (se 3 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 533789 = 200171) B200171
theorem B108315 : Blo 107783 108315 := bstep (se 1 (by rfl) ⟨81236, by rfl⟩ : syracuseStep 108315 = 162473) B162473
theorem B534671 : Blo 107783 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B109599 : Blo 107783 109599 := bstep (se 1 (by rfl) ⟨82199, by rfl⟩ : syracuseStep 109599 = 164399) B164399
theorem B896159 : Blo 107783 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B372221 : Blo 107783 372221 := bstep (se 3 (by rfl) ⟨69791, by rfl⟩ : syracuseStep 372221 = 139583) B139583
theorem B110335 : Blo 107783 110335 := bstep (se 1 (by rfl) ⟨82751, by rfl⟩ : syracuseStep 110335 = 165503) B165503
theorem B2372111 : Blo 107783 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B111719 : Blo 107783 111719 := bstep (se 1 (by rfl) ⟨83789, by rfl⟩ : syracuseStep 111719 = 167579) B167579
theorem B2929829 : Blo 107783 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B1226087 : Blo 107783 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B210431 : Blo 107783 210431 := bstep (se 1 (by rfl) ⟨157823, by rfl⟩ : syracuseStep 210431 = 315647) B315647
theorem B276959 : Blo 107783 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B4766363 : Blo 107783 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B247679 : Blo 107783 247679 := bstep (se 1 (by rfl) ⟨185759, by rfl⟩ : syracuseStep 247679 = 371519) B371519
theorem B183451 : Blo 107783 183451 := bstep (se 1 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 183451 = 275177) B275177
theorem B183559 : Blo 107783 183559 := bstep (se 1 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 183559 = 275339) B275339
theorem B315247 : Blo 107783 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B2578193 : Blo 107783 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B546587 : Blo 107783 546587 := bstep (se 1 (by rfl) ⟨409940, by rfl⟩ : syracuseStep 546587 = 819881) B819881
theorem B1202663 : Blo 107783 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B154651 : Blo 107783 154651 := bstep (se 1 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 154651 = 231977) B231977
theorem B845153 : Blo 107783 845153 := bstep (se 2 (by rfl) ⟨316932, by rfl⟩ : syracuseStep 845153 = 633865) B633865
theorem B157231 : Blo 107783 157231 := bstep (se 1 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 157231 = 235847) B235847
theorem B554687 : Blo 107783 554687 := bstep (se 1 (by rfl) ⟨416015, by rfl⟩ : syracuseStep 554687 = 832031) B832031
theorem B162623 : Blo 107783 162623 := bstep (se 1 (by rfl) ⟨121967, by rfl⟩ : syracuseStep 162623 = 243935) B243935
theorem B163175 : Blo 107783 163175 := bstep (se 1 (by rfl) ⟨122381, by rfl⟩ : syracuseStep 163175 = 244763) B244763
theorem B165119 : Blo 107783 165119 := bstep (se 1 (by rfl) ⟨123839, by rfl⟩ : syracuseStep 165119 = 247679) B247679
theorem B659227 : Blo 107783 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B364391 : Blo 107783 364391 := bstep (se 1 (by rfl) ⟨273293, by rfl⟩ : syracuseStep 364391 = 546587) B546587
theorem B563435 : Blo 107783 563435 := bstep (se 1 (by rfl) ⟨422576, by rfl⟩ : syracuseStep 563435 = 845153) B845153
theorem B597439 : Blo 107783 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B1581407 : Blo 107783 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B140287 : Blo 107783 140287 := bstep (se 1 (by rfl) ⟨105215, by rfl⟩ : syracuseStep 140287 = 210431) B210431
theorem B369791 : Blo 107783 369791 := bstep (se 1 (by rfl) ⟨277343, by rfl⟩ : syracuseStep 369791 = 554687) B554687
theorem B206201 : Blo 107783 206201 := bstep (se 2 (by rfl) ⟨77325, by rfl⟩ : syracuseStep 206201 = 154651) B154651
theorem B108415 : Blo 107783 108415 := bstep (se 1 (by rfl) ⟨81311, by rfl⟩ : syracuseStep 108415 = 162623) B162623
theorem B108783 : Blo 107783 108783 := bstep (se 1 (by rfl) ⟨81587, by rfl⟩ : syracuseStep 108783 = 163175) B163175
theorem B1354553 : Blo 107783 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B109887 : Blo 107783 109887 := bstep (se 1 (by rfl) ⟨82415, by rfl⟩ : syracuseStep 109887 = 164831) B164831
theorem B110663 : Blo 107783 110663 := bstep (se 1 (by rfl) ⟨82997, by rfl⟩ : syracuseStep 110663 = 165995) B165995
theorem B209641 : Blo 107783 209641 := bstep (se 2 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 209641 = 157231) B157231
theorem B7812877 : Blo 107783 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B1718795 : Blo 107783 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B834401 : Blo 107783 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B244601 : Blo 107783 244601 := bstep (se 2 (by rfl) ⟨91725, by rfl⟩ : syracuseStep 244601 = 183451) B183451
theorem B801775 : Blo 107783 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B244745 : Blo 107783 244745 := bstep (se 2 (by rfl) ⟨91779, by rfl⟩ : syracuseStep 244745 = 183559) B183559
theorem B7519517 : Blo 107783 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B4570967 : Blo 107783 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B248147 : Blo 107783 248147 := bstep (se 1 (by rfl) ⟨186110, by rfl⟩ : syracuseStep 248147 = 372221) B372221
theorem B184639 : Blo 107783 184639 := bstep (se 1 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 184639 = 276959) B276959
theorem B841265 : Blo 107783 841265 := bstep (se 2 (by rfl) ⟨315474, by rfl⟩ : syracuseStep 841265 = 630949) B630949
theorem B155135 : Blo 107783 155135 := bstep (se 1 (by rfl) ⟨116351, by rfl⟩ : syracuseStep 155135 = 232703) B232703
theorem B943487 : Blo 107783 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B223393 : Blo 107783 223393 := bstep (se 2 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 223393 = 167545) B167545
theorem B420329 : Blo 107783 420329 := bstep (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) B315247
theorem B355859 : Blo 107783 355859 := bstep (se 1 (by rfl) ⟨266894, by rfl⟩ : syracuseStep 355859 = 533789) B533789
theorem B356447 : Blo 107783 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B817391 : Blo 107783 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B3177575 : Blo 107783 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B950525 : Blo 107783 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B165431 : Blo 107783 165431 := bstep (se 1 (by rfl) ⟨124073, by rfl⟩ : syracuseStep 165431 = 248147) B248147
theorem B297857 : Blo 107783 297857 := bstep (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) B223393
theorem B560843 : Blo 107783 560843 := bstep (se 1 (by rfl) ⟨420632, by rfl⟩ : syracuseStep 560843 = 841265) B841265
theorem B1054271 : Blo 107783 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B137467 : Blo 107783 137467 := bstep (se 1 (by rfl) ⟨103100, by rfl⟩ : syracuseStep 137467 = 206201) B206201
theorem B628991 : Blo 107783 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B3186341 : Blo 107783 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B237239 : Blo 107783 237239 := bstep (se 1 (by rfl) ⟨177929, by rfl⟩ : syracuseStep 237239 = 355859) B355859
theorem B110079 : Blo 107783 110079 := bstep (se 1 (by rfl) ⟨82559, by rfl⟩ : syracuseStep 110079 = 165119) B165119
theorem B242927 : Blo 107783 242927 := bstep (se 1 (by rfl) ⟨182195, by rfl⟩ : syracuseStep 242927 = 364391) B364391
theorem B375623 : Blo 107783 375623 := bstep (se 1 (by rfl) ⟨281717, by rfl⟩ : syracuseStep 375623 = 563435) B563435
theorem B246185 : Blo 107783 246185 := bstep (se 2 (by rfl) ⟨92319, by rfl⟩ : syracuseStep 246185 = 184639) B184639
theorem B2179709 : Blo 107783 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B246527 : Blo 107783 246527 := bstep (se 1 (by rfl) ⟨184895, by rfl⟩ : syracuseStep 246527 = 369791) B369791
theorem B279521 : Blo 107783 279521 := bstep (se 2 (by rfl) ⟨104820, by rfl⟩ : syracuseStep 279521 = 209641) B209641
theorem B280219 : Blo 107783 280219 := bstep (se 1 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 280219 = 420329) B420329
theorem B903035 : Blo 107783 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1069033 : Blo 107783 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B413693 : Blo 107783 413693 := bstep (se 3 (by rfl) ⟨77567, by rfl⟩ : syracuseStep 413693 = 155135) B155135
theorem B2118383 : Blo 107783 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B187049 : Blo 107783 187049 := bstep (se 2 (by rfl) ⟨70143, by rfl⟩ : syracuseStep 187049 = 140287) B140287
theorem B878969 : Blo 107783 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B2225069 : Blo 107783 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B10417169 : Blo 107783 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B1145863 : Blo 107783 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B163067 : Blo 107783 163067 := bstep (se 1 (by rfl) ⟨122300, by rfl⟩ : syracuseStep 163067 = 244601) B244601
theorem B163163 : Blo 107783 163163 := bstep (se 1 (by rfl) ⟨122372, by rfl⟩ : syracuseStep 163163 = 244745) B244745
theorem B5013011 : Blo 107783 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B3047311 : Blo 107783 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B164123 : Blo 107783 164123 := bstep (se 1 (by rfl) ⟨123092, by rfl⟩ : syracuseStep 164123 = 246185) B246185
theorem B164351 : Blo 107783 164351 := bstep (se 1 (by rfl) ⟨123263, by rfl⟩ : syracuseStep 164351 = 246527) B246527
theorem B198571 : Blo 107783 198571 := bstep (se 1 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 198571 = 297857) B297857
theorem B1412255 : Blo 107783 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1483379 : Blo 107783 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B108711 : Blo 107783 108711 := bstep (se 1 (by rfl) ⟨81533, by rfl⟩ : syracuseStep 108711 = 163067) B163067
theorem B108775 : Blo 107783 108775 := bstep (se 1 (by rfl) ⟨81581, by rfl⟩ : syracuseStep 108775 = 163163) B163163
theorem B633683 : Blo 107783 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B1453139 : Blo 107783 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B110287 : Blo 107783 110287 := bstep (se 1 (by rfl) ⟨82715, by rfl⟩ : syracuseStep 110287 = 165431) B165431
theorem B373625 : Blo 107783 373625 := bstep (se 2 (by rfl) ⟨140109, by rfl⟩ : syracuseStep 373625 = 280219) B280219
theorem B373895 : Blo 107783 373895 := bstep (se 1 (by rfl) ⟨280421, by rfl⟩ : syracuseStep 373895 = 560843) B560843
theorem B275795 : Blo 107783 275795 := bstep (se 1 (by rfl) ⟨206846, by rfl⟩ : syracuseStep 275795 = 413693) B413693
theorem B702847 : Blo 107783 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B2408093 : Blo 107783 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B1425377 : Blo 107783 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B2343917 : Blo 107783 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B183289 : Blo 107783 183289 := bstep (se 2 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 183289 = 137467) B137467
theorem B1527817 : Blo 107783 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B250415 : Blo 107783 250415 := bstep (se 1 (by rfl) ⟨187811, by rfl⟩ : syracuseStep 250415 = 375623) B375623
theorem B186347 : Blo 107783 186347 := bstep (se 1 (by rfl) ⟨139760, by rfl⟩ : syracuseStep 186347 = 279521) B279521
theorem B419327 : Blo 107783 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B124699 : Blo 107783 124699 := bstep (se 1 (by rfl) ⟨93524, by rfl⟩ : syracuseStep 124699 = 187049) B187049
theorem B2124227 : Blo 107783 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B158159 : Blo 107783 158159 := bstep (se 1 (by rfl) ⟨118619, by rfl⟩ : syracuseStep 158159 = 237239) B237239
theorem B6944779 : Blo 107783 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B161951 : Blo 107783 161951 := bstep (se 1 (by rfl) ⟨121463, by rfl⟩ : syracuseStep 161951 = 242927) B242927
theorem B3342007 : Blo 107783 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B4063081 : Blo 107783 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B166265 : Blo 107783 166265 := bstep (se 2 (by rfl) ⟨62349, by rfl⟩ : syracuseStep 166265 = 124699) B124699
theorem B264761 : Blo 107783 264761 := bstep (se 2 (by rfl) ⟨99285, by rfl⟩ : syracuseStep 264761 = 198571) B198571
theorem B166943 : Blo 107783 166943 := bstep (se 1 (by rfl) ⟨125207, by rfl⟩ : syracuseStep 166943 = 250415) B250415
theorem B2037089 : Blo 107783 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B988919 : Blo 107783 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1416151 : Blo 107783 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B107967 : Blo 107783 107967 := bstep (se 1 (by rfl) ⟨80975, by rfl⟩ : syracuseStep 107967 = 161951) B161951
theorem B5417441 : Blo 107783 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B109415 : Blo 107783 109415 := bstep (se 1 (by rfl) ⟨82061, by rfl⟩ : syracuseStep 109415 = 164123) B164123
theorem B109567 : Blo 107783 109567 := bstep (se 1 (by rfl) ⟨82175, by rfl⟩ : syracuseStep 109567 = 164351) B164351
theorem B244385 : Blo 107783 244385 := bstep (se 2 (by rfl) ⟨91644, by rfl⟩ : syracuseStep 244385 = 183289) B183289
theorem B279551 : Blo 107783 279551 := bstep (se 1 (by rfl) ⟨209663, by rfl⟩ : syracuseStep 279551 = 419327) B419327
theorem B968759 : Blo 107783 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B9259705 : Blo 107783 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B937129 : Blo 107783 937129 := bstep (se 2 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 937129 = 702847) B702847
theorem B249083 : Blo 107783 249083 := bstep (se 1 (by rfl) ⟨186812, by rfl⟩ : syracuseStep 249083 = 373625) B373625
theorem B249263 : Blo 107783 249263 := bstep (se 1 (by rfl) ⟨186947, by rfl⟩ : syracuseStep 249263 = 373895) B373895
theorem B183863 : Blo 107783 183863 := bstep (se 1 (by rfl) ⟨137897, by rfl⟩ : syracuseStep 183863 = 275795) B275795
theorem B1562611 : Blo 107783 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B941503 : Blo 107783 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B124231 : Blo 107783 124231 := bstep (se 1 (by rfl) ⟨93173, by rfl⟩ : syracuseStep 124231 = 186347) B186347
theorem B421757 : Blo 107783 421757 := bstep (se 3 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 421757 = 158159) B158159
theorem B422455 : Blo 107783 422455 := bstep (se 1 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 422455 = 633683) B633683
theorem B4456009 : Blo 107783 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B1605395 : Blo 107783 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B950251 : Blo 107783 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B165641 : Blo 107783 165641 := bstep (se 2 (by rfl) ⟨62115, by rfl⟩ : syracuseStep 165641 = 124231) B124231
theorem B166055 : Blo 107783 166055 := bstep (se 1 (by rfl) ⟨124541, by rfl⟩ : syracuseStep 166055 = 249083) B249083
theorem B166175 : Blo 107783 166175 := bstep (se 1 (by rfl) ⟨124631, by rfl⟩ : syracuseStep 166175 = 249263) B249263
theorem B659279 : Blo 107783 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B1249505 : Blo 107783 1249505 := bstep (se 2 (by rfl) ⟨468564, by rfl⟩ : syracuseStep 1249505 = 937129) B937129
theorem B563273 : Blo 107783 563273 := bstep (se 2 (by rfl) ⟨211227, by rfl⟩ : syracuseStep 563273 = 422455) B422455
theorem B3611627 : Blo 107783 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B1255337 : Blo 107783 1255337 := bstep (se 2 (by rfl) ⟨470751, by rfl⟩ : syracuseStep 1255337 = 941503) B941503
theorem B5941345 : Blo 107783 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B110843 : Blo 107783 110843 := bstep (se 1 (by rfl) ⟨83132, by rfl⟩ : syracuseStep 110843 = 166265) B166265
theorem B176507 : Blo 107783 176507 := bstep (se 1 (by rfl) ⟨132380, by rfl⟩ : syracuseStep 176507 = 264761) B264761
theorem B111295 : Blo 107783 111295 := bstep (se 1 (by rfl) ⟨83471, by rfl⟩ : syracuseStep 111295 = 166943) B166943
theorem B1358059 : Blo 107783 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B281171 : Blo 107783 281171 := bstep (se 1 (by rfl) ⟨210878, by rfl⟩ : syracuseStep 281171 = 421757) B421757
theorem B2083481 : Blo 107783 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1888201 : Blo 107783 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1070263 : Blo 107783 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B1267001 : Blo 107783 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B186367 : Blo 107783 186367 := bstep (se 1 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 186367 = 279551) B279551
theorem B645839 : Blo 107783 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B122575 : Blo 107783 122575 := bstep (se 1 (by rfl) ⟨91931, by rfl⟩ : syracuseStep 122575 = 183863) B183863
theorem B12346273 : Blo 107783 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B162923 : Blo 107783 162923 := bstep (se 1 (by rfl) ⟨122192, by rfl⟩ : syracuseStep 162923 = 244385) B244385
theorem B430559 : Blo 107783 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B1810745 : Blo 107783 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B108615 : Blo 107783 108615 := bstep (se 1 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 108615 = 162923) B162923
theorem B110427 : Blo 107783 110427 := bstep (se 1 (by rfl) ⟨82820, by rfl⟩ : syracuseStep 110427 = 165641) B165641
theorem B110703 : Blo 107783 110703 := bstep (se 1 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 110703 = 166055) B166055
theorem B110783 : Blo 107783 110783 := bstep (se 1 (by rfl) ⟨83087, by rfl⟩ : syracuseStep 110783 = 166175) B166175
theorem B1388987 : Blo 107783 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B439519 : Blo 107783 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B833003 : Blo 107783 833003 := bstep (se 1 (by rfl) ⟨624752, by rfl⟩ : syracuseStep 833003 = 1249505) B1249505
theorem B375515 : Blo 107783 375515 := bstep (se 1 (by rfl) ⟨281636, by rfl⟩ : syracuseStep 375515 = 563273) B563273
theorem B2407751 : Blo 107783 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B65846789 : Blo 107783 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B836891 : Blo 107783 836891 := bstep (se 1 (by rfl) ⟨627668, by rfl⟩ : syracuseStep 836891 = 1255337) B1255337
theorem B1427017 : Blo 107783 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B248489 : Blo 107783 248489 := bstep (se 2 (by rfl) ⟨93183, by rfl⟩ : syracuseStep 248489 = 186367) B186367
theorem B117671 : Blo 107783 117671 := bstep (se 1 (by rfl) ⟨88253, by rfl⟩ : syracuseStep 117671 = 176507) B176507
theorem B187447 : Blo 107783 187447 := bstep (se 1 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 187447 = 281171) B281171
theorem B7921793 : Blo 107783 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B844667 : Blo 107783 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B2517601 : Blo 107783 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B163433 : Blo 107783 163433 := bstep (se 2 (by rfl) ⟨61287, by rfl⟩ : syracuseStep 163433 = 122575) B122575
theorem B557927 : Blo 107783 557927 := bstep (se 1 (by rfl) ⟨418445, by rfl⟩ : syracuseStep 557927 = 836891) B836891
theorem B165659 : Blo 107783 165659 := bstep (se 1 (by rfl) ⟨124244, by rfl⟩ : syracuseStep 165659 = 248489) B248489
theorem B1902689 : Blo 107783 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B5281195 : Blo 107783 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B563111 : Blo 107783 563111 := bstep (se 1 (by rfl) ⟨422333, by rfl⟩ : syracuseStep 563111 = 844667) B844667
theorem B925991 : Blo 107783 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B108955 : Blo 107783 108955 := bstep (se 1 (by rfl) ⟨81716, by rfl⟩ : syracuseStep 108955 = 163433) B163433
theorem B3356801 : Blo 107783 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B313789 : Blo 107783 313789 := bstep (se 3 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 313789 = 117671) B117671
theorem B249929 : Blo 107783 249929 := bstep (se 2 (by rfl) ⟨93723, by rfl⟩ : syracuseStep 249929 = 187447) B187447
theorem B250343 : Blo 107783 250343 := bstep (se 1 (by rfl) ⟨187757, by rfl⟩ : syracuseStep 250343 = 375515) B375515
theorem B43897859 : Blo 107783 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B287039 : Blo 107783 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B1207163 : Blo 107783 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B586025 : Blo 107783 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B555335 : Blo 107783 555335 := bstep (se 1 (by rfl) ⟨416501, by rfl⟩ : syracuseStep 555335 = 833003) B833003
theorem B1605167 : Blo 107783 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B166619 : Blo 107783 166619 := bstep (se 1 (by rfl) ⟨124964, by rfl⟩ : syracuseStep 166619 = 249929) B249929
theorem B166895 : Blo 107783 166895 := bstep (se 1 (by rfl) ⟨125171, by rfl⟩ : syracuseStep 166895 = 250343) B250343
theorem B29265239 : Blo 107783 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B2237867 : Blo 107783 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B370223 : Blo 107783 370223 := bstep (se 1 (by rfl) ⟨277667, by rfl⟩ : syracuseStep 370223 = 555335) B555335
theorem B371951 : Blo 107783 371951 := bstep (se 1 (by rfl) ⟨278963, by rfl⟩ : syracuseStep 371951 = 557927) B557927
theorem B110439 : Blo 107783 110439 := bstep (se 1 (by rfl) ⟨82829, by rfl⟩ : syracuseStep 110439 = 165659) B165659
theorem B375407 : Blo 107783 375407 := bstep (se 1 (by rfl) ⟨281555, by rfl⟩ : syracuseStep 375407 = 563111) B563111
theorem B804775 : Blo 107783 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B1070111 : Blo 107783 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1268459 : Blo 107783 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B418385 : Blo 107783 418385 := bstep (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) B313789
theorem B617327 : Blo 107783 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B191359 : Blo 107783 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B7041593 : Blo 107783 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B390683 : Blo 107783 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B4694395 : Blo 107783 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B111079 : Blo 107783 111079 := bstep (se 1 (by rfl) ⟨83309, by rfl⟩ : syracuseStep 111079 = 166619) B166619
theorem B111263 : Blo 107783 111263 := bstep (se 1 (by rfl) ⟨83447, by rfl⟩ : syracuseStep 111263 = 166895) B166895
theorem B19510159 : Blo 107783 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B278923 : Blo 107783 278923 := bstep (se 1 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 278923 = 418385) B418385
theorem B1491911 : Blo 107783 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B246815 : Blo 107783 246815 := bstep (se 1 (by rfl) ⟨185111, by rfl⟩ : syracuseStep 246815 = 370223) B370223
theorem B411551 : Blo 107783 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B247967 : Blo 107783 247967 := bstep (se 1 (by rfl) ⟨185975, by rfl⟩ : syracuseStep 247967 = 371951) B371951
theorem B250271 : Blo 107783 250271 := bstep (se 1 (by rfl) ⟨187703, by rfl⟩ : syracuseStep 250271 = 375407) B375407
theorem B1073033 : Blo 107783 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B713407 : Blo 107783 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B255145 : Blo 107783 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B845639 : Blo 107783 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B260455 : Blo 107783 260455 := bstep (se 1 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 260455 = 390683) B390683
theorem B6259193 : Blo 107783 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B164543 : Blo 107783 164543 := bstep (se 1 (by rfl) ⟨123407, by rfl⟩ : syracuseStep 164543 = 246815) B246815
theorem B951209 : Blo 107783 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B165311 : Blo 107783 165311 := bstep (se 1 (by rfl) ⟨123983, by rfl⟩ : syracuseStep 165311 = 247967) B247967
theorem B166847 : Blo 107783 166847 := bstep (se 1 (by rfl) ⟨125135, by rfl⟩ : syracuseStep 166847 = 250271) B250271
theorem B563759 : Blo 107783 563759 := bstep (se 1 (by rfl) ⟨422819, by rfl⟩ : syracuseStep 563759 = 845639) B845639
theorem B371897 : Blo 107783 371897 := bstep (se 2 (by rfl) ⟨139461, by rfl⟩ : syracuseStep 371897 = 278923) B278923
theorem B994607 : Blo 107783 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B274367 : Blo 107783 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B340193 : Blo 107783 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B347273 : Blo 107783 347273 := bstep (se 2 (by rfl) ⟨130227, by rfl⟩ : syracuseStep 347273 = 260455) B260455
theorem B715355 : Blo 107783 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B26013545 : Blo 107783 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B231515 : Blo 107783 231515 := bstep (se 1 (by rfl) ⟨173636, by rfl⟩ : syracuseStep 231515 = 347273) B347273
theorem B663071 : Blo 107783 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B17342363 : Blo 107783 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B4172795 : Blo 107783 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B109695 : Blo 107783 109695 := bstep (se 1 (by rfl) ⟨82271, by rfl⟩ : syracuseStep 109695 = 164543) B164543
theorem B634139 : Blo 107783 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B110207 : Blo 107783 110207 := bstep (se 1 (by rfl) ⟨82655, by rfl⟩ : syracuseStep 110207 = 165311) B165311
theorem B111231 : Blo 107783 111231 := bstep (se 1 (by rfl) ⟨83423, by rfl⟩ : syracuseStep 111231 = 166847) B166847
theorem B375839 : Blo 107783 375839 := bstep (se 1 (by rfl) ⟨281879, by rfl⟩ : syracuseStep 375839 = 563759) B563759
theorem B476903 : Blo 107783 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B247931 : Blo 107783 247931 := bstep (se 1 (by rfl) ⟨185948, by rfl⟩ : syracuseStep 247931 = 371897) B371897
theorem B182911 : Blo 107783 182911 := bstep (se 1 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 182911 = 274367) B274367
theorem B226795 : Blo 107783 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B165287 : Blo 107783 165287 := bstep (se 1 (by rfl) ⟨123965, by rfl⟩ : syracuseStep 165287 = 247931) B247931
theorem B302393 : Blo 107783 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B243881 : Blo 107783 243881 := bstep (se 2 (by rfl) ⟨91455, by rfl⟩ : syracuseStep 243881 = 182911) B182911
theorem B250559 : Blo 107783 250559 := bstep (se 1 (by rfl) ⟨187919, by rfl⟩ : syracuseStep 250559 = 375839) B375839
theorem B317935 : Blo 107783 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B154343 : Blo 107783 154343 := bstep (se 1 (by rfl) ⟨115757, by rfl⟩ : syracuseStep 154343 = 231515) B231515
theorem B11561575 : Blo 107783 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B2781863 : Blo 107783 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B422759 : Blo 107783 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B1768189 : Blo 107783 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B167039 : Blo 107783 167039 := bstep (se 1 (by rfl) ⟨125279, by rfl⟩ : syracuseStep 167039 = 250559) B250559
theorem B110191 : Blo 107783 110191 := bstep (se 1 (by rfl) ⟨82643, by rfl⟩ : syracuseStep 110191 = 165287) B165287
theorem B15415433 : Blo 107783 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B411581 : Blo 107783 411581 := bstep (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) B154343
theorem B1854575 : Blo 107783 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B281839 : Blo 107783 281839 := bstep (se 1 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 281839 = 422759) B422759
theorem B806381 : Blo 107783 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B423913 : Blo 107783 423913 := bstep (se 2 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 423913 = 317935) B317935
theorem B2357585 : Blo 107783 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B162587 : Blo 107783 162587 := bstep (se 1 (by rfl) ⟨121940, by rfl⟩ : syracuseStep 162587 = 243881) B243881
theorem B565217 : Blo 107783 565217 := bstep (se 2 (by rfl) ⟨211956, by rfl⟩ : syracuseStep 565217 = 423913) B423913
theorem B108391 : Blo 107783 108391 := bstep (se 1 (by rfl) ⟨81293, by rfl⟩ : syracuseStep 108391 = 162587) B162587
theorem B274387 : Blo 107783 274387 := bstep (se 1 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 274387 = 411581) B411581
theorem B111359 : Blo 107783 111359 := bstep (se 1 (by rfl) ⟨83519, by rfl⟩ : syracuseStep 111359 = 167039) B167039
theorem B537587 : Blo 107783 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B375785 : Blo 107783 375785 := bstep (se 2 (by rfl) ⟨140919, by rfl⟩ : syracuseStep 375785 = 281839) B281839
theorem B10276955 : Blo 107783 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B1236383 : Blo 107783 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B1571723 : Blo 107783 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B6851303 : Blo 107783 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B824255 : Blo 107783 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B365849 : Blo 107783 365849 := bstep (se 2 (by rfl) ⟨137193, by rfl⟩ : syracuseStep 365849 = 274387) B274387
theorem B376811 : Blo 107783 376811 := bstep (se 1 (by rfl) ⟨282608, by rfl⟩ : syracuseStep 376811 = 565217) B565217
theorem B250523 : Blo 107783 250523 := bstep (se 1 (by rfl) ⟨187892, by rfl⟩ : syracuseStep 250523 = 375785) B375785
theorem B358391 : Blo 107783 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B1047815 : Blo 107783 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B167015 : Blo 107783 167015 := bstep (se 1 (by rfl) ⟨125261, by rfl⟩ : syracuseStep 167015 = 250523) B250523
theorem B955709 : Blo 107783 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B698543 : Blo 107783 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B4567535 : Blo 107783 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B243899 : Blo 107783 243899 := bstep (se 1 (by rfl) ⟨182924, by rfl⟩ : syracuseStep 243899 = 365849) B365849
theorem B251207 : Blo 107783 251207 := bstep (se 1 (by rfl) ⟨188405, by rfl⟩ : syracuseStep 251207 = 376811) B376811
theorem B549503 : Blo 107783 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B167471 : Blo 107783 167471 := bstep (se 1 (by rfl) ⟨125603, by rfl⟩ : syracuseStep 167471 = 251207) B251207
theorem B366335 : Blo 107783 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B465695 : Blo 107783 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B111343 : Blo 107783 111343 := bstep (se 1 (by rfl) ⟨83507, by rfl⟩ : syracuseStep 111343 = 167015) B167015
theorem B637139 : Blo 107783 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B3045023 : Blo 107783 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B162599 : Blo 107783 162599 := bstep (se 1 (by rfl) ⟨121949, by rfl⟩ : syracuseStep 162599 = 243899) B243899
theorem B108399 : Blo 107783 108399 := bstep (se 1 (by rfl) ⟨81299, by rfl⟩ : syracuseStep 108399 = 162599) B162599
theorem B111647 : Blo 107783 111647 := bstep (se 1 (by rfl) ⟨83735, by rfl⟩ : syracuseStep 111647 = 167471) B167471
theorem B244223 : Blo 107783 244223 := bstep (se 1 (by rfl) ⟨183167, by rfl⟩ : syracuseStep 244223 = 366335) B366335
theorem B310463 : Blo 107783 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B2030015 : Blo 107783 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B424759 : Blo 107783 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B566345 : Blo 107783 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B1353343 : Blo 107783 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B206975 : Blo 107783 206975 := bstep (se 1 (by rfl) ⟨155231, by rfl⟩ : syracuseStep 206975 = 310463) B310463
theorem B162815 : Blo 107783 162815 := bstep (se 1 (by rfl) ⟨122111, by rfl⟩ : syracuseStep 162815 = 244223) B244223
theorem B1804457 : Blo 107783 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B108543 : Blo 107783 108543 := bstep (se 1 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 108543 = 162815) B162815
theorem B377563 : Blo 107783 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B551933 : Blo 107783 551933 := bstep (se 3 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 551933 = 206975) B206975
theorem B367955 : Blo 107783 367955 := bstep (se 1 (by rfl) ⟨275966, by rfl⟩ : syracuseStep 367955 = 551933) B551933
theorem B503417 : Blo 107783 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B1202971 : Blo 107783 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B335611 : Blo 107783 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B245303 : Blo 107783 245303 := bstep (se 1 (by rfl) ⟨183977, by rfl⟩ : syracuseStep 245303 = 367955) B367955
theorem B1603961 : Blo 107783 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B1069307 : Blo 107783 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B447481 : Blo 107783 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B163535 : Blo 107783 163535 := bstep (se 1 (by rfl) ⟨122651, by rfl⟩ : syracuseStep 163535 = 245303) B245303
theorem B596641 : Blo 107783 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B109023 : Blo 107783 109023 := bstep (se 1 (by rfl) ⟨81767, by rfl⟩ : syracuseStep 109023 = 163535) B163535
theorem B712871 : Blo 107783 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B795521 : Blo 107783 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B475247 : Blo 107783 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B316831 : Blo 107783 316831 := bstep (se 1 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 316831 = 475247) B475247
theorem B2121389 : Blo 107783 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B1414259 : Blo 107783 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B422441 : Blo 107783 422441 := bstep (se 2 (by rfl) ⟨158415, by rfl⟩ : syracuseStep 422441 = 316831) B316831
theorem B281627 : Blo 107783 281627 := bstep (se 1 (by rfl) ⟨211220, by rfl⟩ : syracuseStep 281627 = 422441) B422441
theorem B942839 : Blo 107783 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B628559 : Blo 107783 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B187751 : Blo 107783 187751 := bstep (se 1 (by rfl) ⟨140813, by rfl⟩ : syracuseStep 187751 = 281627) B281627
theorem B419039 : Blo 107783 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B125167 : Blo 107783 125167 := bstep (se 1 (by rfl) ⟨93875, by rfl⟩ : syracuseStep 125167 = 187751) B187751
theorem B166889 : Blo 107783 166889 := bstep (se 2 (by rfl) ⟨62583, by rfl⟩ : syracuseStep 166889 = 125167) B125167
theorem B279359 : Blo 107783 279359 := bstep (se 1 (by rfl) ⟨209519, by rfl⟩ : syracuseStep 279359 = 419039) B419039
theorem B111259 : Blo 107783 111259 := bstep (se 1 (by rfl) ⟨83444, by rfl⟩ : syracuseStep 111259 = 166889) B166889
theorem B186239 : Blo 107783 186239 := bstep (se 1 (by rfl) ⟨139679, by rfl⟩ : syracuseStep 186239 = 279359) B279359
theorem B124159 : Blo 107783 124159 := bstep (se 1 (by rfl) ⟨93119, by rfl⟩ : syracuseStep 124159 = 186239) B186239
theorem B165545 : Blo 107783 165545 := bstep (se 2 (by rfl) ⟨62079, by rfl⟩ : syracuseStep 165545 = 124159) B124159
theorem B110363 : Blo 107783 110363 := bstep (se 1 (by rfl) ⟨82772, by rfl⟩ : syracuseStep 110363 = 165545) B165545

theorem C0 (j : ℕ) (h1 : 26945 ≤ j) (h2 : j ≤ 27644) : Blo 107783 (4 * j + 3) := by
  interval_cases j
  · exact B107783
  · exact B107787
  · exact B107791
  · exact B107795
  · exact B107799
  · exact B107803
  · exact B107807
  · exact B107811
  · exact B107815
  · exact B107819
  · exact B107823
  · exact B107827
  · exact B107831
  · exact B107835
  · exact B107839
  · exact B107843
  · exact B107847
  · exact B107851
  · exact B107855
  · exact B107859
  · exact B107863
  · exact B107867
  · exact B107871
  · exact B107875
  · exact B107879
  · exact B107883
  · exact B107887
  · exact B107891
  · exact B107895
  · exact B107899
  · exact B107903
  · exact B107907
  · exact B107911
  · exact B107915
  · exact B107919
  · exact B107923
  · exact B107927
  · exact B107931
  · exact B107935
  · exact B107939
  · exact B107943
  · exact B107947
  · exact B107951
  · exact B107955
  · exact B107959
  · exact B107963
  · exact B107967
  · exact B107971
  · exact B107975
  · exact B107979
  · exact B107983
  · exact B107987
  · exact B107991
  · exact B107995
  · exact B107999
  · exact B108003
  · exact B108007
  · exact B108011
  · exact B108015
  · exact B108019
  · exact B108023
  · exact B108027
  · exact B108031
  · exact B108035
  · exact B108039
  · exact B108043
  · exact B108047
  · exact B108051
  · exact B108055
  · exact B108059
  · exact B108063
  · exact B108067
  · exact B108071
  · exact B108075
  · exact B108079
  · exact B108083
  · exact B108087
  · exact B108091
  · exact B108095
  · exact B108099
  · exact B108103
  · exact B108107
  · exact B108111
  · exact B108115
  · exact B108119
  · exact B108123
  · exact B108127
  · exact B108131
  · exact B108135
  · exact B108139
  · exact B108143
  · exact B108147
  · exact B108151
  · exact B108155
  · exact B108159
  · exact B108163
  · exact B108167
  · exact B108171
  · exact B108175
  · exact B108179
  · exact B108183
  · exact B108187
  · exact B108191
  · exact B108195
  · exact B108199
  · exact B108203
  · exact B108207
  · exact B108211
  · exact B108215
  · exact B108219
  · exact B108223
  · exact B108227
  · exact B108231
  · exact B108235
  · exact B108239
  · exact B108243
  · exact B108247
  · exact B108251
  · exact B108255
  · exact B108259
  · exact B108263
  · exact B108267
  · exact B108271
  · exact B108275
  · exact B108279
  · exact B108283
  · exact B108287
  · exact B108291
  · exact B108295
  · exact B108299
  · exact B108303
  · exact B108307
  · exact B108311
  · exact B108315
  · exact B108319
  · exact B108323
  · exact B108327
  · exact B108331
  · exact B108335
  · exact B108339
  · exact B108343
  · exact B108347
  · exact B108351
  · exact B108355
  · exact B108359
  · exact B108363
  · exact B108367
  · exact B108371
  · exact B108375
  · exact B108379
  · exact B108383
  · exact B108387
  · exact B108391
  · exact B108395
  · exact B108399
  · exact B108403
  · exact B108407
  · exact B108411
  · exact B108415
  · exact B108419
  · exact B108423
  · exact B108427
  · exact B108431
  · exact B108435
  · exact B108439
  · exact B108443
  · exact B108447
  · exact B108451
  · exact B108455
  · exact B108459
  · exact B108463
  · exact B108467
  · exact B108471
  · exact B108475
  · exact B108479
  · exact B108483
  · exact B108487
  · exact B108491
  · exact B108495
  · exact B108499
  · exact B108503
  · exact B108507
  · exact B108511
  · exact B108515
  · exact B108519
  · exact B108523
  · exact B108527
  · exact B108531
  · exact B108535
  · exact B108539
  · exact B108543
  · exact B108547
  · exact B108551
  · exact B108555
  · exact B108559
  · exact B108563
  · exact B108567
  · exact B108571
  · exact B108575
  · exact B108579
  · exact B108583
  · exact B108587
  · exact B108591
  · exact B108595
  · exact B108599
  · exact B108603
  · exact B108607
  · exact B108611
  · exact B108615
  · exact B108619
  · exact B108623
  · exact B108627
  · exact B108631
  · exact B108635
  · exact B108639
  · exact B108643
  · exact B108647
  · exact B108651
  · exact B108655
  · exact B108659
  · exact B108663
  · exact B108667
  · exact B108671
  · exact B108675
  · exact B108679
  · exact B108683
  · exact B108687
  · exact B108691
  · exact B108695
  · exact B108699
  · exact B108703
  · exact B108707
  · exact B108711
  · exact B108715
  · exact B108719
  · exact B108723
  · exact B108727
  · exact B108731
  · exact B108735
  · exact B108739
  · exact B108743
  · exact B108747
  · exact B108751
  · exact B108755
  · exact B108759
  · exact B108763
  · exact B108767
  · exact B108771
  · exact B108775
  · exact B108779
  · exact B108783
  · exact B108787
  · exact B108791
  · exact B108795
  · exact B108799
  · exact B108803
  · exact B108807
  · exact B108811
  · exact B108815
  · exact B108819
  · exact B108823
  · exact B108827
  · exact B108831
  · exact B108835
  · exact B108839
  · exact B108843
  · exact B108847
  · exact B108851
  · exact B108855
  · exact B108859
  · exact B108863
  · exact B108867
  · exact B108871
  · exact B108875
  · exact B108879
  · exact B108883
  · exact B108887
  · exact B108891
  · exact B108895
  · exact B108899
  · exact B108903
  · exact B108907
  · exact B108911
  · exact B108915
  · exact B108919
  · exact B108923
  · exact B108927
  · exact B108931
  · exact B108935
  · exact B108939
  · exact B108943
  · exact B108947
  · exact B108951
  · exact B108955
  · exact B108959
  · exact B108963
  · exact B108967
  · exact B108971
  · exact B108975
  · exact B108979
  · exact B108983
  · exact B108987
  · exact B108991
  · exact B108995
  · exact B108999
  · exact B109003
  · exact B109007
  · exact B109011
  · exact B109015
  · exact B109019
  · exact B109023
  · exact B109027
  · exact B109031
  · exact B109035
  · exact B109039
  · exact B109043
  · exact B109047
  · exact B109051
  · exact B109055
  · exact B109059
  · exact B109063
  · exact B109067
  · exact B109071
  · exact B109075
  · exact B109079
  · exact B109083
  · exact B109087
  · exact B109091
  · exact B109095
  · exact B109099
  · exact B109103
  · exact B109107
  · exact B109111
  · exact B109115
  · exact B109119
  · exact B109123
  · exact B109127
  · exact B109131
  · exact B109135
  · exact B109139
  · exact B109143
  · exact B109147
  · exact B109151
  · exact B109155
  · exact B109159
  · exact B109163
  · exact B109167
  · exact B109171
  · exact B109175
  · exact B109179
  · exact B109183
  · exact B109187
  · exact B109191
  · exact B109195
  · exact B109199
  · exact B109203
  · exact B109207
  · exact B109211
  · exact B109215
  · exact B109219
  · exact B109223
  · exact B109227
  · exact B109231
  · exact B109235
  · exact B109239
  · exact B109243
  · exact B109247
  · exact B109251
  · exact B109255
  · exact B109259
  · exact B109263
  · exact B109267
  · exact B109271
  · exact B109275
  · exact B109279
  · exact B109283
  · exact B109287
  · exact B109291
  · exact B109295
  · exact B109299
  · exact B109303
  · exact B109307
  · exact B109311
  · exact B109315
  · exact B109319
  · exact B109323
  · exact B109327
  · exact B109331
  · exact B109335
  · exact B109339
  · exact B109343
  · exact B109347
  · exact B109351
  · exact B109355
  · exact B109359
  · exact B109363
  · exact B109367
  · exact B109371
  · exact B109375
  · exact B109379
  · exact B109383
  · exact B109387
  · exact B109391
  · exact B109395
  · exact B109399
  · exact B109403
  · exact B109407
  · exact B109411
  · exact B109415
  · exact B109419
  · exact B109423
  · exact B109427
  · exact B109431
  · exact B109435
  · exact B109439
  · exact B109443
  · exact B109447
  · exact B109451
  · exact B109455
  · exact B109459
  · exact B109463
  · exact B109467
  · exact B109471
  · exact B109475
  · exact B109479
  · exact B109483
  · exact B109487
  · exact B109491
  · exact B109495
  · exact B109499
  · exact B109503
  · exact B109507
  · exact B109511
  · exact B109515
  · exact B109519
  · exact B109523
  · exact B109527
  · exact B109531
  · exact B109535
  · exact B109539
  · exact B109543
  · exact B109547
  · exact B109551
  · exact B109555
  · exact B109559
  · exact B109563
  · exact B109567
  · exact B109571
  · exact B109575
  · exact B109579
  · exact B109583
  · exact B109587
  · exact B109591
  · exact B109595
  · exact B109599
  · exact B109603
  · exact B109607
  · exact B109611
  · exact B109615
  · exact B109619
  · exact B109623
  · exact B109627
  · exact B109631
  · exact B109635
  · exact B109639
  · exact B109643
  · exact B109647
  · exact B109651
  · exact B109655
  · exact B109659
  · exact B109663
  · exact B109667
  · exact B109671
  · exact B109675
  · exact B109679
  · exact B109683
  · exact B109687
  · exact B109691
  · exact B109695
  · exact B109699
  · exact B109703
  · exact B109707
  · exact B109711
  · exact B109715
  · exact B109719
  · exact B109723
  · exact B109727
  · exact B109731
  · exact B109735
  · exact B109739
  · exact B109743
  · exact B109747
  · exact B109751
  · exact B109755
  · exact B109759
  · exact B109763
  · exact B109767
  · exact B109771
  · exact B109775
  · exact B109779
  · exact B109783
  · exact B109787
  · exact B109791
  · exact B109795
  · exact B109799
  · exact B109803
  · exact B109807
  · exact B109811
  · exact B109815
  · exact B109819
  · exact B109823
  · exact B109827
  · exact B109831
  · exact B109835
  · exact B109839
  · exact B109843
  · exact B109847
  · exact B109851
  · exact B109855
  · exact B109859
  · exact B109863
  · exact B109867
  · exact B109871
  · exact B109875
  · exact B109879
  · exact B109883
  · exact B109887
  · exact B109891
  · exact B109895
  · exact B109899
  · exact B109903
  · exact B109907
  · exact B109911
  · exact B109915
  · exact B109919
  · exact B109923
  · exact B109927
  · exact B109931
  · exact B109935
  · exact B109939
  · exact B109943
  · exact B109947
  · exact B109951
  · exact B109955
  · exact B109959
  · exact B109963
  · exact B109967
  · exact B109971
  · exact B109975
  · exact B109979
  · exact B109983
  · exact B109987
  · exact B109991
  · exact B109995
  · exact B109999
  · exact B110003
  · exact B110007
  · exact B110011
  · exact B110015
  · exact B110019
  · exact B110023
  · exact B110027
  · exact B110031
  · exact B110035
  · exact B110039
  · exact B110043
  · exact B110047
  · exact B110051
  · exact B110055
  · exact B110059
  · exact B110063
  · exact B110067
  · exact B110071
  · exact B110075
  · exact B110079
  · exact B110083
  · exact B110087
  · exact B110091
  · exact B110095
  · exact B110099
  · exact B110103
  · exact B110107
  · exact B110111
  · exact B110115
  · exact B110119
  · exact B110123
  · exact B110127
  · exact B110131
  · exact B110135
  · exact B110139
  · exact B110143
  · exact B110147
  · exact B110151
  · exact B110155
  · exact B110159
  · exact B110163
  · exact B110167
  · exact B110171
  · exact B110175
  · exact B110179
  · exact B110183
  · exact B110187
  · exact B110191
  · exact B110195
  · exact B110199
  · exact B110203
  · exact B110207
  · exact B110211
  · exact B110215
  · exact B110219
  · exact B110223
  · exact B110227
  · exact B110231
  · exact B110235
  · exact B110239
  · exact B110243
  · exact B110247
  · exact B110251
  · exact B110255
  · exact B110259
  · exact B110263
  · exact B110267
  · exact B110271
  · exact B110275
  · exact B110279
  · exact B110283
  · exact B110287
  · exact B110291
  · exact B110295
  · exact B110299
  · exact B110303
  · exact B110307
  · exact B110311
  · exact B110315
  · exact B110319
  · exact B110323
  · exact B110327
  · exact B110331
  · exact B110335
  · exact B110339
  · exact B110343
  · exact B110347
  · exact B110351
  · exact B110355
  · exact B110359
  · exact B110363
  · exact B110367
  · exact B110371
  · exact B110375
  · exact B110379
  · exact B110383
  · exact B110387
  · exact B110391
  · exact B110395
  · exact B110399
  · exact B110403
  · exact B110407
  · exact B110411
  · exact B110415
  · exact B110419
  · exact B110423
  · exact B110427
  · exact B110431
  · exact B110435
  · exact B110439
  · exact B110443
  · exact B110447
  · exact B110451
  · exact B110455
  · exact B110459
  · exact B110463
  · exact B110467
  · exact B110471
  · exact B110475
  · exact B110479
  · exact B110483
  · exact B110487
  · exact B110491
  · exact B110495
  · exact B110499
  · exact B110503
  · exact B110507
  · exact B110511
  · exact B110515
  · exact B110519
  · exact B110523
  · exact B110527
  · exact B110531
  · exact B110535
  · exact B110539
  · exact B110543
  · exact B110547
  · exact B110551
  · exact B110555
  · exact B110559
  · exact B110563
  · exact B110567
  · exact B110571
  · exact B110575
  · exact B110579

theorem C1 (j : ℕ) (h1 : 27645 ≤ j) (h2 : j ≤ 27945) : Blo 107783 (4 * j + 3) := by
  interval_cases j
  · exact B110583
  · exact B110587
  · exact B110591
  · exact B110595
  · exact B110599
  · exact B110603
  · exact B110607
  · exact B110611
  · exact B110615
  · exact B110619
  · exact B110623
  · exact B110627
  · exact B110631
  · exact B110635
  · exact B110639
  · exact B110643
  · exact B110647
  · exact B110651
  · exact B110655
  · exact B110659
  · exact B110663
  · exact B110667
  · exact B110671
  · exact B110675
  · exact B110679
  · exact B110683
  · exact B110687
  · exact B110691
  · exact B110695
  · exact B110699
  · exact B110703
  · exact B110707
  · exact B110711
  · exact B110715
  · exact B110719
  · exact B110723
  · exact B110727
  · exact B110731
  · exact B110735
  · exact B110739
  · exact B110743
  · exact B110747
  · exact B110751
  · exact B110755
  · exact B110759
  · exact B110763
  · exact B110767
  · exact B110771
  · exact B110775
  · exact B110779
  · exact B110783
  · exact B110787
  · exact B110791
  · exact B110795
  · exact B110799
  · exact B110803
  · exact B110807
  · exact B110811
  · exact B110815
  · exact B110819
  · exact B110823
  · exact B110827
  · exact B110831
  · exact B110835
  · exact B110839
  · exact B110843
  · exact B110847
  · exact B110851
  · exact B110855
  · exact B110859
  · exact B110863
  · exact B110867
  · exact B110871
  · exact B110875
  · exact B110879
  · exact B110883
  · exact B110887
  · exact B110891
  · exact B110895
  · exact B110899
  · exact B110903
  · exact B110907
  · exact B110911
  · exact B110915
  · exact B110919
  · exact B110923
  · exact B110927
  · exact B110931
  · exact B110935
  · exact B110939
  · exact B110943
  · exact B110947
  · exact B110951
  · exact B110955
  · exact B110959
  · exact B110963
  · exact B110967
  · exact B110971
  · exact B110975
  · exact B110979
  · exact B110983
  · exact B110987
  · exact B110991
  · exact B110995
  · exact B110999
  · exact B111003
  · exact B111007
  · exact B111011
  · exact B111015
  · exact B111019
  · exact B111023
  · exact B111027
  · exact B111031
  · exact B111035
  · exact B111039
  · exact B111043
  · exact B111047
  · exact B111051
  · exact B111055
  · exact B111059
  · exact B111063
  · exact B111067
  · exact B111071
  · exact B111075
  · exact B111079
  · exact B111083
  · exact B111087
  · exact B111091
  · exact B111095
  · exact B111099
  · exact B111103
  · exact B111107
  · exact B111111
  · exact B111115
  · exact B111119
  · exact B111123
  · exact B111127
  · exact B111131
  · exact B111135
  · exact B111139
  · exact B111143
  · exact B111147
  · exact B111151
  · exact B111155
  · exact B111159
  · exact B111163
  · exact B111167
  · exact B111171
  · exact B111175
  · exact B111179
  · exact B111183
  · exact B111187
  · exact B111191
  · exact B111195
  · exact B111199
  · exact B111203
  · exact B111207
  · exact B111211
  · exact B111215
  · exact B111219
  · exact B111223
  · exact B111227
  · exact B111231
  · exact B111235
  · exact B111239
  · exact B111243
  · exact B111247
  · exact B111251
  · exact B111255
  · exact B111259
  · exact B111263
  · exact B111267
  · exact B111271
  · exact B111275
  · exact B111279
  · exact B111283
  · exact B111287
  · exact B111291
  · exact B111295
  · exact B111299
  · exact B111303
  · exact B111307
  · exact B111311
  · exact B111315
  · exact B111319
  · exact B111323
  · exact B111327
  · exact B111331
  · exact B111335
  · exact B111339
  · exact B111343
  · exact B111347
  · exact B111351
  · exact B111355
  · exact B111359
  · exact B111363
  · exact B111367
  · exact B111371
  · exact B111375
  · exact B111379
  · exact B111383
  · exact B111387
  · exact B111391
  · exact B111395
  · exact B111399
  · exact B111403
  · exact B111407
  · exact B111411
  · exact B111415
  · exact B111419
  · exact B111423
  · exact B111427
  · exact B111431
  · exact B111435
  · exact B111439
  · exact B111443
  · exact B111447
  · exact B111451
  · exact B111455
  · exact B111459
  · exact B111463
  · exact B111467
  · exact B111471
  · exact B111475
  · exact B111479
  · exact B111483
  · exact B111487
  · exact B111491
  · exact B111495
  · exact B111499
  · exact B111503
  · exact B111507
  · exact B111511
  · exact B111515
  · exact B111519
  · exact B111523
  · exact B111527
  · exact B111531
  · exact B111535
  · exact B111539
  · exact B111543
  · exact B111547
  · exact B111551
  · exact B111555
  · exact B111559
  · exact B111563
  · exact B111567
  · exact B111571
  · exact B111575
  · exact B111579
  · exact B111583
  · exact B111587
  · exact B111591
  · exact B111595
  · exact B111599
  · exact B111603
  · exact B111607
  · exact B111611
  · exact B111615
  · exact B111619
  · exact B111623
  · exact B111627
  · exact B111631
  · exact B111635
  · exact B111639
  · exact B111643
  · exact B111647
  · exact B111651
  · exact B111655
  · exact B111659
  · exact B111663
  · exact B111667
  · exact B111671
  · exact B111675
  · exact B111679
  · exact B111683
  · exact B111687
  · exact B111691
  · exact B111695
  · exact B111699
  · exact B111703
  · exact B111707
  · exact B111711
  · exact B111715
  · exact B111719
  · exact B111723
  · exact B111727
  · exact B111731
  · exact B111735
  · exact B111739
  · exact B111743
  · exact B111747
  · exact B111751
  · exact B111755
  · exact B111759
  · exact B111763
  · exact B111767
  · exact B111771
  · exact B111775
  · exact B111779
  · exact B111783

theorem solution (m : ℕ) (hlo : 107783 ≤ m) (hhi : m ≤ 111783) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 26945 ≤ j := by omega
    have hj2 : j ≤ 27945 := by omega
    have hb : Blo 107783 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 27645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
